open Util
open Random
open Ids

let g_debug = false

let num_corpus = 2

let r_space = Str.regexp " "

let _ = Random.self_init ()

(* get groups, lines of a file *)
let lines_of_file f =
  let lines = read_file_lines f in
  List.map (fun str ->
    let words = Str.split r_space str in
    let group = match hd words with
      | "0" -> 0
      | "1" -> 1
      | _   -> failwith "Not 0 or 1 in group"
    in
    group, list_drop 1 words
  ) lines

type topic_src =
  Global | Corpus

let topic_src_of_int = function
  | 0 -> Global
  | 1 -> Corpus
  | _ -> invalid_arg "Topic Src"

type token_data = {
  id: id;
  mutable z: int;
  mutable x: topic_src;
}

let empty_data = {id=empty_id; z=0; x=Global}

type doc_data = {
  tokens: token_data array;
  corpus: int;
  topic_assign: int array; (* size = topics *)
}

type topic_data = {
  word_counts: int array; (* size = words *)
  mutable word_total: int;
}

let empty_topic_data words = {word_counts=Array.create words 0; word_total=0}

type topics_data = topic_data array (* size of topics *)

let empty_topics_data topics words =
  Array.of_list @: list_populate (fun _ -> empty_topic_data words) 0 topics

type global_topics_data = {
  global_topics : topics_data;
  group_topics : topics_data array;
}

let empty_global_topics_data topics words = {
  global_topics=empty_topics_data topics words;
  group_topics=Array.of_list @:
    list_populate (fun _ -> empty_topics_data topics words) 0 num_corpus
}

(* initialize a documents with just the words *)
let init_model topics_num lines =
  List.map (fun (corpus, words) ->
    let data =
      List.map (fun word -> {empty_data with id=id_of_str word}) words
    in
    {corpus; tokens=Array.of_list data; topic_assign=Array.create topics_num 0}
  ) lines

(* initialize probabilities and assign *)
let init_probs topics_num lines =
  List.iter (fun doc ->
    Array.iter (fun token ->
      token.z <- Random.int topics_num;
      token.x <- topic_src_of_int @: Random.int 2
    ) doc.tokens
  ) lines;
  lines

type params = {
  train_file : string;
  test_file : string;
  output_file : string;
  topics_num : int;
  lambda: float;
  alpha: float;
  beta: float;
  iterations: int;
  burn_in: int;
}

let topic_for_token topics document x topic_num = match x with
  | Global -> topics.global_topics.(topic_num)
  | Corpus -> topics.group_topics.(document.corpus).(topic_num)

let modify_cntrs op global_topics document token =
  let id, z, x = token.id, token.z, token.x in
  document.topic_assign.(z) <- op document.topic_assign.(z) 1;
  if document.topic_assign.(z) < 0 then (
    let s = Printf.sprintf "negative counter! doc_topic[%d](%d)"
      z document.topic_assign.(z) in failwith s);
  match global_topics with
  | None        -> ()
  | Some topics ->
    let topic = topic_for_token topics document x z in
    topic.word_counts.(id) <- op topic.word_counts.(id) 1;
    topic.word_total <- op topic.word_total 1;
    if topic.word_total < 0 || topic.word_counts.(id) < 0 then (
      let s = Printf.sprintf "negative counter! word_count[%s](%d), total(%d)"
        (str_of_id id) topic.word_counts.(id) topic.word_total in failwith s)

let remove_cntrs global_topics document token = modify_cntrs (-) global_topics document token
let add_cntrs global_topics document token = modify_cntrs (+) global_topics document token

(* initialize all counters based on initial assignments *)
let init_cntrs global_topics data =
  List.iter (fun doc ->
    Array.iter (fun token_d ->
      add_cntrs global_topics doc token_d
    ) doc.tokens
  ) data

(* draw randomly from a reverse cdf pair list where the p is first *)
let random_from_list l total =
  let r = Random.float total in
  if g_debug then begin
    List.iter (fun (p,_) -> Printf.printf "%f " p) l;
    Printf.printf "total(%f) random(%f)" total r;
    print_newline () end;
  snd @: List.find (fun (p,_) -> p <= r) l (* going backwards *)

let calc_theta_all topics_num alpha document =
  let ndstar = foi @: Array.length document.tokens in
  let bigK = (foi topics_num) *. alpha in
  let dividend = 1. /. (ndstar +. bigK *. alpha) in
  Array.map (fun ndk ->
    (foi ndk +. alpha) *. dividend
  ) document.topic_assign

let calc_theta topics_num alpha document topic_choice =
  let ndk = foi document.topic_assign.(topic_choice) in
  let ndstar = foi @: Array.length document.tokens in
  let bigK = (foi topics_num) *. alpha in
  let answer = (ndk +. alpha) /. (ndstar +. bigK *. alpha) in
  if answer < 0. then
    let s = Printf.sprintf "sanity fail! ndk(%f), ndstar(%f), bigK(%f), answer(%f)" ndk ndstar bigK answer in
      failwith s
    else answer

let calc_phi_all beta topic =
  let nkstar = foi @: topic.word_total in
  let bigV = foi @: word_types () in
  let dividend = 1. /. (nkstar +. bigV *. beta) in
  Array.map (fun nkw ->
    (foi nkw +. beta) *. dividend
  ) topic.word_counts

let calc_phi beta topic token_id =
  let nkw = foi topic.word_counts.(token_id) in
  let bigV = foi @: word_types () in
  let nkstar = foi @: topic.word_total in
  let answer = (nkw +. beta) /. (nkstar +. bigV *. beta) in
  if answer < 0. then 
    let s = Printf.sprintf "sanity fail! nkw(%f), bigV(%f), nkstar(%f), answer(%f)" nkw bigV nkstar answer in
      failwith s
    else answer

let update_train_token params global_topics document token =
  let alpha, beta, lambda = params.alpha, params.beta, params.lambda in
  (* i. exclude assignments of current token *)
  remove_cntrs (Some global_topics) document token;
  (* ii. sample new value for z *)
  (* calculations for random selection *)
  let p_list, total, _ =
    iterate (fun (acc, total, topic_num) ->
      let theta = calc_theta params.topics_num params.alpha document topic_num in
      let topic = topic_for_token global_topics document token.x topic_num in
      let phi = calc_phi params.beta topic token.id in
      let total' = total +. (theta *. phi) in
      (total, topic_num)::acc, total', topic_num + 1
    ) ([], 0., 0) params.topics_num
  in
  let new_z = random_from_list p_list total in
  (* iii. sample new value for x *)
  let p_list, total, _ =
    iterate (fun (acc, total, x) ->
      let topic = topic_for_token global_topics document x new_z in
      let phi = calc_phi params.beta topic token.id in
      let factor = match x with
        | Global -> 1. -. lambda
        | Corpus -> lambda
      in
      let total' = total +. factor *. phi in
      (total, x)::acc, total', Corpus
    ) ([], 0., Global) 2
  in
  let new_x = random_from_list p_list total in
  token.x <- new_x;
  token.z <- new_z;
  add_cntrs (Some global_topics) document token

(* perform an update for a test token *)
let update_test_token phis_g phis params _ document token =
  let alpha, beta, lambda = params.alpha, params.beta, params.lambda in
  (* i. exclude assignments of current token. Don't touch topic counters *)
  remove_cntrs None document token;
  (* ii. sample new value for z *)
  (* calculations for random selection *)
  let phi_src = match token.x with
    | Global -> phis_g | Corpus -> phis.(document.corpus)
  in
  let p_list, total, _ =
    iterate (fun (acc, total, topic_num) ->
      let theta = calc_theta params.topics_num params.alpha document topic_num in
      let phi = phi_src.(topic_num).(token.id) in
      let total' = total +. (theta *. phi) in
      (total, topic_num)::acc, total', topic_num + 1
    ) ([], 0., 0) params.topics_num
  in
  let new_z = random_from_list p_list total in
  (* iii. sample new value for x *)
  let p_list, total, _ =
    iterate (fun (acc, total, x) ->
      let phi_src, factor = match x with
        | Global -> phis_g, 1. -. lambda
        | Corpus -> phis.(document.corpus), lambda
      in
      let phi = phi_src.(new_z).(token.id) in
      let total' = total +. factor *. phi in
      (total, x)::acc, total', Corpus
    ) ([], 0., Global) 2
  in
  let new_x = random_from_list p_list total in
  token.x <- new_x;
  token.z <- new_z;
  add_cntrs None document token


type estimates = {
  thetas : float array array; (* per document per topic*)
  phis_g : float array; (* per topic per word *)
  phis : float array array; (* per corpus, per topic, per word*)
}

let string_of_thetas ts =
  let b = Buffer.create 100 in
  Array.iter (fun topic_arr ->
    Array.iter (fun theta ->
      Printf.bprintf b "%.13f " theta
    ) topic_arr;
    Printf.bprintf b "\n"
  ) ts;
  Buffer.contents b

let string_of_phis ps =
  let b = Buffer.create 100 in
  let jlen = Array.length ps.(0) in
  for i=0 to jlen-1 do (* word *)
    Printf.bprintf b "%s " (str_of_id i);
    for j=0 to Array.length ps - 1 do (* topic *)
      Printf.bprintf b "%.13f " ps.(j).(i)
    done;
    Printf.bprintf b "\n"
  done;
  Buffer.contents b

(*let add_to_estimates thetas phis_g phis estimates =
  array_modify2
    (fun _ theta1 theta2 -> theta1 +. theta2) estimates.thetas thetas;
  array_modify2
    (fun _ phi1 phi2 -> phi1 +. phi2) estimates.phis_g phis_g;
  array_iter2
    (fun arr1 arr2 ->
      array_modify2 (fun _ phi1 phi2 -> phi1 +. phi2) arr1 arr2
    ) estimates.phis phis
*)

(* update all the tokens *)
let update_tokens fn params topics data =
  List.iter (fun doc ->
    Array.iter (fun token ->
      fn params topics doc token
    ) doc.tokens
  ) data

(* calculate the log-likelihood *)
let log_likelihood lambda topics_num thetas phis_g phis data : float =
  let lambda_inv = 1. -. lambda in
  (* loop over document tokens *)
  fst @:
    List.fold_left (fun ((acc:float),d) doc ->
      let corpus = doc.corpus in
      let sum = Array.fold_left (fun (acc':float) token ->
        let id = token.id in
        let sum = fst @:
          iterate (fun (acc'', topic) ->
            let a = (lambda_inv *. phis_g.(topic).(id)) +.
                    (lambda *. phis.(corpus).(topic).(id)) in
            let b = thetas.(d).(topic) *. a in
            (acc'' +. b, topic + 1)
          ) (acc', 0) topics_num
        in
        acc' +. log sum
      ) acc doc.tokens
      in
      (sum, d + 1)
    ) (0., 0) data

(* run one iteration of the algorithm *)
let run_iter num params topics train_data test_data =
  (* run over each token in the set *)
  update_tokens update_train_token params topics train_data;
  (* calculate the new thetas and phis *)
  let new_thetas = Array.of_list @: List.map (fun doc ->
    calc_theta_all params.topics_num params.alpha doc
  ) train_data
  in
  print_endline @: string_of_thetas new_thetas;
  let new_phis_g = Array.map (fun topic ->
    calc_phi_all params.beta topic
  ) topics.global_topics
  in
  print_endline @: string_of_phis new_phis_g;
  let new_phis = Array.map (fun topic_arr ->
    Array.map (fun topic ->
      calc_phi_all params.beta topic
    ) topic_arr
  ) topics.group_topics
  in
  (* if burn-in is passed, add to estimates TODO *)
  (*if num > params.burn_in then*)
    (*add_to_estimates new_thetas new_phis_g new_phis estimates;*)
  (* run over each token in test data *)
  update_tokens (update_test_token new_phis_g new_phis) params topics test_data;
  (* return results *)
  (new_thetas, new_phis_g, new_phis)

type files = Theta | Phi | Phi0 | Phi1 | Train | Test

let file_types = [|Theta; Phi; Phi0; Phi1; Train; Test|]

let int_of_file = function
  | Theta -> 0 | Phi -> 1 | Phi0 -> 2 | Phi1 -> 3 | Train -> 4 | Test -> 5

let file_of_int = function
  | 0 -> Theta | 1 -> Phi | 2 -> Phi0 | 3 -> Phi1 | 4 -> Train | 5 -> Test
  | _ -> invalid_arg "bad int"

let str_of_file = function
  | Theta -> "theta" | Phi -> "phi" | Phi0 -> "phi0"
  | Phi1 -> "phi1" | Train -> "trainll" | Test -> "testll"

let run params =
  let ts = params.topics_num in
  let train_data =
    init_probs ts @: init_model ts @: lines_of_file params.train_file in
  let test_data =
    init_probs ts @: init_model ts @: lines_of_file params.test_file in
  let g_topics = empty_global_topics_data ts @: Ids.word_types () in
  (* initialize the counters *)
  init_cntrs (Some g_topics) train_data;
  init_cntrs None test_data;

  (* open the output files *)
  let o = params.output_file in
  let names = Array.map (fun t -> o^"-"^str_of_file t) file_types in
  let test_handle, train_handle =
    open_out names.(int_of_file Test), open_out names.(int_of_file Train) in

  (* run iterations *)
  let thetas, phis_g, phis, _ =
    iterate (fun (_, _, _, idx) ->
      let thetas, phis_g, phis =
        run_iter idx params g_topics train_data test_data in
      let train_ll =
        log_likelihood  params.lambda params.topics_num thetas phis_g phis train_data in
      Printf.fprintf train_handle "%.13f" train_ll;
      let test_ll =
        log_likelihood  params.lambda params.topics_num thetas phis_g phis test_data in
      Printf.fprintf test_handle "%.13f" test_ll;
      (thetas, phis_g, phis, idx + 1)
    ) ([||], [||], [||], 1) params.iterations
  in
  close_out test_handle;
  close_out train_handle;
  let thetas_s = string_of_thetas thetas in
  write_file names.(int_of_file Theta) thetas_s;
  let phis_g_s = string_of_phis phis_g in
  write_file names.(int_of_file Phi) phis_g_s;
  let phis_0_s = string_of_phis phis.(0) in
  write_file names.(int_of_file Phi0) phis_0_s;
  let phis_1_s = string_of_phis phis.(1) in
  write_file names.(int_of_file Phi1) phis_1_s

let main () =
  let argv = Sys.argv in
  if Array.length argv <> 10 then
    Printf.printf
      "%s input_train input_test output_file topics lambda alpha beta iterations burn-in\n"
      argv.(0)
  else
    let params = {
      train_file = argv.(1);
      test_file = argv.(2);
      output_file = argv.(3);
      topics_num = ios argv.(4);
      lambda = fos argv.(5);
      alpha = fos argv.(6);
      beta = fos argv.(7);
      iterations = ios argv.(8);
      burn_in = ios argv.(9);
    }
    in run params

let _ =
  if !Sys.interactive then ()
  else main ()

