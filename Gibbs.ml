open Util
open Random
open Ids

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

type token_data = {
  token: id;
  z: mutable int;
  x: mutable int;
}

let empty_data = {token=empty_id; z=0; x=0}

type doc_data = {
  tokens: token_data array;
  corpus: int;
  topic_assign: int array; (* size = topics *)
}

type topic_data = {
  word_counts: int array; (* size = words *)
  word_total: mutable int;
}

let empty_topic_data words = {word_counts=Array.create words (-1); word_total=0}

type topics_data = topic_data array (* size of topics *)

let empty_topics_data topics words =
  Array.of_list @: list_populate (fun _ -> empty_topic_data words) 0 topics

type global_topics_data = {
  global_topics : topics_data;
  group_topics : topics_data array;
}

let empty_global_topics_data topics words = {
  global_topics=empty_topics_data topics words;
  group_topics=Array.of_list @: list_populate (fun _ -> empty_topics_data topics words) 0 num_corpus
}

(* initialize a documents with just the words *)
let init_model lines =
  List.map (fun group, words ->
    let data = 
      List.map (fun word -> {empty_data with token=id_of_str word}) words
    in
    {group; tokens=Array.of_list data; topic_assign=Array.create topics (-1)}
  ) words

(* initialize probabilities and assign *)
let init_probs topics lines =
  let topics_num = Array.length topics in
  List.map (fun group, ds ->
    group, Array.iter (fun d ->
      d.z <- Random.int topics_num;
      d.x <- Random.int 2
    ) ds
  ) lines

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

let topic_for_token global_topics document x topic_num = match x with
  | 0 -> global_topics.global_topics.(topic_num)
  | 1 -> global_topics.group_topics.(document.corpus).(topic_num)

let remove_cntrs op global_topics document token =
  let id, z, x = token.id, token.z, token.x in
  document.topic_assign.(z) <- op document.topic_assign.(z) 1;
  match global_topics with 
  | None        -> () 
  | Some topics ->
    let topic = topic_for_token topics document x z in
    topic.word_counts.(id) <- op topic.word_counts.(id) 1;
    topic.word_total <- op topic.word_total 1

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
  let _, result = List.find ((<=) r |- fst) l (* going backwards *)
  in result

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
  (ndk +. alpha) /. (ndstar +. bigK *. alpha)

let calc_phi_all beta topic =
  let nkstar = foi @: topic.word_total in
  let dividend = 1. /. (nkstar +. bigV *. beta) in
  Array.map (fun nkw ->
    (foi nkw +. beta) *. dividend
  ) topic.word_counts

let calc_phi beta topic token_id =
  let nkw = foi topic.word_counts.(token_id) in
  let nkstar = foi @: topic.word_total in
  (nkw +. beta) /. (nkstar +. bigV *. beta)

let update_train_token params global_topics document token =
  let alpha, beta, lambda = params.alpha, params.beta, params.lambda in
  (* i. exclude assignments of current token *)
  remove_cntrs (Some global_topics) document token;
  (* ii. sample new value for z *)
  let theta = calc_theta params document in
  let bigV = foi @: word_types () in
  (* calculations for random selection *)
  let p_list, total, _ =
    iterate (fun (acc, total, topic_num) ->
      let topic = topic_for_token global_topics document token.x topic_num in
      let phi = calc_phi topic in
      let total' = total +. (theta *. phi) in
      (total, topic_num)::acc, total', topic_num + 1
    ) ([], 0., 0) params.topics_num
  in
  let new_z = random_from_list total p_list in
  (* iii. sample new value for x *)
  let p_list, total, _ =
    iterate (fun (acc, total, x) ->
      let topic = topic_for_token global_topics document x new_z in
      let phi = calc_phi topic in
      let factor = match x with 0 -> 1 -. lambda | 1 -> lambda in
      let total' = total +. factor *. phi in
      (total, x)::acc, total', x + 1
    ) ([], 0., 0) 2
  in
  let new_x = random_from_list total p_list in
  token.x <- new_x;
  token.z <- new_z;
  add_cntrs (Some global_topics) document token

(* perform an update for a test token *)
let update_test_token phis_g phis params _ document token =
  let alpha, beta, lambda = params.alpha, params.beta, params.lambda in
  (* i. exclude assignments of current token *)
  remove_cntrs None document token;
  (* ii. sample new value for z *)
  let theta = calc_theta params document in
  let bigV = foi @: word_types () in
  (* calculations for random selection *)
  let phi_src = match token.x with 
    | 0 -> phis_g | 1 -> phis
  in
  let p_list, total, _ =
    iterate (fun (acc, total, topic_num) ->
      let phi = phi_src.(topic_num) in
      let total' = total +. (theta *. phi) in
      (total, topic_num)::acc, total', topic_num + 1
    ) ([], 0., 0) params.topics_num
  in
  let new_z = random_from_list total p_list in
  (* iii. sample new value for x *)
  let p_list, total, _ =
    iterate (fun (acc, total, x) ->
      let phi_src, factor = match x with 
        | 0 -> phis_g, 1 -. lambda | 1 -> phis, lambda
      in
      let phi = phi_src.(new_z)
      let total' = total +. factor *. phi in
      (total, x)::acc, total', x + 1
    ) ([], 0., 0) 2
  in
  let new_x = random_from_list total p_list in
  token.x <- new_x;
  token.z <- new_z;
  add_cntrs None document token


type estimates {
  thetas : float array array; (* per document per topic*)
  phis_g : float array; (* per topic per word *)
  phis : float array array; (* per corpus, per topic, per word*)
}

let add_to_estimates thetas phis_g phis estimates =
  array_modify2
    (fun _ theta1 theta2 -> theta1 +. theta2) estimates.thetas thetas;
  array_modify2 
    (fun _ phi1 phi2 -> phi1 +. phi2) estimates.phis_g phis_g;
  array_iter2 
    (fun arr1 arr2 ->
      array_modify2 (fun _ phi1 phi2 -> phi1 +. phi2) arr1 arr2
    ) estimates.phis phis

(* update all the tokens *)
let update_tokens fn data =
  List.iter (fun doc ->
    Array.iter (fun token ->
      fn params topics doc token
    ) doc.tokens
  ) data

(* calculate the log-likelihood *)
let log_likelihood topics_num thetas phis_g phis data =
  let lambda_inv = 1 -. lambda in
  List.fold_left (fun (acc,d) doc ->
    let corpus = doc.corpus in
    Array.fold_left (fun acc' token ->
      let id = token.id in
      let sum = 
        iterate (fun acc'' topic ->
          let a = (lambda_inv *. phis_g.(topic).(id)) +. (lambda *. phis.(corpus).(topic).(id)) in
          let b = thetas.(d).(topic) *. a
          acc'' +. b
        ) acc' topics_num
      in acc' +. log sum
    ) acc doc.tokens
    (acc, d + 1)
  ) ([], 0) data

(* run one iteration of the algorithm *)
let run_iter num params topics train_data test_data estimates =
  (* run over each token in the set *)
  update_tokens update_train_token train_data;
  (* calculate the new thetas and phis *)
  let new_thetas = Array.of_list @: List.map (fun doc ->
    calc_theta params.topics_num params.alpha doc
  ) data
  in
  let new_phis_g = Array.map (fun topic ->
    calc_phi params.beta topic
  ) topics.global_topics
  in
  let new_phis = Array.map (fun topic_arr ->
    Array.map (fun topic ->
      calc_phi params.beta topic
    ) topic_arr
  ) topics.global_topics
  (* if burn-in is passed, add to estimates *)
  if num > params.burn_in then
    add_to_estimates new_thetas new_phis_g new_phis estimates;
  (* run over each token in test data *)
  update_tokens (update_test_token new_phis_g new_phis) test_data;

let run params =
  let ts = params.topics_num in
  let train_data = init_probs ts @: init_model @: lines_of_file params.train_file in
  let test_data = init_probs ts @: init_model @: lines_of_file params.test_file in
  let g_topics = empty_global_topics_data ts Ids.word_types in
  (* initialize the counters *)
  init_cntrs g_topics train_data;
 

let main () =
  if Array.length Sys.argv <> 9 then
    Printf.printf 
      "%s input_train input_test output_file topics lambda alpha beta iterations burn-in"
      argv.(0)
  else 
    let params = {
      train_file = argv.(1);
      test_file = argv.(2);
      output_file = argv.(3);
      topic_num = ios argv.(4);
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

