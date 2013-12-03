open Util

type id = int

let empty_id = (-1)

(* save memory with hashtbl *)
let id_str_h = Hashtbl.create 100
let str_id_h = Hashtbl.create 100
let g_cnt = ref 0

let id_count () = !g_cnt

let add_id str =
    let id = !g_cnt in
    Hashtbl.add str_id_h str !g_cnt;
    Hashtbl.add id_str_h !g_cnt str;
    g_cnt := !g_cnt + 1;
    id

let id_of_str str = try Hashtbl.find str_id_h str 
  with Not_found -> add_id str

let str_of_id id = try Hashtbl.find id_str_h id
 with Not_found -> failwith @: "Bad id("^soi id^")!"

let id_of_str_many strs = List.map id_of_str strs
let str_of_id_many ids = List.map str_of_id ids

let id_of_str_pairs strs =
  List.map (fun (a,b) -> id_of_str a, id_of_str b) strs
let str_of_id_pairs ids =
  List.map (fun (a,b) -> str_of_id a, str_of_id b) ids

let id_of_str_arr strs = Array.map id_of_str strs
let str_of_id_arr ids = Array.map str_of_id ids

let sosa arr = string_of_string_array @: str_of_id_arr arr
let sosl l = string_of_string_list @: str_of_id_many l
