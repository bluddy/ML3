type t

val empty_id : t 

val word_types : unit -> int

val id_of_str : string -> t
val str_of_id : t -> string
val id_of_str_many : string list -> t list
val str_of_id_many : t list -> string list

val id_of_str_pairs : string * string -> t * t
val str_of_id_pairs : t * t -> string * string

val id_of_str_arr : string array -> t array
val str_of_id_arr : t array -> string array

val sosa : t array -> string
val sosl : t list -> string
