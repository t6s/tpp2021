(* ocamlopt tpp2021.mli tpp2021.ml run2021.ml -o tpp2021.opt *)

open Tpp2021

let rec length_coq_list_aux acc = function
  | Nil -> acc
  | Cons (_, l) -> length_coq_list_aux (acc+1) l

let length_list l = length_coq_list_aux 0 l

let rec nat_of_int_aux acc n =
  if n <= 0 then acc else nat_of_int_aux (S acc) (n-1)

let nat_of_int n = nat_of_int_aux O n

let rec int_of_nat_aux acc = function
  | O -> acc
  | S n -> int_of_nat_aux (acc+1) n

let int_of_nat n = int_of_nat_aux 0 n

let () =
  let results = all_results (nat_of_int 6) in
  Printf.printf "%s = %d\n%s = %d\n%s = %d\n%s = %d\n%s = %d\n%!"
    "final boards" (int_of_nat results.total)
    "no paths" (int_of_nat results.no_path)
    "both colors" (int_of_nat results.both_colors)
    "only white" (int_of_nat results.only_white)
    "only black" (int_of_nat results.only_black)

(*
final boards = 59040
no paths = 26070
both colors = 1536
only white = 15717
only black = 15717

Extracted code takes 12s, vs 2s for a pure ocaml version.
*)
