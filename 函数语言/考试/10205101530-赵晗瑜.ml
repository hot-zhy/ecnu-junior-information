(* 9. Define in OCaml the function (map2 f l1 l2), where f is a function 
that takes two parameters and l1 and l2 are lists, that calls f on each 
pair of corresponding elements from l1 and l2 and returns a list of the 
results. If l1 and l2 do not have the same number of elements. For example, 
the length is n1 for one list and n2 for the other, with n1 < n2, then f 
only operates on the first n1 elements for both lists. For example,

# map2 (fun x y -> x + y) [1;2;3;4] [5;6;7;8;9;10];;
  - : int list = [6; 8; 10; 12]

*) 
let rec map2 f l1 l2=
  match l1 with
  |[]->[]
  |h1::t1->match l2 with
           |[]->[]
           |h2::t2->
            (f h1 h2) :: map2 f t1 t2;;

map2 (fun x y->x+y) [1;2;3;4] [5;6;7;8;9;10];;


(* 10. We will define in OCaml the function (merge sort list), where list 
is an unsorted list of numbers, that implements merge sort and returns a 
new list containing the elements of list in sorted order. 
Let us proceed in three steps.

(a) Define a function (split l), where l is a list of integers, that returns a 
tuple of two lists, (l1, l2), such that half the elements of l are in l1 and half 
are in l2, in alternating order. For example,
# split [1];;
- : int list * int list = ([1], [])
          
# split [1;7;2;6;8;3;9;5;4];;
- : int list * int list = ([1; 2; 8; 9; 4], [7; 6; 3; 5])

*)
let split l =
  let rec split_aux l left right = 
    match l,left,right with
    | ([] | [_]),_,_ -> (List.rev left),right
    | (_::_::t),_,h::right_t -> split_aux t (h::left) right_t
    | _ -> assert false
  in
  split_aux l [] l;;

(*
(b) Define a function (merge l1 l2) that merges two lists sorted in ascending 
order into a new list, still in ascending order. For example,
         
# merge [1;3;5] [2;6;8];;
- : int list = [1; 2; 3; 5; 6; 8]

*)

let rec merge l1 l2 =
  match l1,l2 with
  | [],l | l,[] -> l
  | h1::t1,h2::t2 ->
    if h1<=h2 then h1::(merge t1 l2)
    else h2::(merge l1 t2);;
merge [1;3;5] [2;6;8];;

(*
(c) Now define the function (merge sort list) by making use of the two functions 
split and merge defined above to sort the list list. For example,

# merge_sort [2;4;1;6;9;6;4;1;3;5;10] ;;
- : int list = [1; 1; 2; 3; 4; 4; 5; 6; 6; 9; 10]
*)

let rec merge_sort l= 
  match l with
  | ([] | [_]) as l -> l
  | l ->  let left,right = split l in 
          merge (merge_sort left) (merge_sort right)
;;
merge_sort [2;4;1;6;9;6;4;1;3;5;10] ;;
