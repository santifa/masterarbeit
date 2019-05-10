open Insert_sort


let print_nat n =
  let rec int_of_nat = function
    | O -> 0
    | S p -> 1+(int_of_nat p) in
  print_int (int_of_nat n)


let print_list = function
  | Nil -> print_string "[]"
  | Cons (t, q) ->
    print_string "["; print_nat t;
    let rec print_tail = function
      | Nil -> print_string "]"
      | Cons (x, xs) -> print_string "; "; print_nat x; print_tail xs in
    print_tail q


let _ =
  let zero = O in
  let one = S zero in
  let two = S one in
  let three = S two in
  let four = S three in
  let five = S four in
  let six = S five in
  let seven = S six in
  let eight = S seven in
  let nine = S eight in

  let l = Cons (seven, Cons (nine, Cons (five, Cons (three, Cons (zero, Cons (four, Cons (two, Cons (one, Cons (eight, Cons (six, Nil)))))))))) in
  print_list l; print_newline ();
  let l' = sort_spec l in
  print_list l'; print_newline ()
