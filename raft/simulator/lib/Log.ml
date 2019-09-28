open Core
open Yojson

(* handy print functions with colored output *)
(* print error messages *)
let log_err thread msg =
  print_endline (Colors.kBRED ^ "Error:\t[" ^ thread ^ ": " ^ msg ^ "]" ^ Colors.kNRM);;

(* print info messages with c - color; t - message type; msg - message *)
let log_info thread msg =
  print_endline (Colors.kBLU ^ "Info:\t{" ^ thread ^ ": " ^ msg ^ "}" ^ Colors.kNRM);;

(* print results t - timestamp; d - elapsed time; avg - average *)
let log_res thread t d avg  =
  print_endline (Colors.kMAG ^ "Result:\t[Timestamp: " ^ thread
                 ^ "; elapsed time: " ^ (Batteries.String.of_list (Prelude.Time.time2string d))
                 ^ "; average: " ^ Batteries.String.of_list (Prelude.Time.time2string avg)
                 ^ "]" ^ Colors.kNRM);;

let log_test name msg =
  print_endline (Colors.kLGRN ^ "Test " ^ name ^ ":\t" ^ msg ^ Colors.kNRM);;

let log_msgs typ msgs =
  print_endline (Colors.kGRN ^ typ ^ " :\t" ^ msgs ^ Colors.kNRM);;

let log_state name node =
  print_endline (Colors.kCYN ^ "Node " ^ name ^ ":\t" ^ node ^ Colors.kNRM);;
