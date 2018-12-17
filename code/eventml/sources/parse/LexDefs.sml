structure LexDefs :> LEXDEFS = struct

(* shorten the names of structures *)
structure C = Comment
structure R = Reg

structure LENGTH = BinaryMapFn(type ord_key = int val compare = Int.compare)

type lengths = int LENGTH.map

val lengths = ref (LENGTH.empty : lengths)

fun addLength (row, col) = lengths := LENGTH.insert (!lengths, row, col)
fun getLength row = LENGTH.find (!lengths, row)
fun resetLengths () = lengths := LENGTH.empty

(* declare exceptions *)
exception LexError        of string * string * R.region list
exception BadCharacter    of string * R.region list
exception UnclosedComment of string * R.region list
exception UnclosedString  of string * R.region list
exception ClosedComment   of string * R.region list
exception BadAtomsClosing of string * R.region list

(* raises an exception with the msg, states the file and the regions
 * associated with the error *)
fun error (msg, file, regs) =
    raise LexError (file ^ ":" ^ msg, msg, regs)

(* various messeges detailing a problem in the code *)
val badcharStr = "ignoring bad character"
val uclcommStr = "unclosed comment at end of file"
val uclstrgStr = "unclosed string at end of file"
val unmatchStr = "unmatched closing comment"
val badclosStr = "atom or atom list is badly closed"

(* handlers for:
 * - a bad chraracter
 * - an unclosed comment in a file
 * - an unclosed string in a file
 * - an unmatched close comment (empty comment stack) *)
fun handleLex f x =
    (C.reset (); f x)
    handle
    BadCharacter    (file, regs) => error (badcharStr, file, regs)
  | UnclosedComment (file, regs) => error (uclcommStr, file, regs)
  | UnclosedString  (file, regs) => error (uclstrgStr, file, regs)
  | ClosedComment   (file, regs) => error (unmatchStr, file, regs)
  | BadAtomsClosing (file, regs) => error (badclosStr, file, regs)

(* we don't catch ParseError *)

end
