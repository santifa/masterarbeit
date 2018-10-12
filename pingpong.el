

parameter p: Loc
parameter locs: Loc Bag

(* base message classes : scope : base message name : header : location *)
internal ping:  ''ping''  Loc
internal pong:  ''ping''  Loc
input    start: ''start'' Loc
output   out:   ''out''   Loc

(* import types from nuprl *)
import bag-map

(* !!!!definition order is important!!!! *)
(* initial state which starts the circle *)
class SendPing loc = Output(\slf.{ping'send loc slf});;

(* replay to an incoming ping *)
class ReplyToPing =
  (\slf.\loc.{pong'send loc slf}) o ping'base;;

(* replay to an incoming pong *)
class ReplyToPong client loc =
  let F _ j = if loc=j then {out'send client loc} else {}
  in F o pong'base;;

(* main handler which repsonds to incoming request *)
class Handler (client, loc) = SendPing loc
                            || ReplyToPong client loc;;


class Delegate =
  let F _ client = bag-map (\loc.(client, loc)) locs
  in F o start'base;;

main (Delegate >>= Handler) @ {p} || ReplyToPing @ locs
