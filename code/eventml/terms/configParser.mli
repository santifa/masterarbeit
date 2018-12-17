type location    = string
type host        = string
type port        = int
type address     = location * host * port
type parameter   = string * NuprlTerms.nuprl_term
type message     = NuprlTerms.nuprl_term * NuprlTerms.nuprl_term * NuprlTerms.nuprl_term
type loc_message = location * message

val parse :
    string     (* file to parse *)
  -> (address list * address list * parameter list * loc_message list)

val parseString :
    string     (* string to parse *)
  -> (address list * address list * parameter list * loc_message list)
