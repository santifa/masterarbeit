module C  = ConfigParser
module NT = NuprlTerms
module PN = ParserNuprlAscii
module EV = Evaluators


(* ------ ARGUMENTS ------ *)

type args =
    {input   : string;
     output  : string;
     lib     : string;
     time    : int;
     sub     : bool;
     sanity  : bool;
     nuprl   : bool;
     obid    : string;
     ascii   : bool;
     tcheck  : bool;
     parse   : bool;
     split   : bool;
     prt     : bool;
     eval    : string option;
     alldef  : string;
     test    : int option;
     session : bool;
     simul   : string option;
     step    : int option;
     mono    : bool;
     host    : string;
     port    : int;
     conf    : string;
     client  : bool;
     send    : bool;
     other   : bool;
     all     : bool;
     ev      : string;
     id      : string;
     extra   : string;
     gc      : bool}

let default_el_output = "/tmp/eventml-output.el"
let default_output    = ""
let default_lib       = ""
let default_input     = "test.esh"
let default_time      = 1 (* 1sec by default *)
let default_sub       = false
let default_sanity    = false
let default_nuprl     = false
let default_obid      = ""
let default_ascii     = false
let default_tcheck    = false
let default_parse     = false
let default_split     = false
let default_prt       = false
let default_eval      = None
let default_alldef    = ""
let default_test      = None
let default_session   = false
let default_simul     = None
let default_step      = None
let default_mono      = false
let default_host      = "127.0.0.0"
let default_port      = 14567
let default_conf      = ""
let default_client    = false
let default_send      = false
let default_other     = false
let default_all       = false
let default_ev        = "ev2b" (* ev1 *)
let default_id        = ""
let default_extra     = ""
let default_gc        = false

let initArgs =
  {input   = default_input;
   output  = default_output;
   lib     = default_lib;
   time    = default_time;
   sub     = default_sub;
   sanity  = default_sanity;
   nuprl   = default_nuprl;
   obid    = default_obid;
   ascii   = default_ascii;
   tcheck  = default_tcheck;
   parse   = default_parse;
   split   = default_split;
   prt     = default_prt;
   eval    = default_eval;
   alldef  = default_alldef;
   test    = default_test;
   session = default_session;
   simul   = default_simul;
   step    = default_step;
   mono    = default_mono;
   host    = default_host;
   port    = default_port;
   conf    = default_conf;
   client  = default_client;
   send    = default_send;
   other   = default_other;
   all     = default_all;
   ev      = default_ev;
   id      = default_id;
   extra   = default_extra;
   gc      = default_gc}

let mk_args
    input   output lib    time   sub     sanity
    nuprl   obid   ascii  tcheck parse   split
    prt     eval   alldef test   session simul
    step    mono   host   port   conf    client
    send    other  all    ev     id      extra
    gc =
  {input   = input;
   output  = output;
   lib     = lib;
   time    = time;
   sub     = sub;
   sanity  = sanity;
   nuprl   = nuprl;
   obid    = obid;
   ascii   = ascii;
   tcheck  = tcheck;
   parse   = parse;
   split   = split;
   prt     = prt;
   eval    = eval;
   alldef  = alldef;
   test    = test;
   session = session;
   simul   = simul;
   step    = step;
   mono    = mono;
   host    = host;
   port    = port;
   conf    = conf;
   client  = client;
   send    = send;
   other   = other;
   all     = all;
   ev      = ev;
   id      = id;
   extra   = extra;
   gc      = gc}

let mk_args_ref
    input   output lib    time   sub     sanity
    nuprl   obid   ascii  tcheck parse   split
    prt     eval   alldef test   session simul
    step    mono   host   port   conf    client
    send    other  all    ev     id      extra
    gc =
  mk_args
    (!input)  (!output) (!lib)    (!time)   (!sub)     (!sanity)
    (!nuprl)  (!obid)   (!ascii)  (!tcheck) (!parse)   (!split)
    (!prt)    (!eval)   (!alldef) (!test)   (!session) (!simul)
    (!step)   (!mono)   (!host)   (!port)   (!conf)    (!client)
    (!send)   (!other)  (!all)    (!ev)     (!id)      (!extra)
    (!gc)

let getElOutput outop =
  match outop with
    Some output -> output
  | None -> default_el_output

let updInput   {input = _; output; lib; time; sub; sanity; nuprl; obid; ascii; tcheck; parse; split; prt; eval; alldef; test; session; simul; step; mono; host; port; conf; client; send; other; all; ev; id; extra; gc} input   = {input = input; output = output; lib = lib; time = time; sub = sub; sanity = sanity; nuprl = nuprl; obid = obid; ascii = ascii; tcheck = tcheck; parse = parse; split = split; prt = prt; eval = eval; alldef = alldef; test = test; session = session; simul = simul; step = step; mono = mono; host = host; port = port; conf = conf; client = client; send = send; other = other; all = all; ev = ev; id = id; extra = extra; gc = gc}
let updOutput  {input; output = _; lib; time; sub; sanity; nuprl; obid; ascii; tcheck; parse; split; prt; eval; alldef; test; session; simul; step; mono; host; port; conf; client; send; other; all; ev; id; extra; gc} output  = {input = input; output = output; lib = lib; time = time; sub = sub; sanity = sanity; nuprl = nuprl; obid = obid; ascii = ascii; tcheck = tcheck; parse = parse; split = split; prt = prt; eval = eval; alldef = alldef; test = test; session = session; simul = simul; step = step; mono = mono; host = host; port = port; conf = conf; client = client; send = send; other = other; all = all; ev = ev; id = id; extra = extra; gc = gc}
let updLib     {input; output; lib = _; time; sub; sanity; nuprl; obid; ascii; tcheck; parse; split; prt; eval; alldef; test; session; simul; step; mono; host; port; conf; client; send; other; all; ev; id; extra; gc} lib     = {input = input; output = output; lib = lib; time = time; sub = sub; sanity = sanity; nuprl = nuprl; obid = obid; ascii = ascii; tcheck = tcheck; parse = parse; split = split; prt = prt; eval = eval; alldef = alldef; test = test; session = session; simul = simul; step = step; mono = mono; host = host; port = port; conf = conf; client = client; send = send; other = other; all = all; ev = ev; id = id; extra = extra; gc = gc}
let updTime    {input; output; lib; time = _; sub; sanity; nuprl; obid; ascii; tcheck; parse; split; prt; eval; alldef; test; session; simul; step; mono; host; port; conf; client; send; other; all; ev; id; extra; gc} time    = {input = input; output = output; lib = lib; time = time; sub = sub; sanity = sanity; nuprl = nuprl; obid = obid; ascii = ascii; tcheck = tcheck; parse = parse; split = split; prt = prt; eval = eval; alldef = alldef; test = test; session = session; simul = simul; step = step; mono = mono; host = host; port = port; conf = conf; client = client; send = send; other = other; all = all; ev = ev; id = id; extra = extra; gc = gc}
let updSub     {input; output; lib; time; sub = _; sanity; nuprl; obid; ascii; tcheck; parse; split; prt; eval; alldef; test; session; simul; step; mono; host; port; conf; client; send; other; all; ev; id; extra; gc} sub     = {input = input; output = output; lib = lib; time = time; sub = sub; sanity = sanity; nuprl = nuprl; obid = obid; ascii = ascii; tcheck = tcheck; parse = parse; split = split; prt = prt; eval = eval; alldef = alldef; test = test; session = session; simul = simul; step = step; mono = mono; host = host; port = port; conf = conf; client = client; send = send; other = other; all = all; ev = ev; id = id; extra = extra; gc = gc}
let updSanity  {input; output; lib; time; sub; sanity = _; nuprl; obid; ascii; tcheck; parse; split; prt; eval; alldef; test; session; simul; step; mono; host; port; conf; client; send; other; all; ev; id; extra; gc} sanity  = {input = input; output = output; lib = lib; time = time; sub = sub; sanity = sanity; nuprl = nuprl; obid = obid; ascii = ascii; tcheck = tcheck; parse = parse; split = split; prt = prt; eval = eval; alldef = alldef; test = test; session = session; simul = simul; step = step; mono = mono; host = host; port = port; conf = conf; client = client; send = send; other = other; all = all; ev = ev; id = id; extra = extra; gc = gc}
let updNuprl   {input; output; lib; time; sub; sanity; nuprl = _; obid; ascii; tcheck; parse; split; prt; eval; alldef; test; session; simul; step; mono; host; port; conf; client; send; other; all; ev; id; extra; gc} nuprl   = {input = input; output = output; lib = lib; time = time; sub = sub; sanity = sanity; nuprl = nuprl; obid = obid; ascii = ascii; tcheck = tcheck; parse = parse; split = split; prt = prt; eval = eval; alldef = alldef; test = test; session = session; simul = simul; step = step; mono = mono; host = host; port = port; conf = conf; client = client; send = send; other = other; all = all; ev = ev; id = id; extra = extra; gc = gc}
let updObid    {input; output; lib; time; sub; sanity; nuprl; obid = _; ascii; tcheck; parse; split; prt; eval; alldef; test; session; simul; step; mono; host; port; conf; client; send; other; all; ev; id; extra; gc} obid    = {input = input; output = output; lib = lib; time = time; sub = sub; sanity = sanity; nuprl = nuprl; obid = obid; ascii = ascii; tcheck = tcheck; parse = parse; split = split; prt = prt; eval = eval; alldef = alldef; test = test; session = session; simul = simul; step = step; mono = mono; host = host; port = port; conf = conf; client = client; send = send; other = other; all = all; ev = ev; id = id; extra = extra; gc = gc}
let updAscii   {input; output; lib; time; sub; sanity; nuprl; obid; ascii = _; tcheck; parse; split; prt; eval; alldef; test; session; simul; step; mono; host; port; conf; client; send; other; all; ev; id; extra; gc} ascii   = {input = input; output = output; lib = lib; time = time; sub = sub; sanity = sanity; nuprl = nuprl; obid = obid; ascii = ascii; tcheck = tcheck; parse = parse; split = split; prt = prt; eval = eval; alldef = alldef; test = test; session = session; simul = simul; step = step; mono = mono; host = host; port = port; conf = conf; client = client; send = send; other = other; all = all; ev = ev; id = id; extra = extra; gc = gc}
let updTcheck  {input; output; lib; time; sub; sanity; nuprl; obid; ascii; tcheck = _; parse; split; prt; eval; alldef; test; session; simul; step; mono; host; port; conf; client; send; other; all; ev; id; extra; gc} tcheck  = {input = input; output = output; lib = lib; time = time; sub = sub; sanity = sanity; nuprl = nuprl; obid = obid; ascii = ascii; tcheck = tcheck; parse = parse; split = split; prt = prt; eval = eval; alldef = alldef; test = test; session = session; simul = simul; step = step; mono = mono; host = host; port = port; conf = conf; client = client; send = send; other = other; all = all; ev = ev; id = id; extra = extra; gc = gc}
let updParse   {input; output; lib; time; sub; sanity; nuprl; obid; ascii; tcheck; parse = _; split; prt; eval; alldef; test; session; simul; step; mono; host; port; conf; client; send; other; all; ev; id; extra; gc} parse   = {input = input; output = output; lib = lib; time = time; sub = sub; sanity = sanity; nuprl = nuprl; obid = obid; ascii = ascii; tcheck = tcheck; parse = parse; split = split; prt = prt; eval = eval; alldef = alldef; test = test; session = session; simul = simul; step = step; mono = mono; host = host; port = port; conf = conf; client = client; send = send; other = other; all = all; ev = ev; id = id; extra = extra; gc = gc}
let updSplit   {input; output; lib; time; sub; sanity; nuprl; obid; ascii; tcheck; parse; split = _; prt; eval; alldef; test; session; simul; step; mono; host; port; conf; client; send; other; all; ev; id; extra; gc} split   = {input = input; output = output; lib = lib; time = time; sub = sub; sanity = sanity; nuprl = nuprl; obid = obid; ascii = ascii; tcheck = tcheck; parse = parse; split = split; prt = prt; eval = eval; alldef = alldef; test = test; session = session; simul = simul; step = step; mono = mono; host = host; port = port; conf = conf; client = client; send = send; other = other; all = all; ev = ev; id = id; extra = extra; gc = gc}
let updPrint   {input; output; lib; time; sub; sanity; nuprl; obid; ascii; tcheck; parse; split; prt = _; eval; alldef; test; session; simul; step; mono; host; port; conf; client; send; other; all; ev; id; extra; gc} prt     = {input = input; output = output; lib = lib; time = time; sub = sub; sanity = sanity; nuprl = nuprl; obid = obid; ascii = ascii; tcheck = tcheck; parse = parse; split = split; prt = prt; eval = eval; alldef = alldef; test = test; session = session; simul = simul; step = step; mono = mono; host = host; port = port; conf = conf; client = client; send = send; other = other; all = all; ev = ev; id = id; extra = extra; gc = gc}
let updEval    {input; output; lib; time; sub; sanity; nuprl; obid; ascii; tcheck; parse; split; prt; eval = _; alldef; test; session; simul; step; mono; host; port; conf; client; send; other; all; ev; id; extra; gc} eval    = {input = input; output = output; lib = lib; time = time; sub = sub; sanity = sanity; nuprl = nuprl; obid = obid; ascii = ascii; tcheck = tcheck; parse = parse; split = split; prt = prt; eval = eval; alldef = alldef; test = test; session = session; simul = simul; step = step; mono = mono; host = host; port = port; conf = conf; client = client; send = send; other = other; all = all; ev = ev; id = id; extra = extra; gc = gc}
let updAlldef  {input; output; lib; time; sub; sanity; nuprl; obid; ascii; tcheck; parse; split; prt; eval; alldef = _; test; session; simul; step; mono; host; port; conf; client; send; other; all; ev; id; extra; gc} alldef  = {input = input; output = output; lib = lib; time = time; sub = sub; sanity = sanity; nuprl = nuprl; obid = obid; ascii = ascii; tcheck = tcheck; parse = parse; split = split; prt = prt; eval = eval; alldef = alldef; test = test; session = session; simul = simul; step = step; mono = mono; host = host; port = port; conf = conf; client = client; send = send; other = other; all = all; ev = ev; id = id; extra = extra; gc = gc}
let updTest    {input; output; lib; time; sub; sanity; nuprl; obid; ascii; tcheck; parse; split; prt; eval; alldef; test = _; session; simul; step; mono; host; port; conf; client; send; other; all; ev; id; extra; gc} test    = {input = input; output = output; lib = lib; time = time; sub = sub; sanity = sanity; nuprl = nuprl; obid = obid; ascii = ascii; tcheck = tcheck; parse = parse; split = split; prt = prt; eval = eval; alldef = alldef; test = test; session = session; simul = simul; step = step; mono = mono; host = host; port = port; conf = conf; client = client; send = send; other = other; all = all; ev = ev; id = id; extra = extra; gc = gc}
let updSession {input; output; lib; time; sub; sanity; nuprl; obid; ascii; tcheck; parse; split; prt; eval; alldef; test; session = _; simul; step; mono; host; port; conf; client; send; other; all; ev; id; extra; gc} session = {input = input; output = output; lib = lib; time = time; sub = sub; sanity = sanity; nuprl = nuprl; obid = obid; ascii = ascii; tcheck = tcheck; parse = parse; split = split; prt = prt; eval = eval; alldef = alldef; test = test; session = session; simul = simul; step = step; mono = mono; host = host; port = port; conf = conf; client = client; send = send; other = other; all = all; ev = ev; id = id; extra = extra; gc = gc}
let updSimul   {input; output; lib; time; sub; sanity; nuprl; obid; ascii; tcheck; parse; split; prt; eval; alldef; test; session; simul = _; step; mono; host; port; conf; client; send; other; all; ev; id; extra; gc} simul   = {input = input; output = output; lib = lib; time = time; sub = sub; sanity = sanity; nuprl = nuprl; obid = obid; ascii = ascii; tcheck = tcheck; parse = parse; split = split; prt = prt; eval = eval; alldef = alldef; test = test; session = session; simul = simul; step = step; mono = mono; host = host; port = port; conf = conf; client = client; send = send; other = other; all = all; ev = ev; id = id; extra = extra; gc = gc}
let updStep    {input; output; lib; time; sub; sanity; nuprl; obid; ascii; tcheck; parse; split; prt; eval; alldef; test; session; simul; step = _; mono; host; port; conf; client; send; other; all; ev; id; extra; gc} step    = {input = input; output = output; lib = lib; time = time; sub = sub; sanity = sanity; nuprl = nuprl; obid = obid; ascii = ascii; tcheck = tcheck; parse = parse; split = split; prt = prt; eval = eval; alldef = alldef; test = test; session = session; simul = simul; step = step; mono = mono; host = host; port = port; conf = conf; client = client; send = send; other = other; all = all; ev = ev; id = id; extra = extra; gc = gc}
let updMono    {input; output; lib; time; sub; sanity; nuprl; obid; ascii; tcheck; parse; split; prt; eval; alldef; test; session; simul; step; mono = _; host; port; conf; client; send; other; all; ev; id; extra; gc} mono    = {input = input; output = output; lib = lib; time = time; sub = sub; sanity = sanity; nuprl = nuprl; obid = obid; ascii = ascii; tcheck = tcheck; parse = parse; split = split; prt = prt; eval = eval; alldef = alldef; test = test; session = session; simul = simul; step = step; mono = mono; host = host; port = port; conf = conf; client = client; send = send; other = other; all = all; ev = ev; id = id; extra = extra; gc = gc}
let updHost    {input; output; lib; time; sub; sanity; nuprl; obid; ascii; tcheck; parse; split; prt; eval; alldef; test; session; simul; step; mono; host = _; port; conf; client; send; other; all; ev; id; extra; gc} host    = {input = input; output = output; lib = lib; time = time; sub = sub; sanity = sanity; nuprl = nuprl; obid = obid; ascii = ascii; tcheck = tcheck; parse = parse; split = split; prt = prt; eval = eval; alldef = alldef; test = test; session = session; simul = simul; step = step; mono = mono; host = host; port = port; conf = conf; client = client; send = send; other = other; all = all; ev = ev; id = id; extra = extra; gc = gc}
let updPort    {input; output; lib; time; sub; sanity; nuprl; obid; ascii; tcheck; parse; split; prt; eval; alldef; test; session; simul; step; mono; host; port = _; conf; client; send; other; all; ev; id; extra; gc} port    = {input = input; output = output; lib = lib; time = time; sub = sub; sanity = sanity; nuprl = nuprl; obid = obid; ascii = ascii; tcheck = tcheck; parse = parse; split = split; prt = prt; eval = eval; alldef = alldef; test = test; session = session; simul = simul; step = step; mono = mono; host = host; port = port; conf = conf; client = client; send = send; other = other; all = all; ev = ev; id = id; extra = extra; gc = gc}
let updConf    {input; output; lib; time; sub; sanity; nuprl; obid; ascii; tcheck; parse; split; prt; eval; alldef; test; session; simul; step; mono; host; port; conf = _; client; send; other; all; ev; id; extra; gc} conf    = {input = input; output = output; lib = lib; time = time; sub = sub; sanity = sanity; nuprl = nuprl; obid = obid; ascii = ascii; tcheck = tcheck; parse = parse; split = split; prt = prt; eval = eval; alldef = alldef; test = test; session = session; simul = simul; step = step; mono = mono; host = host; port = port; conf = conf; client = client; send = send; other = other; all = all; ev = ev; id = id; extra = extra; gc = gc}
let updClient  {input; output; lib; time; sub; sanity; nuprl; obid; ascii; tcheck; parse; split; prt; eval; alldef; test; session; simul; step; mono; host; port; conf; client = _; send; other; all; ev; id; extra; gc} client  = {input = input; output = output; lib = lib; time = time; sub = sub; sanity = sanity; nuprl = nuprl; obid = obid; ascii = ascii; tcheck = tcheck; parse = parse; split = split; prt = prt; eval = eval; alldef = alldef; test = test; session = session; simul = simul; step = step; mono = mono; host = host; port = port; conf = conf; client = client; send = send; other = other; all = all; ev = ev; id = id; extra = extra; gc = gc}
let updSend    {input; output; lib; time; sub; sanity; nuprl; obid; ascii; tcheck; parse; split; prt; eval; alldef; test; session; simul; step; mono; host; port; conf; client; send = _; other; all; ev; id; extra; gc} send    = {input = input; output = output; lib = lib; time = time; sub = sub; sanity = sanity; nuprl = nuprl; obid = obid; ascii = ascii; tcheck = tcheck; parse = parse; split = split; prt = prt; eval = eval; alldef = alldef; test = test; session = session; simul = simul; step = step; mono = mono; host = host; port = port; conf = conf; client = client; send = send; other = other; all = all; ev = ev; id = id; extra = extra; gc = gc}
let updOther   {input; output; lib; time; sub; sanity; nuprl; obid; ascii; tcheck; parse; split; prt; eval; alldef; test; session; simul; step; mono; host; port; conf; client; send; other = _; all; ev; id; extra; gc} other   = {input = input; output = output; lib = lib; time = time; sub = sub; sanity = sanity; nuprl = nuprl; obid = obid; ascii = ascii; tcheck = tcheck; parse = parse; split = split; prt = prt; eval = eval; alldef = alldef; test = test; session = session; simul = simul; step = step; mono = mono; host = host; port = port; conf = conf; client = client; send = send; other = other; all = all; ev = ev; id = id; extra = extra; gc = gc}
let updAll     {input; output; lib; time; sub; sanity; nuprl; obid; ascii; tcheck; parse; split; prt; eval; alldef; test; session; simul; step; mono; host; port; conf; client; send; other; all = _; ev; id; extra; gc} all     = {input = input; output = output; lib = lib; time = time; sub = sub; sanity = sanity; nuprl = nuprl; obid = obid; ascii = ascii; tcheck = tcheck; parse = parse; split = split; prt = prt; eval = eval; alldef = alldef; test = test; session = session; simul = simul; step = step; mono = mono; host = host; port = port; conf = conf; client = client; send = send; other = other; all = all; ev = ev; id = id; extra = extra; gc = gc}
let updEv      {input; output; lib; time; sub; sanity; nuprl; obid; ascii; tcheck; parse; split; prt; eval; alldef; test; session; simul; step; mono; host; port; conf; client; send; other; all; ev = _; id; extra; gc} ev      = {input = input; output = output; lib = lib; time = time; sub = sub; sanity = sanity; nuprl = nuprl; obid = obid; ascii = ascii; tcheck = tcheck; parse = parse; split = split; prt = prt; eval = eval; alldef = alldef; test = test; session = session; simul = simul; step = step; mono = mono; host = host; port = port; conf = conf; client = client; send = send; other = other; all = all; ev = ev; id = id; extra = extra; gc = gc}
let updId      {input; output; lib; time; sub; sanity; nuprl; obid; ascii; tcheck; parse; split; prt; eval; alldef; test; session; simul; step; mono; host; port; conf; client; send; other; all; ev; id = _; extra; gc} id      = {input = input; output = output; lib = lib; time = time; sub = sub; sanity = sanity; nuprl = nuprl; obid = obid; ascii = ascii; tcheck = tcheck; parse = parse; split = split; prt = prt; eval = eval; alldef = alldef; test = test; session = session; simul = simul; step = step; mono = mono; host = host; port = port; conf = conf; client = client; send = send; other = other; all = all; ev = ev; id = id; extra = extra; gc = gc}
let updExtra   {input; output; lib; time; sub; sanity; nuprl; obid; ascii; tcheck; parse; split; prt; eval; alldef; test; session; simul; step; mono; host; port; conf; client; send; other; all; ev; id; extra = _; gc} extra   = {input = input; output = output; lib = lib; time = time; sub = sub; sanity = sanity; nuprl = nuprl; obid = obid; ascii = ascii; tcheck = tcheck; parse = parse; split = split; prt = prt; eval = eval; alldef = alldef; test = test; session = session; simul = simul; step = step; mono = mono; host = host; port = port; conf = conf; client = client; send = send; other = other; all = all; ev = ev; id = id; extra = extra; gc = gc}
let updGc      {input; output; lib; time; sub; sanity; nuprl; obid; ascii; tcheck; parse; split; prt; eval; alldef; test; session; simul; step; mono; host; port; conf; client; send; other; all; ev; id; extra; gc = _} gc      = {input = input; output = output; lib = lib; time = time; sub = sub; sanity = sanity; nuprl = nuprl; obid = obid; ascii = ascii; tcheck = tcheck; parse = parse; split = split; prt = prt; eval = eval; alldef = alldef; test = test; session = session; simul = simul; step = step; mono = mono; host = host; port = port; conf = conf; client = client; send = send; other = other; all = all; ev = ev; id = id; extra = extra; gc = gc}

type arg =
    I       of string        (* input     *)
  | O       of string        (* ouput     *)
  | L       of string        (* library   *)
  | T       of int           (* timelimit *)
  | OBID    of string        (* object_id to use when generating the nuprl code *)
  | EVAL    of string        (* term to evaluate *)
  | DEF     of string        (* the alldef file  *)
  | TEST    of int
  | STEP    of int           (* to step through a protocl, by specifying (int) the message to send next *)
  | SIMUL   of string        (* simulate an EML program with a configuration file *)
  | HOST    of string        (* host name *)
  | PORT    of int           (* port number *)
  | CONF    of string        (* run an EML program in a distributed environment using a conf file *)
  | EV      of string        (* picks one of our Nuprl evaluator *)
  | ID      of string        (* machine identifier *)
  | EXTRA   of string        (* extra arguments *)
  | CLIENT                   (* start a dummy client *)
  | SEND                     (* send the initial messages in transit *)
  | OTHER                    (* run a `forward` machine *)
  | ALL                      (* simulates all the machines *)
  | SESSION
  | TONUPRL
  | SUBTYPING
  | SANITY
  | FROMASCII
  | TYPECHECK
  | PARSE
  | SPLIT
  | PRINT
  | MONO
  | GC

let format args =
  let rec gen lst r =
    match lst with
      [] -> r
    | SUBTYPING      :: list -> gen list (updSub     r true)
    | SANITY         :: list -> gen list (updSanity  r true)
    | FROMASCII      :: list -> gen list (updAscii   r true)
    | TYPECHECK      :: list -> gen list (updTcheck  r true)
    | PARSE          :: list -> gen list (updParse   r true)
    | SPLIT          :: list -> gen list (updSplit   r true)
    | PRINT          :: list -> gen list (updPrint   r true)
    | TONUPRL        :: list -> gen list (updNuprl   r true)
    | SESSION        :: list -> gen list (updSession r true)
    | MONO           :: list -> gen list (updMono    r true)
    | SEND           :: list -> gen list (updSend    r true)
    | OTHER          :: list -> gen list (updOther   r true)
    | CLIENT         :: list -> gen list (updClient  r true)
    | ALL            :: list -> gen list (updAll     r true)
    | GC             :: list -> gen list (updGc      r true)
    | (EXTRA   str)  :: list -> gen list (updExtra   r str)
    | (HOST    host) :: list -> gen list (updHost    r host)
    | (PORT    port) :: list -> gen list (updPort    r port)
    | (OBID    obid) :: list -> gen list (updObid    r obid)
    | (T       time) :: list -> gen list (updTime    r time)
    | (I       file) :: list -> gen list (updInput   r file)
    | (EV      ev)   :: list -> gen list (updEv      r ev)
    | (ID      id)   :: list -> gen list (updId      r id)
    | (CONF    file) :: list -> gen list (updConf    r file)
    | (SIMUL   file) :: list -> gen list (updSimul   r (Some file))
    | (STEP    n)    :: list -> gen list (updStep    r (Some n))
    | (TEST    n)    :: list -> gen list (updTest    r (Some n))
    | (EVAL    str)  :: list -> gen list (updEval    r (Some str))
    | (O       file) :: list -> gen list (updOutput  r file)
    | (L       file) :: list -> gen list (updLib     r file)
    | (DEF     file) :: list -> gen list (updAlldef  r file)
  in gen args initArgs


(* ------ A FEW GLOBAL VARIABLES ------ *)

let program : (string list * NT.nuprl_term) option ref = ref None

let default_alldefs = "/usr/fdl/lib/alldefs"

let loaded     = ref false
let configured = ref false

let components : (NT.nuprl_term * NT.nuprl_term) list ref = ref []
let intransit : NT.nuprl_term list ref = ref []

let process : NT.nuprl_term option ref = ref None

let reset_all () =
  (program    := None;
   components := [];
   intransit  := [];
   process    := None;
   ())

let ip_server = "127.0.0.1"
let port_server = 8987

let a_sock_ref = ref ([] : Unix.file_descr list)
let p_sock_ref = ref ([] : Unix.file_descr list)

let add_a_sock_ref sock = a_sock_ref := sock :: !a_sock_ref
let add_p_sock_ref sock = p_sock_ref := sock :: !p_sock_ref


(* ------ EXCEPTIONS ------ *)

exception NOT_FD
exception TRY_FD
exception RCV_INT of Unix.file_descr
exception RCV_SYS of Unix.file_descr
exception SEL_SYS of string

exception CONN_HANDLE
exception CONN_LOOP

exception DONE


(* ------ A FEW USEFUL FUNCTIONS ------ *)

let print_eml str = print_endline ("[" ^ str ^ "]")
let print_eml2 str = print_endline str

let rec implode chars =
  match chars with
    [] -> ""
  | char :: chars -> String.make 1 char ^ implode chars


(* ------ TYPES ------ *)

type extra =
    EX_INT  of int
  | EX_BOOL of bool
  | EX_DUMP
  | EX_HASKELL
  | EX_NSOCK
  | EX_NONE
  | EX_CBVA
  | EX_FOLD
  | EX_NPROG

type sock_info =
    {si_id    : NT.nuprl_term;
     si_thost : NT.nuprl_term;
     si_tport : NT.nuprl_term;
     si_sock  : Unix.file_descr}

type ident =
    Loc of string
  | Mac of string * int


(* ------ IDENTS ------ *)

let ident_to_string ident =
  match ident with
    Mac (host, port) -> "(" ^ host ^ "," ^ string_of_int port ^ ")"
  | Loc id -> id


(* ------ EXTRA ------ *)

let getExtra str =
  List.map
    (fun elt ->
      try EX_INT (int_of_string elt)
      with _ ->
	match str with
	  "true"    -> EX_BOOL true
	| "false"   -> EX_BOOL false
	| "T"       -> EX_BOOL true
	| "F"       -> EX_BOOL false
	| "newsock" -> EX_NSOCK
	| "fold"    -> EX_FOLD
	| "newprog" -> EX_NPROG
	| _         -> EX_NONE)
    (Str.split
       (Str.regexp "[ ,:;]")
       str)

let get_int_extra str =
  try
    Some (List.find
	    (fun ex -> match ex with (EX_INT n) -> true  | _ -> false)
	    (getExtra str))
  with _ -> None

let is_nsock_extra   str = List.exists (fun ex -> match ex with EX_NSOCK   -> true  | _ -> false) (getExtra str)
let is_fold_extra    str = List.exists (fun ex -> match ex with EX_FOLD    -> true  | _ -> false) (getExtra str)
let is_newprog_extra str = List.exists (fun ex -> match ex with EX_NPROG   -> true  | _ -> false) (getExtra str)


(* ------ TO STRING + DESTRUCTORS ------ *)

let addr_to_string sock_addr =
  match sock_addr with
    Unix.ADDR_UNIX str -> "(" ^ str ^ ")"
  | Unix.ADDR_INET (inet_addr, port) ->
      "(" ^ Unix.string_of_inet_addr inet_addr ^ "," ^ string_of_int port ^ ")"

let dest_inet_sockaddr sock_addr =
  match sock_addr with
    Unix.ADDR_UNIX str -> failwith "dest_inet_sockaddr"
  | Unix.ADDR_INET (inet_addr, port) -> (inet_addr, port)

let rec print_message_list n lst =
  match lst with
    [] -> ()
  | msg :: msgs ->
      (print_string (string_of_int n ^ ": " ^ NT.nuprlTerm2eml msg ^ "\n--\n");
       print_message_list (n + 1) msgs)

let print_messages_intransit () =
  (print_string ("\n-------IN-TRANSIT-------\n"); print_message_list 1 (!intransit))

let print_messages msgs =
    List.iter
    (fun msg ->
      ((*print (NT.toStringTerm msg ^ "msg" ^ "\n");*)
	print_string (NT.nuprlTerm2eml msg ^ "\n")))
  msgs


(* ------ SOCKET INFORMATION ------ *)

let mk_sock_info id thost tport sock =
  {si_id = id; si_thost = thost; si_tport = tport; si_sock = sock}

let select_id     (nfo : sock_info) = nfo.si_id
let select_socket (nfo : sock_info) = nfo.si_sock

let get_socks = List.map select_socket

let add_socket sock (id,thost,tport) = mk_sock_info id thost tport sock

let get_id_in_locs ident locations =
  match ident with
    Mac (ip, port) ->
      (try
	Some
	  (List.find
	     (fun (id,thost,tport) ->
	       let h = NT.dest_ihost thost in
	       let p = NT.dest_iport tport in
   (*val _ = print ("-" ^ h ^ "-" ^ Int.toString p ^ "-\n")*)
	       ip = h && port = p)
	     locations)
      with _ -> None)
  | Loc loc ->
      (try Some (List.find (fun (id,thost,tport) -> NT.dest_id id = loc) locations)
      with _ -> None)

let get_ip_port_in_locs loc locations =
    get_id_in_locs (Loc (NT.dest_id loc)) locations

let mk_client_sock_info sock addr =
  let (host,port) = dest_inet_sockaddr addr in
  let shost       = Unix.string_of_inet_addr host in
  let loc         = NT.mk_nuprl_mkid_term "client" in  (* Never used *)
  let thost       = NT.mk_nuprl_ihost_term shost in     (* Never used *)
  let tport       = NT.mk_nuprl_iport_term port in      (* Never used *)
  [mk_sock_info loc thost tport sock]


(* ------ CONFIGURATION FILE ------ *)

let load_config_parse_locations locs =
  List.map (fun (loc, host, port) ->
    (NT.mk_nuprl_mkid_term  loc,
     NT.mk_nuprl_ihost_term host,
     NT.mk_nuprl_iport_term port))
    locs

let load_config_parse_messages msgs =
  List.map (fun (id, (hdr, typ, body)) ->
    let pair = NT.mk_pair_term typ body in
    let msg  = NT.mk_pair_term hdr pair in
    (*val msg = NT.mk_nuprl_make_msg_term hdr typ body*)
    let pid = NT.mk_nuprl_mkid_term id in
    NT.mk_pair_term pid msg)
    msgs

let load_config_parse config =
  let (ls, ls', ps, ms) = C.parse config in
  let locations  = load_config_parse_locations ls in
  let locations' = load_config_parse_locations ls' in
  let messages   = load_config_parse_messages ms in
  (locations, locations', ps, messages)

let load_config_parse_str str =
  let (_,_,_,msgs) = C.parseString str
  in load_config_parse_messages msgs


(* ------ SOCKETS CLEANING ------ *)

let same_desc desc1 desc2 = failwith "TODO"

let rec clean_sockets desc lst =
  match lst with
    [] -> []
  | entry :: sockets ->
      let sock = select_socket entry in
      if same_desc sock desc
      then
	let _ = print_eml ("--removing from socket list")
	in clean_sockets desc sockets
      else entry :: (clean_sockets desc sockets)

let rec try_clean_sockets lst =
  match lst with
    [] -> (false,[])
  | entry :: socks ->
      let sock = select_socket entry in
      try
	let timeout    = (float 1) /. (float 1000) in
	let _          = Unix.getsockname sock in
	let _          = Unix.getpeername sock in
	let _          = Unix.select [sock] [] [] timeout in
	let (b,socks') = try_clean_sockets socks in
	(b, entry :: socks')
      with _ -> (print_eml ("--socket seems dead, removing it from list"); (true, socks))


(* ------ RECEIVE ------ *)

let receive_integer_gen n pref prt_msg desc rcv =
  try
    let rec loop b lst =
      let (str, len) = rcv 1 in
      if b && len = 0
      then (print_eml ("--error, received empty vector(" ^ string_of_int n ^ ")");
	    raise (RCV_INT desc))
      else if len = 1
      then
	let char = String.get str 0 in
	if char = '!'
	then lst
	else loop false (lst @ [char])
      else failwith ("receive_integer(" ^ string_of_int n ^ ")"
		     ^ ":bad_length"
		     ^ ":expecting_message_length_1_received_" ^ string_of_int len
		     ^ ":received_so_far_" ^ implode lst
		     ^ ":" ^ prt_msg
		     ^ "\n") in
    let chars = loop true [] in
    let str   = implode chars in
    (
     try Some (int_of_string (pref ^ str))
     with _ -> None
    )
  with err ->
    (print_eml ("--error, cannot receive integer, trying to recover(" ^ string_of_int n ^ ")");
     raise (RCV_SYS desc))

let receive_integer str sock =
  receive_integer_gen
    1
    ""
    str
    sock
    (fun n -> let str = String.create n in (str, Unix.recv sock str 0 n []))

let rec receive_message_sockets infd_op sockets =
  match sockets with
    [] -> 
      (print_eml ("no more sockets to read from");
       failwith "no more sockets to read from")
  | _ ->
      try
	let descs   = get_socks sockets in
	let timeout =
	  match infd_op with
	    Some _ -> float 1
	  | None   -> float (-1) in
	let (rds, wrs, exs) = Unix.select descs [] [] timeout in
	(match rds with
	  sock :: _ ->
	    let name = Unix.getsockname sock in
	    let peer = Unix.getpeername sock in
	    let nstr = addr_to_string name in
	    let pstr = addr_to_string peer in
	    let str  = "(name:" ^ nstr ^ ",peer:" ^ pstr ^ ")" in
	    (match receive_integer str sock with
	      Some n ->
		(
		 try
		   let str = String.create n in
		   let m   = Unix.recv sock str 0 n [] in
		   if m = n
		   then (str, false, sockets)
		   else failwith "receive_message_bad_length"
		 with _ ->
		   let _ = print_eml ("--error while sending vector, trying to recover") in
		   raise (RCV_SYS sock)
		)
	    | None -> failwith "receive_message:not_an_int")
	| [] -> raise TRY_FD)
      with
	RCV_INT desc ->
	  let _        = print_eml ("--cleaning socket list") in
	  let sockets' = clean_sockets desc sockets in
	  let _        = print_eml ("--retrying receive with new socket list") in
	  receive_message_sockets infd_op sockets'
      | RCV_SYS desc ->
	  let _        = print_eml ("--cleaning socket list") in
	  let sockets' = clean_sockets desc sockets in
	  let _        = print_eml ("--retrying receive with new socket list") in
	  receive_message_sockets infd_op sockets'
      | TRY_FD -> receive_message infd_op sockets
      | err ->
	  let _ = print_eml ("--error, cannot receive message (sockets)") in
	  let _ = print_eml ("--trying to find dead sockets") in
	  let (b,sockets') = try_clean_sockets sockets in
	  if b
	  then (print_eml ("--retrying receive with new socket list");
		receive_message_sockets infd_op sockets')
	  else (print_eml ("--system error, but sockets seem fine, failing");
		raise err)

(* How can we read from either sockets of infd? *)
and receive_message infd_op sockets =
  try
    (match infd_op with
      Some infd ->
	(*val _   = print ("[receive_message: trying to receive message from internal connection]\n");*)
	let rcv n = let str = String.create n in (str, Unix.read infd str 0 n) in
	let (str, m) = rcv 1 in
	(match receive_integer_gen 2 str "" infd rcv with
	  Some n ->
	    let (str, len) = rcv n in
	    if len = n
	    then (str, true, sockets)
	    else failwith "receive_message:bad_length"
	| None -> failwith "receive_message:fd")
    | None -> (print_eml ("receive_message: no internal connection");
	       raise NOT_FD))
  with
    Failure str -> (print_eml ("receive_message: Fail error occured(" ^ str ^ ")");
		    failwith str)
  | _ -> receive_message_sockets infd_op sockets

let receive_message' sockets =
  let (msgs, b, sockets') = receive_message None sockets in msgs


(* ------ DEBUG ------ *)

let parse_message_debug n string prt =
  try PN.parseString prt [] string
  with exn ->
    (print_string ("\n-EXC("
		   ^ string_of_int n
		   ^ ")----------------------\n"
		   ^ string
		   ^ "\n--------------------------\n");
     raise exn)


(* ------ MESSAGE PACKING ------ *)

let pack_message str =
  let len   = String.length str in
  let slen  = string_of_int len ^ "!" in
  (slen, str)

let pack_nuprl_message msg = pack_message (NT.toStringTerm msg)


(* ------ SEND ------ *)

let rec send_nuprl_messages_to_itself outfd lst =
  match lst with
    [] -> print_eml ("sent messages to myself")
  | msg :: msgs ->
      let (slen, slice) = pack_nuprl_message msg in
      let _ = Unix.write outfd slen 0 (String.length slen) in
      let _ = Unix.write outfd slice 0 (String.length slice) in
      send_nuprl_messages_to_itself outfd msgs


(* ------ NEW CONNECTIONS ------ *)

let handle_new_connection gc outfd sock addr =
  try
    let saddr   = addr_to_string addr in
    let _       = print_eml ("--received new connection request from " ^ saddr) in
    let sockets = mk_client_sock_info sock addr in
    let rec loop () =
      let msgstr = receive_message' sockets in
      let msgs   = parse_message_debug 1 msgstr false in
      let _      = print_eml ("--received input messages from " ^ saddr) in
      let _      = print_messages msgs in
      (*val _      = print "[--closing socket]\n"
	val _      = Socket.close sock*)
      let _      = print_eml "--sending message to myself" in
      let _      = send_nuprl_messages_to_itself outfd msgs in
      loop () in
    loop ()
  with _ -> raise CONN_HANDLE


(* ------ LISTENER ------ *)

let rec keep_listening_for_inputs_aux gc outfd server =
  try
    let (sock,addr) = Unix.accept server in
    let n = Unix.fork () in
    if n = 0
    then handle_new_connection gc outfd sock addr (* child *)
    else keep_listening_for_inputs_aux gc outfd server
  with
    CONN_HANDLE -> raise CONN_HANDLE
  | _           -> raise CONN_LOOP

let keep_listening_for_inputs gc outfd server =
  let _ = reset_all () in
  let _ = if gc then Gc.minor () else () in
  keep_listening_for_inputs_aux gc outfd server

let waiting_on_connection socket =
  let (sock,addr) = Unix.accept socket in
  let _           = add_a_sock_ref sock in
  let _           = print_eml ("--received connection request from " ^ addr_to_string addr) in
  let client_port =
    match receive_integer "" sock with
      Some p -> p
    | None -> failwith "connect_to_lower:received_non_int_data" in
  let _           = print_eml ("--received port number " ^ string_of_int client_port) in
  (sock,addr,client_port)

let remove_address_from_list addr port lst =
  let (ip,_) = dest_inet_sockaddr addr in
  let ips = Unix.string_of_inet_addr ip in
  List.partition
    (fun (id,thost,tport) ->
      let h = NT.dest_ihost thost in
      let p = NT.dest_iport tport in
      h = ips && p = port)
    lst

let rec connect_to_lower server lst =
  match lst with
    [] -> []
  | _ ->
      let n                = string_of_int (List.length lst) in
      let _                = print_eml ("--waiting on " ^ n ^ " connection(s)") in
      let (sock,addr,port) = waiting_on_connection server in
      let (connected,lst') = remove_address_from_list addr port lst in
      let sockets          = List.map (add_socket sock) connected in
      sockets @ (connect_to_lower server lst')

let create_new_socket ip port =
  let sock = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in (* a file_descr *)
  let addr = 
    try Unix.inet_addr_of_string ip
    with _ -> failwith ("create_server_socket:not_a_internet_address(" ^ ip ^ ")") in
  let sock_addr = Unix.ADDR_INET (addr, port) in
  let saddr     = addr_to_string sock_addr in
  (sock, sock_addr, saddr)

(* connect to server using socket.
 * It differs from connect by the fact that if it fails to connect,
 * it creates a new socket. *)
let rec connect' socket server =
  try
    let s = addr_to_string server in
    let _ = print_eml ("--n-connecting to " ^ s) in
    let _ = Unix.connect socket server in
    socket
  with _ ->
    let retry_limit = 2 in
    let st   = string_of_int retry_limit in
    let _    = print_eml ("--n-cannot connect, will retry in " ^ st ^ "s") in
    let _    = Unix.sleep retry_limit in
    let _    = print_eml ("--n-ready to retry, creating a new socket") in
    let sock = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
    connect' sock server

(* connect to server using socket *)
let rec connect socket server =
  try
    let s = addr_to_string server in
    let _ = print_eml ("--connecting to " ^ s) in
    let _ = Unix.connect socket server in
    socket
  with _ ->
    let retry_limit = 2 in
    let st = string_of_int retry_limit in
    let _  = print_eml ("--cannot connect, will retry in " ^ st ^ "s") in
    let _  = Unix.sleep retry_limit in
    let _  = print_eml ("--ready to retry") in
    connect socket server

let send_something sock str =
  try
    let (rds, wrs, exs) = Unix.select [] [sock] [] (float (-1)) in
    match wrs with
      [_] ->
	let _    = Unix.getsockname sock in
	let _    = Unix.getpeername sock in
	let n    = String.length str in
	(*val _    = print ("[--socket is ready, sending slice of length " ^ Int.toString n ^ "]\n")*)
	let _    = Unix.set_nonblock sock in
	let m    = Unix.send sock str 0 n [] in
	let _    = Unix.clear_nonblock sock in
	(*val _    = print ("[--checking that slice has been correctly sent]\n")*)
	if n = m
	then print_eml ("--successfully sent " ^ string_of_int m ^ "bytes")
	else print_eml ("--send_message:bag length(sent " ^ string_of_int m ^ ", should have sent " ^ string_of_int n ^ ")")
    | lst -> (print_eml ("--send_something:error: " ^ string_of_int (List.length lst) ^ " sockets writable");
	      failwith "send_something")
  with _ -> print_eml ("--error, cannot send message")

let filter_socks id nfo = NT.dest_id id = NT.dest_id (select_id nfo)

let send_message sockets loc str =
  try
    let {si_id;si_thost;si_tport;si_sock} = List.find (filter_socks loc) sockets in
    let _ = print_eml ("sending message to " ^ NT.toStringTerm loc) in
    let (slen, slice) = pack_message str in
    (*val _ = print ("[--sending length]\n")*)
    let _ = send_something si_sock slen in
    (*val _ = print ("[--length sent]\n")*)
    (*val _ = print ("[--sending slice]\n")*)
    let _ = send_something si_sock slice in
    (*val _ = print ("[--slice sent]\n")*)
    ()
  with _ -> print_eml ("recipient does not exist anymore, ignoring send request")

let send_port_number portop sock =
  match portop with
    Some port ->
      let pstr   = string_of_int port in
      let pslice = pstr ^ "!" in
      let _      = print_eml ("--sending port number " ^ pstr) in
      let _      = send_something sock pslice in
      ()
  | None -> ()

let rec connect_to_higher port nsock lst =
  match lst with
    [] -> []
  | ((id,thost,tport) as nfo) :: lst ->
      let n      = string_of_int (List.length lst + 1) in
      let _      = print_eml ("--still " ^ n ^ " machine(s) to connect to") in
      (* -- generates sock (a new socket) where thost is the host we have to connect to -- *)
      let (sock, server, saddr) = create_new_socket (NT.dest_ihost thost) (NT.dest_iport tport) in
      (* -- tries to connect to server using socket sock -- *)
      let sock =
	if nsock
	then connect' sock server
	else connect  sock server in
      (* -- sends port number to server -- *)
      let _      = send_port_number port sock in
      (add_socket sock nfo) :: (connect_to_higher port nsock lst)

let create_server_socket (ip, port) =
  let (sock, sock_addr, saddr) = create_new_socket ip port in
  let _ = print_eml ("created server socket at " ^ saddr) in
  let _ = Unix.setsockopt sock Unix.SO_REUSEADDR true in
  let _ = Unix.bind sock sock_addr in
  let _ = print_eml ("binding") in
  let _ = Unix.listen sock 100 in
  let _ = print_eml ("listening") in
  let _ = add_p_sock_ref sock in
  (sock, sock_addr)

let getParams params map_params =
  List.map
    (fun param ->
      try let (id,v) = List.find (fun (id, _) -> id = param) map_params in v
      with _ -> failwith ("get_params(" ^ param ^ ")"))
    params

let rec nuprl_all t   =
  if NT.is_nuprl_iclosure_term t
  then
    let (a,e) = NT.dest_iclosure t in
    NT.mk_nuprl_iclosure_term (nuprl_all a) e
  else NT.mk_nuprl_callbyvalueall_term t ("x", NT.mk_variable_term "x")

let rec nuprl_app p t =
  if NT.is_nuprl_iclosure_term p
  then
    let (a,e) = NT.dest_iclosure p in
    NT.mk_nuprl_iclosure_term (nuprl_app a t) e
  else NT.mk_apply_term p t

let load_program ev gc ident params id extra =
  match !program with
    Some (prms, p) ->
      let args      = getParams prms params in
      let _         = print_eml (string_of_int (List.length args) ^ " parameters") in
      let prog1     = NT.mk_nuprl_applies_term p args in
      let (prog2,_) = ev [] (-1) prog1 in
      let mng       =
	if is_newprog_extra extra
	then nuprl_app prog2 id
	else NT.mk_nuprl_df_program_meaning_term (nuprl_app prog2 id) in
      let _         = print_eml ("component loaded") in
      let (prog3,_) = ev [] (-1) mng in
      let _         = print_eml ("size: " ^ string_of_int (NT.size prog3)) in
      (* -- *)
      if is_fold_extra extra
      then prog3
      else
	let _         = print_eml ("unfolding term") in
	let lib       = EV.get_lib () in
	let prog4     = NT.unfold_all lib prog3 in
	let _         = print_eml ("term unfolded") in
	let _         = print_eml ("unloading library") in
	let _         = EV.reset_lib () in
	let _         = if gc then Gc.minor() else () in
	let _         = print_eml ("library unloaded") in
	(* -- *)
	(*val _         = print ("[size: " ^ Int.toString (NT.size prog4) ^ "]\n")*)
	prog4
  | None -> failwith "[no program]"

let rec split_locations (ip, port) lst =
  match lst with
    [] -> ([], [])
  | ((id, thost, tport) as nfo) :: lst ->
    let h = NT.dest_ihost thost in
    let p = NT.dest_iport tport in
    let (less, greater) = split_locations (ip, port) lst in
    let n = String.compare ip h in
    if n < 0
    then (less, nfo :: greater)
    else if n = 0
    then
      let m = compare port p in
      if m < 0
      then (less, nfo :: greater)
      else if m = 0
      then (less, greater)
      else (nfo :: less, greater)
    else (nfo :: less, greater)

let boot_up_prog ev gc ident spec lib alldefs id params extra =
  (* -- load library and generates program -- *)
  let _     = print_eml ("loading program and library") in
  let prt   = default_prt in
  let terms = PN.parse prt [] spec false in
  let terms =
    match terms with
      (prog :: rest) ->
	let (vars, _) = NT.dest_lambdas prog in
	let _ = program := Some (vars, prog) in
	rest
    | _ -> failwith "error, no program" in
  let _     =
    match alldefs with
      "" -> failwith "error, no library"
    | _ ->
	let _   = print_eml "parsing Nuprl library" in
	let ts  = PN.parse prt NT.to_filter_out alldefs false in
	let _   = print_eml "generating EML library" in
	let lib = NT.terms2map ts in
	let _   = NT.print_lib_stats lib in
	let _   = EV.start_session_lib lib in
	(*let _   = NT.dump_lib_termofs "output-termofs" lib in*)
	let _   = print_eml "library loaded" in
	(*let _   = print_eml (if NT.is_in_lib lib "at-prc" then "at-prc in lib" else "at-prc not in lib") in*)
	let _   = loaded := true in
	() in
  (* -- Add programs to library -- *)
  let _     = EV.add_to_session terms in
  (* -- Load component -- *)
  let _     = print_eml ("loading component") in
  load_program ev gc ident params id extra

let boot_up_conn nsock ip port locs locs' =
  (* -- Split the locations into those with lower ip/port and those with greater -- *)
  let (lt, gt) = split_locations (ip, port) locs in
  let lt_size  = string_of_int (List.length lt) in
  let gt_size  = string_of_int (List.length gt) in
  let _        = print_eml (lt_size ^ " lower machine(s), " ^ gt_size ^ " higher machine(s)") in
  (* -- create a server socket -- *)
  let _             = print_eml ("starting sever socket") in
  let (sock, addr)  = create_server_socket (ip, port) in
  (* -- wait to get the connections from machines with lower ip/port -- *)
  let _       = print_eml ("waiting on connections from lower machines") in
  let lst_lt  = connect_to_lower sock lt in
  (* -- Connect to machines with higher ip/port -- *)
  let _       = print_eml ("connecting to higher machines") in
  let lst_gt  = connect_to_higher (Some port) nsock gt in
  let _       = print_eml ("connecting to other machines") in
  let lst_ot  = connect_to_higher (Some port) nsock locs' in
  (sock, lst_lt @ lst_gt @ lst_ot)

let boot_up nsock ev gc ident config spec lib alldefs extra =
  (* ------ reading configuration file ------ *)
  let _     = print_eml ("loading configuration file") in
  let (locs, locs', params, msgs) = load_config_parse config in
  let _     = print_eml ("configuration file loaded") in
  let (id, loc, ip, port) =
    match get_id_in_locs ident locs (* extract own location *) with
      Some (id,thost,tport) ->
	let loc  = NT.dest_id id in
	let ip   = NT.dest_ihost thost in
	let port = NT.dest_iport tport in
	(id, loc, ip, port)
    | None -> failwith "[unknown location]\n" in
  (* -- *)
  (* ------ generating connections ------ *)
  let _     = print_eml ("connecting") in
  let (server, sockets) = boot_up_conn nsock ip port locs locs' in
  let (infd, outfd) = Unix.pipe () in
  let _     = Unix.set_nonblock infd in
  let n     = Unix.fork () in
  let _     =
    if n = 0
    then keep_listening_for_inputs gc outfd server (* child *)
    else print_eml ("forking listner: " ^ string_of_int n) in
  (* -- *)
  (* ------ loading program ------ *)
  let _     = print_eml ("loading program") in
  let prog  = boot_up_prog ev gc ident spec lib alldefs id params extra in
  (loc, prog, server, sockets, infd)

let send_nuprl_message sockets loc msg = send_message sockets loc (NT.toStringTerm msg)

let rec send_nuprl_messages loc sockets terms =
  match terms with
    [] -> []
  | term :: terms ->
      let (id, msg) = NT.dest_pair 5 term in
      if loc = NT.dest_id id
      then msg :: (send_nuprl_messages loc sockets terms)
      else
	let _ = send_nuprl_message sockets id msg in
	send_nuprl_messages loc sockets terms

let run_distributed_program2 nsock ev gc ident config spec lib alldefs prt extra =
  let _     = print_eml "booting up" in
  let (loc, term, server, sockets, infd) =
    boot_up nsock ev gc ident config spec lib alldefs extra in
  let _     = print_eml "running process" in
  let rec loop sockets internal_messages prog (*n*) =
    let progop =
      if is_newprog_extra extra
      then
	if NT.is_nuprl_inl_term prog
	then Some (NT.dest_inl prog)
	else if NT.is_nuprl_inr_term prog
	then None
	else failwith ("run_stepper:newprog:not_inl_or_inr(" ^ NT.opid_of_term prog ^ ")")
      else Some prog
    in match progop with
      Some prog ->
	let _ = if gc then Gc.minor() else () in
	let (msg, rest, sockets') =
	  match internal_messages with
	    [] ->
	      let _ = print_eml "process waiting for a new message" in
	      let (msgstr,b,sockets') = receive_message (Some infd) sockets in
	      (match parse_message_debug 3 msgstr prt with
		[msg] -> (msg, [],sockets')
	      | _ -> failwith "run_program")
	  | msg :: msgs -> (msg, msgs, sockets) in
	(* Note that this is not fair because all the internal
	 * messages will be dealt with first. *)
	(*val _             = print ("[size: " ^ Int.toString (NT.size prog) ^ "]\n")*)
	(*val _             = print ("[size: " ^ Int.toString (NT.size prog) ^ "," ^ Int.toString (NT.env_size prog) ^ "]\n")*)
	(*val _             = dump_prog_stream prog ("output-term-" ^ loc)*)
	let _             = print_eml "received message" in
	let _             = print_eml2 (NT.nuprlTerm2eml msg) in
	(*val _             = print (NT.toStringTerm msg ^ "\n")*)
	let toeval        = nuprl_all (nuprl_app prog msg) in
	let (prog1,steps) = ev [] (-1) toeval in
	let _             = print_eml (string_of_int steps ^ " steps") in
	let (prog2,msgs)  = NT.dest_pair 7 prog1 in
	let msgs_lst      = NT.dest_list msgs in
	let _             = print_eml ("sending messages(" ^ string_of_int (List.length msgs_lst) ^ ")") in
	let _             = print_message_list 1 msgs_lst in
	let msgs_slf      = send_nuprl_messages loc sockets' msgs_lst in
	let _             = print_eml "messages sent" in
	(*if n > k
	  then print ("[DONE]\n")
	  else*) loop sockets' (rest @ msgs_slf) prog2 (*(n+1)*)
    | None -> print_eml "program finished"
  in loop sockets [] term (*0*)

let run_distributed_program2_extra lim nsock ev gc ident config spec lib alldefs prt extra =
  let _     = print_eml "booting up" in
  let (loc, term, server, sockets, infd) =
    boot_up nsock ev gc ident config spec lib alldefs extra in
  let _     = print_eml "running process" in
  let rec loop sockets internal_messages prog n =
    let progop =
      if is_newprog_extra extra
      then
	if NT.is_nuprl_inl_term prog
	then Some (NT.dest_inl prog)
	else if NT.is_nuprl_inr_term prog
	then None
	else failwith ("run_stepper:newprog:not_inl_or_inr(" ^ NT.opid_of_term prog ^ ")")
      else Some prog
    in match progop with
      Some prog ->
	let (msg, rest, sockets') =
	  match internal_messages with
	    [] ->
	      (
	       let (msgstr,b,sockets') = receive_message (Some infd) sockets in
	       match parse_message_debug 4 msgstr prt with
		 [msg] -> (msg, [], sockets')
	       | _ -> failwith "run_program"
	      )
	  | msg :: msgs -> (msg, msgs, sockets) in
	(* Note that this is not fair because all the internal
	 * messages will be dealt with first. *)
	(*val _             = print_eml ("size: " ^ Int.toString (NT.size prog))*)
	(*val _             = print_eml ("size: " ^ Int.toString (NT.size prog) ^ "," ^ Int.toString (NT.env_size prog))*)
	(*val _             = dump_prog_stream prog ("output-term-" ^ loc)*)
	let _             = print_eml "received message" in
	let _             = print_eml2 (NT.nuprlTerm2eml msg) in
	let toeval        = nuprl_all (nuprl_app prog msg) in
	let (prog1,steps) = ev [] (-1) toeval in
	let _             = print_eml (string_of_int steps ^ " steps") in
	let (prog2,msgs)  = NT.dest_pair 8 prog1 in
	let msgs_lst      = NT.dest_list msgs in
	let _             = print_eml "sending messages" in
	let _             = print_message_list 1 msgs_lst in
	let msgs_slf      = send_nuprl_messages loc sockets msgs_lst in
	let _             = print_eml "messages sent" in
	if n > lim
	then print_eml "DONE"
	else loop sockets' (rest @ msgs_slf) prog2 (n + 1)
    | None -> print_eml "program finished"
  in loop sockets [] term 0

let run_distributed_program extra ev gc ident config spec lib alldefs prt =
  try
    let f =
      match get_int_extra extra with
	Some (EX_INT n) -> run_distributed_program2_extra n
      | _  -> run_distributed_program2 in
    let () = f (is_nsock_extra extra) ev gc ident config spec lib alldefs prt extra in
    let _ = print_eml "process terminated without error" in
    ()
  with
    CONN_HANDLE -> print_eml "connection handler died"
  | CONN_LOOP   -> print_eml "listner died"

let simulate_clients_server config =
  let (_, locs', _, _) = load_config_parse config in
  let sockets = connect_to_higher None false locs' in
  let rec loop sockets =
    let (msgstr,b,sockets') = receive_message_sockets None sockets in
    let _ = print_eml2 ("\n-------------\n"
			^ "received: "
			^ msgstr
			^ "\n-------------\n") in
    loop sockets' in
  loop sockets

let simulate_clients_send config alldefs prt gc =
  let lib =
    match alldefs with
    | "" -> NT.emlib ()
    | f ->
      let _     = print_eml ("parsing Nuprl library") in
      let terms = PN.parse prt NT.to_filter_out f false in
      let _     = print_eml ("generating EML library") in
      let lib   = NT.terms2map terms in
      let _     = NT.print_lib_stats lib in
      lib in
  let rec send_intransit_messages locs lst =
    match lst with
      [] -> ()
    |  dmsg :: msgs ->
	let (id,msg) = NT.dest_pair 10 dmsg in
	match get_ip_port_in_locs id locs with
	  Some ((id,thost,tport) as nfo) ->
	    let (sock,server,s) = create_new_socket (NT.dest_ihost thost) (NT.dest_iport tport) in
	    let _       = print_eml ("connecting to " ^ s) in
	    let _       = Unix.connect sock server in
	    let sockets = [add_socket sock nfo] in
	    let _       = print_eml ("sending message to " ^ s) in
	    let _       = send_nuprl_message sockets id msg in
	    let _       = print_eml "message sent" in
	    let _       = print_eml "closing socket" in
	    let _       = Unix.close sock in
	    let _       = print_eml "socket closed" in
	    send_intransit_messages locs msgs
	| None ->
	    let _ = print_eml "unknown location" in
	    send_intransit_messages locs msgs in
  let cid = ref 1 in
  let input aux =
    let _    = print_string "send? " in
    (match read_line () with
      ""    -> aux None
    | "sp" ->
	let c = string_of_int (!cid) in
	let _ = cid := !cid + 1 in
	aux (Some ("rep1 : (``swap``, (Int * Tok List), (" ^ c ^ ",``paxos``))"))
    | "st" ->
	let c = string_of_int (!cid) in
	let _ = cid := !cid + 1 in
	aux (Some ("rep1 : (``swap``, (Int * Tok List), (" ^ c ^ ",``2/3``))"))
    | "c" ->
	let c = string_of_int (!cid) in
	let _ = cid := !cid + 1 in
	aux (Some ("rep1 : (``request``, (Loc * (Int * Tok List)), (LOC(client), (" ^ c ^ ",``" ^ c ^ "``)))"))
    | msg   -> aux (Some msg)) in
  let rec aux msgop =
    let (locs, _, _, msgs) = load_config_parse config in
    let _ = print_eml "selecting message" in
    let msgs =
      match msgop with
	None -> msgs
      | Some msg -> load_config_parse_str msg in
    let _ = print_eml "selected message" in
    let time = Unix.gettimeofday () in
    let _    = print_eml ("unfolding messages(" ^ string_of_float time ^ "s)") in
    let msgs = List.map (NT.unfold_all lib) msgs in
    let _    = if gc then Gc.minor () else () in
    let time = Unix.gettimeofday () in
    let _    = print_eml ("sending intransit messages(" ^ string_of_float time ^ "s)") in
    let _    = send_intransit_messages locs msgs in
    input aux in
  input aux

let run_other_machine ident config prt =
  let (locs, locs', _, _) = load_config_parse config in
  (* -- checks whethere ip/port is in the configuration file -- *)
  let str = ident_to_string ident in
  let (loc,host,port) =
    match get_id_in_locs ident locs' with
      Some (id,thost,tport) -> (NT.dest_id id, NT.dest_ihost thost, NT.dest_iport tport)
    | None -> failwith ("[unknown location" ^ str ^ "]") in
  let _ = print_eml ("starting sever socket") in
  (* -- creates a server socket -- *)
  let (sock,addr) = create_server_socket (host, port) in
  let _ = print_eml ("connecting to machines") in
  (* -- waits on connection requests from the other machines -- *)
  let sockets = connect_to_lower sock locs in
  (* -- waits on a connection request from some client -- *)
  let (client,caddr) = Unix.accept sock in
  let (chost,cport) = dest_inet_sockaddr caddr in
  let scaddr  = addr_to_string caddr in
  let _       = print_eml ("--received connection request from " ^ scaddr) in
  let schost  = Unix.string_of_inet_addr chost in
  let cloc    = NT.mk_nuprl_mkid_term  "client" in
  let tchost  = NT.mk_nuprl_ihost_term schost in
  let tcport  = NT.mk_nuprl_iport_term cport in
  let clients = [mk_sock_info cloc tchost tcport client] in
  (* -- forwards to client messages received from internal locations --  *)
  let rec internal sockets =
    let (msgstr,b,sockets') = receive_message_sockets None sockets in
    let time = Unix.gettimeofday () in
    let _    = print_eml ("received message at " ^ string_of_float time ^ "s") in
    match parse_message_debug 7 msgstr prt with
      [msg] ->
	let str = NT.nuprlTerm2eml msg in
	let _ = send_message clients cloc str in
	internal sockets'
    | _ -> failwith "run_program" in
  internal sockets

let start_all_machines ev gc config spec lib alldefs prt =
  try
    let (locs, locs', _, _) = load_config_parse config in
    let _ =
      List.iter
	(fun (id,thost,tport) ->
	  let m = Unix.fork () in
	  if m = 0
	  then
	    let _ = run_other_machine (Loc (NT.dest_id id)) config prt
	    in raise DONE
	  else ())
	locs' in
    let _ =
      List.iter (fun (id,thost,tport) ->
	let m = Unix.fork () in
	if m = 0
	then
	  let _ = run_distributed_program "" ev gc (Loc (NT.dest_id id)) config spec lib alldefs prt
	  in raise DONE
	else ())
	locs in
    ()
  with DONE -> ()

(* ------ TIMER ------ *)

let start_timer () = Sys.time ()

let get_time timer =
  let time = Sys.time () in time -. timer

let string_of_time timer =
  let time = Sys.time () in string_of_float (time -. timer)

(* ------ EVALUATORS ------ *)

let eval_wrap ev ts n t =
  let timer = start_timer () in
  let res   = ev ts n t in
  let _     = print_eml ("timer:" ^ string_of_time timer) in
  res

let ev1  = EV.run_ev1_map
let ev2  = EV.run_ev2_map
let ev2b = EV.run_ev2b_map
let ev2c = EV.run_ev2c_map
let ev2d = EV.run_ev2d_map
let ev3  = EV.run_ev3_map
let ev3b = EV.run_ev3b_map
let ev3c = EV.run_ev3c_map
let ev3d = EV.run_ev3d_map
let ev4  = EV.run_ev4_map
let ev4b = EV.run_ev4b_map
let ev5  = EV.run_ev5_map
let ev5b = EV.run_ev5b_map

let ev1  = eval_wrap ev1
let ev2  = eval_wrap ev2
let ev2b = eval_wrap ev2b
let ev2c = eval_wrap ev2c
let ev2d = eval_wrap ev2d
let ev3  = eval_wrap ev3
let ev3b = eval_wrap ev3b
let ev3c = eval_wrap ev3c
let ev3d = eval_wrap ev3d
let ev4  = eval_wrap ev4
let ev4b = eval_wrap ev4b
let ev5  = eval_wrap ev5
let ev5b = eval_wrap ev5b

let get_ev ev =
  match ev with
    "ev1"  -> ("1",  ev1)
	(* 2nd evalutator *)
  | "ev2"  -> ("2",  ev2)
  | "ev2b" -> ("2b", ev2b)
  | "2b"   -> ("2b", ev2b)
  | "ev2c" -> ("2c", ev2c)
  | "2c"   -> ("2c", ev2c)
  | "ev2d" -> ("2d", ev2d)
  | "2d"   -> ("2d", ev2d)
	(* 3rd evalutator *)
  | "ev3"  -> ("3",  ev3)
  | "ev3b" -> ("3b", ev3b)
  | "3b"   -> ("3b", ev3b)
  | "ev3c" -> ("3c", ev3c)
  | "3c"   -> ("3c", ev3c)
  | "ev3d" -> ("3d", ev3d)
  | "3d"   -> ("3d", ev3d)
	(* 4th evalutator *)
  | "ev4"  -> ("4",  ev4)
  | "ev4b" -> ("4b", ev4b)
  | "4b"   -> ("4b", ev4b)
	(* 5th evalutator *)
  | "ev5"  -> ("5",  ev5)
  | "ev5b" -> ("5b", ev5b)
  | "5b"   -> ("5b", ev5b)
	(* failure *)
  | _ -> failwith "get_ev"

(* ------ INTERFACE ------ *)

let run
    {input;  output;  lib;     time;    sub;      sanity;
     nuprl;  obid;    ascii;   tcheck;  parse;    split;
     prt;    eval;    alldef;  test;    session;  simul;
     step;   mono;    host;    port;    conf;     client;
     send;   other;   all;     ev;      id;       extra;
     gc} =
  let _ = print_endline ("[starting program]") in
  let _ = not mono in
  let _ = true in
  let (_, ev) = try (get_ev ev) with _ -> get_ev default_ev in
  let ident = if id = "" then Mac (host, port) else Loc id in
  if conf = ""
  then print_endline ("[no configuration file]")
  else if client
  then simulate_clients_server conf
  else if send
  then simulate_clients_send conf alldef prt gc
  else if other
  then run_other_machine ident conf prt
  else if all
  then start_all_machines ev gc conf input lib alldef prt
  else run_distributed_program extra ev gc ident conf input lib alldef prt

let ref_default_el_output = ref "/tmp/eventml-output.el"
let ref_default_output    = ref ""
let ref_default_lib       = ref ""
let ref_default_input     = ref "test.esh"
let ref_default_time      = ref 1 (* 1sec by default *)
let ref_default_sub       = ref false
let ref_default_sanity    = ref false
let ref_default_nuprl     = ref false
let ref_default_obid      = ref ""
let ref_default_ascii     = ref false
let ref_default_tcheck    = ref false
let ref_default_parse     = ref false
let ref_default_split     = ref false
let ref_default_prt       = ref false
let ref_default_alldef    = ref ""
let ref_default_session   = ref false
let ref_default_mono      = ref false
let ref_default_host      = ref "127.0.0.0"
let ref_default_port      = ref 14567
let ref_default_conf      = ref ""
let ref_default_client    = ref false
let ref_default_send      = ref false
let ref_default_other     = ref false
let ref_default_all       = ref false
let ref_default_ev        = ref "ev2b" (* ev1 *)
let ref_default_id        = ref ""
let ref_default_extra     = ref ""
let ref_default_gc        = ref false

let x =
  let _ =
    Arg.parse
      [("--ascii",       Arg.Set ref_default_ascii,    "parse nuprl ascii file");
       ("-ascii",        Arg.Set ref_default_ascii,    "parse nuprl ascii file");
       ("--ascii-split", Arg.Set ref_default_split,    "split big ascii file");
       ("-ascii-split",  Arg.Set ref_default_split,    "split big ascii file");
       ("--sanitizer",   Arg.Set ref_default_sanity,   "runs sanity checker");
       ("-sanitizer",    Arg.Set ref_default_sanity,   "runs sanity checker");
       ("--sub",         Arg.Set ref_default_sub,      "turns on subtyping");
       ("-sub",          Arg.Set ref_default_sub,      "turns on subtyping");
       ("--print",       Arg.Set ref_default_prt,      "print debug information");
       ("-print",        Arg.Set ref_default_prt,      "print debug information");
       ("--nuprl",       Arg.Set ref_default_nuprl,    "converts EML to Nuprl");
       ("-nuprl",        Arg.Set ref_default_nuprl,    "converts EML to Nuprl");
       ("--session",     Arg.Set ref_default_session,  "starts an interactive EML session");
       ("-session",      Arg.Set ref_default_session,  "starts an interactive EML session");
       ("--mono",        Arg.Set ref_default_mono,     "monomorphic type checking");
       ("-mono",         Arg.Set ref_default_mono,     "monomorphic type checking");
       ("--client",      Arg.Set ref_default_client,   "runs clients");
       ("-client",       Arg.Set ref_default_client,   "runs clients");
       ("--send",        Arg.Set ref_default_send,     "send intransit messages");
       ("-semd",         Arg.Set ref_default_send,     "send intransit messages");
       ("--other",       Arg.Set ref_default_other,    "");
       ("-other",        Arg.Set ref_default_other,    "");
       ("--all",         Arg.Set ref_default_all,      "");
       ("-all",          Arg.Set ref_default_all,      "");
       ("--gc",          Arg.Set ref_default_gc,       "turns on GC");
       ("-gc",           Arg.Set ref_default_gc,       "turns on GC");
       ("--extra",       Arg.Set_string ref_default_extra,  "");
       ("-extra",        Arg.Set_string ref_default_extra,  "");
       ("--host",        Arg.Set_string ref_default_host,   "");
       ("-host",         Arg.Set_string ref_default_host,   "");
       ("--obid",        Arg.Set_string ref_default_obid,   "");
       ("-obid",         Arg.Set_string ref_default_obid,   "");
       ("--id",          Arg.Set_string ref_default_id,     "");
       ("-id",           Arg.Set_string ref_default_id,     "");
       ("--eval",        Arg.Set_string ref_default_ev,     "");
       ("-eval",         Arg.Set_string ref_default_ev,     "");
       ("--conf",        Arg.Set_string ref_default_conf,   "");
       ("-conf",         Arg.Set_string ref_default_conf,   "");
       ("--o",           Arg.Set_string ref_default_output, "");
       ("-o",            Arg.Set_string ref_default_output, "");
       ("--output",      Arg.Set_string ref_default_output, "");
       ("-output",       Arg.Set_string ref_default_output, "");
       ("--lib",         Arg.Set_string ref_default_lib,    "");
       ("-lib",          Arg.Set_string ref_default_lib,    "");
       ("--nuprl-defs",  Arg.Set_string ref_default_alldef, "");
       ("-nuprl-defs",   Arg.Set_string ref_default_alldef, "");
       ("--input",       Arg.Set_string ref_default_input,  "");
       ("-input",        Arg.Set_string ref_default_input,  "");
       ("--i",           Arg.Set_string ref_default_input,  "");
       ("-i",            Arg.Set_string ref_default_input,  "");
       ("--port",        Arg.Set_int ref_default_port, "");
       ("-port",         Arg.Set_int ref_default_port, "");
       ("--timelimit",   Arg.Set_int ref_default_time, "");
       ("-timelimit",    Arg.Set_int ref_default_time, "")]
      (fun str -> ())
      "EventML arguments" in
  let args =
    mk_args_ref
      ref_default_input   ref_default_output ref_default_lib    ref_default_time   ref_default_sub     ref_default_sanity
      ref_default_nuprl   ref_default_obid   ref_default_ascii  ref_default_tcheck ref_default_parse   ref_default_split
      ref_default_prt     (ref None)         ref_default_alldef (ref None)         ref_default_session (ref None)
      (ref None)          ref_default_mono   ref_default_host   ref_default_port   ref_default_conf    ref_default_client
      ref_default_send    ref_default_other  ref_default_all    ref_default_ev     ref_default_id      ref_default_extra
      ref_default_gc in
  run args
