(* Copyright 2011 Cornell University
 * Copyright 2012 Cornell University
 *
 *
 * This file is part of EventML - a tool aiming at specifying
 * distributed protocols in an ML like language.  It is an interface
 * to the logic of events and is compiled into Nuprl.  It is written
 * by the NUPRL group of Cornell University, Ithaca, NY.
 *
 * EventML is a free software: you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * EventML is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with EventML.  If not, see <http://www.gnu.org/licenses/>.
 *
 *  o Authors:     Vincent Rahli
 *  o Affiliation: Cornell University, NUPRL group
 *  o Date:        20 May 2011
 *  o File name:   Interface.sml
 *  o Description: EventML interface.
 *)


structure Interface :> INTERFACE = struct

structure P  = Parser
structure C  = ConfigParse
structure A  = Ast
structure E  = Enum
structure N  = ToNuprl
structure D  = Deps
structure G  = Gen
structure EN = Env
structure GL = GenLib
structure NT = NuprlTerms
structure EH = LibBase
structure EV = Evaluators
structure PN = ParserNuprlAscii


(* ------ ARGUMENTS ------ *)

val default_el_output = "/tmp/eventml-output.el"
val default_output    = NONE
val default_lib       = NONE
val default_input     = "test.esh"
val default_time      = LargeInt.fromInt 1000 (* 1sec by default *)
val default_sub       = false
val default_sanity    = false
val default_nuprl     = false
val default_obid      = ""
val default_ascii     = false
val default_tcheck    = false
val default_parse     = false
val default_split     = false
val default_prt       = false
val default_eval      = NONE
val default_alldef    = NONE
val default_test      = NONE
val default_session   = false
val default_simul     = NONE
val default_step      = NONE
val default_mono      = false
val default_host      = "127.0.0.0"
val default_port      = 14567
val default_conf      = NONE
val default_client    = false
val default_send      = false
val default_other     = false
val default_all       = false
val default_ev        = "ev2b" (* ev1 *)
val default_id        = ""
val default_extra     = ""
val default_gc        = false

val initArgs =
    {input   = default_input,
     output  = default_output,
     lib     = default_lib,
     time    = default_time,
     sub     = default_sub,
     sanity  = default_sanity,
     nuprl   = default_nuprl,
     obid    = default_obid,
     ascii   = default_ascii,
     tcheck  = default_tcheck,
     parse   = default_parse,
     split   = default_split,
     prt     = default_prt,
     eval    = default_eval,
     alldef  = default_alldef,
     test    = default_test,
     session = default_session,
     simul   = default_simul,
     step    = default_step,
     mono    = default_mono,
     host    = default_host,
     port    = default_port,
     conf    = default_conf,
     client  = default_client,
     send    = default_send,
     other   = default_other,
     all     = default_all,
     ev      = default_ev,
     id      = default_id,
     extra   = default_extra,
     gc      = default_gc}

fun getElOutput (SOME output) = output
  | getElOutput NONE = default_el_output

fun updInput   {input = _, output, lib, time, sub, sanity, nuprl, obid, ascii, tcheck, parse, split, prt, eval, alldef, test, session, simul, step, mono, host, port, conf, client, send, other, all, ev, id, extra, gc} input   = {input = input, output = output, lib = lib, time = time, sub = sub, sanity = sanity, nuprl = nuprl, obid = obid, ascii = ascii, tcheck = tcheck, parse = parse, split = split, prt = prt, eval = eval, alldef = alldef, test = test, session = session, simul = simul, step = step, mono = mono, host = host, port = port, conf = conf, client = client, send = send, other = other, all = all, ev = ev, id = id, extra = extra, gc = gc}
fun updOutput  {input, output = _, lib, time, sub, sanity, nuprl, obid, ascii, tcheck, parse, split, prt, eval, alldef, test, session, simul, step, mono, host, port, conf, client, send, other, all, ev, id, extra, gc} output  = {input = input, output = output, lib = lib, time = time, sub = sub, sanity = sanity, nuprl = nuprl, obid = obid, ascii = ascii, tcheck = tcheck, parse = parse, split = split, prt = prt, eval = eval, alldef = alldef, test = test, session = session, simul = simul, step = step, mono = mono, host = host, port = port, conf = conf, client = client, send = send, other = other, all = all, ev = ev, id = id, extra = extra, gc = gc}
fun updLib     {input, output, lib = _, time, sub, sanity, nuprl, obid, ascii, tcheck, parse, split, prt, eval, alldef, test, session, simul, step, mono, host, port, conf, client, send, other, all, ev, id, extra, gc} lib     = {input = input, output = output, lib = lib, time = time, sub = sub, sanity = sanity, nuprl = nuprl, obid = obid, ascii = ascii, tcheck = tcheck, parse = parse, split = split, prt = prt, eval = eval, alldef = alldef, test = test, session = session, simul = simul, step = step, mono = mono, host = host, port = port, conf = conf, client = client, send = send, other = other, all = all, ev = ev, id = id, extra = extra, gc = gc}
fun updTime    {input, output, lib, time = _, sub, sanity, nuprl, obid, ascii, tcheck, parse, split, prt, eval, alldef, test, session, simul, step, mono, host, port, conf, client, send, other, all, ev, id, extra, gc} time    = {input = input, output = output, lib = lib, time = time, sub = sub, sanity = sanity, nuprl = nuprl, obid = obid, ascii = ascii, tcheck = tcheck, parse = parse, split = split, prt = prt, eval = eval, alldef = alldef, test = test, session = session, simul = simul, step = step, mono = mono, host = host, port = port, conf = conf, client = client, send = send, other = other, all = all, ev = ev, id = id, extra = extra, gc = gc}
fun updSub     {input, output, lib, time, sub = _, sanity, nuprl, obid, ascii, tcheck, parse, split, prt, eval, alldef, test, session, simul, step, mono, host, port, conf, client, send, other, all, ev, id, extra, gc} sub     = {input = input, output = output, lib = lib, time = time, sub = sub, sanity = sanity, nuprl = nuprl, obid = obid, ascii = ascii, tcheck = tcheck, parse = parse, split = split, prt = prt, eval = eval, alldef = alldef, test = test, session = session, simul = simul, step = step, mono = mono, host = host, port = port, conf = conf, client = client, send = send, other = other, all = all, ev = ev, id = id, extra = extra, gc = gc}
fun updSanity  {input, output, lib, time, sub, sanity = _, nuprl, obid, ascii, tcheck, parse, split, prt, eval, alldef, test, session, simul, step, mono, host, port, conf, client, send, other, all, ev, id, extra, gc} sanity  = {input = input, output = output, lib = lib, time = time, sub = sub, sanity = sanity, nuprl = nuprl, obid = obid, ascii = ascii, tcheck = tcheck, parse = parse, split = split, prt = prt, eval = eval, alldef = alldef, test = test, session = session, simul = simul, step = step, mono = mono, host = host, port = port, conf = conf, client = client, send = send, other = other, all = all, ev = ev, id = id, extra = extra, gc = gc}
fun updNuprl   {input, output, lib, time, sub, sanity, nuprl = _, obid, ascii, tcheck, parse, split, prt, eval, alldef, test, session, simul, step, mono, host, port, conf, client, send, other, all, ev, id, extra, gc} nuprl   = {input = input, output = output, lib = lib, time = time, sub = sub, sanity = sanity, nuprl = nuprl, obid = obid, ascii = ascii, tcheck = tcheck, parse = parse, split = split, prt = prt, eval = eval, alldef = alldef, test = test, session = session, simul = simul, step = step, mono = mono, host = host, port = port, conf = conf, client = client, send = send, other = other, all = all, ev = ev, id = id, extra = extra, gc = gc}
fun updObid    {input, output, lib, time, sub, sanity, nuprl, obid = _, ascii, tcheck, parse, split, prt, eval, alldef, test, session, simul, step, mono, host, port, conf, client, send, other, all, ev, id, extra, gc} obid    = {input = input, output = output, lib = lib, time = time, sub = sub, sanity = sanity, nuprl = nuprl, obid = obid, ascii = ascii, tcheck = tcheck, parse = parse, split = split, prt = prt, eval = eval, alldef = alldef, test = test, session = session, simul = simul, step = step, mono = mono, host = host, port = port, conf = conf, client = client, send = send, other = other, all = all, ev = ev, id = id, extra = extra, gc = gc}
fun updAscii   {input, output, lib, time, sub, sanity, nuprl, obid, ascii = _, tcheck, parse, split, prt, eval, alldef, test, session, simul, step, mono, host, port, conf, client, send, other, all, ev, id, extra, gc} ascii   = {input = input, output = output, lib = lib, time = time, sub = sub, sanity = sanity, nuprl = nuprl, obid = obid, ascii = ascii, tcheck = tcheck, parse = parse, split = split, prt = prt, eval = eval, alldef = alldef, test = test, session = session, simul = simul, step = step, mono = mono, host = host, port = port, conf = conf, client = client, send = send, other = other, all = all, ev = ev, id = id, extra = extra, gc = gc}
fun updTcheck  {input, output, lib, time, sub, sanity, nuprl, obid, ascii, tcheck = _, parse, split, prt, eval, alldef, test, session, simul, step, mono, host, port, conf, client, send, other, all, ev, id, extra, gc} tcheck  = {input = input, output = output, lib = lib, time = time, sub = sub, sanity = sanity, nuprl = nuprl, obid = obid, ascii = ascii, tcheck = tcheck, parse = parse, split = split, prt = prt, eval = eval, alldef = alldef, test = test, session = session, simul = simul, step = step, mono = mono, host = host, port = port, conf = conf, client = client, send = send, other = other, all = all, ev = ev, id = id, extra = extra, gc = gc}
fun updParse   {input, output, lib, time, sub, sanity, nuprl, obid, ascii, tcheck, parse = _, split, prt, eval, alldef, test, session, simul, step, mono, host, port, conf, client, send, other, all, ev, id, extra, gc} parse   = {input = input, output = output, lib = lib, time = time, sub = sub, sanity = sanity, nuprl = nuprl, obid = obid, ascii = ascii, tcheck = tcheck, parse = parse, split = split, prt = prt, eval = eval, alldef = alldef, test = test, session = session, simul = simul, step = step, mono = mono, host = host, port = port, conf = conf, client = client, send = send, other = other, all = all, ev = ev, id = id, extra = extra, gc = gc}
fun updSplit   {input, output, lib, time, sub, sanity, nuprl, obid, ascii, tcheck, parse, split = _, prt, eval, alldef, test, session, simul, step, mono, host, port, conf, client, send, other, all, ev, id, extra, gc} split   = {input = input, output = output, lib = lib, time = time, sub = sub, sanity = sanity, nuprl = nuprl, obid = obid, ascii = ascii, tcheck = tcheck, parse = parse, split = split, prt = prt, eval = eval, alldef = alldef, test = test, session = session, simul = simul, step = step, mono = mono, host = host, port = port, conf = conf, client = client, send = send, other = other, all = all, ev = ev, id = id, extra = extra, gc = gc}
fun updPrint   {input, output, lib, time, sub, sanity, nuprl, obid, ascii, tcheck, parse, split, prt = _, eval, alldef, test, session, simul, step, mono, host, port, conf, client, send, other, all, ev, id, extra, gc} prt     = {input = input, output = output, lib = lib, time = time, sub = sub, sanity = sanity, nuprl = nuprl, obid = obid, ascii = ascii, tcheck = tcheck, parse = parse, split = split, prt = prt, eval = eval, alldef = alldef, test = test, session = session, simul = simul, step = step, mono = mono, host = host, port = port, conf = conf, client = client, send = send, other = other, all = all, ev = ev, id = id, extra = extra, gc = gc}
fun updEval    {input, output, lib, time, sub, sanity, nuprl, obid, ascii, tcheck, parse, split, prt, eval = _, alldef, test, session, simul, step, mono, host, port, conf, client, send, other, all, ev, id, extra, gc} eval    = {input = input, output = output, lib = lib, time = time, sub = sub, sanity = sanity, nuprl = nuprl, obid = obid, ascii = ascii, tcheck = tcheck, parse = parse, split = split, prt = prt, eval = eval, alldef = alldef, test = test, session = session, simul = simul, step = step, mono = mono, host = host, port = port, conf = conf, client = client, send = send, other = other, all = all, ev = ev, id = id, extra = extra, gc = gc}
fun updAlldef  {input, output, lib, time, sub, sanity, nuprl, obid, ascii, tcheck, parse, split, prt, eval, alldef = _, test, session, simul, step, mono, host, port, conf, client, send, other, all, ev, id, extra, gc} alldef  = {input = input, output = output, lib = lib, time = time, sub = sub, sanity = sanity, nuprl = nuprl, obid = obid, ascii = ascii, tcheck = tcheck, parse = parse, split = split, prt = prt, eval = eval, alldef = alldef, test = test, session = session, simul = simul, step = step, mono = mono, host = host, port = port, conf = conf, client = client, send = send, other = other, all = all, ev = ev, id = id, extra = extra, gc = gc}
fun updTest    {input, output, lib, time, sub, sanity, nuprl, obid, ascii, tcheck, parse, split, prt, eval, alldef, test = _, session, simul, step, mono, host, port, conf, client, send, other, all, ev, id, extra, gc} test    = {input = input, output = output, lib = lib, time = time, sub = sub, sanity = sanity, nuprl = nuprl, obid = obid, ascii = ascii, tcheck = tcheck, parse = parse, split = split, prt = prt, eval = eval, alldef = alldef, test = test, session = session, simul = simul, step = step, mono = mono, host = host, port = port, conf = conf, client = client, send = send, other = other, all = all, ev = ev, id = id, extra = extra, gc = gc}
fun updSession {input, output, lib, time, sub, sanity, nuprl, obid, ascii, tcheck, parse, split, prt, eval, alldef, test, session = _, simul, step, mono, host, port, conf, client, send, other, all, ev, id, extra, gc} session = {input = input, output = output, lib = lib, time = time, sub = sub, sanity = sanity, nuprl = nuprl, obid = obid, ascii = ascii, tcheck = tcheck, parse = parse, split = split, prt = prt, eval = eval, alldef = alldef, test = test, session = session, simul = simul, step = step, mono = mono, host = host, port = port, conf = conf, client = client, send = send, other = other, all = all, ev = ev, id = id, extra = extra, gc = gc}
fun updSimul   {input, output, lib, time, sub, sanity, nuprl, obid, ascii, tcheck, parse, split, prt, eval, alldef, test, session, simul = _, step, mono, host, port, conf, client, send, other, all, ev, id, extra, gc} simul   = {input = input, output = output, lib = lib, time = time, sub = sub, sanity = sanity, nuprl = nuprl, obid = obid, ascii = ascii, tcheck = tcheck, parse = parse, split = split, prt = prt, eval = eval, alldef = alldef, test = test, session = session, simul = simul, step = step, mono = mono, host = host, port = port, conf = conf, client = client, send = send, other = other, all = all, ev = ev, id = id, extra = extra, gc = gc}
fun updStep    {input, output, lib, time, sub, sanity, nuprl, obid, ascii, tcheck, parse, split, prt, eval, alldef, test, session, simul, step = _, mono, host, port, conf, client, send, other, all, ev, id, extra, gc} step    = {input = input, output = output, lib = lib, time = time, sub = sub, sanity = sanity, nuprl = nuprl, obid = obid, ascii = ascii, tcheck = tcheck, parse = parse, split = split, prt = prt, eval = eval, alldef = alldef, test = test, session = session, simul = simul, step = step, mono = mono, host = host, port = port, conf = conf, client = client, send = send, other = other, all = all, ev = ev, id = id, extra = extra, gc = gc}
fun updMono    {input, output, lib, time, sub, sanity, nuprl, obid, ascii, tcheck, parse, split, prt, eval, alldef, test, session, simul, step, mono = _, host, port, conf, client, send, other, all, ev, id, extra, gc} mono    = {input = input, output = output, lib = lib, time = time, sub = sub, sanity = sanity, nuprl = nuprl, obid = obid, ascii = ascii, tcheck = tcheck, parse = parse, split = split, prt = prt, eval = eval, alldef = alldef, test = test, session = session, simul = simul, step = step, mono = mono, host = host, port = port, conf = conf, client = client, send = send, other = other, all = all, ev = ev, id = id, extra = extra, gc = gc}
fun updHost    {input, output, lib, time, sub, sanity, nuprl, obid, ascii, tcheck, parse, split, prt, eval, alldef, test, session, simul, step, mono, host = _, port, conf, client, send, other, all, ev, id, extra, gc} host    = {input = input, output = output, lib = lib, time = time, sub = sub, sanity = sanity, nuprl = nuprl, obid = obid, ascii = ascii, tcheck = tcheck, parse = parse, split = split, prt = prt, eval = eval, alldef = alldef, test = test, session = session, simul = simul, step = step, mono = mono, host = host, port = port, conf = conf, client = client, send = send, other = other, all = all, ev = ev, id = id, extra = extra, gc = gc}
fun updPort    {input, output, lib, time, sub, sanity, nuprl, obid, ascii, tcheck, parse, split, prt, eval, alldef, test, session, simul, step, mono, host, port = _, conf, client, send, other, all, ev, id, extra, gc} port    = {input = input, output = output, lib = lib, time = time, sub = sub, sanity = sanity, nuprl = nuprl, obid = obid, ascii = ascii, tcheck = tcheck, parse = parse, split = split, prt = prt, eval = eval, alldef = alldef, test = test, session = session, simul = simul, step = step, mono = mono, host = host, port = port, conf = conf, client = client, send = send, other = other, all = all, ev = ev, id = id, extra = extra, gc = gc}
fun updConf    {input, output, lib, time, sub, sanity, nuprl, obid, ascii, tcheck, parse, split, prt, eval, alldef, test, session, simul, step, mono, host, port, conf = _, client, send, other, all, ev, id, extra, gc} conf    = {input = input, output = output, lib = lib, time = time, sub = sub, sanity = sanity, nuprl = nuprl, obid = obid, ascii = ascii, tcheck = tcheck, parse = parse, split = split, prt = prt, eval = eval, alldef = alldef, test = test, session = session, simul = simul, step = step, mono = mono, host = host, port = port, conf = conf, client = client, send = send, other = other, all = all, ev = ev, id = id, extra = extra, gc = gc}
fun updClient  {input, output, lib, time, sub, sanity, nuprl, obid, ascii, tcheck, parse, split, prt, eval, alldef, test, session, simul, step, mono, host, port, conf, client = _, send, other, all, ev, id, extra, gc} client  = {input = input, output = output, lib = lib, time = time, sub = sub, sanity = sanity, nuprl = nuprl, obid = obid, ascii = ascii, tcheck = tcheck, parse = parse, split = split, prt = prt, eval = eval, alldef = alldef, test = test, session = session, simul = simul, step = step, mono = mono, host = host, port = port, conf = conf, client = client, send = send, other = other, all = all, ev = ev, id = id, extra = extra, gc = gc}
fun updSend    {input, output, lib, time, sub, sanity, nuprl, obid, ascii, tcheck, parse, split, prt, eval, alldef, test, session, simul, step, mono, host, port, conf, client, send = _, other, all, ev, id, extra, gc} send    = {input = input, output = output, lib = lib, time = time, sub = sub, sanity = sanity, nuprl = nuprl, obid = obid, ascii = ascii, tcheck = tcheck, parse = parse, split = split, prt = prt, eval = eval, alldef = alldef, test = test, session = session, simul = simul, step = step, mono = mono, host = host, port = port, conf = conf, client = client, send = send, other = other, all = all, ev = ev, id = id, extra = extra, gc = gc}
fun updOther   {input, output, lib, time, sub, sanity, nuprl, obid, ascii, tcheck, parse, split, prt, eval, alldef, test, session, simul, step, mono, host, port, conf, client, send, other = _, all, ev, id, extra, gc} other   = {input = input, output = output, lib = lib, time = time, sub = sub, sanity = sanity, nuprl = nuprl, obid = obid, ascii = ascii, tcheck = tcheck, parse = parse, split = split, prt = prt, eval = eval, alldef = alldef, test = test, session = session, simul = simul, step = step, mono = mono, host = host, port = port, conf = conf, client = client, send = send, other = other, all = all, ev = ev, id = id, extra = extra, gc = gc}
fun updAll     {input, output, lib, time, sub, sanity, nuprl, obid, ascii, tcheck, parse, split, prt, eval, alldef, test, session, simul, step, mono, host, port, conf, client, send, other, all = _, ev, id, extra, gc} all     = {input = input, output = output, lib = lib, time = time, sub = sub, sanity = sanity, nuprl = nuprl, obid = obid, ascii = ascii, tcheck = tcheck, parse = parse, split = split, prt = prt, eval = eval, alldef = alldef, test = test, session = session, simul = simul, step = step, mono = mono, host = host, port = port, conf = conf, client = client, send = send, other = other, all = all, ev = ev, id = id, extra = extra, gc = gc}
fun updEv      {input, output, lib, time, sub, sanity, nuprl, obid, ascii, tcheck, parse, split, prt, eval, alldef, test, session, simul, step, mono, host, port, conf, client, send, other, all, ev = _, id, extra, gc} ev      = {input = input, output = output, lib = lib, time = time, sub = sub, sanity = sanity, nuprl = nuprl, obid = obid, ascii = ascii, tcheck = tcheck, parse = parse, split = split, prt = prt, eval = eval, alldef = alldef, test = test, session = session, simul = simul, step = step, mono = mono, host = host, port = port, conf = conf, client = client, send = send, other = other, all = all, ev = ev, id = id, extra = extra, gc = gc}
fun updId      {input, output, lib, time, sub, sanity, nuprl, obid, ascii, tcheck, parse, split, prt, eval, alldef, test, session, simul, step, mono, host, port, conf, client, send, other, all, ev, id = _, extra, gc} id      = {input = input, output = output, lib = lib, time = time, sub = sub, sanity = sanity, nuprl = nuprl, obid = obid, ascii = ascii, tcheck = tcheck, parse = parse, split = split, prt = prt, eval = eval, alldef = alldef, test = test, session = session, simul = simul, step = step, mono = mono, host = host, port = port, conf = conf, client = client, send = send, other = other, all = all, ev = ev, id = id, extra = extra, gc = gc}
fun updExtra   {input, output, lib, time, sub, sanity, nuprl, obid, ascii, tcheck, parse, split, prt, eval, alldef, test, session, simul, step, mono, host, port, conf, client, send, other, all, ev, id, extra = _, gc} extra   = {input = input, output = output, lib = lib, time = time, sub = sub, sanity = sanity, nuprl = nuprl, obid = obid, ascii = ascii, tcheck = tcheck, parse = parse, split = split, prt = prt, eval = eval, alldef = alldef, test = test, session = session, simul = simul, step = step, mono = mono, host = host, port = port, conf = conf, client = client, send = send, other = other, all = all, ev = ev, id = id, extra = extra, gc = gc}
fun updGc      {input, output, lib, time, sub, sanity, nuprl, obid, ascii, tcheck, parse, split, prt, eval, alldef, test, session, simul, step, mono, host, port, conf, client, send, other, all, ev, id, extra, gc = _} gc      = {input = input, output = output, lib = lib, time = time, sub = sub, sanity = sanity, nuprl = nuprl, obid = obid, ascii = ascii, tcheck = tcheck, parse = parse, split = split, prt = prt, eval = eval, alldef = alldef, test = test, session = session, simul = simul, step = step, mono = mono, host = host, port = port, conf = conf, client = client, send = send, other = other, all = all, ev = ev, id = id, extra = extra, gc = gc}

datatype arg = I       of string        (* input     *)
	     | O       of string        (* ouput     *)
	     | L       of string        (* library   *)
	     | T       of LargeInt.int  (* timelimit *)
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

fun format args =
    let fun gen [] r = r
	  | gen (SUBTYPING      :: list) r = gen list (updSub     r true)
	  | gen (SANITY         :: list) r = gen list (updSanity  r true)
	  | gen (FROMASCII      :: list) r = gen list (updAscii   r true)
	  | gen (TYPECHECK      :: list) r = gen list (updTcheck  r true)
	  | gen (PARSE          :: list) r = gen list (updParse   r true)
	  | gen (SPLIT          :: list) r = gen list (updSplit   r true)
	  | gen (PRINT          :: list) r = gen list (updPrint   r true)
	  | gen (TONUPRL        :: list) r = gen list (updNuprl   r true)
	  | gen (SESSION        :: list) r = gen list (updSession r true)
	  | gen (MONO           :: list) r = gen list (updMono    r true)
	  | gen (SEND           :: list) r = gen list (updSend    r true)
	  | gen (OTHER          :: list) r = gen list (updOther   r true)
	  | gen (CLIENT         :: list) r = gen list (updClient  r true)
	  | gen (ALL            :: list) r = gen list (updAll     r true)
	  | gen (GC             :: list) r = gen list (updGc      r true)
	  | gen ((EXTRA   str)  :: list) r = gen list (updExtra   r str)
	  | gen ((HOST    host) :: list) r = gen list (updHost    r host)
	  | gen ((PORT    port) :: list) r = gen list (updPort    r port)
	  | gen ((OBID    obid) :: list) r = gen list (updObid    r obid)
	  | gen ((T       time) :: list) r = gen list (updTime    r time)
	  | gen ((I       file) :: list) r = gen list (updInput   r file)
	  | gen ((EV      ev)   :: list) r = gen list (updEv      r ev)
	  | gen ((ID      id)   :: list) r = gen list (updId      r id)
	  | gen ((CONF    file) :: list) r = gen list (updConf    r (SOME file))
	  | gen ((SIMUL   file) :: list) r = gen list (updSimul   r (SOME file))
	  | gen ((STEP    n)    :: list) r = gen list (updStep    r (SOME n))
	  | gen ((TEST    n)    :: list) r = gen list (updTest    r (SOME n))
	  | gen ((EVAL    str)  :: list) r = gen list (updEval    r (SOME str))
	  | gen ((O       file) :: list) r = gen list (updOutput  r (SOME file))
	  | gen ((L       file) :: list) r = gen list (updLib     r (SOME file))
	  | gen ((DEF     file) :: list) r = gen list (updAlldef  r (SOME file))
    in gen args initArgs
    end

datatype extra = EX_INT  of int
	       | EX_BOOL of bool
	       | EX_DUMP
	       | EX_HASKELL
	       | EX_NSOCK
	       | EX_NONE
	       | EX_CBVA
	       | EX_FOLD
	       | EX_NPROG

fun getExtra str =
    let val lst = String.tokens (fn #" " => true
				  | #"," => true
				  | #":" => true
				  | #";" => true
				  | #"-" => true
				  | #"+" => true
				  | _    => false)
				str
	(*val str = ListFormat.fmt {init  = "",
				  final = "",
				  sep   = ":",
				  fmt   = fn x => x}
				 lst
	val _ = print ("[extras:" ^ str ^ "]\n")*)
    in map (fn elt =>
	       case Int.fromString elt of
		   SOME n => EX_INT n
		 | NONE =>
		   case elt of
		       "true"    => EX_BOOL true
		     | "false"   => EX_BOOL false
		     | "True"    => EX_BOOL true
		     | "False"   => EX_BOOL false
		     | "T"       => EX_BOOL true
		     | "F"       => EX_BOOL false
		     | "newsock" => EX_NSOCK
		     | "dump"    => EX_DUMP
		     | "haskell" => EX_HASKELL
		     | "cbva"    => EX_CBVA
		     | "fold"    => EX_FOLD
		     | "newprog" => EX_NPROG
		     | _         => EX_NONE)
	   lst
    end

fun is_true_extra    str = List.exists (fn (EX_BOOL b) => b    | _ => false) (getExtra str)
fun get_int_extra    str = List.find   (fn (EX_INT n)  => true | _ => false) (getExtra str)
fun is_nsock_extra   str = List.exists (fn EX_NSOCK    => true | _ => false) (getExtra str)
fun is_dump_extra    str = List.exists (fn EX_DUMP     => true | _ => false) (getExtra str)
fun is_haskell_extra str = List.exists (fn EX_HASKELL  => true | _ => false) (getExtra str)
fun is_cbva_extra    str = List.exists (fn EX_CBVA     => true | _ => false) (getExtra str)
fun is_fold_extra    str = List.exists (fn EX_FOLD     => true | _ => false) (getExtra str)
fun is_newprog_extra str = List.exists (fn EX_NPROG    => true | _ => false) (getExtra str)

datatype ident = Loc of string
	       | Mac of string * int

fun ident_to_string (Mac (host, port)) = "(" ^ host ^ "," ^ Int.toString port ^ ")"
  | ident_to_string (Loc id) = id


(* ------ A FEW GLOBAL VARIABLES ------ *)

val program = ref NONE : (string list * NT.nuprl_term) option ref

val default_alldefs = "/usr/fdl/lib/alldefs"

val loaded     = ref false
val configured = ref false

val components = ref [] : (NT.nuprl_term * NT.nuprl_term) list ref
val intransit  = ref [] : NT.nuprl_term list ref

val process : NT.nuprl_term option ref = ref NONE

fun reset_all () =
    (program    := NONE;
     components := [];
     intransit  := [];
     process    := NONE;
    ())

(* ------ TIMER ------ *)

type timer = {real : Timer.real_timer,
	      cpu  : Timer.cpu_timer}

fun startTimer () = {real = Timer.startRealTimer (),
		     cpu  = Timer.startCPUTimer  ()}
fun getTime (timer : timer) = Timer.checkRealTimer (#real timer)
fun getMilliTime timer = Time.toMilliseconds (getTime timer)


(* ------ EVALUATORS ------ *)

fun eval_wrap ev ts n t =
    let val timer = startTimer ()
	val res   = ev ts n t
	val time  = getMilliTime timer
	val _     = print ("[" ^ LargeInt.toString time ^ "ms]\n")
    in res
    end

val ev1  = EV.run_ev1_map
val ev2  = EV.run_ev2_map
val ev2b = EV.run_ev2b_map
val ev2c = EV.run_ev2c_map
val ev2d = EV.run_ev2d_map
val ev3  = EV.run_ev3_map
val ev3b = EV.run_ev3b_map
val ev3c = EV.run_ev3c_map
val ev3d = EV.run_ev3d_map
val ev4  = EV.run_ev4_map
val ev4b = EV.run_ev4b_map
val ev5  = EV.run_ev5_map
val ev5b = EV.run_ev5b_map

val ev1  = eval_wrap ev1
val ev2  = eval_wrap ev2
val ev2b = eval_wrap ev2b
val ev2c = eval_wrap ev2c
val ev2d = eval_wrap ev2d
val ev3  = eval_wrap ev3
val ev3b = eval_wrap ev3b
val ev3c = eval_wrap ev3c
val ev3d = eval_wrap ev3d
val ev4  = eval_wrap ev4
val ev4b = eval_wrap ev4b
val ev5  = eval_wrap ev5
val ev5b = eval_wrap ev5b

fun get_ev "ev1"  = ("1",  ev1)
  (* 2nd evalutator *)
  | get_ev "ev2"  = ("2",  ev2)
  | get_ev "ev2b" = ("2b", ev2b)
  | get_ev "2b"   = ("2b", ev2b)
  | get_ev "ev2c" = ("2c", ev2c)
  | get_ev "2c"   = ("2c", ev2c)
  | get_ev "ev2d" = ("2d", ev2d)
  | get_ev "2d"   = ("2d", ev2d)
  (* 3rd evalutator *)
  | get_ev "ev3"  = ("3",  ev3)
  | get_ev "ev3b" = ("3b", ev3b)
  | get_ev "3b"   = ("3b", ev3b)
  | get_ev "ev3c" = ("3c", ev3c)
  | get_ev "3c"   = ("3c", ev3c)
  | get_ev "ev3d" = ("3d", ev3d)
  | get_ev "3d"   = ("3d", ev3d)
  (* 4th evalutator *)
  | get_ev "ev4"  = ("4",  ev4)
  | get_ev "ev4b" = ("4b", ev4b)
  | get_ev "4b"   = ("4b", ev4b)
  (* 5th evalutator *)
  | get_ev "ev5"  = ("5",  ev5)
  | get_ev "ev5b" = ("5b", ev5b)
  | get_ev "5b"   = ("5b", ev5b)
  (* failure *)
  | get_ev _ = raise Fail "get_ev"


(* ------ PARSING ------ *)

fun parseEML input =
    let val _    = D.reset ()
	val term = P.parse [input]
	val st1  = A.export term
	val st2  = A.toString term
	val _    = print (st1 ^ "\n")
	val _    = print (st2 ^ "\n")
    in ()
    end


(* ------ EVALUATION ------ *)

fun getLastAbstraction [] = (NONE, [])
  | getLastAbstraction lst =
    let val rev    = List.rev lst
	val last   = List.hd rev
	val firsts = List.rev (List.tl rev)
    in if NT.is_nuprl_iabstraction_term last
       then (SOME (NT.dest_iabstraction last), [])
       else let val (termop, terms) = getLastAbstraction firsts
	    in (termop, terms @ [last])
	    end
    end

fun keepAbsWf [] = []
  | keepAbsWf (term :: terms) =
    if NT.is_nuprl_iabstraction_term term
       orelse
       NT.is_nuprl_iwftheorem_term term
    then term :: keepAbsWf terms
    else keepAbsWf terms

fun pairAbsWf [] = []
  | pairAbsWf [x] = raise EH.Impossible "pairAbsWf"
  | pairAbsWf (abs :: wf :: terms) =
    if NT.is_nuprl_iabstraction_term abs
       andalso
       NT.is_nuprl_iwftheorem_term wf
    then (abs, wf) :: pairAbsWf terms
    else raise EH.Impossible "pairAbsWf"

fun splitLastAbs terms =
    let val terms' = keepAbsWf terms
	val pairs  = pairAbsWf terms'
	val rev    = List.rev pairs
    in if List.length rev > 0
       then let val (abs, wf) = List.hd rev
		val firsts = List.rev (List.tl rev)
	    in (SOME (NT.dest_iabstraction abs, wf), firsts)
	    end
       else (NONE, [])
    end

fun terms2sub terms =
    map (fn (abs,wf) =>
	    let val (cond,lhs,rhs)  = NT.dest_iabstraction abs
		val (opid,subterms) = NT.dest_simple_term (NT.rterm2term lhs)
	    in case subterms of
		   [] => (opid,NT.rterm2term rhs)
		 | _  => raise Fail "terms2sub:term-has-subterms"
	    end)
	terms

fun copy_file filein fileout =
    let val instream  = TextIO.openIn filein
	val outstream = TextIO.openOut fileout
	fun aux () =
	    case TextIO.inputLine instream of
		SOME line => (TextIO.output (outstream, line); aux ())
	      | NONE => ()
	val _ = aux ()
	val _ = TextIO.closeIn instream
	val _ = TextIO.closeOut outstream
    in ()
    end

fun evaluate_gen ev input str libop obid sub prt btyp extra =
    let val _        = D.reset ()
	val (n,str)  = case String.tokens (fn #"%" => true | _ => false) str of
			   [n,x] => (case Int.fromString n of
					 SOME m => (m,x)
				       | NONE => (~1,str))
			 | _ => (~1,str)
	(*val n = ~1*)
	(*val _        = print ("[" ^ str ^ " will be evaluated in " ^ Int.toString n ^ " steps]\n")*)
	val tmp      = OS.FileSys.tmpName ()
	val _        = copy_file input tmp
	val stout    = TextIO.openAppend tmp
	val _        = TextIO.output (stout, "let it = " ^ str ^ "\n")
	val _        = TextIO.closeOut stout
	val san      = true
    in let val (term, env, b) = E.slice [tmp] NONE libop 1 prt sub san btyp
       in if b
	  then let val s_term        = A.simplify term
		   val lib           = NONE
		   val pref          = false
		   val poly          = true
		   val stdma         = true
		   val cbva          = is_cbva_extra extra
		   val newprog       = is_newprog_extra extra
		   val (n_terms1, _) = N.toNuprl lib tmp obid s_term env sub pref poly stdma btyp cbva newprog
		   val _             = OS.FileSys.remove tmp
	       in case splitLastAbs n_terms1 of
		      (SOME ((r_cond, r_left, r_right), wf), terms) =>
		      let val left   = NT.rterm2term r_left
			  val right  = NT.rterm2term r_right
			  (*val _      = print (NT.toStringTerm left  ^ "\n***********\n")*)
			  (*val _      = print (NT.toStringTerm right ^ "\n***********\n")*)
			  (*val _      = print (NT.toStringTerm wf    ^ "\n***********\n")*)
			  (*val _      = app (fn (abs,wf) => print (NT.toStringTerm abs ^ "\n***********\n")) terms*)
			  val right1 = NT.replace_terms (terms2sub terms) right
			  (*val _      = print (NT.toStringTerm right1 ^ "\n***********\n")*)
			  (*val _      = print ("[evaluating rhs]\n")*)
			  (*val right2 = ev (NT.mk_nuprl_evalall_term right) terms n*)
			  val right2 = ev (NT.mk_nuprl_evalall_term right1) [] n
			  (*val _      = print ("[evaluation done]\n")*)
			  val abs    = NT.mk_nuprl_iabstraction_term left right2
			  val thm    = NT.dest_iwftheorem wf
			  val sta    = NT.nuprl2eml_abs "it" abs
			  val stw    = NT.nuprl2eml_wf  "it" wf
			  (*val _ = print (NT.toStringTerm wf)*)
			  val _ =
			      if sta = "-"
				 andalso
				 n >= 0
			      then print (NT.ppTerm right2 ^ "\n")
			      else if sta = "`???`"
			      then print ("evaluation failed.\n")
			      else print (sta ^ " : " ^ stw ^ "\n")
		      (*app (fn t => print (NT.nuprl2eml t ^ "\n")) [abs, wf]*)
		      in ()
		      end
		    | _ => ()
	       end
	  else print "Untypable.\n"
       end handle e => ((OS.FileSys.remove tmp; raise e) handle _ => raise e)
    end

fun evaluate input str libop alldefop obid sub extra =
    evaluate_gen (fn t => fn ts => fn s => #1 (EV.run_ev2b true alldefop ts s t))
		 input str libop obid sub (true, true) true extra

fun evaluate_map ev input str libop obid sub btyp extra =
    evaluate_gen (fn t => fn ts => fn s => let val (u, n) = ev ts s t in u end)
		 input str libop obid sub (true, false) btyp extra

fun run_gen_session ev strm libop input obid sub btyp extra =
    let val _ = print "EventML# "
    in run_session ev strm libop input obid sub btyp extra
    end

and run_ev_session ev str strm libop input obid sub btyp extra =
    let val _ = print ("\nswitched to evaluator" ^ str ^ "\n")
    in run_gen_session ev strm libop input obid sub btyp extra
    end

and run_help_session ev strm libop input obid sub btyp extra =
    let val _ = print ("\n"
		       ^ "  - To evaluate an expression, type an expresion followed by ;;."
		       ^ "\n"
		       ^ "  - To quit, type 'quit'."
		       ^ "\n"
		       ^ "  - To disable the type inferencer, type 'notype'."
		       ^ "\n"
		       ^ "  - To enable the type inferencer, type 'type'."
		       ^ "\n"
		       ^ "  - To change the evaluator, type one of these: ev1, ev2, ev2b, ev2c, ev2d, ev3, ev3b, ev3c, ev3d, ev4, ev4b, ev5, ev5b"
		       ^ "\n\n")
    in run_gen_session ev strm libop input obid sub btyp extra
    end

and run_session ev strm libop input obid sub btyp extra =
    case TextIO.inputLine strm of
	NONE => run_session ev strm libop input obid sub btyp extra
      | SOME "quit\n"     => (print "\nend of session\n"; EV.end_session ())
      | SOME "exit\n"     => (print "\nend of session\n"; EV.end_session ())
      | SOME "aurevoir\n" => (print "\nend of session\n"; EV.end_session ())
      | SOME "type\n"     => (print "\nenabled type inferencer\n";  print "EventML# "; run_session ev strm libop input obid sub true  extra)
      | SOME "notype\n"   => (print "\ndisabled type inferencer\n"; print "EventML# "; run_session ev strm libop input obid sub false extra)
      | SOME "ev1\n"      => run_ev_session ev1  "1"  strm libop input obid sub btyp extra
      | SOME "ev2\n"      => run_ev_session ev2  "2"  strm libop input obid sub btyp extra
      | SOME "ev2b\n"     => run_ev_session ev2b "2b" strm libop input obid sub btyp extra
      | SOME "2b\n"       => run_ev_session ev2b "2b" strm libop input obid sub btyp extra
      | SOME "ev2c\n"     => run_ev_session ev2c "2c" strm libop input obid sub btyp extra
      | SOME "2c\n"       => run_ev_session ev2c "2c" strm libop input obid sub btyp extra
      | SOME "ev2d\n"     => run_ev_session ev2d "2d" strm libop input obid sub btyp extra
      | SOME "2d\n"       => run_ev_session ev2d "2d" strm libop input obid sub btyp extra
      | SOME "ev3\n"      => run_ev_session ev3  "3"  strm libop input obid sub btyp extra
      | SOME "ev3b\n"     => run_ev_session ev3b "3b" strm libop input obid sub btyp extra
      | SOME "3b\n"       => run_ev_session ev3b "3b" strm libop input obid sub btyp extra
      | SOME "ev3c\n"     => run_ev_session ev3c "3c" strm libop input obid sub btyp extra
      | SOME "3c\n"       => run_ev_session ev3c "3c" strm libop input obid sub btyp extra
      | SOME "ev3d\n"     => run_ev_session ev3d "3d" strm libop input obid sub btyp extra
      | SOME "3d\n"       => run_ev_session ev3d "3d" strm libop input obid sub btyp extra
      | SOME "ev4\n"      => run_ev_session ev4  "4"  strm libop input obid sub btyp extra
      | SOME "ev4b\n"     => run_ev_session ev4b "4b" strm libop input obid sub btyp extra
      | SOME "4b\n"       => run_ev_session ev4b "4b" strm libop input obid sub btyp extra
      | SOME "ev5\n"      => run_ev_session ev5  "5"  strm libop input obid sub btyp extra
      | SOME "ev5b\n"     => run_ev_session ev5b "5b" strm libop input obid sub btyp extra
      | SOME "5b\n"       => run_ev_session ev5b "5b" strm libop input obid sub btyp extra
      | SOME "help\n"     => run_help_session ev strm libop input obid sub btyp extra
      | SOME line         =>
	let val _ = evaluate_map ev input line libop obid sub btyp extra
	    val _ = print "EventML# "
	in run_session ev strm libop input obid sub btyp extra
	end

fun start_session ev input libop alldefop obid sub extra =
    let val _    = print "Loading library...\n"
	val _    = EV.start_session false alldefop
	val strm = TextIO.stdIn
	val _    = print "EventML# "
	val btyp = true
    in run_session ev strm libop input obid sub btyp extra
    end


(* ------ TYPE CHECKER ------ *)

val eval_test = EV.test

val typecheck = E.typecheck

fun slice input outputop libop timelimit sub =
    let val san  = false
	val btyp = true
	val (prog, env, b) = E.slice [input] outputop libop timelimit (true, true) sub san btyp
    in ()
    end

fun dump_prog_stream n_terms prog file =
    let val _      = print "[dumping program]\n"
	val time   = #stime (Posix.ProcEnv.times ())
	val output = file ^ "-" ^ Time.toString time
	val _      = NT.toStringTermStream prog output
	val _      = print "[program dumped]\n"
    in ()
    end

fun dump_prog n_terms prog fdump =
    let	val time   = #stime (Posix.ProcEnv.times ())
	val output = "output-term-" ^ Time.toString time
	val _      = print ("[dumping program in " ^ output ^ "]\n")
	val stout  = TextIO.openOut output
	val _      = TextIO.output (stout, fdump prog ^ "\004\n\n")
	val _      = map (fn t => TextIO.output (stout, fdump t ^ "\004\n")) n_terms
	val _      = TextIO.closeOut stout
    in ()
    end

fun pp_dump_prog_op nterms (SOME (_, prog)) = dump_prog nterms prog NT.ppTerm
  | pp_dump_prog_op _ _ = ()

fun dump_prog_op nterms (SOME (_, prog)) = dump_prog nterms prog NT.toStringTerm
  | dump_prog_op _ _ = ()

fun dump_hs lib prog =
    let	val time    = #stime (Posix.ProcEnv.times ())
	val date    = Date.fmt "%j-%m-%d" (Date.fromTimeLocal time)
	val output  = "program-" ^ date ^ "-" ^ Time.toString time
	val output1 = output ^ ".unfolded"
	val output2 = output ^ ".hs"
	val _       = print ("[dumping unfolded program in " ^ output1 ^ "]\n")
	val _       = NT.print_lib_stats lib
	val prog'   = NT.unfold_all lib prog
	val stout1  = TextIO.openOut output1
	val _       = TextIO.output (stout1, NT.toStringTerm prog')
	val _       = TextIO.closeOut stout1
	val _       = print ("[dumping haskell program in " ^ output2 ^ "]\n")
	val stout2  = TextIO.openOut output2
	val _       = TextIO.output (stout2, NT.nuprl2haskell prog')
	val _       = TextIO.closeOut stout2
    in ()
    end

fun dump_hs_op (SOME lib) (SOME (_, prog)) = dump_hs lib prog
  | dump_hs_op _ _ = ()

fun toNuprl input outputop libop alldefop obid timelimit sub prt sprt poly btyp extra =
    let val san    = false
	(* export is true if we actually want to export the terms in a file *)
	val export = Option.isSome outputop
	val _      = if export
		     then (NT.reset_dtag (); NT.reset_LC ())
		     else (print ("[setting dummy tag]\n"); NT.set_dummy_dtag (); NT.set_LC ())
	val (term, env, b) = E.slice [input] NONE libop timelimit sprt sub san btyp
    in if b
       then let val s_term = A.simplify term
		val mapop =
		    case alldefop of
			SOME f =>
			let val _     = print ("[parsing Nuprl library]\n")
			    val terms = PN.parse prt NT.to_filter_out f false
			    val _     = print ("[generating EML library]\n")
			    val lib   = NT.terms2map terms
			    val _     = NT.print_lib_stats lib
			    val _     = EV.start_session_lib lib
			    val _     = print ("[library loaded]\n")
			    val _     = loaded := true
			in SOME lib
			end
		      | NONE => NONE
		val pref    = true
		val stdma   = true
		val cbva    = is_cbva_extra extra
		val newprog = is_newprog_extra extra
		val (n_terms, prog) = N.toNuprl mapop input obid s_term env sub pref poly stdma btyp cbva newprog
		(* -- Add programs to library -- *)
		val _  = EV.add_to_session n_terms
		val _  = program := prog
		val _  =
		    if is_dump_extra extra
		    then dump_prog_op n_terms prog
		    else ()
		val _  =
		    if is_haskell_extra extra
		    then dump_hs_op mapop prog
		    else ()
		val st =
		    if prt
		    then app (fn n_term => print (NT.toStringTerm n_term ^ "\n")) n_terms
		    else ()
		val _  =
		    case outputop of
			NONE => ()
		      | SOME file =>
			let val file' = file ^ ".tmp"
			    val stout = TextIO.openOut file'
			    val _     = map (fn n_term => TextIO.output (stout, NT.toStringTerm n_term ^ "\004\n")) n_terms
			    val _     = TextIO.closeOut stout
			    val _     = OS.FileSys.rename {old = file', new = file}
			in () end
			handle IO.Io {name, function, cause} =>
			       (raise EH.Impossible ("cannot open or close one of the output file (function:" ^ function ^ ",name:" ^ name ^ ")\n"))
	    in n_terms
	    end
       else (print "We won't convert the program into a Nuprl term because it contains errors.\n"; [])
    end

fun parseNuprl input outputop prt split extra =
    let val force = is_true_extra extra
    in GL.exportTerms input outputop prt split force
    end

fun sanitizer input outputop libop timelimit sub =
    let val san  = true
	val btyp = true
	val (prog, env, b) = E.slice [input] outputop libop timelimit (true, true) sub san btyp
    in ()
    end


(* ------ PROTOCOL SIMULATION ------ *)

fun getComponents term =
    if NT.is_nuprl_cons_term term
    then let val (head, tail) = NT.dest_cons term
	 in if NT.is_nuprl_pair_term head
	    then (NT.dest_pair 1 head) :: (getComponents tail)
	    else raise EH.Impossible "getComponents"
	 end
    else if NT.is_nuprl_nil_term term
    then []
    else raise EH.Impossible "getComponents"

fun how_many_components term =
    if NT.is_nuprl_pair_term term
    then 1 + how_many_components (#2 (NT.dest_pair 2 term))
    else 1

fun nuprl_all t   =
    if NT.is_nuprl_iclosure_term t
    then let val (a,e) = NT.dest_iclosure t
	 in NT.mk_nuprl_iclosure_term (nuprl_all a) e
	 end
    else NT.mk_nuprl_callbyvalueall_term t ("x", NT.mk_variable_term "x")
fun nuprl_app p t =
    if NT.is_nuprl_iclosure_term p
    then let val (a,e) = NT.dest_iclosure p
	 in NT.mk_nuprl_iclosure_term (nuprl_app a t) e
	 end
    else NT.mk_apply_term p t

fun testing 0 = EV.start_session true (SOME default_alldefs)
  | testing 1 = EV.end_session ()
  | testing n =
    let val terms   = GL.parseTerms "output" false false
	(* list of locations: *)
	val pid     = NT.mk_nuprl_mkid_term "p"
	val l1id    = NT.mk_nuprl_mkid_term "l1"
	val l2id    = NT.mk_nuprl_mkid_term "l2"
	val ids     = [pid, l1id, l2id]
	val lstls   = NT.mk_nuprl_finite_list_term [l1id, l2id]
    in case terms of
	   [prog] =>
	   let (* program: *)
	       val prog1 = NT.mk_apply_term prog lstls
	       val prog2 = NT.mk_apply_term prog1 pid
	       val prog3 = #1 (ev1 [] (~1) prog2)
	       fun build id = NT.mk_nuprl_df_program_meaning_term (nuprl_app prog3 id)
	       (*val xxx =
		   let val x = ev n (build pid)
		       val _ = print ("\n-+1+-----------\n" ^ NT.toStringTerm prog  ^ "\n-+1+-----------\n")
		       val _ = print ("\n-+2+-----------\n" ^ NT.toStringTerm prog3 ^ "\n-+2+-----------\n")
		       val _ = print ("\n-+3+-----------\n" ^ NT.toStringTerm x     ^ "\n-+3+-----------\n")
		       val _ = raise Fail ""
		   in ()
		   end*)
	       val lst = map (fn id => (id, #1 (ev1 [] (~1) (build id)))) ids
	       (* inital message: *)
	       val client = NT.mk_nuprl_mkid_term "client"
	       val start  = NT.mk_nuprl_token_term "start"
	       val hdr    = NT.mk_nuprl_finite_list_term [start]
	       val loc    = NT.mk_nuprl_loc_term
	       val msg    = NT.mk_nuprl_make_msg_term hdr loc client
	   (* now we select the program associated with "p" *)
	   in case List.find (fn (id, p) => NT.alpha_equal_terms id pid) lst of
		  SOME (i, p) =>
		  let (*val _ = print ("\n-+a+-----------\n" ^ NT.toStringTerm p  ^ "\n-+a+-----------\n")*)
		      val p' = #1 (ev1 [] (~1) (nuprl_all (nuprl_app p msg)))
		  in print ("\n-+b+-----------\n" ^ NT.toStringTerm p' ^ "\n-+b+-----------\n")
		  end
		| NONE => ()
	   end
	 | _ => ()
    end

(*
fun extractInfoParam list =
    let val locs =
	    map (fn loc =>
		    if String.isPrefix "LOC(" loc
		       andalso
		       String.isSuffix ")" loc
		    then let val to = String.size loc - 5
			     val id = String.substring (loc, 4, to)
			 in NT.mk_nuprl_mkid_term id
			 end
		    else raise Fail ("extract_info_param - " ^ loc))
		list
    in case locs of
	   []  => raise Fail ("extract_info_param - " ^ Int.toString (List.length locs))
	 | [l] => l
	 | _   => NT.mk_nuprl_finite_list_term locs
    end

(* Write a proper parser for that! *)
fun load_config config =
    let val strm = TextIO.openIn config
	val fsep = fn #" " => true | _ => false
	val locations =
	    case TextIO.inputLine strm of
		SOME line =>
		let val line = String.substring (line, 0, String.size line - 1)
		    val elts = String.tokens fsep line
		in case elts of
		       x :: xs =>
		       if x = "locations:"
		       then map NT.mk_nuprl_mkid_term xs
		       else raise Fail "load_config"
		     | [] => raise Fail "load_config"
		end
	      | NONE => raise Fail "load_config"
	fun getParams () =
	    case TextIO.inputLine strm of
		SOME line =>
		let val line = String.substring (line, 0, String.size line - 1)
		    val elts = String.fields fsep line
		in case elts of
		       (name :: vs) =>
		       if name = ""
		       then getParams ()
		       else (case String.fields (fn #":" => true | _ => false) name of
				 [name, ""] => (name, extractInfoParam vs) :: getParams ()
			       | _ => raise Fail "load_config - name")
		     | _ => raise Fail "load_config - elts"
		end
	      | NONE => []
	val params = getParams ()
	val _ = TextIO.closeIn strm
    in (locations, params, [])
    end
*)


(* ------ operation on configation file ------ *)

fun get_locs_from_groups groups =
    foldr (fn ((name,mem,locs),lst) => locs @ lst)
	  []
	  groups

fun get_internal_locs_from_groups groups =
    foldr (fn ((name,mem,locs),lst) => if mem then locs @ lst else lst)
	  []
	  groups

fun get_external_locs_from_groups groups =
    foldr (fn ((name,mem,locs),lst) => if mem then lst else locs @ lst)
	  []
	  groups

fun find_group (ip, port) groups =
    List.find
	(fn (name,mem,locs) =>
	    List.exists
		(fn (id,thost,tport) =>
		    let val h = NT.dest_ihost thost
			val p = NT.dest_iport tport
		    in ip = h andalso port = p
		    end)
		locs)
	groups

fun find_lt_groups name conns =
    List.foldr
	(fn ((from,to),names) =>
	    if name = to
	    then from :: names
	    else names)
	[]
	conns

fun find_gt_groups name conns =
    List.foldr
	(fn ((from,to),names) =>
	    if name = from
	    then to :: names
	    else names)
	[]
	conns

fun filter_groups groups names =
    List.filter
	(fn (name,mem,locs) => List.exists (fn x => x = name) names)
	groups

fun load_config_parse_locations locs =
    map (fn (loc, host, port) =>
	    (NT.mk_nuprl_mkid_term  loc,
	     NT.mk_nuprl_ihost_term host,
	     NT.mk_nuprl_iport_term port))
	locs

fun load_config_parse_groups groups =
    map (fn (name, mem, locs) => (name, mem, load_config_parse_locations locs))
	groups

fun load_config_parse_messages msgs =
    map (fn (id, (hdr, typ, body)) =>
	    let val pair = NT.mk_pair_term typ body
		val msg  = NT.mk_pair_term hdr pair
		(*val msg = NT.mk_nuprl_make_msg_term hdr typ body*)
		val pid = NT.mk_nuprl_mkid_term id
	    in NT.mk_pair_term pid msg
	    end)
	msgs

fun load_config_parse config =
    let val (grps, conns, params, msgs) = C.parse config
	val groups   = load_config_parse_groups   grps
	val messages = load_config_parse_messages msgs
    in (groups, conns, params, messages)
    end

fun load_config_parse_str str = load_config_parse_messages (#4 (C.parseString str))


(* ------ ... ------ *)

fun testing _ = (load_config_parse "new_conf"; ())

fun testing n =
    let val _ = EV.start_session true (SOME default_alldefs)
	val _ = print ("[loaded library]")
    in eval_test n
    end

fun getParams params map_params =
    map (fn param =>
	    case List.find (fn (id : string, _) => id = param) map_params of
		SOME (id, v) => v
	      | NONE => raise Fail ("get_params(" ^ param ^ ")"))
	params

fun update_component (i, s) cmps =
    map (fn (j, p) =>
	    ((*print ("--" ^ NT.toStringTerm j ^ "\n");*)
	     if NT.alpha_equal_terms i j
	     then (i, s)
	     else (j, p)))
	cmps

fun print_message_list _ [] = ()
  | print_message_list n (msg :: msgs) =
    (print (Int.toString n ^ ": " ^ NT.nuprlTerm2eml msg ^ "\n--\n");
     print_message_list (n + 1) msgs)

fun print_messages_intransit () =
    (print ("\n-------IN-TRANSIT-------\n"); print_message_list 1 (!intransit))

fun debug_eval previous_result term n =
    let val _ = print ("-" ^ Int.toString n ^ "\n")
	val (p1,n1) = ev1 [] n term
	val (p2,n2) = ev2 [] n term
    in if n1 = n2 andalso NT.alpha_equal_terms p1 p2
       then if n1 = n
	    then debug_eval p1 term (n + 1)
	    else print ("equal[1:" ^ Int.toString n1 ^ ",2:" ^ Int.toString n2 ^ "]\n")
       else let val stout = TextIO.openOut "output-old"
		val _     = TextIO.output (stout, NT.toStringTerm previous_result ^ "\004\n")
		val _     = TextIO.closeOut stout
		val stout = TextIO.openOut "output-1"
		val _     = TextIO.output (stout, NT.toStringTerm p1 ^ "\004\n")
		val _     = TextIO.closeOut stout
		val stout = TextIO.openOut "output-2"
		val _     = TextIO.output (stout, NT.toStringTerm p2 ^ "\004\n")
		val _     = TextIO.closeOut stout
	    in print ("diff[1:" ^ Int.toString n1 ^ ",2:" ^ Int.toString n2 ^ "]\n")
	    end
    end

fun run_stepper n ev gc debug remove config alldefs extra =
    if n < 0
    then let val _ = configured := false
	     val _ = components := []
	     val _ = intransit  := []
	 in ()
	 end
    else if !loaded
    then if !configured
	 then case !intransit of
		  [] => print "[no message in transit]\n"
		| lst =>
		  if n > List.length lst orelse n < 1
		  then print "[out of bound]\n"
		  else if remove
		  then let val new_msgs = (List.take (lst, n - 1)) @ (List.drop (lst, n))
			   val _ = intransit := new_msgs
		       in ()
		       end
		  else let val (id, msg) = NT.dest_pair 3 (List.nth (lst, n - 1))
			   (*val _ = print ("-+-" ^ NT.toStringTerm id ^ "\n")*)
		       in case List.find (fn (i, p) =>
					     ((*print ("---" ^ NT.toStringTerm i ^ "\n");*)
					      NT.alpha_equal_terms i id))
					 (!components) of
			      SOME (i, p) =>
			      let (*val _ = print ("\n-+a+-----------\n" ^ NT.toStringTerm p  ^ "\n-+a+-----------\n")*)
				  (*val _  = print ("[size: " ^ IntInf.toString (NT.large_size p) ^ "]\n")*)
				  val _ = print ("[size(1): " ^ Int.toString (NT.size p) ^ "]\n")
				  val pop =
				      if is_newprog_extra extra
				      then if NT.is_nuprl_inl_term p
					   then SOME (NT.dest_inl p)
					   else if NT.is_nuprl_inr_term p
					   then NONE
					   else (dump_prog [] p NT.toStringTerm;
						 raise Fail ("run_stepper:newprog:not_inl_or_inr("
							     ^ NT.opid_of_term p
							     ^ ")"))
				      else SOME p
			      in case pop of
				     SOME p =>
				     let val toeval = nuprl_all (nuprl_app p msg)
					 val (p',stps) = ev [] (~1) toeval
					 val _ = if debug
						 then debug_eval toeval toeval 2025
						 else () (**)
					 (*val _ = raise Fail "--"*)
					 val (s,msgs) = NT.dest_pair 4 p'
					 val _  = print ("[size(2): " ^ IntInf.toString (NT.large_size s) ^ "]\n")
					 (*val _  = print ("[depth: " ^ Int.toString (NT.env_depth s) ^ "]\n")*)
					 (*val _  = print ("[env: " ^ Int.toString (NT.env_size s) ^ "]\n")*)
					 (*val _ = print ("\n-+b+-----------\n" ^ NT.toStringTerm p' ^ "\n-+b+-----------\n")*)
					 (*val _ = print ("\n-------MSGS------\n" ^ NT.toStringTerm msgs ^ "\n------------\n")*)
					 val lst_msgs = NT.dest_list msgs
					 val new_cmps = update_component (i, s) (!components)
					 val new_msgs = (List.take (lst, n - 1)) @ (List.drop (lst, n)) @ lst_msgs
					 val _ = components := new_cmps
					 val _ = intransit := new_msgs
				     in ()
				     end
				   | NONE => print "[program finished]\n"
			      end
			    | NONE => print "[no recipient]\n"
		       end
	 else let (* gets the locations and parameters from the input config file *)
		 val (groups, conns, params, messages) = load_config_parse config
		 (*val (locations, params, messages) = load_config config*)
		 (* generates the list of components *)
		 val cmps =
		     case !program of
			 SOME (prms, p) =>
			 let val args  = getParams prms params
			     val _     = print ("[size initial component: " ^ Int.toString (NT.size p) ^ "]\n")
			     val prog1 = NT.mk_nuprl_applies_term p args
			     val mng1  = NT.mk_lambda_term "p" (NT.mk_nuprl_df_program_meaning_term (NT.mk_variable_term "p"))
			     val (prog2,mng2) =
				 if is_fold_extra extra
				 then (prog1, mng1)
				 else let val _     = print ("[unfolding]\n")
					  val lib   = EV.get_lib ()
					  val _     = NT.print_lib_stats lib
					  val prog2 = NT.unfold_all lib prog1
					  val mng2  = NT.unfold_all lib mng1
					  val _     = print ("[size after unfolding: " ^ Int.toString (NT.size prog2) ^ "]\n")
					  val _     = print ("[GC library]\n")
					  val _     = EV.reset_lib ()
					  val _     = if gc then MLton.GC.collect() else ()
				      in (prog2, mng2)
				      end
			     (*val _     = dump_prog [] prog2 NT.toStringTerm*)
			     fun build id =
				 if is_newprog_extra extra
				 then nuprl_app prog2 id
				 else nuprl_app mng2 (nuprl_app prog2 id)
			 in map (fn (id,host,port) =>
				    let val _ = print ("[generatig program for " ^ NT.toStringTerm id ^ "]\n")
					val b = build id
					val (p,stps) = ev [] (~1) b
					val _ = print ("[size component: " ^ Int.toString (NT.size p) ^ "]\n")
				    in (id, p)
				    end)
				(get_internal_locs_from_groups groups)
			 end
		       | NONE => raise Fail "[not a program]"
		 val cmps' =
		     if is_newprog_extra extra
		     then map (fn (id, prog) =>
				  let val prog' = NT.partial_ev_opt prog
				      (*val _     = dump_prog [] prog' NT.toStringTerm*)
				      val _     = print ("[size after partial evaluation: " ^ Int.toString (NT.size prog') ^ "]\n")
				  in (id, prog')
				  end)
			      cmps
		     else cmps
		 val _ = components := cmps'
		 val _ = intransit  := messages
		 val _ = configured := true
		 val _ = print ("[components loaded]\n")
	     in ()
	     end
    else let (* loads the alldefs file *)
	    val _ = EV.start_session true (SOME default_alldefs)
	    val _ = loaded := true
	    val _ = print ("[library loaded]\n")
	in ()
	end

fun loop_gen_stepper ev gc strm conf alldefs extra =
    let val _ = print "message? "
    in loop_stepper ev gc strm conf alldefs extra
    end

and loop_ev_stepper ev str gc strm conf alldefs extra =
    let val _ = print ("\nswitched to evaluator" ^ str ^ "\n")
    in loop_gen_stepper ev gc strm conf alldefs extra
    end

and loop_help_stepper ev gc strm conf alldefs extra =
    let val _ = print ("\n"
		       ^ "  - To send a message enter an integer corresponding to a message in transit."
		       ^ "\n"
		       ^ "  - To quit, type quit."
		       ^ "\n"
		       ^ "  - To change the evaluator, type one of these: ev1, ev2, ev2b, ev2c, ev2d, ev3, ev3b, ev3c, ev3d, ev4, ev4b, ev5, ev5b"
		       ^ "\n\n")
    in loop_gen_stepper ev gc strm conf alldefs extra
    end

and loop_stepper ev gc strm conf alldefs extra =
    case TextIO.inputLine strm of
	NONE => loop_stepper ev gc strm conf alldefs extra
      | SOME "quit\n"     => (print "\nend of session\n"; run_stepper (~1) ev gc false false conf alldefs extra)
      | SOME "exit\n"     => (print "\nend of session\n"; run_stepper (~1) ev gc false false conf alldefs extra)
      | SOME "aurevoir\n" => (print "\nend of session\n"; run_stepper (~1) ev gc false false conf alldefs extra)
      | SOME "ev1\n"      => loop_ev_stepper ev1  "1"  gc strm conf alldefs extra
      | SOME "ev2\n"      => loop_ev_stepper ev2  "2"  gc strm conf alldefs extra
      | SOME "ev2b\n"     => loop_ev_stepper ev2b "2b" gc strm conf alldefs extra
      | SOME "2b\n"       => loop_ev_stepper ev2b "2b" gc strm conf alldefs extra
      | SOME "ev2c\n"     => loop_ev_stepper ev2c "2c" gc strm conf alldefs extra
      | SOME "2c\n"       => loop_ev_stepper ev2c "2c" gc strm conf alldefs extra
      | SOME "ev2d\n"     => loop_ev_stepper ev2d "2d" gc strm conf alldefs extra
      | SOME "2d\n"       => loop_ev_stepper ev2d "2d" gc strm conf alldefs extra
      | SOME "ev3\n"      => loop_ev_stepper ev3  "3"  gc strm conf alldefs extra
      | SOME "ev3b\n"     => loop_ev_stepper ev3b "3b" gc strm conf alldefs extra
      | SOME "3b\n"       => loop_ev_stepper ev3b "3b" gc strm conf alldefs extra
      | SOME "ev3c\n"     => loop_ev_stepper ev3c "3c" gc strm conf alldefs extra
      | SOME "3c\n"       => loop_ev_stepper ev3c "3c" gc strm conf alldefs extra
      | SOME "ev3d\n"     => loop_ev_stepper ev3d "3d" gc strm conf alldefs extra
      | SOME "3d\n"       => loop_ev_stepper ev3d "3d" gc strm conf alldefs extra
      | SOME "ev4\n"      => loop_ev_stepper ev4  "4"  gc strm conf alldefs extra
      | SOME "ev4b\n"     => loop_ev_stepper ev4b "4b" gc strm conf alldefs extra
      | SOME "4b\n"       => loop_ev_stepper ev4b "4b" gc strm conf alldefs extra
      | SOME "ev5\n"      => loop_ev_stepper ev5  "5"  gc strm conf alldefs extra
      | SOME "ev5b\n"     => loop_ev_stepper ev5b "5b" gc strm conf alldefs extra
      | SOME "5b\n"       => loop_ev_stepper ev5b "5b" gc strm conf alldefs extra
      | SOME "help\n"     => loop_help_stepper ev gc strm conf alldefs extra
      | SOME line         =>
	let fun aux [] =
		(print_messages_intransit ();
		 print "message? ";
		 loop_stepper ev gc strm conf alldefs extra)
	      | aux (input :: inputs) =
		let val (input',debug,remove) =
			if String.isPrefix "d" input
			then (String.substring (input, 1, (String.size input) - 1), true, false)
			else if String.isPrefix "r" input
			then (String.substring (input, 1, (String.size input) - 1), false, true)
			else (input, false, false)
		in case Int.fromString input' of
		       SOME n => (run_stepper n ev gc debug remove conf alldefs extra;
				  MLton.GC.collect();
				  aux inputs)
		     | NONE => (print "please, enter a nat\n";
				print "message? ";
				loop_stepper ev gc strm conf alldefs extra)
		end
	in aux (String.tokens (fn #" " => true | #"\n" => true | _ => false) line)
	end (*handle _ => print "empty line"*)

fun start_stepper spec conf ev gc lib alldefs obid time sub prt extra =
    let (* loads library and generates program *)
	val _     = print ("[type checking and loading library]\n")
	val poly  = true
	val btyp  = true
	val terms = toNuprl spec NONE lib alldefs obid time sub prt (true, false) poly btyp extra
	(* evaluators *)
	val _     = print ("[evaluators available: 1/2/2b/3/3b/3c/3d/4/4b/5/5b]\n")
	(* loads the components *)
	val _     = print ("[loading components]\n")
	val _     = run_stepper 0 ev gc false false conf alldefs extra
	(* print the list of messages initially in transit *)
	val _     = print ("[running simulator]\n")
	val _     = print_messages_intransit ()
	val _     = print "message? "
	(* generates stream on the standard input *)
	val strm  = TextIO.stdIn
    (* starts simulator *)
    in loop_stepper ev gc strm conf alldefs extra
    end


(* ------ SOCKET STUFF ------ *)

val ip_server = "127.0.0.1"
val port_server = 8987

fun addr_to_string addr =
    let val (a,p) = INetSock.fromAddr addr
    in "(" ^ NetHostDB.toString a ^ "," ^ Int.toString p ^ ")"
    end

val word_to_char     = Char.chr o Word8.toInt
val word_to_str      = String.str o word_to_char
val vector_to_string = Word8Vector.foldl (fn (elt, str) => str ^ word_to_str elt) ""
val slice_to_string  = vector_to_string o Word8VectorSlice.vector

val a_sock_ref = ref ([] : (INetSock.inet, Socket.active  Socket.stream) Socket.sock list)
val p_sock_ref = ref ([] : (INetSock.inet, Socket.passive Socket.stream) Socket.sock list)

fun add_a_sock_ref sock = a_sock_ref := sock :: !a_sock_ref
fun add_p_sock_ref sock = p_sock_ref := sock :: !p_sock_ref

fun create_server_socket (ip, port) =
    let val sock      = INetSock.TCP.socket ()
	val addr      = Option.valOf (NetHostDB.fromString ip)
	val sock_addr = INetSock.toAddr (addr, port)
	val saddr     = addr_to_string sock_addr
	val _         = print ("[created server socket at " ^ saddr ^ "]\n")
	val _         = Socket.Ctl.setREUSEADDR (sock, true)
	val _         = Socket.bind (sock, sock_addr)
	val _         = print ("[binding]\n")
	val _         = Socket.listen (sock, 100)
	val _         = print ("[listening]\n")
	val _         = add_p_sock_ref sock
    in (sock, sock_addr)
    end

fun print_syserror_msg (str, NONE) = "(" ^ str ^ ")"
  | print_syserror_msg (str, SOME syserror) =
    "(type:" ^ str ^ ",msg:" ^ OS.errorMsg syserror ^ ",name:" ^ OS.errorName syserror ^ ")"

val _ = MLton.Signal.setHandler
	    (Posix.Signal.int,
	     MLton.Signal.Handler.simple
		 (fn () =>
		     let val _ = app (fn sock =>
					 let val _ = print ("[cleaning active socket]\n")
					     val _ = Socket.shutdown (sock, Socket.NO_RECVS_OR_SENDS)
					 in Socket.close sock
					    handle OS.SysErr err =>
						   print ("[--ignoring close socket failure:" ^ print_syserror_msg err ^ "]\n")
					 end)
				     (!a_sock_ref)
			 val _ = app (fn sock =>
					 let val _ = print ("[cleaning passive socket]\n")
					     val _ = Socket.shutdown (sock, Socket.NO_RECVS_OR_SENDS)
					 in Socket.close sock
					    handle OS.SysErr err =>
						   print ("[--ignoring close socket failure:" ^ print_syserror_msg err ^ "]\n")
					 end)
				     (!p_sock_ref)
			 val _ = Posix.Process.exit 0w0
		     in ()
		     end))

(*
fun get_server_info () =
    let val addr   = Option.valOf (NetHostDB.fromString ip_server)
	val server = INetSock.toAddr (addr, port_server)
    in (server)
    end

fun run_client n =
    let val sock   = INetSock.TCP.socket ()
	(* -- server socket -- *)
	val server = get_server_info ()
	(* -- stuff to send -- *)
	val vect  = Word8Vector.fromList [Word8.fromInt n]
	val slice = Word8VectorSlice.full vect
	(*----*)
	val _     = print ("connecting to server\n")
	val _     = Socket.connect (sock, server)
	val _     = print ("connected\n")
	fun loop () =
	    let val _ = print ("sending data\n")
		val _ = Socket.sendVec (sock, slice)
		val _ = print ("data sent\n")
	    in loop ()
	    end
    in loop ()
    end
*)

fun get_id_in_locs (Mac (ip, port)) locations =
    List.find (fn (id,thost,tport) =>
		  let val h = NT.dest_ihost thost
		      val p = NT.dest_iport tport
		      (*val _ = print ("-" ^ h ^ "-" ^ Int.toString p ^ "-\n")*)
		  in ip = h andalso port = p
		  end)
	      locations
  | get_id_in_locs (Loc loc) locations =
    List.find (fn (id,thost,tport) => NT.dest_id id = loc) locations

fun get_id_in_groups ident groups =
    get_id_in_locs ident (get_internal_locs_from_groups groups)

fun get_ip_port_in_locs loc locations =
    get_id_in_locs (Loc (NT.dest_id loc)) locations

fun load_program ev gc ident params id extra =
    case !program of
	SOME (prms, p) =>
	let val args      = getParams prms params
	    val prog1     = NT.mk_nuprl_applies_term p args
	    val (prog2,_) = ev [] (~1) prog1
	    val mng       =
		if is_newprog_extra extra
		then nuprl_app prog2 id
		else NT.mk_nuprl_df_program_meaning_term (nuprl_app prog2 id)
	    val _         = print ("[component loaded]\n")
	    val (prog3,_) = ev [] (~1) mng
	    val _         = print ("[size: " ^ Int.toString (NT.size prog3) ^ "]\n")
	(* -- *)
	in if is_fold_extra extra
	   then prog3
	   else let val _     = print ("[unfolding]\n")
		    val lib   = EV.get_lib ()
		    val _     = NT.print_lib_stats lib
		    val prog4 = NT.unfold_all lib prog3
		    val _     = EV.reset_lib ()
		    val _     = if gc then MLton.GC.collect() else ()
		    val _     = print ("[size(after unfolding): " ^ Int.toString (NT.size prog4) ^ "]\n")
		in if is_newprog_extra extra
		   then let val prog5 = NT.partial_ev_opt prog4
			    val _     = print ("[size(after partial evaluation): " ^ Int.toString (NT.size prog5) ^ "]\n")
			in prog5
			end
		   else prog4
		end
	end
      | NONE => raise Fail "[no program]"

fun testing n =
    let val sock  = INetSock.TCP.socket ()
	(*----*)
	val addr   = Option.valOf (NetHostDB.fromString ip_server)
	val server = INetSock.toAddr (addr, port_server)
	(*----*)
	val _     = print ("connecting to server\n")
	val _     = Socket.connect (sock, server)
	val _     = print ("connected\n")
	(*----*)
	val vect  = Word8Vector.fromList [Word8.fromInt n]
	val slice = Word8VectorSlice.full vect
	fun loop () =
	    let val _ = print ("sending data\n")
		val _ = Socket.sendVec (sock, slice)
		val _ = print ("data sent\n")
	    in loop ()
	    end
    in loop ()
    end

fun split_locations_in_group (ip, port) [] = ([], [])
  | split_locations_in_group (ip, port) ((nfo as (id, thost, tport)) :: lst) =
    let val h = NT.dest_ihost thost
	val p = NT.dest_iport tport
	val (less, greater) = split_locations_in_group (ip, port) lst
    in case (String.compare (ip, h), Int.compare (port, p)) of
	   (LESS, _)      => (less, nfo :: greater)
	 | (EQUAL, LESS)  => (less, nfo :: greater)
	 | (EQUAL, EQUAL) => (less, greater)
	 | _              => (nfo :: less, greater)
    end

fun split_locations (ip, port) groups conns =
    case find_group (ip, port) groups of
	SOME (name, mem, locs) =>
	let val (lt1, gt1) = split_locations_in_group (ip, port) locs
	    val lt_groups = find_lt_groups name conns
	    val gt_groups = find_gt_groups name conns
	    val lt2 = get_locs_from_groups (filter_groups groups lt_groups)
	    val gt2 = get_locs_from_groups (filter_groups groups gt_groups)
	in (lt1 @ lt2, gt1 @ gt2)
	end
      | NONE => ([], [])

fun select_id        (id,thost,tport,sock,desc) = id
fun select_socket    (id,thost,tport,sock,desc) = sock
fun select_desc      (id,thost,tport,sock,desc) = desc
fun select_sock_desc (id,thost,tport,sock,desc) = (sock,desc)

fun add_socket_desc sock desc (id,thost,tport) = (id,thost,tport,sock,desc)
fun add_socket sock nfo = add_socket_desc sock (Socket.sockDesc sock) nfo

fun filter_socks id nfo = NT.dest_id id = NT.dest_id (select_id nfo)

fun filter_socks_op i (nfo as (id,thost,tport,sock,desc)) =
    if filter_socks i nfo
    then SOME (sock,desc)
    else NONE

fun socket_to_string (id,thost,tport,sock,desc) =
    "("   ^ NT.toStringTerm id
    ^ "," ^ NT.toStringTerm thost
    ^ "," ^ NT.toStringTerm tport
    ^ ")"

fun sockets_to_string sockets =
    ListFormat.fmt {init  = "[",
		    final = "]",
		    sep   = ", ",
		    fmt   = socket_to_string}
		   sockets

fun get_descs sockets = map select_desc sockets

fun get_sock_from_desc _ [] = NONE
  | get_sock_from_desc d ((nfo as (id,thost,tport,sock,desc)) :: lst) =
    if Socket.sameDesc (d, desc)
    then SOME nfo
    else get_sock_from_desc d lst

fun string_to_slice str =
    let (* -- we transfrom the string into a character list -- *)
	val chars = String.explode str
	(* -- we transform the char list -> int list -> word list -- *)
	val words = map (Word8.fromInt o Char.ord) chars
	(* -- we get a vector from the work list -- *)
	val vec   = Word8Vector.fromList words
	(* -- we get a slice from the vector -- *)
	val slice = Word8VectorSlice.full vec
    in slice
    end

fun pack_message str =
    let val slice = string_to_slice str
	val len   = Word8VectorSlice.length slice
	val slen  = string_to_slice (Int.toString len ^ "!")
    in (slen, slice)
    end

fun pack_nuprl_message msg = pack_message (NT.toStringTerm msg)

fun send_something (sock,desc) slice =
    (case #wrs (Socket.select {rds = [], wrs = [desc], exs = [], timeout = NONE}) of
	 [_] =>
	 let val name = Socket.Ctl.getSockName sock
	     val peer = Socket.Ctl.getPeerName sock
	     val n    = Word8VectorSlice.length slice
	     (*val _    = print ("[--socket is ready, sending slice of length " ^ Int.toString n ^ "]\n")*)
	     val mop  = Socket.sendVecNB (sock, slice)
	     (*val _    = print ("[--checking that slice has been correctly sent]\n")*)
	 in case mop of
		SOME m =>
		if n = m
		then print ("[--successfully sent " ^ Int.toString m ^ "bytes]\n")
		else print ("[--send_message:bag length(sent " ^ Int.toString m ^ ", should have sent " ^ Int.toString n ^ ")]\n")
	      | NONE => print ("[--send has to wait (blocked)]\n")
	 end
       | lst => (print ("[--send_something:error: " ^ Int.toString (List.length lst) ^ " sockets writable]\n");
		 raise Fail "send_something"))
    handle OS.SysErr err => print ("[--error, cannot send message:" ^ print_syserror_msg err ^ "]\n")
	 | _ => print ("[--cannot send message: unknown error]\n")

fun send_message sockets loc str =
    let val socks = List.find (filter_socks loc) sockets
	val _ = print ("[sending message to " ^ NT.toStringTerm loc ^ "]\n")
    in case socks of
	   SOME (id,thost,tport,sock,desc) =>
	   let val (slen, slice) = pack_message str
	       (*val _ = print ("[--sending length]\n")*)
	       val _ = send_something (sock,desc) slen
	       (*val _ = print ("[--length sent]\n")*)
	       (*val _ = print ("[--sending slice]\n")*)
	       val _ = send_something (sock,desc) slice
	       (*val _ = print ("[--slice sent]\n")*)
	   in ()
	   end
	 | NONE => (*(print (sockets_to_string sockets); raise Fail "send_message")*)
	   (print ("[recipient does not exist anymore, ignoring send request]\n"); ())
    end handle _ => (print ("[ignoring send request (because an unknown error occured)]\n"); ())

fun send_nuprl_message sockets loc msg = send_message sockets loc (NT.toStringTerm msg)

fun send_nuprl_messages loc sockets [] = []
  | send_nuprl_messages loc sockets (term :: terms) =
    let val (id, msg) = NT.dest_pair 5 term
    in if loc = NT.dest_id id
       then msg :: (send_nuprl_messages loc sockets terms)
       else let val _ = send_nuprl_message sockets id msg
	    in send_nuprl_messages loc sockets terms
	    end
    end

exception NOT_FD
exception TRY_FD
exception RCV_INT of Socket.sock_desc option
exception RCV_SYS of Socket.sock_desc option * (string * OS.syserror option)
exception SEL_SYS of string * OS.syserror option

fun receive_integer_gen loc n pref str descop rcv =
    let fun loop b lst =
	    let val vec  = rcv 1
		val len  = Word8Vector.length vec
		val nstr = Int.toString n
	    in if b andalso len = 0
	       then (print ("[--error(@" ^ loc ^ "), received empty vector(" ^ nstr ^ ")]\n");
		     raise RCV_INT descop)
	       else if len = 1
	       then let val word = Word8Vector.sub (vec, 0)
			val char = word_to_char word
		    in if char = #"!"
		       then lst
		       else loop false (lst @ [char])
		    end
	       else raise Fail ("receive_integer(" ^ nstr ^ ")"
				^ ":bad_length"
				^ ":expecting_message_length_1_received_" ^ Int.toString len
				^ ":received_so_far_" ^ String.implode lst
				^ ":" ^ str
				^ "\n")
	    end
	val chars = loop true []
	val str   = String.implode chars
    in Int.fromString (pref ^ str)
    end handle OS.SysErr err =>
	       let val s = print_syserror_msg err
		   val _ = print ("[--error, cannot receive integer:" ^ s ^ ", trying to recover]\n")
	       in raise RCV_SYS (descop, err)
	       end

fun receive_integer loc str sock desc =
    receive_integer_gen loc 1 "" str (SOME desc) (fn n => Socket.recvVec (sock, n))

fun clean_sockets NONE sockets = sockets
  | clean_sockets (SOME desc) [] = []
  | clean_sockets (SOME desc) (entry :: sockets) =
    let val (sock,desc') = select_sock_desc entry
    in if Socket.sameDesc (desc', desc)
       then let val _ = print ("[--removing from socket list]\n")
	    in clean_sockets (SOME desc) sockets
	    end
       else entry :: clean_sockets (SOME desc) sockets
    end

fun try_clean_sockets [] = (false,[])
  | try_clean_sockets (entry :: socks) =
    let val (sock,desc) = select_sock_desc entry
    in let val timeout    = SOME (Time.fromMilliseconds 1)
	   val name       = Socket.Ctl.getSockName sock
	   val peer       = Socket.Ctl.getPeerName sock
	   val _          = Socket.select {rds = [desc], wrs = [], exs = [], timeout = timeout}
	   val (b,socks') = try_clean_sockets socks
       in (b, entry :: socks')
       end handle _ => (print ("[--socket seems dead, removing it from list]\n"); (true, socks))
    end

fun receive_message_sockets loc infd_op [] =
    (print ("[no more sockets to read from]\n");
     raise Fail "no more sockets to read from")
  | receive_message_sockets loc infd_op sockets =
    let val descs   = get_descs sockets
	val timeout =
	    if Option.isSome infd_op
	    then SOME (Time.fromMilliseconds 500)
	    else NONE
    in case #rds (Socket.select {rds = descs, wrs = [], exs = [], timeout = timeout}) of
	   (desc :: _) =>
	   (case get_sock_from_desc desc sockets of
		SOME (_,_,_,sock,desc) =>
		let val name = Socket.Ctl.getSockName sock
		    val peer = Socket.Ctl.getPeerName sock
		    val nstr = addr_to_string name
		    val pstr = addr_to_string peer
		    val str  = "(name:" ^ nstr ^ ",peer:" ^ pstr ^ ")"
		in case receive_integer loc str sock desc of
		       SOME n =>
		       (let fun aux n s =
				if n = 0
				then (s, false, sockets)
				else if n < 0
				then raise Fail ("receive_message_bad_length(negative)")
				else let val vec = Socket.recvVec (sock, n)
					 val len = Word8Vector.length vec
					 val str = vector_to_string vec
				     in aux (n - len) (s ^ str)
				     end
			in aux n ""
			end
			handle OS.SysErr err =>
			       let val s = print_syserror_msg err
				   val _ = print ("[--error while sending vector:" ^ s ^ ", trying to recover]\n")
			       in raise RCV_SYS (SOME desc, err)
			       end)
		     | NONE => raise Fail "receive_message:not_an_int"
		end
	      | NONE => raise Fail "receive_message:no_corresponding_socket")
	 | [] => raise TRY_FD
    end handle OS.SysErr err =>
	       let val s = print_syserror_msg err
		   val _ = print ("[--error, cannot receive message (sockets):" ^ s ^ "]\n")
		   val _ = print ("[--trying to find dead sockets]\n")
		   val (b,sockets') = try_clean_sockets sockets
	       in if b
		  then (print ("[--retrying receive with new socket list]\n");
			receive_message_sockets loc infd_op sockets')
		  else (print ("[--system error, but sockets seem fine, failing]\n");
			raise OS.SysErr err)
	       end
	     | RCV_INT descop =>
	       let val _        = print ("[--cleaning socket list]\n")
		   val sockets' = clean_sockets descop sockets
		   val _        = print ("[--retrying receive with new socket list]\n")
	       in receive_message_sockets loc infd_op sockets'
	       end
	     | RCV_SYS (descop, err) =>
	       let val _        = print ("[--cleaning socket list]\n")
		   val sockets' = clean_sockets descop sockets
		   val _        = print ("[--retrying receive with new socket list]\n")
	       in receive_message_sockets loc infd_op sockets'
	       end
	     | TRY_FD => receive_message loc infd_op sockets
	     | exc => (print ("[--unknow error while receiving message from sockets]\n"); raise exc)

(* How can we read from either sockets of infd? *)
and receive_message loc infd_op sockets =
    (case infd_op of
	SOME infd =>
	let (*val _   = print ("[receive_message: trying to receive message from internal connection]\n");*)
	    fun rcv n = Posix.IO.readVec (infd, n)
	    val vec = rcv 1
	    val str = vector_to_string vec
     	in case receive_integer_gen loc 2 str "" NONE rcv of
	       SOME n =>
	       let val vec = rcv n
		   val len = Word8Vector.length vec
	       in if len = n
		  then (vector_to_string vec, true, sockets)
		  else raise Fail "receive_message:bad_length"
	       end
	     | NONE => raise Fail "receive_message:fd"
	end
      | NONE => (print ("[receive_message: no internal connection]\n");
		 raise NOT_FD))
    handle Fail str => (print ("[receive_message: Fail error occured(" ^ str ^ ")]\n");
			raise Fail str)
	 | _ => ((*print ("[receive_message: trying to receive message from sockets]\n");*)
		 receive_message_sockets loc infd_op sockets)

fun receive_message' loc sockets =
    let val (msgs, b, sockets') = receive_message loc NONE sockets
    in msgs
    end

(* connect to server using socket.
 * It differs from connect by the fact that if it fails to connect,
 * it creates a new socket. *)
fun connect' socket desc server =
    let val s = addr_to_string server
	val _ = print ("[--n-connecting to " ^ s ^ "]\n")
	val _ = Socket.connect (socket, server)
    in (socket,desc)
    end handle OS.SysErr err =>
	       let val retry_limit = 2
		   val st   = IntInf.toString retry_limit
		   val _    = print ("[--n-cannot connect" ^ print_syserror_msg err ^ ", will retry in " ^ st ^ "s]\n")
		   val _    = Posix.Process.sleep (Time.fromSeconds retry_limit)
		   val _    = print ("[--n-ready to retry, creating a new socket]\n")
		   val sock = INetSock.TCP.socket ()
		   val desc = Socket.sockDesc sock
	       in connect' sock desc server
	       end
	     | exc => (print ("[--n-cannot connect, unknown error]\n"); raise exc)

(* connect to server using socket *)
fun connect socket desc server =
    let val s = addr_to_string server
	val _ = print ("[--connecting to " ^ s ^ "]\n")
	val _ = Socket.connect (socket, server)
    in (socket,desc)
    end handle OS.SysErr err =>
	       let val retry_limit = 2
		   val st = IntInf.toString retry_limit
		   val _  = print ("[--cannot connect" ^ print_syserror_msg err ^ ", will retry in " ^ st ^ "s]\n")
		   val _  = Posix.Process.sleep (Time.fromSeconds retry_limit)
		   val _  = print ("[--ready to retry]\n")
	       in connect socket desc server
	       end
	     | exc => (print ("[--cannot connect, unknown error]\n"); raise exc)

fun send_port_number (SOME port) sock desc =
    let val pstr   = Int.toString port
	val pslice = string_to_slice (pstr ^ "!")
	val _      = print ("[--sending port number " ^ pstr ^ "]\n")
	val _      = send_something (sock, desc) pslice
    in ()
    end
  | send_port_number NONE sock desc = ()

fun connect_to port nsock [] = []
  | connect_to port nsock ((nfo as (id,thost,tport)) :: lst) =
    let val n      = Int.toString (List.length lst + 1)
	val _      = print ("[--still " ^ n ^ " machine(s) to connect to]\n")
	(* -- generates sock (a new socket) and desc (description of the socket) *)
	val sock   = INetSock.TCP.socket ()
	val desc   = Socket.sockDesc sock
	(* -- server to which we have to connect -- *)
	val addr   = Option.valOf (NetHostDB.fromString (NT.dest_ihost thost))
	val server = INetSock.toAddr (addr, NT.dest_iport tport)
	(* -- tries to connect to server using socket sock -- *)
	val (sock,desc) =
	    if nsock
	    then connect' sock desc server
	    else connect  sock desc server
	(* -- sends port number to server -- *)
	val _      = send_port_number port sock desc
    in (add_socket_desc sock desc nfo) :: (connect_to port nsock lst)
    end

fun remove_address_from_list addr port lst =
    let val (ip,_) = INetSock.fromAddr addr
    in List.partition
	   (fn (id,thost,tport) =>
	       let val h = NT.dest_ihost thost
		   val p = NT.dest_iport tport
	       in h = NetHostDB.toString ip andalso p = port
	       end)
	   lst
    end

fun dest_pair_debug n pair =
    (NT.dest_pair n pair)
    handle exc =>
	   (print (NT.toStringTerm pair ^ "\n"); raise exc)

fun send_nuprl_messages_to_itself outfd [] = print ("[sent messages to myself]\n")
  | send_nuprl_messages_to_itself outfd (msg :: msgs) =
    let val (slen, slice) = pack_nuprl_message msg
	val _ = Posix.IO.writeVec (outfd, slen)
	val _ = Posix.IO.writeVec (outfd, slice)
    in send_nuprl_messages_to_itself outfd msgs
    end

fun parse_message_debug n string prt =
    let val str = string
    in PN.parseString prt [] string
    end handle exn =>
	       (print ("\n-EXC("
		       ^ Int.toString n
		       ^ ")----------------------\n"
		       ^ string
		       ^ "\n--------------------------\n");
		raise exn)

fun mk_client_sock_info sock addr =
    let val (host,port) = INetSock.fromAddr addr
	val shost       = NetHostDB.toString host
	val loc         = NT.mk_nuprl_mkid_term  "client"  (* Never used *)
	val thost       = NT.mk_nuprl_ihost_term shost     (* Never used *)
	val tport       = NT.mk_nuprl_iport_term port      (* Never used *)
	val desc        = Socket.sockDesc sock
	val sockets     = [(loc,thost,tport,sock,desc)]
    in sockets
    end

fun print_messages msgs =
    app (fn msg =>
	    ((*print (NT.toStringTerm msg ^ "msg" ^ "\n");*)
	     print (NT.nuprlTerm2eml msg ^ "\n")))
	msgs

exception CONN_HANDLE
exception CONN_LOOP

fun handle_new_connection loc gc outfd sock addr =
    let val saddr   = addr_to_string addr
	val _       = print ("[--received new connection request from " ^ saddr ^ "]\n")
	val sockets = mk_client_sock_info sock addr
	fun loop () =
	    let val msgstr = receive_message' loc sockets
		val msgs   = parse_message_debug 1 msgstr false
		val _      = print ("[--received input messages from " ^ saddr ^ "]\n")
		val _      = print_messages msgs
		(*val _      = print "[--closing socket]\n"
		val _      = Socket.close sock*)
		val _      = print "[--sending message to myself]\n"
		val _      = send_nuprl_messages_to_itself outfd msgs
	    in loop ()
	    end
    in loop ()
    end handle _ => raise CONN_HANDLE

fun keep_listening_for_inputs_aux loc gc outfd server =
    let val (sock,addr) = Socket.accept server
    in case Posix.Process.fork () of
		SOME child => keep_listening_for_inputs_aux loc gc outfd server
	      | NONE => handle_new_connection loc gc outfd sock addr
    end handle CONN_HANDLE => raise CONN_HANDLE
	     | _ => raise CONN_LOOP

fun keep_listening_for_inputs loc gc outfd server =
    let val _ = reset_all ()
	val _ = if gc then MLton.GC.collect() else ()
    in keep_listening_for_inputs_aux loc gc outfd server
    end

fun waiting_on_connection loc socket =
    let val (sock,addr) = Socket.accept socket
	val _           = add_a_sock_ref sock
	val desc        = Socket.sockDesc sock
	val _           = print ("[--received connection request from " ^ addr_to_string addr ^ "]\n")
	val client_port =
	    case receive_integer loc "" sock desc of
		SOME p => p
	      | NONE => raise Fail "waiting_on_connection:received_non_int_data"
	val _           = print ("[--received port number " ^ Int.toString client_port ^ "]\n")
    in (sock,desc,addr,client_port)
    end

fun wait_for_connections loc server [] = []
  | wait_for_connections loc server lst =
    let val n                     = Int.toString (List.length lst)
	val _                     = print ("[--waiting on " ^ n ^ " connection(s)]\n")
	val (sock,desc,addr,port) = waiting_on_connection loc server
	val (connected,lst')      = remove_address_from_list addr port lst
	val sockets               = map (add_socket_desc sock desc) connected
    in sockets @ (wait_for_connections loc server lst')
    end

fun boot_up_prog ev gc ident spec lib alldefs id params extra =
    let (* -- load library and generates program -- *)
	val _     = print ("[type checking and loading library]\n")
	(* -- *)
	val poly  = true
	val btyp  = true
	val prt   = default_prt
	val sub   = default_sub
	val obid  = default_obid
	val time  = default_time
	(* -- *)
	(* -- Generate program from specification -- *)
	val terms = toNuprl spec NONE lib alldefs obid time sub prt (true, true) poly btyp extra
	(* -- Load component -- *)
	val _     = print ("[loading component]\n")
	val prog  = load_program ev gc ident params id extra
    in prog
    end

fun boot_up_conn loc nsock ip port groups conns =
    let (* -- Split the locations into those with lower ip/port and those with greater -- *)
	val (lt, gt) = split_locations (ip, port) groups conns
	val lt_size  = Int.toString (List.length lt)
	val gt_size  = Int.toString (List.length gt)
	val _        = print ("[" ^ lt_size ^ " lower machine(s), " ^ gt_size ^ " higher machine(s)]\n")
	(* -- create a server socket -- *)
	val _             = print ("[starting sever socket]\n")
	val (server,addr) = create_server_socket (ip, port)
	(* -- connect to machines with higher ip/port -- *)
	val _       = print ("[connecting to higher machines]\n")
	val lst_gt  = connect_to (SOME port) nsock gt
	(* -- waits for connections from machines with lower ip/port -- *)
	val _       = print ("[waiting on connections from lower machines]\n")
	val lst_lt  = wait_for_connections loc server lt
	(*(* -- waits for connections from other machines -- *)
	val _       = print ("[connecting to other machines]\n")
	val lst_ot  = wait_for_connections server locs'*)
    in (server, lst_lt @ lst_gt (*@ lst_ot*))
    end

fun boot_up nsock ev gc ident config spec lib alldefs extra =
    let (* ------ reading configuration file ------ *)
	val _     = print ("[reading configuration file]\n")
	val (groups,conns,params,msgs) = load_config_parse config
	val (id, loc, ip, port) =
	    case get_id_in_groups ident groups (* extract own location *) of
		SOME (id,thost,tport) =>
		let val loc  = NT.dest_id id
		    val ip   = NT.dest_ihost thost
		    val port = NT.dest_iport tport
		in (id, loc, ip, port)
		end
	      | NONE => raise Fail "[unknown location]\n"
	(* -- *)
	(* ------ generating connections ------ *)
	val _     = print ("[connecting]\n")
	val (server, sockets) = boot_up_conn loc nsock ip port groups conns
	val {infd, outfd} = Posix.IO.pipe ()
	val _     = Posix.IO.setfl (infd, Posix.IO.O.nonblock)
	val _     =
	    case Posix.Process.fork () of
		SOME child => (* parent *)
		let val word = Posix.Process.pidToWord child
		in print ("[forking listner: " ^ SysWord.toString word ^ "]\n")
		end
	      | NONE => keep_listening_for_inputs loc gc outfd server (* child *)
	(* -- *)
	(* ------ loading program ------ *)
	val _     = print ("[loading program]\n")
	val prog  = boot_up_prog ev gc ident spec lib alldefs id params extra
    in (loc, prog, server, sockets, infd)
    end

fun run_distributed_program2 nsock ev gc ident config spec lib alldefs prt extra =
    let val _     = print "[booting up]\n"
	val (loc, term, server, sockets, infd) =
	    boot_up nsock ev gc ident config spec lib alldefs extra
	val _     = print "[running process]\n"
	fun loop sockets internal_messages prog (*n*) =
	    let val progop =
		    if is_newprog_extra extra
		    then if NT.is_nuprl_inl_term prog
			 then SOME (NT.dest_inl prog)
			 else if NT.is_nuprl_inr_term prog
			 then NONE
			 else (dump_prog [] prog NT.toStringTerm;
			       raise Fail ("run_stepper:newprog:not_inl_or_inr("
					   ^ NT.opid_of_term prog
					   ^ ")"))
		    else SOME prog
	    in case progop of
		   SOME prog =>
		   let val _ = if gc then MLton.GC.collect() else ()
		       val (msg, rest, sockets') =
			   case internal_messages of
			       [] =>
			       let val _ = print ("[process waiting for a new message]\n")
				   val (msgstr,b,sockets') = receive_message loc (SOME infd) sockets
			       in case parse_message_debug 3 msgstr prt of
				      [msg] => (msg, [],sockets')
				    | _ => raise Fail "run_program"
			       end
			     | (msg :: msgs) => (msg, msgs, sockets)
		       (* Note that this is not fair because all the internal
			* messages will be dealt with first. *)
		       (*val _             = print ("[size: " ^ Int.toString (NT.size prog) ^ "]\n")*)
		       (*val _             = print ("[size: " ^ Int.toString (NT.size prog) ^ "," ^ Int.toString (NT.env_size prog) ^ "]\n")*)
		       (*val _             = dump_prog_stream prog ("output-term-" ^ loc)*)
		       val _             = print "[received message]\n"
		       val _             = print (NT.nuprlTerm2eml msg ^ "\n")
		       (*val _             = print (NT.toStringTerm msg ^ "\n")*)
		       val toeval        = nuprl_all (nuprl_app prog msg)
		       val (prog1,steps) = ev [] (~1) toeval
		       val _             = print ("[" ^ Int.toString steps ^ " steps]\n")
		       val (prog2,msgs)  = NT.dest_pair 7 prog1
		       val msgs_lst      = NT.dest_list msgs
		       val _             = print "[sending messages]\n"
		       val _             = print_message_list 1 msgs_lst
		       val msgs_slf      = send_nuprl_messages loc sockets' msgs_lst
		       val _             = print "[messages sent]\n"
		   in (*if n > k
			then print ("[DONE]\n")
			else*) loop sockets' (rest @ msgs_slf) prog2 (*(n+1)*)
		   end
		 | NONE => print "[program finished]\n"
	    end
    in loop sockets [] term (*0*)
    end

fun run_distributed_program2_extra lim nsock ev gc ident config spec lib alldefs prt extra =
    let val _     = print "[booting up]\n"
	val (loc, term, server, sockets, infd) =
	    boot_up nsock ev gc ident config spec lib alldefs extra
	val _     = print "[running process]\n"
	fun loop sockets internal_messages prog n =
	    let val progop =
		    if is_newprog_extra extra
		    then if NT.is_nuprl_inl_term prog
			 then SOME (NT.dest_inl prog)
			 else if NT.is_nuprl_inr_term prog
			 then NONE
			 else (dump_prog [] prog NT.toStringTerm;
			       raise Fail ("run_stepper:newprog:not_inl_or_inr("
					   ^ NT.opid_of_term prog
					   ^ ")"))
		    else SOME prog
	    in case progop of
		   SOME prog =>
		   let val (msg, rest, sockets') =
			   case internal_messages of
			       [] =>
			       let val (msgstr,b,sockets') = receive_message loc (SOME infd) sockets
			       in case parse_message_debug 4 msgstr prt of
				      [msg] => (msg, [], sockets')
				    | _ => raise Fail "run_program"
			       end
			     | (msg :: msgs) => (msg, msgs, sockets)
		       (* Note that this is not fair because all the internal
			* messages will be dealt with first. *)
		       (*val _             = print ("[size: " ^ Int.toString (NT.size prog) ^ "]\n")*)
		       (*val _             = print ("[size: " ^ Int.toString (NT.size prog) ^ "," ^ Int.toString (NT.env_size prog) ^ "]\n")*)
		       (*val _             = dump_prog_stream prog ("output-term-" ^ loc)*)
		       val _             = print "[received message]\n"
		       val _             = print (NT.nuprlTerm2eml msg ^ "\n")
		       val toeval        = nuprl_all (nuprl_app prog msg)
		       val (prog1,steps) = ev [] (~1) toeval
		       val _             = print ("[" ^ Int.toString steps ^ " steps]\n")
		       val (prog2,msgs)  = NT.dest_pair 8 prog1
		       val msgs_lst      = NT.dest_list msgs
		       val _             = print "[sending messages]\n"
		       val _             = print_message_list 1 msgs_lst
		       val msgs_slf      = send_nuprl_messages loc sockets msgs_lst
		       val _             = print "[messages sent]\n"
		   in if n > lim
		      then print ("[DONE]\n")
		      else loop sockets' (rest @ msgs_slf) prog2 (n + 1)
		   end
		 | NONE => print "[program finished]\n"
	    end
    in loop sockets [] term 0
    end

fun run_distributed_program extra ev gc ident config spec lib alldefs prt =
    let val F =
	    case get_int_extra extra of
		SOME (EX_INT n) => run_distributed_program2_extra n
	      | _ => run_distributed_program2
	val () = F (is_nsock_extra extra) ev gc ident config spec lib alldefs prt extra
	val _ = print ("[process terminated without error]\n")
    in ()
    end handle CONN_HANDLE => print ("[connection handler died]\n")
	     | CONN_LOOP   => print ("[listner died]\n")


(* This is just for testing purposes, this is never going to be used. *)
(*fun simulate_clients_server config =
    let val (locations, locations', params, messages) = load_config_parse config
	fun listen_and_print sock =
	    let val sockets = wait_for_connections sock locations
		val descs   = map select_desc sockets
		fun loop () =
		    let val msgstr = receive_message NONE sockets descs
		    in case parse_message_debug 6 msgstr false of
			   [msg] =>
			   let val _ =  print ("\n-------------\n"
					       ^ "received: "
					       ^ NT.nuprlTerm2eml msg
					       ^ "\n-------------\n")
			   in loop ()
			   end
			 | _ => raise Fail "simulate_clients:listen_and_print"
		    end
	    in loop ()
	    end
	fun start_listening_sockets [] = []
	  | start_listening_sockets ((id, thost, tport) :: lst) =
	    let val h = NT.dest_ihost thost
		val p = NT.dest_iport tport
		val (sock, addr) = create_server_socket (h,p)
		val _ =
		    case Posix.Process.fork () of
			SOME pid => () (* parent *)
		      | NONE => listen_and_print sock (* child *)
	    in start_listening_sockets lst
	    end
	val _ = print "[waiting on connections]\n"
	val _ = start_listening_sockets locations'
    in ()
    end*)

fun simulate_clients_server config =
    let val (groups,_,_,_) = load_config_parse config
	val _       = print ("[--connecting to other machines]\n")
	val sockets = connect_to NONE false (get_external_locs_from_groups groups)
	val _       = print ("[--ready to receive messages from other machines]\n")
	fun loop sockets =
	    let val (msgstr,b,sockets') = receive_message_sockets "client" NONE sockets
		val _ = print ("\n-------------\n"
			       ^ "received: "
			       ^ msgstr
			       ^ "\n-------------\n")
	    in loop sockets'
	    end
    in loop sockets
    end

fun simulate_clients_send config alldefop prt gc =
    let	val lib =
	    case alldefop of
		SOME f =>
		let val _     = print ("[parsing Nuprl library]\n")
		    val terms = PN.parse prt NT.to_filter_out f false
		    val _     = print ("[generating EML library]\n")
		    val lib   = NT.terms2map terms
		    val _     = NT.print_lib_stats lib
		in lib
		end
	      | NONE => NT.emlib ()
	val strm = TextIO.stdIn
	val cid  = ref 1
	fun send_intransit_messages locs [] = ()
	  | send_intransit_messages locs (dmsg :: msgs) =
	    let val (id,msg) = NT.dest_pair 10 dmsg
	    in case get_ip_port_in_locs id locs of
		   SOME (nfo as (id,thost,tport)) =>
		   let val sock    = INetSock.TCP.socket ()
		       val h       = NT.dest_ihost thost
		       val p       = NT.dest_iport tport
		       val addr    = Option.valOf (NetHostDB.fromString h)
		       val server  = INetSock.toAddr (addr, p)
		       val s       = addr_to_string server
		       val _       = print ("[connecting to " ^ s ^ "]\n")
		       val _       = Socket.connect (sock, server)
		       val sockets = [add_socket sock nfo]
		       val _       = print ("[sending message to " ^ s ^ "]\n")
		       val _       = send_nuprl_message sockets id msg
		       val _       = print ("[message sent]\n")
		       val _       = print ("[closing socket]\n")
		       val _       = Socket.close sock
		       val _       = print ("[socket closed]\n")
		   in send_intransit_messages locs msgs
		   end
		 | NONE =>
		   let val _ = print "[unknown location]\n"
		   in send_intransit_messages locs msgs
		   end
	    end
	fun aux msgop =
	    let val (groups,_,_,msgs) = load_config_parse config
		val locs = get_internal_locs_from_groups groups
		val msgs =
		    case msgop of
			NONE => msgs
		      | SOME msg => load_config_parse_str msg
		val time = Time.toMilliseconds (Time.now ())
		val _    = print ("[unfolding messages(" ^ LargeInt.toString time ^ "ms)]\n")
		val msgs = map (NT.unfold_all lib) msgs
		val _    = if gc then MLton.GC.collect() else ()
		val time = Time.toMilliseconds (Time.now ())
		val _    = print ("[sending intransit messages(" ^ LargeInt.toString time ^ "ms)]\n")
		val _    = send_intransit_messages locs msgs
		val _    = print "send? "
	    in case TextIO.inputLine strm of
		   NONE       => aux NONE
		 | SOME ""    => aux NONE
		 | SOME "\n"  => aux NONE
		 | SOME "sp\n" =>
		   let val c = Int.toString (!cid)
		       val _ = cid := !cid + 1
		   in aux (SOME ("rep1 : (``swap``, (Int * Tok List), (" ^ c ^ ",``paxos``))"))
		   end
		 | SOME "st\n" =>
		   let val c = Int.toString (!cid)
		       val _ = cid := !cid + 1
		   in aux (SOME ("rep1 : (``swap``, (Int * Tok List), (" ^ c ^ ",``2/3``))"))
		   end
		 | SOME "c\n" =>
		   let val c = Int.toString (!cid)
		       val _ = cid := !cid + 1
		   in aux (SOME ("rep1 : (``bcast``, (Int * Tok List), (" ^ c ^ ",``" ^ c ^ "``))"))
		   end
		 | SOME msg   => aux (SOME msg)
	    end
	val _ = print "send? "
    in case TextIO.inputLine strm of
	   NONE       => aux NONE
	 | SOME ""    => aux NONE
	 | SOME "\n"  => aux NONE
	 | SOME "sp\n" =>
	   let val c = Int.toString (!cid)
	       val _ = cid := !cid + 1
	   in aux (SOME ("rep1 : (``swap``, (Int * Tok List), (" ^ c ^ ",``paxos``))"))
	   end
	 | SOME "st\n" =>
	   let val c = Int.toString (!cid)
	       val _ = cid := !cid + 1
	   in aux (SOME ("rep1 : (``swap``, (Int * Tok List), (" ^ c ^ ",``2/3``))"))
	   end
	 | SOME "c\n" =>
	   let val c = Int.toString (!cid)
	       val _ = cid := !cid + 1
	   in aux (SOME ("rep1 : (``bcast``, (Int * Tok List), (" ^ c ^ ",``" ^ c ^ "``))"))
	   end
	 | SOME msg   => aux (SOME msg)
    end

fun run_other_machine extra ident config prt =
    let val (groups,_,_,_) = load_config_parse config
	val locs  = get_internal_locs_from_groups groups
	val locs' = get_external_locs_from_groups groups
	(* -- checks whethere ip/port is in the configuration file -- *)
	val nsock = is_nsock_extra extra
	val str   = ident_to_string ident
	val (loc,host,port) =
	    case get_id_in_locs ident locs' of
		SOME (id,thost,tport) => (NT.dest_id id, NT.dest_ihost thost, NT.dest_iport tport)
	      | NONE => raise Fail ("[unknown location" ^ str ^ "\n")
	(* -- connects to the other machines -- *)
	val _              = print ("[connecting to machines]\n")
	val sockets        = connect_to (SOME port) nsock locs
	(* -- waits on a connection request from some client -- *)
	val _              = print ("[starting sever socket]\n")
	val (sock,addr)    = create_server_socket (host, port)
	val (client,caddr) = Socket.accept sock
	val (chost,cport)  = INetSock.fromAddr caddr
	val scaddr  = addr_to_string caddr
	val _       = print ("[--received connection request from " ^ scaddr ^ "]\n")
	val schost  = NetHostDB.toString chost
	val cloc    = NT.mk_nuprl_mkid_term  "client"
	val tchost  = NT.mk_nuprl_ihost_term schost
	val tcport  = NT.mk_nuprl_iport_term cport
	val cdesc   = Socket.sockDesc client
	val clients = [(cloc,tchost,tcport,client,cdesc)]
	val _       = print ("[--ready to receive messages and forward to " ^ scaddr ^ "]\n")
	(* -- forwards to client messages received from internal locations --  *)
	fun internal sockets =
	    let val (msgstr,b,sockets') = receive_message_sockets loc NONE sockets
		val time = Time.toMilliseconds (Time.now ())
		val _    = print ("[received message at " ^ LargeInt.toString time ^ "ms]\n")
		val _    = print ("\n-------------\nreceived:\n"
				  ^ msgstr
				  ^ "\n-------------\n")
	    in case parse_message_debug 7 msgstr prt of
		   [msg] =>
		   let val str = NT.nuprlTerm2eml msg
		       val _   = send_message clients cloc str
		   in internal sockets'
		   end
		 | _ => raise Fail "run_program"
	    end
    in internal sockets
    end

exception DONE

fun start_all_machines ev gc config spec lib alldefs prt extra =
    let val (groups,_,_,_) = load_config_parse config
	val locs  = get_internal_locs_from_groups groups
	val locs' = get_external_locs_from_groups groups
	val _ =
	    List.app (fn (id,thost,tport) =>
			 case Posix.Process.fork () of
			     SOME child => ()
			   | NONE =>
			     let val _ = run_other_machine extra (Loc (NT.dest_id id)) config prt
			     in raise DONE
			     end)
		     locs'
	val _ =
	    List.app (fn (id,thost,tport) =>
			 case Posix.Process.fork () of
			     SOME child => ()
			   | NONE =>
			     let val _ = run_distributed_program extra ev gc (Loc (NT.dest_id id)) config spec lib alldefs prt
			     in raise DONE
			     end)
		     locs
    in ()
    end handle DONE => ()

(* ------ TESTING ------ *)

fun testing n =
    let val str = "{make-Msg:OPID}\n({cons:OPID}\n ({token:OPID,propose:t}();\n  {nil:OPID}());\n {product:OPID}\n ({int:OPID}();\n  {bound_id:OPID,:v}\n  ({int:OPID}()));\n {pair:OPID}\n ({natural_number:OPID,12:n}();\n  {natural_number:OPID,4:n}()))"
	val _ = parse_message_debug 8 str true
    in ()
    end

fun testing n =
    let val str = "{make-Msg:OPID}\n({cons:OPID}\n ({token:OPID,propose:t}();\n  {nil:OPID}());\n {product:OPID}\n ({int:OPID}();\n  {bound_id:OPID,:v}\n  ({int:OPID}()));\n {pair:OPID}\n ({natural_number:OPID,12:n}();\n  {natural_number:OPID,4:n}()))"
    in case parse_message_debug 9 str true of
	   [term] =>
	   (print (NT.toStringTerm term ^ "\n");
	    dump_prog_stream [] term "output-debug-blahblah")
	 | _ => raise Fail "run_program"
    end


(* ------ MAIN ------ *)

fun run args =
    let val {input,  output,  lib,     time,    sub,      sanity,
	     nuprl,  obid,    ascii,   tcheck,  parse,    split,
	     prt,    eval,    alldef,  test,    session,  simul,
	     step,   mono,    host,    port,    conf,     client,
	     send,   other,   all,     ev,      id,       extra,
	     gc} = format args
	val poly = not mono
	val btyp = true
	val (evstr, ev) = (get_ev ev) handle _ => get_ev default_ev
	val _     = print ("[using evalutor " ^ evstr ^ "]\n")
	val ident = if id = "" then Mac (host, port) else Loc id
	(*val _ = print ("[extra:"
		       ^ extra
		       ^ "-"
		       ^ Bool.toString (is_dump_extra extra)
		       ^ "-"
		       ^ Bool.toString (is_haskell_extra extra)
		       ^ "]\n")*)
    in if Option.isSome test
       then testing (Option.valOf test)
       else if parse
       then parseEML input
       else if tcheck
       then typecheck input sub
       else if sanity
       then sanitizer input output lib time sub
       else if nuprl
       then (toNuprl input output lib alldef obid time sub prt (true, true) poly btyp extra; ())
       else if ascii
       then parseNuprl input output prt split extra
       else if Option.isSome eval
       then evaluate input (Option.valOf eval) lib alldef obid sub extra
       else if session
       then start_session ev input lib alldef obid sub extra
       else if Option.isSome step
       then run_stepper (Option.valOf step) ev gc false false input alldef extra
       else if Option.isSome simul
       then start_stepper input (Option.valOf simul) ev gc lib alldef obid time sub prt extra
       else if Option.isSome conf
       then let val config = Option.valOf conf
	    in if client
	       then simulate_clients_server config
	       else if send
	       then simulate_clients_send config alldef prt gc
	       else if other
	       then run_other_machine extra ident config prt
	       else if all
	       then start_all_machines ev gc config input lib alldef prt extra
	       else run_distributed_program extra ev gc ident config input lib alldef prt
	    end
       else slice input output lib time sub
    end

end
