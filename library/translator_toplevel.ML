signature ML_TRANSLATOR_TOP = sig

type reporter = { succeed: Position.T * string -> unit,
                  start: Position.T -> bool,
                  fail : Position.T * exn -> unit }

val interactive_reporter : unit -> reporter
(*val socket_reporter : BinIO.StreamIO.instream * BinIO.StreamIO.outstream
                   -> reporter*)

val init_translator : Path.T -> reporter -> unit
val translate_src   : REPL.cfg -> string -> unit
val translate_file  : string (*path*) -> unit

val REPL_App : REPL_Server.App

end

structure ML_Translator_Top : ML_TRANSLATOR_TOP = struct

exception Translation_Fail = MinLang_Translator.Translation_Fail

local

fun is_proof_command (Command_Span.Command_Span (name, _)) =
      member (op =) ["lemma", "theorem", "schematic_goal", "proposition", "corollary",
                     "interpretation", "global_interpretation", "sublocale"] name
  | is_proof_command _ = false
fun is_proof_command' (Command_Span.Span (k, _)) = is_proof_command k

val extract_proof =
  let datatype ele = FWD | BWD
      fun pop _ [] = raise MinLang_Translator.Unsupported "Malformed Source"
        | pop k (k'::SK) = if k = k' then SK else raise MinLang_Translator.Unsupported "Malformed Source"
      fun pass [] _ = []
        | pass stack ((_, sp as Command_Span.Span (Command_Span.Command_Span (name, _), _)) :: L)
            = (case name
                 of "proof" => sp :: pass (FWD :: stack) L
                  | "qed"   => sp :: pass (stack |> pop FWD |> pop BWD) L
                  | "have"  => sp :: pass (BWD :: stack) L
                  | "show"  => sp :: pass (BWD :: stack) L
                  | "hence" => sp :: pass (BWD :: stack) L
                  | "thus"  => sp :: pass (BWD :: stack) L
                  | "consider"  => sp :: pass (BWD :: stack) L
                  | "obtain"    => sp :: pass (BWD :: stack) L
                  | "interpret" => sp :: pass (BWD :: stack) L
                  | "subgoal"   => sp :: pass (BWD :: stack) L
                  | "by"    => sp :: pass (pop BWD stack) L
                  | "done"  => sp :: pass (pop BWD stack) L
                  | "apply_end" => sp :: pass (pop BWD stack) L
                  | "."     => sp :: pass (pop BWD stack) L
                  | ".."    => sp :: pass (pop BWD stack) L
                  |  _      => sp :: pass stack L
              )
        | pass _ _ = raise Translation_Fail "Malformed Source"
   in pass [BWD]
  end

in

type reporter = { succeed: Position.T * string -> unit,
                  start: Position.T -> bool,
                  fail : Position.T * exn -> unit }

fun interactive_reporter () =
  let val success = Unsynchronized.ref 0
      val total   = Unsynchronized.ref 0
   in { succeed = (fn (pos, str) => (
            success := !success + 1
          ; REPL.origin_tracing [("Translated line " ^ string_of_int (the (Position.line_of pos))),
                                 ", succeeded ", string_of_int (!success), "/", string_of_int (!total),
                                 "\n", str]
        )),
        fail   = (fn (pos, E) =>
            REPL.origin_warning ( "Fail to translate " :: string_of_int (the (Position.line_of pos)) ::
                                  ", succeeded " :: string_of_int (!success) :: "/" :: string_of_int (!total)
                               :: "\n" :: Runtime.exn_message_list E )
        ),
        start  = (fn _ => (total := !total +1; true))
      }
   end

fun REPL_plugin reporter : REPL.collector = fn {current_command, state, remaining} =>
  if is_proof_command' current_command andalso
     Toplevel.is_proof state andalso
     let val st = #goal (Proof.raw_goal (Toplevel.proof_of state))
      in not (Thm.is_dummy st) andalso not (Thm.no_prems st)
     end
  then let val pos  = case hd remaining
                   of (_, Command_Span.Span (Command_Span.Command_Span (_, pos), _)) => pos
                    | _ => raise Translation_Fail "Malformed Source"
   in if #start reporter pos
    then let
        val prf = extract_proof remaining
               |> map (fn Command_Span.Span (_, src) => filter Token.is_proper src)
        val ast' = MinLang_Translator.translate_m (state, prf)
        val str  = MinLang_Translator.print_mast true ast'
     in #succeed reporter (pos, str)
      ; (NONE, NONE)
    end handle E => (
      #fail reporter (pos, E)
    ; (NONE, NONE))
    else (NONE, NONE)
  end else (NONE, NONE)
  
(* fun translate_thy src *)

end

fun init_translator base_dir_of_theories reporter = (
      REPL.init_repler base_dir_of_theories NONE
    ; REPL.set_register_thy false
    ; REPL.register_plugin ("MinLang.Translator", REPL_plugin reporter)
    ; REPL.add_evaluated_theories ("Minilang.Minilang_Base", \<^theory>\<open>Minilang_Base\<close>) )

fun translate_src cfg src = (REPL.RE cfg src; ())

fun translate_file path =
  let val path' = Path.explode path
      val thy_qualifier = the_default "HOL" (REPL_Aux.parse_session_name path')
      val src = File.read path'
   in translate_src { thy_qualifier = thy_qualifier,
                      file = SOME path,
                      position_label = NONE,
                      additional_libs = ["Minilang.Minilang_Base"] }
                    src
  end


fun pos_packer pos =
  let open MessagePackBinIO.Unpack MessagePackBinIO.Pack
      val {line, offset, end_offset, props} = Position.dest pos
      val {label, file, id} = props
   in packTuple4 (packInt, packInt, packInt, packTuple3 (packString, packString, packString))
      (line, offset, end_offset, (label, file, id))
  end

fun socket_reporter (cin,cout) =
  let open MessagePackBinIO.Unpack MessagePackBinIO.Pack
   in { start = (fn pos =>
          let val _ = doPack (packPair (packInt, pos_packer)) (0, pos) cout 
              val _ = BinIO.StreamIO.flushOut cout
              val (ret, cin') = doUnpack unpackBool (!cin)
           in cin := cin'
           ; ret
          end),
        fail  = (fn (pos, E) => (
            doPack (packTuple3 (packInt, pos_packer, packString))
                   (1, pos, Minilang_Aux.trim_markup (String.concat (Runtime.exn_message_list E))) cout
          ; BinIO.StreamIO.flushOut cout )),
        succeed = (fn (pos, str) => (
            doPack (packTuple3 (packInt, pos_packer, packString))
                   (2, pos, str) cout
          ; BinIO.StreamIO.flushOut cout ))
      }
  end

fun REPL_App (cin, cout) =
  let open MessagePackBinIO.Unpack MessagePackBinIO.Pack
      val (path, cin') = doUnpack unpackString cin
      val cin = Unsynchronized.ref cin'
   in REPL.register_plugin ("MinLang.Translator", REPL_plugin (socket_reporter (cin,cout)))
    ; translate_file path
    ; doPack packInt 3 cout
    ; BinIO.StreamIO.flushOut cout
    ; !cin
  end

end