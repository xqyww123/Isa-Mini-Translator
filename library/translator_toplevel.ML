signature ML_TRANSLATOR_TOP = sig

type reporter = { report : Position.T (*position of goal statement*)
                         * Position.T (*position of the first line of the proof*)
                         * (string * (string (*translation result*) * exn list (*errors*))) list
                        -> unit,
                  error : exn -> unit,
                  start: Position.T -> bool,
                  declaration : Position.T * string -> unit,
                  new_thy : Position.T * Thy_Header.header -> unit }

val interactive_reporter : unit -> reporter
(*val socket_reporter : BinIO.StreamIO.instream * BinIO.StreamIO.outstream
                   -> reporter*)

val init_translator : string list (*targets*) -> Path.T -> reporter -> unit
val translate_src   : REPL.cfg -> string -> unit
val translate_file  : string (*path*) -> unit

val REPL_App : REPL_Server.App

end

structure ML_Translator_Top : ML_TRANSLATOR_TOP = struct

exception Translation_Fail = MinLang_Translator.Translation_Fail
exception Bad_Source = MinLang_Translator.Bad_Source

local

fun is_goal_command (Command_Span.Command_Span (name, _)) =
      member (op =) ["lemma", "theorem", "schematic_goal", "proposition", "corollary",
                     "interpretation", "global_interpretation", "sublocale"] name
  | is_goal_command _ = false
fun is_goal_command' (Command_Span.Span (k, _)) = is_goal_command k

fun is_theory (Command_Span.Command_Span (name, _)) = name = "theory"
  | is_theory _ = false
fun is_theory' (Command_Span.Span (k, _)) = is_theory k

fun is_end (Command_Span.Command_Span (name, _)) = name = "end"
  | is_end _ = false
fun is_end' (Command_Span.Span (k, _)) = is_end k

fun is_declarative (Command_Span.Command_Span (name, _)) =
  member (op =) ["adhoc_overloading", "alias", "axiomatization", "class", "coinductive",
                 "coinductive_set", "consts", "datatype", "definition", "fun",
                 "function", "lift_definition", "overloading", "primcorec", "primcorecursive",
                 "primrec", "quotient_definition", "quotient_type", "record", "specification",
                 "type_alias", "type_synonym", "typedecl", "typedef", "chapter", "context",
                 "corollary", "instance", "instantiation", "interpretation",
                 "lemma", "lemmas", "locale", "notation", "paragraph", "proposition",
                 "schematic_goal", "section", "subclass", "sublocale", "subparagraph", "subsection",
                 "subsubsection", "syntax", "syntax_declaration", "text", "text_raw", "theorem",
                 "txt", "type_notation", "codatatype", "inductive", "inductive_set"]
        name
  | is_declarative _ = false
fun is_declarative' (Command_Span.Span (k, _)) = is_declarative k

fun has_begin_tail toks =
  let val toks' = filter Token.is_proper toks
      val tok = List.last toks'
   in Token.is_kind Token.Keyword tok andalso
      Token.content_of tok = "begin"
  end handle List.Empty => false

in

type reporter = { report : Position.T (*position of goal statement*)
                         * Position.T (*position of the first line of the proof*)
                         * (string * (string (*translation result*) * exn list (*errors*))) list
                        -> unit,
                  start: Position.T -> bool,
                  error : exn -> unit,
                  declaration : Position.T * string -> unit,
                  new_thy : Position.T * Thy_Header.header -> unit }

fun interactive_reporter () =
  let val success = Unsynchronized.ref 0
      val total   = Unsynchronized.ref 0
   in { report = (fn (_, pos, rets) => (
            if forall (null o snd o snd) rets
            then ( success := !success + 1 ;
                   REPL.origin_tracing ([("Translated line " ^ string_of_int (the (Position.line_of pos))),
                                 ", succeeded ", string_of_int (!success), "/", string_of_int (!total),
                                 "\n"] @ maps (fn (k,(v,_)) => [k," : ",v,"\n"]) rets) )
            else REPL.origin_warning (
                        "Fail to translate " :: string_of_int (the (Position.line_of pos)) ::
                        ", succeeded " :: string_of_int (!success) :: "/" :: string_of_int (!total)
                     :: "\n" :: [String.concatWith "\n" (maps (
                              map (String.concat o Runtime.exn_message_list) o snd o snd) rets)] )
        )),
        error = (fn exn => REPL.origin_warning (Runtime.exn_message_list exn)),
        start  = (fn _ => (total := !total +1; true)),
        declaration = (fn (pos, str) =>
            REPL.origin_warning [str]),
        new_thy = (fn x => ((@{print} x); ()))
      }
   end

val end_counter' = Thread_Data.var ()
fun end_counter () =
  case Thread_Data.get end_counter'
    of SOME rf => rf
     | NONE => let val rf = Unsynchronized.ref []
                in Thread_Data.put end_counter' (SOME rf)
                 ; rf
               end

fun REPL_plugin targets reporter : REPL.collector = fn cfg => fn {current_command, state, remaining} =>
  let val cnt = end_counter ()
      val Command_Span.Span (_, toks) = current_command
      val pos = case current_command of Command_Span.Span (Command_Span.Command_Span (_, pos), _) => pos
                   | _ => Position.none
      val next_pos = case remaining
                  of (_, Command_Span.Span (Command_Span.Command_Span (_, pos), _)) :: _ => pos
                   | _ => Position.none
      fun report_decl () =
        if is_theory' current_command
        then let
             val header = Thy_Header.read_tokens Position.none toks
             fun qualify name = if Long_Name.is_qualified name then name
                                else Long_Name.qualify (#thy_qualifier cfg) name
             fun qualify_name {name,imports,keywords} =
                    {name = apfst qualify name,
                     imports = map (apfst qualify) imports,
                     keywords = keywords}
             val header = qualify_name header
          in cnt := [true]
           ; #new_thy reporter (pos, header)
           ; #declaration reporter (pos, String.concat (Minilang_Aux.print_toks toks))
         end
        else let val is_decl = is_declarative' current_command
          in if has_begin_tail toks
             then cnt := is_decl :: !cnt
             else ()
           ; if is_decl
        then #declaration reporter (pos, String.concat (Minilang_Aux.print_toks toks))
        else if is_end' current_command
        then let
             val print :: cnt' = !cnt
          in cnt := cnt'
           ; if print
             then #declaration reporter (pos, "end")
             else ()
         end
        else ()
         end
   in report_decl ()
   ; if is_goal_command' current_command andalso
        Toplevel.is_proof state andalso
         let val st = #goal (Proof.raw_goal (Toplevel.proof_of state))
          in not (Thm.is_dummy st) andalso not (Thm.no_prems st)
         end
    then if #start reporter pos
      then let
          val ret = Unsynchronized.ref []
          val prf_spans = Minilang_Aux.extract_proof remaining
          val prf = map (fn (_, Command_Span.Span (_, src)) => filter Token.is_proper src) prf_spans
          
          val origin = String.concatWith "\n" (map (String.concat o Minilang_Aux.print_toks) prf)
          val spec   = String.concat (Minilang_Aux.print_toks toks)
          val _ =
              if member (op =) targets "origin"
              then ret := ("origin", (origin, [])) :: !ret
              else ()
          val _ =
              if member (op =) targets "goal"
              then ret := ("goal", (spec, [])) :: !ret
              else ()
          val _ =
              if member (op =) targets "isar-SH"
              then \<^try>\<open>
                let val thor = Thor.translate_thor false state prf_spans
                 in ret := ("isar-SH", (thor, [])) :: !ret
                end 
                catch E =>
                    ret := ("isar-SH", ("", [E])) :: !ret \<close>
              else ()
          val _ =
              if member (op =) targets "isar-SH*"
              then \<^try>\<open>
                let val thor = Thor.translate_thor true state prf_spans
                 in ret := ("isar-SH*", (thor, [])) :: !ret
                end 
                catch E =>
                    ret := ("isar-SH*", ("", [E])) :: !ret\<close>
              else ()
          val _ =
              if exists (member (op =) targets) ["refined", "raw", "reord_raw", "reord_refined"]
              then \<^try>\<open>let
                  val asts = MinLang_Translator.translate_m targets (state, prf)
                  val strs = map (apsnd (apfst (MinLang_Translator.print_mast true))) asts
                  val _ = REPL.origin_warning [origin]
               in ret := strs @ !ret
              end catch E =>
                  ret := ("refined", ("", [E])) :: !ret \<close>
              else ()
       in #report reporter (pos, next_pos, !ret)
        ; (NONE, NONE)
      end
      else (NONE, NONE)
    else (NONE, NONE)
  end
  
(* fun translate_thy src *)

end

fun init_translator targets base_dir_of_theories reporter = (
      REPL.init_repler base_dir_of_theories NONE
    ; REPL.set_register_thy false
    ; REPL.register_plugin ("MinLang.Translator", REPL_plugin targets reporter)
    ; REPL.add_evaluated_theories ("Minilang.Minilang_Base", \<^theory>\<open>Minilang_Base\<close>) )

fun translate_src cfg src =
  let val errs = REPL.collect_erros (REPL.RE cfg src) []
   in if null errs
    then ()
    else raise Bad_Source (String.concatWith "\n" errs)
  end

fun translate_file path =
  let val path' = Path.explode path
      val thy_qualifier = the_default "HOL" (REPL_Aux.parse_session_name path')
      val src = File.read path'
      val dir = Path.dir path'
   in \<^try>\<open> (
      REPL.set_base_dir dir
    ; translate_src { thy_qualifier = thy_qualifier,
                      file = SOME path,
                      position_label = NONE,
                      additional_libs = [] (*["Minilang.Minilang_Base"]*),
                      import_dir = NONE }
                    src )
   finally REPL.reset_base_dir () \<close>
  end


fun pos_packer pos =
  let open MessagePackBinIO.Unpack MessagePackBinIO.Pack
      val {line, offset, end_offset, props} = Position.dest pos
      val {label, file, id} = props
   in packTuple4 (packInt, packInt, packInt, packTuple3 (packString, packString, packString))
      (line, offset, end_offset, (label, file, id))
  end

fun thy_packer {name, imports, ...} =
  let open MessagePackBinIO.Unpack MessagePackBinIO.Pack
   in packPair (packString, packList packString) (fst name, map fst imports)
  end

fun socket_reporter (cin,cout) =
  let open MessagePackBinIO.Unpack MessagePackBinIO.Pack
      val packError  = packString o Minilang_Aux.trim_markup o String.concat o Runtime.exn_message_list
      val packErrors = packList packError
   in { start = (fn pos =>
          let val _ = doPack (packPair (packInt, pos_packer)) (0, pos) cout 
              val _ = BinIO.StreamIO.flushOut cout
              val (ret, cin') = doUnpack unpackBool (!cin)
           in cin := cin'
           ; ret
          end),
        report = (fn (pos_spec, pos_proof, rets) => (
            doPack (packTuple4 (packInt, pos_packer, pos_packer,
                                packPairList (packString, packPair (packString, packErrors))))
                   (2, pos_spec, pos_proof, rets) cout
          ; BinIO.StreamIO.flushOut cout )),
        error = (fn exn => (
            doPack (packPair (packInt, packError)) (7, exn) cout
          ; BinIO.StreamIO.flushOut cout )),
        declaration = (fn (pos, line) =>
            (doPack (packTuple3 (packInt, pos_packer, packString))
                    (4, pos, line) cout )),
        new_thy = (fn (pos, header) => (
            doPack (packTuple3 (packInt, pos_packer, thy_packer)) (5, pos, header) cout
          ; BinIO.StreamIO.flushOut cout))
      }
  end

fun REPL_App (cin, cout) =
  let open MessagePackBinIO.Unpack MessagePackBinIO.Pack
      val ((path, targets), cin') = doUnpack (unpackPair (unpackString, unpackList unpackString)) (!cin)
      val _ = cin := cin'

      val KNOWN_TARGETS = ["origin", "isar-SH", "isar-SH*", "refined", "raw", "reord_raw",
                           "reord_refined", "goal"]
      val _ = case find_first (not o member (op =) KNOWN_TARGETS) targets
                of SOME bad => error ("Unknown translation target: " ^ bad ^
                                "\nAcceptable targets: " ^ String.concatWith ", " KNOWN_TARGETS)
                 | NONE => ()
      val reporter = socket_reporter (cin,cout)

   in REPL.register_plugin ("MinLang.Translator", REPL_plugin targets reporter)
    ; \<^try>\<open>
      translate_file path
      catch E => #error reporter E\<close>
    ; doPack packInt 3 cout
    ; BinIO.StreamIO.flushOut cout
  end

end