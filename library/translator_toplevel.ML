signature ML_TRANSLATOR_TOP = sig

type reporter = { report : Position.T (*position of goal statement*)
                         * Position.T (*position of the first line of the proof*)
                         * (string * string) list (*translation result*)
                         * exn list (*errors*)
                        -> unit,
                  start: Position.T -> bool,
                  declaration : Position.T * string -> unit,
                  new_thy : Position.T * Thy_Header.header -> unit }

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
                         * (string * string) list (*translation result*)
                         * exn list (*errors*)
                        -> unit,
                  start: Position.T -> bool,
                  declaration : Position.T * string -> unit,
                  new_thy : Position.T * Thy_Header.header -> unit }

fun interactive_reporter () =
  let val success = Unsynchronized.ref 0
      val total   = Unsynchronized.ref 0
   in { report = (fn (_, pos, strs, errs) => (
            if null errs
            then ( success := !success + 1 ;
                   REPL.origin_tracing ([("Translated line " ^ string_of_int (the (Position.line_of pos))),
                                 ", succeeded ", string_of_int (!success), "/", string_of_int (!total),
                                 "\n"] @ maps (fn (k,v) => [k," : ",v,"\n"]) strs) )
            else REPL.origin_warning (
                        "Fail to translate " :: string_of_int (the (Position.line_of pos)) ::
                        ", succeeded " :: string_of_int (!success) :: "/" :: string_of_int (!total)
                     :: "\n" :: [String.concatWith "\n" (
                          map (String.concat o Runtime.exn_message_list) errs)] )
        )),
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

fun REPL_plugin reporter : REPL.collector = fn cfg => fn {current_command, state, remaining} =>
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
          val target_str = getenv "ML_Translation"
          val _ = if target_str = ""
                  then error "No translation target is indicated. \
                             \Please suggest by setting environement variable 'ML_Translation'"
                  else ()
          val targets = String.tokens (fn c => c = #" ") target_str
          val _ = find_first (not o member (op =) ["origin", "isar-SH", "isar-SH*", "refined"]) targets

          val ret = Unsynchronized.ref []
          val errs= Unsynchronized.ref []
          val prf_spans = Minilang_Aux.extract_proof remaining
          val prf = map (fn (_, Command_Span.Span (_, src)) => filter Token.is_proper src) prf_spans
          val origin = String.concatWith "\n" (map (String.concat o Minilang_Aux.print_toks) prf)
          val _ = ret := ("origin", origin) :: !ret
       (* val _ = \<^try>\<open>
              let val thor = Thor.translate_thor false state prf_spans
               in ret := ("isar-SH", thor) :: !ret
              end 
              catch _ => ()\<close> *)
          val _ = \<^try>\<open>
              let val thor = Thor.translate_thor true state prf_spans
               in ret := ("isar-SH*", thor) :: !ret
              end 
              catch X => errs := X :: !errs\<close> (*
          val _ = \<^try>\<open>let
                  val asts = MinLang_Translator.translate_m (state, prf)
                  val strs = map (apsnd (MinLang_Translator.print_mast true)) asts
                  val _ = REPL.origin_warning [origin]
               in ret := strs @ !ret
              end catch E => errs := E :: !errs \<close> *)
       in #report reporter (pos, next_pos, !ret, !errs)
        ; (NONE, NONE)
      end
      else (NONE, NONE)
    else (NONE, NONE)
  end
  
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
                      additional_libs = [] (*["Minilang.Minilang_Base"]*),
                      import_dir = NONE }
                    src
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
   in { start = (fn pos =>
          let val _ = doPack (packPair (packInt, pos_packer)) (0, pos) cout 
              val _ = BinIO.StreamIO.flushOut cout
              val (ret, cin') = doUnpack unpackBool (!cin)
           in cin := cin'
           ; ret
          end),
        report = (fn (pos_spec, pos_proof, strs, errs) => (
            doPack (packTuple5 (packInt, pos_packer, pos_packer,
                                packPairList (packString, packString),
                                packList packString))
                   (2, pos_spec, pos_proof, strs,
                     map (Minilang_Aux.trim_markup o String.concat o Runtime.exn_message_list) errs) cout
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
      val (path, cin') = doUnpack unpackString (!cin)
      val _ = cin := cin'
   in REPL.register_plugin ("MinLang.Translator", REPL_plugin (socket_reporter (cin,cout)))
    ; translate_file path
    ; doPack packInt 3 cout
    ; BinIO.StreamIO.flushOut cout
  end

end