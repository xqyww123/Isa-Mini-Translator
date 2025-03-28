signature THOR = sig

val translate_thor : bool -> Toplevel.state -> (Toplevel.transition * Command_Span.span) list -> string
val translate_thor_src : bool -> Toplevel.state -> string -> string

end

structure Thor : THOR = struct
open Minilang_Aux

exception Unsupported = MinLang_Translator.Unsupported
exception Translation_Fail = MinLang_Translator.Translation_Fail

fun unsuported' (Command_Span.Command_Span (name, _)) =
      member (op =) ["oops", "sorry"]
        name
  | unsuported' _ = false
fun unsuported (Command_Span.Span (k, _)) = unsuported' k

val raw_sledgehammer = [fst (Token.make ((0,0),"by") Position.none),
                        fst (Token.make ((2,0),"raw_sledgehammers") Position.none)]
val [raw_sledgehammer_span] = Outer_Syntax.parse_spans raw_sledgehammer

fun mkstr (Command_Span.Span (Command_Span.Command_Span (_, pos), toks)) =
      (SOME pos, String.concat (print_toks toks))
  | mkstr _ = (NONE, "")
fun concat_strs pstrs =
  let fun cat ((p1, s1) :: (p2, s2) :: L) =
            let val l1 = Option.mapPartial Position.line_of p1
                val l2 = Option.mapPartial Position.line_of p2
             in if is_some l1 andalso is_some l2 andalso the l1 = the l2
                then s1 :: " " :: cat ((p2, s2) :: L)
                else s1 :: "\n" :: cat ((p2, s2) :: L)
            end
        | cat L = map snd L
   in String.concat (cat pstrs)
  end

val raw_SH_str = mkstr raw_sledgehammer_span |> apfst (K NONE)

fun print_goal0 stat =
  let val ctxt = Toplevel.context_of stat
      val proof = Toplevel.proof_of stat
      val {goal, facts, ...} = Proof.goal proof
      val goals = goal
               |> Thm.prems_of
               |> map ( Syntax.string_of_term ctxt
                     #> trim_markup
                     #> quote
                     #> single )
      val facts = facts
               |> map ( Thm.string_of_thm ctxt
                     #> trim_markup
                     #> quote
                     #> single )
   in ( if null facts
        then []
        else ["(*using " :: implode_with " and " facts @ [" *)"] ] )
    @ ( if null goals
        then []
        else ["(*goals: " :: implode_with " and " goals @ [" *)"]] )
  end

fun print_goal (Command_Span.Span (Command_Span.Command_Span (name, _), _)) stat =
      if member (op =) ["apply", "prefer", "defer", "subgoal", "supply", "using", "with", "from",
                        "then", "consider", "obtain", "proof"] name
      then case implode_with "\n" (print_goal0 stat)
             of [] => []
              | L => [(NONE, String.concat L)]
      else []
  | print_goal _ _ = []

fun pretty_tm ctxt tm = single (quote_space (trim_markup (Syntax.string_of_term ctxt tm)))

fun print_case_newthings (Command_Span.Span (Command_Span.Command_Span (name, _), toks)) stat =
      if name = "case"
      then let
           val ctxt = Toplevel.context_of stat
           val proof = Toplevel.proof_of stat
           val ((_,MinLang_Translator.CASE (_, (name, vs))), _) =
                MinLang_Translator.case_parser proof (tl (filter Token.is_proper toks) @ [Token.eof])
           val kase as Rule_Cases.Case {fixes,...} =
                Proof_Context.check_case ctxt true (name, Position.none)
                                              (map (Option.map Binding.name) vs)
           val (facts, ctxt') = Proof_Context.apply_case kase ctxt
           val ret = ( if null fixes
                       then []
                       else "(*fixes variables "
                          :: implode_with' " and " (
                                map (fn (name,typ) =>
                                  [Binding.name_of name, " :: ", quote_space (pretty_ty ctxt typ)] ) fixes)
                             [" *)"] )
                   @ ( if null facts
                       then []
                       else "(*introduces facts "
                         :: implode_with' " and " (
                                map (fn (v,T) =>
                                  v :: ": " :: implode_with " " (map (pretty_tm ctxt) T)) facts)
                            [" *)"] )
        in case ret
        of [] => []
         | L => [(NONE, String.concat L)]
       end
      else []
  | print_case_newthings _ _ = []

fun translate_thor improved stat commands =
  let fun translate _ [] = []
        | translate stat (all_commands as (tr, span) :: commands) =
            let val aa = concat_strs (map (mkstr o snd) all_commands)
                fun fallback () =
                     case Toplevel.command_errors true tr stat
                       of ([], SOME stat') =>
                               mkstr span
                            :: print_goal span stat'
                             @ print_case_newthings span stat'
                             @ translate stat' commands
                        | X => error "BUG translate_thor - Isar evaluation fails"
             in (*
            if unsuported span
            then raise Unsupported "oops or sorry"
            else *) if Toplevel.is_proof stat andalso
                    is_tactic all_commands
            then let val ctxt = Toplevel.context_of stat
                     val sequent = #goal (Proof.goal (Toplevel.proof_of stat))

                     val override =
                        if improved
                        then let
                             val origin_prf = extract_proof all_commands
                                           |> map ( filter Token.is_proper
                                                  o Command_Span.content o snd)
                             val origin_ast = try MinLang_Translator.parse_isar (stat, origin_prf)
                                           |> the_default []
                             val (w,wo) = MinLang_Translator.collect_facts origin_ast
                          in { add = w, del = wo, only = false }
                         end
                        else Sledgehammer_Fact.no_fact_override
                     val sequent_opt' = try (
                                Phi_Sledgehammer_Solver.all_auto improved override NONE ctxt) sequent
                  in case sequent_opt'
                  of SOME (SH_prf, sequent') => let
                           val meth = Method.Basic (K (Method.METHOD (K (K (Seq.single sequent')))))
                           val tr' = Isar_Cmd.terminal_proof ((meth, Position.no_range), NONE) Toplevel.empty
                           val (w,wo) = MinLang_Translator.facts_in_SH_return SH_prf
                           val sh_str =
                                if improved
                                then let
                                     val add = (if null w  then [] else [" add: "])
                                             @ print_facts w
                                     val del = (if null wo then [] else [" del: "])
                                             @ print_facts (#del override)
                                     val code = String.concat (
                                                   "by (auto_sledgehammer"
                                                :: add
                                                 @ del
                                                 @ [")"])
                                  in (NONE, code)
                                 end
                                else raw_SH_str
                        in case Toplevel.command_errors false tr' stat
                             of ([], SOME stat') =>
                                     sh_str
                                  :: translate stat' (remove_tactic all_commands)
                              | _ => fallback ()
                       end
                   | NONE => fallback ()
                 end
            else fallback ()
            end
      val ret = translate stat commands
   in concat_strs ret
  end

fun parse state src =
  let val thy = Toplevel.theory_of state
      val kws = Thy_Header.get_keywords thy
      val pos = Position.make {
                  line=1, offset=1, end_offset=1, props={label="", file="#TRANSLATOR", id="0"}}
      val toks = Symbol_Pos.explode (src, pos)
              |> Token.tokenize kws {strict = false}
              |> Outer_Syntax.parse_spans
              |> filter (fn Command_Span.Span (Command_Span.Ignored_Span, _) => false
                          | _ => true)
              |> map (` (Outer_Syntax.parse_span thy (K thy) o Command_Span.content))
   in (state, toks)
  end

fun translate_thor_src improved state src =
  let val (state, cmds) = parse state src
   in translate_thor improved state cmds
  end


end