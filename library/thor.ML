signature THOR = sig

val translate_thor : Toplevel.state -> (Toplevel.transition * Command_Span.span) list -> string

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

val is_tactic =
  let datatype ele = FWD | BWD
      fun pop _ [] = raise MinLang_Translator.Unsupported "Malformed Source"
        | pop k (k'::SK) = if k = k' then SK else raise MinLang_Translator.Unsupported "Malformed Source"
      fun pass [] _ = true
        | pass stack ((_, Command_Span.Span (Command_Span.Command_Span (name, _), _)) :: L)
            = (case name
                 of "proof" => false
                  | "qed"   => false
                  | "have"  => false
                  | "show"  => false
                  | "hence" => false
                  | "thus"  => false
                  | "consider"  => false
                  | "obtain"    => false
                  | "interpret" => false
                  | "subgoal"   => false
                  | "by"    => pass (pop BWD stack) L
                  | "done"  => pass (pop BWD stack) L
                  | "apply_end" => pass (pop BWD stack) L
                  | "."     => pass (pop BWD stack) L
                  | ".."    => pass (pop BWD stack) L
                  |  _      => pass stack L
              )
        | pass _ [] = false
        | pass _ X = raise Translation_Fail "Malformed Source"
   in pass [BWD]
  end

val remove_tactic =
  let datatype ele = FWD | BWD
      fun pop _ [] = raise MinLang_Translator.Unsupported "Malformed Source"
        | pop k (k'::SK) = if k = k' then SK else raise MinLang_Translator.Unsupported "Malformed Source"
      fun pass [] ret = ret
        | pass stack ((_, Command_Span.Span (Command_Span.Command_Span (name, _), _)) :: L)
            = (case name
                 of "proof" => pass (FWD :: stack) L
                  | "qed"   => pass (stack |> pop FWD |> pop BWD) L
                  | "have"  => pass (BWD :: stack) L
                  | "show"  => pass (BWD :: stack) L
                  | "hence" => pass (BWD :: stack) L
                  | "thus"  => pass (BWD :: stack) L
                  | "consider"  => pass (BWD :: stack) L
                  | "obtain"    => pass (BWD :: stack) L
                  | "interpret" => pass (BWD :: stack) L
                  | "subgoal"   => pass (BWD :: stack) L
                  | "by"    => pass (pop BWD stack) L
                  | "done"  => pass (pop BWD stack) L
                  | "apply_end" => pass (pop BWD stack) L
                  | "."     => pass (pop BWD stack) L
                  | ".."    => pass (pop BWD stack) L
                  |  _      => pass stack L
              )
        | pass _ X = raise Translation_Fail "Malformed Source"
   in pass [BWD]
  end

val raw_sledgehammer = [fst (Token.make ((0,0),"by") Position.none),
                        fst (Token.make ((2,0),"raw_sledgehammers") Position.none)]
val [raw_sledgehammer_span] = Outer_Syntax.parse_spans raw_sledgehammer

fun mkstr (Command_Span.Span (Command_Span.Command_Span (_, pos), toks)) =
      (pos, String.concat (print_toks toks))
  | mkstr _ = (Position.none, "")
fun concat_strs pstrs =
  let fun cat ((p1, s1) :: (p2, s2) :: L) =
            let val l1 = Position.line_of p1
                val l2 = Position.line_of p1
             in if is_some l1 andalso is_some l2 andalso the l1 = the l2
                then s1 :: " " :: cat ((p2, s2) :: L)
                else s1 :: "\n" :: cat ((p2, s2) :: L)
            end
        | cat L = map snd L
   in String.concat (cat pstrs)
  end

val raw_SH_str = mkstr raw_sledgehammer_span

fun translate_thor stat commands =
  let fun translate _ [] = []
        | translate stat (all_commands as (tr, span) :: commands) =
            let val aa = concat_strs (map (mkstr o snd) all_commands)
             in
            if unsuported span
            then raise Unsupported "oops or sorry"
            else if Toplevel.is_proof stat andalso
                    is_tactic all_commands
            then let val ctxt = Toplevel.context_of stat
                     val sequent = #goal (Proof.goal (Toplevel.proof_of stat))
                     val sequent_opt' = try (snd o
                                Phi_Sledgehammer_Solver.all_auto false
                                    Sledgehammer_Fact.no_fact_override NONE ctxt) sequent
                     val sh_str = raw_SH_str
                  in case sequent_opt'
                  of SOME sequent' => let
                           val meth = Method.Basic (K (Method.METHOD (K (K (Seq.single sequent')))))
                           val tr' = Isar_Cmd.terminal_proof ((meth, Position.no_range), NONE) Toplevel.empty
                        in case Toplevel.command_errors false tr' stat
                             of ([], SOME stat') =>
                                     sh_str :: translate stat' (remove_tactic all_commands)
                              | _ => (
                           case Toplevel.command_errors false tr stat
                             of ([], SOME stat') =>
                                     mkstr span :: translate stat' commands
                              | X => error "BUG translate_thor - Isar evaluation fails")
                       end
                   | NONE => (
                           case Toplevel.command_errors false tr stat
                             of ([], SOME stat') =>
                                     mkstr span :: translate stat' commands
                              | X => error "BUG translate_thor - Isar evaluation fails")
                 end
            else (case Toplevel.command_errors false tr stat
              of ([], SOME stat') =>
                  mkstr span :: translate stat' commands
               | X => error "BUG translate_thor - Isar evaluation fails")
            end
      val ret = translate stat commands
   in concat_strs ret
  end

end