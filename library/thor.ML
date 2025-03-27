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
                     

fun translate_thor stat commands =
  let val thy = Toplevel.theory_of stat
      fun translate _ [] = []
        | translate stat (all_commands as (tr, span) :: commands) =
            if unsuported span
            then raise Unsupported "oops or sorry"
            else if Toplevel.is_proof stat andalso
                    is_tactic all_commands
            then let val tr' = Outer_Syntax.parse_span thy (K thy) raw_sledgehammer
                  in case Toplevel.command_errors false tr' stat
                       of ([], SOME stat') =>
                               raw_sledgehammer_span :: translate stat' (remove_tactic all_commands)
                        | _ => (
                     case Toplevel.command_errors false tr stat
                       of ([], SOME stat') =>
                               span :: translate stat' commands
                        | _ => error "BUG translate_thor - Isar evaluation fails")
                 end
            else (case Toplevel.command_errors false tr stat
              of ([], SOME stat') =>
                  span :: translate stat' commands
               | X => error "BUG translate_thor - Isar evaluation fails")
      val ret = translate stat commands
   in map (String.concat o print_toks o Command_Span.content) ret
   |> String.concatWith "\n"
  end

end