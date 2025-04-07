signature MINILANG_AUX = sig
include MINILANG_AUX

val is_tactic : (Toplevel.transition * Command_Span.span) list -> bool
val remove_tactic : (Toplevel.transition * Command_Span.span) list
                 -> (Toplevel.transition * Command_Span.span) list
val extract_proof : (Toplevel.transition * Command_Span.span) list
                 -> (Toplevel.transition * Command_Span.span) list

exception Translation_Fail of string
exception Unsupported of string


val quote_space : string -> string
val quote_fact  : string -> string

val print_mixfix : mixfix -> string list
val print_var : binding * string option * mixfix -> bstring list
val print_vars : (binding * string option * mixfix) list -> string list
val print_for : (binding * string option * mixfix) list -> string list

val print_attr : Token.T list list -> string list
val print_attrbind  : binding * Token.T list list -> string list
val print_attrbind' : binding * Token.T list list -> string list
val print_iv' : Facts.interval -> string list
val print_iv : Facts.interval list option -> string list
val print_factref : Facts.ref -> string list
val print_fact : Facts.ref * Token.T list list -> string list
val print_facts : (Facts.ref * Token.T list list) list -> string list
val print_term : string -> string list
val pretty_ty : Proof.context -> typ -> string



val tok_eq : Token.T * Token.T -> bool
val fact_eq : (Facts.ref * Token.src list) * (Facts.ref * Token.src list) -> bool
val foldl1' : ('a list * 'a list -> 'a list) -> 'a list list -> 'a list
val merge_facts : (Facts.ref * Token.src list) list list -> (Facts.ref * Token.src list) list
val merge_facts2 : ( (Facts.ref * Token.src list) list *
                     (Facts.ref * Token.src list) list
                   ) list
                -> (  Facts.ref * Token.src list) list
                   * (Facts.ref * Token.src list) list

end

structure Minilang_Aux : MINILANG_AUX = struct
open Minilang_Aux
exception Translation_Fail of string
exception Unsupported of string

val is_tactic =
  let datatype ele = FWD | BWD
      fun pop _ [] = raise Unsupported "Malformed Source"
        | pop k (k'::SK) = if k = k' then SK else raise Unsupported "Malformed Source"
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
      fun pop _ [] = raise Unsupported "Malformed Source"
        | pop k (k'::SK) = if k = k' then SK else raise Unsupported "Malformed Source"
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

val extract_proof =
  let datatype ele = FWD | BWD
      fun pop _ [] = raise Unsupported "Malformed Source"
        | pop k (k'::SK) = if k = k' then SK else raise Unsupported "Malformed Source"
      fun pass [] _ = []
        | pass stack ((tr, sp as Command_Span.Span (Command_Span.Command_Span (name, _), _)) :: L)
            = (case name
                 of "proof" => (tr, sp) :: pass (FWD :: stack) L
                  | "qed"   => (tr, sp) :: pass (stack |> pop FWD |> pop BWD) L
                  | "have"  => (tr, sp) :: pass (BWD :: stack) L
                  | "show"  => (tr, sp) :: pass (BWD :: stack) L
                  | "hence" => (tr, sp) :: pass (BWD :: stack) L
                  | "thus"  => (tr, sp) :: pass (BWD :: stack) L
                  | "consider"  => (tr, sp) :: pass (BWD :: stack) L
                  | "obtain"    => (tr, sp) :: pass (BWD :: stack) L
                  | "interpret" => (tr, sp) :: pass (BWD :: stack) L
                  | "subgoal"   => (tr, sp) :: pass (BWD :: stack) L
                  | "by"    => (tr, sp) :: pass (pop BWD stack) L
                  | "done"  => (tr, sp) :: pass (pop BWD stack) L
                  | "apply_end" => (tr, sp) :: pass (pop BWD stack) L
                  | "."     => (tr, sp) :: pass (pop BWD stack) L
                  | ".."    => (tr, sp) :: pass (pop BWD stack) L
                  |  _      => (tr, sp) :: pass stack L
              )
        | pass _ _ = raise Translation_Fail "Malformed Source"
   in pass [BWD]
  end





val quote_space = Phi_Help.quote_space
val quote_fact  = Phi_Help.quote_fact


fun print_mixfix NoSyn = []
  | print_mixfix (Mixfix (s,is,i,_)) =
      [" (", Input.string_of s, " ["] @ map string_of_int is @ ["] ", string_of_int i, ")"]
  | print_mixfix (Infix (s,i,_)) =
      [" (infix ", Input.string_of s, " ", string_of_int i, ")"]
  | print_mixfix (Infixl (s,i,_)) =
      [" (infixl ", Input.string_of s, " ", string_of_int i, ")"]
  | print_mixfix (Infixr (s,i,_)) =
      [" (infixr ", Input.string_of s, " ", string_of_int i, ")"]
  | print_mixfix (Binder (s,i,j,_)) =
      [" (binder ", Input.string_of s, " [", string_of_int i, "] ", string_of_int j, ")"]
  | print_mixfix (Structure _) = [" (structure)"]

fun print_var (v, SOME T, synt) = [Binding.name_of v, " :: ", quote_space (trim_markup T)] @ print_mixfix synt
  | print_var (v, NONE  , synt) = [Binding.name_of v] @ print_mixfix synt
fun print_vars vs = implode_with " and " (map print_var vs)
fun print_for  [] = []
  | print_for  vs = " for " :: print_vars vs

fun print_attr [] = []
  | print_attr attrs =
        ["["]
      @ implode_with ", " (map (implode_with " " o (map (single o Token.unparse))) attrs)
      @ ["]"]
fun print_attrbind (B,attrs) =
      if Binding.is_empty B
      then print_attr attrs
      else quote_space (Binding.name_of B) :: print_attr attrs
fun print_attrbind' (B,attrs) =
      if Binding.is_empty B andalso null attrs then []
      else print_attrbind (B,attrs) @ [": "]

fun print_iv' (Facts.FromTo (i,j)) = [string_of_int i, "-", string_of_int j]
  | print_iv' (Facts.From i) = [string_of_int i, "-"]
  | print_iv' (Facts.Single i) = [string_of_int i]
fun print_iv NONE = []
  | print_iv (SOME ivs) = "(" :: implode_with "," (map print_iv' ivs) @ [")"]

fun print_factref (Facts.Named ((N,_),iv)) = quote_fact N :: print_iv iv
  | print_factref (Facts.Fact expr) = ["\<open>", trim_markup expr, "\<close>"]
fun print_fact (rf,attrs) = print_factref rf @ print_attr attrs
val print_facts = implode_with " " o map print_fact

fun print_term tm = [quote_space (trim_markup tm)]
fun pretty_ty ctxt T = trim_markup (Syntax.string_of_typ ctxt T)





fun tok_eq (tok1,tok2) =
  Token.kind_of tok1 = Token.kind_of tok2 andalso Token.content_of tok1 = Token.content_of tok2
fun fact_eq ((r1,att1),(r2,att2)) =
  r1 = r2 andalso eq_list (eq_list tok_eq) (att1, att2)

fun foldl1' _ [] = []
  | foldl1' F L = foldl1 F L

val merge_facts = foldl1' (merge fact_eq)
fun merge_facts2 facts = (merge_facts (map fst facts), merge_facts (map snd facts))



end