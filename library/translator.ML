signature ML_TRANSLATOR = sig
include ML_TRANSLATOR

type source = string
type typ'  = source
type term' = source
type var = binding * typ' option * mixfix
type fact = Facts.ref * Token.src list
type      statement = (term' * term' list) list list
type attr_statement = (Attrib.binding * (term' * term' list) list) list
type structured_statement = var list        (*vars*)
                          * statement       (*assumes*)
                          * attr_statement  (*shows*)
type structured_statement' = var list       (*vars*)
                           * attr_statement (*assumes*)
                           * attr_statement (*shows*)

exception Parse_Fail of Token.src list
exception Translation_Fail of string
exception Unsupported of string
exception Bad_Source of string

val print_comments : bool Unsynchronized.ref

datatype var_inst = VI_Fix of string
                  | VI_Inside_Prop of int
                  | VI_Not_Found
datatype asm_inst = AI_Fix of string * int * int
                  | AI_Inside_Prop of int * int
                  | AI_Not_Found

type fix_assms_case =
    var_inst list (*fixed variables in the order of the quantified variable of the goal*)
  * asm_inst vector (*bindings of assumptions*)
  * (binding * (string * string option list)) option (*case clause if any*)

datatype ast =
(* Isar Specific *)
    PROOF  of Method.text * (Proof.state option * ast) list
  | QED    of Method.text option * Time.time option
  | BRCBLK of (binding * (var list * (Attrib.binding * string list) list) option)
            * (Proof.state option * ast) list
  | ENDBLK
  | FIX    of var list
  | ASSUME of structured_statement
  | THUS   of structured_statement' * (Proof.state option * ast) list
  | HENCE  of structured_statement' * (Proof.state option * ast) list
  | SHOW   of structured_statement' * (Proof.state option * ast) list
  | CASE   of Attrib.binding
            * (string * string option list)
  | ISAR_OBTAIN   of (var list * structured_statement)
                   * (Proof.state option * ast) list
  | ISAR_CONSIDER of (binding * Element.obtains )
                   * (Proof.state option * ast) list
  | USING  of fact list
  | DEFER  of int
  | PREFER of int
  | WITH   of fact list
  | FROM   of fact list
  | ISAR_THEN
  | ISAR_BY   of (Method.text * Method.text option) * Time.time option
  | APPLY_END of Method.text
  | DONE
  | DDOT
  | DOT
  | ALSO       of fact list
  | FINALLY    of fact list * bool
  | MOREOVER
  | ULTIMATELY of bool
  | SUBGOAL    of ( Attrib.binding
                  * Attrib.binding option
                  * (bool * (string option * Position.T) list) )
                * (Proof.state option * ast) list

(* Shared *)
  | UNFOLD of fact list
  | TACTIC of Method.text * (fact list (*using*) * fact list (*not using*)) * Time.time option
  | DEFINE   of var list * attr_statement * var list
  | LET      of (string list * string) list
  | NOTATION of Syntax.mode * (string * mixfix) list
  | INCLUDE  of string list
  | INCLUDING of string list

(* Roughly Shared *)
  | HAVE   of structured_statement' * (Proof.state option * ast) list
  | NEXT
  | OPEN_MODULE of Expression.expression * (Proof.state option * ast) list
  | NOTE   of (Attrib.binding * fact list) list

(* Scaffolds *)
  | MPROOF   of (Proof.state option * ast) list
              * (Proof.state option * structured_statement')
              * fix_assms_case option
              * (Proof.state option * ast) list
  | BRANCH_SUBGOALS of (Proof.state option * ast) list list
  | SORRY
(*  | MCALCULATION of (binding * term' * ( fact list (*the indicated rules*)
                                       * Facts.ref list (*the this*) ) list) *)

type ast' = (Proof.state option * ast) list

(* The Min Lang *)
type mvars = Minilang.opt_var_names

datatype mast =
    MCRUSH  of mvars * ((*with*) fact list * (*without*) fact list)
  | MINTRO  of Minilang.intros_mode * mvars (*VARS*)
  | MHAMMER of (*with*) fact list * (*without*) fact list
  | MEND    of ( Minilang.endblk_type * mvars (*VARS*)
               * (*with*) fact list * (*without*) fact list)
             * string option (*proof failure reason*)
  | MCONSIDER of (var list * structured_statement) list
               * (Minilang.state option * mast) list
  | MSIMP   of (*with*) fact list * (*without*) fact list
(* Shared *)
  | MUNFOLD of fact list
  | MTACTIC of Method.text * ((*with*) fact list * (*without*) fact list) * Time.time option
  | MDEFINE   of var list * attr_statement * var list
  | MLET      of (string list * string) list
  | MNOTATION of Syntax.mode * (string * mixfix) list
(* Roughly Shared *)
  | MHAVE   of structured_statement' * (Minilang.state option * mast) list
  | MRULE   of fact list * fact list
  | MCHOOSE of (string * (binding * string option * mixfix) list (*vars*)) list (*terms*)
  | MOPEN_MODULE of Expression.expression * (Minilang.state option * mast) list
  | MCFG_FACTS of (Attrib.binding * fact list) list
  | MCFG_BUNDL of string list

  | MBRANCH_SUBGOALS of (Minilang.state option * mast) list list
  | MINDUCT of Token.src * mvars * fact list
  | MCASE   of Token.src * mvars * fact list
(*  | MSTEP   of (fact list * term')
             * (Minilang.state option * mast) list *)

  (*scaffold*)
  | MINSERT of fact list
(*  | MCALC   of (binding * term' * ( fact list (*the indicated rules*)
                                  * Facts.ref list (*the this*) ) list)
             * (Minilang.state option * mast) list *)

type mast' = (Minilang.state option * mast) list
datatype AST = Isar_AST of ast' | Mini_AST of mast' | NO_AST
type ret = (string * (AST * exn list)) list
val print_AST : AST -> string

val elaborate  : ret Unsynchronized.ref -> Toplevel.state * Token.src list -> ast'
val translate' : ret Unsynchronized.ref -> Toplevel.state -> string -> ast'

val anotate_types  : Toplevel.state * Token.src list -> ast'
val anotate_types' : Toplevel.state -> string -> ast'

type version = string (*can be `refined`, `raw` that is not refined*)
val translate_m  : string list -> ret Unsynchronized.ref -> Toplevel.state * Token.src list -> unit
val translate'm  : string list -> ret Unsynchronized.ref -> Toplevel.state -> string -> unit
val translate'test : Toplevel.state -> string -> unit

val print_ast  : bool (*use_mproof*) -> ast' -> string
val print_mast : bool (*prints response*) -> mast' -> string

val parse_isar : Toplevel.state * Token.src list -> ast'
val parse_isar_no_state : Token.src list -> ast'
val collect_facts : ast' -> (Facts.ref * Token.src list) list (*using*)
                          * (Facts.ref * Token.src list) list (*not using*)
val facts_in_SH_return : string -> (Facts.ref * Token.src list) list (*using*)
                                 * (Facts.ref * Token.src list) list (*not using*)

val case_parser : ast parser
val msorry_printing : string Unsynchronized.ref

end

structure MinLang_Translator : ML_TRANSLATOR = struct
open MinLang_Translator Minilang_Aux
type version = string (*can be `refined`, `raw` that is not refined*)

(*** Tools ***)

(* Tokens *)

fun mk_idt name = fst (Token.make ((2,0), name) Position.none)
fun mk_tok_nat i = fst (Token.make ((8,0), string_of_int i) Position.none)
fun mk_tok_kwd s = fst (Token.make ((1,0), s) Position.none)
fun mk_tok_sym s = fst (Token.make ((4,0), s) Position.none)

val tok_comma = mk_tok_kwd ","
val tok_brakL = mk_tok_kwd "["
val tok_brakR = mk_tok_kwd "]"
val tok_parL  = mk_tok_kwd "("
val tok_parR  = mk_tok_kwd ")"
val tok_minus = mk_tok_sym "-"
val tok_unfold= mk_idt "unfold"
val tok_unfolded = mk_idt "unfolded"
val tok_this  = mk_idt "this"
val method_this = Method.Source [tok_this]
val tok_assumption  = mk_idt "assumption"
fun tac_for_1 tac = Method.Combinator (Method.no_combinator_info, Method.Select_Goals 1, [tac])
val method_assumption = tac_for_1 (Method.Source [tok_assumption])
val tok_insert = mk_idt "insert"
val tok_where = mk_idt "where"
val tok_symmetric = mk_idt "symmetric"
val tok_cases = mk_idt "cases"

(* parse facts in tactic *)

local
val thms = Scan.repeat Parse.thm
val metis = Metis_Tactic.parse_metis_options |-- thms
val meson = thms
val simpN = "simp";
val iffN = "iff";
open Args
val aqbo = Scan.option add |-- Scan.option ($$$ "?")
         |-- Scan.option ($$$ "!") |-- Scan.option ($$$ "only")
val dqbo = del |-- Scan.option ($$$ "?") |-- Scan.option ($$$ "!")
val simp_modifiers0 =
               (($$$ simpN -- aqbo -- colon) >> K (rpair []))
            || (($$$ simpN -- dqbo -- colon) >> K ( pair []))
            || ((aqbo -- colon) >> K (rpair []))
            || ((dqbo -- colon) >> K ( pair []))
            || (($$$ iffN -- aqbo -- colon) >> K (rpair []))
            || (($$$ iffN -- dqbo -- colon) >> K ( pair []))
            || (($$$ "cong" -- aqbo -- colon) >> K (rpair []))
            || (($$$ "cong" -- dqbo -- colon) >> K ( pair []))
            || (($$$ "split" -- aqbo -- colon) >> K (rpair []))
            || (($$$ "split" -- dqbo -- colon) >> K ( pair []))
            || (($$$ "dest" -- aqbo -- colon) >> K (rpair []))
            || (($$$ "dest" -- dqbo -- colon) >> K ( pair []))
            || (($$$ "elim" -- aqbo -- colon) >> K (rpair []))
            || (($$$ "elim" -- dqbo -- colon) >> K ( pair []))
            || (($$$ "intro" -- aqbo -- colon) >> K (rpair []))
            || (($$$ "intro" -- dqbo -- colon) >> K ( pair []))
            || ((Scan.option ($$$ simpN) |-- $$$ "flip" -- colon) >> K (fn thms =>
                let fun ist (rf, atts) = (rf, atts @ [[tok_symmetric]])
                 in (map ist thms, thms)
                end ))
            || (Args.parens (Args.$$$ "no_asm") >> K (K ([], [])) )
            || (Args.parens (Args.$$$ "no_asm_use") >> K (K ([], [])) )
            || (Args.parens (Args.$$$ "no_asm_simp") >> K (K ([], [])) )
            || (Args.parens (Args.$$$ "asm_lr") >> K (K ([], [])) )
            

fun simp_modifiers toks =
  let fun parse ret _ (toks as [_]) = (ret, toks)
        | parse ret _ (toks as [ ]) = (ret, toks)
        | parse (L,R) prev toks0 =
        let val (assmber, toks) = (simp_modifiers0 || Scan.succeed prev) toks0
            val (thm, toks) = Scan.optional (Parse.thm >> single) [] toks
            val (L',R') = assmber thm
         in if null thm andalso length toks0 = length toks
          then error "BUG simp_modifiers"
          else parse (L' @ L, R' @ R) assmber toks
        end
   in parse ([],[]) (rpair []) toks
  end

val auto = Scan.option (Parse.nat -- Parse.nat) |-- simp_modifiers
val simp = simp_modifiers

val parse_smt_options = 
  Scan.optional
    (Args.parens (Args.name -- Scan.option (\<^keyword>\<open>,\<close> |-- Args.name)) >> apfst SOME)
    (NONE, NONE)
val smt = parse_smt_options |-- thms

val subst = Args.mode "asm" -- Scan.optional (Args.parens (Scan.repeat Parse.nat)) [0] |-- thms

val from_to =
  Parse.nat -- ($$$ "-" |-- Parse.nat) >> (fn (i, j) => fn tac => Seq.INTERVAL tac i j) ||
  Parse.nat --| $$$ "-" >> (fn i => fn tac => fn st => Seq.INTERVAL tac i (Thm.nprems_of st) st) ||
  Parse.nat >> (fn i => fn tac => tac i) ||
  $$$ "!" >> K ALLGOALS

val goal = Parse.keyword_improper "[" |-- Parse.!!! (from_to --| Parse.keyword_improper "]")

val named_insts =
  Parse.and_list1
    (Args.var -- (Args.$$$ "=" |-- Parse.!!! Parse.embedded_inner_syntax))
    -- Parse.for_fixes

fun cuttoks parser toks =
  let val (_, toks') = parser toks
   in (take (length toks - length toks') toks, toks')
  end

in

val where_parser = Parse.$$$ "where" |-- named_insts
val simp_parser = simp
val auto_parser = auto
val rule_tac_parser = Scan.option goal |-- Scan.option (cuttoks named_insts --| $$$ "in") -- thms
val rule_parser = Scan.option (Args.parens Parse.nat) |-- thms

fun tac_can_refine [] = NONE
  | tac_can_refine (tok :: toks) =
    ( case Token.content_of tok
        of "auto"   => auto  toks |> fst |> SOME
         | "metis"  => metis toks |> fst |> rpair [] |> SOME
         | "meson"  => meson toks |> fst |> rpair [] |> SOME
         | "smt"    => smt   toks |> fst |> rpair [] |> SOME
         | "simp"   => simp  toks |> fst |> SOME
         | "insert" => thms  toks |> fst |> rpair [] |> SOME
         | "fastforce" => simp  toks |> fst |> SOME
         | "force"   => simp  toks |> fst |> SOME
         | "subst"   => subst toks |> fst |> rpair [] |> SOME
         | "clarify" => SOME ([], [])
         | "linarith"=> SOME ([], [])
         | "arith"   => SOME ([], [])
         | "standard"=> SOME ([], [])
         | "contradiction" => SOME ([], [])
         | "blast"   => simp  toks |> fst |> SOME
         | "fast"    => simp  toks |> fst |> SOME
         | "slow"    => simp  toks |> fst |> SOME
         | "best"    => simp  toks |> fst |> SOME
         | "deepen"  => (Scan.option Parse.nat |-- simp)  toks |> fst |> SOME
         | "safe"    => simp  toks |> fst |> SOME
         | "safe_step" => simp  toks |> fst |> SOME
         | "inst_step" => simp  toks |> fst |> SOME
         | "step"    => simp  toks |> fst |> SOME
         | "slow_step" => simp  toks |> fst |> SOME
         | "clarify_step" => simp  toks |> fst |> SOME
         | "intro"   => simp  toks |> fst |> SOME
         | "elim"    => simp  toks |> fst |> SOME
         | "dest"    => simp  toks |> fst |> SOME
         | "fact"    => thms  toks |> fst |> rpair [] |> SOME
         | "unfold"  => thms  toks |> fst |> rpair [] |> SOME
         | "slowsimp" => simp  toks |> fst |> SOME
         | "bestsimp" => simp  toks |> fst |> SOME
         | "clarsimp" => simp  toks |> fst |> SOME
         | "rule"     => thms  toks |> fst |> rpair [] |> SOME
         | "erule"    => rule_parser toks |> fst |> rpair [] |> SOME
         | "drule"    => rule_parser toks |> fst |> rpair [] |> SOME
         | "frule"    => rule_parser toks |> fst |> rpair [] |> SOME
         | "rule_tac"  => rule_tac_parser toks |> fst |> snd |> rpair [] |> SOME
         | "erule_tac" => rule_tac_parser toks |> fst |> snd |> rpair [] |> SOME
         | "drule_tac" => rule_tac_parser toks |> fst |> snd |> rpair [] |> SOME
         | "frule_tac" => rule_tac_parser toks |> fst |> snd |> rpair [] |> SOME
         | "cut_tac"   => rule_tac_parser toks |> fst |> snd |> rpair [] |> SOME
         | "assumption" => SOME ([], [])
         | "this"     => SOME ([], [])
         | _ => NONE )

fun facts_in_tac toks =
      case tac_can_refine toks
        of SOME ret => ret
         | NONE => ([],[])
      
(*
and facts_in_facts facts
      = merge_facts (facts :: map (merge_facts o map facts_in_attr' o snd) facts)
and facts_in_attr [] = []
  | facts_in_attr (tok :: toks) =
    ( case Token.content_of tok
        of "OF"       => thms toks |> fst |> facts_in_facts
         | "THEN"     => thms toks |> fst |> facts_in_facts
         | "unfolded" => thms toks |> fst |> facts_in_facts
         | "folded"   => thms toks |> fst |> facts_in_facts
         | "simplified" => thms toks |> fst |> facts_in_facts
         | _ => [] )
and facts_in_attr' tok = facts_in_attr (tok @ [Token.eof])
*)

fun facts_in_method (Method.Source toks) = facts_in_tac (toks @ [Token.eof])
  | facts_in_method (Method.Combinator (_, _, tacs)) = merge_facts2 (map facts_in_method tacs)
  | facts_in_method _ = ([], [])

end

val keywords = Keyword.no_major_keywords (Thy_Header.get_keywords \<^theory>)
fun facts_in_SH_return src =
  if src = "" then ([], [])
  else if src = "()" then ([], [])
  else let
      val ((m, _), _) =
          Input.string src
             |> Input.source_explode
             |> Token.tokenize keywords {strict = true}
             |> filter Token.is_proper
             |> (fn toks => toks @ [Token.eof])
             |> Method.parse
   in facts_in_method m
  end

(* Minilang reporter *)

val new_items_data = Thread_Data.var () : (Minilang.items * term list option (*goals*)) Unsynchronized.ref Thread_Data.var
fun new_items () =
      case Thread_Data.get new_items_data
        of SOME nid => nid
         | NONE => let
               val nid = Unsynchronized.ref (Minilang.empty_items, NONE)
            in Thread_Data.put new_items_data (SOME nid)
             ; nid
           end

val current_case_data = Thread_Data.var () : string Unsynchronized.ref Thread_Data.var
fun current_case () =
      case Thread_Data.get current_case_data
        of SOME nid => nid
         | NONE => let
               val store = Unsynchronized.ref ""
            in Thread_Data.put current_case_data (SOME store)
             ; store
           end

val internal_data = Thread_Data.var () : exn Thread_Data.var

val SH_prfs_data = Thread_Data.var () : string list Unsynchronized.ref Thread_Data.var
fun SH_prfs () =
      case Thread_Data.get SH_prfs_data
        of SOME nid => nid
         | NONE => let
               val store = Unsynchronized.ref []
            in Thread_Data.put SH_prfs_data (SOME store)
             ; store
           end

fun item_reporter (Minilang.New_Items items') =
      let val store = new_items ()
          val (items, goals) = !store
       in store := (Minilang.cat_items items' items, goals)
      end
  | item_reporter (Minilang.Goals goals') =
      let val store = new_items ()
          val (items, goals) = !store
       in store := (items, goals')
      end
  | item_reporter (Minilang.Consider_Case name) =
      let val store = current_case ()
       in store := name
      end
  | item_reporter (Minilang.Internal (Minilang.SH_PRF prf)) =
      let val store = SH_prfs ()
       in store := prf :: !store
      end
  | item_reporter (Minilang.Internal exn) =
      Thread_Data.put internal_data (SOME exn)

fun fetch_items () =
  let val store = new_items ()
      val ret = !store
   in store := (Minilang.empty_items, NONE)
    ; ret
  end

(*** AST ***)

type source = string
type typ'  = source
type term' = source
type var = binding * typ' option * mixfix
type mvars = Minilang.opt_var_names
type fact = Facts.ref * Token.src list
type fact'= fact
type statement  = (term' * term' list) list list
type attr_statement = (Attrib.binding * (term' * term' list) list) list
type structured_statement = var list      (*vars*)
                          * statement      (*assumes*)
                          * attr_statement (*shows*)
type structured_statement' = var list       (*vars*)
                           * attr_statement (*assumes*)
                           * attr_statement (*shows*)

exception Parse_Fail of Token.src list
exception Bad_Source of string

datatype var_inst = VI_Fix of string
                  | VI_Inside_Prop of int
                  | VI_Not_Found
datatype asm_inst = AI_Fix of string * int * int
                  | AI_Inside_Prop of int * int
                  | AI_Not_Found

type fix_assms_case =
    var_inst list (*fixed variables in the order of the quantified variable of the goal*)
  * asm_inst vector (*bindings of assumptions*)
  * (binding * (string * string option list)) option (*case clause if any*)


datatype ast =
(* Isar Specific *)
    PROOF  of Method.text * (Proof.state option * ast) list
  | QED    of Method.text option * Time.time option
  | BRCBLK of (binding * (var list * (Attrib.binding * string list) list) option)
            * (Proof.state option * ast) list
  | ENDBLK
  | FIX    of var list
  | ASSUME of structured_statement
  | THUS   of structured_statement' * (Proof.state option * ast) list
  | HENCE  of structured_statement' * (Proof.state option * ast) list
  | SHOW   of structured_statement' * (Proof.state option * ast) list
  | CASE   of Attrib.binding
            * (string * string option list)
  | ISAR_OBTAIN   of (var list * structured_statement)
                   * (Proof.state option * ast) list
  | ISAR_CONSIDER of (binding * Element.obtains)
                   * (Proof.state option * ast) list
  | USING  of fact' list                                   
  | DEFER  of int
  | PREFER of int
  | WITH   of fact' list
  | FROM   of fact' list
  | ISAR_THEN
  | ISAR_BY   of (Method.text * Method.text option) * Time.time option
  | APPLY_END of Method.text
  | DONE
  | DDOT
  | DOT
  | ALSO       of fact list
  | FINALLY    of fact list * bool
  | MOREOVER
  | ULTIMATELY of bool
  | SUBGOAL    of ( Attrib.binding
                  * Attrib.binding option
                  * (bool * (string option * Position.T) list) )
                * (Proof.state option * ast) list

(* Shared *)
  | UNFOLD of fact' list
  | TACTIC of Method.text * (fact list (*using*) * fact list (*not using*)) * Time.time option
  | DEFINE   of var list * attr_statement * var list
  | LET      of (string list * string) list
  | NOTATION of Syntax.mode * (string * mixfix) list
  | INCLUDE  of string list
  | INCLUDING of string list

(* Roughly Shared *)
  | HAVE   of structured_statement' * (Proof.state option * ast) list
  | NEXT
  | OPEN_MODULE of Expression.expression * (Proof.state option * ast) list
  | NOTE   of (Attrib.binding * fact' list) list

(* Scaffolds *)
  | MPROOF   of (Proof.state option * ast) list
              * (Proof.state option * structured_statement')
              * fix_assms_case option
              * (Proof.state option * ast) list
  | BRANCH_SUBGOALS of (Proof.state option * ast) list list
  | SORRY
(*  | MCALCULATION of (binding * term' * ( fact list (*the indicated rules*)
                                       * Facts.ref list (*the this*) ) list) *)


type ast' = (Proof.state option * ast) list

fun fact'_eq ctxt ((rf1,toks1), (rf2,toks2)) =
      ((rf1 = rf2) orelse let
           val thms1 = Attrib.eval_thms ctxt [(rf1,toks1)]
           val thms2 = Attrib.eval_thms ctxt [(rf2,toks2)]
        in eq_set Thm.eq_thm_prop (thms1, thms2) andalso
           eq_list (eq_list ((op =) o apply2 Token.content_of)) (toks1, toks2)
      end)

(* The Min Lang *)
datatype mast =
    MCRUSH  of mvars * ((*with*) fact' list * (*without*) fact' list)
  | MINTRO  of Minilang.intros_mode * mvars (*VARS*)
  | MHAMMER of (*with*) fact' list * (*without*) fact' list
  | MEND    of ( Minilang.endblk_type * mvars (*VARS*)
               * (*with*) fact list * (*without*) fact list)
             * string option (*proof failure reason*)
  | MCONSIDER of (var list * structured_statement) list
               * (Minilang.state option * mast) list
  | MSIMP   of (*with*) fact list * (*without*) fact list
(* Shared *)
  | MUNFOLD of fact' list
  | MTACTIC of Method.text * ((*with*) fact' list * (*without*) fact' list) * Time.time option
  | MDEFINE   of var list * attr_statement * var list
  | MLET      of (string list * string) list
  | MNOTATION of Syntax.mode * (string * mixfix) list
(* Roughly Shared *)
  | MHAVE   of structured_statement' * (Minilang.state option * mast) list
  | MRULE   of fact' list * fact' list
  | MCHOOSE of (string (*term*) * (binding * string option * mixfix) list (*vars*)) list
  | MOPEN_MODULE of Expression.expression * (Minilang.state option * mast) list
  | MCFG_FACTS of (Attrib.binding * fact' list) list
  | MCFG_BUNDL of string list

  | MBRANCH_SUBGOALS of (Minilang.state option * mast) list list
  | MINDUCT of Token.src * mvars * fact list
  | MCASE   of Token.src * mvars * fact list
(*  | MSTEP   of (fact list * term')
             * (Minilang.state option * mast) list *)

(*scaffold*)
  | MINSERT of fact list
(*  | MCALC   of (binding * term' * ( fact list (*the indicated rules*)
                                  * Facts.ref list (*the this*) ) list)
             * (Minilang.state option * mast) list *)

type mast' = (Minilang.state option * mast) list



(** Helpers **)

(* val method_sorry  = tac_for_1 (Method.Source [mk_idt "msorry"]) *)

(*fun all2 _ [] [] = true
  | all2 f (x :: xs) (y :: ys) = f x y andalso all2 f xs ys
  | all2 _ _ _ = false *)

(** Pre-Print **)



fun tokenize_iv' (Facts.FromTo (i,j)) = [mk_tok_nat i, tok_minus, mk_tok_nat j]
  | tokenize_iv' (Facts.From i) = [mk_tok_nat i, tok_minus]
  | tokenize_iv' (Facts.Single i) = [mk_tok_nat i]
fun tokenize_iv NONE = []
  | tokenize_iv (SOME ivs) =
      mk_tok_kwd "(" :: implode_with (tok_comma) (map tokenize_iv' ivs) @ [mk_tok_kwd ")"]

fun tokenize_factref (Facts.Named (N_pos, iv)) = Token.make_string N_pos :: tokenize_iv iv
  | tokenize_factref (Facts.Fact expr) =
      Token.tokenize keywords {strict = false}
          (Symbol_Pos.explode ("\<open>" ^ trim_markup expr ^ "\<close>", Position.none))
fun tokenize_fact  (rf, []) = tokenize_factref rf
  | tokenize_fact  (rf, atts) =
      tokenize_factref rf @ tok_brakL :: implode_with (tok_comma) atts @ [tok_brakR]
fun method_insert  thms = (Method.Source (tok_insert :: maps tokenize_fact thms))
fun method_insert1 thms = tac_for_1 (Method.Source (tok_insert :: maps tokenize_fact thms))

(** Pass Helpers **)

fun linear_pass' scope F =
  let fun set_scope ast H =
        case scope of NONE => H ()
                    | SOME scp => let
                          val _ = scp := ast :: !scp
                          val ret = H ()
                          val _ = scp := tl (!scp)
                       in ret
                      end
      fun add_his _ [] = error "BUG add_his"
        | add_his x (H::R) = (x::H)::R
      fun pass his ast =
        case F his ast
          of (x as (s, a as PROOF (tacs, ast')))::L =>
                set_scope a (fn _ => (s, PROOF (tacs, pass ([]::his) ast')))
             :: pass (add_his x his) L
           | (x as (s, a as BRCBLK (data, ast))) :: L =>
                set_scope a (fn _ => (s, BRCBLK (data, pass ([]::his) ast)))
             :: pass (add_his x his) L
           | (x as (s, a as THUS (st, ast'))) :: L =>
                set_scope a (fn _ => (s, THUS (st, pass ([]::his) ast')))
             :: pass (add_his x his) L
           | (x as (s, a as HENCE (st, ast'))) :: L =>
                set_scope a (fn _ => (s, HENCE (st, pass ([]::his) ast')))
             :: pass (add_his x his) L
           | (x as (s, a as SHOW (st, ast'))) :: L =>
                set_scope a (fn _ => (s, SHOW (st, pass ([]::his) ast')))
             :: pass (add_his x his) L
           | (x as (s, a as ISAR_OBTAIN (st, ast'))) :: L =>
             (s, ISAR_OBTAIN (st, pass ([]::his) ast')) :: pass (add_his x his) L
           | (x as (s, a as ISAR_CONSIDER (st, ast'))) :: L =>
                set_scope a (fn _ => (s, ISAR_CONSIDER (st, pass ([]::his) ast')))
             :: pass (add_his x his) L
           | (x as (s, a as HAVE (st, ast'))) :: L =>
                set_scope a (fn _ => (s, HAVE (st, pass ([]::his) ast')))
             :: pass (add_his x his) L
           | (x as (s, a as OPEN_MODULE (st, ast'))) :: L =>
                set_scope a (fn _ => (s, OPEN_MODULE (st, pass ([]::his) ast')))
             :: pass (add_his x his) L
           | (x as (s, a as MPROOF (pre, ss, data, prf))) :: L =>
                 set_scope a (fn _ => (s, MPROOF (pass ([]::his) pre, ss, data, pass ([]::his) prf)))
              :: pass (add_his x his) L
           | (x as (s, a as BRANCH_SUBGOALS nexts)) :: L =>
                 set_scope a (fn _ => (s, BRANCH_SUBGOALS (map (pass his) nexts)))
              :: pass (add_his x his) L
           | (x as (s, a as SUBGOAL (st, ast'))) :: L =>
                set_scope a (fn _ => (s, SUBGOAL (st, pass ([]::his) ast')))
             :: pass (add_his x his) L
           | element :: L => element :: pass (add_his element his) L
           | [] => []
   in pass [[]]
  end

(*top-down*)
fun segment_pass F =
  let fun pass ast =
        case ast
          of (s, PROOF (tacs, ast'))::L =>
             (s, PROOF (tacs, pass (F ast'))) :: pass L
           | (s, BRCBLK (data, ast)) :: L =>
             (s, BRCBLK (data, pass (F ast))) :: pass L
           | (s, THUS (st, ast'))::L =>
             (s, THUS (st, pass (F ast'))) :: pass L
           | (s, HENCE (st, ast'))::L =>
             (s, HENCE (st, pass (F ast'))) :: pass L
           | (s, SHOW (st, ast'))::L =>
             (s, SHOW (st, pass (F ast'))) :: pass L
           | (s, ISAR_OBTAIN (st, ast'))::L =>
             (s, ISAR_OBTAIN (st, pass (F ast'))) :: pass L
           | (s, ISAR_CONSIDER (st, ast'))::L =>
             (s, ISAR_CONSIDER (st, pass (F ast'))) :: pass L
           | (s, HAVE (st, ast'))::L =>
             (s, HAVE (st, pass (F ast'))) :: pass L
           | (s, OPEN_MODULE (st, ast'))::L =>
             (s, OPEN_MODULE (st, pass (F ast'))) :: pass L
           | (s, MPROOF (pre, ss, data, prf)) :: L =>
             (s, MPROOF (pass (F pre), ss, data, pass (F prf))) :: pass L
           | (s, BRANCH_SUBGOALS nexts) :: L =>
             (s, BRANCH_SUBGOALS (map (pass o F) nexts)) :: pass L
           | (s, SUBGOAL (st, ast'))::L =>
             (s, SUBGOAL (st, pass (F ast'))) :: pass L
           | element :: L => element :: pass L
           | [] => []
  in pass o F
 end


fun linear_pass scope F =
  let fun set_scope ast H =
        case scope of NONE => H ()
                    | SOME scp => let
                          val _ = scp := ast :: !scp
                          val ret = H ()
                          val _ = scp := tl (!scp)
                       in ret
                      end
      fun pass ast =
        case F ast
          of (s, x as PROOF (tacs, ast'))::L =>
             set_scope x (fn () => (s, PROOF (tacs, pass ast'))) :: pass L
           | (s, x as BRCBLK (data, ast)) :: L =>
             set_scope x (fn () => (s, BRCBLK (data, pass ast))) :: pass L
           | (s, x as THUS (st, ast'))::L =>
             set_scope x (fn () => (s, THUS (st, pass ast'))) :: pass L
           | (s, x as HENCE (st, ast'))::L =>
             set_scope x (fn () => (s, HENCE (st, pass ast'))) :: pass L
           | (s, x as SHOW (st, ast'))::L =>
             set_scope x (fn () => (s, SHOW (st, pass ast'))) :: pass L
           | (s, x as ISAR_OBTAIN (st, ast'))::L =>
             set_scope x (fn () => (s, ISAR_OBTAIN (st, pass ast'))) :: pass L
           | (s, x as ISAR_CONSIDER (st, ast'))::L =>
             set_scope x (fn () => (s, ISAR_CONSIDER (st, pass ast'))) :: pass L
           | (s, x as HAVE (st, ast'))::L =>
             set_scope x (fn () => (s, HAVE (st, pass ast'))) :: pass L
           | (s, x as OPEN_MODULE (st, ast'))::L =>
             set_scope x (fn () => (s, OPEN_MODULE (st, pass ast'))) :: pass L
           | (s, x as MPROOF (pre, ss, data, prf)) :: L =>
             set_scope x (fn () => (s, MPROOF (pass pre, ss, data, pass prf))) :: pass L
           | (s, x as BRANCH_SUBGOALS nexts) :: L =>
             set_scope x (fn () => (s, BRANCH_SUBGOALS (map pass nexts))) :: pass L
           | (s, x as SUBGOAL (st, ast'))::L =>
             set_scope x (fn () => (s, SUBGOAL (st, pass ast'))) :: pass L
           | element :: L => element :: pass L
           | [] => []
   in pass
  end

fun linear_fold F ast x =
  let val ret = Unsynchronized.ref x
   in linear_pass NONE (
        fn [] => []
         | origin as (a :: _) => (
             ret := F a (!ret)
           ; origin )
      ) ast
    ; !ret
  end

fun linear_passm scope F =
  let fun set_scope ast H =
        case scope of NONE => H ()
                    | SOME scp => let
                          val _ = scp := ast :: !scp
                          val ret = H ()
                          val _ = scp := tl (!scp)
                       in ret
                      end
      fun pass ast =
        case F ast
          of (s, x as MCONSIDER (args, ast'))::L =>
             set_scope x (fn () => (s, MCONSIDER (args, pass ast'))) :: pass L
           | (s, x as MHAVE (args, ast'))::L =>
             set_scope x (fn () => (s, MHAVE (args, pass ast'))) :: pass L
(*           | (s, x as MSTEP (args, ast'))::L =>
             set_scope x (fn () => (s, MSTEP (args, pass ast'))) :: pass L *)
           | (s, x as MOPEN_MODULE (args, ast'))::L =>
             set_scope x (fn () => (s, MOPEN_MODULE (args, pass ast'))) :: pass L
           | (s, x as MBRANCH_SUBGOALS ast')::L =>
             set_scope x (fn () => (s, MBRANCH_SUBGOALS (map pass ast'))) :: pass L
           | element :: L => element :: pass L
           | [] => []
   in pass
  end

fun linear_foldm F ast x =
  let val ret = Unsynchronized.ref x
   in linear_passm NONE (
        fn [] => []
         | origin as (a :: _) => (
             ret := F a (!ret)
           ; origin )
      ) ast
    ; !ret
  end

(*top-down*)
fun segment_passm scope F =
  let fun set_scope ast H =
        case scope of NONE => H ()
                    | SOME scp => let
                          val _ = scp := ast :: !scp
                          val ret = H ()
                          val _ = scp := tl (!scp)
                       in ret
                      end
      fun pass ast =
        case ast
          of (s, x as MCONSIDER (args, ast'))::L =>
             set_scope x (fn () => (s, MCONSIDER (args, pass (F ast')))) :: pass L
           | (s, x as MHAVE (args, ast'))::L =>
             set_scope x (fn () => (s, MHAVE (args, pass (F ast')))) :: pass L
(*           | (s, x as MSTEP (args, ast'))::L =>
             set_scope x (fn () => (s, MSTEP (args, pass ast'))) :: pass L *)
           | (s, x as MOPEN_MODULE (args, ast'))::L =>
             set_scope x (fn () => (s, MOPEN_MODULE (args, pass (F ast')))) :: pass L
           | (s, x as MBRANCH_SUBGOALS ast')::L =>
             set_scope x (fn () => (s, MBRANCH_SUBGOALS (map (pass o F) ast'))) :: pass L
           | element :: L => element :: pass L
           | [] => []
   in pass o F
  end

fun prf_segment_passm scope F =
  let fun prf_seg ((x as (_, MCRUSH _)) :: L) = x :: prf_seg L
        | prf_seg ((x as (_, MSIMP  _)) :: L) = x :: prf_seg L
        | prf_seg ((x as (_, MINTRO _)) :: L) = x :: prf_seg L
        | prf_seg (origin as (_, MHAMMER _) :: _) = origin
        | prf_seg (origin as (_, MEND _) :: _) = origin
        | prf_seg (origin as (_, MBRANCH_SUBGOALS _) :: _) = origin
        | prf_seg ((x as (_, MCONSIDER _)) :: L) = x :: prf_seg L
        | prf_seg ((x as (_, MDEFINE _)) :: L) = x :: prf_seg L
        | prf_seg ((x as (_, MLET _)) :: L) = x :: prf_seg L
        | prf_seg ((x as (_, MNOTATION _)) :: L) = x :: prf_seg L
        | prf_seg ((x as (_, MHAVE _)) :: L) = x :: prf_seg L
        | prf_seg ((x as (_, MOPEN_MODULE _)) :: L) = x :: prf_seg L
        | prf_seg ((x as (_, MCFG_FACTS _)) :: L) = x :: prf_seg L
        | prf_seg ((x as (_, MCFG_BUNDL _)) :: L) = x :: prf_seg L
        | prf_seg ((x as (_, MINDUCT _)) :: L) = x :: prf_seg L
        | prf_seg ((x as (_, MCASE _)) :: L) = x :: prf_seg L
        | prf_seg L = F L
   in segment_passm scope prf_seg
  end

fun elementwise_pass scope F = linear_pass scope (
      fn [] => []
       | (x :: L) => F x :: L
    )

fun elementwise_pass' scope F = linear_pass' scope (fn history =>
      fn [] => []
       | (x :: L) => F history x :: L
    )

fun recursive F x = recursive F (F x) handle Match => x | Bind => x

  (*particularly for backward proofs*)
fun bottom_up_prfs F ast' = 
  let fun pass _ [] = []
        | pass F ((s, PROOF (tac, blk)) :: L)
            = (s, PROOF (tac, pass F blk)) :: pass F L
        | pass F ((s, BRCBLK (data, blk)) :: L)
            = (s, BRCBLK (data, pass F blk)) :: pass F L
        | pass F ((s, THUS  (ss, blk)) :: L)
            = (s, THUS  (ss, F (pass F blk))) :: pass F L
        | pass F ((s, HENCE (ss, blk)) :: L)
            = (s, HENCE (ss, F (pass F blk))) :: pass F L
        | pass F ((s, SHOW  (ss, blk)) :: L)
            = (s, SHOW  (ss, F (pass F blk))) :: pass F L
        | pass F ((s, HAVE  (ss, blk)) :: L)
            = (s, HAVE  (ss, F (pass F blk))) :: pass F L
        | pass F ((s, SUBGOAL (ss, blk)) :: L)
            = (s, SUBGOAL (ss, F (pass F blk))) :: pass F L
        | pass F ((s, ISAR_OBTAIN (ss, blk)) :: L)
            = (s, ISAR_OBTAIN (ss, F (pass F blk))) :: pass F L
        | pass F ((s, ISAR_CONSIDER (ss, blk)) :: L)
            = (s, ISAR_CONSIDER (ss, F (pass F blk))) :: pass F L
        | pass F ((s, OPEN_MODULE (ss, blk)) :: L)
            = (s, OPEN_MODULE (ss, F (pass F blk))) :: pass F L
        | pass F ((s, MPROOF (pre, ss, data, prf)) :: L)
            = (s, MPROOF (pass F pre, ss, data, F (pass F prf))) :: pass F L
        | pass F ((s, BRANCH_SUBGOALS bodies) :: L)
            = (s, BRANCH_SUBGOALS (map (pass F) bodies)) :: pass F L
        | pass F (x :: L) = x :: pass F L
   in pass F ast'
   |> F
  end


fun exists_ast P (ast as PROOF (_, body))
      = P ast orelse exists (exists_ast P o snd) body
  | exists_ast P (ast as BRCBLK (_, body))
      = P ast orelse exists (exists_ast P o snd) body
  | exists_ast P (ast as THUS (_, body))
      = P ast orelse exists (exists_ast P o snd) body
  | exists_ast P (ast as HENCE (_, body))
      = P ast orelse exists (exists_ast P o snd) body
  | exists_ast P (ast as SHOW (_, body))
      = P ast orelse exists (exists_ast P o snd) body
  | exists_ast P (ast as HAVE (_, body))
      = P ast orelse exists (exists_ast P o snd) body
  | exists_ast P (ast as SUBGOAL (_, body))
      = P ast orelse exists (exists_ast P o snd) body
  | exists_ast P (ast as ISAR_OBTAIN (_, body))
      = P ast orelse exists (exists_ast P o snd) body
  | exists_ast P (ast as ISAR_CONSIDER (_, body))
      = P ast orelse exists (exists_ast P o snd) body
  | exists_ast P (ast as OPEN_MODULE (_, body))
      = P ast orelse exists (exists_ast P o snd) body
  | exists_ast P (ast as MPROOF (pre,_,_,prf))
      = P ast orelse exists (exists_ast P o snd) pre
              orelse exists (exists_ast P o snd) prf
  | exists_ast P (ast as BRANCH_SUBGOALS bodies)
      = P ast orelse exists (exists (exists_ast P o snd)) bodies
  | exists_ast P ast = P ast

fun exists_mast P (ast as MCONSIDER (_, body))
      = P ast orelse exists (exists_mast P o snd) body
  | exists_mast P (ast as MHAVE (_, body))
      = P ast orelse exists (exists_mast P o snd) body
  | exists_mast P (ast as MOPEN_MODULE (_, body))
      = P ast orelse exists (exists_mast P o snd) body
(*  | exists_mast P (ast as MSTEP (_, body))
      = P ast orelse exists (exists_mast P o snd) body *)
  | exists_mast P (ast as MBRANCH_SUBGOALS bodies)
      = P ast orelse exists (exists (exists_mast P o snd)) bodies
  | exists_mast P ast = P ast

val mast_cheat = exists_mast (fn MEND (_, SOME _) => true
                                   | _ => false)
val mast_cheat' = exists (mast_cheat o snd)

(* map facts *)

fun unquote s =
  if String.isPrefix "\"" s andalso String.isSuffix "\"" s
  then String.substring (s, 1, size s - 2)
  else if String.isPrefix "\<open>" s andalso String.isSuffix "\<close>" s
  then String.substring (s, 7, size s - 15)
  else s

(*
local open Token
in fun token_kind_of Command = 0
     | token_kind_of Keyword = 1
     | token_kind_of Ident   = 2
     | token_kind_of Long_Ident = 3
     | token_kind_of Sym_Ident  = 4
     | token_kind_of Var = 5
     | token_kind_of Type_Ident = 6
     | token_kind_of Type_Var = 7
     | token_kind_of Nat = 8
     | token_kind_of Float = 9
     | token_kind_of Space = 10
     | token_kind_of _ = ~1
end

fun map_token_content f tok =
  case f (Token.content_of tok)
    of SOME s => let val k = token_kind_of (Token.kind_of tok)
                  in if k = ~1
                   then tok
                   else fst (Token.make ((k,0), s) (Token.pos_of tok))
                 end
     | NONE => tok
*)

fun exists_token_content P tok = P (Token.content_of tok)

fun compact_factsegs ((ent1 as (name1,i1,n1,N)) :: (LL as (name2,i2,n2,_) :: L)) =
      if name1 = name2 andalso i1+n1 = i2
      then compact_factsegs ((name1,i1,n1+n2,N) :: L)
      else ent1 :: compact_factsegs LL
  | compact_factsegs L = L

fun prepend x L = x :: L

(*F : name -> intervals as [(name', initial index k, length n, capacity N of name'), ...]
  where k starts from 0*)
fun select_facts _ given NONE = compact_factsegs given
  | select_facts len given (SOME ivs) =
      let fun sel _ _ [] = []
            | sel ofst (iv as Facts.FromTo (i,j)) ((name,k,n,N)::L) =
                if ofst <= j andalso i < ofst+n
                then let val n' = Int.min (n, j - Int.max(i,ofst) + 1)
                      in (name, k + i - ofst, n', N )
                      :: sel (ofst + n) (Facts.FromTo (i+n',j)) L
                     end
                else sel (ofst + n) iv L
            | sel ofst (Facts.From i) L =
                sel ofst (Facts.FromTo (i, Lazy.force len - 1)) L
            | sel ofst (Facts.Single i) L =
                sel ofst (Facts.FromTo (i, i)) L
       in ivs
       |> sort (int_ord o apply2 (fn Facts.FromTo (i,_) => i
                                   | Facts.From i => i
                                   | Facts.Single i => i))
       |> maps (fn iv => sel 1 iv given)
       |> compact_factsegs
      end

fun $$$$ _ [] = Scan.fail []
  | $$$$ name (tok :: toks) =
      if Token.kind_of tok = Token.Keyword andalso Token.content_of tok = name
      then toks
      else Scan.fail []

val permissive_thm_sel = let open Parse
  in Scan.permissive (
    $$$ "(" |-- list1
 (nat --| minus -- nat >> Facts.FromTo ||
  nat --| minus >> Facts.From ||
  nat >> Facts.Single) --| (pair () o $$$$ ")") )
 end

fun match_toks [] _ = true
  | match_toks _ [] = false
  | match_toks ((kinds, content) :: pats) (tok::toks) =
      member (op =) kinds (Token.kind_of tok) andalso
      (case content of SOME c => c = Token.content_of tok
                     | NONE   => true)
      andalso match_toks pats toks

fun subst_fact_in_toks'gen F =
  let val match = match_toks
      open Token

      fun subs_toks [] = []
        | subs_toks toks =
            if match [([Keyword], SOME "where"),
                      ([String, Alt_String, Cartouche, Ident, Sym_Ident, Long_Ident], NONE),
                      ([Keyword], SOME "="),
                      ([String, Alt_String, Cartouche, Ident, Sym_Ident, Long_Ident], NONE)]
                     toks
            then take 3 toks @ subs_toks (drop 3 toks)
            else if match [([Keyword], SOME "of")]
                          toks
            then let val i = find_index (fn tok => kind_of tok = Keyword andalso
                                                   content_of tok = "," ) toks
              in if i = ~1
                then toks
                else take i toks @ subs_toks (drop i toks)
             end
            else case toks
              of [] => []
               | toks as tok :: R =>
              if (case Token.kind_of tok
                    of Ident => true
                     | Sym_Ident => true
                     | String => true
                     | Alt_String => true
                     | Long_Ident => true
                     | _ => false
                  )
              then F toks subs_toks
              else tok :: subs_toks R
   in fn toks =>
   let val ret = subs_toks toks
    in if eq_list pointer_eq (ret, toks)
     then toks
     else ret
   end
  end

fun subst_fact_in_toks ctxt F = 
  let fun tokenize_seg (name, i, n, N) =
        if n = N andalso i = 0
        then [mk_idt name]
        else if n = 1
        then [mk_idt name, tok_parL, mk_tok_nat i, tok_parR]
        else if i + n - 1 = N
        then [mk_idt name, tok_parL, mk_tok_nat i, tok_minus, tok_parR]
        else [mk_idt name, tok_parL, mk_tok_nat i, tok_minus, mk_tok_nat (i+n-1), tok_parR]

      open Token

      fun read_attr' ~1 toks = ([], toks)
        | read_attr' lev toks =
            (( $$$$ "[" #> read_attr' (lev + 1)
            || $$$$ "]" #> read_attr' (lev - 1)
            || tl #> read_attr' lev)
            >> prepend (hd toks) ) toks

      fun read_attr [] = Scan.fail []
        | read_attr toks =
            ( $$$$ "[" #> read_attr' 0 >> prepend (hd toks) ) toks

      val read_fact = let open Parse Scan in
                        Scan.option (
                          read_attr >> pair ("", NONE) ||
                          (( Scan.permissive name -- Scan.option permissive_thm_sel )
                          -- (read_attr || pair []) ) )
                      end
      fun subst [] _ = error "BUG subst_fact_in_toks.subst"
        | subst (toks as tok :: R) subs_toks =
            case read_fact toks
              of (NONE, _) => tok :: subs_toks R
               | (SOME ((name, ivs), attrs), remaining) => (
             case F ctxt (unquote name)
               of NONE => tok :: subs_toks R
                | SOME provide (*must be sorted, can be compact*) => let
                     val len = Lazy.lazy (fn () => length (Proof_Context.get_thms (the ctxt) name))
                     val segs = select_facts len provide ivs
                             |> maps (fn s => tokenize_seg s @ attrs)
                  in segs @ subs_toks remaining
                 end)
   in subst
  end



fun map_tac_token'gen _ (Method.Source []) = (Method.Source [])
  | map_tac_token'gen F (Method.Source (h::L)) = (Method.Source (h :: subst_fact_in_toks'gen F L))
  | map_tac_token'gen F (Method.Combinator (oi, opr, tacs))
      = Method.Combinator (oi, opr, map (map_tac_token'gen F) tacs)
  | map_tac_token'gen _ m = m

fun exists_tac_token _ (Method.Source []) = false
  | exists_tac_token P (Method.Source (_::L)) = exists (exists_token_content P) L
  | exists_tac_token P (Method.Combinator (_, _, tacs))
      = exists (exists_tac_token P) tacs
  | exists_tac_token _ _ = false

fun map_a_fact ctxt F (origin as Facts.Named ((name,_),iv), attrs0) =
  let val attrs = map (subst_fact_in_toks'gen (subst_fact_in_toks ctxt F)) attrs0
   in case F ctxt (unquote name)
        of NONE => [(origin, attrs)]
         | SOME provide => let
               fun mk_iv (_,i,n,N) =
                    if n = N andalso i = 0
                    then NONE
                    else if n = 1
                    then SOME [Facts.Single (i+1)]
                    else if i + n = N
                    then SOME [Facts.From (i+1)]
                    else SOME [Facts.FromTo (i+1,i+n)]
               fun mk_fact (arg as (name,_,_,_)) = (name, mk_iv arg)
               fun compact ((x as (name1, iv1)) :: (LL as (name2, iv2) :: L)) =
                    if name1 = name2
                    then (case (iv1,iv2)
                      of (SOME iv1', SOME iv2') => compact ((name1, SOME (iv1' @ iv2')) :: L)
                       | (NONE, _) => compact ((name1, NONE) :: L)
                       | (_, NONE) => compact ((name1, NONE) :: L) )
                    else x :: compact LL
                 | compact L = L

               val len = Lazy.lazy (fn () => length (Proof_Context.get_thms (the ctxt) name))
            in select_facts len provide iv
            |> map mk_fact
            |> compact
            |> map (fn (name, iv) => (Facts.Named ((name, Position.none), iv), attrs))
           end
  end
  | map_a_fact _ _ origin = [origin]

fun replace_fact_expr_with_name'core ctxt raw_expr =
      let val thy = Proof_Context.theory_of ctxt
          val facts = Proof_Context.facts_of ctxt
          val local_facts =
            Facts.dest_static true [Global_Theory.facts_of thy] facts
       in case try (Syntax.read_prop (Proof_Context.set_mode Proof_Context.mode_pattern ctxt)) raw_expr
       of NONE => NONE
        | SOME pat => let
          fun distinct [(_, _, fact)] = SOME fact
            | distinct ((th1, len1, fact1) :: (th2, len2, fact2) :: L) =
                if Thm.equiv_thm thy (th1, th2)
                then if len1 <= len2
                   then distinct ((th1, len1, fact1) :: L)
                   else distinct ((th2, len2, fact2) :: L)
                else NONE
            | distinct _ = NONE
          val options = map_filter (fn (name, ths) =>
                    case get_index (fn th => if Pattern.matches thy (pat, Thm.prop_of th)
                                                    then SOME th
                                                    else NONE ) ths
                      of NONE => NONE
                       | SOME (i, th) => let
                             val name' = simp_fact_name ctxt name
                             val iv = (case ths of [_] => NONE
                                                 | _ => SOME [Facts.Single (i+1)] )
                          in if name' = "this"
                           then NONE
                           else SOME (th, length ths, Facts.Named ((name', Position.none), iv))
                         end
                    ) local_facts
       in distinct options
      end
      end

fun replace_fact_expr_with_name _ (origin as (Facts.Named _, _)) = [origin]
  | replace_fact_expr_with_name opt_ctxt (origin as (Facts.Fact raw_expr, attrs)) =
      let val ctxt = (case opt_ctxt of SOME ctxt => ctxt
                                     | NONE => error "BUG replace_fact_expr_with_name - opt_ctxt" )
       in case replace_fact_expr_with_name'core ctxt raw_expr
       of SOME x => [(x, attrs)]
        | NONE   => [origin]
      end

fun replace_fact_expr_with_name_in_toks _ [] _ = error "BUG replace_fact_expr_with_name_in_toks - empty"
  | replace_fact_expr_with_name_in_toks opt_ctxt (toks as tok :: _) continue =
  let fun fallback [] = error "BUG replace_fact_expr_with_name_in_toks - empty"
        | fallback (tok :: toks) = tok :: continue toks
   in if Token.is_kind Token.Cartouche tok
    then case try Parse.term toks
           of SOME (raw_expr, toks') =>
               let val ctxt = (case opt_ctxt of SOME ctxt => ctxt
                                              | NONE => error "BUG replace_fact_expr_with_name_in_toks - opt_ctxt" )
                in case replace_fact_expr_with_name'core ctxt raw_expr
                of SOME x => tokenize_factref x @ continue toks'
                 | NONE   => fallback toks
               end
            | NONE => fallback toks
    else fallback toks
  end




fun map_facts'gen G factsx =
  let val ret' = maps G factsx
   (* val ret' = maps (map_a_fact (SOME ctxt) F) factsx *)
      val _ = if exists ((fn Facts.Named (_, SOME iv) => 
                              exists (fn Facts.Single i => i <= 0
                                       | Facts.From i => i <= 0
                                       | Facts.FromTo (i,j) => i <= 0 orelse j < i) iv
                          | _ => false) o fst) ret'
              then error "BUG map_facts"
              else ()
   in if eq_list pointer_eq (ret', factsx)
   then factsx
   else ret'
(*   else case (try (Attrib.eval_thms ctxt) factsx,
              try (Attrib.eval_thms ctxt) ret')
     of (SOME thms1, SOME thms2) =>
          let val thy = Proof_Context.theory_of ctxt
           in if eq_list (Thm.equiv_thm thy) (thms1, thms2)
            then ret'
            else (maps (map_a_fact (SOME ctxt) F) factsx;
                 error "BUG map_facts'" )
          end
      | _ => ret' *)
  end

fun exists_fact_factref P (Facts.Named ((name,_),_)) = P name
  | exists_fact_factref _ _ = false
fun exists_fact_fact  P (rf, toks)
      = exists_fact_factref P rf orelse exists (exists (exists_token_content P)) toks

fun map_ast_fact'gen G F =
let fun map_ast (s, PROOF (tac, body))
          = (s, PROOF (map_tac_token'gen (F (Option.map Proof.context_of s)) tac, body))
      | map_ast (s, QED (tac, time))
          = (s, QED (Option.map (map_tac_token'gen (F (Option.map Proof.context_of s))) tac, time))
      | map_ast (s, USING facts)
          = (s, USING (map_facts'gen (G (Option.map Proof.context_of s)) facts))
    (*  | map_ast_fact F (s, MCALCULATION (B, goal, using))
          = let val using' = map (fn (rules, facts) =>
                      let val ctxt = Proof.context_of (the s)
                          val facts' = facts |> map (rpair [])
                                             |> map_facts ctxt F
                                             |> map fst
                          val rules' = map_facts ctxt F rules
                       in (rules', facts')
                      end ) using
             in (s, MCALCULATION (B, goal, using'))
            end *)
      | map_ast (s, WITH facts)
          = (s, WITH (map_facts'gen (G (Option.map Proof.context_of s)) facts))
      | map_ast (s, FROM facts)
          = (s, FROM (map_facts'gen (G (Option.map Proof.context_of s)) facts))
      | map_ast (s, UNFOLD facts)
          = (s, UNFOLD (map_facts'gen (G (Option.map Proof.context_of s)) facts))
      | map_ast (s, ISAR_BY ((t1, t2), time))
          = (s, ISAR_BY ( (map_tac_token'gen (F (Option.map Proof.context_of s)) t1,
                           Option.map (map_tac_token'gen (F (Option.map Proof.context_of s))) t2)
                        , time ))
      | map_ast (s, APPLY_END tac)
          = (s, APPLY_END (map_tac_token'gen (F (Option.map Proof.context_of s)) tac))
      | map_ast (s, TACTIC (tac, (using, not_using), t))
          = (s, TACTIC (map_tac_token'gen (F (Option.map Proof.context_of s)) tac,
                        (map_facts'gen (G (Option.map Proof.context_of s)) using,
                         map_facts'gen (G (Option.map Proof.context_of s)) not_using),
                        t))
      | map_ast (s, NOTE facts)
          = let val ctxt = Option.map Proof.context_of s
             in (s, NOTE (map (fn (AT, facts') =>
                              (AT, map_facts'gen (G ctxt) facts')) facts))
            end
      | map_ast X = X
 in map_ast
end


fun map_ast_fact F =
      map_ast_fact'gen (fn ctxt => map_a_fact ctxt F)
                       (fn ctxt => subst_fact_in_toks ctxt F)
fun map_ast_fact' F = elementwise_pass NONE (map_ast_fact F)

val replace_fact_expr =
      map_ast_fact'gen replace_fact_expr_with_name
                       replace_fact_expr_with_name_in_toks
val replace_fact_expr' = elementwise_pass NONE replace_fact_expr




fun exists_fact_in P (PROOF (tac, _)) = exists_tac_token P tac
  | exists_fact_in P (QED (SOME tac, _)) = exists_tac_token P tac
  | exists_fact_in P (USING facts) = exists (exists_fact_fact P) facts
(*  | exists_fact_in P (MCALCULATION (_,_,using)) =
      exists (fn (rules, this) =>
                exists (exists_fact_factref P) this orelse
                exists (exists_fact_fact P) rules
             ) using *)
  | exists_fact_in P (WITH  facts) = exists (exists_fact_fact P) facts
  | exists_fact_in P (FROM  facts) = exists (exists_fact_fact P) facts
  | exists_fact_in P (UNFOLD facts)= exists (exists_fact_fact P) facts
  | exists_fact_in P (ISAR_BY ((t1, t2), _))
      = exists_tac_token P t1 orelse
        (case t2 of SOME tac => exists_tac_token P tac
                  | NONE => false)
  | exists_fact_in P (APPLY_END tac) = exists_tac_token P tac
  | exists_fact_in P (TACTIC (tac, (using, not_using), _))
      = exists (exists_fact_fact P) using orelse
        exists (exists_fact_fact P) not_using orelse
        exists_tac_token P tac
  | exists_fact_in _ _ = false

val exists_ast_fact = exists_ast o exists_fact_in
fun exists_ast_fact' P = exists (exists_ast_fact P o snd)

fun exists_fact_inm P (MCRUSH (_, (w,wo))) =
      exists (exists_fact_fact P) w orelse exists (exists_fact_fact P) wo
  | exists_fact_inm P (MSIMP (w,wo)) =
      exists (exists_fact_fact P) w orelse exists (exists_fact_fact P) wo
  | exists_fact_inm P (MHAMMER (w,wo)) =
      exists (exists_fact_fact P) w orelse exists (exists_fact_fact P) wo
  | exists_fact_inm P (MEND ((_,_,w,wo), _)) =
      exists (exists_fact_fact P) w orelse exists (exists_fact_fact P) wo
  | exists_fact_inm P (MUNFOLD w) = exists (exists_fact_fact P) w
  | exists_fact_inm P (MTACTIC (m,(u,nu),_)) =
      exists_tac_token P m orelse
      exists (exists_fact_fact P) u orelse
      exists (exists_fact_fact P) nu
  | exists_fact_inm P (MRULE (w,wo)) =
      exists (exists_fact_fact P) w orelse exists (exists_fact_fact P) wo
  | exists_fact_inm P (MCFG_FACTS facts) =
      exists (exists (exists_fact_fact P) o snd) facts
  | exists_fact_inm P (MINDUCT (_,_,w)) = exists (exists_fact_fact P) w
  | exists_fact_inm P (MCASE (_,_,w)) = exists (exists_fact_fact P) w
  | exists_fact_inm P (MINSERT w) = exists (exists_fact_fact P) w
(*  | exists_fact_inm P (MCALC ((_,_,w),_)) =
      exists (fn (x,y) => exists (exists_fact_fact P) x orelse
                          exists (exists_fact_factref P) y
             ) w *)
  | exists_fact_inm _ _ = false

val exists_mast_fact = exists_mast o exists_fact_inm
fun exists_mast_fact' P = exists (exists_mast_fact P o snd)


(* collects facts in AST *)


fun collect_facts ast = let
     fun add (facts1, facts2) (ret1, ret2) =
             (merge fact_eq (ret1, facts1), merge fact_eq (ret2, facts2))
  in linear_fold (
       fn (_, USING facts) => add (facts, [])
        | (_, WITH  facts) => add (facts, [])
        | (_, FROM  facts) => add (facts, [])
        | (_, ISAR_BY ((m1, SOME m2),_)) =>
              add (merge_facts2 [facts_in_method m1, facts_in_method m2])
        | (_, ISAR_BY ((m1, NONE),_)) => add (facts_in_method m1)
        | (_, APPLY_END m) => add (facts_in_method m)
        | (_, ALSO  facts) => add (facts, [])
        | (_, FINALLY (facts, _)) => add (facts, [])
        | (_, UNFOLD facts) => add (facts, [])
        | (_, TACTIC (m, facts, _)) =>
                 add (facts_in_method m)
              #> add facts
        | (_, NOTE facts) => add (maps snd facts, [])
        | _ => I
     ) ast ([], [])
 end

fun collect_mfacts ast = let
     fun add (w',wo') (w,wo) = (merge fact_eq (w,w'), merge fact_eq (wo,wo'))
  in linear_foldm (
       fn (_, MCRUSH  (_, wwo)) => add wwo
        | (_, MHAMMER wwo) => add wwo
        | (_, MEND ((_,_,w,wo), _)) => add (w,wo)
        | (_, MSIMP wwo) => add wwo
        | (_, MUNFOLD w) => add (w,[])
        | (_, MTACTIC (_,w,_)) => add w
        | (_, MRULE (w,w')) => add (merge fact_eq (w,w'), [])
        | (_, MCFG_FACTS w) => add (maps snd w,[])
        | (_, MINSERT w) => add (w,[])
        | _ => I
     ) ast ([],[])
 end

(** Print **)

(* fun print_toks toks = String.concatWith " " (map Token.unparse toks) *)

val msorry_printing = Unsynchronized.ref "msorry"

fun print_method (Method.Source toks) = print_toks toks
  | print_method (Method.Combinator (_, Method.Then, tacs))
      = implode_with ", " (map print_method tacs)
  | print_method (Method.Combinator (_, Method.Then_All_New, tacs))
      = implode_with "; " (map print_method tacs)
  | print_method (Method.Combinator (_, Method.Orelse, tacs))
      = implode_with " | " (map (fn tac => ["("] @ print_method tac @ [")"]) tacs)
  | print_method (Method.Combinator (_, Method.Try, [x1]))
      = ["("] @ print_method x1 @ [")?"]
  | print_method (Method.Combinator (_, Method.Repeat1, [x1]))
      = ["("] @ print_method x1 @ [")+"]
  | print_method (Method.Combinator (_, Method.Select_Goals i, [x1]))
      = ["("] @ print_method x1 @ [")[", string_of_int i, "]"]
  | print_method (m as Method.Basic _) =
      if pointer_eq (m, method_sorry)
      then [!msorry_printing]
      else error "BUG Fail to print internal methods"
  | print_method (Method.Combinator _) = error "BUG Bad method combinator"



fun print_ty_raw' (Type (N, TS)) = ["("] @ maps print_ty_raw' TS @ [") ", N]
  | print_ty_raw' (TFree (N, _)) = [N]
  | print_ty_raw' (TVar (N, _))  = [Term.string_of_vname N]
fun print_ty_raw ctxt T =
  let val s = String.concat (print_ty_raw' T)
   in if \<^try>\<open>Syntax.read_typ ctxt s = T catch _ => false\<close>
      then s else raise TERM("BUG Fail to print type in a raw way", [])
  end
fun print_ty ctxt T =
  let val s = trim_markup (Syntax.string_of_typ ctxt T)
   in if \<^try>\<open>Syntax.read_typ ctxt s = T catch _ => false\<close> then s else print_ty_raw ctxt T
  end

fun print_tm_raw'_ty ctxt =
  let fun print _ (Const (N,T)) = ["(",N,"::", print_ty ctxt T, ")"]
        | print _ (Free (N,T))  = ["(",N,"::", print_ty ctxt T, ")"]
        | print _ (Var (N,T))   = ["(",Term.string_of_vname N,"::", print_ty ctxt T, ")"]
        | print (bvs,_)    (Bound i)     = [nth bvs i]
        | print (bvs,ctxt) (Abs (N,_,X)) =
            let val (N',ctxt') = Name.variant N ctxt
             in "(\<lambda>" :: N' :: ". " :: print (N'::bvs, ctxt') X @ [")"]
            end
        | print bvc (tm as (_ $ _)) =
            let val (H,args) = strip_comb tm
             in "(" :: print bvc H @ maps (fn x => " " :: print bvc x) args @ [")"]
            end
    in print ([], Name.context)
   end

fun print_tm_raw' ctxt =
  let fun print _ (Const (N,_)) = [N]
        | print _ (Free (N,_))  = [Variable.revert_fixed ctxt N]
        | print _ (Var (N,_))   = [Term.string_of_vname N]
        | print (bvs,_)    (Bound i)     = [nth bvs i]
        | print (bvs,ctxt) (Abs (N,_,X)) =
            let val (N',ctxt') = Name.variant N ctxt
             in "(\<lambda>" :: N' :: ". " :: print (N'::bvs, ctxt') X @ [")"]
            end
        | print bvc (tm as (_ $ _)) =
            let val (H,args) = strip_comb tm
             in "(" :: print bvc H @ maps (fn x => " " :: print bvc x) args @ [")"]
            end
   in print ([], Name.context)
  end

fun print_tm ctxt tm =
  let val tm = Envir.beta_eta_contract tm
      val s1 = trim_markup (Syntax.string_of_term ctxt tm)
   in if \<^try>\<open>Syntax.read_term ctxt s1 aconv tm catch _ => false\<close> then s1
    else let
      val pty = not (Config.get ctxt Printer.show_types)
      val s2 = if pty
               then trim_markup (Syntax.string_of_term (Config.put Printer.show_types true ctxt) tm)
               else s1
   in if pty andalso \<^try>\<open>Syntax.read_term ctxt s2 aconv tm catch _ => false\<close> then s2
    else let
      val s3 = trim_markup (Syntax.string_of_term (Config.put Printer.show_sorts true ctxt) tm)
   in if \<^try>\<open>Syntax.read_term ctxt s3 aconv tm catch _ => false\<close> then s3
    else let
      val s = String.concat (print_tm_raw' ctxt tm)
   in if \<^try>\<open>Syntax.read_term ctxt s aconv tm catch _ => false\<close> then s
    else let val s4 = String.concat (print_tm_raw'_ty ctxt tm)
      in if \<^try>\<open>Syntax.read_prop ctxt s4 aconv tm catch _ => false\<close> then s4
         else raise TERM("BUG print_prop", [tm])
     end
  end
  end
  end
  end

fun print_prop ctxt tm =
  let val tm = Envir.beta_eta_contract tm
      val s1 = trim_markup (Syntax.string_of_term ctxt tm)
      fun filter (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = X
        | filter X = X
   in if \<^try>\<open>Syntax.read_prop ctxt s1 aconv tm catch _ => false\<close> then s1
    else let
      val pty = not (Config.get ctxt Printer.show_types)
      val s2 = if pty
               then trim_markup (Syntax.string_of_term (Config.put Printer.show_types true ctxt) tm)
               else s1
   in if pty andalso \<^try>\<open>Syntax.read_prop ctxt s2 aconv tm catch _ => false\<close> then s2
    else let
      val s2s = trim_markup (Syntax.string_of_term (Config.put Printer.show_sorts true ctxt) tm)
   in if \<^try>\<open>Syntax.read_prop ctxt s2s aconv tm catch _ => false\<close> then s2s
    else let
      val s3 = String.concat (print_tm_raw' ctxt (filter tm))
   in if \<^try>\<open>Syntax.read_prop ctxt s3 aconv tm catch _ => false\<close> then s3
    else let val s4 = String.concat (print_tm_raw'_ty ctxt (filter tm))
      in if \<^try>\<open>Syntax.read_prop ctxt s4 aconv tm catch _ => false\<close> then s4
         else raise TERM("BUG print_prop", [tm])
     end
  end
  end
  end
  end

fun may_print_tm ctxt (prop,fallback) =
  print_tm ctxt prop
    handle TERM _ => fallback

fun may_print_prop ctxt (prop,fallback) =
  print_prop ctxt prop
    handle TERM _ => fallback

fun print_statement (tm, [])   = print_term tm
  | print_statement (tm, pats) = print_term tm @ maps (fn pat => " (" :: print_term pat @ [")"]) pats
val print_statements = implode_with " " o map print_statement
val print_attr_statements = implode_with " and " o
      map (fn (B,tms) => print_attrbind' B @ print_statements tms)

fun print_structured_statement ((vars, assms, show) : structured_statement) =
      print_attr_statements show
        @ (if null assms then [] else " if " :: implode_with " and " (map print_statements assms))
        @ print_for vars

fun print_structured_statement' ((vars, assms, show) : structured_statement') =
      print_attr_statements show
        @ (if null assms then [] else " if " :: print_attr_statements assms)
        @ print_for vars

(*
fun print_structured_statement' ((vars, assms, show) : structured_statement') =
        print_structured_statement (vars, map snd assms, show)
      @(if null assms
        then []
        else "\nnote " :: implode_with " and " (fst (fold_map (fn (B,tms) => fn N =>
              let val M = length tms
               in case M
               of 1 => ([quote_space (Binding.name_of B), " = that(", string_of_int N, ")"], N + M)
                | _ => ([quote_space (Binding.name_of B), " = that(",
                            string_of_int N, "-", string_of_int (N+M-1), ")"], N + M)
              end
             ) assms 1))
        ) *)

fun print_obtain (B,(vs,props)) =
        (if Binding.is_empty B then [] else ["(", Binding.name_of B, ")"])
      @ (if null vs then [] else print_vars vs @ [" where "])
      @ implode_with " and " (map print_term props)

fun print_locale_expr (exprs, vars) =
      let fun print_insts (Expression.Positional terms) =
                maps (fn NONE => [" _"] | SOME tm => " " :: print_term tm) terms
            | print_insts (Expression.Named terms) =
                " where " :: implode_with " and " (
                    map (fn (name,tm) => name :: " = " :: print_term tm) terms)
          fun print_rewr [] = []
            | print_rewr rewrs =
                " rewrites " :: implode_with " and " (
                    map (fn (B,prop) => print_attrbind' B @ print_term prop
                ) rewrs)
          fun print_prefix (qual,mandatory) =
                if (qual,mandatory) = ("",false) then []
                else qual :: (if mandatory then [] else ["?"]) @ [": "]
          fun print_expr ((name,_), (prefix, (inst, rewr))) =
                print_prefix prefix @ name :: print_insts inst @ print_rewr rewr
       in implode_with " + " (map print_expr exprs) @ print_for vars
      end

val space_word = Byte.charToByte #" "
val newline_word = Byte.charToByte #"\n"
fun mk_newline_ident' i = Byte.bytesToString (Word8Vector.tabulate (2*i + 1, fn i =>
      if i = 0 then newline_word else space_word))
val newline_indents = Vector.tabulate (20, mk_newline_ident')
fun newline_indent_of n = if n < 20 then Vector.sub (newline_indents, n)
                                    else mk_newline_ident' n

fun mk_ident' i = Byte.bytesToString (Word8Vector.tabulate (2*i, K space_word))
val indents = Vector.tabulate (10, fn i => mk_ident' i)
fun indent_of n = if n < 10 then Vector.sub (indents, n) else mk_ident' n


fun print_ast use_mproof =
  let val mproof = if use_mproof then "mproof" else "proof (-)"
      val mqed = if use_mproof then "mqed" else "qed"
      datatype mode = NL | SP | ST
      fun newline i NL = newline_indent_of i
        | newline i ST = indent_of i
        | newline _ SP = " "
      fun print _ _ [] = ["\n"]
        | print i ik ((_, PROOF (tac, body)) :: L) =
              newline i ik :: "proof (" :: print_method tac @ ")" :: print (i+1) NL body
            @ print i NL L
        | print i _ ((_, QED (tac, _)) :: L) =
            newline (i-1) NL :: "qed" ::
            (case tac of SOME tac' => " ("::print_method tac'@[")"] | _ => [])
            @ print i NL L
        | print i ik ((_, BRCBLK ((B,_), body)) :: L) =
              newline i ik :: "{" :: print (i+1) NL body
            @ newline i NL :: "note " :: quote_space (Binding.name_of B) :: " = this"
           :: print i NL L
        | print i _ ((_, ENDBLK) :: L) = newline (i-1) NL :: "}" :: print (i-1) NL L
        | print i ik ((_, FIX vs) :: L) = newline i ik :: "fix " :: print_vars vs @ print i NL L
        | print i ik ((_, ASSUME ss) :: L) =
              newline i ik :: "assume " :: print_structured_statement ss @ print i NL L
        | print i ik ((_, HAVE (ss, body)) :: L) =
              newline i ik :: "have " :: print_structured_statement' ss
            @ print (i-1) NL body @ print i NL L
        | print i ik ((_, THUS (ss, body)) :: L) =
              newline i ik :: "thus " :: print_structured_statement' ss
            @ print (i+1) NL body @ print i NL L
        | print i ik ((_, HENCE (ss, body)) :: L) =
              newline i ik :: "hence " :: print_structured_statement' ss
            @ print (i+1) NL body @ print i NL L
        | print i ik ((_, SHOW (ss, body)) :: L) =
              newline i ik :: "show " :: print_structured_statement' ss
            @ print (i+1) NL body @ print i NL L
        | print i ik ((_, CASE (B,(N,vs))) :: L) =
              newline i ik :: "case " :: print_attrbind' B @ " " ::
            (case vs of [] => [N]
                      | _ => " (" :: N ::
                             maps (fn SOME N => [" ",N] | NONE => ["_"]) vs @ [")"]
            ) @ print i NL L
        | print i ik ((_, ISAR_OBTAIN ((vs,ss), body)) :: L) =
              newline i ik :: "obtain " :: print_vars vs
            @ " where " :: print_structured_statement ss
            @ print (i+1) NL body @ print i NL L
        | print i ik ((_, ISAR_CONSIDER ((B, obt), body)) :: L) =
            newline i ik :: "consider " ::
            implode_with " | " (map print_obtain obt) @ print (i+1) NL body
            @ newline i NL :: "note " :: Binding.name_of B :: " = this" :: print i NL L
        | print i ik ((_, SUBGOAL ((a,b,(opt,c)), body)) :: L) =
            newline i ik :: "subgoal"
         :: (if Binding.is_empty_atts a then [] else " " :: print_attrbind a)
          @ (case b of SOME b' => "premises " ::  print_attrbind b'
                     | NONE => [] )
          @ (if opt then " for ..." else " for ")
         :: implode_with " and " (map (fn (NONE  , _) => ["_"]
                                        | (SOME s, _) => [s] ) c)
          @ print (i+1) NL body
          @ print i NL L
        | print i ik ((_, USING facts) :: L) =
            newline i ik :: "using " :: print_facts facts @ print i SP L
(*        | print ((_, MCALCULATION (B, goal, using)) :: L) =
            "have " :: quote_space (Binding.name_of B) :: ": " :: print_term goal
          @ " using" :: maps (maps (fn B => " " :: print_factref B) o #2) using
          @ " sorry\n" :: print L *)
        | print k ik ((_, DEFER i) :: L) =
            newline k ik :: "defer " :: string_of_int i :: print i NL L
        | print k ik ((_, PREFER i) :: L) =
            newline k ik :: "prefer " :: string_of_int i :: print i NL L
        | print i ik ((_, WITH facts) :: L) =
            newline i ik :: "with " :: implode_with " " (map print_fact facts) @ print i SP L
        | print i ik ((_, FROM facts) :: L) =
            newline i ik :: "from " :: implode_with " " (map print_fact facts) @ print i SP L
        | print i ik ((_, ISAR_THEN) :: L) =
            newline i ik :: "then" :: print i SP L
        | print i ik ((_, ISAR_BY ((tac1, tac2), _)) :: L) =
            newline i ik :: "by (" :: print_method tac1 @ ") " ::
              (case tac2 of SOME tac => "("::print_method tac @ [")"] | _ => [])
            @ print i NL L
        | print i ik ((_, APPLY_END tac) :: L) =
            newline i ik :: "apply_end (" :: print_method tac @ ")" :: print i NL L
        | print i ik ((_, DONE) :: L) = newline i ik :: "done" :: print i NL L
        | print i _ ((_, DDOT) :: L) = newline i SP :: ".." :: print i NL L
        | print i _ ((_,  DOT) :: L) = newline i SP :: "."  :: print i NL L
        | print i ik ((_, ALSO _) :: L) =
            newline i ik :: "also" :: print i SP L
        | print i ik ((_, FINALLY _) :: L) =
            newline i ik :: "finally" :: print i SP L
        | print i ik ((_, MOREOVER) :: L) =
            newline i ik :: "moreover" :: print i SP L
        | print i ik ((_, ULTIMATELY _) :: L) =
            newline i ik :: "ultimately" :: print i SP L
        | print i ik ((_, UNFOLD facts) :: L) =
            newline i ik :: "unfolding " :: implode_with " " (map print_fact facts) @ print i NL L
        | print i ik ((_, TACTIC (tac, (using, _), _)) :: L) =
            newline i ik
            :: (if null using then [] else "using " :: print_facts using)
            @ "apply (" :: print_method tac @ ")" :: print i NL L
        | print i ik ((_, DEFINE (vs, astmt, fixes)) :: L) =
            newline i ik
             :: "define " :: print_vars vs
              @ " where " :: print_attr_statements astmt
              @ print_for fixes
              @ print i NL L
        | print i ik ((_, LET args) :: L) =
            newline i ik
            :: "let " :: implode_with " and " (map (fn (vs,tm) =>
               implode_with " " (map (single o trim_markup) vs) @ " = " :: print_term tm
             ) args)
            @ print i NL L
        | print i ik ((_, NOTATION (mode, xx)) :: L) =
            newline i ik
             :: "write " :: (if mode = Syntax.mode_default then []
                         else case mode
                           of ("", false)   => ["output"]
                            | (name, false) => [name, " output"]
                            | (name, _ )    => [name] )
              @ implode_with " and " (map (fn (tm,synt) =>
                    print_term tm @ " (" :: print_mixfix synt @ [")"] ) xx)
              @ print i NL L
        | print i ik ((_, INCLUDE names) :: L) =
              newline i ik
           :: "include " :: implode_with " " (map (single o quote_space) names)
            @ print i NL L
        | print i ik ((_, INCLUDING names) :: L) =
              newline i ik :: "including " :: implode_with " " (map (single o quote_space) names)
            @ print i NL L
        | print i ik ((_, NEXT) :: L) =
            newline i ik :: "next" :: print i NL L
        | print i ik ((_, OPEN_MODULE (exprs, body)) :: L) =
                newline i ik :: "interpret " :: print_locale_expr  exprs
              @ print i NL body @ print i NL L
        | print i ik ((_, NOTE notes) :: L) =
            newline i ik :: "note " :: implode_with " and " (
                map (fn (B,facts) => print_attrbind B @ " = " :: print_facts facts) notes)
            @ print i NL L
        | print i ik ((_, MPROOF (pre, (_,ss), _, prf)) :: L) =
             newline i ik :: mproof :: print (i+1) NL pre
              @ newline (i+1) NL :: "show " :: print_structured_statement' ss
              @ print (i+2) NL prf
              @ newline i NL :: mqed :: print i NL L
        | print i ik ((_, BRANCH_SUBGOALS []) :: L) = print i ik L
        | print i ik ((_, BRANCH_SUBGOALS [body]) :: L) = print i ik body @ print i NL L
        | print i _  ((_, BRANCH_SUBGOALS bodys) :: L) =
               newline i NL :: "(*" :: string_of_int (length bodys) :: " subgoals*)"
            :: implode_with (newline i NL ^ "(*NEXT*)")
                            (map (print (i+1) NL) bodys)
             @ newline i NL :: "(*end " :: string_of_int (length bodys) :: " subgoals*)"
            :: print i NL L
        | print i ik ((_, SORRY) :: L) = newline i ik :: "sorry" :: print i NL L

   in print 0 ST
  end

val print_ast = String.concat oo print_ast

fun print_mvars NONE = []
  | print_mvars (SOME vs) =
      ( if null vs then [] else [" VARS "] )
      @ implode_with " " (map (fn NONE => ["_"] | SOME s => [s]) vs)
fun print_with _ [] = []
  | print_with m facts = m :: print_facts facts

val print_comments = Unsynchronized.ref false


(*** Translation Passes ***)

(** Initial Pass **)

val VARS = Parse.vars

exception Term_Restore_Fail of term' * term
exception Type_Restore_Fail of typ'  * typ

(*
fun restore_tm ctxt (tm, src) =
      if tm aconv Syntax.read_term ctxt src then src
      else raise Term_Restore_Fail ((tm, src), Syntax.read_term ctxt src)
fun restore_prop ctxt (tm, src) =
      if tm aconv Syntax.read_prop ctxt src then src
      else raise Term_Restore_Fail ((tm, src), Syntax.read_prop ctxt src)
fun restore_ty ctxt (ty, src) =
      if ty = Syntax.read_typ ctxt src then src
      else raise Type_Restore_Fail ((ty, src), Syntax.read_typ ctxt src)
*)

val if_statement' = Scan.optional (
        (Parse.$$$ "if" || Parse.$$$ "when") |-- Parse.!!! Parse_Spec.statement') [];
val if_statement = Scan.optional (
        (Parse.$$$ "if" || Parse.$$$ "when") |-- Parse.!!! Parse_Spec.statement) [];

fun structured_statement F =
  Parse_Spec.statement -- if_statement' -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) => F (fixes, assumes, shows) )

fun structured_statement' F =
  Parse_Spec.statement -- if_statement  -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) => F (fixes, assumes, shows) )

exception IGNORE
fun ignore _ = raise IGNORE

fun TODO name _ = raise Unsupported name
fun BAD_SOURCE _ = raise Bad_Source ""

val standard_tac = Method.Source [mk_idt "standard"]
val no_tac = Method.Source [mk_idt "-"]

local

val text_range = Option.map (rpair Position.no_range)

fun facts  F = Parse.and_list1 Parse.thms1 >> F
fun facts' F = Scan.optional (Parse.and_list1 Parse.thms1) [] >> F

fun tactic_parser F = Method.parse >> (F o fst)
(* fun tactic_parser2 state = Method.parse -- Scan.option Method.parse
                       >> (fn ((t1,_), SOME (t2,_)) => pair state (TACTIC (
                                   Method.Combinator (Method.no_combinator_info,
                                                      Method.Then,
                                                      [t1,t2])))
                            | ((t1,_), NONE) => pair state (TACTIC t1) ) *)
val qed_parser = Scan.option (Method.parse >> fst) >> (QED o rpair NONE)
val proof_parser =
        Scan.optional (Method.parse >> fst) standard_tac >> (PROOF o rpair [])

val fix_parser = VARS >> FIX
val assume_parser = structured_statement ASSUME
val unfold_parser = facts (UNFOLD o flat)
val using_parser  = facts (USING  o flat)

(*TODO*)
val case_parser = (
        Parse_Spec.opt_thm_name ":" --
      ( \<^keyword>\<open>(\<close> |-- Parse.!!! (Parse.name
                    -- Scan.repeat (Parse.maybe Parse.name) --| \<^keyword>\<open>)\<close>)
     || Parse.name >> rpair []))
      >> CASE
val restore_case = apsnd ( apfst (rpair Position.none)
                        #> apsnd (map (Option.map Binding.name)))

val define_parser = (Parse.vars --| Parse.where_) -- Parse_Spec.statement -- Parse.for_fixes
      >> (fn ((a,b),c) => DEFINE (a,b,c))

val config_parser = Parse_Spec.name_facts >> NOTE
fun include_parser C = Scan.repeat1 Parse.name >> C

val obtain_parser =
     Scan.optional (Parse.vars --| Parse.where_) []
  -- (Parse_Spec.statement -- Parse_Spec.if_statement' -- Parse.for_fixes)
    >> (fn (BB, ((shows, assumes), fixes)) => ISAR_OBTAIN ((BB, (fixes, assumes, shows)), []) )

val consider_parser = Parse_Spec.obtains
      >> (ISAR_CONSIDER o rpair [] o pair Binding.empty)

local

val opt_fact_binding =
  Scan.optional (Parse.binding -- Parse.opt_attribs || Parse.attribs >> pair Binding.empty)
    Binding.empty_atts;

val for_params =
  Scan.optional
    (\<^keyword>\<open>for\<close> |--
      Parse.!!! ((Scan.option Parse.dots >> is_some) --
        (Scan.repeat1 (Parse.maybe_position Parse.name_position))))
    (false, []);

in
val subgoal_parser =
      opt_fact_binding -- (Scan.option (\<^keyword>\<open>premises\<close> |-- Parse.!!! opt_fact_binding)) -- for_params
    >> (fn ((a,b),c) => SUBGOAL ((a,b,c), []))
end

in

val case_parser = case_parser
val restore_case = restore_case

val initial_parsers = Symtab.make [

  ("apply",      tactic_parser (fn m => TACTIC (m, ([], []), NONE))),
  ("proof",      proof_parser),
  ("qed"  ,      qed_parser),
  ("apply_end",  tactic_parser APPLY_END),
  ("by",         (Method.parse >> fst)
              -- Scan.option (Method.parse >> fst)
              >> (ISAR_BY o rpair NONE)),
  ("fix",        fix_parser),
  ("assume",     assume_parser),
  ("presume",    assume_parser),
  ("unfolding",  unfold_parser),
  ("using",      using_parser),
  ("case",       case_parser),
  ("write",      Parse.syntax_mode -- Parse.and_list1 (Parse.const -- Parse.mixfix)
              >> NOTATION ),
  ("let",        Parse.and_list1 (Parse.and_list1 Parse.term -- (\<^keyword>\<open>=\<close> |-- Parse.term))
              >> LET ),
  ("define",     define_parser),
  ("supply",     config_parser),
  ("note",       config_parser),
  ("include",    include_parser INCLUDE),
  ("including",  include_parser INCLUDING),

  ("defer",      Scan.optional Parse.nat 1 >> DEFER),
  ("prefer",     Scan.optional Parse.nat 1 >> DEFER),
  ("with",       facts (WITH o flat)),
  ("from",       facts (FROM o flat)),
  ("then",       Scan.succeed ISAR_THEN),

  ("have",       structured_statement' (HAVE  o rpair [])),
  ("show",       structured_statement' (SHOW  o rpair [])),
  ("thus",       structured_statement' (THUS  o rpair [])),
  ("hence",      structured_statement' (HENCE o rpair [])),
  ("interpret",  Parse.!!! Parse_Spec.locale_expression >> (OPEN_MODULE o rpair [])),
  ("consider",   consider_parser),
  ("obtain",     obtain_parser),

  ("next",       Scan.succeed NEXT),
  ("done",       Scan.succeed DONE),
  (".",          Scan.succeed DOT ),
  ("..",         Scan.succeed DDOT),

  ("{",          Scan.succeed (BRCBLK ((Binding.empty, NONE), []))),
  ("}",          Scan.succeed ENDBLK),
  ("subgoal",    subgoal_parser),

  ("oops",       BAD_SOURCE),
  ("sorry",      Scan.succeed SORRY),

  ("also",       facts' (ALSO o flat)),
  ("finally",    facts' (FINALLY o rpair false o flat)),
  ("moreover",   Scan.succeed MOREOVER),
  ("ultimately", Scan.succeed (ULTIMATELY false)),

  ("print_trans_rules", ignore),
  ("help",       ignore),
  ("print_commands", ignore),
  ("print_options",  ignore),
  ("print_context",  ignore),
  ("print_theory",   ignore),
  ("print_definitions", ignore),
  ("print_syntax",      ignore),
  ("print_defn_rules",  ignore),
  ("print_abbrevs",     ignore),
  ("print_theorems",    ignore),
  ("print_locales",     ignore),
  ("print_classes",     ignore),
  ("print_locale",      ignore),
  ("print_interps",     ignore),
  ("print_attributes",  ignore),
  ("print_simpset",     ignore),
  ("print_rules",       ignore),
  ("print_methods",     ignore),
  ("print_antiquotations",    ignore),
  ("print_ML_antiquotations", ignore),
  ("locale_deps",             ignore),
  ("print_term_bindings",     ignore),
  ("print_facts",             ignore),
  ("print_cases",             ignore),
  ("print_statement",         ignore),
  ("thm",            ignore),
  ("prf",            ignore),
  ("full_prf",       ignore),
  ("prop",           ignore),
  ("term",           ignore),
  ("typ",            ignore),
  ("print_codesetup",ignore),
  ("print_context_tracing",    ignore),
  ("print_state",              ignore),
  ("welcome",                  ignore),
  ("text", ignore),
  ("txt" , ignore)
]

val threshold = Time.fromSeconds 1
val default_time = Time.fromSeconds 120
fun tac_time t =
  let val t' = if t <= threshold then threshold else t
   in Time.fromMilliseconds (Time.toMilliseconds t' * 3)
  end

val is_single_prf_mode =
  let fun chk [(_, DOT)] = true
        | chk [] = true
        | chk ((_, TACTIC (Method.Combinator (_, Method.Select_Goals 1, _), _, _)) :: L) = chk L
        | chk ((_, BRANCH_SUBGOALS _) :: _) = true
        | chk _ = false
   in chk
  end

exception ESORRY of exn

fun end_proof time glb loc s =
    ( if Proof.level s <= 2
      then Timeout.apply (the_default default_time time) glb s |> Proof.init
      else Timeout.apply (the_default default_time time) loc s )
    handle E as ERROR _ => raise ESORRY E
         | E as Timeout.TIMEOUT _ => raise ESORRY E

fun eval_single (CASE arg) s
      = Proof.case_cmd (restore_case arg) s
  | eval_single SORRY s
      = end_proof NONE (Proof.global_skip_proof false)
                       (Proof.local_skip_proof  false) s
  | eval_single (NOTE facts) s
      = Proof.note_thmss_cmd facts s
  | eval_single NEXT s
      = Proof.next_block s
  | eval_single (NOTATION (mode, args)) s
      = Proof.write_cmd mode args s
  | eval_single (INCLUDING names) s
      = Bundle.including_cmd (map (rpair Position.none) names) s
  | eval_single (INCLUDE names) s
      = Bundle.include_cmd (map (rpair Position.none) names) s
  | eval_single (LET arg) s
      = Proof.let_bind_cmd arg s
  | eval_single (DEFINE (a,b,c)) s = Proof.define_cmd a c b s
  | eval_single (UNFOLD facts) s
      = Proof.unfolding_cmd [facts] s
  | eval_single (TACTIC (tac, (using, _), time)) s
      = (  s
        |> not (null using) ? Proof.using_cmd [using]
        |> Timeout.apply (the_default default_time time) (
                Proof.apply (tac, Position.no_range)
             #> Seq.the_result "Tactic application fail")
        handle E as ERROR _ => raise ESORRY E
             | E as Timeout.TIMEOUT _ => raise ESORRY E)
  | eval_single DOT s
      = ( end_proof NONE Proof.global_immediate_proof Proof.local_immediate_proof s
        handle E as ERROR _ => raise ESORRY E )
  | eval_single DDOT s
      = end_proof NONE Proof.global_default_proof Proof.local_default_proof s
  | eval_single DONE s
      = end_proof NONE Proof.global_done_proof Proof.local_done_proof s
  | eval_single (APPLY_END arg) s
      = Proof.apply_end (arg, Position.no_range) s
     |> Seq.the_result "BUG"
  | eval_single (ISAR_BY (arg, time)) s =
    let val arg' = arg |> apfst (rpair Position.no_range)
                       |> apsnd (Option.map (rpair Position.no_range))
     in end_proof time (Proof.global_terminal_proof arg')
                       (Proof.local_terminal_proof arg') s
    end
  | eval_single ISAR_THEN s = Proof.chain s
  | eval_single (FROM facts) s
      = Proof.from_thmss_cmd [facts] s
  | eval_single (WITH facts) s
      = Proof.with_thmss_cmd [facts] s
  | eval_single (PREFER i) s  = Proof.prefer i s
  | eval_single (DEFER i) s   = Proof.defer i s
  | eval_single (USING facts) s
      = Proof.using_cmd [facts] s
(*  | eval_single (MCALCULATION _) _
      = error "Cannot eval MCALCULATION by a single step" *)
  | eval_single (ASSUME (a,b,c)) s = Proof.assume_cmd a b c s
  | eval_single (FIX vars) s = Proof.fix_cmd vars s

  | eval_single (PROOF (tac, _)) s
      = Proof.proof (SOME (tac, Position.no_range)) s
     |> Seq.the_result "BUG DAWHU"
  | eval_single (QED (tac, time)) s
      = end_proof time (Proof.global_qed (text_range tac, true))
                       (Proof.local_qed  (text_range tac, true)) s
  | eval_single (BRCBLK _) s
      = Proof.begin_block s
  | eval_single ENDBLK s
      = Proof.end_block s
  | eval_single (THUS ((a,b,c), _)) s
      = Proof.chain s
     |> Proof.show_cmd true NONE (K I) a b c false
     |> snd
  | eval_single (HENCE ((a,b,c), _)) s
      = Proof.chain s
     |> Proof.have_cmd true NONE (K I) a b c false
     |> snd
  | eval_single (SHOW ((a,b,c), _)) s
      = Proof.show_cmd true NONE (K I) a b c false s
     |> snd
  | eval_single (HAVE ((a,b,c), _)) s
      = Proof.have_cmd true NONE (K I) a b c false s
     |> snd
  | eval_single (SUBGOAL ((a,b,c), _)) s
      = Subgoal.subgoal_cmd a b c s
     |> snd
  | eval_single (ISAR_OBTAIN ((b, (c, d, e)), _)) s
      = Obtain.obtain_cmd Binding.empty b c d e false s
  | eval_single (ISAR_CONSIDER ((BB,arg), _)) s
      = consider_cmd arg true BB s
  | eval_single (OPEN_MODULE (expr, _)) s
      = Interpretation.interpret_cmd expr s
  | eval_single (MPROOF _) _ = error "BUG Cannot evaluate MPROOF by a single step"
  | eval_single (BRANCH_SUBGOALS _) _ = error "BUG Cannot evaluate BRANCH_SUBGOALS by a single step"
  | eval_single (ALSO rules) s =
      Calculation.also_cmd (case rules of [] => NONE | _ => SOME rules) false s
        |> Seq.the_result "BUG RHUI"
  | eval_single (FINALLY (rules, _)) s =
      Calculation.finally_cmd (case rules of [] => NONE | _ => SOME rules) false s
        |> Seq.the_result "BUG IL#R&"
  


fun mk_with_clause ctxt (wth, wthout) =
  let fun convert is_with (rf, atts) =
        let val name = case rf
                         of Facts.Named ((name,_),_) => name
                          | _ => ""
         in Attrib.eval_thms ctxt [(rf, atts)]
         |> map (fn th => (is_with, name, th))
        end
   in maps (convert true) wth
    @ maps (convert false) wthout
  end

fun eval_singlem (MCRUSH arg) s = Minilang.CRUSH (apsnd (mk_with_clause (Minilang.context_of s)) arg) s
  | eval_singlem (MSIMP arg ) s = Minilang.SIMP (mk_with_clause (Minilang.context_of s) arg) s
  | eval_singlem (MINTRO arg) s = uncurry Minilang.INTRO arg s
  | eval_singlem (MHAMMER (with_facts, without_facts)) s =
      Minilang.HAMMER { add = with_facts, del = without_facts, only = false } s
  | eval_singlem (MEND ((typ, vs, with_facts, without_facts), _)) s =
      (case typ of Minilang.T_END => Minilang.END | _ => Minilang.NXT vs)
           { add = with_facts, del = without_facts, only = false } s
  | eval_singlem (MCONSIDER (args, _)) s = Minilang.CONSIDER args s
  | eval_singlem (MUNFOLD facts) s =
      Minilang.UNFOLD (Attrib.eval_thms (Minilang.context_of s) facts) s
  | eval_singlem (MTACTIC (tac, (using,_), time)) s = Minilang.APPLY'' time using tac s
  | eval_singlem (MDEFINE (a,b,c)) s = Minilang.DEFINE'' a b c s
  | eval_singlem (MLET args) s = Minilang.LET'' args s
  | eval_singlem (MNOTATION args) s = uncurry Minilang.NOTATION'' args s
  | eval_singlem (MHAVE ((a,b,c), _)) s = Minilang.HAVE a b c s
  | eval_singlem (MRULE (rules, facts)  ) s = Minilang.RULE rules facts s
  | eval_singlem (MCHOOSE tm) s = Minilang.CHOOSE'' tm s
  | eval_singlem (MOPEN_MODULE (expr, _)) s = Minilang.OPEN_MODULE'' expr s
  | eval_singlem (MCFG_FACTS args) s = Minilang.CONFIG_FACTS'' args s
  | eval_singlem (MCFG_BUNDL args) s = Minilang.CONFIG_BUNDL'' args s
  | eval_singlem (MINDUCT args) s = Minilang.INDUCT'' args s
  | eval_singlem (MCASE args) s = Minilang.CASE_SPLIT'' args s
  | eval_singlem (MBRANCH_SUBGOALS _) _ = error "BUG MBRANCH_SUBGOALS cannot be evaluated by a single step"
  | eval_singlem (MINSERT facts) s =
      Minilang.APPLY'' NONE [] (Method.Basic (fn ctxt => Method.insert (Attrib.eval_thms ctxt facts))) s
(*  | eval_singlem (MCALC ((B,src,_),_)) s = s
      |> Minilang.HAVE [] [] [((B,[]),[(src,[])])]
      |> Minilang.APPLY'' NONE [] method_sorry
      |> Minilang.END {add = [], del = [], only = false}
  | eval_singlem (MSTEP ((facts,term),_)) s = s
      |> Minilang.STEP'' facts term *)


fun validate_tail [] = ()
  | validate_tail [(_, DOT)] = ()
  | validate_tail _ = error "BUG fq23hl"

fun set_time (TACTIC (a,b,t0)) = SOME (t0, fn t => TACTIC (a,b,SOME t))
  | set_time (ISAR_BY (a,t0))  = SOME (t0, fn t => ISAR_BY (a,SOME t))
  | set_time (QED (a,t0))      = SOME (t0, fn t => QED (a,SOME t))
  | set_time _ = NONE

fun DO s ast F L  =
  let val set = set_time ast
      val (ast', s') = case set
          of SOME (t0, setter) =>
              let val (t,s') = Timing.timing F s
                  val t = case t0 of SOME tt => tt
                                   | NONE => tac_time (#cpu t)
               in (setter t, s')
              end
           | NONE => (ast, F s)
   in eval s' L
   |> apsnd (prepend (SOME s, ast'))
  end
and BLK s body ast F L =
    let val (s', body') = eval (F s) body
     in eval s' L
     |> apsnd (prepend (SOME s, ast body'))
    end
and BLK' s body ast F G L =
    let val (s', body') = eval (F s) body
        val s'' = G s'
     in eval s'' L
     |> apsnd (prepend (SOME s, ast body'))
    end
and eval s [] = (s, [])
  | eval s ((_, ast as PROOF (tac, body)) :: L) =
      BLK s body (fn b => PROOF (tac, b)) (eval_single ast) L
  | eval s ((_, ast as BRCBLK ((BB,data), body)) :: L) =
      BLK' s body (fn B => BRCBLK ((BB,data), B))
                  (eval_single ast)
                  (Proof.note_thmss_cmd [((BB,[]),[(Facts.Named (("this", Position.none), NONE), [])])])
                  L
  | eval s ((_, ast as THUS (arg, body)) :: L) =
      BLK s body (fn B => THUS (arg, B)) (eval_single ast) L
  | eval s ((_, ast as HENCE (arg, body)) :: L) =
      BLK s body (fn B => HENCE (arg, B)) (eval_single ast) L
  | eval s ((_, ast as SHOW (arg, body)) :: L) =
      BLK s body (fn B => SHOW (arg, B)) (eval_single ast) L
  | eval s ((_, ast as HAVE (arg, body)) :: L) =
      BLK s body (fn B => HAVE (arg, B)) (eval_single ast) L
  | eval s ((_, ast as SUBGOAL (arg, body)) :: L) =
      BLK s body (fn B => SUBGOAL (arg, B)) (eval_single ast) L
  | eval s ((_, ast as ISAR_OBTAIN (arg, body)) :: L) =
      BLK s body (fn B => ISAR_OBTAIN (arg, B)) (eval_single ast) L
  | eval s ((_, ast as ISAR_CONSIDER ((BB,arg), body)) :: L) =
      BLK s body (fn B => ISAR_CONSIDER ((BB,arg), B)) (eval_single ast) L

  | eval s ((_, ast as OPEN_MODULE (expr, body)) :: L) =
      BLK s body (fn B => OPEN_MODULE (expr, B)) (eval_single ast) L
  | eval s0 ((_, MPROOF (prelude, (_, ss as (a,b,c)), data, prf)) :: L) =
      let val (s, prelude') = eval (mproof s0) prelude
          val sxx = s
          val s = Proof.show_cmd true NONE (K I) a b c false s |> snd
          val (s, prf') = eval s prf
          val s = mqed s
       in eval s L
       |> apsnd (prepend (SOME s0, MPROOF (prelude', (SOME sxx, ss), data, prf')))
      end
  | eval s ((_, BRANCH_SUBGOALS bodies) :: L) =
      let val (bodies', s') = fold_map (fn body => fn s => swap (eval s body)) bodies s
       in validate_tail L
        ; eval s' L
       |> apsnd (prepend (SOME s, BRANCH_SUBGOALS bodies'))
      end
(*  | eval s ((_, MCALCULATION (B, goal, using)) :: L) =
      let val (s', _) = eval s [(NONE, HAVE (([],[],[((B,[]),[(goal,[])])]), [(NONE, SORRY)]))]
       in eval s' L
       |> apsnd (prepend (SOME s, MCALCULATION (B, goal, using)))
      end *)
  | eval s ((_, tac as TACTIC (m,u,t0)) :: L) =
     (let val (t,s') = Timing.timing (eval_single tac) s
          val t = case t0 of SOME tt => tt
                           | NONE => tac_time (#cpu t)
       in eval s' L
       |> apsnd (prepend (SOME s, TACTIC (m, u, SOME t)))
      end handle ESORRY E =>
        let val facts = collect_facts L
         in rescue (merge_facts2 [u, facts]) s L E
        end )
  | eval s ((_, x) :: L) =
      ( DO s x (eval_single x) L
       handle ESORRY E => rescue (collect_facts L) s L E)
and rescue (using, not_using) s L E =
  if is_single_prf_mode L
  then let val ctxt = Proof.context_of s
           val using' = filter (can (Attrib.eval_thms ctxt o single)) using
           val not_using' = filter (can (Attrib.eval_thms ctxt o single)) not_using
           val sorry = TACTIC (method_sorry, (using', not_using'), NONE)
           val s'  = eval_single sorry s
           val s'' = eval_single DOT s'
    in (s'', [(SOME s, sorry), (SOME s', DOT)])
   end
  else raise E

fun DO s ast F L  =
  let exception RESCUE of exn in
  let val s' = F s handle E as Minilang.OPR_FAIL (Minilang.PROOF_FAIL, _) => raise RESCUE E
   in evalm s' L
  end handle RESCUE E =>
        let val origin = (SOME s, ast) :: L
            val (w,wo) = collect_mfacts origin
            fun tail_end [(_, MEND ((ty,vs,_,_),_))] = (ty,vs)
              | tail_end (_ :: L) = tail_end L
              | tail_end _ = Exn.reraise E
            val (ty,vs) = tail_end origin
            val mast = MEND ((ty,vs,w,wo), NONE)
         in (eval_singlem mast s, [(SOME s, mast)])
            handle Minilang.OPR_FAIL (Minilang.PROOF_FAIL, err) =>
            let val mast = MEND ((ty,vs,w,wo), SOME err)
                val s' = s |> eval_singlem (MTACTIC (method_sorry, ([],[]), NONE))
                           |> eval_singlem mast
             in (s', [(SOME s, mast)])
            end
        end
   end  |> apsnd (prepend (SOME s, ast))
and BLK s body ast F L =
    let val (s', body') = evalm (F s) body
     in evalm s' L
     |> apsnd (prepend (SOME s, ast body'))
    end
and evalm s [] = (s, [])
  | evalm s ((_, ast as MCONSIDER (ss, body)) :: L) =
      BLK s body (fn B => MCONSIDER (ss, B)) (eval_singlem ast) L
  | evalm s ((_, ast as MHAVE (ss, body)) :: L) =
      BLK s body (fn B => MHAVE (ss, B)) (eval_singlem ast) L
(*  | evalm s ((_, ast as MSTEP (args, body)) :: L) =
      BLK s body (fn B => MSTEP (args, B)) (eval_singlem ast) L *)
  | evalm s ((_, ast as MOPEN_MODULE (ss, body)) :: L) =
      BLK s body (fn B => MOPEN_MODULE (ss, B)) (eval_singlem ast) L
(*  | evalm s ((_, ast as MCALC (args, body)) :: L) =
      BLK s body (fn B => MCALC (args, B)) (eval_singlem ast) L *)
  | evalm s ((_, MBRANCH_SUBGOALS bodies) :: L) =
      let val (bodies', s') = fold_map (fn body => fn s => swap (evalm s body)) bodies s
       in evalm s' L
       |> apsnd (prepend (SOME s', MBRANCH_SUBGOALS bodies'))
      end
  | evalm s ((_, ast as MEND ((ty,vs,w,wo), _)) :: L) =
      let val _ = if null L then () else error "BUG evalm L not nil"
          val store = SH_prfs ()
          val _ = store := []
          val (s', w', wo', err) =
              let val (s', err) = (eval_singlem ast s, NONE)
                  val w'wo' = map facts_in_SH_return (!store)
                  val w'  = foldl1' (merge fact_eq) (map fst w'wo')
                  val wo' = foldl1' (merge fact_eq) (wo :: map snd w'wo')
               in (s', w', wo', err)
              end handle Minilang.OPR_FAIL (Minilang.PROOF_FAIL, err) =>
                    let val s' = s |> eval_singlem (MTACTIC (method_sorry, ([],[]), NONE))
                                   |> eval_singlem ast
                     in (s', w, wo, SOME err)
                    end
          val _ = store := []
          val ast' = MEND ((ty,vs,w',wo), err)
       in (s', [(SOME s, ast')])
      end
  | evalm s ((_, x) :: L) = DO s x (eval_singlem x) L



fun validate s msg ast =
  let val (rets, ast') = eval s ast
   in ast'
   (* if Proof.is_notepad rets orelse Proof.goal_finished rets
      then ast' else error msg *)
  end




end

fun print_mast print_response =
  let fun response' i (s, mast) =
        let val _ = fetch_items ()
            val ctxt = Minilang.context_of (the s)
            val _ = try (eval_singlem mast) (the s)
            val ((vs, hs), goals) = fetch_items ()
            val vs' = if null vs then []
                      else indent_of i :: "(*fixes variables "
                        :: implode_with' " and " (
                              map (fn (v,T) => [v, " :: ", quote_space (pretty_ty ctxt T)]) vs) [" *)"]
            val string_of = single o quote_space o trim_markup o Syntax.string_of_term ctxt
            val hs' = if null hs then []
                      else indent_of i :: "(*introduces facts "
                        :: implode_with' " and " (
                              map (fn (v,T) => v :: ": " ::
                                      implode_with " " (map string_of T)) hs) [" *)"]
            val gs' = case goals of NONE => []
                         | SOME [] => ["(*no goal remains!*)"]
                         | SOME goals =>
                           indent_of i :: "(*goal: "
                        :: implode_with' " and " (map string_of goals) [" *)"]
         in maps (fn [] => [] | L => L @ ["\n"]) [vs', hs', gs']
        end
        val response = if print_response then response' else K (K [])
      fun print _ _ [] = []
        | print i k ((x as (_, MCRUSH (mvars, (wth, wthout)))) :: L) =
              indent_of i :: "CRUSH"
           :: print_mvars mvars
            @ print_with " WITH " wth
            @ print_with " WITHOUT " wthout
            @ newline x i k L
        | print i k ((x as (_, MSIMP (wth, wthout))) :: L) =
              indent_of i :: "SIMP"
           :: print_with " WITH " wth
            @ print_with " WITHOUT " wthout
            @ newline x i k L
        | print i k ((x as (_, MINTRO (m,vars))) :: L) =
              indent_of i
           :: (case m of Minilang.ALL_SUBGOALS => "INTRO_ALL"
                      | Minilang.SINGLE_GOAL  => "INTRO")
           :: print_mvars vars
            @ newline x i k L
        | print i k ((x as (_, MHAMMER (wth, wthout))) :: L) =
              indent_of i :: "HAMMER"
           :: print_with " WITH " wth
            @ print_with " WITHOUT " wthout
            @ newline x i k L
        | print i k ((x as (_, MEND ((typ, vs, wth, wthout), _))) :: L) =
              indent_of k
           :: (case typ of Minilang.T_END => "END" | _ => "NEXT")
           :: print_mvars vs
            @ print_with " WITH " wth
            @ print_with " WITHOUT " wthout
            @ newline x i k L
        | print i k ((x as (_, MCONSIDER (branches,body))) :: L) =
              indent_of i
           :: "CONSIDER "
           :: implode_with " | " (
                map (fn ([],ss) => print_structured_statement ss
                      | (vs,ss) => print_vars vs
                                 @ " where "
                                :: print_structured_statement ss
                    ) branches)
            @ newline x (i+1) i body
            @ print i k L
        | print i k ((x as (_, MUNFOLD facts)) :: L) =
              indent_of i
           :: "UNFOLD "
           :: print_facts facts
            @ newline x i k L
        | print i k ((x as (_, MTACTIC (tac, (using,_), _))) :: L) =
              indent_of i
           :: "APPLY ("
           :: print_method tac
            @ ")"
           :: (if null using then [] else " WITH " :: print_facts using)
            @ newline x i k L
        | print i k ((x as (_, MDEFINE (vs, astmt, fixes))) :: L) =
              indent_of i
           :: "DEFINE "
           :: print_vars vs
            @ " where " :: print_attr_statements astmt
            @ print_for fixes
            @ newline x i k L
        | print i k ((x as (_, MLET args)) :: L) =
              indent_of i
           :: "LET "
           :: implode_with " and " (map (fn (vs,tm) =>
                implode_with " " (map (single o trim_markup) vs) @ (" = " :: print_term tm)
              ) args)
            @ newline x i k L
        | print i k ((x as (_, MHAVE (ss, body))) :: L) =
              indent_of i
           :: "HAVE "
           :: print_structured_statement' ss
            @ newline x (i+1) i body
            @ print i k L
        | print i k ((x as (_, MNOTATION (mode, xx))) :: L) =
              indent_of i
           :: "NOTATION "
           :: (if mode = Syntax.mode_default then []
                         else case mode
                           of ("", false)   => ["output"]
                            | (name, false) => [name, " output"]
                            | (name, _ )    => [name] )
              @ implode_with " and " (map (fn (tm,synt) =>
                    print_term tm @ " (" :: print_mixfix synt @ [")"] ) xx)
            @ newline x i k L
        | print i k ((x as (_, MRULE (rules, wth))) :: L) =
              indent_of i
           :: "RULE "
           :: print_facts rules
            @ print_with " WITH " wth
            @ newline x i k L
        | print i k ((x as (_, MCHOOSE terms)) :: L) =
              indent_of i
           :: "CHOOSE "
           :: implode_with " and " (map (fn (term, vs) =>
                quote term :: print_vars vs
              ) terms)
            @ newline x i k L
        | print i k ((x as (_, MOPEN_MODULE (exprs, body))) :: L) =
              indent_of i :: "OPEN_MODULE "
           :: print_locale_expr exprs
            @ newline x (i+1) i body
            @ print i k L
        | print i k ((x as (_, MCFG_FACTS notes)) :: L) =
              indent_of i
           :: "CONFIG "
           :: implode_with " and " (
                map (fn (B,facts) => print_attrbind B @ " = " :: print_facts facts) notes)
            @ newline x i k L
        | print i k ((x as (_, MCFG_BUNDL bundls)) :: L) =
              indent_of i
           :: "CONFIG "
           :: implode_with " " (map single bundls)
            @ newline x i k L
        | print i k ((x as (_, MBRANCH_SUBGOALS bodies)) :: L) =
            let fun maps [] = []
                  | maps [body] = print (i+1) k body
                  | maps (body :: bodies) = print (i+1) i body @ maps bodies
                val N = length bodies
             in (if !print_comments andalso N >= 1
                 then [indent_of i, "(*generates ", string_of_int N, " subgoals*)\n"]
                 else [] )
              @ maps bodies
              @ print i k L
            end
        | print i k ((x as (_, MINDUCT (toks, vs, using) )) :: L) =
              indent_of i :: "INDUCT "
           :: print_toks toks
            @ print_mvars vs
            @ print_with " WITH " using
            @ newline x i k L
        | print i k ((x as (_, MCASE (toks, vs, using))) :: L) =
              indent_of i :: "CASE_SPLIT "
           :: print_toks toks
            @ print_mvars vs
            @ print_with " WITH " using
            @ newline x i k L
        | print i k ((x as (_, MINSERT facts)) :: L) =
              indent_of i :: "APPLY (insert "
           :: print_facts facts
            @ ")"
           :: newline x i k L
(*        | print i k ((_, MCALC ((B, goal, _), body)) :: L) =
              indent_of i :: "HAVE " :: quote_space (Binding.name_of B) :: ": " :: print_term goal
            @ " TACTIC (msorry)"
           :: newline (i+1) i body @ print i k L
        | print i k ((_, MSTEP ((rules, term), body)) :: L) =
              indent_of i :: "STEP "
           :: (if null rules then [] else "(" :: print_facts rules @ [") "])
            @ print_term term
            @ newline (i+1) i body @ print i k L *)
      and newline x i k L =
         (* (case L
            of [(_, MEND  _)] => " " :: print i 0 L
             | _ => *) "\n" :: response i x @ print i k L (* ) *)
   in print 0 0
  end
      
val print_mast = String.concat oo print_mast

fun validatem ctxt0 s ast =
  let val (rets, ast') = evalm s ast
   in Minilang.conclude ctxt0 rets
    ; ast'
  end

datatype blk_behv = OPEN_BLK

val initial_state = Thread_Data.var ()

val parse_isar : Toplevel.state * Token.src list -> ast' =
  let fun chk_end (ret, []) = ret
        | chk_end (ret, [eof]) =
            if Token.is_eof eof then ret else raise Parse_Fail [[eof]]
        | chk_end (_, src) = raise Parse_Fail [src]

      fun parse (_, []) = raise Parse_Fail []
        | parse (s, src::srcs) =
        let val (name,_) = Token.name_of_src src
            val parser0 = case Symtab.lookup initial_parsers name
                            of SOME parser => parser
                             | NONE => raise Unsupported name
            val tr = Outer_Syntax.parse_span (Toplevel.theory_of s) (fn _ => error "BUG") src
            val s' = Toplevel.command_exception false tr s

            fun parser toks =
              let val (ast, toks) = parser0 toks
               in case set_time ast
               of NONE => (ast,toks)
                | SOME (_, set) => (set (tac_time (Toplevel.timing_of tr)),toks)
              end

            fun BLK F =
              let val (ast, s_srcs'') = parse (s', srcs)
               in parse s_srcs'' |> apfst (fn L => F ast :: L)
              end

         in case chk_end ( parser (tl src @ [Token.eof])
                        |> apfst (pair (SOME (Toplevel.proof_of s))))
         of ast as (_, DONE) => ([ast], (s', srcs))
          | ast as (_, DDOT) => ([ast], (s', srcs))
          | ast as (_, DOT)  => ([ast], (s', srcs))
          | ast as (_, QED _) => ([ast], (s', srcs))
          | ast as (_, ENDBLK) => ([ast], (s', srcs))
          | ast as (_, ISAR_BY _) => ([ast], (s', srcs))
          | ast as (_, APPLY_END _) => ([ast], (s', srcs))
          | (ctxt, HAVE  (smt, _)) => BLK (fn ast => (ctxt, HAVE  (smt, ast)))
          | (ctxt, THUS  (smt, _)) => BLK (fn ast => (ctxt, THUS  (smt, ast)))
          | (ctxt, HENCE (smt, _)) => BLK (fn ast => (ctxt, HENCE (smt, ast)))
          | (ctxt, SHOW  (smt, _)) => BLK (fn ast => (ctxt, SHOW  (smt, ast)))
          | (ctxt, SUBGOAL (smt, _)) => BLK (fn ast => (ctxt, SUBGOAL (smt, ast)))
          | (ctxt, ISAR_CONSIDER (arg, _)) => BLK (fn ast => (ctxt, ISAR_CONSIDER (arg, ast)))
          | (ctxt, ISAR_OBTAIN (arg, _)) => BLK (fn ast => (ctxt, ISAR_OBTAIN (arg, ast)))
          | (ctxt, OPEN_MODULE (expr, _)) => BLK (fn ast => (ctxt, OPEN_MODULE (expr, ast)))
          | (ctxt, PROOF (txt, _)) =>
              let val (ast, s_srcs'') = parse (s', srcs)
                  fun chk [] = raise Unsupported "proof is not ended by `qed`"
                    | chk [(_, QED _)] = ()
                    | chk (_ :: L) = chk L
               in chk ast
                ; ([(ctxt, PROOF (txt, ast))], s_srcs'')
              end
          | (ctxt, BRCBLK (data, _)) =>
              BLK (fn ast =>
                let fun chk [] = raise Unsupported "`{` is not ended by `}`"
                      | chk [(_, ENDBLK)] = ()
                      | chk (_ :: L) = chk L
                 in chk ast
                  ; (ctxt, BRCBLK (data, ast))
                end)
          | other => parse (s', srcs) |> apfst (fn L => other :: L)
        end
      handle IGNORE => parse (s, srcs)
   in parse
   #> (fn (ret, (_, [])) => ret
        | (_, (_, toks)) => raise Parse_Fail toks)
  end

val parse_isar_no_state : Token.src list -> ast' =
  let fun chk_end (ret, []) = ret
        | chk_end (ret, [eof]) =
            if Token.is_eof eof then ret else raise Parse_Fail [[eof]]
        | chk_end (_, src) = raise Parse_Fail [src]

      fun parse [] = raise Parse_Fail []
        | parse (src::srcs) =
        let val (name,_) = Token.name_of_src src
            val parser = case Symtab.lookup initial_parsers name
                           of SOME parser => parser
                            | NONE => raise Unsupported name

            fun BLK F =
              let val (ast, s_srcs'') = parse srcs
               in parse s_srcs'' |> apfst (fn L => F ast :: L)
              end

         in case chk_end ( parser (tl src @ [Token.eof])
                        |> apfst (pair NONE) )
         of ast as (_, DONE) => ([ast], srcs)
          | ast as (_, DDOT) => ([ast], srcs)
          | ast as (_, DOT)  => ([ast], srcs)
          | ast as (_, QED _) => ([ast], srcs)
          | ast as (_, ENDBLK) => ([ast], srcs)
          | ast as (_, ISAR_BY _) => ([ast], srcs)
          | ast as (_, APPLY_END _) => ([ast], srcs)
          | (ctxt, HAVE  (smt, _)) => BLK (fn ast => (ctxt, HAVE  (smt, ast)))
          | (ctxt, THUS  (smt, _)) => BLK (fn ast => (ctxt, THUS  (smt, ast)))
          | (ctxt, HENCE (smt, _)) => BLK (fn ast => (ctxt, HENCE (smt, ast)))
          | (ctxt, SHOW  (smt, _)) => BLK (fn ast => (ctxt, SHOW  (smt, ast)))
          | (ctxt, SUBGOAL (smt, _)) => BLK (fn ast => (ctxt, SUBGOAL (smt, ast)))
          | (ctxt, ISAR_CONSIDER (arg, _)) => BLK (fn ast => (ctxt, ISAR_CONSIDER (arg, ast)))
          | (ctxt, ISAR_OBTAIN (arg, _)) => BLK (fn ast => (ctxt, ISAR_OBTAIN (arg, ast)))
          | (ctxt, OPEN_MODULE (expr, _)) => BLK (fn ast => (ctxt, OPEN_MODULE (expr, ast)))
          | (ctxt, PROOF (txt, _)) =>
              let val (ast, s_srcs'') = parse srcs
                  fun chk [] = raise Unsupported "proof is not ended by `qed`"
                    | chk [(_, QED _)] = ()
                    | chk (_ :: L) = chk L
               in chk ast
                ; ([(ctxt, PROOF (txt, ast))], s_srcs'')
              end
          | (ctxt, BRCBLK (data, _)) =>
              BLK (fn ast =>
                let fun chk [] = raise Unsupported "`{` is not ended by `}`"
                      | chk [(_, ENDBLK)] = ()
                      | chk (_ :: L) = chk L
                 in chk ast
                  ; (ctxt, BRCBLK (data, ast))
                end)
          | other => parse srcs |> apfst (fn L => other :: L)
        end
   in parse
   #> (fn (ret, []) => ret
        | (_, toks) => raise Parse_Fail toks)
  end


(** Pass I - Preliminary Syntax Pass **)

(*
fun assign_fact_name ast =
  let val i = Unsynchronized.ref 0
      fun incr () = let val ret = !i in i := ret + 1; ret end
      fun new_name () = "anonym_" ^ (string_of_int (incr ()))
      fun new_binding () = Binding.name (new_name ())
      fun name_binding b = if Binding.is_empty b then new_binding () else b
      (* fun name_bstring b = if b = "" then new_name () else b *)
      val name_attr_stmt = map (apfst (apfst name_binding))
      fun name_strstmt (vs,asm,show) = (vs, asm, name_attr_stmt show)
   in linear_pass (
        fn (s, ASSUME args)::L => (s, ASSUME (name_strstmt args))::L
         | (s, THUS  args)::L => (s, THUS  (apfst name_strstmt args))::L
         | (s, HENCE args)::L => (s, HENCE (apfst name_strstmt args))::L
         | (s, SHOW  args)::L => (s, SHOW  (apfst name_strstmt args))::L
         | (s, CASE  args)::L => (s, CASE  (apfst (apfst name_binding) args))::L
         | (s, ISAR_OBTAIN args)::L =>
                (s, ISAR_OBTAIN (apfst ( apfst (apfst name_binding)
                                      #> apsnd name_strstmt ) args))::L
         | (s, ISAR_CONSIDER args)::L =>
                (s, ISAR_CONSIDER (apfst (map (apfst name_binding)) args))::L
         | (s, CONSIDER args) :: L =>
                (s, CONSIDER (apsnd name_strstmt args)) :: L
         | (s, DEFINE (vs, astmt, fixes)) :: L =>
                (s, DEFINE (vs, name_attr_stmt astmt, fixes)) :: L 
         | (s, HAVE args) :: L =>
                (s, HAVE (apfst name_strstmt args)) :: L
         | (s, NOTE args) :: L =>
                (s, NOTE (map (apfst (apfst name_binding)) args)) :: L
         | oth => oth
        ) ast
  end
*)


(* pass cases *)

fun vars_inside ast = let
      val cat = fold Name.declare
      fun add_vs (vs : var list) L = cat (map (Binding.name_of o #1) vs) L
      fun add_ss ss L = add_vs (#1 ss) L
   in linear_fold (
      fn (_, FIX vs) => add_vs vs
       | (_, ASSUME ss) => add_ss ss
       | (_, HAVE (ss, _)) => add_ss ss
       | (_, THUS (ss, _)) => add_ss ss
       | (_, HENCE (ss, _)) => add_ss ss
       | (_, SHOW (ss, _)) => add_ss ss
       | (_, CASE (_, (_, vs))) => cat (map_filter I vs)
       | (_, ISAR_OBTAIN ((vs, ss), _)) => add_ss ss #> add_vs vs
       | (_, ISAR_CONSIDER ((_, ks), _)) => add_vs (maps (fst o snd) ks)
       | (_, SUBGOAL ((_, _, (_,ks)), _)) => cat (map_filter fst ks)
       | (_, DEFINE (vs, _, _)) => add_vs vs
       | (_, MPROOF (_, _, SOME (vs,_,k), _)) =>
          cat (map_filter (fn VI_Fix x => SOME x | _ => NONE) vs) #>
          cat (case k of SOME (_, (_, vs)) => map_filter I vs | _ => [])
       | _ => I
    ) ast Name.context
  end

val pad_vars_in_case = linear_pass NONE (
  fn (s0, CASE (b, (name, vs))) :: L =>
     let val ctxt = Proof.context_of (the s0)
         val Rule_Cases.Case {fixes=fixes0,...} =
                Proof_Context.check_case ctxt true (name, Position.none)
                                              (map (Option.map Binding.name) vs)
         val fixes = filter_out (fn (B,_) => Binding.name_of B = "thesis") fixes0
         val nctxt = vars_inside L
         fun unsuffix s =
            let val i = Unsynchronized.ref (size s)
             in while !i > 0 andalso String.sub (s, !i - 1) = #"_" do i := !i - 1
              ; if !i <> size s
                then String.substring (s, 0, !i)
                else s
            end
         fun pad _ [] [] = []
           | pad nctxt ((B,_) :: fixes) [] =
              let val (name', nctxt') = Name.variant (unsuffix (Binding.name_of B)) nctxt
               in SOME name' :: pad nctxt' fixes []
              end
           | pad nctxt ((B,_) :: fixes) (NONE :: L) =
              let val (name', nctxt') = Name.variant (unsuffix (Binding.name_of B)) nctxt
               in SOME name' :: pad nctxt' fixes L
              end
           | pad nctxt (_ :: fixes) (SOME name :: L) =
              if exists (fn SOME b' => b' = name | _ => false) L
              then let val (name', nctxt') = Name.variant name nctxt
                    in SOME name' :: pad nctxt' fixes L
                   end
              else SOME name :: pad nctxt fixes L

         val vs' = pad nctxt fixes vs
      in (s0, CASE (b, (name, vs'))) :: L
     end
   | L => L
)

(* Assign Anonymous Facts with Names *)

val counter_store = Thread_Data.var ()

fun counter () =
  let val cnt = (case Thread_Data.get counter_store
                   of SOME rf => rf
                    | NONE => let
                           val rf = Unsynchronized.ref 0
                        in Thread_Data.put counter_store (SOME rf)
                         ; rf
                       end )
   in fn () =>
        let val ret = !cnt
         in cnt := ret + 1
          ; ret
        end
  end

fun assign_factname ast =
  let val cnt = counter ()
      fun mkB () = Binding.name ("fact" ^ string_of_int (cnt ()))
      fun mapB B = if Binding.is_empty B then mkB () else B
      val mapAS = map (apfst (apfst mapB))
      fun mapSS  (v,a,s) = (v, a, mapAS s)
      fun mapSS' (v,a,s) = (v, mapAS a, mapAS s)
   in linear_pass NONE (
     fn (s, HAVE (st, body)) :: L =>
        (s, HAVE (mapSS' st, body)) :: L
      | (s, ASSUME st) :: L =>
        (s, ASSUME (mapSS st)) :: L
      | (s, THUS (st, body)) :: L =>
        (s, THUS (mapSS' st, body)) :: L
      | (s, HENCE (st, body)) :: L =>
        (s, HENCE (mapSS' st, body)) :: L
      | (s, SHOW (st, body)) :: L =>
        (s, SHOW (mapSS' st, body)) :: L
      | (s, CASE ((B,atts), (name, args))) :: L =>
        let val B' = if Binding.is_empty B
                     then Binding.name (variant_factname (Proof.context_of (the s)) name)
                     else B
         in (s, CASE ((B',atts), (name, args))) :: L
        end
      | (s, ISAR_OBTAIN ((vs,st), body)) :: L =>
        (s, ISAR_OBTAIN ((vs, mapSS st), body)) :: L
      | (s, ISAR_CONSIDER ((B,obt), body)) :: L =>
        let val pass_obt = map_index (fn (i,(B,params)) =>
                  if Binding.is_empty B then (Binding.name (string_of_int (i+1)), params)
                                        else (B,params))
         in (s, ISAR_CONSIDER ((mapB B, pass_obt obt), body)) :: L
        end
      | (s, ast as DEFINE (vs, st, fx)) :: L =>
        let fun pass [] = []
              | pass ((x as ((B,atts), props)) :: clauses) =
                  if Binding.is_empty B
                  then (case props
                    of [(src, _)] =>
                      let val ctxt = Proof.context_of (eval_single ast (the s))
                          fun name_of (Free (N, _)) = Thm.def_name (Variable.revert_fixed ctxt N)
                            | name_of _ = error "BUG malformed definition"
                          fun LHS_of (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = LHS_of X
                            | LHS_of (Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _, X)) = LHS_of X
                            | LHS_of (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = LHS_of X
                            | LHS_of (Const(\<^const_name>\<open>Pure.eq\<close>, _) $ X $ _) = name_of (Term.head_of X)
                            | LHS_of (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ X $ _) = name_of (Term.head_of X)
                            | LHS_of X = raise TERM ("BUG malformed definition", [X])
                          val prop = Syntax.read_prop ctxt src
                       in ((Binding.name (LHS_of prop), atts), props) :: pass clauses
                      end
                     | _ => ((mapB B, atts), props) :: pass clauses)
                  else x :: pass clauses
         in (s, DEFINE (vs, pass st, fx)) :: L
        end
      | (s, NOTE notes) :: L =>
        (s, NOTE (map (apfst (apfst mapB)) notes)) :: L
(*      | (s, MCALCULATION (B, src, using)) :: L =>
        (s, MCALCULATION (mapB B, src, using)) :: L *)
      | (s, BRCBLK ((B,data),body)) :: L =>
        (s, BRCBLK ((mapB B,data),body)) :: L
      | L => L
    ) ast
  end

local
fun names_of_AS x = map (Binding.name_of o fst o fst) x
fun names_of_st x = names_of_AS (#3 x)
fun assms_of_st x = names_of_AS (#2 x)
in

fun parse_this [] = error "BUG Fail to parse the `this` fact"
  | parse_this ([]::R) = parse_this R
  | parse_this (((_, HAVE (st, _))::_)::_) = names_of_st st
  | parse_this (((_, ASSUME st)::_)::_) = names_of_st st
  | parse_this (((_, THUS (st, _))::_)::_) = names_of_st st
  | parse_this (((_, HENCE (st, _))::_)::_) = names_of_st st
  | parse_this (((_, SHOW (st, _))::_)::_) = names_of_st st
  | parse_this (((_, ISAR_OBTAIN ((_,st), _))::_)::_) = names_of_st st
  | parse_this (((_, ISAR_CONSIDER ((B,_), _))::_)::_) = [Binding.name_of B]
  | parse_this (((_, DEFINE (_, st, _))::_)::_) = names_of_AS st
  | parse_this (((_, NOTE notes)::_)::_) = map (Binding.name_of o fst o fst) notes
  | parse_this (((_, CASE ((B,_),(B',_)))::_)::_) =
      if Binding.is_empty B then [B'] else [Binding.name_of B]
(*  | parse_this (((_, MCALCULATION (B,_,_))::_)::_) = [Binding.name_of B] *)
  | parse_this (((_, BRCBLK ((B,_),_)) :: _) :: _) = [Binding.name_of B]
  | parse_this ((_::R)::RR) = parse_this (R::RR)

fun parse_that [] =
      let val ctxt0 = the (Thread_Data.get initial_state)
                   |> Proof.context_of
       in if can (Proof_Context.get_thms ctxt0) "that"
          then ["that"]
          else error "BUG cannot parse the `that` fact"
      end
  | parse_that (HAVE (st, _) :: R) = parse_that' (assms_of_st st) R
  | parse_that (THUS (st, _) :: R) = parse_that' (assms_of_st st) R
  | parse_that (HENCE(st, _) :: R) = parse_that' (assms_of_st st) R
  | parse_that (SHOW (st, _) :: R) = parse_that' (assms_of_st st) R
  | parse_that (_::R) = parse_that R
and parse_that' ret L = if null ret then parse_that L else ret

fun parse_this' ctxt history =
  map (fn name =>
    let val ths = Proof_Context.get_thms ctxt name
        val len = length ths
     in (name, 0, len, len)
    end)
  (parse_this history)

fun parse_that' ctxt history =
  map (fn name =>
    let val ths = Proof_Context.get_thms ctxt name
        val len = length ths
     in (name, 0, len, len)
    end)
  (parse_that history)


end

fun fact_this history =
  let val these = parse_this history
   in map (fn this => ((Facts.Named ((this, Position.none), NONE)), []) ) these
  end

(* Unfolding Syntax Sugars *)

(*eliminates FROM, WITH, ISAR_THEN \<mapsto> using ... 
  eliminates HENCE, THUS \<mapsto> using this ...
  merges USING USING
  USING HAVE \<mapsto> HAVE USING
  exhaustively*)
val norm_FROM_WITH_USING = linear_pass' NONE (fn history => recursive (
  let fun restore_using L =
            the (fst (hd L)) |> Proof.using_facts [] |> SOME
   in fn (s, WITH facts) :: L =>
         (s, USING (facts @ fact_this history)) :: L
       | (s, FROM facts) :: L =>
         (s, USING facts) :: L
       | (s, ISAR_THEN) :: L =>
         (s, USING (fact_this history)) :: L
       | (s, HENCE args) :: L =>
         (s, USING (fact_this history)) :: (Option.map Proof.chain s, HAVE args) :: L
       | (s, THUS args) :: L =>
         (s, USING (fact_this history)) :: (Option.map Proof.chain s, SHOW args) :: L
       | (s, USING facts1) :: (_, USING facts2) :: L =>
         (s, USING (merge (fact'_eq (Proof.context_of (the s))) (facts2, facts1))) :: L
       | (s, USING facts) :: (_, HAVE (stmt, Prf)) :: L =>
         (s, HAVE (stmt, (restore_using Prf, USING facts) :: Prf)) :: L
       | (s, USING facts) :: (_, SHOW (stmt, Prf)) :: L =>
         (s, SHOW (stmt, (restore_using Prf, USING facts) :: Prf)) :: L
       | (s, USING facts) :: (_, ISAR_OBTAIN (stmt, Prf)) :: L =>
         (s, ISAR_OBTAIN (stmt, (restore_using Prf, USING facts) :: Prf)) :: L
       | (s, USING facts) :: (_, ISAR_CONSIDER (stmt, Prf)) :: L =>
         (s, ISAR_CONSIDER (stmt, (restore_using Prf, USING facts) :: Prf)) :: L
       | (s, USING facts) :: (_, OPEN_MODULE (stmt, Prf)) :: L =>
         (s, OPEN_MODULE (stmt, (restore_using Prf, USING facts) :: Prf)) :: L
       | (s, USING facts) :: (s2, DOT) :: L =>
         (s, USING facts) :: (s2, TACTIC (method_this, ([], []), NONE)) :: (NONE, DOT) :: L
       | (s, us as USING _) :: (_, incl as INCLUDING _) :: L =>
         (s, incl) :: (Option.map (eval_single incl) s, us) :: L
       | (s, USING facts) :: (_, UNFOLD facts') :: L =>
          let val attr = tok_unfolded :: (maps tokenize_fact facts')
              val s' = Option.map (eval_single (UNFOLD facts')) s
           in (s , UNFOLD facts')
           :: (s', USING (map (apsnd (fn toks => toks @ [attr])) facts))
           :: L
          end
       | (s, USING facts) :: (_, SUBGOAL (stmt, Prf)) :: L =>
         (s, SUBGOAL (stmt, (restore_using Prf, USING facts) :: Prf)) :: L
  end))

(* Resolving \<open>this\<close> *)

(*requires full states*)
fun resolve_this ast =
  let val scope = Unsynchronized.ref []
   in elementwise_pass' (SOME scope) (fn history => fn (s, ast) =>
        let val ctxt = Proof.context_of (the s)
            val this = Lazy.lazy (fn () => SOME (parse_this' ctxt history))
            val that = Lazy.lazy (fn () => SOME (parse_that' ctxt (!scope)))
         in map_ast_fact (K (fn "this" => Lazy.force this
                              | "that" => Lazy.force that
                              | _ => NONE))
                         (s, ast)
        end ) ast
  end

(* Ensuring assumptions having no attributes *)

fun lets_of_statement (s : statement) =
      maps (maps (fn (_,[]) => []
                   | (tm,pats) => map (rpair tm o single) pats)) s
fun lets_of_attr_statement (s : attr_statement) =
      maps (maps (fn (_,[]) => []
                   | (tm,pats) => map (rpair tm o single) pats) o snd) s
fun lets_of_ss ((_, assms, shows) : structured_statement) =
      lets_of_statement assms @ lets_of_attr_statement shows


fun norm_assums ast =
  let val cnt = counter ()
      fun mkB () = Binding.name ("fact'" ^ string_of_int (cnt ()))
      fun mk_fact' B =
            let val name = Binding.name_of B
             in ((Facts.Named ((name, Position.none), NONE)), [])
            end
      val scope = Unsynchronized.ref []
   in linear_pass (SOME scope) (
     (fn origin as (s, ast as ASSUME st0) :: L =>
         (case !scope
            of (BRCBLK _) :: _ => origin
             | _ => let val s' = eval_single ast (the s)
                        val notes = map_filter (fn ((B,atts), _) =>
                                        if null atts
                                        then NONE
                                        else SOME ((mkB(),atts), [mk_fact' B]) ) (#3 st0)
                     in if null notes
                      then origin
                      else (s, ast) :: (SOME s', NOTE notes) :: L
                    end )
       | origin as (s, ast as CASE ((B,atts),_)) :: L =>
          if null atts
          then origin
          else let
              val s' = eval_single ast (the s)
              val notes = [((mkB(),atts), [mk_fact' B])]
           in (s, ast) :: (SOME s', NOTE notes) :: L
          end
       | L => L)
  #> (fn origin as (ast0 as (s, ASSUME st0)) :: L =>
          let val lets = lets_of_ss st0
           in if null lets
            then origin
            else let val ast = LET lets
                     val s' = Option.map (eval_single ast) s
              in ast0 :: (s', ast) :: L
             end
          end
       | L => L)
      ) ast
  end


(* Also & Finally *)

fun pass_also_finally astx = astx
|> linear_pass NONE (
      fn (s, ALSO _) :: L => (s, MOREOVER) :: L
       | (s, FINALLY _) :: L => (s, ULTIMATELY false) :: L
       | L => L
    )
|> segment_pass (
  let (* val count = counter ()
         fun mkB () = Binding.name ("fact" ^ string_of_int (count ())) *)
      fun pass _ _ _ [] = []
(*        | pass history alsos _
               ((x as (_, HAVE ((_,_,shows),_))) :: (_, ALSO rules) :: L) =
            let val facts' = map ( (fn s => Facts.Named ((s,Position.none),NONE))
                                 o Binding.name_of o fst o fst ) shows
             in x :: pass (x :: history) ((rules, facts') :: alsos) [] L
            end
         | pass history alsos _ (x :: (_, ALSO rules) :: L) =
            let val this0 = parse_this [x :: history]
                val this = map (fn s => Facts.Named ((s,Position.none),NONE)) this0
             in x :: pass (x :: history) ((rules, this) :: alsos) [] L
            end
         | pass history alsos _ (x :: (s, FINALLY (rules, false)) :: L) =
            pass history alsos [] (
                 x
              :: (s, ALSO rules)
              :: (Option.map (eval_single (ALSO rules)) s, FINALLY ([], true))
              :: L )
         | pass history alsos _ ((s, FINALLY (_, true)) :: L) =
            let val ctxt = Proof.context_of (the s)
                val term' = Proof_Context.get_thm ctxt "calculation"
                         |> Thm.prop_of
                val B = mkB()
                val x = (s, MCALCULATION (B, print_prop ctxt term', rev alsos))
                val (s', _) = eval (the s) [x]
                val fact = Facts.Named ((Binding.name_of B, Position.none), NONE)
             in x
             :: (SOME s', FROM [(fact,[])])
             :: pass (x :: history) [] [[fact]] L
            end *)
         | pass history alsos moreover ((x as (_, HAVE ((_,_,shows),_))) :: (s, MOREOVER) :: L) =
            if null alsos
            then let val facts' = map ( (fn s => Facts.Named ((s,Position.none),NONE))
                                 o Binding.name_of o fst o fst ) shows
             in x :: pass (x :: history) [] (facts' :: moreover) L
            end else pass history alsos [] (x :: (s, FINALLY ([], false)) :: (s, MOREOVER) :: L)
         | pass history alsos moreover (x :: (s, MOREOVER) :: L) =
            if null alsos
            then let val this0 = parse_this [x :: history]
                     val this = map (fn s => Facts.Named ((s,Position.none),NONE)) this0
             in x :: pass (x :: history) [] (this :: moreover) L
            end else pass history alsos [] (x :: (s, FINALLY ([], false)) :: (s, MOREOVER) :: L)
         | pass history alsos moreover (x :: (s, ULTIMATELY false) :: L) =
            pass history alsos moreover (x :: (s, MOREOVER) :: (s, ULTIMATELY true) :: L)
         | pass history _ moreover ((x as (s, ULTIMATELY true)) :: L) =
            (s, FROM (map (rpair []) (flat (rev moreover)))) :: pass (x :: history) [] [] L
         | pass history alsos moreover (x :: L) =
            x :: pass (x :: history) alsos moreover L
   in fn ast => pass [] [] [] ast
  end
)

(*
val pass_also_finally = segment_pass (
  let datatype step = ALSO_HAVE of (term' * term)
                                      * (Proof.state option * ast) list
                    | ALSO_NOTE of fact * term
      exception NOT_FOUND
      exception NONAPPLICATABLE
      val cvt_step =
        let fun pass (info, xassms)
                     ((s0, HAVE ((vs,assms,shows),body)) :: (_, ALSO) :: L) =
                  let val ((B,atts),show) =
                            (case shows of [(AB,[x])] => (AB,x)
                                         | _ => raise NONAPPLICATABLE)
                      val can_move =
                            not (exists_ast_fact' (fn name => Binding.name_of B = name) L) andalso
                            null atts andalso
                            forall (forall (null o snd)) assms
                      val ctxt = Proof.context_of (the s0)
                      val thy  = Proof_Context.theory_of ctxt
                      val (stmt, ctxt') = Proof_Context.read_statement vs assms (map snd shows) ctxt
                      val xassms' = fold (AList.update (Pattern.equiv thy))
                                         (flat (#assumes stmt) ~~ flat assms)
                                         xassms
                   in ()
                  end
         in ()
        end
   in I
  end
)
*)

(* Convert SUBGOAL to PROOF *)

fun strip_hhf tm =
  let fun strip Hs Vs (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ H $ X) = strip (H::Hs) Vs X
        | strip Hs Vs (Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (N, T, X)) = strip Hs ((N,T)::Vs) X
        | strip Hs Vs X = (rev Hs, rev Vs, X)
   in strip [] [] tm
  end

val rewrite_subgoal = linear_pass NONE (
  fn (s0, SUBGOAL ((a,b,c0), body)) :: L =>
    let val s = the s0
        val (_, vs, _) = strip_hhf (fst (Logic.dest_implies (Thm.prop_of (#goal (Proof.raw_goal s)))))
        val vs' = Variable.variant_frees (Proof.context_of s)
                                         (map_filter (fn (SOME name,_) => SOME (Free (name, dummyT))
                                                       | (NONE, _) => NONE) (snd c0)) vs
        fun merge_names [] [] = []
          | merge_names ((name, _) :: L) ((NONE, pos) :: L') = (SOME name, pos) :: merge_names L L'
          | merge_names (_ :: L) (x :: L') = x :: merge_names L L'
        val c = apsnd (fn vs0 =>
                  let val vs1 = take (length vs' - length vs0) vs'
                             |> map (fn (name, _) => (SOME name, Position.none))
                   in merge_names vs' (vs1 @ vs0)
                  end ) c0

        val (foc, s') = Subgoal.subgoal_cmd a b c s
        val ctxt' = Proof.context_of s'
        val fixes = map (fn (_,ctm) =>
                  let val name = case Thm.term_of ctm
                                   of Free (name0, _) => Variable.revert_fixed ctxt' name0
                                    | _ => error "BUG rewrite_subgoal 1"
                   in (Binding.name name, SOME (print_ty ctxt' (Thm.typ_of_cterm ctm)), NoSyn)
                  end ) (#params foc)
        val fix' = if null fixes then [] else [(NONE, FIX fixes)]

        val asms = map (fn ctm => (print_prop ctxt' (Thm.term_of ctm), [])) (#asms foc)
        val asm' = case b of NONE => []
                           | SOME b' => [(NONE, ASSUME ([], [], [(b', asms)]))]

        val show = ([], [], [(Binding.empty_atts, [(print_prop ctxt' (Thm.term_of (#concl foc)), [])])])
     in if Binding.is_empty_atts a then ()
        else raise Unsupported "SUBGOAL that binds its conclusion is not supported."
      ; (s0, MPROOF (fix' @ asm',
                     (NONE, show),
                     NONE,
                     body)
        ) :: L
    end
   | L => L
)

(** Pass II - Ensuring One Proof Block for One Goal **)

(* Normalize Tactics *)

fun is_no_tac_toks toks =
      let val s = String.concatWith " " (map Token.unparse toks)
       in s = "-" orelse s = "\"-\""
      end 
fun is_no_tac (Method.Source toks) = is_no_tac_toks toks
  | is_no_tac _ = false

fun clean_tac [] = []
  | clean_tac ((m as Method.Source toks) :: L) =
      if is_no_tac_toks toks then L else m :: clean_tac L
  | clean_tac (Method.Combinator (oi, Method.Then, tacs) :: L) =
      (case clean_tac tacs
         of [] => []
          | [t] => [t]
          | tacs => [Method.Combinator (oi, Method.Then, tacs)] )
      @ clean_tac L
  | clean_tac (Method.Combinator (oi, Method.Then_All_New, tacs) :: L) =
      let fun cleans [] = []
            | cleans (tac :: tacs) =
                (case clean_tac [tac]
                   of [] => []
                    | [tac'] => tac' :: cleans tacs)
       in case cleans tacs
       of [] => clean_tac L
        | tacs' => Method.Combinator (oi, Method.Then_All_New, tacs') :: L
      end
  | clean_tac (Method.Combinator (oi, Method.Orelse, tacs) :: L) =
      (case clean_tac tacs
         of [] => []
          | [t] => [t]
          | tacs => [Method.Combinator (oi, Method.Orelse, tacs)] )
      @ clean_tac L
  | clean_tac (Method.Combinator (oi, Method.Try, tacs) :: L) =
      (case clean_tac tacs
         of [] => []
          | tacs => [Method.Combinator (oi, Method.Try, tacs)] )
      @ clean_tac L
  | clean_tac (Method.Combinator (oi, Method.Repeat1, tacs) :: L) =
      (case clean_tac tacs
         of [] => []
          | tacs => [Method.Combinator (oi, Method.Repeat1, tacs)] )
      @ clean_tac L
  | clean_tac (Method.Combinator (oi, Method.Select_Goals i, tacs) :: L) =
      (case clean_tac tacs
         of [] => []
          | tacs => [Method.Combinator (oi, Method.Select_Goals i, tacs)] )
      @ clean_tac L
  | clean_tac (m :: L) = m :: clean_tac L

val clean_tac_pass = linear_pass NONE (
  fn (s, TACTIC (tac, using, time)) :: L =>
      (case clean_tac [tac]
         of []  => L
          | [t] => (s, TACTIC (t, using, time)) :: L
          | _   => error "BUG")
   | L => L
  )

val norm_prf1 = linear_pass NONE (
  fn org as (s, PROOF (tac, prf)) :: L =>
      if is_no_tac tac
      then org
      else (s, TACTIC (tac, ([],[]), NONE)) :: (Option.map (Proof.refine_singleton tac) s, PROOF (no_tac, prf)) :: L
   | (s, ISAR_BY ((tac, NONE), time)) :: L =>
        (s, TACTIC (tac, ([],[]), time))
     :: (Option.map (eval_single (TACTIC (tac, ([],[]), NONE))) s, DOT)
     :: L
   | (s, ISAR_BY ((tac, SOME tac'), time)) :: L =>
      let val s1 = Option.map (eval_single (TACTIC (tac, ([],[]),time))) s
          val s2 = Option.map (eval_single (TACTIC (tac',([],[]),time))) s1
       in (s, TACTIC (tac,([],[]),time)) :: (s1, TACTIC (tac',([],[]),time)) :: (s2, DOT) :: L
      end
   | (s, APPLY_END tac) :: L =>
        (s, TACTIC (tac,([],[]),NONE))
     :: (Option.map (eval_single (TACTIC (tac,([],[]),NONE))) s, DOT)
     :: L
   | (s, DONE) :: L =>
     (s, DOT) :: L
   | (s, DDOT) :: L =>
        (s, TACTIC (standard_tac,([],[]),NONE))
     :: (Option.map (eval_single (TACTIC (standard_tac,([],[]),NONE))) s, DOT)
     :: L
   | (s, UNFOLD facts) :: L =>
     let val toks = tok_unfold :: maps tokenize_fact facts
         val meth = Method.Source toks
      in if can (eval_single (TACTIC (meth, ([],[]), NONE))) (the s)
       then (s, TACTIC (meth,([],[]),NONE)) :: L
       else L
     end
   | L => L)
#> linear_pass NONE (recursive (
  fn (s, USING facts1) :: (_, USING facts2) :: L =>
     (s, USING (merge (fact'_eq (Proof.context_of (the s))) (facts2, facts1))) :: L
   | (s, USING facts) :: (_, TACTIC (tac, (using, not_using), _)) :: L =>
      (s, TACTIC (tac, (facts @ using, not_using), NONE)) :: L
   | (s, USING _) :: (_, PROOF prf) :: L =>
     (s, PROOF prf) :: L
   | (s, TACTIC (tac, (using, not_using), _)) :: L =>
      if is_no_tac tac
      then if null using
      then L
      else (s, TACTIC (Method.Source (tok_insert :: maps tokenize_fact using), ([],not_using), NONE)) :: L
      else raise Match
 (*  | (s, USING facts) :: (_, TACTIC (tac, using)) :: L =>
      let fun insert_tac (Method.Source toks) =
                let val facts = maps tokenize_fact' facts
                    val toks_str = String.concatWith " " ("\<open>" :: map Token.unparse toks @ ["\<close>"])
                    val tac' = Token.tokenize pure_keywords {strict = false}
                                    (Symbol_Pos.explode (toks_str, Position.none))
                 in Method.Source (tok_use :: facts @ tok_in :: tac')
                end
            | insert_tac (Method.Combinator (oi, Method.Then, tac::tacs)) =
                Method.Combinator (oi, Method.Then, insert_tac tac :: tacs)
            | insert_tac (Method.Combinator (oi, Method.Then_All_New, tac::tacs)) =
                Method.Combinator (oi, Method.Then_All_New, insert_tac tac :: tacs)
            | insert_tac (Method.Combinator (oi, Method.Orelse, tacs)) =
                Method.Combinator (oi, Method.Orelse, map insert_tac tacs)
            | insert_tac (Method.Combinator (oi, Method.Try, tacs)) =
                Method.Combinator (oi, Method.Try, map insert_tac tacs) (*FIX ME*)
            | insert_tac (Method.Combinator (oi, Method.Repeat1, tacs)) =
                Method.Combinator (oi, Method.Repeat1, map insert_tac tacs)
            | insert_tac (Method.Combinator (oi, Method.Select_Goals i, tacs)) =
                Method.Combinator (oi, Method.Select_Goals i, map insert_tac tacs)
            | insert_tac x = x
       in (s, TACTIC (insert_tac tac, using)) :: L
      end *)
))
#> clean_tac_pass

(* Duplicatable *)

fun tac_duplicatable (Method.Source toks) =
    ( case Token.unparse (hd toks)
        of "auto"         => true
         | "\"auto\""     => true
         | "simp"         => true
         | "\"simp\""     => true
         | "simp_all"     => true
         | "\"simp_all\"" => true
         | _              => false )
  | tac_duplicatable (Method.Combinator (_, Method.Then, tacs)) =
      forall tac_duplicatable tacs
  | tac_duplicatable (Method.Combinator (_, Method.Then_All_New, tacs)) =
      forall tac_duplicatable tacs
  | tac_duplicatable (Method.Combinator (_, Method.Orelse, tacs)) =
      exists tac_duplicatable tacs
  | tac_duplicatable (Method.Combinator (_, Method.Try, _)) = true
  | tac_duplicatable (Method.Combinator (_, Method.Repeat1, _)) = true
  | tac_duplicatable (Method.Combinator (_, Method.Select_Goals _, _)) = false
  | tac_duplicatable _ = false

fun prf_duplicatable [] = true
  | prf_duplicatable [(_,ISAR_BY ((t1, t2), _))] =
      tac_duplicatable t1 andalso (case t2 of SOME t => tac_duplicatable t | _ => true)
  | prf_duplicatable [(_,APPLY_END tac)] = tac_duplicatable tac
  | prf_duplicatable [(_,DONE)] = true
  | prf_duplicatable [(_,DDOT)] = true
  | prf_duplicatable [(_, DOT)] = true
  | prf_duplicatable ((_, TACTIC (tac,_,_)) :: L) = tac_duplicatable tac andalso prf_duplicatable L
  | prf_duplicatable _ = false


(* Separate Proofs for Respective Subgoals *)

(*
fun fold_map_filter _ [] y = ([], y)
  | fold_map_filter f (x :: xs) y =
      let
        val (x', y') = f x y;
        val (xs', y'') = fold_map_filter f xs y';
      in ((case x' of SOME xx => xx :: xs'
                    | NONE => xs'),
          y'')
     end *)

fun mk_branch_subgoals [goal] = goal
  | mk_branch_subgoals goals = [(NONE, BRANCH_SUBGOALS goals)]

fun chk_first_tac P (Method.Combinator (_, _, tacs)) = chk_first_tac P (hd tacs)
        | chk_first_tac P tac = P tac
fun is_ind tac = chk_first_tac (
                    fn (Method.Source (tok :: _)) => Token.content_of tok = "induct"
                     | _ => false ) tac
fun is_ind_opr ((_, TACTIC (tac,_,_)) :: _) = is_ind tac
  | is_ind_opr _ = false

fun init_grdprf use_raw s =
  new_oneshots (Thm.nprems_of (#goal (if use_raw then Proof.raw_goal s else Proof.goal s)))

fun conclude_grdprf tree =
  case get_oneshot' tree
    of NONE => error "BUG GRDTREE doesn't complete"
     | SOME (GRDTREE (prfs, [])) => prfs
     | SOME (GRDTREE (prfs, [child]))  => prfs @ conclude_grdprf child
     | SOME (GRDTREE (prfs, children)) => prfs @ [(NONE, BRANCH_SUBGOALS (map conclude_grdprf children))]

fun get_inductP ctxt (fact :: _) = map single (Induct.find_inductP ctxt (Thm.concl_of fact))
  | get_inductP _ _ = [];

fun is_conj_goal s =
  case Thm.prop_of (#goal (Proof.raw_goal s))
    of Const(\<^const_name>\<open>Pure.imp\<close>, _) $ (Const(\<^const_name>\<open>Pure.conjunction\<close>, _) $ _ $ _) $ _
         => true
     | _ => false

fun separate_tac time =
  let exception PRF_FAIL of (unit -> string)

      fun pass_tac (origin as Method.Source (tok::toks)) =
            (case Token.unparse tok
               of "simp_all" => Method.Source (mk_idt "simp" :: toks)
                | _ => origin)
        | pass_tac tac = tac

      fun pass_tac' s tac =
          let val tac' = pass_tac tac
              val normal = not (is_ind tac andalso is_conj_goal s)
           in if normal
            then tac_for_1 tac'
            else tac'
          end

      fun apply (using,_) tac s =
            \<^try>\<open>
            Timeout.apply (the_default default_time time) Seq.pull
                    (  s
                    |> not (null using) ? Proof.using_cmd [using]
                    |> Proof.apply (tac, Position.no_range))
               |> (fn NONE => raise PRF_FAIL (K "")
                    | SOME (Seq.Result s'', _) => s''
                    | SOME (Seq.Error err, _)  => raise PRF_FAIL err )
            catch Timeout.TIMEOUT _ => raise PRF_FAIL (fn _ => "Timeout")
                |  ERROR msg         => raise PRF_FAIL (fn _ => msg)
                | _ => raise PRF_FAIL (fn _ => "")\<close>
      fun apply1 using tac s = s
                   |> Proof.refine_primitive (K (Goal.protect 1))
                   |> apply using tac 
                   |> Proof.refine_primitive (K Goal.conclude)
      fun apply' using tac (leaves, s) =
        let val thy = Proof.theory_of s
            val st  = #goal (Proof.raw_goal s)
            val nprem = Thm.nprems_of st
            val _ = if length leaves = nprem then ()
                    else error "BUG 3PLbwUDhTAGAvX/M+3jl3g"

            val s'  = apply using tac s
            val st' = #goal (Proof.goal s')
            val is_multi_goal = \<^try>\<open>let
                    val s'p  = apply1 using tac s
                    val st'p = #goal (Proof.goal s'p)
                 in not (Thm.equiv_thm thy (st', st'p))
                end catch _ => true\<close>

         in (*assumption: a tactic either applies to the first goal only or the entire all goals*)
            if is_multi_goal
            then let
                 val M = length leaves
                 fun app s [] = ([], s)
                   | app s (lf::leaves) =
                    let val (leaves', s') = app s leaves
                        val N = M - length leaves
                        val s'2 = Proof.refine_primitive (K (Goal.restrict N 1)) s'
                     in case try (apply using tac) s'2
                     of SOME s'3 => let
                             val M = Thm.nprems_of (#goal (Proof.goal s'3))
                             val new_leaves = new_oneshots M
                          in set_oneshot (lf,
                                  GRDTREE ([(SOME s, TACTIC (pass_tac' s tac, using, NONE))], new_leaves))
                           ; (new_leaves @ leaves',
                              Proof.refine_primitive (K (Goal.unrestrict N)) s'3)
                         end
                      | NONE => (lf :: leaves', s')
                    end
              in app s leaves
             end
            else let
                 val diff = Thm.nprems_of st' - nprem
                 val _ = if diff < ~1 then error "BUG 7139" else ()
                 val new_goals = new_oneshots (diff + 1)
              in set_oneshot (hd leaves,
                    GRDTREE ([(SOME s, TACTIC (pass_tac' s tac, using, NONE))], new_goals))
               ; (new_goals @ tl leaves, s')
             end
        end

      fun sep using (tac as Method.Source _) leaves_s = apply' using tac leaves_s
        | sep using (tac as Method.Basic  _) leaves_s = apply' using tac leaves_s
        | sep using (Method.Combinator (_, Method.Then, tacs)) leaves_s
            = fold (sep using) tacs leaves_s
        | sep _ (Method.Combinator (_, Method.Then_All_New, [])) leaves_s = leaves_s
        | sep using (Method.Combinator (_, Method.Then_All_New, [t1])) leaves_s
            = sep using t1 leaves_s
        | sep using (Method.Combinator (_, Method.Then_All_New, [t1,t2])) (leaves0, s0) =
            let val s = Proof.refine_primitive (K (Goal.protect 1)) s0
                val leaves = [hd leaves0]
                val (leaves', s') = sep using t1 (leaves, s)
                val diff = length leaves' - length leaves

                fun restrict i n (leaves, s) =
                  let val s' = Proof.refine_primitive (K (Goal.restrict i n)) s
                   in (take n (drop (i-1) leaves), s')
                  end
                fun unrestrict i n origin_leaves (leaves, s) =
                  let val s' = Proof.refine_primitive (K (Goal.unrestrict i)) s
                   in (take (i-1) origin_leaves @ leaves @ drop (i-1+n) origin_leaves, s')
                  end

                fun rep j leaves_s =
                  if j < 0 then leaves_s
                  else leaves_s
                   |> restrict (j+1) 1
                   |> sep using t2
                   |> unrestrict (j+1) 1 (fst leaves_s)
                   |> rep (j-1)
                val (leaves'', s'') = rep diff (leaves', s')
             in (leaves'' @ tl leaves0,
                 Proof.refine_primitive (K Goal.conclude) s'')
            end
        | sep using (Method.Combinator (oi, Method.Then_All_New, tac::tacs)) leaves_s =
            sep using (Method.Combinator (oi, Method.Then_All_New,
                  [tac, Method.Combinator (oi, Method.Then_All_New, tacs)])) leaves_s
        | sep _ (Method.Combinator (_, Method.Orelse, [])) _ = raise PRF_FAIL (K "")
        | sep using (Method.Combinator (oi, Method.Orelse, tac::tacs)) leaves_s =
            \<^try>\<open>sep using tac leaves_s
              catch err =>
                if null tacs
                then raise err
                else sep using (Method.Combinator (oi, Method.Orelse, tacs)) leaves_s\<close>
        | sep using (Method.Combinator (_, Method.Try, [tac])) leaves_s =
            \<^try>\<open>sep using tac leaves_s catch _ => leaves_s\<close>
        | sep _ (Method.Combinator (_, Method.Try, _)) _ = error "BUG hCRyVI8/SFmTGEbnFjbnWg"
        | sep using (origin as Method.Combinator (_, Method.Repeat1, [tac])) leaves_s =
          ( case \<^try>\<open>SOME (sep using tac leaves_s) catch _ => NONE\<close>
              of SOME leaves_s' => sep using origin leaves_s'
               | NONE => leaves_s )
        | sep _ (Method.Combinator (_, Method.Repeat1, _)) _ = error "BUG hCRyVI8/SFmTGEbnFjbnWg"
        | sep using (Method.Combinator (_, Method.Select_Goals i, [tac])) leaves_s =
            let fun select i (leaves,s) =
                    (take i leaves, Proof.refine_primitive (K (Goal.protect i)) s)
                fun unselect i origin_leaves (leaves,s) =
                    (leaves @ drop i origin_leaves,
                     Proof.refine_primitive (K (Goal.conclude)) s)
             in leaves_s
             |> select i
             |> sep using tac
             |> unselect i (fst leaves_s)
            end
        | sep _ (Method.Combinator (_, Method.Select_Goals _, _)) _ = error "BUG hCRyVI8/SFmTGEbnFjbnWg"

      fun init using tac leaves_s =
        let val insert = not (is_ind tac andalso is_conj_goal (snd leaves_s))
            val _ = if insert then () else ()
         in leaves_s
          |> insert ? apsnd ( Proof.refine_insert [] )
          |> sep using tac
        end
   in init
  end

fun separate_prf tail =
  let fun sep [] leaves = leaves
        | sep ((_, PROOF _) :: _) _ = error "BUG: PROOF should be already eliminated here"
        | sep ((_, QED _) :: _) _ = error "BUG: QED should be already eliminated here"
        | sep ((_, WITH _) :: _) _ = error "BUG: WITH should be already eliminated here"
        | sep ((_, FROM _) :: _) _ = error "BUG: FROM should be already eliminated here"
        | sep ((_, ISAR_THEN) :: _) _ = error "BUG: ISAR_THEN should be already eliminated here"
        | sep ((_, ISAR_BY _) :: _) _ = error "BUG: ISAR_BY should be already eliminated here"
        | sep ((_, APPLY_END _) :: _) _ = error "BUG: ISAR_BY should be already eliminated here"
        | sep ((_, DONE) :: _) _ = error "BUG: DONE should be already eliminated here"
        | sep ((_, DDOT) :: _) _ = error "BUG: DDOT should be already eliminated here"
        | sep ((_, USING _) :: _) _ = error "BUG: USING should be already eliminated here"
(*        | sep ((_, MCALCULATION _) :: _) _ = error "BUG: MCALCULATION should be already eliminated here" *)
        | sep ((_, UNFOLD _) :: _) _ = error "BUG: UNFOLD should be already eliminated here"
        | sep ((_, DEFER i) :: L) leaves =
            let fun defer _ [] = error "BUG separate_prf.sep.defer"
                  | defer i (x::L) =
                      if i <= 1 then L @ [x] else x :: defer (i-1) L
             in sep L (defer i leaves)
            end
        | sep ((_, PREFER i) :: L) leaves =
            let val leaves' = nth leaves i :: take (i-1) leaves @ drop i leaves
             in sep L leaves'
            end
        | sep ((ast' as (s, DOT)) :: L) leaves =
            if null leaves
            then if null L
               then ( tail := [ast']
                    ; leaves)
               else error "BUG more proofs after the end"
            else let
                 val N = Thm.nprems_of (#goal (Proof.goal (the s)))
                 val leaves' =
                        if N > 1
                        then ( List.app (fn lf =>
                                 set_oneshot (lf, GRDTREE (
                                      [(NONE, TACTIC (method_assumption,([],[]),NONE))], []))
                               ) (take (N-1) leaves)
                             ; drop (N-1) leaves)
                        else leaves
              in set_oneshot (hd leaves', GRDTREE ([ast'], []))
               ; sep L (tl leaves')
             end
        | sep ((s, TACTIC (tac, using, time)) :: L) leaves =
            separate_tac time using tac (leaves, the s)
                |> fst
                |> sep L
        | sep ((ast' as (_, MPROOF _)) :: L) leaves =
            ( set_oneshot (hd leaves, GRDTREE ([ast'], []))
            ; sep L (tl leaves))
        | sep ((_, BRANCH_SUBGOALS bodies) :: L) leaves =
            ( List.app (fn (lf, body) => if null (sep body [lf]) then () else error "BUG sep")
                       (leaves ~~ bodies)
            ; tail := L
            ; [] )
        | sep ((_, SORRY) :: L) leaves =
            ( List.app (fn lf =>
                let val facts = collect_facts L
                 in set_oneshot (lf, GRDTREE ([(NONE, TACTIC (method_sorry, facts, NONE))], []))
                end
              ) leaves
            ; tail := L
            ; [] )
        | sep ((_, INCLUDING names) :: L) leaves =
            let val lf = new_oneshot ()
             in set_oneshot (hd leaves, GRDTREE ([(NONE, INCLUDING names)], [lf]) )
              ; sep L (lf :: tl leaves)
            end
        | sep _ _ = error "BUG should not occur here"
   in sep
  end

val separate_prf_pass = bottom_up_prfs (
  fn [] => []
   | ast' =>
  let val s = the (fst (hd ast'))
      val use_raw = is_ind_opr ast' andalso is_conj_goal s
      val roots = init_grdprf use_raw s
      val tail = Unsynchronized.ref []
      val _ = case separate_prf tail ast' roots
                of [] => ()
                 | _ => error "BUG h8KYedJsTC2jm63bGgXzfg"
      val ret = mk_branch_subgoals (map conclude_grdprf roots)
   in ret @ !tail
  end)

(* Match Proof Context *)

fun mk_pattern tm =
  let val i = Term.maxidx_term tm ~1 + 1
      fun mk Hs Vs (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ H $ X) = mk (subst Vs 0 H :: Hs) Vs X
        | mk Hs Vs (Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (N, T, X)) = mk Hs (((N,i),T)::Vs) X
        | mk Hs Vs X = (i, Hs, Vs, subst Vs 0 X)
      and subst Vs j (Bound k) =
            if k < j then Bound k
                     else Var (nth Vs (k-j))
        | subst Vs j (org as (A $ B)) =
            let val A' = subst Vs j A
                val B' = subst Vs j B
             in if pointer_eq (A, A')
                then if pointer_eq (B, B')
                   then org
                   else A $ B'
                else A' $ B'
            end
        | subst Vs j (org as (Abs (N,T,X))) =
            let val X' = subst Vs (j+1) X
             in if pointer_eq (X, X')
               then org
               else Abs (N,T,X')
            end
        | subst _ _ X = X
   in mk [] [] tm
  end

fun match_hyps ctxt fixes ii hpats =
  let val norm_tmenv = Vartab.map (K (apsnd Envir.beta_eta_contract))
      fun chkenv (Envir.Envir {tenv, ...}) =
            Vartab.forall (
                fn ((_,i),(_,tm)) =>
                       i <> ii orelse
                        (case tm
                           of Free (N,_) => member (fn (a,(b,_)) => a = b) fixes N
                            | _ => false)
              ) (norm_tmenv tenv)
      fun update_ret (k,name) ret = Vector.update (ret, k, name)
      fun match ret _ _ env [] = Seq.single (ret, env)
        | match  _  _ [] _  _  = Seq.empty
        | match ret passed ((k,pat)::pats) env ((name,hyp)::hyps) =
            Seq.append
                (Unify.hounifiers [] (ctxt, env, [(pat, hyp)])
              |> Seq.maps (fn (env', _) =>
                  if chkenv env'
                  then Seq.append (match (update_ret (k,name) ret) [] (passed @ pats) env' hyps)
                                  (match ret ((k,pat)::passed) pats env ((name,hyp)::hyps))
                  else Seq.empty))
                (match ret ((k,pat)::passed) pats env ((name,hyp)::hyps))
      val N = length hpats
   in match (Vector.tabulate (N, K AI_Not_Found)) [] (map_index (apfst (fn i => N - 1 - i)) hpats)
  end

fun match_goal ctxt goal =
  let val (ii, Hp, Vp, Cp) = mk_pattern goal
      val idx = fold Term.maxidx_term Hp (Term.maxidx_term Cp ~1)
   in fn (fixes, Hs, C) =>
      let val env = Envir.empty idx
          val m = Unify.hounifiers [] (ctxt, env, [(Cp, C)])
               |> Seq.maps (fn (env, _) => match_hyps ctxt fixes ii Hp env Hs)
       in Seq.pull m
       |> Option.map (fn ((ret, Envir.Envir {tenv=env,...}),_) =>
            (map (fn (v,_) => case Vartab.lookup env v
                                of SOME (_, Free (name,_)) =>
                                   the_default VI_Not_Found (AList.lookup (op =) fixes name)
                                 | _ => VI_Not_Found ) (rev Vp),
             ret) )
      end
      handle Pattern.MATCH => NONE
  end

(*
fun match_term (redex, residue) =
  let fun match env (Free (N,T), Free (N',T')) =
            (case Symtab.lookup env )
   in xx
  end *)

fun rev_append [] L = L
  | rev_append (x :: xs) L = rev_append xs (x :: L)

fun get_first_remove P xs =
  let fun get _ [] = (NONE, xs)
        | get prev (x :: xs) =
            case P x
              of NONE => get (x :: prev) xs
               | some => (some, rev_append prev xs)
   in get [] xs
  end

fun structured_statement_2_terms ctxt ((vs, assm, show) : structured_statement) =
  let val (stmt, _) = Proof_Context.read_statement vs assm (map snd show) ctxt
      val add_assm = fold_rev (fold_rev (fn A => fn C => \<^Const>\<open>Pure.imp\<close> $ A $ C)) (#assumes stmt)
      val quant = fold_rev (fn (_, Free v) => fn C => \<^Const>\<open>Pure.all \<open>#2 v\<close>\<close> $ Term.absfree v C)
                           (#fixes stmt)
   in map2 (fn ((B,_),tms) => map_index (fn (i,x) =>
                (AI_Fix (Binding.name_of B, i, length tms), quant (add_assm x))
        )) show (#shows stmt)
   |> flat
  end

fun structured_statement_2_a_src ((vs, assm, show) : structured_statement) =
  let val add_assms = fold_rev (fold_rev (fn (A,_) => fn C => trim_markup A :: " \<Longrightarrow> " :: C)) assm
      val quant = if null vs
                  then I
                  else (fn C => "\<And>" :: fold_rev (fn (B,_,_) => fn C =>
                                            Binding.name_of B :: " " :: C) vs (". " :: C))
   in map ( apsnd (map (String.concat o quant o add_assms o single o trim_markup o fst))) show
  end

fun assumes_and_fixes_of thy assms fixes [] = (assms, fixes)
  | assumes_and_fixes_of thy assms fixes ((s, ASSUME ss) :: L)
      = let val new = structured_statement_2_terms (Proof.context_of (the s)) ss
                   |> filter_out (fn (_, term) => exists (fn (_, term') =>
                        Pattern.equiv thy (term, term')
                      ) assms)
         in assumes_and_fixes_of thy (new @ assms) fixes L
        end
  | assumes_and_fixes_of thy assms fixes ((s, FIX vs) :: L) =
      let val (names', _) = Proof_Context.add_fixes_cmd vs (Proof.context_of (the s))
       in assumes_and_fixes_of thy assms ((names' ~~ map (VI_Fix o Binding.name_of o #1) vs) @ fixes) L
      end
  | assumes_and_fixes_of thy assms0 fixes0 ((s, CASE arg) :: L)
      = let val (_, ((name, pos), xs)) = restore_case arg
            val ctxt = Proof.context_of (the s)

            val kase as Rule_Cases.Case {fixes, ...} = Proof_Context.check_case ctxt false (name, pos) xs
            
            val (names', ctxtxxx) = 
                  fold_map (fn (a,b) => Proof_Context.add_fixes [(a, SOME b, NoSyn)]
                                     #> apfst hd ) fixes ctxt
            val terms = map Free (names' ~~ map snd fixes)
            val Rule_Cases.Case {assumes, fixes, ...} = Rule_Cases.apply terms kase

            val assms = maps ( apsnd (map Envir.beta_eta_contract)
                           #> (fn (name, tms) => map_index (fn (i,tm) =>
                                  (AI_Fix (name,i,length tms), tm)) tms)) assumes
            val new_fixes = names' ~~ map (VI_Fix o Binding.name_of o #1) fixes

            val assms0' = assms0
                  |> filter_out (fn (_, term) => exists (fn (_, term') =>
                        Pattern.equiv thy (term, term')
                      ) assms)
         in assumes_and_fixes_of thy (assms @ assms0') (new_fixes @ fixes0) L
        end
  | assumes_and_fixes_of thy assms fixes (_ :: L) = assumes_and_fixes_of thy assms fixes L

fun HVC_of ctxt outter_ctxt prev ((vs, hs, show0) : structured_statement') concl =
        let val thy = Proof_Context.theory_of ctxt
            val (assms0, fixes0) = assumes_and_fixes_of thy [] [] prev
            val (stmt, ctxt') = Proof_Context.read_statement vs (map snd hs) (map snd show0) ctxt
            val concl' = Syntax.read_prop ctxt' concl

            fun strip_hhf ctxt tm =
              let fun strip Hs Vs ctxt (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ H $ X)
                        = strip (H::Hs) Vs ctxt X
                    | strip Hs Vs ctxt (Const(\<^const_name>\<open>Pure.all\<close>, _) $ (X as Abs _))
                        = let val (((N,T),X'),ctxt') = Variable.dest_abs X ctxt
                           in strip Hs ((N,T)::Vs) ctxt' X'
                          end
                    | strip Hs Vs _ X = (rev Hs, rev Vs, X)
               in strip [] [] ctxt tm
              end

            val (emb_asms', emb_vs', concl'') = strip_hhf ctxt' concl'
            val emb_vs = map_index (fn (i, (name,_)) => (name, VI_Inside_Prop i) ) emb_vs'
            val ea_len = length emb_asms'
            val emb_asms = map_index (fn (i,term) => (AI_Inside_Prop (i, ea_len), term)) emb_asms'
            
            val assms_stmt = (map fst hs) ~~ (#assumes stmt)
                  |> maps (fn ((B,[]), tms) =>
                      let val name = Binding.name_of B
                          val N = length tms
                       in map_index (fn (i,tm) => (AI_Fix (name,i,N),tm) ) tms
                      end   | _ => error "BUG assumptions should have no attribute here." )
         in (map_index (fn (i, (b, Free (a,_))) => (a, VI_Fix b)
                         | _ => error "BUG fE67") (#fixes stmt)
                     @ fixes0
                     @ emb_vs ,
             map (apsnd (singleton (Variable.exportT_terms ctxt outter_ctxt)))
                 (assms_stmt @ assms0 @ emb_asms),
             (* maps (map (pair ("",0,1))) (#assumes stmt) @ assms0, *)
             singleton (Variable.exportT_terms ctxt outter_ctxt) concl'')
        end

fun split_proof s0 prfs =
  let val ctxt0 = Proof.context_of s0
      fun spl  _   _  [] = error "BUG Not ended by QED"
        | spl buf ret [(s, QED tac)] = ((the s, tac), rev (rev buf :: ret))
        | spl buf ret ((_, NEXT)::L) = spl [] (rev buf :: ret) L
        | spl buf ret (x :: L) = spl (x::buf) ret L

      val ((tail_state0, (tail_prf, tail_time)), blks) = spl [] [] prfs
      val tail_state = Proof.enter_backward tail_state0

      fun replace stmt show =
          (#1 stmt, #2 stmt, [(Binding.empty_atts, [(show,[])])])
      fun fact_not_used prf (B,[]) =
            Binding.is_empty B orelse
            not (exists_ast_fact' (fn name => Binding.name_of B = name) prf)
        | fact_not_used _ _ = false

      fun dup _ [] = []
        | dup prev0 ((s, SHOW (stmt, prf)) :: L) =
          let val ctxt = Proof.context_of (the s)
              val prev = if forall (fact_not_used L o fst) (#3 stmt)
                         then prev0
                         else (s, HAVE (stmt, prf)) :: prev0
           in if (length (#3 stmt) <= 1 orelse prf_duplicatable prf)
              then maps (map (fn (show_src,_) =>
                      (rev prev,
                       HVC_of ctxt ctxt0 prev stmt show_src,
                       (s, replace stmt show_src),
                       prf
                      )) o snd
                   ) (#3 stmt)
                 @ dup prev L
              else maps (map (fn (show_src,_) =>
                      (rev prev,
                       HVC_of ctxt ctxt0 prev stmt show_src,
                       (s, replace stmt show_src),
                       [(fst (hd prf), SORRY)])
                   ) o snd) (#3 stmt)
                 @ dup prev L
          end
        | dup prev (x :: L) = dup (x :: prev) L
      val blkss = maps (dup []) blks

      val goals = Thm.prems_of (#goal (Proof.goal s0))
      val (ordered_prfs', remaining_goals) =
            fold_map (fn G => fn X =>
              let val match = match_goal (Context.Proof ctxt0) G
               in get_first_remove (fn (pre,VHC,ss,prf) =>
                      match VHC |> Option.map (K (pre, ss, NONE, prf))
                   ) X
              end ) goals blkss
      val _ = if null remaining_goals
              then ()
              else error "BUG Some subgoal is not paired"

      val result = 
          if length (filter_out is_some ordered_prfs') <= 1 orelse
             (case tail_prf of SOME tac => tac_duplicatable tac
                             | NONE => error "BUG bb5e")
          then mk_branch_subgoals (
                 map (fn SOME x => [(NONE, MPROOF x)]
                       | NONE   => [(SOME tail_state, TACTIC (tac_for_1 (the tail_prf), ([],[]), NONE))]
                     ) ordered_prfs' )
          else let
               val grdprfs = init_grdprf false tail_state
               val _ = case separate_tac tail_time ([],[]) (the tail_prf) (grdprfs, tail_state)
                         of ([], _) => ()
                          |  _      => error "BUG h8KYedJsTC2jm63bGgXzfg"
               val prfs = map conclude_grdprf grdprfs
               fun retro [] [] = []
                 | retro []  _ = error "BUG more separations remains"
                 | retro (NONE :: _) [] = error "BUG insufficient separations"
                 | retro (NONE :: xs) (y :: ys) = y :: retro xs ys
                 | retro (SOME x :: xs) ys = [(NONE, MPROOF x)] :: retro xs ys
            in mk_branch_subgoals (retro ordered_prfs' prfs)
           end

   in result @ [(NONE, DOT)]
  end

val split_proof_pass = linear_pass NONE (
  fn (s, PROOF (_, body)) :: L => split_proof (the s) body @ L
   | L => L
)

(* Check and Pass `consider` *)

val pass_consider = linear_pass NONE (
    fn origin as ((_, ISAR_CONSIDER ((B,_),_)) :: L) =>
        let val name = Binding.name_of B
            fun P x = if x = name then true else false
            val using = Unsynchronized.ref []
            val bad = exists (exists_ast (
                fn ast as TACTIC (Method.Source (tok::_), _, _) =>
                    if Token.content_of tok = "cases"
                    then ( using := []; false)
                    else ( exists (exists_fact_fact P) (!using)
                         ; using := []
                         ; exists_fact_in P ast)
                 | USING facts =>
                    ( using := facts @ !using
                    ; false )
                 | ast => (
                      exists (exists_fact_fact P) (!using)
                    ; using := []
                    ; exists_fact_in P ast ) )
              o snd) L
         in if bad
          then raise Unsupported "the result of consider is used for purposes other than case split"
          else origin
        end
     | L => L
)

(** Pass III - More Translations **)

(* translate bracket *)

(*destroys states*)
val move_assms = let
      fun pass (L as (_, ASSUME _) :: (_, ASSUME _) :: _) = L
        | pass (L as (_, FIX  _) :: (_, FIX  _) :: _) = L
        | pass (L as (_, CASE _) :: (_, CASE _) :: _) = L
        | pass (L as (_, FIX _) :: (_, ASSUME _) :: _) = L
        | pass (L as (_, CASE _) :: (_, ASSUME _) :: _) = L
        | pass (L as (_, CASE _) :: (_, FIX _) :: _) = L
        | pass (A :: (B as (_, CASE _)) :: L) = B :: A :: L
        | pass (A :: (B as (_, ASSUME _)) :: L) = B :: A :: L
        | pass (A :: (B as (_, FIX _)) :: L) = B :: A :: L
      fun top_down [] = []
        | top_down L =
            (case pass L
               of [] => []
                | (x :: L) => x :: top_down L)
            handle Match => L
      fun bottom_up [] = []
        | bottom_up (x :: L) =
            top_down (x :: bottom_up L)
   in (fn ast => segment_pass bottom_up ast)
  end 

(*
fun structured_statement_2_single_term ctxt ((vs, assm, show) : structured_statement) =
  let
   in x
  end
*)

(*preserves states*)
(*translate the tactic \<open>goal_cases\<close>*)
val pass_goal_cases = linear_pass NONE (
  let fun chk_m (Method.Source (tok :: _)) = Token.content_of tok = "goal_cases"
        | chk_m (Method.Combinator (_, Method.Then, tacs)) = chk_m (List.last tacs)
        | chk_m _ = false
      fun trim_m [Method.Combinator (oi, Method.Then, tacs)]
            = (case trim_m tacs of [] => []
                                 | L => [Method.Combinator (oi, Method.Then, L)])
        | trim_m [_] = []
        | trim_m (x :: L) = x :: trim_m L
        | trim_m _ = error "BUG trim_m"
   in fn origin as ((s0, TACTIC (tac, using, time)) :: L) =>
      if chk_m tac
      then let 
          fun pass_br ((s, MPROOF (pre,(sx,ss),data,prf)) :: L) =
                let val (assms, vars, _) = strip_hhf (fst (
                                    Logic.dest_implies (Thm.prop_of (#goal (Proof.goal (the s))))))
                    fun pass [] = raise Translation_Fail "the case command in goal_cases is not found"
                      | pass ((s, CASE (B, (_, fixes))) :: L) =
                      let val ctxt = Proof.context_of (the s)
                       in (if null fixes then []
                           else [
                             (s, FIX (map2 (fn NONE => raise Unsupported "goal_cases has underscore"
                                             | SOME name => fn (_, T) =>
                                                    (Binding.name name, SOME (print_ty ctxt T), NoSyn) )
                                           fixes vars)) ] )
                        @ (if null assms then []
                           else [ (NONE,
                               ASSUME ([],[],[(B, map (rpair [] o print_prop ctxt) assms)])
                             ) ])
                        @ L
                      end
                      | pass (x :: L) = x :: pass L

                    val ctxt = Proof.context_of (the sx)
                    val (stmt, ctxt') = Proof_Context.read_statement
                                              (#1 ss) (map snd (#2 ss)) (map snd (#3 ss)) ctxt
                    val show' = map2 (fn (B,props) => fn tms =>
                                    (B, map2 (fn (_,pats) => fn tm =>
                                        (print_prop ctxt' tm, pats)
                                    ) props tms)
                                  ) (#3 ss) (#shows stmt)
                    val ss' = (#1 ss, #2 ss, show')
                 in (s, MPROOF (pass pre, (sx,ss'), data, prf)) :: L
                end
              | pass_br L = L
          fun pass ((s, BRANCH_SUBGOALS branches) :: L) =
                (s, BRANCH_SUBGOALS (map pass_br branches)) :: L
            | pass br = pass_br br
          val head' = case trim_m [tac] of [] => []
                         | [tac'] => [(s0, TACTIC (tac', using, time))]
       in eval (the s0) (head' @ pass L) |> snd
      end
      else origin
   | L => L
  end
)

(* replace `induct_tac`, `case_tac` with `induct`, `cases` *)

val replace_case_tac = linear_pass NONE (
let fun qchk (Method.Source (tok :: _)) = Token.content_of tok = "case_tac"
      | qchk (Method.Combinator (_, _, tacs)) = exists qchk tacs
      | qchk _ = false
    fun pass_tac (tac as Method.Source (tok :: args)) =
          if Token.content_of tok = "case_tac"
          then Method.Source (tok_cases :: args)
          else tac
      | pass_tac (Method.Combinator (oi, opr, tacs)) =
          Method.Combinator (oi, opr, map pass_tac tacs)
      | pass_tac M = M
 in fn origin as (s0, TACTIC (tac, using, time)) :: L =>
        if qchk tac
        then let val src' = (s0, TACTIC (pass_tac tac, using, time)) :: L
          in case try (eval (the s0)) src'
               of SOME (_, src'') => src''
                | NONE => origin
         end
        else origin
     | L => L
end
)


(* translate bracket *)

(*requires proof state before every `MPROOF`*)
val collect_fix_assms_case = elementwise_pass NONE (
      fn (s0, MPROOF (pre, (sss, ss), _, prf)) =>
          let val s = the s0
              val ctxt = Proof.context_of s
              val mG = fst (hd (snd (hd (#3 ss))))
              val (fixes, assms, mG') = HVC_of (Proof.context_of (the sss)) ctxt pre ss mG
              val G = Thm.prop_of (#goal (Proof.goal s))
                   |> Logic.dest_implies |> fst

              val (vs, hs) = case match_goal (Context.Proof ctxt) G (fixes, assms, mG')
                               of SOME x => x
                                | NONE => error "BUG fails to match the goal"
              val cas = get_first (fn (_, CASE ((B,_),args)) => SOME (B, args)
                                    | _ => NONE ) pre
           in (s0, MPROOF (pre, (sss, ss), SOME (vs, hs, cas), prf))
          end
       | (s0, BRCBLK ((B,_), body)) =>
          let fun collect assms fixes [] = (assms, fixes)
                | collect assms fixes ((_, ASSUME ss) :: L)
                    = collect (assms @ structured_statement_2_a_src ss) fixes L
                | collect assms fixes ((_, FIX vs) :: L)
                    = collect assms (fixes @ vs) L
                | collect assms fixes (_ :: L) = collect assms fixes L

              val (assms, fixes) = collect [] [] body
              val data = SOME (fixes, assms)
           in (s0, BRCBLK ((B,data), body))
          end
       | X => X
)

val empty_vector = Vector.tabulate (0, fn _ => error "BUG empty vector")

val translating_bracket = linear_pass NONE (
  fn (s0, BRCBLK ((B,data), body)) :: L =>
    let val SOME (fixes, assms) = data
        fun pass pre [(_,HAVE ((fixes0, assms0, shows0), prf)), (_, ENDBLK)] =
            let val assms' = map (apsnd (map (rpair []))) assms
             (* val N = count (length o snd) assms'
                val (translation, _) = fold (fn (B,tms) => fn (tab,M) =>
                      (Symtab.update (Binding.name_of B, [("that", M, length tms, N)]) tab,
                       M + length tms)
                    ) assms (Symtab.empty, 0)
                fun translate _ = Symtab.lookup translation *)
                val shows0 = case shows0
                               of [((_,atts), tms)] => [((B,atts),tms)]
                                | _ => if forall (null o snd o fst) shows0
                                       then [((B,[]), maps snd shows0)]
                                       else raise Unsupported "BRCBLK of multiple goals having different attributes"
                val ss' = (fixes @ fixes0, assms' @ assms0, shows0)
                val blocks = maps (fn (B, props) => map (fn (prop, pats) =>
                      let val shows1 = [(B, [(prop, pats)])]
                       in [(NONE, MPROOF (rev pre, (NONE, ([],[],shows1)), SOME ([],empty_vector,NONE), prf))]
                      end
                    ) props) shows0
                val prf = mk_branch_subgoals blocks
             (* val pre' = map_ast_fact' translate (rev pre)
                val prf' = map_ast_fact' translate prf *)
             in [(NONE, HAVE (ss', prf @ [(NONE, DOT)]))]
             |> validate (the s0) "translating_bracket"
            end
          | pass _ [] = raise Unsupported "Unsupported Bracket Block"
          | pass pre ((_, ASSUME _) :: L) = pass pre L
          | pass pre ((_, FIX _) :: L) = pass pre L
          | pass pre (x :: L) = pass (x :: pre) L
     in pass [] body @ L
    end
   | L => L
)

(* Reduce MPROOF *)

fun count P L = fold (fn x => fn n => n + P x) L 0

fun desugar_ss00 ctxtx additional_vs (ss : structured_statement)
  : Proof_Context.statement * structured_statement =
  let val (stmt, _) = Proof_Context.read_statement (additional_vs @ #1 ss) (#2 ss) (map snd (#3 ss)) ctxtx
      val assms' = map (map (may_print_prop ctxtx))
                       (map (fn (L1,L2) => (L1 ~~ map fst L2)) (#assumes stmt ~~ (#2 ss)))
      val shows' = map (map (may_print_prop ctxtx))
                       (map (fn (L1,L2) => (L1 ~~ map fst L2)) (#shows stmt ~~ map snd (#3 ss)))
      val ss' = (#1 ss,
                 map2 (fn props => fn props' => props' ~~ map snd props) (#2 ss) assms',
                 map2 (fn (AT, props) => fn props' => (AT, props' ~~ map snd props)) (#3 ss) shows')
   in (stmt, ss')
  end

fun desugar_ss ctxtx (ss : structured_statement) : structured_statement =
  snd (desugar_ss00 ctxtx [] (ss : structured_statement))

fun desugar_obtain ctxt (vs, ss) =
  let val (stmt, ss') = desugar_ss00 ctxt vs ss
      val vs' = map (
              fn (B,SOME T,mf) => (B,SOME T,mf)
               | (B,NONE,mf) =>
                  case AList.lookup (op =) (#fixes stmt) (Binding.name_of B)
                    of SOME term =>
                          (B, SOME (print_ty ctxt (Term.fastype_of term)), mf)
                     | NONE => error "BUG desugar_obtain") vs
   in (vs', ss')
  end

fun desugar_consider ctxt (B, (vs, terms)) =
  let val (vs', (_, _, terms')) =
          desugar_obtain ctxt (vs, ([], [], [(Binding.empty_atts, map (rpair []) terms)]))
   in (B, (vs', flat (map (map fst o snd) terms')))
  end
fun desugar_considers ctxt : Element.obtains -> Element.obtains = map (desugar_consider ctxt)


fun desugar_ss' ctxtx additional_vs (ss : structured_statement') : structured_statement' =
  let val (stmt, _) = Proof_Context.read_statement
                              (additional_vs @ #1 ss) (map snd (#2 ss)) (map snd (#3 ss)) ctxtx
      val assms' = map (map (may_print_prop ctxtx))
                       (map (fn (L1,L2) => (L1 ~~ map fst L2)) (#assumes stmt ~~ map snd (#2 ss)))
      val shows' = map (map (may_print_prop ctxtx))
                       (map (fn (L1,L2) => (L1 ~~ map fst L2)) (#shows stmt ~~ map snd (#3 ss)))
      val ss' = (#1 ss,
                 map2 (fn (AT, props) => fn props' => (AT, props' ~~ map snd props)) (#2 ss) assms',
                 map2 (fn (AT, props) => fn props' => (AT, props' ~~ map snd props)) (#3 ss) shows')
   in ss'
  end

fun desugar_at_ss ctxt vs (ass : attr_statement) : attr_statement =
  let val (stmt, _) = Proof_Context.read_statement vs [] (map snd ass) ctxt
      val shows' = map (map (may_print_prop ctxt))
                       (map (fn (L1,L2) => (L1 ~~ map fst L2)) (#shows stmt ~~ map snd ass))
   in map2 (fn (AT, props) => fn props' => (AT, props' ~~ map snd props)) ass shows'
  end

fun desugar_ss'pair (s, ss) = (s, desugar_ss' (Proof.context_of (the s)) [] ss)

fun desugar_if_need s (ss : structured_statement') =
  let val ctxt = Proof.context_of (the s)
      val ctxt_p = Proof_Context.set_mode Proof_Context.mode_schematic ctxt
      val has_thesis = maps (map fst o snd) (#3 ss)
               |> map (Syntax.parse_term ctxt_p)
               |> exists (Term.exists_subterm (fn Var (("thesis", _),_) => true
                                                | Var (("dddot", _), _) => true
                                                | _ => false))
   in if has_thesis
    then desugar_ss' ctxt [] ss
         handle TERM _ => ss
    else ss
  end

val desugar = linear_pass NONE (
  fn (s, HAVE (ss, body)) :: L =>
     (s, HAVE (desugar_ss' (Proof.context_of (the s)) [] ss, body)) :: L
   | (s, SHOW (ss, body)) :: L =>
     (s, SHOW (desugar_ss' (Proof.context_of (the s)) [] ss, body)) :: L
   | (s, THUS (ss, body)) :: L =>
     (s, THUS (desugar_ss' (Proof.context_of (the s)) [] ss, body)) :: L
   | (s, HENCE (ss, body)) :: L =>
     (s, HENCE (desugar_ss' (Proof.context_of (the s)) [] ss, body)) :: L
   | (s, ASSUME ss) :: L =>
     (s, ASSUME (desugar_ss (Proof.context_of (the s)) ss)) :: L
   | (s, ISAR_OBTAIN ((vs, ss), body)) :: L =>
     (s, ISAR_OBTAIN (desugar_obtain (Proof.context_of (the s)) (vs, ss), body)) :: L
   | (s, ISAR_CONSIDER ((B, obts), body)) :: L =>
     (s, ISAR_CONSIDER ((B, desugar_considers (Proof.context_of (the s)) obts), body)) :: L
   | (s, DEFINE (vs, ss, vs')) :: L =>
     (s, DEFINE (vs, desugar_at_ss (Proof.context_of (the s)) (vs @ vs') ss, vs')) :: L
   | L => L
)

val reduce_MPROOFs = linear_pass NONE (
  let fun process_tail prf L =
        let val tail = case L of [] => NONE
                               | L => SOME L
            fun chk_tail [] =
                  if is_some tail then the tail else []
              | chk_tail [dot as (_, DOT)] =
                  if is_some tail then the tail else []
              | chk_tail (x :: L) = x :: chk_tail L
         in chk_tail prf
        end
   in fn origin as ((s0, MPROOF (pre, ss, data, prf)) :: L) =>
    if null pre andalso (
          case data
            of SOME (vs, asms, NONE) =>
                forall (fn VI_Fix _ => false | _ => true) vs andalso
                Vector.all (fn AI_Fix _ => false | _ => true) asms
             | _ => false)
    then process_tail prf L
    else (case (data, prf)
      of ( SOME (vs, asms, kase)
         , (_, MPROOF (pre', ss', SOME (vs', asms', kase'), prf')) :: L') =>
        let fun merge_vinst [] _ = []
              | merge_vinst (VI_Fix a :: L) L' = VI_Fix a :: merge_vinst L L'
              | merge_vinst (VI_Inside_Prop i :: L) L'
                  = nth L' i :: merge_vinst L L'
              | merge_vinst (VI_Not_Found :: L) L' = VI_Not_Found :: merge_vinst L L'
            val vs'' = merge_vinst vs vs'
            val asms'' = Vector.map (fn AI_Inside_Prop (i,_) => Vector.sub (asms', i)
                                      | X => X) asms
            val kase'' = (case (kase,kase') of (SOME _, SOME _) => error "BUG reduce_MPROOFs kase"
                                             | (SOME _, _) => kase
                                             | (_, SOME _) => kase'
                                             | _           => NONE )
            
         in if count (fn VI_Inside_Prop _ => 1 | _ => 0) vs = length vs' then ()
            else error "BUG reduce_MPROOFs, unequal vs"
        (*; if count (fn AI_Inside_Prop _ => 1 | _ => 0) asms = length asms' then ()
            else error "BUG reduce_MPROOFs, unequal vs" *)
          ; (s0, MPROOF (pre @ pre', desugar_ss'pair ss', SOME (vs'', asms'', kase''), prf')) :: L
        end
       | _ => origin)
   | L => L
  end
)

(* Move lemmas (referenced by once) to where they are used. *)

(** Pass IV - Translating to the Minimal Lang **)

structure Consider_Branch = Proof_Data (
  type T = ( (binding * (var list * structured_statement)) list
           * (Proof.state option * ast) list
           ) Symtab.table
  val init = K Symtab.empty
)

fun fact_translation hs hs' =
  let fun norm_seg [] = []
        | norm_seg ((a as (_,_,n,_)) :: L) =
            if n <= 0 then norm_seg L else a :: norm_seg L
      fun update_seg' _ _ [] = error "BUG update_seg'"
        | update_seg' i name' ((name,k,n,N) :: L) =
            if i < n
            then (name,k,i,N) :: (name',0,1,1) :: (name,i+1,n-i-1,N) :: L
            else (name,k,n,N) :: update_seg' (i-n) name' L
      val update_seg = norm_seg ooo update_seg'
      val translation = fold_index (fn (i,name') =>
              if i < Vector.length hs
              then case Vector.sub (hs, i)
                of AI_Fix (name, i, N) =>
                    Symtab.map_default (name, [(name, 0, N, N)]) (fn LL => update_seg i name' LL)
                 | _ => I
              else I
          ) hs' Symtab.empty
   in translation
  end

fun insertion_hs_of hs hs' =
  fold_index (fn (i,name') =>
              if i < Vector.length hs
              then case Vector.sub (hs, i)
                of AI_Inside_Prop (j, N) => prepend (j, N, name')
                 | _ => I
              else I
          ) hs' []
   |> sort (fn ((i,_,_),(j,_,_)) => int_ord (i,j))
   |> (fn L =>
     let val LEN = length L
      in map_index (fn (i,(j,N,name)) =>
            if i = j andalso N = LEN
            then (Facts.Named ((name,Position.none),NONE), [])
            else error "BUG insertion_hs_of"
         ) L
     end)

fun trans_to_minlang ast s =
let
val end_using = Unsynchronized.ref ([],[])

fun mk_end (ty, vs) s =
  let val (using, not_using) = !end_using
      val mast = MEND ((ty, vs, using, not_using), NONE)
   in end_using := ([],[])
    ; swap (evalm s [(NONE, mast)])
  end

fun mk_end' NONE s = ([], s)
  | mk_end' (SOME vs') s = mk_end vs' s

val v_inst_2_mvar = map (fn VI_Fix name => SOME name | _ => NONE)

fun merge2 eq ((A1,A2), (B1,B2)) = (merge eq (A1,B1), merge eq (A2,B2))

fun trans_pass vs [] s = mk_end' vs s
  | trans_pass vs [(_, DOT)] s = mk_end' vs s
  | trans_pass _ ((_, DOT) :: _) _ = error "BUG fno$#@"
  | trans_pass vs ((_, ASSUME _) :: L) s = trans_pass vs L s
  | trans_pass vs ((_, FIX _)  :: L)   s = trans_pass vs L s
  | trans_pass vs ((_, CASE _) :: L)   s = trans_pass vs L s
  | trans_pass vs ((si0, ast as TACTIC (raw_tac, using, time)) :: L) s =
      let val (tac, toks, name) =
              case raw_tac
                of Method.Combinator (_, Method.Select_Goals 1, [tac]) =>
                    (case tac of Method.Source (toks as tok :: _) =>
                                    (tac, toks, Token.content_of tok)
                               | _ => if pointer_eq (tac, method_sorry)
                                      then (method_sorry, [], "msorry")
                                      else if is_ind tac
                                      then case tac of Method.Source (tok :: toks) =>
                                           (tac, toks, Token.content_of tok)
                                      else error "BUG Bad tactic 1")
                 | _ => if pointer_eq (raw_tac, method_sorry)
                        then (method_sorry, [], "msorry")
                        else if is_ind raw_tac
                        then case raw_tac of Method.Source (toks as tok :: _) =>
                             (raw_tac, toks, Token.content_of tok)
                        else error "BUG Bad tactic 2"
          val si1 = case L of [] => NONE
                            | x :: _ => SOME (the (fst x))
       in case name
       of "cases"  => translate_cases using name tac toks vs L s
        | "induct" => translate_cases using name tac toks vs L s
        | "induction" => translate_cases using name tac toks vs L s
        | "nominal_induct" => raise Unsupported "nominal_induct"
        | "msorry" => (
               end_using := merge2 fact_eq (!end_using, using)
             ; trans_pass vs [] s )
        | _ => default_tactic_translation time using tac vs L (the si0) si1 s
      end
  | trans_pass nvs ((sxxx, MPROOF (pre, _, data0, prf)) :: L) s =
      let val (vs, hs, cas) = the data0
          val _ = if is_some cas then error "BUG case" else ()
          val _ = fetch_items ()
          val need_intro = not (null vs) orelse Vector.length hs <> 0
                                                        (*can fail*)
          val mast = MINTRO (Minilang.SINGLE_GOAL, SOME (v_inst_2_mvar vs))
          val s' = if need_intro then eval_singlem mast s else s
          val ((_, hs'),_) = fetch_items ()
          
          val hs'names = map fst hs'
          val translation = fact_translation hs hs'names
          val translate = K (Symtab.lookup translation)
          val inserts = insertion_hs_of hs hs'names

          val pre' = map_ast_fact' translate pre
          val prf' = map_ast_fact' translate prf
          val prf'2 = case inserts of [] => prf'
                         | _ => (fst (hd prf), TACTIC (method_insert1 inserts, ([],[]), NONE)) :: prf'

          val (pre'', s'') = trans_pass NONE pre' s'
          val (prf'', s'3) = trans_pass nvs prf'2 s''
          (* val (L'', s'4)   = trans_pass nvs  L  s'3 *)
       in validate_tail L
        ; ((if need_intro then [(SOME s', mast)] else []) @ pre'' @ prf'', s'3)
      end
  | trans_pass nvs ((_, BRANCH_SUBGOALS bodies) :: L) s =
      let fun NVS _ bodies s =
            let val nvs = case bodies
                            of [] => nvs
                             | ((_, MPROOF (_, _, SOME (vs,_,_), _)) :: _) :: _ =>
                                    SOME (Minilang.T_NXT, SOME (v_inst_2_mvar vs))
                             | _ => SOME (Minilang.T_NXT, NONE)
             in mk_end' nvs s
            end
       in validate_tail L
        ; trans_branch_subgoals NVS bodies s
      end
  | trans_pass nvs ((s0, HAVE (ss, body)) :: L) s =
      let val s' = eval_singlem (MHAVE (ss, [])) s
          val (body', s'') = trans_pass (SOME (Minilang.T_END, NONE)) body s'
       in trans_pass nvs L s''
       |> apfst (prepend (SOME s, MHAVE (ss, body')))
      end
  | trans_pass nvs ((_, ISAR_OBTAIN (vss, body)) :: L) s =
      let val s' = eval_singlem (MCONSIDER ([vss], [])) s
          val (body'', s'') = trans_pass (SOME (Minilang.T_END, NONE)) body s'
          val (L'3, s'3) = trans_pass nvs L s''
          val mast = MCONSIDER ([vss], body'')
       in ((SOME s', mast) :: L'3, s'3)
      end
  | trans_pass nvs ((_, ISAR_CONSIDER ((B,branches),body)) :: L) s =
      let val mast = map (fn (B,(vs,props)) =>
                       (B, (vs, ([],[], [((B,[]), map (rpair []) props)])))
                     ) branches
       in s
       |> Minilang.map_context (Consider_Branch.map (
                Symtab.update (Binding.name_of B, (mast, body))))
       |> trans_pass nvs L
      end
  | trans_pass nvs ((_, NOTE notes) :: L) s =
      let val mast = MCFG_FACTS notes
       in trans_pass nvs L (eval_singlem mast s)
       |> apfst (prepend (SOME s, mast))
      end
  | trans_pass nvs ((_, DEFINE args) :: L) s =
      let val mast = MDEFINE args
       in trans_pass nvs L (eval_singlem mast s)
       |> apfst (prepend (SOME s, mast))
      end
  | trans_pass nvs ((_, LET args) :: L) s =
      let val mast = MLET args
       in trans_pass nvs L (eval_singlem mast s)
       |> apfst (prepend (SOME s, mast))
      end
  | trans_pass nvs ((_, NOTATION args) :: L) s =
      let val mast = MNOTATION args
       in trans_pass nvs L (eval_singlem mast s)
       |> apfst (prepend (SOME s, mast))
      end
  | trans_pass nvs ((_, INCLUDING names) :: L) s =
      let val mast = MCFG_BUNDL names
       in trans_pass nvs L (eval_singlem mast s)
       |> apfst (prepend (SOME s, mast))
      end
  | trans_pass nvs ((_, INCLUDE names) :: L) s =
      let val mast = MCFG_BUNDL names
       in trans_pass nvs L (eval_singlem mast s)
       |> apfst (prepend (SOME s, mast))
      end
  | trans_pass nvs ((_, OPEN_MODULE (exprs, body)) :: L) s =
      let val s' = eval_singlem (MOPEN_MODULE (exprs, [])) s
          val (body', s') = trans_pass (SOME (Minilang.T_END, NONE)) body s'
       in trans_pass nvs L s'
       |> apfst (prepend (SOME s, MOPEN_MODULE (exprs, body')))
      end
(*  | trans_pass nvs ((_, MCALCULATION args) :: L) s =
      let val mast = MCALC (args, [])
          val s' = eval_singlem mast s
       in trans_pass nvs L s'
       |> apfst (prepend (SOME s, mast))
      end *)
  | trans_pass _ (X :: _) _ = error "BUG AFSLH"
and default_tactic_translation time (using,not_using) tac vs L si0 si1 sxx =
  let val nd = Int.max (~1,
                case si1 of SOME si1 =>
                                Thm.nprems_of (#goal (Proof.raw_goal si1))
                              - Thm.nprems_of (#goal (Proof.raw_goal si0))
                          | NONE => ~1)
      val mast = MTACTIC (tac, (using,not_using), time)
      fun fallback () =
        let val (facts, not_facts) = collect_facts L
         in end_using := merge2 fact_eq (!end_using, (using @ facts, not_using @ not_facts))
          ; trans_pass vs [] sxx
        end
      val _ = fetch_items ()
   in case \<^try>\<open>SOME (eval_singlem mast sxx) catch _ => NONE\<close>
   of SOME s' =>
      let val (_, SOME goals) = fetch_items ()
       in if length goals - 1 = nd
        then trans_pass vs L s'
        else fallback ()
      end
   |> apfst (prepend (SOME sxx, mast))
    | NONE => fallback ()
  end
and translate_cases (using,_) tac_name tac toks nvs L s =
  let val consider_rule =
            if tac_name = "cases"
            then case using of [(Facts.Named ((name,_),_), [])] => SOME name
                             | _ => NONE
            else NONE
      val branches = case L of (_, BRANCH_SUBGOALS branches) :: tail =>
                                  (validate_tail tail ; branches)
                             | L => [L]
   in case Option.mapPartial (Symtab.lookup (Consider_Branch.get (Minilang.context_of s))) consider_rule
   of NONE => let
          fun get_vars (((_, MPROOF (_, _, SOME (_ , _, SOME (_, (_, params))), _)) :: _ ) :: _) = SOME params
            | get_vars (((_, MPROOF (_, _, SOME (vs, _, NONE), _)) :: _ ) :: _) = SOME (v_inst_2_mvar vs)
            | get_vars _ = NONE
          val need_IH_map = (case tac_name of "induct" => true | _ => false)
          val mast = (case tac_name
                        of "cases" => MCASE | "induct" => MINDUCT | "induction" => MINDUCT
                         | _ => raise Unsupported ("tactic " ^ tac_name))
                     (tl toks, get_vars branches, using)

          val kase = current_case ()
          fun fresh_kas () = (kase := ""; fetch_items (); ())
          fun fetch_kas () =
                let val q = !kase
                    val itms0 = fetch_items ()
                             |> fst |> snd |> map fst
                    val itms1 = filter_out (String.isPrefix (q ^ ".")) itms0
                             |> exists (String.isPrefix (q ^ ".")) itms0 ? prepend q
                 in (q, itms1)
                end

          val _ = fresh_kas ()
          val s01 = eval_singlem mast s
          val kas = fetch_kas ()

          val IH_map =
                if need_IH_map
                then case Thread_Data.get internal_data
                       of SOME (Minilang.IH_MAP m) =>
                          map (apsnd (fn binds =>
                            let fun count ret _ [] = ret
                                  | count ret name (name' :: L) =
                                      count (if name' = name then ret+1 else ret) name L
                                fun mk_iv _ [] = []
                                  | mk_iv prev (name :: L) =
                                      (name, count 0 name prev, 1, count 0 name binds) :: mk_iv (name :: prev) L
                                val ivs0 = mk_iv [] binds
                                    (* map_index (fn (i,name) => (name,i,1, count 0 name binds)) binds *)
                                fun collapse ((A as (nam1,i1,n1,N1)) :: (L' as (nam2,_,n2,_) :: L)) =
                                      if nam1 = nam2
                                      then collapse ((nam1, i1, n1+n2, N1) :: L)
                                      else A :: collapse L'
                                  | collapse L = L
                             in collapse ivs0
                            end )) m
                       | _ => error "BUG IH_map lost"
                else []
          
       (* val _ = if not need_IH_map orelse length IH_map = length branches
                  then () else error "BUG: IH_map" *)
        (*  val branches =
            if is_induct then map2 (
                fn (_,[]) => I
                 | (prefix,binds) => fn bodyx =>
                  let fun count ret _ [] = ret
                        | count ret name (name' :: L) =
                            count (if name' = name then ret+1 else ret) name L
                      val ivs0 = map_index (fn (i,name) => (name,i,1, count 0 name binds)) binds
                      fun collapse ((A as (nam1,i1,n1,N1)) :: (L' as (nam2,_,n2,_) :: L)) =
                            if nam1 = nam2
                            then collapse ((nam1, i1, n1+n2, N1) :: L)
                            else A :: collapse L'
                        | collapse L = L
                      val ivs1 = collapse ivs0
                              |> map (fn (name,i,n,N) => (prefix ^ "." ^ name,i,n,N))
                      val redex = prefix ^ "." ^ Rule_Cases.case_hypsN
                      fun translate _ name =
                        if name = redex then SOME ivs1 else NONE
                   in map_ast_fact' translate bodyx
                  end ) IH_map branches
              else branches *)
          (* val mast0 = (case name ) *)

          fun fold_map _ [] s = ([], s)
            | fold_map (_, hs') ( ((_, MPROOF (pre0, _, SOME (_, hs, NONE), prf0)) :: L) :: bodies) saa =
                let fun drop_vec d v =
                          if d <= 0 then v
                          else Vector.tabulate (Vector.length v - d, fn i => Vector.sub (v, i+d))
                    val translation = fact_translation (drop_vec (Vector.length hs - length hs') hs) hs'
                    val translate = K (Symtab.lookup translation)
                    val inserts = insertion_hs_of hs hs'

                    val pre' = map_ast_fact' translate pre0
                    val prf' = map_ast_fact' translate prf0
                    val prf'2 = case inserts of [] => prf'
                                   | _ => (fst (hd prf'), TACTIC (method_insert1 inserts, ([],[]), NONE)) :: prf'
                    val _ = validate_tail L
                    
                    val (body', sxx) = trans_pass NONE (pre' @ prf'2) saa
                    val _ = fresh_kas ()
                    val (END, s) = mk_end' (if null bodies then nvs
                                            else SOME (Minilang.T_NXT, get_vars bodies)) sxx
                    val kas_nxt = fetch_kas ()
                    val (bodies', s) = fold_map kas_nxt bodies s
                 in ((body' @ END) :: bodies', s)
                end
            | fold_map (q, _  ) ( ((_, MPROOF (pre0, _, SOME (_, _, SOME (B0, (name, _))), prf0)) :: L) :: bodies) saa =
                let val _ = if q = "" then error "BUG case qualifier lost" else ()
                    val ivs = if need_IH_map
                              then case AList.lookup (op =) IH_map name
                                     of SOME x => x
                                               |> map (fn (name,i,n,N) => (q ^ "." ^ name,i,n,N))
                                      | NONE => error "BUG IH_map not found"
                              else []
                    val trans =
                        let val p = Binding.name_of B0
                            val pfx = p ^ "."
                            val qfx = q ^ "."
                            val _ = if p = "ListRed1" then () else ()
                            val sz = size pfx
                            fun len_of ctxt name =
                                  length (Proof_Context.get_thms (the ctxt) name)
                            val hyps_redex = p ^ "." ^ Rule_Cases.case_hypsN
                            fun translate ctxt name =
                                  if need_IH_map andalso name = hyps_redex
                                  then SOME ivs
                                  else if p = q
                                  then NONE
                                  else if name = p
                                  then let val N = len_of ctxt name
                                        in SOME [(q, 0, N, N)]
                                       end
                                  else if String.isPrefix pfx name
                                  then let val N = len_of ctxt name
                                           val name' = qfx ^ String.substring (name, sz, size name - sz)
                                        in SOME [(name', 0, N, N)]
                                       end
                                  else NONE
                         in map_ast_fact' translate
                        end
                    val pre' = trans pre0
                    val prf' = trans prf0
                    val _ = validate_tail L
                    
                    val (body', sxx) = trans_pass NONE (pre' @ prf') saa
                    val _ = fresh_kas ()
                    val (END, s) = mk_end' (if null bodies then nvs
                                            else SOME (Minilang.T_NXT, get_vars bodies)) sxx
                    val kas_nxt = fetch_kas ()
                    val (bodies', s) = fold_map kas_nxt bodies s
                 in ((body' @ END) :: bodies', s)
                end
            | fold_map (_, facts0) (body :: bodies) s =
                let val facts = map (fn x => (Facts.Named ((x,Position.none), NONE), [])) facts0
                    val (s, prfx) = if null facts then (s,[])
                                    else let val s' = eval_singlem (MINSERT facts) s
                                          in (s', [(SOME s', MINSERT facts)])
                                         end
                    val (body', s) = trans_pass NONE body s
                    val _ = fresh_kas ()
                    val (END, s) = mk_end' (if null bodies then nvs
                                            else SOME (Minilang.T_NXT, get_vars bodies)) s
                    val kas = fetch_kas ()
                    val (bodies', s) = fold_map kas bodies s
                 in ((prfx @ body' @ END) :: bodies', s)
                end
          val (branches', s') = fold_map kas branches s01
       in ([(SOME s, mast), (SOME s01, MBRANCH_SUBGOALS branches')], s')
      end
    | SOME (considers, body) => let
      val _ = case toks of [_] => ()
                         |  _  => raise Unsupported "Unsupported case tactic"
      val branches' = map2 (fn (B,stmt) =>
            let val correct_name = Binding.name_of B
             in fn (_, MPROOF (pre0, _, SOME (_, _, SOME (B', (name, params))), prf0)) :: tail =>
                  let val _ = if correct_name = name then ()
                              else error "BUG seems the proof blocks are not ordered"
                      val _ = if null params then ()
                              else raise Unsupported "Unsupported FBUI"
                      val (pre,prf) =
                          if Binding.name_of B' = name then (pre0, prf0)
                          else let
                              val N = length (maps #2 (#3 (#2 stmt)))
                              val Bname = Binding.name_of B'
                              fun translate _ nam =
                                    if nam = Bname then SOME [(name, 0, N, N)]
                                                   else NONE
                              val pre' = map_ast_fact' translate pre0
                              val prf' = map_ast_fact' translate prf0
                           in (pre', prf')
                          end
                   in pre @ prf @ tail
                  end
                 | (_, MPROOF _) :: _ => raise Unsupported "Bad MPROOF block for case split"
                 | L => L
            end) considers branches
      val consider_brs = map snd considers
      val s' = eval_singlem (MCONSIDER (consider_brs, [])) s
      val (body', s'') = trans_pass (SOME (Minilang.T_NXT, NONE)) body s'
      val mast = MCONSIDER (consider_brs, body')

      fun NVS _ [] s = mk_end' nvs s
        | NVS _ _  s = mk_end' (SOME (Minilang.T_NXT, NONE)) s

   in trans_branch_subgoals NVS branches' s''
   |> apfst (prepend (SOME s, mast))
  end
  end
and trans_branch_subgoals NVS bodies s =
  let fun fold_map [] s = ([], s)
        | fold_map (body :: bodies) s =
            let val (body', s1) = trans_pass NONE body s
                val (END, s2)   = NVS body bodies s1
                val (bodies', s3) = fold_map bodies s2
             in ((body' @ END) :: bodies', s3)
            end
      val (bodies', s') = fold_map bodies s
   in ([(SOME s, MBRANCH_SUBGOALS bodies')], s')
  end

 in trans_pass (SOME (Minilang.T_END, NONE)) ast s
end

(** Pass V - Before Refining Minilang **)

(* Replace expression-based fact ref to named fact ref *)



(* Calculation *)

(*
val remove_calc = linear_passm NONE (
  fn (s, MCALC ((B,goal,steps), body)) :: L =>
      (s, MHAVE (([],[],[((B,[]),[(goal, [])])]), body)) :: L
   | L => L
)

val calc_pass = linear_passm NONE (
  fn (s0, MCALC ((BB,goal0,steps), body)) :: L =>
    let val collect_body_facts =
          let fun collect ret ((_, MHAVE ((_,_,ss),_)) :: L)
                    = collect (merge (op =) (ret, map (Binding.name_of o fst o fst) ss)) L
                | collect ret (_ :: L) = collect ret L
                | collect ret [] = ret
           in collect []
          end
        val body_facts = collect_body_facts body

        val ctxt0 = Minilang.context_of (the s0)
        val goal = Syntax.read_prop ctxt0 goal0
        fun get_LRHS tm = case Logic.strip_imp_concl tm
                            of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (_ $ LHS $ RHS) => (LHS, RHS)
                             | _ => raise Translation_Fail "get_LRHS"
        val (LHS, RHS) = get_LRHS goal


        fun step_by_note LHS rules fact =
          let val th = case Attrib.eval_thms ctxt0 [fact]
                         of [th] => th
                          | _ => raise Translation_Fail "step_by_note"
              val (LHS',RHS') = get_LRHS (Thm.concl_of th)
              val _ = if LHS aconv LHS' then ()
                      else raise Translation_Fail "LHS doesn' match LHS'"
              val RHS_tm = print_tm ctxt0 RHS'
           in (RHS', MSTEP ((rules, RHS_tm), [(NONE, MEND (Minilang.T_END, NONE, [fact], []))]))
          end

        fun pass _ steps [] =
              if null steps then [(NONE, MEND (Minilang.T_END, NONE, [], []))]
                            else error "BUG calc_pass"
          | pass LHS
                 (all_steps as ((rules,[fact' as Facts.Named ((fact,_),_)]) :: R))
                 (origin as (head as (sx, MCFG_FACTS notes)) :: L) =
              if map (Binding.name_of o fst o fst) notes = [fact]
              then let val reducible = not (exists_mast_fact' (fn name => name = fact) L)
                                       andalso length (snd (hd notes)) = 1
                       val note' = if reducible
                                   then (case hd notes
                                     of ((_,atts1),[(fact,atts2)]) => (fact, atts2 @ atts1) )
                                   else (fact', [])
                       val (LHS', mast) = step_by_note LHS rules note'
                in (if reducible then [] else [head])
                 @ (NONE, mast) :: pass LHS' R L
               end
              else if member (op =) body_facts fact
              then head :: pass LHS all_steps L
              else by_note LHS all_steps origin
          | pass LHS
                 (all_steps as ((rules,[Facts.Named ((fact,_),_)]) :: R))
                 (origin as (head as (sx, MHAVE (sss, body))) :: L) =
              (case sss
                 of ([],[],[((B,[]), [(prop, [])])]) =>
                 if Binding.name_of B = fact
                 then let
                      val ctxtx = Minilang.context_of (the sx)
                      val (LHS',RHS') = get_LRHS (Syntax.read_prop ctxtx prop)
                      val _ = if LHS aconv LHS' then ()
                              else raise Translation_Fail "LHS doesn' match LHS'"
                      val RHS_tm = print_tm ctxtx RHS'

                      fun subs_end [] = error "BUG subs_end"
                        | subs_end [(s, MEND (Minilang.T_END, vs, w, wo))] =
                                   [(s, MEND (Minilang.T_NXT, vs, w, wo))]
                        | subs_end (x :: L) = x :: subs_end L
                   in if RHS' aconv RHS
                    then body
                    else (sx, MSTEP ((rules, RHS_tm), subs_end body)) :: pass RHS' R L
                  end
                 else if member (op =) body_facts fact
                 then head :: pass LHS all_steps L
                 else by_note LHS all_steps origin
                  | _ => origin )
        and by_note LHS
                 (all_steps as ((rules,[fact]) :: R)) L =
            let val (LHS', mast) = step_by_note LHS rules (fact,[])
             in (NONE, mast) :: pass LHS' R L
            end
          | by_note _ _ _ = error "BUG by_note"
     in (s0, MCALC ((BB,goal0,steps), pass LHS steps body)) :: L
    end
    | L => L
) #> remove_calc
*)

(*

fun move_lemma names x ast =
  let val occurs = map (fn name =>
            count_ast_fact' (fn name' => if name' = name then 1 else 0) ast) names
   in if forall (fn i => i = 0) occurs
    then ast
    else if forall (fn i => i <= 1) occurs
    then let
         val moved = Unsynchronized.ref false
         val falses = List.tabulate (length names, K false)
         fun P ast =
            if !moved
            then falses
            else map (fn name => exists (exists_fact_in (fn name' => name' = name) o snd) ast) names
         fun M ast = (moved := true; x :: ast)
      in find_and_move P M ast
     end
    else x :: ast
  end

val move_lemmas = linear_pass (
  fn (origin as (_, HAVE ((_,_,shows),_))) :: L =>
      move_lemma (map (Binding.name_of o fst o fst) shows) origin L
   | ast => ast
)
*)


fun chk s origin L = \<^try>\<open>L
           |> evalm s
           |> snd
           |> (fn X =>
             if mast_cheat' X
             then raise Minilang.OPR_FAIL (Minilang.PROOF_FAIL, "")
             else X)
       catch _ => origin\<close>

local
val use_parser = Scan.repeat Parse.thm -- (Parse.$$$ "in" |-- Parse.token Parse.embedded)

fun norm_tac_phase1 (origin as (s, MTACTIC (Method.Source (tok :: toks), using, time)) :: L) =
      let fun norm toks =
            let val ((insts0, thms), _) = rule_tac_parser (toks @ [Token.eof])
             in case insts0
             of NONE => toks
              | SOME [] => toks
              | SOME inst =>
                let val att = tok_where :: inst
                 in maps (fn (rf, atts) => tokenize_fact (rf, att :: atts)) thms
                end
            end
          fun chk L = \<^try>\<open> L
               |> evalm (the s)
               |> snd
              catch _ => origin \<close>
       in case Token.content_of tok
       of "rule_tac" =>
          chk ((s, MTACTIC (Method.Source (tok :: norm toks), using, time)) :: L)
        | "erule_tac" =>
          chk ((s, MTACTIC (Method.Source (tok :: norm toks), using, time)) :: L)
        | "drule_tac" =>
          chk ((s, MTACTIC (Method.Source (tok :: norm toks), using, time)) :: L)
        | "frule_tac" =>
          chk ((s, MTACTIC (Method.Source (tok :: norm toks), using, time)) :: L)
        | "insert" => let
               val (thms, _) = Scan.repeat Parse.thm (toks @ [Token.eof])
            in if null thms
             then L
             else (s, MINSERT thms) :: L
           end
        | _ => origin
      end
(*  | norm_tac_phase1 ((_, MINSERT _) :: L) = L *)
  | norm_tac_phase1 L = L

in

val norm_Mtac = linear_passm NONE (
   recursive (
     fn (s, MTACTIC (Method.Source (tok :: toks), (using, not_using), time)) :: L =>
      (case Token.content_of tok
         of "use" => let
               val ctxt = Minilang.context_of (the s)
               val ((using', tac'), _) = use_parser (toks @ [Token.eof])
               val keywords = Keyword.no_major_keywords (Thy_Header.get_keywords' ctxt)
               val tac = Parse.read_embedded ctxt keywords (Scan.many Token.not_eof) (Token.input_of tac')
            in (s, MTACTIC (Method.Source tac, (using @ using', not_using), time)) :: L
           end
          | _ => raise Match )
      | _ => raise Match )

#> norm_tac_phase1

#>(fn origin as (s, MTACTIC (Method.Source (tok :: toks), (using, _), time)) :: L =>
  let val chk = chk (the s) origin
      val ctxt = Minilang.context_of (the s)
      fun mk_rule' thms =
        let fun is_ex_rule th =
              case Thm.concl_of th
                of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Ex\<close>, _) $ _) => true
                 | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Ex1\<close>, _) $ _) => true
                 | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Set.Bex\<close>, _) $ _) => true
                 | _ => false
            val is_ex_rule = forall is_ex_rule (Attrib.eval_thms ctxt thms)

            fun ind_of_rule "exI"  = SOME 1
              | ind_of_rule "ex1I" = SOME 1
              | ind_of_rule "bexI" = SOME 1
              | ind_of_rule _ = NONE

            fun term_of name toks =
              (case try where_parser toks
                 |> Option.mapPartial (fn ((insts, vs), _) =>
                      AList.lookup (fn (k,(k',_)) => k = k') insts "x"
                        |> (fn NONE => AList.lookup (fn (k,(k',_)) => k = k') insts "a"
                             | some => some)
                        |> Option.map (rpair vs))
                 of SOME (tm, vs) => [(trim_markup tm, vs)]
                  | NONE => (
                case try (Args.$$$ "of" |-- Scan.repeat1 Parse.term -- Parse.for_fixes) toks
                  of SOME ((tms, vs),_) =>
                    ( case ind_of_rule name
                        of SOME i => if i < length tms
                                     then [(trim_markup (nth tms i), vs)]
                                     else []
                         | NONE => [] )
                   | NONE => []
               ))
         in(if is_ex_rule
          then let val arg = maps (
                      fn (Facts.Named ((name,_),_), atts) =>
                            maps (fn att => term_of name (att @ [Token.eof])) atts
                       | _ => []) thms
                       
            in MCHOOSE arg
           end
          else MRULE (thms, using)
          )
        end
      fun mk_rule thms =
          (s, mk_rule' thms) :: L
            |> chk

   in case Token.content_of tok
           (* use xxx in yyy *)
        of "unfold" => let
            val (facts, _) = Parse.thms1 (toks @ [Token.eof])
            val (using, s') = if null using then ([], s)
                              else let val mast = MINSERT facts
                                       val s' = Option.map (eval_singlem mast) s
                                in ([(s, mast)], s')
                               end
         in using @ (s', MUNFOLD facts) :: L
        end
         | "rule" => let
           val (thms, _) = Scan.repeat Parse.thm (toks @ [Token.eof])
        in mk_rule thms
       end
         | "drule" => let
           val (thmsx, _) = rule_parser (toks @ [Token.eof])
        in (s, MRULE (thmsx, using)) :: L
        |> chk
       end
         | "erule" => let
           val (thms, _) = rule_parser (toks @ [Token.eof])
        in (s, MRULE (thms, using)) :: L
        |> chk
       end
         | "frule" => let
           val (thms, _) = rule_parser (toks @ [Token.eof])
        in (s, MRULE (thms, using)) :: L
        |> chk
       end
         | "intro" => let
           val (thmsx, _) = Scan.repeat Parse.thm (toks @ [Token.eof])
           fun repeat N s =
                if N >= 100 then raise Minilang.OPR_FAIL (Minilang.PROOF_FAIL, "")
                else \<^try>\<open>let val mast = mk_rule' thmsx
                         val s' = eval_singlem mast s
                 in (SOME s, mast) :: repeat (N+1) s'
                end catch _ => []\<close>
        in \<^try>\<open>repeat 0 (the s) @ L
        |> chk
           catch _ => origin\<close>
       end
         | "elim" => let
           val (thmsx, _) = Scan.repeat Parse.thm (toks @ [Token.eof])
           fun repeat N s = \<^try>\<open>
                if N >= 100 then raise Minilang.OPR_FAIL (Minilang.PROOF_FAIL, "")
                else let val s' = eval_singlem (MRULE (thmsx, using)) s
                 in (SOME s, MRULE (thmsx, using)) :: repeat (N+1) s'
                end catch _ => []\<close>
        in \<^try>\<open>
           repeat 0 (the s) @ L
        |> chk
           catch Minilang.OPR_FAIL _ => origin\<close>
       end
         | "dest" => let
           val (thms, _) = Scan.repeat Parse.thm (toks @ [Token.eof])
        in (s, MRULE (thms, using)) :: L
        |> chk
       end
         | "standard" => (s, MRULE ([], using)) :: L
         | "unfold_locales" =>
         let val ist = (NONE, MINSERT using)
             fun insert' ((s, MBRANCH_SUBGOALS brs) :: L) = (s, MBRANCH_SUBGOALS (map insert' brs)) :: L
               | insert' L = ist :: L
             val insert = if null using then I else insert'
          in (s, MRULE ([], [])) :: insert L
          |> chk
         end
         | "rule_tac" => let
           val ((_,thms), _) = rule_tac_parser (toks @ [Token.eof])
        in mk_rule thms
       end
         | "erule_tac" => let
           val ((_,thms), _) = rule_tac_parser (toks @ [Token.eof])
        in (s, MRULE (thms, using)) :: L
        |> chk
       end
         | "drule_tac" => let
           val ((_,thms), _) = rule_tac_parser (toks @ [Token.eof])
        in (s, MRULE (thms, using)) :: L
        |> chk
       end
         | "frule_tac" => let
           val ((_,thms), _) = rule_tac_parser (toks @ [Token.eof])
        in (s, MRULE (thms, using)) :: L
        |> chk
       end
         | _ => origin
   end
   | origin as ((s, MBRANCH_SUBGOALS branches) :: L) =>
      if null L then origin
      else let fun map [] = []
                 | map [L'] = [L' @ L]
                 | map (x :: L') = x :: map L'
            in [(s, MBRANCH_SUBGOALS (map branches))]
           end
   | L => L
))
#> linear_passm NONE (fn L => recursive (
  fn ((s0, MINSERT arg) :: (_, MCHOOSE arg') :: L) =>
     (s0, MCHOOSE arg') :: (NONE, MINSERT arg) :: L
) L)
#> linear_passm NONE (
  fn origin as (s0, MINSERT thmsx) :: (_, MTACTIC (tac, (using, not_using), time)) :: L =>
      chk (the s0) origin
          ( (s0, MTACTIC (tac, (merge_facts [thmsx, using], not_using), time)) :: L )
   | L => L
)

end

(** Pass VI - Refinement **)

(*preserve state*)
val refinement = linear_passm NONE (
  let fun can_refine N (w,wo) [(_, MEND ((ty, vs, w', wo'), cheat))]
            = if N > 0 orelse is_some cheat
              then SOME (ty, vs, merge_facts [w, w'], merge_facts [wo, wo'])
              else NONE
        | can_refine N (w,wo) ((_, MTACTIC (Method.Source tac, (using, not_using), _)) :: L) =
           (case tac_can_refine (tac @ [Token.eof])
              of SOME (w',wo') =>
                    can_refine (N+1) (merge_facts [using, w', w], merge_facts [not_using, wo', wo]) L
               | NONE => NONE)
        | can_refine N (w,wo) ((_, MINSERT facts) :: L) =
            can_refine (N+1) (merge_facts [facts, w], wo) L
        | can_refine N (w,wo) ((_, MUNFOLD facts) :: L) =
            can_refine (N+1) (merge_facts [facts, w], wo) L
        | can_refine N (w,wo) ((_, MRULE (rules, using)) :: L) =
            can_refine (N+1) (merge_facts [rules, using, w], wo) L
        | can_refine _ _ _ = NONE
   in fn [] => []
       | L =>
      case can_refine 0 ([],[]) L
        of SOME mend =>
            let val s = the (fst (hd L))
                     |> Minilang.map_context (
                          Config.put Phi_Sledgehammer_Solver.sledgehammer_params "timeout = 15")
             in case try (evalm s) [(NONE, MEND (mend, NONE))]
             of SOME (_, ast) =>
                  if mast_cheat' ast
                  then case L
                    of [_] => raise Minilang.OPR_FAIL (Minilang.PROOF_FAIL, "Some proof obligation fails")
                     |  _  => L
                  else ast
              | NONE => L
            end
         | NONE => L
  end
)

(** Pass VII - Post Refinement **)

(* Move Lemmas to Where They are Used *)

datatype scope = SCOPE  of scope list Unsynchronized.ref
                         * mast
                         * (mast' -> Minilang.state option * mast)
               | SELEMT of (Minilang.state option * mast)
               | SBRS   of Minilang.state option * scope list list

fun build_scope [] = []
  | build_scope ((s, x as MCONSIDER (args, body)) :: L) =
         SCOPE (Unsynchronized.ref (build_scope body), x,
                fn B => (s, MCONSIDER (args, B)))
      :: build_scope L
  | build_scope ((s, x as MHAVE (args, body)) :: L) =
         SCOPE (Unsynchronized.ref (build_scope body), x,
                fn B => (s, MHAVE (args, B)))
      :: build_scope L
(*  | build_scope ((s, x as MSTEP (args, body)) :: L) =
         SCOPE (Unsynchronized.ref (build_scope body), x,
                fn B => (s, MSTEP (args, B)))
      :: build_scope L *)
  | build_scope ((s, x as MOPEN_MODULE (args, body)) :: L) =
         SCOPE (Unsynchronized.ref (build_scope body), x,
                fn B => (s, MOPEN_MODULE (args, B)))
      :: build_scope L
(*  | build_scope ((s, x as MCALC (args, body)) :: L) =
         SCOPE (Unsynchronized.ref (build_scope body), x,
                fn B => (s, MCALC (args, B)))
      :: build_scope L *)
  | build_scope ((s, MBRANCH_SUBGOALS brs) :: L) =
         SBRS (s, map build_scope brs)
      :: build_scope L
  | build_scope (x :: L) = SELEMT x :: build_scope L

fun restore_scope [] = []
  | restore_scope (SCOPE (scopes, _, re) :: L) = re (restore_scope (!scopes)) :: restore_scope L
  | restore_scope (SELEMT x :: L) = x :: restore_scope L
  | restore_scope (SBRS (s, brs) :: L) = (s, MBRANCH_SUBGOALS (map restore_scope brs)) :: restore_scope L

(*P returns whether the fact occurs or not*)
fun scopes_of_fact P  =
  let fun join _ []  = NONE
        | join _ [x] = SOME x
        | join x _  = SOME x
      fun scope_of scps (SCOPE (scp, x, _)) =
          let val ret = map_filter (scope_of (scp::scps)) (!scp)
           in if exists_fact_inm P x
            then SOME (scp::scps)
            else join scps ret
          end
        | scope_of scps (SELEMT (_, x)) =
            if exists_fact_inm P x then SOME scps else NONE
        | scope_of scps (SBRS (_, brs)) =
            (join scps o map_filter (join scps o map_filter (scope_of scps))) brs
   in join [] o map_filter (scope_of [])
  end

fun segment_pass_scp F =
  let fun ivk scps = F (pass scps)
      and pass [] = []
        | pass (SCOPE (scps, decls, R) :: L) =
            let val L' = pass L
             in scps := ivk (!scps)
              ; SCOPE (scps, decls, R) :: L'
             end
        | pass (SBRS (s, brs) :: L) =
            let val L' = pass L
                fun rmap [] = []
                  | rmap (x :: L) =
                      let val L' = rmap L
                       in ivk x :: L'
                      end
             in SBRS (s, rmap brs) :: L'
            end
        | pass (x :: L) = x :: pass L
   in ivk
  end

(*
fun split P =
  let fun F buf ret [] = rev (rev buf :: ret)
        | F buf ret (x :: L) =
            if P x then F [] (rev buf :: ret) L
                   else F (x :: buf) ret L
   in F [] []
  end *)

val all_non_declarative_tok =
  let open Token
      val non_declaratives = ["where", "of", "OF", "simplified", "symmetric", "THEN",
                              "unfolded", "folded"]
   in forall (fn [] => true
               | (tok :: _) => member (op =) non_declaratives (content_of tok))
  end

fun decls_of (MHAVE (args, _)) = map (Binding.name_of o fst o fst) (#3 args)
  | decls_of (MCFG_FACTS notes) = map_filter (fn ((B,atts), _) =>
                                      if all_non_declarative_tok atts
                                      then SOME (Binding.name_of B)
                                      else NONE ) notes
  | decls_of _ = []

val move_lemma =
  build_scope
#>segment_pass_scp (
  let fun pass [] = []
        | pass ((cur as SCOPE (_, x, _)) :: L) = try_move cur x L
        | pass ((cur as SELEMT (_,x)) :: L) = try_move cur x L
        | pass (x :: L) = x :: pass L
      and try_move cur x L =
            let val L' = pass L
                val decls = decls_of x
             in if null decls
             then cur :: L'
             else case scopes_of_fact (member (op =) decls) L
             of SOME (target :: _) =>
                  ( target := cur :: !target
                  ; L' )
              | _ => cur :: L'
            end
   in pass
  end
) #> restore_scope


(* GEN SIMP *)

val SIMP_LIKE = ["simp", "auto", "simp_all", "clarsimp"]

val red_SIMP = linear_passm NONE (
  fn origin as (s00, MTACTIC (Method.Source (tok :: toks), (using, not_using), _)) :: L =>
      if member (op =) SIMP_LIKE (Token.content_of tok)
      then \<^try>\<open>let
           val ((w,wo), _) =
              case Token.content_of tok
                of "auto" => auto_parser (toks @ [Token.eof])
                 | _ => simp_parser (toks @ [Token.eof])
           val s0 = the s00
           val s1 = case L of H1 :: _ => SOME (the (fst H1))
                            | _ => NONE
           val mast = MSIMP (merge_facts [using, w], merge_facts [not_using, wo])
           val s1'= eval_singlem mast s0
           val chk = chk s0 origin
        in if is_some s1 andalso Minilang.equiv_proof_state (the s1, s1')
         then (s00, mast) :: L
         else if Minilang.num_goals s1' = (case s1 of SOME ss => Minilang.num_goals ss | _ => 0)
         then (s00, mast) :: L
           |> chk
         else origin
       end catch _ => origin\<close>
      else origin
   | L => L
)


(* reprint *)

val reprint_pass = linear_passm NONE (
  fn (so, MDEFINE (vs, ass, vsx)) :: L =>
     let val ctxt = Minilang.context_of (the so)
         val ass' = desugar_at_ss ctxt [] ass
      in (so, MDEFINE (vs, ass', vsx)) :: L
     end
   | (so, MHAVE (ss, body)) :: L =>
     let val ctxt = Minilang.context_of (the so)
         val ss' = desugar_ss' ctxt [] ss
      in (so, MHAVE (ss', body)) :: L
     end
   | (so, MCONSIDER (cases, body)) :: L =>
     let val ctxt = Minilang.context_of (the so)
         fun reprint (vs, ss) =
            let val (_, ss') = desugar_ss00 ctxt vs ss
             in (vs, ss')
            end
      in (so, MCONSIDER (map reprint cases, body)) :: L
     end
   | (so, MCHOOSE terms) :: L =>
     let val ctxt = Minilang.context_of (the so)
         fun reprint (term, vs0) =
          let val vs = map (fn (B,T,synt) =>
                          (B,Option.map (Syntax.read_typ ctxt) T,synt)) vs0
              val (_, ctxt') = Proof_Context.add_fixes vs ctxt
              val termx = Syntax.read_term ctxt' term
              val term' = may_print_tm ctxt' (termx, term)
           in (term', vs0)
          end
      in (so, MCHOOSE (map reprint terms)) :: L
     end
   | L => L
)

(*** Toplevel ***)

fun anotate_types (s, toks) =
  let val s = Toplevel.command_exception false
                  (Toplevel.proof (Proof.map_context ( Config.put Printer.show_markup false
                                                    #> Config.put Goal.quick_and_dirty true
                                                    #> Config.put show_types true ))
                                  Toplevel.empty) s
      val ps = if Toplevel.is_proof s then Toplevel.proof_of s
                                      else error "BUG Not a proof state"
   in Thread_Data.put counter_store NONE
    ; Thread_Data.put initial_state (SOME ps)
    ; parse_isar (s, toks)
   (* |> validate ps "Validation Fail: Initial Pass" (*UNNECESSARY*) *)
   |> pad_vars_in_case                               (*requires and preserves states*)
   |> desugar                                        (*preserves states*)
  end

datatype AST = Isar_AST of ast' | Mini_AST of mast' | NO_AST
type ret = (string * (AST * exn list)) list

fun print_AST (Isar_AST ast) = print_ast true ast
  | print_AST (Mini_AST ast) = print_mast true ast
  | print_AST NO_AST = ""

fun elaborate ret (s, toks) =
  let val s = Toplevel.command_exception false
                  (Toplevel.proof (Proof.map_context ( Config.put Printer.show_markup false
                                                    #> Config.put Goal.quick_and_dirty true
                                                    #> Config.put show_types true ))
                                  Toplevel.empty) s
      val ps = if Toplevel.is_proof s then Toplevel.proof_of s
                                      else error "BUG Not a proof state"
   in Thread_Data.put counter_store NONE
    ; Thread_Data.put initial_state (SOME ps)
    ; parse_isar (s, toks)
   (* |> validate ps "Validation Fail: Initial Pass" (*UNNECESSARY*) *)
   |> pad_vars_in_case                               (*requires and preserves states*)
   |> desugar                                        (*preserves states*)
   |> (fn X => (ret := ("after_desugar", (Isar_AST X, [])) :: !ret; X))
   |> assign_factname                                (*requires and preserves states*)
   |> pass_also_finally                              (*preserves states*)
   |> (fn X => (ret := ("before_norm_assums", (Isar_AST X, [])) :: !ret; X))
   |> norm_assums                                    (*destroys   states*)
   |> validate ps "Validation Fail: assign_factname" (*NECESSARY*)
   |> (fn X => (ret := ("before_elim_this_connectives", (Isar_AST X, [])) :: !ret; X))
   |> resolve_this                                   (*preserves states*)
   |> norm_FROM_WITH_USING                           (*preserves states*)
   |> (fn X => (ret := ("after_elim_this_connectives", (Isar_AST X, [])) :: !ret; X))
   |> replace_fact_expr'                             (*preserves states*)
   |> rewrite_subgoal
   (* |> validate ps "Validation Fail: norm_FROM_WITH_USING" (*UNNECESSARY*) *)
   |> pass_consider                                  (*preserves states*)
   |> norm_prf1
   |> (fn X => (ret := ("before_split_proof", (Isar_AST X, [])) :: !ret; X))
   |> split_proof_pass                               (*restructure, messes up states of PROOF*)
   |> (fn X => (ret := ("after_split_proof", (Isar_AST X, [])) :: !ret; X))
   |> move_assms                                     (*destroys states, requires no states*)
   |> validate ps "Validation Fail: split_proof_pass" (*NECESSARY*)
   |> replace_case_tac                               (*preserves states*)
   |> pass_goal_cases                                (*destroys states, requires states of MPROOF*)
   |> collect_fix_assms_case                         (*preserves states*)
   |> translating_bracket                            (*restructure, messes up states of BRCBLK*)
   |> (fn X => (ret := ("before_sep_tactic", (Isar_AST X, [])) :: !ret; X))
   |> separate_prf_pass
   |> reduce_MPROOFs
      (*any tactic is applied only to the leading subgoal, in form `apply((tac)[1])`*)
      (*at this stage,   , QED, THUS, HENCE, SHOW, USING, DEFER,  , WITH,
                       FROM, ISAR_THEN, ISAR_BY, APPLY_END, DONE, DDOT, UNFOLD, NEXT, SORRY
        are eliminated, leaving FIX, ASSUME, CASE, ISAR_OBTAIN, ISAR_CONSIDER,
                       DOT, TACTIC, DEFINE, LET, NOTATION, HAVE, OPEN_MODULE, NOTE, MPROOF,
                       BRANCH_SUBGOALS *)
   |> validate ps "Validation Fail: final pass"
   |> (fn X => (ret := ("final_isar_pass", (Isar_AST X, [])) :: !ret; X))
 (* |> (fn X => (warning (print_ast X); X)) *)
  end

fun translate_m targets ret (s, toks) =
  let val gen_target = member (op =) targets
      val ps = if Toplevel.is_proof s then Toplevel.proof_of s
                                      else error "BUG Not a proof state"
      val ps = ps
            |> Proof.map_context ( Config.put Printer.show_markup false
                                #> Config.put Goal.quick_and_dirty true
                                #> Config.put Minilang.enable_cache_by_step false
                                #> Config.put Phi_Sledgehammer_Solver.sledgehammer_params "timeout = 20"
                                #> Config.put show_types true
                                #> Config.put show_types_nv true
                             (* #> Config.put show_sorts true *) )
      val ps_notyp = ps
            |> Proof.map_context ( Config.put show_types false
                                #> Config.put show_types_nv false
                             (* #> Config.put show_sorts false *) )
      val s0 = Minilang.INIT' ps
      val ctxt0 = Proof.context_of ps
      val ctxt0_notyp = Config.put show_types false ctxt0
      val _ = Minilang.set_reporter item_reporter
      fun report cat rep =
            if mast_cheat' rep then rep else (ret := (cat, (Mini_AST rep, [])) :: !ret ; rep)
      fun err cat E = (ret := (cat, (NO_AST, [E])) :: !ret; NONE)
      val raw = trans_to_minlang (elaborate ret (s, toks)) s0 |> fst
             |> norm_Mtac                            (*destroys state*)
             |> validatem ctxt0 (Minilang.INIT' ps)
             |> gen_target "raw" ? report "raw"
      val refined = raw
             |> refinement                           (*preserves state*)
             |> validatem ctxt0 (Minilang.INIT' ps)
             |> red_SIMP                           
             |> validatem ctxt0 (Minilang.INIT' ps)
      val _ = if mast_cheat' refined
              then raise Minilang.OPR_FAIL (Minilang.PROOF_FAIL, "Some proof obligation fails")
              else ( if gen_target "refined"
                     then ret := ("refined", (Mini_AST refined, [])) :: !ret
                     else () )
      val _ = if gen_target "untyp_refined"
              then \<^try>\<open> refined
                     |> validatem ctxt0_notyp (Minilang.INIT' ps_notyp)
                     |> reprint_pass
                     |> report "untyp_refined"
                     |> SOME
                   catch E => err "untyp_refined" E\<close>
              else NONE
      val _ = if gen_target "untyp_raw"
              then \<^try>\<open> raw
                     |> validatem ctxt0_notyp (Minilang.INIT' ps_notyp)
                     |> reprint_pass
                     |> report "untyp_raw"
                     |> SOME
                   catch E => err "untyp_raw" E\<close>
              else NONE
      val _ = if gen_target "reord_raw"
              then \<^try>\<open> raw
                     |> move_lemma                           (*destroys state*)
                     |> validatem ctxt0 (Minilang.INIT' ps)
                     |> report "reord_raw" 
                     |> SOME
                   catch E =>
                        err "reord_raw" E \<close>
              else NONE
      val _ = if gen_target "reord_refined"
              then \<^try>\<open> refined
                     |> move_lemma
                     |> validatem ctxt0 (Minilang.INIT' ps)
                     |> report "reord_refined"
                     |> SOME
                   catch E =>
                        err "reord_defined" E \<close>
              else NONE
   (* val _ = warning (String.concatWith " " ("produce: " :: map (fst) (!ret))) *)
   in ()
  end

fun parse state src =
  let val thy = Toplevel.theory_of state
      val kws = Thy_Header.get_keywords thy
      val pos = Position.make {
                  line=1, offset=1, end_offset=1, props={label="", file="#TRANSLATOR", id="0"}}
      val toks = Symbol_Pos.explode (src, pos)
              |> Token.tokenize kws {strict = false}
              |> Outer_Syntax.parse_spans
              |> map_filter (
                    (fn [] => NONE | x => SOME x) o
                    filter Token.is_proper o
                    Command_Span.content)
   in (state, toks)
  end

fun anotate_types'  state src = anotate_types (parse state src)
fun translate'  ret state src = elaborate ret (parse state src)
fun translate'm targets ret state src = translate_m targets ret (parse state src)
fun translate'test state src =
  let val output = Unsynchronized.ref []
   in translate'm ["refined", "raw"] output state src
    ; app (let open Pretty in
        fn (name, (NO_AST, fails)) =>
            warning (string_of (chunks (
              str (name ^ " fails: ") ::
              map (item o single o Runtime.pretty_exn) fails
            ) ))
          | (name, (ast, _)) =>
            Output.writeln (name ^ ":\n" ^ print_AST ast)
        end ) (!output)
    ; ()
  end

end

