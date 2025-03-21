structure MinLang_Translator = struct

structure MProof_Data = Proof_Data (
  type T = Proof.state list
  val init = K []
)

local

fun local_qed s =
  let val (s'1::s'::_) = MProof_Data.get (Proof.context_of s)
   in s'
   |> Proof.refine_primitive (fn ctxt => fn st' =>
      let val th = Goal.conclude (#goal (Proof.goal s))
                |> singleton (Proof_Context.export (Proof.context_of s) (Proof.context_of s'1))
       in Minilang.MP ctxt st' th
      end )
  end

in

(* val mqed = local_qed; *)
fun mqed s = s
      |> Proof.local_qed (NONE, true)

fun mproof s0 = let
       val s = Proof.refine_insert [] s0
       val {context = ctxt, goal = st, ...} = Proof.raw_goal s;
       val bind = Thm.major_prem_of st |> try HOLogic.dest_Trueprop

       fun after_qed (ctxt'', [[result]]) =
          Proof.end_block #> (fn state' =>
            let val ctxt' = Proof.context_of state';
                val result' = singleton (Proof_Context.export ctxt'' ctxt') result
             in state'
             |> Proof.refine_primitive (fn _ => fn _ =>
                    Minilang.MP ctxt st result')
            end)
          #> Proof.reset_facts
          #> Proof.enter_backward

    in s
      |> Proof.enter_forward
      |> Proof.using_facts []
      |> Proof.begin_block
      |> Proof.internal_goal (K (K ())) (Proof_Context.mode_schematic) true "subgoal"
          NONE after_qed [] [] [(Binding.empty_atts, [(Thm.term_of (Thm.cprem_of st 1), [])])] |> #2
 
(*
      |> Proof.refine_singleton (Method.Basic (fn _ => fn _ =>
            fn (ctxt, st) =>
            let val bind = Thm.major_prem_of st |> try HOLogic.dest_Trueprop
             in Seq.make_results (Seq.single (
                  MProof_Data.map (fn L => s :: L) ctxt
                    |> (is_some bind andalso not (Term.is_open (the bind))) ?
                       Proof_Context.bind_term ( (Auto_Bind.thesisN, 0), the bind ),
                  Goal.init (Thm.cprem_of st 1) ))
            end )) *)
      |> Proof.proof (SOME (Method.Basic (K (K (Seq.make_results o Seq.single))), Position.no_range))
      |> Seq.the_result ""
      |> (is_some bind andalso not (Term.is_open (the bind))
                       andalso Term.maxidx_term (the bind) ~1 = ~1) ?
         (fn s => Proof.map_context (Proof_Context.bind_term ( (Auto_Bind.thesisN, 0), the bind )) s)
      (* |> (fn s => Proof.map_context (MProof_Data.map (fn L => s :: L)) s) *)
   end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>mproof\<close> "backward proof step"
    (Scan.succeed (Toplevel.proof mproof))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>mqed\<close> "conclude proof"
    (Scan.succeed (Toplevel.proof mqed))


end
end


local open Obtain

fun gen_consider prep_obtains raw_obtains int BB state =
  let
    val _ = Proof.assert_forward_or_chain state;
    val ctxt = Proof.context_of state;

    val ((_, thesis), thesis_ctxt) = Obtain.obtain_thesis ctxt;
    val obtains = prep_obtains thesis_ctxt thesis raw_obtains;
    val atts = Rule_Cases.cases_open :: Obtain.obtains_attributes raw_obtains;
  in
    state
    |> Proof.have true NONE
       (fn (ctxt', these) => fn ss =>
         let val these' = Proof_Context.export ctxt' (Proof.context_of ss) (flat these)
          in Proof.note_thmss [((BB,[]), [(these',[])])] ss
         end )
      [(Binding.name Auto_Bind.thesisN, NONE, NoSyn)]
      (map (fn (a, A) => ((a, [Context_Rules.intro_query NONE]), [(A, [])])) obtains)
      [((Binding.empty, atts), [(thesis, [])])] int
    |-> Proof.refine_insert
  end;

fun prepare_obtains prep_clause check_terms
    ctxt thesis (raw_obtains: ('typ, 'term) Element.obtain list) =
  let
    val clauses = raw_obtains
      |> map (fn (_, (raw_vars, raw_props)) => prep_clause ctxt thesis raw_vars raw_props)
      |> check_terms ctxt;
  in map fst raw_obtains ~~ clauses end;

fun prepare_clause prep_var parse_prop mk_all ctxt thesis raw_vars raw_props =
  let
    val ((xs', vars), ctxt') = ctxt
      |> fold_map prep_var raw_vars
      |-> (fn vars => Proof_Context.add_fixes vars ##>> pair vars);
    val xs = map (Variable.check_name o #1) vars;
  in
    Logic.list_implies (map (parse_prop ctxt') raw_props, thesis)
    |> fold_rev (mk_all ctxt') (xs ~~ xs')
  end;

val mk_all_external = Logic.all_constraint o Variable.default_type;

fun mk_all_internal ctxt (y, z) t =
  let
    val frees = Frees.build (t |> Term.fold_aterms (fn Free v => Frees.add_set v | _ => I));
    val T =
      Frees.get_first (fn ((x, T), _) => if x = z then SOME T else NONE) frees
      |> \<^if_none>\<open>the_default dummyT (Variable.default_type ctxt z)\<close>;
  in Logic.all_const T $ Term.lambda_name (y, Free (z, T)) t end;

val parse_clause = prepare_clause Proof_Context.read_var Syntax.parse_prop mk_all_external;
val cert_clause = prepare_clause Proof_Context.cert_var (K I) mk_all_internal;

val read_obtains = prepare_obtains parse_clause Syntax.check_terms;
val cert_obtains = prepare_obtains cert_clause (K I);

in

val consider = gen_consider cert_obtains;
val consider_cmd = gen_consider read_obtains;

end
