theory MS_Translator
  imports Minilang.Minilang
  keywords "mproof" :: prf_block % "proof"
       and "mqed"   :: qed_block % "proof"
begin

(* declare [[ML_debugger]] *)

method_setup msorry = \<open>
  Scan.succeed (fn _ =>
    CONTEXT_METHOD (fn _ => fn (ctxt, st) =>
      TACTIC_CONTEXT ctxt (ALLGOALS (Skip_Proof.cheat_tac ctxt) st))) \<close>

ML_file \<open>library/translator_auxcmds.ML\<close>
ML_file \<open>library/oneshot_ref.ML\<close>
ML_file \<open>library/aux.ML\<close>
ML_file \<open>library/translator.ML\<close>
ML_file \<open>library/thor.ML\<close>

end
