theory Translation_Test
  imports Main "HOL-Library.Log_Nat" "HOL-Library.Lattice_Algebras"
          "../MS_Translator_Top" HOL.Transcendental HOL.Groups_Big
begin


declare [[ML_debugger, ML_exception_debugger, ML_exception_trace]]

declare [[ML_print_depth = 100]]
 
term 1

(*
lemma \<open>(XX \<longrightarrow> True) \<and> True\<close>
  apply (rule, rule)
proof -
  fix a :: int
  have "aaa"
  ML_val \<open>Variable.dest_fixes (\<^context>)\<close>
  proof -
    fix b :: nat
    ML_val \<open>Variable.dest_fixes (\<^context> |> Local_Theory.target_of)\<close>

  sorry
(* proof -
  show True and True
    by auto
qed *)

mproof
  let ?x = \<open>XX \<Longrightarrow> True\<close>
  term ?thesis
  show ?thesis
  show True ..
mqed
mproof
  show True ..
mqed
  . *)
lemma \<open>(True \<or> False) \<and> (True \<and> True)\<close>
  ML_val \<open>val _ = MinLang_Translator.translate' @{Isar.state}
    "unfolding False_def by (rule conjI, (auto; auto), rule conjI, auto)"
  \<close>
apply ((unfold "False_def")[1])
apply ((rule conjI)[1])
(*2 subgoals*)
apply ((auto)[1])
(*NEXT*)
apply ((rule conjI)[1])
(*2 subgoals*)
apply ((auto)[1])
(*NEXT*) 
apply ((auto)[1])
.

declare [[quick_and_dirty]]
 
lemma polyfun_extremal_lemma: 
    fixes c :: "nat \<Rightarrow> 'a::real_normed_div_algebra"
  assumes "0 < e"
  shows "\<exists>M. \<forall>z. M \<le> norm(z) \<longrightarrow> norm (\<Sum>i\<le>n. c(i) * z^i) \<le> e * norm(z) ^ (Suc n)"
                             
  ML_val \<open>val _ = MinLang_Translator.translate'm @{Isar.state}
"proof (induct n)\n\
\  case 0 with assms\n\
\  show ?case\n\
\    apply (rule_tac x=\"norm (c 0) / e\" in exI)\n\
\    apply (auto simp: field_simps)\n\
\    done\n\
\next\n\
\  case (Suc n)\n\
\  obtain M where M: \"\<And>z. M \<le> norm z \<Longrightarrow> norm (\<Sum>i\<le>n. c i * z^i) \<le> e * norm z ^ Suc n\"\n\
\    using Suc assms by blast\n\
\  show ?case\n\
\  proof (rule exI [where x= \"max M (1 + norm(c(Suc n)) / e)\"], clarsimp simp del: power_Suc)\n\
\    fix z::'a\n\
\    assume z1: \"M \<le> norm z\" and \"1 + norm (c (Suc n)) / e \<le> norm z\"\n\
\    then have z2: \"e + norm (c (Suc n)) \<le> e * norm z\"\n\
\      using assms by (simp add: field_simps)\n\
\    have \"norm (\<Sum>i\<le>n. c i * z^i) \<le> e * norm z ^ Suc n\"\n\
\      using M [OF z1] by simp\n\
\    then have \"norm (\<Sum>i\<le>n. c i * z^i) + norm (c (Suc n) * z ^ Suc n) \<le> e * norm z ^ Suc n + norm (c (Suc n) * z ^ Suc n)\"\n\
\      by simp\n\
\    then have \"norm ((\<Sum>i\<le>n. c i * z^i) + c (Suc n) * z ^ Suc n) \<le> e * norm z ^ Suc n + norm (c (Suc n) * z ^ Suc n)\"\n\
\      by (blast intro: norm_triangle_le elim: )\n\
\    also have \"... \<le> (e + norm (c (Suc n))) * norm z ^ Suc n\"\n\
\      by (simp add: norm_power norm_mult algebra_simps)\n\
\    also have \"... \<le> (e * norm z) * norm z ^ Suc n\"\n\
\      by (metis z2 mult.commute mult_left_mono norm_ge_zero norm_power)\n\
\    finally show \"norm ((\<Sum>i\<le>n. c i * z^i) + c (Suc n) * z ^ Suc n) \<le> e * norm z ^ Suc (Suc n)\"\n\
\      by simp\n\
\  qed\n\
\qed"\<close>


 apply ((induct n)[1])
(*2 subgoals*)
mproof
case 0:  0
show "?case"
using assms "0" apply ((rule_tac x = "norm (c 0) / e" in exI)[1])
 apply ((auto simp : field_simps)[1])
.
mqed
(*NEXT*)
mproof
case Suc:   (Suc n)
obtain M where M: "\<And>z. M \<le> norm z \<Longrightarrow> norm (\<Sum>i\<le>n. c i * z^i) \<le> e * norm z ^ Suc n"
using Suc assms apply ((blast)[1])
.
show "?case"
 apply ((rule exI [ where x = "max M (1 + norm(c(Suc n)) / e)" ])[1])
 apply ((clarsimp simp del : power_Suc)[1])
mproof
fix z :: 'a
assume z1: "M \<le> norm z" and fact2: "1 + norm (c (Suc n)) / e \<le> norm z"
have z2: "e + norm (c (Suc n)) \<le> e * norm z"
using z1 fact2 assms apply ((simp add : field_simps)[1])
.
have fact3: "norm (\<Sum>i\<le>n. c i * z^i) \<le> e * norm z ^ Suc n"
using M[OF z1] apply ((simp)[1])
.
have fact4: "norm (\<Sum>i\<le>n. c i * z^i) + norm (c (Suc n) * z ^ Suc n) \<le> e * norm z ^ Suc n + norm (c (Suc n) * z ^ Suc n)"
using fact3 apply ((simp)[1])
.
have fact5: "norm ((\<Sum>i\<le>n. c i * z^i) + c (Suc n) * z ^ Suc n) \<le> e * norm z ^ Suc n + norm (c (Suc n) * z ^ Suc n)"
using fact4 apply ((blast intro : norm_triangle_le elim :)[1])
.
have fact6: "... \<le> (e + norm (c (Suc n))) * norm z ^ Suc n"
 apply ((simp add : norm_power norm_mult algebra_simps)[1])
.
have fact7: "... \<le> (e * norm z) * norm z ^ Suc n"
 apply ((metis z2 mult.commute mult_left_mono norm_ge_zero norm_power)[1])
.
have fact9: "norm ((\<Sum>i\<le>n. c i * z ^ i) + c (Suc n) * z ^ Suc n) \<le> e * norm z * norm z ^ Suc n" using fact5 fact6 fact7 sorry
show "norm ((\<Sum>i\<le>n. c i * z^i) + c (Suc n) * z ^ Suc n) \<le> e * norm z ^ Suc (Suc n)"
using fact9 apply ((simp)[1])
.
mqed
.
mqed
(*end 2 subgoals*)
  .


lemma "n choose k \<le> n choose (n div 2)"
                                                    
ML_val \<open>val _ = MinLang_Translator.translate' @{Isar.state}
"proof -\n\
    \have \"k \<le> n div 2 \<longleftrightarrow> 2*k \<le> n\" by linarith\n\
    \consider \"2*k \<le> n\" | \"2*k \<ge> n\" \"k \<le> n\" | \"k > n\" by linarith\n\
    \from this show ?thesis\n\
    \proof cases\n\
      \case 1\n\
      \thus ?thesis by (intro binomial_mono) linarith+\n\
    \next\n\
      \case 2\n\
      \thus ?thesis by (intro binomial_antimono) simp_all\n\
    \qed (simp_all add: binomial_eq_0)\n\
  \qed"
\<close>

thm order.antisym

mproof
have "fact0":"k \<le> n div 2 \<longleftrightarrow> 2*k \<le> n"
apply ((linarith)[1])
.
consider "2*k \<le> n" | "2*k \<ge> n" and "k \<le> n" | "k > n"
apply ((linarith)[1])
.
note fact1 = this
show "n choose k \<le> n choose n div 2"
apply ((use "fact1" in \<open>  cases \<close>)[1])
(*3 subgoals*)
mproof  
case  1
show "n choose k \<le> n choose n div 2"
apply ((use "1" in \<open> intro binomial_mono \<close>)[1])
(*2 subgoals*)
apply ((linarith)[1])
(*NEXT*)  
apply ((linarith)[1]) 
(*end 2 subgoals*)
. 
mqed 
(*NEXT*)      
mproof       
case  2 
show "n choose k \<le> n choose n div 2" 
apply ((use "2" in \<open> intro binomial_antimono \<close>)[1])
(*3 subgoals*)
apply ((simp)[1])  
(*NEXT*)   
apply ((simp)[1])  
(*NEXT*)    
apply ((simp)[1])
(*end 3 subgoals*)  
.   
mqed       
(*NEXT*) 
apply (simp_all add : binomial_eq_0)
(*end 3 subgoals*) 
.    
mqed       
.                
                         
ML \<open>ML_Translator_Top.init_translator (Path.explode "/tmp/xxx")
                                      (ML_Translator_Top.interactive_reporter ())\<close>
 


ML \<open>ML_Translator_Top.translate_file "/home/xero/repo/Isabelle2024/src/HOL/Library/Sublist.thy"\<close>

ML \<open>ML_Translator_Top.init_translator (Path.explode "/tmp/xxx")
                                      (ML_Translator_Top.interactive_reporter ())\<close>

ML \<open>ML_Translator_Top.translate_file "/home/xero/repo/Isabelle2024/src/HOL/Library/IArray.thy"\<close>
 
   
ML \<open>ML_Translator_Top.init_translator (Path.explode "/tmp/xxx")
                                      (ML_Translator_Top.interactive_reporter ())\<close>
  
ML \<open>ML_Translator_Top.translate_file "/home/xero/repo/Isabelle2024/src/HOL/Library/Infinite_Set.thy"\<close>
 
ML \<open>ML_Translator_Top.init_translator (Path.explode "/tmp/xxx")
                                      (ML_Translator_Top.interactive_reporter ())\<close>

ML \<open>ML_Translator_Top.translate_file "/home/xero/repo/Isabelle2024/src/HOL/Library/Omega_Words_Fun.thy"\<close>


term 1


ML \<open>(Path.explode "/home/xero/repo/Isabelle2023/src/HOL/Library/Sublist.thy")\<close>

lemma \<open>True\<close>
proof -
have \<open>(1::nat) < 2\<close> by auto
also have \<open>(2::nat) < 3\<close> by auto

term 1
ML_val \<open>@{thms trans}\<close>

end
