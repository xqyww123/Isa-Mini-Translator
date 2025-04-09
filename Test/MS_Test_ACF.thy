(* Author: Alexander Maletzky *)

section \<open>Algebraically Closed Fields\<close>

theory MS_Test_ACF
  imports "HOL-Computational_Algebra.Fundamental_Theorem_Algebra" Minilang_Translator.MS_Translator
begin

lemma prod_eq_zeroE:
  assumes "prod f I = (0::'a::{semiring_no_zero_divisors,comm_monoid_mult,zero_neq_one})"
  obtains i where "finite I" and "i \<in> I" and "f i = 0"
ML_val \<open>val _ =  MinLang_Translator.translate'm  @{Isar.state} 
    (File.read (Path.explode "./Test/t59.txt"))\<close>
  sorry

lemma degree_prod_eq:
  assumes "finite I" and "\<And>i. i \<in> I \<Longrightarrow> f i \<noteq> 0"
  shows "Polynomial.degree (prod f I :: _::semiring_no_zero_divisors poly) = (\<Sum>i\<in>I. Polynomial.degree (f i))"
  using assms
proof (induct I)
  case empty
  show ?case by simp
next
  case (insert j J)
  have 1: "f i \<noteq> 0" if "i \<in> J" for i
  proof (rule insert.prems)
    from that show "i \<in> insert j J" by simp
  qed
  hence eq: "Polynomial.degree (prod f J) = (\<Sum>i\<in>J. Polynomial.degree (f i))" by (rule insert.hyps)
  from insert.hyps(1, 2) have "Polynomial.degree (prod f (insert j J)) = Polynomial.degree (f j * prod f J)"
    by simp
  also have "\<dots> = Polynomial.degree (f j) + Polynomial.degree (prod f J)"
  proof (rule degree_mult_eq)
    show "f j \<noteq> 0" by (rule insert.prems) simp
  next
    show "prod f J \<noteq> 0"
    proof
      assume "prod f J = 0"
      then obtain i where "i \<in> J" and "f i = 0" by (rule prod_eq_zeroE)
      from this(1) have "f i \<noteq> 0" by (rule 1)
      thus False using \<open>f i = 0\<close> ..
    qed
  qed
  also from insert.hyps(1, 2) have "\<dots> = (\<Sum>i\<in>insert j J. Polynomial.degree (f i))" by (simp add: eq)
  finally show ?case .
qed

class alg_closed_field =
  assumes alg_closed_field_axiom: "\<And>p::'a::field poly. 0 < Polynomial.degree p \<Longrightarrow> \<exists>z. poly p z = 0"
begin

lemma rootE:
  assumes "0 < Polynomial.degree p"
  obtains z where "poly p z = (0::'a)"
proof -
  from assms have "\<exists>z. poly p z = 0" by (rule alg_closed_field_axiom)
  then obtain z where "poly p z = 0" ..
  thus ?thesis ..
qed

lemma infinite_UNIV: "infinite (UNIV::'a set)"
ML_val \<open>val _ =  MinLang_Translator.translate'm  @{Isar.state} 
    (File.read (Path.explode "./Test/t58.txt"))\<close>
  sorry
 
lemma linear_factorsE: 
  fixes p :: "'a poly"
  obtains c A m where "finite A" and "p = Polynomial.smult c (\<Prod>a\<in>A. [:- a, 1:] ^ m a)"
    and "\<And>a. m a = 0 \<longleftrightarrow> a \<notin> A" and "c = 0 \<longleftrightarrow> p = 0" and "\<And>z. poly p z = 0 \<longleftrightarrow> (c = 0 \<or> z \<in> A)"
  ML_val \<open>val _ = MinLang_Translator.translate'm  @{Isar.state} 
    (File.read (Path.explode "./Test/t57.txt"))\<close>
  sorry

end (* alg_closed_field *)

instance complex :: alg_closed_field
  by standard (rule fundamental_theorem_of_algebra, simp add: constant_degree)

end (* theory *)
