(*  Title:       Nested Multisets
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2016
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2016
    Maintainer:  Dmitriy Traytel <traytel at inf.ethz.ch>
*)

section \<open>Nested Multisets\<close>

theory MS_Test_Nested_Multiset
imports "HOL-Library.Multiset_Order" Minilang_Translator.MS_Translator
begin

declare multiset.map_comp [simp]
declare multiset.map_cong [cong]


subsection \<open>Type Definition\<close>

datatype 'a nmultiset =
  Elem 'a
| MSet "'a nmultiset multiset"

inductive no_elem :: "'a nmultiset \<Rightarrow> bool" where
  "(\<And>X. X \<in># M \<Longrightarrow> no_elem X) \<Longrightarrow> no_elem (MSet M)"

inductive_set sub_nmset :: "('a nmultiset \<times> 'a nmultiset) set" where
  "X \<in># M \<Longrightarrow> (X, MSet M) \<in> sub_nmset"

lemma wf_sub_nmset[simp]: "wf sub_nmset"
ML_val \<open>val _ =  MinLang_Translator.elaborate_tatic'test (SOME "type") @{Isar.state} 
"proof (rule wfUNIVI)\n\
\  fix P :: \"'a nmultiset \<Rightarrow> bool\" and M :: \"'a nmultiset\"\n\
\  assume IH: \"\<forall>M. (\<forall>N. (N, M) \<in> sub_nmset \<longrightarrow> P N) \<longrightarrow> P M\"\n\
\  show \"P M\"\n\
\    by (induct M; rule IH[rule_format]) (auto simp: sub_nmset.simps)\n\
\qed"\<close>
proof (rule wfUNIVI)
  (*goal: \<open>\<And>(P::'a nmultiset \<Rightarrow> bool) x::'a nmultiset. \<forall>x::'a nmultiset. (\<forall>y::'a nmultiset. (y, x) \<in> sub_nmset \<longrightarrow> P y) \<longrightarrow> P x \<Longrightarrow> P x\<close>*)
  fix P :: "'a nmultiset \<Rightarrow> bool" and M :: "'a nmultiset"
  assume IH: "\<forall>M. (\<forall>N. (N, M) \<in> sub_nmset \<longrightarrow> P N) \<longrightarrow> P M" (*\<open>\<forall>M::'a nmultiset. (\<forall>N::'a nmultiset. (N, M) \<in> sub_nmset \<longrightarrow> (P::'a nmultiset \<Rightarrow> bool) N) \<longrightarrow> P M\<close>*)
  show "P M"
    apply (induct M)
    (*goals:
      1. \<open>\<And>x::'a. (P::'a nmultiset \<Rightarrow> bool) (Elem x)\<close>
      2. \<open>\<And>x::'a nmultiset multiset. (\<And>xa::'a nmultiset. xa \<in># x \<Longrightarrow> (P::'a nmultiset \<Rightarrow> bool) xa) \<Longrightarrow> P (MSet x)\<close>
    discuss goal 1*)
      apply (rule IH[rule_format])
      (*top goal: \<open>\<And>x::'a. (P::'a nmultiset \<Rightarrow> bool) (Elem x)\<close>*)
      apply ((auto simp: sub_nmset.simps)[1])
    (*discuss goal 2*)
      apply (rule IH[rule_format])
      (*top goal: \<open>\<And>x::'a nmultiset multiset. (\<And>xa::'a nmultiset. xa \<in># x \<Longrightarrow> (P::'a nmultiset \<Rightarrow> bool) xa) \<Longrightarrow> P (MSet x)\<close>*)
      apply ((auto simp: sub_nmset.simps)[1])
    (*proven 2 subgoals*) .
qed

primrec depth_nmset :: "'a nmultiset \<Rightarrow> nat" ("|_|") where
  "|Elem a| = 0"
| "|MSet M| = (let X = set_mset (image_mset depth_nmset M) in if X = {} then 0 else Suc (Max X))"

lemma depth_nmset_MSet: "x \<in># M \<Longrightarrow> |x| < |MSet M|"
  by (auto simp: less_Suc_eq_le)

declare depth_nmset.simps(2)[simp del]


subsection \<open>Dershowitz and Manna's Nested Multiset Order\<close>

text \<open>The Dershowitz--Manna extension:\<close>

definition less_multiset_ext\<^sub>D\<^sub>M :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset \<Rightarrow> bool" where
  "less_multiset_ext\<^sub>D\<^sub>M R M N \<longleftrightarrow>
   (\<exists>X Y. X \<noteq> {#} \<and> X \<subseteq># N \<and> M = (N - X) + Y \<and> (\<forall>k. k \<in># Y \<longrightarrow> (\<exists>a. a \<in># X \<and> R k a)))"

lemma less_multiset_ext\<^sub>D\<^sub>M_imp_mult:
  assumes
    N_A: "set_mset N \<subseteq> A" and M_A: "set_mset M \<subseteq> A" and less: "less_multiset_ext\<^sub>D\<^sub>M R M N"
  shows "(M, N) \<in> mult {(x, y). x \<in> A \<and> y \<in> A \<and> R x y}"
proof -
  from less obtain X Y where
    "X \<noteq> {#}" and "X \<subseteq># N" and "M = N - X + Y" and "\<forall>k. k \<in># Y \<longrightarrow> (\<exists>a. a \<in># X \<and> R k a)"
    unfolding less_multiset_ext\<^sub>D\<^sub>M_def by blast
  with N_A M_A have "(N - X + Y, N - X + X) \<in> mult {(x, y). x \<in> A \<and> y \<in> A \<and> R x y}"
    by (intro one_step_implies_mult, blast,
      metis (mono_tags, lifting) case_prodI mem_Collect_eq mset_subset_eqD mset_subset_eq_add_right
        subsetCE)
  with \<open>M = N - X + Y\<close> \<open>X \<subseteq># N\<close> show "(M, N) \<in> mult {(x, y). x \<in> A \<and> y \<in> A \<and> R x y}"
    by (simp add: subset_mset.diff_add)
qed

lemma mult_imp_less_multiset_ext\<^sub>D\<^sub>M:
  assumes
    N_A: "set_mset N \<subseteq> A" and M_A: "set_mset M \<subseteq> A" and
    trans: "\<forall>x \<in> A. \<forall>y \<in> A. \<forall>z \<in> A. R x y \<longrightarrow> R y z \<longrightarrow> R x z" and
    in_mult: "(M, N) \<in> mult {(x, y). x \<in> A \<and> y \<in> A \<and> R x y}"
  shows "less_multiset_ext\<^sub>D\<^sub>M R M N"
  using in_mult N_A M_A unfolding mult_def less_multiset_ext\<^sub>D\<^sub>M_def
proof induct
  case (base N)
  then obtain y M0 X where "N = add_mset y M0" and "M = M0 + X" and "\<forall>a. a \<in># X \<longrightarrow> R a y"
    unfolding mult1_def by auto
  thus ?case
    by (auto intro: exI[of _ "{#y#}"])
next
  case (step N N')
  note N_N'_in_mult1 = this(2) and ih = this(3) and N'_A = this(4) and M_A = this(5)

  have N_A: "set_mset N \<subseteq> A"
    using N_N'_in_mult1 N'_A unfolding mult1_def by auto

  obtain Y X where y_nemp: "Y \<noteq> {#}" and y_sub_N: "Y \<subseteq># N" and M_eq: "M = N - Y + X" and
    ex_y: "\<forall>x. x \<in># X \<longrightarrow> (\<exists>y. y \<in># Y \<and> R x y)"
    using ih[OF N_A M_A] by blast

  obtain z M0 Ya where N'_eq: "N' = M0 + {#z#}" and N_eq: "N = M0 + Ya" and
    z_gt: "\<forall>y. y \<in># Ya \<longrightarrow> y \<in> A \<and> z \<in> A \<and> R y z"
    using N_N'_in_mult1[unfolded mult1_def] by auto

  let ?Za = "Y - Ya + {#z#}"
  let ?Xa = "X + Ya + (Y - Ya) - Y"

  have xa_sub_x_ya: "set_mset ?Xa \<subseteq> set_mset (X + Ya)"
    by (metis diff_subset_eq_self in_diffD subsetI subset_mset.diff_diff_right)

  have x_A: "set_mset X \<subseteq> A"
    using M_A M_eq by auto
  have ya_A: "set_mset Ya \<subseteq> A"
    by (simp add: subsetI z_gt)

  have ex_y': "\<exists>y. y \<in># Y - Ya + {#z#} \<and> R x y" if x_in: "x \<in># X + Ya" for x
  proof (cases "x \<in># X")
    case True
    then obtain y where y_in: "y \<in># Y" and y_gt_x: "R x y"
      using ex_y by blast
    show ?thesis
    proof (cases "y \<in># Ya")
      case False
      hence "y \<in># Y - Ya + {#z#}"
        using y_in count_greater_zero_iff in_diff_count by fastforce
      thus ?thesis
        using y_gt_x by blast
    next
      case True
      hence "y \<in> A" and "z \<in> A" and "R y z"
        using z_gt by blast+
      hence "R x z"
        using trans y_gt_x x_A ya_A x_in by (meson subsetCE union_iff)
      thus ?thesis
        by auto
    qed
  next
    case False
    hence "x \<in># Ya"
      using x_in by auto
    hence "x \<in> A" and "z \<in> A" and "R x z"
      using z_gt by blast+
    thus ?thesis
      by auto
  qed

  show ?case
  proof (rule exI[of _ ?Za], rule exI[of _ ?Xa], intro conjI)
    show "Y - Ya + {#z#} \<subseteq># N'"
      using mset_subset_eq_mono_add subset_eq_diff_conv y_sub_N N_eq N'_eq
      by (simp add: subset_eq_diff_conv)
  next
    show "M = N' - (Y - Ya + {#z#}) + (X + Ya + (Y - Ya) - Y)"
      unfolding M_eq N_eq N'_eq by (auto simp: multiset_eq_iff)
  next
    show "\<forall>x. x \<in># X + Ya + (Y - Ya) - Y \<longrightarrow> (\<exists>y. y \<in># Y - Ya + {#z#} \<and> R x y)"
      using ex_y' xa_sub_x_ya by blast
  qed auto
qed

lemma less_multiset_ext\<^sub>D\<^sub>M_iff_mult:
  assumes
    N_A: "set_mset N \<subseteq> A" and M_A: "set_mset M \<subseteq> A" and
    trans: "\<forall>x \<in> A. \<forall>y \<in> A. \<forall>z \<in> A. R x y \<longrightarrow> R y z \<longrightarrow> R x z"
  shows "less_multiset_ext\<^sub>D\<^sub>M R M N \<longleftrightarrow> (M, N) \<in> mult {(x, y). x \<in> A \<and> y \<in> A \<and> R x y}"
  using mult_imp_less_multiset_ext\<^sub>D\<^sub>M[OF assms] less_multiset_ext\<^sub>D\<^sub>M_imp_mult[OF N_A M_A] by blast

instantiation nmultiset :: (preorder) preorder
begin

lemma less_multiset_ext\<^sub>D\<^sub>M_cong[fundef_cong]:
  "(\<And>X Y k a. X \<noteq> {#} \<Longrightarrow> X \<subseteq># N \<Longrightarrow> M = (N - X) + Y \<Longrightarrow> k \<in># Y \<Longrightarrow> R k a = S k a) \<Longrightarrow>
  less_multiset_ext\<^sub>D\<^sub>M R M N = less_multiset_ext\<^sub>D\<^sub>M S M N"
  unfolding less_multiset_ext\<^sub>D\<^sub>M_def by metis

function less_nmultiset :: "'a nmultiset \<Rightarrow> 'a nmultiset \<Rightarrow> bool" where
  "less_nmultiset (Elem a) (Elem b) \<longleftrightarrow> a < b"
| "less_nmultiset (Elem a) (MSet M) \<longleftrightarrow> True"
| "less_nmultiset (MSet M) (Elem a) \<longleftrightarrow> False"
| "less_nmultiset (MSet M) (MSet N) \<longleftrightarrow> less_multiset_ext\<^sub>D\<^sub>M less_nmultiset M N"
  by pat_completeness auto
termination
  by (relation "sub_nmset <*lex*> sub_nmset", fastforce,
    metis sub_nmset.simps in_lex_prod mset_subset_eqD mset_subset_eq_add_right)

lemmas less_nmultiset_induct =
  less_nmultiset.induct[case_names Elem_Elem Elem_MSet MSet_Elem MSet_MSet]

lemmas less_nmultiset_cases =
  less_nmultiset.cases[case_names Elem_Elem Elem_MSet MSet_Elem MSet_MSet]

lemma trans_less_nmultiset: "X < Y \<Longrightarrow> Y < Z \<Longrightarrow> X < Z" for X Y Z :: "'a nmultiset"
(*
proof (induct "Max {|X|, |Y|, |Z|}" arbitrary: X Y Z
    rule: less_induct)
  case less
  from less(2,3) show ?case
  proof (cases X; cases Y; cases Z)
    fix M N N' :: "'a nmultiset multiset"
    define A where "A = set_mset M \<union> set_mset N \<union> set_mset N'"
    assume XYZ: "X = MSet M" "Y = MSet N" "Z = MSet N'"
    then have trans: "\<forall>x \<in> A. \<forall>y \<in> A. \<forall>z \<in> A. x < y \<longrightarrow> y < z \<longrightarrow> x < z"
      by (auto elim!: less(1)[rotated -1] dest!: depth_nmset_MSet simp add: A_def)
    have "set_mset M \<subseteq> A" "set_mset N \<subseteq> A" "set_mset N' \<subseteq> A"
      unfolding A_def by auto
    with less(2,3) XYZ show "X < Z"
      by (auto simp: less_multiset_ext\<^sub>D\<^sub>M_iff_mult[OF _ _ trans] mult_def)
  qed (auto elim: less_trans)
qed
*) 
  sorry
  (*
ML_val \<open>val _ =  MinLang_Transl ator.translate'm  @{Isar.state} 
"proof (induct \"Max {|X|, |Y|, |Z|}\" arbitrary: X Y Z\n\
\    rule: less_induct)\n\
\  case less\n\
\  from less(2,3) show ?case\n\
 \ proof (cases X; cases Y; cases Z)\n\
 \   fix M N N' :: \"'a nmultiset multiset\"\n\
\    define A where \"A = set_mset M \<union> set_mset N \<union> set_mset N'\"\n\
\    assume XYZ: \"X = MSet M\" \"Y = MSet N\" \"Z = MSet N'\"\n\
\    then have trans: \"\<forall>x \<in> A. \<forall>y \<in> A. \<forall>z \<in> A. x < y \<longrightarrow> y < z \<longrightarrow> x < z\"\n\
\      by (auto elim!: less(1)[rotated -1] dest!: depth_nmset_MSet simp add: A_def)\n\
\    have \"set_mset M \<subseteq> A\" \"set_mset N \<subseteq> A\" \"set_mset N' \<subseteq> A\"\n\
\      unfolding A_def by auto\n\
\    with less(2,3) XYZ show \"X < Z\"\n\
\      by (auto simp: less_multiset_ext\<^sub>D\<^sub>M_iff_mult[OF _ _ trans] mult_def)\n\
\  qed (auto elim: less_trans)\n\
\qed"\<close> *)

lemma irrefl_less_nmultiset:
  fixes X :: "'a nmultiset"
  shows "X < X \<Longrightarrow> False"
  ML_val \<open>val _ =  MinLang_Translator.translate'm  @{Isar.state} 
    (File.read (Path.explode "./Test/t53.txt")) \<close>
  sorry

lemma antisym_less_nmultiset:
  fixes X Y :: "'a nmultiset"
  shows "X < Y \<Longrightarrow> Y < X \<Longrightarrow> False"
  using trans_less_nmultiset irrefl_less_nmultiset by blast

definition less_eq_nmultiset :: "'a nmultiset \<Rightarrow> 'a nmultiset \<Rightarrow> bool" where
  "less_eq_nmultiset X Y = (X < Y \<or> X = Y)"

instance
proof (intro_classes, goal_cases less_def refl trans)
  case (less_def x y)
  then show ?case
    unfolding less_eq_nmultiset_def by (metis irrefl_less_nmultiset antisym_less_nmultiset)
next
  case (refl x)
  then show ?case
    unfolding less_eq_nmultiset_def by blast
next
  case (trans x y z)
  then show ?case
    unfolding less_eq_nmultiset_def by (metis trans_less_nmultiset)
qed

lemma less_multiset_ext\<^sub>D\<^sub>M_less: "less_multiset_ext\<^sub>D\<^sub>M (<) = (<)"
  unfolding fun_eq_iff less_multiset_ext\<^sub>D\<^sub>M_def less_multiset\<^sub>D\<^sub>M by blast

end

instantiation nmultiset :: (order) order
begin

instance
proof (intro_classes, goal_cases antisym)
  case (antisym x y)
  then show ?case
    unfolding less_eq_nmultiset_def by (metis trans_less_nmultiset irrefl_less_nmultiset)
qed

end

instantiation nmultiset :: (linorder) linorder
begin

lemma total_less_nmultiset:
  fixes X Y :: "'a nmultiset"
  shows "\<not> X < Y \<Longrightarrow> Y \<noteq> X \<Longrightarrow> Y < X"
ML_val \<open>val _ =  MinLang_Translator.translate'm  @{Isar.state} 
"proof (induct X Y rule: less_nmultiset_induct)\n\
\  case (MSet_MSet M N)\n\
\  then show ?case\n\
\    unfolding nmultiset.inject less_nmultiset.simps less_multiset_ext\<^sub>D\<^sub>M_less less_multiset\<^sub>H\<^sub>O\n\
\    by (metis add_diff_cancel_left' count_inI diff_add_zero in_diff_count less_imp_not_less\n\
\      mset_subset_eq_multiset_union_diff_commute subset_mset.refl)\n\
\qed auto"\<close>
  sorry

instance
proof (intro_classes, goal_cases total)
  case (total x y)
  then show ?case
    unfolding less_eq_nmultiset_def by (metis total_less_nmultiset)
qed

end

lemma less_depth_nmset_imp_less_nmultiset: "depth_nmset X < depth_nmset Y \<Longrightarrow> X < Y"
proof (induct X Y rule: less_nmultiset_induct)
  case (MSet_MSet M N)
  then show ?case
  proof (cases "M = {#}")
    case False
    with MSet_MSet show ?thesis
      by (auto 0 4 simp: depth_nmset.simps(2) less_multiset_ext\<^sub>D\<^sub>M_def not_le Max_gr_iff
        intro: exI[of _ N] split: if_splits)
  qed (auto simp: depth_nmset.simps(2) less_multiset_ext\<^sub>D\<^sub>M_less split: if_splits)
qed simp_all
              
lemma less_nmultiset_imp_le_depth_nmset: "X < Y \<Longrightarrow> depth_nmset X \<le> depth_nmset Y"
ML_val \<open>val _ =  MinLang_Translator.translate'm  @{Isar.state} 
    (File.read (Path.explode "./Test/t54.txt")) \<close>

  sorry

lemma eq_mlex_I:
  fixes f :: "'a \<Rightarrow> nat" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "\<And>X Y. f X < f Y \<Longrightarrow> R X Y" and "antisymp R"
  shows "{(X, Y). R X Y} = f <*mlex*> {(X, Y). f X = f Y \<and> R X Y}"
proof safe
  fix X Y
  assume "R X Y"
  show "(X, Y) \<in> f <*mlex*> {(X, Y). f X = f Y \<and> R X Y}"
  proof (cases "f X" "f Y" rule: linorder_cases)
    case less
    with \<open>R X Y\<close> show ?thesis
      by (elim mlex_less)
  next
    case equal
    with \<open>R X Y\<close> show ?thesis
      by (intro mlex_leq) auto
  next
    case greater
    from \<open>R X Y\<close> assms(1)[OF greater] \<open>antisymp R\<close> greater show ?thesis
      unfolding antisymp_def by auto
  qed
next
  fix X Y
  assume "(X, Y) \<in> f <*mlex*> {(X, Y). f X = f Y \<and> R X Y}"
  then show "R X Y"
    unfolding mlex_prod_def by (auto simp: assms(1))
qed

instantiation nmultiset :: (wellorder) wellorder
begin

lemma depth_nmset_eq_0[simp]: "|X| = 0 \<longleftrightarrow> (X = MSet {#} \<or> (\<exists>x. X = Elem x))"
  by (cases X; simp add: depth_nmset.simps(2))

lemma depth_nmset_eq_Suc[simp]: "|X| = Suc n \<longleftrightarrow>
  (\<exists>N. X = MSet N \<and> (\<exists>Y \<in># N. |Y| = n) \<and> (\<forall>Y \<in># N. |Y| \<le> n))"
  by (cases X; auto simp add: depth_nmset.simps(2) intro!: Max_eqI)
    (metis (no_types, lifting) Max_in finite_imageI finite_set_mset imageE image_is_empty
      set_mset_eq_empty_iff)

lemma wf_less_nmultiset_depth:
  "wf {(X :: 'a nmultiset, Y). depth_nmset X = i \<and> depth_nmset Y = i \<and> X < Y}"
ML_val \<open>val _ =  MinLang_Translator.translate'm  @{Isar.state} 
    (File.read (Path.explode "./Test/t55.txt")) \<close>
  sorry

lemma wf_less_nmultiset: "wf {(X :: 'a nmultiset, Y :: 'a nmultiset). X < Y}" (is "wf ?R")
  ML_val \<open>val _ =  MinLang_Translator.translate'm  @{Isar.state} 
"proof -\n\
\  have \"?R = depth_nmset <*mlex*> {(X, Y). |X| = |Y| \<and> X < Y}\"\n\
\    by (rule eq_mlex_I) (auto simp: antisymp_def less_depth_nmset_imp_less_nmultiset)\n\
\  also have \"{(X, Y). depth_nmset X = depth_nmset Y \<and> X < Y} = (\<Union>i. {(X, Y). |X| = i \<and> |Y| = i \<and> X < Y})\"\n\
\    by auto\n\
\  finally show ?thesis\n\
\    by (fastforce intro: wf_mlex wf_Union wf_less_nmultiset_depth)\n\
\qed"\<close>

instance using wf_less_nmultiset unfolding wf_def mem_Collect_eq prod.case by intro_classes metis

end

end
