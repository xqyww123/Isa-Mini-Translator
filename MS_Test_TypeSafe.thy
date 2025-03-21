(*  Title:      JinjaDCI/J/TypeSafe.thy

    Author:     Tobias Nipkow, Susannah Mansky
    Copyright   2003 Technische Universitaet Muenchen, 2019-20 UIUC

    Based on the Jinja theory J/TypeSafe.thy by Tobias Nipkow
*)

section \<open> Type Safety Proof \<close>

theory MS_Test_TypeSafe
imports JinjaDCI.Progress JinjaDCI.BigStep JinjaDCI.SmallStep JinjaDCI.JWellForm MS_Translator
begin

(* here because it requires well-typing def *)
lemma red_shext_incr: "P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle>
  \<Longrightarrow> (\<And>E T. P,E,h,sh \<turnstile> e : T \<Longrightarrow> sh \<unlhd>\<^sub>s sh')"
  and reds_shext_incr: "P \<turnstile> \<langle>es,(h,l,sh),b\<rangle> [\<rightarrow>] \<langle>es',(h',l',sh'),b'\<rangle>
  \<Longrightarrow> (\<And>E Ts. P,E,h,sh \<turnstile> es [:] Ts \<Longrightarrow> sh \<unlhd>\<^sub>s sh')"
(*<*)
proof(induct rule:red_reds_inducts) qed(auto simp: shext_def)
(*>*)

lemma wf_types_clinit:
assumes wf:"wf_prog wf_md P" and ex: "class P C = Some a" and proc: "sh C = \<lfloor>(sfs, Processing)\<rfloor>"
shows "P,E,h,sh \<turnstile> C\<bullet>\<^sub>sclinit([]) : Void"
proof -
  from ex obtain D fs ms where "a = (D,fs,ms)" by(cases a)
  then have sP: "(C, D, fs, ms) \<in> set P" using ex map_of_SomeD[of P C a] by(simp add: class_def)
  then have "wf_clinit ms" using assms by(unfold wf_prog_def wf_cdecl_def, auto)
  then obtain pns body where sm: "(clinit, Static, [], Void, pns, body) \<in> set ms"
    by(unfold wf_clinit_def) auto
  then have "P \<turnstile> C sees clinit,Static:[] \<rightarrow> Void = (pns,body) in C"
    using mdecl_visible[OF wf sP sm] by simp
  then show ?thesis using WTrtSCall proc by simp
qed

declare [[ML_print_depth =1000]]

subsection\<open>Basic preservation lemmas\<close>

text\<open> First some easy preservation lemmas. \<close>
  
ML \<open>@{thms red_reds_inducts} |> length
\<close> 
thm WTrt.cases
      
theorem red_preserves_hconf:
  "P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle> \<Longrightarrow> (\<And>T E. \<lbrakk> P,E,h,sh \<turnstile> e : T; P \<turnstile> h \<surd> \<rbrakk> \<Longrightarrow> P \<turnstile> h' \<surd>)"
and reds_preserves_hconf:
  "P \<turnstile> \<langle>es,(h,l,sh),b\<rangle> [\<rightarrow>] \<langle>es',(h',l',sh'),b'\<rangle> \<Longrightarrow> (\<And>Ts E. \<lbrakk> P,E,h,sh \<turnstile> es [:] Ts; P \<turnstile> h \<surd> \<rbrakk> \<Longrightarrow> P \<turnstile> h' \<surd>)"
(*<*)      
ML_val \<open>val _ =  MinLang_Translator.translate'm  @{Isar.state}
(File.read (Path.explode "./Translator/t24.txt"))\<close>
(*>*)

sorry

























theorem red_preserves_lconf:
  "P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle> \<Longrightarrow>
  (\<And>T E. \<lbrakk> P,E,h,sh \<turnstile> e:T; P,h \<turnstile> l (:\<le>) E \<rbrakk> \<Longrightarrow> P,h' \<turnstile> l' (:\<le>) E)"
and reds_preserves_lconf:
  "P \<turnstile> \<langle>es,(h,l,sh),b\<rangle> [\<rightarrow>] \<langle>es',(h',l',sh'),b'\<rangle> \<Longrightarrow>
  (\<And>Ts E. \<lbrakk> P,E,h,sh \<turnstile> es[:]Ts; P,h \<turnstile> l (:\<le>) E \<rbrakk> \<Longrightarrow> P,h' \<turnstile> l' (:\<le>) E)"

(*<*) 
ML_val \<open>val _ =  MinLang_Translator.translate'm  @{Isar.state}
(File.read (Path.explode "./Translator/t25.txts"))\<close>
(*>*)
sorry
 
       
        
theorem red_preserves_shconf:
  "P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle> \<Longrightarrow> (\<And>T E. \<lbrakk> P,E,h,sh \<turnstile> e : T; P,h \<turnstile>\<^sub>s sh \<surd> \<rbrakk> \<Longrightarrow> P,h' \<turnstile>\<^sub>s sh' \<surd>)"
and reds_preserves_shconf:
  "P \<turnstile> \<langle>es,(h,l,sh),b\<rangle> [\<rightarrow>] \<langle>es',(h',l',sh'),b'\<rangle> \<Longrightarrow> (\<And>Ts E. \<lbrakk> P,E,h,sh \<turnstile> es [:] Ts; P,h \<turnstile>\<^sub>s sh \<surd> \<rbrakk> \<Longrightarrow> P,h' \<turnstile>\<^sub>s sh' \<surd>)"
(*<*)   
ML_val \<open>val _ =  MinLang_Translator.translate'm  @{Isar.state}
(File.read (Path.explode "./Translator/t26.txt"))\<close>
(*>*) 
sorry






theorem assumes wf: "wwf_J_prog P"
shows red_preserves_iconf:
  "P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle> \<Longrightarrow> iconf sh e \<longrightarrow> iconf sh' e'"
and reds_preserves_iconf:
  "P \<turnstile> \<langle>es,(h,l,sh),b\<rangle> [\<rightarrow>] \<langle>es',(h',l',sh'),b'\<rangle> \<Longrightarrow> iconfs sh es \<longrightarrow> iconfs sh' es'"
(*<*)                 
      
ML_val \<open>val _ =  MinLang_Translator.translate'm  @{Isar.state} 
(File.read (Path.explode "./Translator/t5.txt"))\<close>
sorry
(*>*)

  
lemma Seq_bconf_preserve_aux:
assumes "P \<turnstile> \<langle>e,(h, l, sh),b\<rangle> \<rightarrow> \<langle>e',(h', l', sh'),b'\<rangle>" and "P,sh \<turnstile>\<^sub>b (e;; e\<^sub>2,b) \<surd>"
  and "P,sh \<turnstile>\<^sub>b (e::expr,b) \<surd> \<longrightarrow> P,sh' \<turnstile>\<^sub>b (e'::expr,b') \<surd>"
shows "P,sh' \<turnstile>\<^sub>b (e';;e\<^sub>2,b') \<surd>" 
ML_val \<open>val _ =  MinLang_Translator.translate'm  @{Isar.state} 
(File.read (Path.explode "./Translator/t27.txts"))\<close>
 

sorry












  

theorem red_preserves_bconf:
  "P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle> \<Longrightarrow> iconf sh e \<Longrightarrow> P,sh \<turnstile>\<^sub>b (e,b) \<surd> \<Longrightarrow> P,sh' \<turnstile>\<^sub>b (e',b') \<surd>"
and reds_preserves_bconf:
  "P \<turnstile> \<langle>es,(h,l,sh),b\<rangle> [\<rightarrow>] \<langle>es',(h',l',sh'),b'\<rangle> \<Longrightarrow> iconfs sh es \<Longrightarrow> P,sh \<turnstile>\<^sub>b (es,b) \<surd> \<Longrightarrow> P,sh' \<turnstile>\<^sub>b (es',b') \<surd>"
(*<*)       
ML_val \<open>val _ =  MinLang_Translator.translate'm  @{Isar.state} 
(File.read (Path.explode "./Translator/t28.txt"))\<close>
sorry














text\<open> Preservation of definite assignment more complex and requires a
few lemmas first. \<close>

lemma [iff]: "\<And>A. \<lbrakk> length Vs = length Ts; length vs = length Ts\<rbrakk> \<Longrightarrow>
 \<D> (blocks (Vs,Ts,vs,e)) A = \<D> e (A \<squnion> \<lfloor>set Vs\<rfloor>)"
(*<*)
by (induct Vs Ts vs e rule:blocks_induct)
   (simp_all add:hyperset_defs)
(*>*)


lemma red_lA_incr: "P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle>
   \<Longrightarrow> \<lfloor>dom l\<rfloor> \<squnion> \<A> e \<sqsubseteq>  \<lfloor>dom l'\<rfloor> \<squnion> \<A> e'"
and reds_lA_incr: "P \<turnstile> \<langle>es,(h,l,sh),b\<rangle> [\<rightarrow>] \<langle>es',(h',l',sh'),b'\<rangle>
   \<Longrightarrow> \<lfloor>dom l\<rfloor> \<squnion> \<A>s es \<sqsubseteq>  \<lfloor>dom l'\<rfloor> \<squnion> \<A>s es'"
(*<*)
ML_val \<open>val _ =  MinLang_Translator.translate'm  @{Isar.state} 
(File.read (Path.explode "./Translator/t29.txt"))\<close>
sorry
(*>*)
 
text\<open> Now preservation of definite assignment. \<close>

lemma assumes wf: "wf_J_prog P"
shows red_preserves_defass:
  "P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle> \<Longrightarrow> \<D> e \<lfloor>dom l\<rfloor> \<Longrightarrow> \<D> e' \<lfloor>dom l'\<rfloor>"
and "P \<turnstile> \<langle>es,(h,l,sh),b\<rangle> [\<rightarrow>] \<langle>es',(h',l',sh'),b'\<rangle> \<Longrightarrow> \<D>s es \<lfloor>dom l\<rfloor> \<Longrightarrow> \<D>s es' \<lfloor>dom l'\<rfloor>"
(*<*)
ML_val \<open>val _ =  MinLang_Translator.translate'm  @{Isar.state} 
(File.read (Path.explode "./Translator/t30.txts"))\<close>


 apply (induct rule:red_reds_inducts)
(*95 subgoals*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
mproof
case BinOpRed1:  BinOpRed1
show "?case"
using BinOpRed1 apply ((auto elim!: D_mono[OF red_lA_incr])[1])
.
mqed
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
mproof
case FAssRed1:  FAssRed1
show "?case"
using FAssRed1 apply ((auto elim!: D_mono[OF red_lA_incr])[1])
.
mqed
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
mproof
case CallObj:  CallObj
show "?case"
using CallObj apply ((auto elim!: Ds_mono[OF red_lA_incr])[1])
.
mqed
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
mproof
case RedCall:  RedCall
show "?case"
using RedCall apply ((auto dest!:sees_wf_mdecl[OF wf] simp:wf_mdecl_def hyperset_defs elim!:D_mono')[1])
.
mqed
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
mproof
case RedSCall:  RedSCall
show "?case"
using RedSCall apply ((auto dest!:sees_wf_mdecl[OF wf] simp:wf_mdecl_def hyperset_defs elim!:D_mono')[1])
.
mqed
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
mproof
case SCallInitRed:  SCallInitRed
show "?case"
using SCallInitRed apply ((auto simp:hyperset_defs Ds_Vals)[1])
.
mqed
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
mproof
case BlockRedNone:  BlockRedNone
show "?case"
using BlockRedNone apply ((auto simp:hyperset_defs elim!:D_mono' simp del:fun_upd_apply)[1])
.
mqed
(*NEXT*)
mproof
case BlockRedSome:  BlockRedSome
show "?case"
using BlockRedSome apply ((auto simp:hyperset_defs elim!:D_mono' simp del:fun_upd_apply)[1])
.
mqed
(*NEXT*)
mproof
case InitBlockRed:  InitBlockRed
show "?case"
using InitBlockRed apply ((auto simp:hyperset_defs elim!:D_mono' simp del:fun_upd_apply)[1])
.
mqed
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
mproof
case SeqRed:  SeqRed
show "?case"
using SeqRed apply ((auto elim!: D_mono[OF red_lA_incr])[1])
.
mqed
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
mproof
case CondRed:  CondRed
show "?case"
using CondRed apply ((auto elim!: D_mono[OF red_lA_incr])[1])
.
mqed
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
mproof
case RedWhile:  RedWhile
show "?case"
using RedWhile apply ((auto simp:hyperset_defs elim!:D_mono')[1])
.
mqed
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
mproof
case TryRed:  TryRed
show "?case"
using TryRed apply ((fastforce dest:red_lcl_incr intro:D_mono' simp:hyperset_defs)[1])
.
mqed
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
mproof
case ListRed1:  ListRed1
show "?case"
using ListRed1 apply ((auto elim!: Ds_mono[OF red_lA_incr])[1])
.
mqed
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
mproof
case RedInit:  RedInit
show "?case"
using RedInit apply ((auto intro: D_mono' simp: hyperset_defs)[1])
.
mqed
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
mproof
case RInitRed:   (RInitRed e h l sh b e' h' l' sh' b' C Cs e\<^sub>0)
show "?case"
using RInitRed apply ((auto simp:hyperset_defs dest:red_lcl_incr elim!:D_mono')[1])
.
mqed
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*NEXT*)
 apply ((auto simp:hyperset_defs)[1])
(*end 95 subgoals*)
.


(*>*)


text\<open> Combining conformance of heap, static heap, and local variables: \<close>

definition sconf :: "J_prog \<Rightarrow> env \<Rightarrow> state \<Rightarrow> bool"   ("_,_ \<turnstile> _ \<surd>"   [51,51,51]50)
where
  "P,E \<turnstile> s \<surd>  \<equiv>  let (h,l,sh) = s in P \<turnstile> h \<surd> \<and> P,h \<turnstile> l (:\<le>) E \<and> P,h \<turnstile>\<^sub>s sh \<surd>"

lemma red_preserves_sconf:
  "\<lbrakk> P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle>; P,E,hp s,shp s \<turnstile> e : T; P,E \<turnstile> s \<surd> \<rbrakk> \<Longrightarrow> P,E \<turnstile> s' \<surd>"
(*<*)
by(fastforce intro:red_preserves_hconf red_preserves_lconf red_preserves_shconf
            simp add:sconf_def)
(*>*)

lemma reds_preserves_sconf:
  "\<lbrakk> P \<turnstile> \<langle>es,s,b\<rangle> [\<rightarrow>] \<langle>es',s',b'\<rangle>; P,E,hp s,shp s \<turnstile> es [:] Ts; P,E \<turnstile> s \<surd> \<rbrakk> \<Longrightarrow> P,E \<turnstile> s' \<surd>"
(*<*)
by(fastforce intro:reds_preserves_hconf reds_preserves_lconf reds_preserves_shconf
            simp add:sconf_def)
(*>*)


subsection "Subject reduction"
 
lemma wt_blocks:
 "\<And>E. \<lbrakk> length Vs = length Ts; length vs = length Ts \<rbrakk> \<Longrightarrow>
       (P,E,h,sh \<turnstile> blocks(Vs,Ts,vs,e) : T) =
       (P,E(Vs[\<mapsto>]Ts),h,sh \<turnstile> e:T \<and> (\<exists>Ts'. map (typeof\<^bsub>h\<^esub>) vs = map Some Ts' \<and> P \<turnstile> Ts' [\<le>] Ts))"
(*<*) 
proof(induct Vs Ts vs e rule:blocks_induct)
  case (1 V Vs T Ts v vs e)
  then show ?case by(force simp add:rel_list_all2_Cons2)
qed simp_all
(*>*) 
      
theorem assumes wf: "wf_J_prog P"
shows subject_reduction2: "P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle> \<Longrightarrow>
  (\<And>E T. \<lbrakk> P,E \<turnstile> (h,l,sh) \<surd>; iconf sh e; P,E,h,sh \<turnstile> e:T \<rbrakk>
           \<Longrightarrow> \<exists>T'. P,E,h',sh' \<turnstile> e':T' \<and> P \<turnstile> T' \<le> T)"
and subjects_reduction2: "P \<turnstile> \<langle>es,(h,l,sh),b\<rangle> [\<rightarrow>] \<langle>es',(h',l',sh'),b'\<rangle> \<Longrightarrow>
  (\<And>E Ts. \<lbrakk> P,E \<turnstile> (h,l,sh) \<surd>; iconfs sh es; P,E,h,sh \<turnstile> es [:] Ts \<rbrakk>
            \<Longrightarrow> \<exists>Ts'. P,E,h',sh' \<turnstile> es' [:] Ts' \<and> P \<turnstile> Ts' [\<le>] Ts)"
(*<*)    
ML_val \<open>val _ =  MinLang_Translator.translate'm  @{Isar.state} 
(File.read (Path.explode "./Translator/t31.txt "))\<close>
(*>*)
term 1




 apply (induct rule:red_reds_inducts)
(*95 subgoals*)

mproof
case RedNew:  RedNew
show "?case"
using RedNew apply ((auto simp: blank_def)[1])
.
mqed
(*NEXT*)
mproof
case RedNewFail:  RedNewFail
show "?case"
using RedNewFail apply ((unfold sconf_def hconf_def)[1])
 apply ((fastforce elim!:typeof_OutOfMemory)[1])
.
mqed
(*NEXT*)
 apply ((fastforce)[1])
(*NEXT*)
 apply ((fastforce)[1])
(*NEXT*)
mproof
case CastRed:  CastRed
show "?case"
using CastRed apply ((clarsimp simp:is_refT_def)[1])
 apply ((blast intro: widens_trans dest!:widen_Class[THEN iffD1])[1])
.
mqed
(*NEXT*)
 apply ((fastforce)[1])
(*NEXT*)
 apply ((fastforce)[1])
(*NEXT*)
mproof
case RedCastFail:  RedCastFail
show "?case"
using RedCastFail apply ((unfold sconf_def hconf_def)[1])
 apply ((fastforce elim!:typeof_ClassCast)[1])
.
mqed
(*NEXT*)
mproof
case BinOpRed1:   (BinOpRed1 e\<^sub>1 h l sh b e\<^sub>1' h' l' sh' b' bop e\<^sub>2)
have red: "P \<turnstile> \<langle>e\<^sub>1,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e\<^sub>1',(h',l',sh'),b'\<rangle>" and IH: "\<And>E T. \<lbrakk>P,E \<turnstile> (h,l,sh) \<surd>; iconf sh e\<^sub>1; P,E,h,sh \<turnstile> e\<^sub>1:T\<rbrakk>
                 \<Longrightarrow> \<exists>U. P,E,h',sh' \<turnstile> e\<^sub>1' : U \<and> P \<turnstile> U \<le> T" and conf: "P,E \<turnstile> (h,l,sh) \<surd>" and iconf: "iconf sh (e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2)" and wt: "P,E,h,sh \<turnstile> e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2 : T"
(*5 subgoals*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*end 5 subgoals*)
.
have val: "val_of e\<^sub>1 = None"
using red iconf val_no_step apply ((auto)[1])
.
have iconf1: "iconf sh e\<^sub>1" and nsub_RI2: "\<not>sub_RI e\<^sub>2"
(*2 subgoals*)
using val iconf apply ((simp)[1])
(*NEXT*)
using val iconf apply ((simp)[1])
(*end 2 subgoals*)
.
have fact4: "P,E,h',sh' \<turnstile> e\<^sub>1' \<guillemotleft>bop\<guillemotright> e\<^sub>2 : T"
 apply ((cases bop)[1])
(*2 subgoals*)
mproof
assume fact5[simp]: "bop = Eq"
note fact'171[simp] = fact5
obtain T\<^sub>1 and T\<^sub>2 where fact6[simp]: "T = Boolean" and "wt\<^sub>1": "P,E,h,sh \<turnstile> e\<^sub>1 : T\<^sub>1" and "wt\<^sub>2": "P,E,h,sh \<turnstile> e\<^sub>2 : T\<^sub>2"
using wt apply ((auto)[1])
.
show "P,E,h',sh' \<turnstile> e\<^sub>1' \<guillemotleft>bop\<guillemotright> e\<^sub>2 : T"
using WTrt_hext_shext_mono[OF wt\<^sub>2 red_hext_incr [ OF red ] red_shext_incr [ OF red wt\<^sub>1 ] nsub_RI2] IH[OF conf iconf1 wt\<^sub>1] apply ((auto)[1])
.
mqed
(*NEXT*)
mproof
assume fact8[simp]: "bop = Add"
note fact'172[simp] = fact8
have fact9[simp]: "T = Integer" and "wt\<^sub>1": "P,E,h,sh \<turnstile> e\<^sub>1 : Integer" and "wt\<^sub>2": "P,E,h,sh \<turnstile> e\<^sub>2 : Integer"
(*3 subgoals*)
using wt apply ((auto)[1])
(*NEXT*)
using wt apply ((auto)[1])
(*NEXT*)
using wt apply ((auto)[1])
(*end 3 subgoals*)
.
show "P,E,h',sh' \<turnstile> e\<^sub>1' \<guillemotleft>bop\<guillemotright> e\<^sub>2 : T"
using WTrt_hext_shext_mono[OF wt\<^sub>2 red_hext_incr [ OF red ] red_shext_incr [ OF red wt\<^sub>1 ] nsub_RI2] IH[OF conf iconf1 wt\<^sub>1] apply ((auto)[1])
.
mqed
(*end 2 subgoals*)
.
show "?case"
using fact4 apply ((auto)[1])
.
mqed
(*NEXT*)
mproof
case BinOpRed2:   (BinOpRed2 e\<^sub>2 h l sh b e\<^sub>2' h' l' sh' b' v\<^sub>1 bop)
have red: "P \<turnstile> \<langle>e\<^sub>2,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e\<^sub>2',(h',l',sh'),b'\<rangle>" and IH: "\<And>E T. \<lbrakk>P,E \<turnstile> (h,l,sh) \<surd>; iconf sh e\<^sub>2; P,E,h,sh \<turnstile> e\<^sub>2:T\<rbrakk>
                 \<Longrightarrow> \<exists>U. P,E,h',sh' \<turnstile> e\<^sub>2' : U \<and> P \<turnstile> U \<le> T" and conf: "P,E \<turnstile> (h,l,sh) \<surd>" and iconf: "iconf sh (Val v\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2)" and wt: "P,E,h,sh \<turnstile> (Val v\<^sub>1) \<guillemotleft>bop\<guillemotright> e\<^sub>2 : T"
(*5 subgoals*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*end 5 subgoals*)
.
have iconf2: "iconf sh e\<^sub>2"
using iconf apply ((simp)[1])
.
have fact12: "P,E,h',sh' \<turnstile> (Val v\<^sub>1) \<guillemotleft>bop\<guillemotright> e\<^sub>2' : T"
 apply ((cases bop)[1])
(*2 subgoals*)
mproof
assume fact13[simp]: "bop = Eq"
note fact'173[simp] = fact13
obtain T\<^sub>1 and T\<^sub>2 where fact14[simp]: "T = Boolean" and "wt\<^sub>1": "P,E,h,sh \<turnstile> Val v\<^sub>1 : T\<^sub>1" and "wt\<^sub>2": "P,E,h,sh \<turnstile> e\<^sub>2:T\<^sub>2"
using wt apply ((auto)[1])
.
show "P,E,h',sh' \<turnstile> Val v\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2' : T"
using IH[OF conf iconf2 wt\<^sub>2] WTrt_hext_mono[OF wt\<^sub>1 red_hext_incr [ OF red ]] apply ((auto)[1])
.
mqed
(*NEXT*)
mproof
assume fact16[simp]: "bop = Add"
note fact'174[simp] = fact16
have fact17[simp]: "T = Integer" and "wt\<^sub>1": "P,E,h,sh \<turnstile> Val v\<^sub>1 : Integer" and "wt\<^sub>2": "P,E,h,sh \<turnstile> e\<^sub>2 : Integer"
(*3 subgoals*)
using wt apply ((auto)[1])
(*NEXT*)
using wt apply ((auto)[1])
(*NEXT*)
using wt apply ((auto)[1])
(*end 3 subgoals*)
.
show "P,E,h',sh' \<turnstile> Val v\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2' : T"
using IH[OF conf iconf2 wt\<^sub>2] WTrt_hext_mono[OF wt\<^sub>1 red_hext_incr [ OF red ]] apply ((auto)[1])
.
mqed
(*end 2 subgoals*)
.
show "?case"
using fact12 apply ((auto)[1])
.
mqed
(*NEXT*)
mproof
case RedBinOp:   (RedBinOp bop)
show "?case"
using RedBinOp apply ((cases bop)[1])
(*2 subgoals*)
mproof
case Eq:  Eq
show "?thesis"
using Eq RedBinOp apply ((auto)[1])
.
mqed
(*NEXT*)
mproof
case Add:  Add
show "?thesis"
using Add RedBinOp apply ((auto)[1])
.
mqed
(*end 2 subgoals*)
.
mqed
(*NEXT*)
mproof
case RedVar:  RedVar
show "?case"
using RedVar apply ((fastforce simp:sconf_def lconf_def conf_def)[1])
.
mqed
(*NEXT*)
mproof
case LAssRed:   (LAssRed e h l sh b e' h' l' sh' b' V)
obtain Te where Te: "P,E,h,sh \<turnstile> e : Te \<and> P \<turnstile> Te \<le> the(E V)"
using LAssRed.prems(3) apply ((auto)[1])
.
have wide: "P \<turnstile> Te \<le> the(E V)"
using Te LAssRed apply ((simp)[1])
.
have fact24: "\<exists>T'. P,E,h',sh' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> Te"
using wide LAssRed.hyps(2) LAssRed.prems(1,2) Te widen_trans[OF _ wide] apply ((auto)[1])
.
obtain T' where wt: "P,E,h',sh' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> Te"
using fact24 apply ((clarsimp)[1])
.
have fact25: "P,E,h',sh' \<turnstile> V:=e' : Void"
using LAssRed wt widen_trans[OF _ wide] apply ((auto)[1])
.
show "?case"
using fact25 LAssRed apply ((rule_tac x = Void in exI)[1])
 apply ((auto)[1])
.
mqed
(*NEXT*)
 apply ((fastforce)[1])
(*NEXT*)
mproof
case FAccRed:   (FAccRed e h l sh b e' h' l' sh' b' F D)
have IH: "\<And>E T. \<lbrakk>P,E \<turnstile> (h,l,sh) \<surd>; iconf sh e; P,E,h,sh \<turnstile> e : T\<rbrakk>
                 \<Longrightarrow> \<exists>U. P,E,h',sh' \<turnstile> e' : U \<and> P \<turnstile> U \<le> T" and conf: "P,E \<turnstile> (h,l,sh) \<surd>" and iconf: "iconf sh (e\<bullet>F{D})" and wt: "P,E,h,sh \<turnstile> e\<bullet>F{D} : T"
(*4 subgoals*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*end 4 subgoals*)
.
have iconf': "iconf sh e"
using iconf apply ((simp)[1])
.
have fact27: "?case" if wte: "P,E,h,sh \<turnstile> e : Class C" and has: "P \<turnstile> C has F,NonStatic:T in D" for C
mproof
obtain U where wte': "P,E,h',sh' \<turnstile> e' : U" and UsubC: "P \<turnstile> U \<le> Class C"
using IH[OF conf iconf' wte] apply ((auto)[1])
.
have fact28: "?case" if fact29: "U = NT"
using fact29 wte' apply ((blast intro:WTrtFAccNT widen_refl)[1])
.
have fact31: "?case" if U: "U = Class C'" and C'subC: "P \<turnstile> C' \<preceq>\<^sup>* C" for C'
using has_field_mono[OF has C'subC] wte' U apply ((blast intro:WTrtFAcc)[1])
.
show fact27: "?case"
using fact28 fact31 UsubC apply ((simp add: widen_Class)[1])
 apply ((blast)[1])
.
mqed
.
have fact34: "?case" if fact35: "P,E,h,sh \<turnstile> e : NT"
mproof
have fact36: "P,E,h',sh' \<turnstile> e' : NT"
using fact35 IH[OF conf iconf'] apply ((fastforce)[1])
.
show fact34: "?case"
using fact36 apply ((fastforce intro:WTrtFAccNT widen_refl)[1])
.
mqed
.
show "?case"
using fact27 fact34 wt apply ((blast)[1])
.
mqed
(*NEXT*)
mproof
case RedFAcc:  RedFAcc
show "?case"
using RedFAcc apply ((fastforce simp:sconf_def hconf_def oconf_def conf_def has_field_def dest:has_fields_fun)[1])
.
mqed
(*NEXT*)
mproof
case RedFAccNull:  RedFAccNull
show "?case"
using RedFAccNull apply ((fastforce intro: widen_refl WTThrow[OF WTVal] elim!: typeof_NullPointer simp: sconf_def hconf_def)[1])
.
mqed
(*NEXT*)
 apply ((fastforce)[1])
(*NEXT*)
mproof
case RedFAccStatic:  RedFAccStatic
show "?case"
using RedFAccStatic apply ((fastforce intro: WTrtThrow[OF WTrtVal] elim!: typeof_IncompatibleClassChangeError simp: sconf_def hconf_def)[1])
.
mqed
(*NEXT*)
mproof
case RedSFAcc:   (RedSFAcc C F t D sh sfs i v h l es)
have fact43: "P \<turnstile> C has F,Static:T in D"
using RedSFAcc apply ((fast)[1])
.
have dM: "P \<turnstile> D has F,Static:T in D"
using fact43 apply ((rule has_field_idemp)[1])
.
show "?case"
using dM RedSFAcc apply ((fastforce simp:sconf_def shconf_def soconf_def conf_def)[1])
.
mqed
(*NEXT*)
mproof
case SFAccInitDoneRed:  SFAccInitDoneRed
show "?case"
using SFAccInitDoneRed apply ((meson widen_refl)[1])
.
mqed
(*NEXT*)
mproof
case SFAccInitRed:   (SFAccInitRed C F t D sh h l E T)
have fact46: "is_class P D"
using SFAccInitRed.hyps(1) apply ((rule has_field_is_class')[1])
.
have fact47: "P,E,h,sh \<turnstile> INIT D ([D],False) \<leftarrow> C\<bullet>\<^sub>sF{D} : T \<and> P \<turnstile> T \<le> T"
using fact46 SFAccInitRed WTrtInit[OF SFAccInitRed.prems ( 3 )] apply ((clarsimp)[1])
.
show "?case"
using fact47 apply ((rule exI)[1])
.
mqed
(*NEXT*)
mproof
case RedSFAccNone:  RedSFAccNone
show "?case"
using RedSFAccNone apply ((fastforce intro: WTrtThrow[OF WTrtVal] elim!: typeof_NoSuchFieldError simp: sconf_def hconf_def)[1])
.
mqed
(*NEXT*)
mproof
case RedSFAccNonStatic:  RedSFAccNonStatic
show "?case"
using RedSFAccNonStatic apply ((fastforce intro: WTrtThrow[OF WTrtVal] elim!: typeof_IncompatibleClassChangeError simp: sconf_def hconf_def)[1])
.
mqed
(*NEXT*)
mproof
case FAssRed1:   (FAssRed1 e h l sh b e' h' l' sh' b' F D e\<^sub>2)
have red: "P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle>" and IH: "\<And>E T. \<lbrakk>P,E \<turnstile> (h,l,sh) \<surd>; iconf sh e; P,E,h,sh \<turnstile> e : T\<rbrakk>
                 \<Longrightarrow> \<exists>U. P,E,h',sh' \<turnstile> e' : U \<and> P \<turnstile> U \<le> T" and conf: "P,E \<turnstile> (h,l,sh) \<surd>" and iconf: "iconf sh (e\<bullet>F{D} := e\<^sub>2)" and wt: "P,E,h,sh \<turnstile> e\<bullet>F{D}:=e\<^sub>2 : T"
(*5 subgoals*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*end 5 subgoals*)
.
have val: "val_of e = None"
using red iconf val_no_step apply ((auto)[1])
.
have iconf': "iconf sh e" and nsub_RI2: "\<not>sub_RI e\<^sub>2"
(*2 subgoals*)
using val iconf apply ((simp)[1])
(*NEXT*)
using val iconf apply ((simp)[1])
(*end 2 subgoals*)
.
have void: "T = Void"
using wt apply ((blast)[1])
.
have fact50: "?case" if wt': "P,E,h,sh \<turnstile> e : NT"
mproof
have fact51: "P,E,h',sh' \<turnstile> e' : NT"
using wt' IH[OF conf iconf'] apply ((fastforce)[1])
.
obtain T\<^sub>2 where fact52: "P,E,h,sh \<turnstile> e\<^sub>2 : T\<^sub>2"
using wt apply ((auto)[1])
.
have fact53: "P,E,h',sh' \<turnstile> e\<^sub>2 : T\<^sub>2"
using fact52 red_hext_incr[OF red] red_shext_incr[OF red wt'] nsub_RI2 apply ((rule WTrt_hext_shext_mono)[1])
.
show fact50: "?case"
using fact51 fact53 void apply ((blast intro!:WTrtFAssNT)[1])
.
mqed
.
have fact55: "?case" if "wt\<^sub>1": "P,E,h,sh \<turnstile> e : Class C" and "wt\<^sub>2": "P,E,h,sh \<turnstile> e\<^sub>2 : T\<^sub>2" and has: "P \<turnstile> C has F,NonStatic:TF in D" and sub: "P \<turnstile> T\<^sub>2 \<le> TF" for C and TF and T\<^sub>2
mproof
obtain U where "wt\<^sub>1'": "P,E,h',sh' \<turnstile> e' : U" and UsubC: "P \<turnstile> U \<le> Class C"
using IH[OF conf iconf' wt\<^sub>1] apply ((blast)[1])
.
have "wt\<^sub>2'": "P,E,h',sh' \<turnstile> e\<^sub>2 : T\<^sub>2"
 apply ((rule WTrt_hext_shext_mono[OF wt\<^sub>2 red_hext_incr[OF red] red_shext_incr[OF red wt\<^sub>1] nsub_RI2])[1])
.
have fact56: "?case" if fact57: "U = NT"
using "wt\<^sub>1'" "wt\<^sub>2'" void fact57 apply ((blast intro!:WTrtFAssNT)[1])
.
have fact59: "?case" if UClass: "U = Class C'" and subclass: "P \<turnstile> C' \<preceq>\<^sup>* C" for C'
mproof
have fact60: "P,E,h',sh' \<turnstile> e' : Class C'"
using "wt\<^sub>1'" UClass apply ((auto)[1])
.
have fact61: "P \<turnstile> C' has F,NonStatic:TF in D"
 apply ((rule has_field_mono[OF has "subclass"])[1])
.
show fact59: "?case"
using fact60 fact61 "wt\<^sub>2'" sub void apply ((blast intro:WTrtFAss)[1])
.
mqed
.
show fact55: "?case"
using fact56 fact59 UsubC apply ((auto simp add:widen_Class)[1])
.
mqed
.
show "?case"
using fact50 fact55 wt apply ((blast)[1])
.
mqed
(*NEXT*)
mproof
case FAssRed2:   (FAssRed2 e\<^sub>2 h l sh b e\<^sub>2' h' l' sh' b' v F D)
have red: "P \<turnstile> \<langle>e\<^sub>2,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e\<^sub>2',(h',l',sh'),b'\<rangle>" and IH: "\<And>E T. \<lbrakk>P,E \<turnstile> (h,l,sh) \<surd>; iconf sh e\<^sub>2; P,E,h,sh \<turnstile> e\<^sub>2 : T\<rbrakk>
                 \<Longrightarrow> \<exists>U. P,E,h',sh' \<turnstile> e\<^sub>2' : U \<and> P \<turnstile> U \<le> T" and conf: "P,E \<turnstile> (h,l,sh) \<surd>" and iconf: "iconf sh (Val v\<bullet>F{D} := e\<^sub>2)" and wt: "P,E,h,sh \<turnstile> Val v\<bullet>F{D}:=e\<^sub>2 : T"
(*5 subgoals*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*end 5 subgoals*)
.
have iconf2: "iconf sh e\<^sub>2"
using iconf apply ((simp)[1])
.
have fact65[simp]: "T = Void"
using wt apply ((auto)[1])
.
show "?case"
using wt apply ((rule WTrt_elim_cases)[1])
(*2 subgoals*)
mproof
fix C and TF and T\<^sub>2
assume "wt\<^sub>1": "P,E,h,sh \<turnstile> Val v : Class C" and has: "P \<turnstile> C has F,NonStatic:TF in D" and "wt\<^sub>2": "P,E,h,sh \<turnstile> e\<^sub>2 : T\<^sub>2" and TsubTF: "P \<turnstile> T\<^sub>2 \<le> TF"
have "wt\<^sub>1'": "P,E,h',sh' \<turnstile> Val v : Class C"
using WTrt_hext_mono[OF wt\<^sub>1 red_hext_incr [ OF red ]] apply ((auto)[1])
.
obtain T\<^sub>2' where "wt\<^sub>2'": "P,E,h',sh' \<turnstile> e\<^sub>2' : T\<^sub>2'" and T'subT: "P \<turnstile> T\<^sub>2' \<le> T\<^sub>2"
using IH[OF conf iconf2 wt\<^sub>2] apply ((blast)[1])
.
have fact67: "P,E,h',sh' \<turnstile> Val v\<bullet>F{D}:=e\<^sub>2' : Void"
 apply ((rule WTrtFAss[OF wt\<^sub>1' has wt\<^sub>2' widen_trans[OF T'subT TsubTF]])[1])
.
show "?case"
using fact67 apply ((auto)[1])
.
mqed
(*NEXT*)
mproof
fix T\<^sub>2
assume null: "P,E,h,sh \<turnstile> Val v : NT" and "wt\<^sub>2": "P,E,h,sh \<turnstile> e\<^sub>2 : T\<^sub>2"
have fact69: "v = Null"
using null apply ((simp)[1])
.
obtain T\<^sub>2' where fact70: "P,E,h',sh' \<turnstile> e\<^sub>2' : T\<^sub>2' \<and> P \<turnstile> T\<^sub>2' \<le> T\<^sub>2"
using IH[OF conf iconf2 wt\<^sub>2] apply ((blast)[1])
.
show "\<exists>T'. P,E,h',sh' \<turnstile> Val v\<bullet>F{D} := e\<^sub>2' : T' \<and> P \<turnstile> T' \<le> T"
using fact69 fact70 apply ((fastforce intro:WTrtFAssNT)[1])
.
mqed
(*end 2 subgoals*)
.
mqed
(*NEXT*)
mproof
case RedFAss:  RedFAss
show "?case"
using RedFAss apply ((auto simp del:fun_upd_apply)[1])
.
mqed
(*NEXT*)
mproof
case RedFAssNull:  RedFAssNull
show "?case"
using RedFAssNull apply ((fastforce intro: WTThrow[OF WTVal] elim!:typeof_NullPointer simp:sconf_def hconf_def)[1])
.
mqed
(*NEXT*)
 apply ((fastforce)[1])
(*NEXT*)
mproof
case RedFAssStatic:  RedFAssStatic
show "?case"
using RedFAssStatic apply ((fastforce intro: WTrtThrow[OF WTrtVal] elim!: typeof_IncompatibleClassChangeError simp: sconf_def hconf_def)[1])
.
mqed
(*NEXT*)
mproof
case SFAssRed:   (SFAssRed e h l sh b e' h' l' sh' b' C F D E T)
have IH: "\<And>E T. \<lbrakk>P,E \<turnstile> (h,l,sh) \<surd>; iconf sh e; P,E,h,sh \<turnstile> e : T\<rbrakk>
                 \<Longrightarrow> \<exists>U. P,E,h',sh' \<turnstile> e' : U \<and> P \<turnstile> U \<le> T" and conf: "P,E \<turnstile> (h,l,sh) \<surd>" and iconf: "iconf sh (C\<bullet>\<^sub>sF{D} := e)" and wt: "P,E,h,sh \<turnstile> C\<bullet>\<^sub>sF{D}:=e : T"
(*4 subgoals*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*end 4 subgoals*)
.
have iconf': "iconf sh e"
using iconf apply ((simp)[1])
.
have fact75[simp]: "T = Void"
using wt apply ((auto)[1])
.
show "?case"
using wt apply ((rule WTrt_elim_cases)[1])
mproof
fix TF and T1
assume has: "P \<turnstile> C has F,Static:TF in D" and wt1: "P,E,h,sh \<turnstile> e : T1" and TsubTF: "P \<turnstile> T1 \<le> TF"
obtain T' where wt1': "P,E,h',sh' \<turnstile> e' : T'" and T'subT: "P \<turnstile> T' \<le> T1"
using IH[OF conf iconf' wt1] apply ((blast)[1])
.
have fact77: "P,E,h',sh' \<turnstile> C\<bullet>\<^sub>sF{D}:=e' : Void"
 apply ((rule WTrtSFAss[OF wt1' has widen_trans[OF T'subT TsubTF]])[1])
.
show "?case"
using fact77 apply ((auto)[1])
.
mqed
.
mqed
(*NEXT*)
 apply ((fastforce)[1])
(*NEXT*)
mproof
case SFAssInitDoneRed:  SFAssInitDoneRed
show "?case"
using SFAssInitDoneRed apply ((meson widen_refl)[1])
.
mqed
(*NEXT*)
mproof
case SFAssInitRed:   (SFAssInitRed C F t D sh v h l E T)
have fact80: "is_class P D"
using SFAssInitRed.hyps(1) apply ((rule has_field_is_class')[1])
.
have fact81: "P,E,h,sh \<turnstile> INIT D ([D],False) \<leftarrow> C\<bullet>\<^sub>sF{D} := Val v : T \<and> P \<turnstile> T \<le> T"
using fact80 SFAssInitRed WTrtInit[OF SFAssInitRed.prems ( 3 )] apply ((clarsimp)[1])
.
show "?case"
using fact81 apply ((rule exI)[1])
.
mqed
(*NEXT*)
mproof
case RedSFAssNone:  RedSFAssNone
show "?case"
using RedSFAssNone apply ((fastforce intro: WTrtThrow[OF WTrtVal] elim!: typeof_NoSuchFieldError simp: sconf_def hconf_def)[1])
.
mqed
(*NEXT*)
mproof
case RedSFAssNonStatic:  RedSFAssNonStatic
show "?case"
using RedSFAssNonStatic apply ((fastforce intro: WTrtThrow[OF WTrtVal] elim!: typeof_IncompatibleClassChangeError simp: sconf_def hconf_def)[1])
.
mqed
(*NEXT*)
mproof
case CallObj:   (CallObj e h l sh b e' h' l' sh' b' M es)
have red: "P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle>" and IH: "\<And>E T. \<lbrakk>P,E \<turnstile> (h,l,sh) \<surd>; iconf sh e; P,E,h,sh \<turnstile> e : T\<rbrakk>
                 \<Longrightarrow> \<exists>U. P,E,h',sh' \<turnstile> e' : U \<and> P \<turnstile> U \<le> T" and conf: "P,E \<turnstile> (h,l,sh) \<surd>" and iconf: "iconf sh (e\<bullet>M(es))" and wt: "P,E,h,sh \<turnstile> e\<bullet>M(es) : T"
(*5 subgoals*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*end 5 subgoals*)
.
have val: "val_of e = None"
using red iconf val_no_step apply ((auto)[1])
.
have iconf': "iconf sh e" and nsub_RIs: "\<not>sub_RIs es"
(*2 subgoals*)
using val iconf apply ((simp)[1])
(*NEXT*)
using val iconf apply ((simp)[1])
(*end 2 subgoals*)
.
have fact85: "?case" if wt': "P,E,h,sh \<turnstile> e:NT" and wtes: "P,E,h,sh \<turnstile> es [:] Ts" for Ts
mproof
have fact86: "P,E,h',sh' \<turnstile> e' : NT"
using wt' IH[OF conf iconf'] apply ((fastforce)[1])
.
have fact87: "P,E,h',sh' \<turnstile> es [:] Ts"
 apply ((rule WTrts_hext_shext_mono[OF wtes red_hext_incr[OF red] red_shext_incr[OF red wt'] nsub_RIs])[1])
.
show fact85: "?case"
using fact86 fact87 apply ((blast intro!:WTrtCallNT)[1])
.
mqed
.
have fact89: "?case" if wte: "P,E,h,sh \<turnstile> e : Class C" and method: "P \<turnstile> C sees M,NonStatic:Ts\<rightarrow>T = (pns,body) in D" and wtes: "P,E,h,sh \<turnstile> es [:] Us" and subs: "P \<turnstile> Us [\<le>] Ts" for C and D and Ts and Us and pns and body
mproof
obtain U where wte': "P,E,h',sh' \<turnstile> e' : U" and UsubC: "P \<turnstile> U \<le> Class C"
using IH[OF conf iconf' wte] apply ((blast)[1])
.
have fact90: "?case" if fact91: "U = NT"
mproof
have fact92: "P,E,h',sh' \<turnstile> es [:] Us"
 apply ((rule WTrts_hext_shext_mono[OF wtes red_hext_incr[OF red] red_shext_incr[OF red wte] nsub_RIs])[1])
.
show fact90: "?case"
using fact91 fact92 wte' apply ((blast intro!:WTrtCallNT)[1])
.
mqed
.
have fact94: "?case" if UClass: "U = Class C'" and subclass: "P \<turnstile> C' \<preceq>\<^sup>* C" for C'
mproof
have fact95: "P,E,h',sh' \<turnstile> e' : Class C'"
using wte' UClass apply ((auto)[1])
.
obtain Ts' and T' and pns' and body' and D' where method': "P \<turnstile> C' sees M,NonStatic:Ts'\<rightarrow>T' = (pns',body') in D'" and subs': "P \<turnstile> Ts [\<le>] Ts'" and sub': "P \<turnstile> T' \<le> T"
using Call_lemma[OF "method" "subclass" wf] apply ((fast)[1])
.
have fact96: "P,E,h',sh' \<turnstile> es [:] Us"
 apply ((rule WTrts_hext_shext_mono[OF wtes red_hext_incr[OF red] red_shext_incr[OF red wte] nsub_RIs])[1])
.
show fact94: "?case"
using fact95 method' subs' sub' fact96 subs apply ((blast intro:WTrtCall rtrancl_trans widens_trans)[1])
.
mqed
.
show fact89: "?case"
using fact90 fact94 UsubC apply ((auto simp add:widen_Class)[1])
.
mqed
.
show "?case"
using fact85 fact89 wt apply ((auto)[1])
.
mqed
(*NEXT*)
mproof
case CallParams:   (CallParams es h l sh b es' h' l' sh' b' v M)
have reds: "P \<turnstile> \<langle>es,(h,l,sh),b\<rangle> [\<rightarrow>] \<langle>es',(h',l',sh'),b'\<rangle>" and IH: "\<And>E Ts. \<lbrakk>P,E \<turnstile> (h,l,sh) \<surd>; iconfs sh es; P,E,h,sh \<turnstile> es [:] Ts\<rbrakk>
                 \<Longrightarrow> \<exists>Us. P,E,h',sh' \<turnstile> es' [:] Us \<and> P \<turnstile> Us [\<le>] Ts" and conf: "P,E \<turnstile> (h,l,sh) \<surd>" and iconf: "iconf sh (Val v\<bullet>M(es))" and wt: "P,E,h,sh \<turnstile> Val v\<bullet>M(es) : T"
(*5 subgoals*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*end 5 subgoals*)
.
have iconfs: "iconfs sh es"
using iconf apply ((simp)[1])
.
show "?case"
using wt apply ((rule WTrt_elim_cases)[1])
(*2 subgoals*)
mproof
fix C and D and Ts and Us and pns and body
assume wte: "P,E,h,sh \<turnstile> Val v : Class C" and fact101: "P \<turnstile> C sees M,NonStatic:Ts\<rightarrow>T = (pns,body) in D" and wtes: "P,E,h,sh \<turnstile> es [:] Us" and fact102: "P \<turnstile> Us [\<le>] Ts"
have fact103: "P,E,h',sh' \<turnstile> Val v : Class C"
using WTrt_hext_mono[OF wte reds_hext_incr [ OF reds ]] apply ((auto)[1])
.
obtain Us' where fact104: "P,E,h',sh' \<turnstile> es' [:] Us' \<and> P \<turnstile> Us' [\<le>] Us"
using IH[OF conf iconfs wtes] apply ((blast)[1])
.
show "\<exists>T'. P,E,h',sh' \<turnstile> Val v\<bullet>M(es') : T' \<and> P \<turnstile> T' \<le> T"
using wte fact101 wtes fact102 fact103 fact104 apply ((blast intro:WTrtCall widens_trans)[1])
.
mqed
(*NEXT*)
mproof
fix Us
assume null: "P,E,h,sh \<turnstile> Val v : NT" and wtes: "P,E,h,sh \<turnstile> es [:] Us"
have fact106: "v = Null"
using null apply ((simp)[1])
.
obtain Us' where fact107: "P,E,h',sh' \<turnstile> es' [:] Us' \<and> P \<turnstile> Us' [\<le>] Us"
using IH[OF conf iconfs wtes] apply ((blast)[1])
.
show "\<exists>T'. P,E,h',sh' \<turnstile> Val v\<bullet>M(es') : T' \<and> P \<turnstile> T' \<le> T"
using fact106 fact107 apply ((fastforce intro:WTrtCallNT)[1])
.
mqed
(*end 2 subgoals*)
.
mqed
(*NEXT*)
mproof
case RedCall:   (RedCall h a C fs M Ts T pns body D vs l sh b E T')
have hp: "h a = Some(C,fs)" and method: "P \<turnstile> C sees M,NonStatic: Ts\<rightarrow>T = (pns,body) in D" and wt: "P,E,h,sh \<turnstile> addr a\<bullet>M(map Val vs) : T'"
(*3 subgoals*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*end 3 subgoals*)
.
obtain Ts' where wtes: "P,E,h,sh \<turnstile> map Val vs [:] Ts'" and subs: "P \<turnstile> Ts' [\<le>] Ts" and T'isT: "T' = T"
using wt method hp apply ((auto dest:sees_method_fun)[1])
.
have length_vs: "length vs = length Ts"
using wtes subs apply ((fastforce simp:list_all2_iff dest!:WTrts_same_length)[1])
.
obtain T'' where wtabody: "P,[this#pns [\<mapsto>] Class D#Ts] \<turnstile> body :: T''" and T''subT: "P \<turnstile> T'' \<le> T" and length_pns: "length pns = length Ts"
using sees_wf_mdecl[OF wf "method"] apply ((fastforce simp:wf_mdecl_def simp del:map_upds_twist)[1])
.
have fact109: "P,Map.empty(this#pns [\<mapsto>] Class D#Ts),h,sh \<turnstile> body : T''"
using wtabody apply ((rule WT_implies_WTrt)[1])
.
have fact110: "P,E(this#pns [\<mapsto>] Class D#Ts),h,sh \<turnstile> body : T''"
using fact109 apply ((rule WTrt_env_mono)[1])
 apply ((simp)[1])
.
have fact111: "P,E,h,sh \<turnstile> blocks(this#pns, Class D#Ts, Addr a#vs, body) : T''"
using fact110 wtes subs hp sees_method_decl_above[OF "method"] length_vs length_pns apply ((fastforce simp add:wt_blocks rel_list_all2_Cons2)[1])
.
show "?case"
using T''subT T'isT fact111 apply ((blast)[1])
.
mqed
(*NEXT*)
mproof
case RedCallNull:  RedCallNull
show "?case"
using RedCallNull apply ((fastforce intro: WTThrow[OF WTVal] elim!:typeof_NullPointer simp: sconf_def hconf_def)[1])
.
mqed
(*NEXT*)
 apply ((fastforce)[1])
(*NEXT*)
mproof
case RedCallStatic:  RedCallStatic
show "?case"
using RedCallStatic apply ((fastforce intro: WTrtThrow[OF WTrtVal] elim!: typeof_IncompatibleClassChangeError simp: sconf_def hconf_def)[1])
.
mqed
(*NEXT*)
mproof
case SCallParams:   (SCallParams es h l sh b es' h' l' sh' b' C M)
have IH: "\<And>E Ts. \<lbrakk>P,E \<turnstile> (h,l,sh) \<surd>; iconfs sh es; P,E,h,sh \<turnstile> es [:] Ts\<rbrakk>
                 \<Longrightarrow> \<exists>Us. P,E,h',sh' \<turnstile> es' [:] Us \<and> P \<turnstile> Us [\<le>] Ts" and conf: "P,E \<turnstile> (h,l,sh) \<surd>" and iconf: "iconf sh (C\<bullet>\<^sub>sM(es))" and wt: "P,E,h,sh \<turnstile> C\<bullet>\<^sub>sM(es) : T"
(*4 subgoals*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*end 4 subgoals*)
.
have iconfs: "iconfs sh es"
using iconf apply ((simp)[1])
.
show "?case"
using wt apply ((rule WTrt_elim_cases)[1])
mproof
fix D and Ts and Us and pns and body and sfs and vs
assume method: "P \<turnstile> C sees M,Static:Ts\<rightarrow>T = (pns,body) in D" and wtes: "P,E,h,sh \<turnstile> es [:] Us" and us: "P \<turnstile> Us [\<le>] Ts" and clinit: "M = clinit \<longrightarrow> sh D = \<lfloor>(sfs,Processing)\<rfloor> \<and> es = map Val vs"
obtain Us' where es': "P,E,h',sh' \<turnstile> es' [:] Us'" and us': "P \<turnstile> Us' [\<le>] Us"
using IH[OF conf iconfs wtes] apply ((blast)[1])
.
show "\<exists>T'. P,E,h',sh' \<turnstile> C\<bullet>\<^sub>sM(es') : T' \<and> P \<turnstile> T' \<le> T"
 apply ((cases "M = clinit")[1])
(*2 subgoals*)
mproof
case True:  True
show "\<exists>T'. P,E,h',sh' \<turnstile> C\<bullet>\<^sub>sM(es') : T' \<and> P \<turnstile> T' \<le> T"
using True clinit SCallParams.hyps(1) apply ((blast)[1])
.
mqed
(*NEXT*)
mproof
case False:  False
show "\<exists>T'. P,E,h',sh' \<turnstile> C\<bullet>\<^sub>sM(es') : T' \<and> P \<turnstile> T' \<le> T"
using False es' method us us' apply ((blast intro:WTrtSCall widens_trans)[1])
.
mqed
(*end 2 subgoals*)
.
mqed
.
mqed
(*NEXT*)
mproof
case RedSCall:   (RedSCall C M Ts T pns body D vs h l sh E T')
have method: "P \<turnstile> C sees M,Static: Ts\<rightarrow>T = (pns,body) in D" and wt: "P,E,h,sh \<turnstile> C\<bullet>\<^sub>sM(map Val vs) : T'"
(*2 subgoals*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*end 2 subgoals*)
.
obtain Ts' where wtes: "P,E,h,sh \<turnstile> map Val vs [:] Ts'" and subs: "P \<turnstile> Ts' [\<le>] Ts" and T'isT: "T' = T"
using wt method map_Val_eq apply ((auto dest:sees_method_fun)[1])
using wt method map_Val_eq apply ((auto dest:sees_method_fun)[1])
.
have length_vs: "length vs = length Ts"
using wtes subs apply ((fastforce simp:list_all2_iff dest!:WTrts_same_length)[1])
.
obtain T'' where wtabody: "P,[pns [\<mapsto>] Ts] \<turnstile> body :: T''" and T''subT: "P \<turnstile> T'' \<le> T" and length_pns: "length pns = length Ts"
using sees_wf_mdecl[OF wf "method"] apply ((fastforce simp:wf_mdecl_def simp del:map_upds_twist)[1])
.
have fact119: "P,Map.empty(pns [\<mapsto>] Ts),h,sh \<turnstile> body : T''"
using wtabody apply ((rule WT_implies_WTrt)[1])
.
have fact120: "P,E(pns [\<mapsto>] Ts),h,sh \<turnstile> body : T''"
using fact119 apply ((rule WTrt_env_mono)[1])
 apply ((simp)[1])
.
have fact121: "P,E,h,sh \<turnstile> blocks(pns, Ts, vs, body) : T''"
using fact120 wtes subs sees_method_decl_above[OF "method"] length_vs length_pns apply ((fastforce simp add:wt_blocks rel_list_all2_Cons2)[1])
.
show "?case"
using T''subT T'isT fact121 apply ((blast)[1])
.
mqed
(*NEXT*)
mproof
case SCallInitDoneRed:  SCallInitDoneRed
show "?case"
using SCallInitDoneRed apply ((meson widen_refl)[1])
.
mqed
(*NEXT*)
mproof
case SCallInitRed:   (SCallInitRed C F Ts t pns body D sh v h l E T)
have fact124: "is_class P D"
using SCallInitRed.hyps(1) apply ((rule sees_method_is_class')[1])
.
have fact125: "P,E,h,sh \<turnstile> INIT D ([D],False) \<leftarrow> C\<bullet>\<^sub>sF(map Val v) : T \<and> P \<turnstile> T \<le> T"
using fact124 SCallInitRed WTrtInit[OF SCallInitRed.prems ( 3 )] apply ((clarsimp)[1])
.
show "?case"
using fact125 apply ((rule exI)[1])
.
mqed
(*NEXT*)
mproof
case RedSCallNone:  RedSCallNone
show "?case"
using RedSCallNone apply ((fastforce intro: WTrtThrow[OF WTrtVal] elim!: typeof_NoSuchMethodError simp: sconf_def hconf_def)[1])
.
mqed
(*NEXT*)
mproof
case RedSCallNonStatic:  RedSCallNonStatic
show "?case"
using RedSCallNonStatic apply ((fastforce intro: WTrtThrow[OF WTrtVal] elim!: typeof_IncompatibleClassChangeError simp: sconf_def hconf_def)[1])
.
mqed
(*NEXT*)
mproof
case BlockRedNone:  BlockRedNone
show "?case"
using BlockRedNone apply ((auto simp del:fun_upd_apply)[1])
 apply ((fastforce simp:sconf_def lconf_def)[1])
.
mqed
(*NEXT*)
mproof
case BlockRedSome:   (BlockRedSome e h l V sh b e' h' l' sh' b' v T E Te)
have red: "P \<turnstile> \<langle>e,(h,l(V:=None),sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle>" and IH: "\<And>E T. \<lbrakk>P,E \<turnstile> (h,l(V:=None),sh) \<surd>; iconf sh e; P,E,h,sh \<turnstile> e : T\<rbrakk>
                   \<Longrightarrow> \<exists>T'. P,E,h',sh' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T" and Some: "l' V = Some v" and conf: "P,E \<turnstile> (h,l,sh) \<surd>" and iconf: "iconf sh {V:T; e}" and wt: "P,E,h,sh \<turnstile> {V:T; e} : Te"
(*6 subgoals*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*end 6 subgoals*)
.
obtain Te' where IH': "P,E(V\<mapsto>T),h',sh' \<turnstile> e' : Te' \<and> P \<turnstile> Te' \<le> Te"
using IH conf iconf wt apply ((fastforce simp:sconf_def lconf_def)[1])
.
have fact130: "P,h' \<turnstile> l' (:\<le>) E(V\<mapsto>T)"
using conf wt apply ((fastforce intro:red_preserves_lconf[OF red] simp:sconf_def lconf_def)[1])
.
have fact131: "P,h' \<turnstile> v :\<le> T"
using fact130 Some apply ((fastforce simp:lconf_def)[1])
.
show "?case"
using IH' fact131 apply ((fastforce simp:sconf_def conf_def fun_upd_same simp del:fun_upd_apply)[1])
.
mqed
(*NEXT*)
mproof
case InitBlockRed:   (InitBlockRed e h l V v sh b e' h' l' sh' b' v' T E T')
have red: "P \<turnstile> \<langle>e, (h,l(V\<mapsto>v),sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle>" and IH: "\<And>E T. \<lbrakk>P,E \<turnstile> (h,l(V\<mapsto>v),sh) \<surd>; iconf sh e; P,E,h,sh \<turnstile> e : T\<rbrakk>
                    \<Longrightarrow> \<exists>U. P,E,h',sh' \<turnstile> e' : U \<and> P \<turnstile> U \<le> T" and v': "l' V = Some v'" and conf: "P,E \<turnstile> (h,l,sh) \<surd>" and iconf: "iconf sh {V:T; V:=Val v;; e}" and wt: "P,E,h,sh \<turnstile> {V:T := Val v; e} : T'"
(*6 subgoals*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*NEXT*)
 apply ((fact)[1])
(*end 6 subgoals*)
.
obtain T\<^sub>1 where "wt\<^sub>1": "typeof\<^bsub>h\<^esub> v = Some T\<^sub>1" and T1subT: "P \<turnstile> T\<^sub>1 \<le> T" and "wt\<^sub>2": "P,E(V\<mapsto>T),h,sh \<turnstile> e : T'"
using wt apply ((auto)[1])
.
have "lconf\<^sub>2": "P,h \<turnstile> l(V\<mapsto>v) (:\<le>) E(V\<mapsto>T)"
using conf "wt\<^sub>1" T1subT apply ((simp add:sconf_def lconf_upd2 conf_def)[1])
.
have fact133: "\<exists>T\<^sub>1'. typeof\<^bsub>h'\<^esub> v' = Some T\<^sub>1' \<and> P \<turnstile> T\<^sub>1' \<le> T"
using v' red_preserves_lconf[OF red wt\<^sub>2 lconf\<^sub>2] apply ((fastforce simp:lconf_def conf_def)[1])
.
show "?case"
using IH conf iconf "lconf\<^sub>2" "wt\<^sub>2" fact133 apply ((fastforce simp add:sconf_def)[1])
.
mqed
(*NEXT*)
 apply ((fastforce)[1])
(*NEXT*)
 apply ((fastforce)[1])
(*NEXT*)
mproof
case SeqRed:   (SeqRed e h l sh b e' h' l' sh' b' e\<^sub>2)
have val: "val_of e = None"
using SeqRed apply ((simp add: val_no_step)[1])
.
show "?case"
 apply ((cases "lass_val_of e")[1])
(*2 subgoals*)
mproof
case None:  None
show "\<exists>T'. P,E,h',sh' \<turnstile> e';; e\<^sub>2 : T' \<and> P \<turnstile> T' \<le> T"
using None SeqRed val apply ((auto elim: WTrt_hext_shext_mono[OF _ red_hext_incr red_shext_incr])[1])
.
mqed
(*NEXT*)
mproof
case Some:   (Some a)
have fact137: "sh = sh'"
using SeqRed lass_val_of_spec[OF Some] apply ((auto)[1])
.
show "\<exists>T'. P,E,h',sh' \<turnstile> e';; e\<^sub>2 : T' \<and> P \<turnstile> T' \<le> T"
using fact137 SeqRed val Some apply ((auto intro: lass_val_of_iconf[OF Some] elim: WTrt_hext_mono[OF _ red_hext_incr])[1])
.
mqed
(*end 2 subgoals*)
.
mqed
(*NEXT*)
 apply ((fastforce)[1])
(*NEXT*)
mproof
case CondRed:  CondRed
show "?case"
using CondRed apply ((auto)[1])
(*4 subgoals*)
 apply ((blast intro:WTrt_hext_shext_mono[OF _ red_hext_incr red_shext_incr])[1])
(*NEXT*)
 apply ((blast intro:WTrt_hext_shext_mono[OF _ red_hext_incr red_shext_incr])[1])
(*NEXT*)
 apply ((blast intro:WTrt_hext_shext_mono[OF _ red_hext_incr red_shext_incr])[1])
(*NEXT*)
 apply ((blast intro:WTrt_hext_shext_mono[OF _ red_hext_incr red_shext_incr])[1])
(*end 4 subgoals*)
.
mqed
(*NEXT*)
 apply ((fastforce)[1])
(*NEXT*)
 apply ((fastforce)[1])
(*NEXT*)
 apply ((fastforce)[1])
(*NEXT*)
mproof
case ThrowRed:  ThrowRed
show "?case"
using ThrowRed apply ((auto simp:is_refT_def)[1])
(*2 subgoals*)
 apply ((blast dest:widen_Class[THEN iffD1])[1])
(*NEXT*)
 apply ((blast dest:widen_Class[THEN iffD1])[1])
(*end 2 subgoals*)
.
mqed
(*NEXT*)
mproof
case RedThrowNull:  RedThrowNull
show "?case"
using RedThrowNull apply ((fastforce intro: WTThrow[OF WTVal] elim!:typeof_NullPointer simp:sconf_def hconf_def)[1])
.
mqed
(*NEXT*)
mproof
case TryRed:  TryRed
show "?case"
using TryRed apply ((auto)[1])
 apply ((blast intro:widen_trans WTrt_hext_shext_mono[OF _ red_hext_incr red_shext_incr])[1])
.
mqed
(*NEXT*)
 apply ((fastforce)[1])
(*NEXT*)
 apply ((fastforce)[1])
(*NEXT*)
mproof
case RedTryFail:  RedTryFail
show "?case"
using RedTryFail apply ((fastforce intro: WTrtThrow[OF WTrtVal] simp:sconf_def hconf_def)[1])
.
mqed
(*NEXT*)
mproof
case ListRed1:   (ListRed1 e h l sh b e' h' l' sh' b' es)
have val: "val_of e = None"
using ListRed1 apply ((simp add: val_no_step)[1])
.
obtain U and Us where Ts: "Ts = U # Us"
using ListRed1 apply ((auto)[1])
.
have nsub_RI: "\<not> sub_RIs es" and wts: "P,E,h,sh \<turnstile> es [:] Us" and wt: "P,E,h,sh \<turnstile> e : U" and IH: "\<And>E T. \<lbrakk>P,E \<turnstile> (h, l, sh) \<surd>; P,E,h,sh \<turnstile> e : T\<rbrakk> \<Longrightarrow> \<exists>T'. P,E,h',sh' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T"
(*4 subgoals*)
using Ts ListRed1 val apply ((auto)[1])
(*NEXT*)
using Ts ListRed1 val apply ((auto)[1])
(*NEXT*)
using Ts ListRed1 val apply ((auto)[1])
(*NEXT*)
using Ts ListRed1 val apply ((auto)[1])
(*end 4 subgoals*)
.
obtain T' where fact144: "\<forall>E0 E1. (\<exists>T2. P,E1,h',sh' \<turnstile> e' : T2 \<and> P \<turnstile> T2 \<le> E0) = (P,E1,h',sh' \<turnstile> e' : T' E0 E1 \<and> P \<turnstile> T' E0 E1 \<le> E0)"
 apply ((moura)[1])
.
have disj: "\<forall>E t. \<not> P,E \<turnstile> (h, l, sh) \<surd> \<or> \<not> P,E,h,sh \<turnstile> e : t \<or> P,E,h',sh' \<turnstile> e' : T' t E \<and> P \<turnstile> T' t E \<le> t"
using fact144 IH apply ((presburger)[1])
.
have fact145: "P,E,h',sh' \<turnstile> es [:] Us"
using nsub_RI wts wt apply ((metis (no_types) ListRed1.hyps(1) WTrts_hext_shext_mono red_hext_incr red_shext_incr)[1])
.
have fact146: "\<exists>ts. (\<exists>t tsa. ts = t # tsa \<and> P,E,h',sh' \<turnstile> e' : t \<and> P,E,h',sh' \<turnstile> es [:] tsa) \<and> P \<turnstile> ts [\<le>] (U # Us)"
using fact145 disj wt ListRed1.prems(1) apply ((blast)[1])
.
show "?case"
using fact146 Ts apply ((auto)[1])
.
mqed
(*NEXT*)
mproof
case ListRed2:  ListRed2
show "?case"
using ListRed2 apply ((fastforce dest: hext_typeof_mono[OF reds_hext_incr])[1])
.
mqed
(*NEXT*)
 apply ((fastforce)[1])
(*NEXT*)
mproof
case InitNoneRed:   (InitNoneRed sh C C' Cs e h l b)
have sh: "sh \<unlhd>\<^sub>s sh(C \<mapsto> (sblank P C, Prepared))"
using InitNoneRed apply ((simp add: shext_def)[1])
.
have wt: "P,E,h,sh(C \<mapsto> (sblank P C, Prepared)) \<turnstile> INIT C' (C # Cs,False) \<leftarrow> e : T"
using InitNoneRed WTrt_shext_mono[OF _ sh] apply ((fastforce)[1])
.
show "?case"
using wt apply ((rule_tac x = T in exI)[1])
 apply ((simp add: fun_upd_def)[1])
.
mqed
(*NEXT*)
mproof
case RedInitDone:   (RedInitDone sh C sfs C' Cs e h l b)
have fact150: "P,E,h,sh \<turnstile> INIT C' (Cs,True) \<leftarrow> e : T"
using RedInitDone apply ((auto)[1])
 apply ((metis Nil_tl list.set_sel(2))[1])
.
show "?case"
using fact150 apply ((rule_tac x = T in exI)[1])
 apply ((simp)[1])
.
mqed
(*NEXT*)
mproof
case RedInitProcessing:   (RedInitProcessing sh C sfs C' Cs e h l b)
have fact152: "P,E,h,sh \<turnstile> INIT C' (Cs,True) \<leftarrow> e : T"
using RedInitProcessing apply ((auto)[1])
(*2 subgoals*)
 apply ((metis Nil_tl list.set_sel(2))[1])
(*NEXT*)
 apply ((metis Nil_tl list.set_sel(2))[1])
(*end 2 subgoals*)
.
show "?case"
using fact152 apply ((rule_tac x = T in exI)[1])
 apply ((simp)[1])
.
mqed
(*NEXT*)
mproof
case RedInitError:  RedInitError
show "?case"
using RedInitError apply ((fastforce intro: WTrtThrow[OF WTrtVal] elim!: typeof_NoClassDefFoundError simp: sconf_def hconf_def)[1])
.
mqed
(*NEXT*)
mproof
case InitObjectRed:   (InitObjectRed sh C sfs sh' C' Cs e h l b)
have sh: "sh \<unlhd>\<^sub>s sh(Object \<mapsto> (sfs, Processing))"
using InitObjectRed apply ((simp add: shext_def)[1])
.
have fact155: "P,E,h,sh' \<turnstile> INIT C' (C # Cs,True) \<leftarrow> e : T"
using InitObjectRed WTrt_shext_mono[OF _ sh] apply ((auto)[1])
.
show "?case"
using fact155 apply ((rule_tac x = T in exI)[1])
 apply ((simp add: fun_upd_def)[1])
.
mqed
(*NEXT*)
mproof
case InitNonObjectSuperRed:   (InitNonObjectSuperRed sh C sfs D fs ms sh' C' Cs e h l b)
have sh: "sh \<unlhd>\<^sub>s sh(C \<mapsto> (sfs, Processing))"
using InitNonObjectSuperRed apply ((simp add: shext_def)[1])
.
have cd: "is_class P D"
using sh InitNonObjectSuperRed class_wf wf wf_cdecl_supD apply ((blast)[1])
.
have sup': "supercls_lst P (C # Cs)"
using InitNonObjectSuperRed.prems(3) apply ((auto)[1])
.
have sup: "supercls_lst P (D # C # Cs)"
using sup' supercls_lst_app[of P C Cs D] subcls1I[OF InitNonObjectSuperRed.hyps ( 3 , 2 )] apply ((auto)[1])
.
have fact157: "distinct (C # Cs)"
using InitNonObjectSuperRed.prems(3) apply ((auto)[1])
.
have dist: "distinct (D # C # Cs)"
using fact157 wf_supercls_distinct_app[OF wf InitNonObjectSuperRed.hyps ( 2 - 3 ) sup'] apply ((simp)[1])
.
have fact158: "P,E,h,sh' \<turnstile> INIT C' (D # C # Cs,False) \<leftarrow> e : T"
using InitNonObjectSuperRed WTrt_shext_mono[OF _ sh] cd sup dist apply ((auto)[1])
.
show "?case"
using fact158 apply ((rule_tac x = T in exI)[1])
 apply ((simp)[1])
.
mqed
(*NEXT*)
mproof
case RedInitRInit:   (RedInitRInit C' C Cs e' h l sh b E T)
obtain a and sfs where C: "class P C = \<lfloor>a\<rfloor>" and proc: "sh C = \<lfloor>(sfs, Processing)\<rfloor>"
using RedInitRInit WTrtInit apply ((auto simp: is_class_def)[1])
.
have T': "P,E,h,sh \<turnstile> C\<bullet>\<^sub>sclinit([]) : Void"
using C proc wf_types_clinit[OF wf C] apply ((simp)[1])
.
have fact160: "P,E,h,sh \<turnstile> RI (C,C\<bullet>\<^sub>sclinit([])) ; Cs \<leftarrow> e' : T"
using RedInitRInit apply ((auto intro: T')[1])
.
show "?case"
using fact160 apply ((rule_tac x = T in exI)[1])
 apply ((simp)[1])
.
mqed
(*NEXT*)
mproof
case RInitRed:   (RInitRed e h l sh b e' h' l' sh' b' C Cs e\<^sub>0 E T)
have fact162: "(\<And>E T. P,E \<turnstile> (h, l, sh) \<surd> \<Longrightarrow> P,E,h,sh \<turnstile> e : T \<Longrightarrow> \<exists>T'. P,E,h',sh' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T)"
using RInitRed apply ((auto)[1])
.
have fact163: "\<exists>T'. P,E,h',sh' \<turnstile> e' : T'"
using fact162 RInitRed apply ((blast)[1])
.
obtain T' where e': "P,E,h',sh' \<turnstile> e' : T'"
using fact163 apply ((auto)[1])
.
have "wt\<^sub>0": "P,E,h',sh' \<turnstile> e\<^sub>0 : T"
using RInitRed apply ((simp)[1])
 apply ((auto intro: WTrt_hext_shext_mono[OF _ red_hext_incr red_shext_incr])[1])
.
have nip: "\<forall>C' \<in> set (C#Cs). not_init C' e' \<and> (\<exists>sfs. sh' C' = \<lfloor>(sfs, Processing)\<rfloor>)"
using RInitRed red_proc_pres[OF wf_prog_wwf_prog [ OF wf ]] apply ((auto)[1])
.
have shC: "\<exists>sfs. sh' C = \<lfloor>(sfs, Processing)\<rfloor> \<or> sh' C = \<lfloor>(sfs, Error)\<rfloor> \<and> e' = THROW NoClassDefFoundError"
using RInitRed red_proc_pres[OF wf_prog_wwf_prog [ OF wf ] RInitRed.hyps ( 1 )] apply ((blast)[1])
.
have fact164: "P,E,h',sh' \<turnstile> RI (C,e') ; Cs \<leftarrow> e\<^sub>0 : T"
using RInitRed e' "wt\<^sub>0" nip shC apply ((auto)[1])
.
show "?case"
using fact164 apply ((rule_tac x = T in exI)[1])
 apply ((simp)[1])
.
mqed
(*NEXT*)
mproof
case RedRInit:   (RedRInit sh C sfs i sh' C' Cs v e h l b)
have sh: "sh \<unlhd>\<^sub>s sh(C \<mapsto> (sfs, Done))"
using RedRInit apply ((auto simp: shext_def)[1])
.
have wt: "P,E,h,sh(C \<mapsto> (sfs, Done)) \<turnstile> e : T"
using RedRInit WTrt_shext_mono[OF _ sh] apply ((auto)[1])
.
have shC: "\<forall>C' \<in> set(tl Cs). \<exists>sfs. sh C' = \<lfloor>(sfs, Processing)\<rfloor>"
using RedRInit apply ((cases Cs)[1])
(*2 subgoals*)
using RedRInit apply ((auto)[1])
(*NEXT*)
using RedRInit apply ((auto)[1])
(*end 2 subgoals*)
.
have fact166: "P,E,h,sh' \<turnstile> INIT C' (Cs,True) \<leftarrow> e : T"
using RedRInit wt shC apply ((cases Cs)[1])
(*2 subgoals*)
using RedRInit wt shC apply ((auto)[1])
(*NEXT*)
using RedRInit wt shC apply ((auto)[1])
(*end 2 subgoals*)
.
show "?case"
using fact166 apply ((rule_tac x = T in exI)[1])
 apply ((simp)[1])
.
mqed
(*NEXT*)
 apply ((fastforce)[1])
(*NEXT*)
 apply ((fastforce)[1])
(*NEXT*)
 apply ((fastforce)[1])
(*NEXT*)
 apply ((fastforce)[1])
(*NEXT*)
 apply ((fastforce)[1])
(*NEXT*)
 apply ((fastforce)[1])
(*NEXT*)
 apply ((fastforce)[1])
(*NEXT*)
 apply ((fastforce)[1])
(*NEXT*)
 apply ((fastforce)[1])
(*NEXT*)
 apply ((fastforce)[1])
(*NEXT*)
mproof
case SCallThrowParams:   (SCallThrowParams es vs e es' C M h l sh b)
show "?case"
using SCallThrowParams map_Val_nthrow_neq[of _ vs e es'] apply ((fastforce)[1])
.
mqed
(*NEXT*)
 apply ((fastforce)[1])
(*NEXT*)
 apply ((fastforce)[1])
(*NEXT*)
 apply ((fastforce)[1])
(*NEXT*)
 apply ((fastforce)[1])
(*NEXT*)
 apply ((fastforce)[1])
(*NEXT*)
mproof
case RInitInitThrow:   (RInitInitThrow sh C sfs i sh' a D Cs e h l b)
have sh: "sh \<unlhd>\<^sub>s sh(C \<mapsto> (sfs, Error))"
using RInitInitThrow apply ((auto simp: shext_def)[1])
.
have wt: "P,E,h,sh(C \<mapsto> (sfs, Error)) \<turnstile> e : T"
using RInitInitThrow WTrt_shext_mono[OF _ sh] apply ((clarsimp)[1])
.
have fact169: "P,E,h,sh' \<turnstile> RI (D,Throw a) ; Cs \<leftarrow> e : T"
using wt RInitInitThrow apply ((auto)[1])
.
show "?case"
using fact169 apply ((rule_tac x = T in exI)[1])
 apply ((simp)[1])
.
mqed
(*NEXT*)
 apply ((fastforce)[1])
(*end 95 subgoals*)
.
 


corollary subject_reduction:
  "\<lbrakk> wf_J_prog P; P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle>; P,E \<turnstile> s \<surd>; iconf (shp s) e; P,E,hp s,shp s \<turnstile> e:T \<rbrakk>
  \<Longrightarrow> \<exists>T'. P,E,hp s',shp s' \<turnstile> e':T' \<and> P \<turnstile> T' \<le> T"
(*<*)by(cases s, cases s', fastforce dest:subject_reduction2)(*>*)

corollary subjects_reduction:
  "\<lbrakk> wf_J_prog P; P \<turnstile> \<langle>es,s,b\<rangle> [\<rightarrow>] \<langle>es',s',b'\<rangle>; P,E \<turnstile> s \<surd>; iconfs (shp s) es; P,E,hp s,shp s \<turnstile> es[:]Ts \<rbrakk>
  \<Longrightarrow> \<exists>Ts'. P,E,hp s',shp s' \<turnstile> es'[:]Ts' \<and> P \<turnstile> Ts' [\<le>] Ts"
(*<*)by(cases s, cases s', fastforce dest:subjects_reduction2)(*>*)


subsection \<open> Lifting to @{text"\<rightarrow>*"} \<close>

text\<open> Now all these preservation lemmas are first lifted to the transitive
closure \dots \<close>

lemma Red_preserves_sconf:
assumes wf: "wf_J_prog P" and Red: "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle>"
shows "\<And>T. \<lbrakk> P,E,hp s,shp s \<turnstile> e : T; iconf (shp s) e; P,E \<turnstile> s \<surd> \<rbrakk> \<Longrightarrow> P,E \<turnstile> s' \<surd>"
(*<*)
using Red
proof (induct rule:converse_rtrancl_induct3)
  case refl show ?case by fact
next
  case (step e s b e' s' b')
  obtain h l sh h' l' sh' where s:"s = (h,l,sh)" and s':"s' = (h',l',sh')"
    by(cases s, cases s')
  then have "P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle>" using step.hyps(1) by simp
  then have iconf': "iconf (shp s') e'" using red_preserves_iconf[OF wf_prog_wwf_prog[OF wf]]
    step.prems(2) s s' by simp
  thus ?case using step
    by(blast intro:red_preserves_sconf dest: subject_reduction[OF wf])
qed
(*>*)

lemma Red_preserves_iconf:
assumes wf: "wwf_J_prog P" and Red: "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle>"
shows "iconf (shp s) e \<Longrightarrow> iconf (shp s') e'"
(*<*)
using Red
proof (induct rule:converse_rtrancl_induct3)
  case refl show ?case by fact
next
  case (step e s b e' s' b')
  thus ?case using wf step by(cases s, cases s', simp) (blast intro:red_preserves_iconf)
qed
(*>*)

lemma Reds_preserves_iconf:
assumes wf: "wwf_J_prog P" and Red: "P \<turnstile> \<langle>es,s,b\<rangle> [\<rightarrow>]* \<langle>es',s',b'\<rangle>"
shows "iconfs (shp s) es \<Longrightarrow> iconfs (shp s') es'"
(*<*)
using Red
proof (induct rule:converse_rtrancl_induct3)
  case refl show ?case by fact
next
  case (step e s b e' s' b')
  thus ?case using wf step by(cases s, cases s', simp) (blast intro:reds_preserves_iconf)
qed
(*>*)

lemma Red_preserves_bconf:
assumes wf: "wwf_J_prog P" and Red: "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle>"
shows "iconf (shp s) e \<Longrightarrow> P,(shp s) \<turnstile>\<^sub>b (e,b) \<surd> \<Longrightarrow> P,(shp s') \<turnstile>\<^sub>b (e'::expr,b') \<surd>"
(*<*)
using Red
proof (induct rule:converse_rtrancl_induct3)
  case refl show ?case by fact
next
  case (step e s1 b e' s2 b')
  then have "iconf (shp s2) e'" using step red_preserves_iconf[OF wf]
   by(cases s1, cases s2) auto
  thus ?case using step by(cases s1, cases s2, simp) (blast intro:red_preserves_bconf)
qed
(*>*)

lemma Reds_preserves_bconf:
assumes wf: "wwf_J_prog P" and Red: "P \<turnstile> \<langle>es,s,b\<rangle> [\<rightarrow>]* \<langle>es',s',b'\<rangle>"
shows "iconfs (shp s) es \<Longrightarrow> P,(shp s) \<turnstile>\<^sub>b (es,b) \<surd> \<Longrightarrow> P,(shp s') \<turnstile>\<^sub>b (es'::expr list,b') \<surd>"
(*<*)
using Red
proof (induct rule:converse_rtrancl_induct3)
  case refl show ?case by fact
next
  case (step es s1 b es' s2 b')
  then have "iconfs (shp s2) es'" using step reds_preserves_iconf[OF wf]
   by(cases s1, cases s2) auto
  thus ?case using step by(cases s1, cases s2, simp) (blast intro:reds_preserves_bconf)
qed
(*>*)

lemma Red_preserves_defass:
assumes wf: "wf_J_prog P" and reds: "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle>"
shows "\<D> e \<lfloor>dom(lcl s)\<rfloor> \<Longrightarrow> \<D> e' \<lfloor>dom(lcl s')\<rfloor>"
using reds
proof (induct rule:converse_rtrancl_induct3)
  case refl thus ?case .
next
  case (step e s b e' s' b') thus ?case
    by(cases s,cases s')(auto dest:red_preserves_defass[OF wf])
qed


lemma Red_preserves_type:
assumes wf: "wf_J_prog P" and Red: "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle>"
shows "!!T. \<lbrakk> P,E \<turnstile> s\<surd>; iconf (shp s) e; P,E,hp s,shp s \<turnstile> e:T \<rbrakk>
    \<Longrightarrow> \<exists>T'. P \<turnstile> T' \<le> T \<and> P,E,hp s',shp s' \<turnstile> e':T'"
(*<*)
using Red
proof (induct rule:converse_rtrancl_induct3)
  case refl thus ?case by blast
next
  case step thus ?case
    by(blast intro:widen_trans red_preserves_sconf Red_preserves_iconf[OF wf_prog_wwf_prog[OF wf]]
             dest:subject_reduction[OF wf])
qed
(*>*)


subsection "The final polish"

text\<open> The above preservation lemmas are now combined and packed nicely. \<close>

definition wf_config :: "J_prog \<Rightarrow> env \<Rightarrow> state \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool"   ("_,_,_ \<turnstile> _ : _ \<surd>"   [51,0,0,0,0]50)
where
  "P,E,s \<turnstile> e:T \<surd>  \<equiv>  P,E \<turnstile> s \<surd> \<and> iconf (shp s) e \<and> P,E,hp s,shp s \<turnstile> e:T"

theorem Subject_reduction: assumes wf: "wf_J_prog P"
shows "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle> \<Longrightarrow> P,E,s \<turnstile> e : T \<surd>
       \<Longrightarrow> \<exists>T'. P,E,s' \<turnstile> e' : T' \<surd> \<and> P \<turnstile> T' \<le> T"
(*<*)
by(cases s, cases s')
  (force simp: wf_config_def
         elim:red_preserves_sconf red_preserves_iconf[OF wf_prog_wwf_prog[OF wf]]
         dest:subject_reduction[OF wf])
(*>*)


theorem Subject_reductions:
assumes wf: "wf_J_prog P" and reds: "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle>"
shows "\<And>T. P,E,s \<turnstile> e:T \<surd> \<Longrightarrow> \<exists>T'. P,E,s' \<turnstile> e':T' \<surd> \<and> P \<turnstile> T' \<le> T"
(*<*)
using reds
proof (induct rule:converse_rtrancl_induct3)
  case refl thus ?case by blast
next
  case step thus ?case
    by(blast dest:Subject_reduction[OF wf] intro:widen_trans)
qed
(*>*)


corollary Progress: assumes wf: "wf_J_prog P"
shows "\<lbrakk> P,E,s  \<turnstile> e : T \<surd>; \<D> e \<lfloor>dom(lcl s)\<rfloor>; P,shp s \<turnstile>\<^sub>b (e,b) \<surd>; \<not> final e \<rbrakk>
   \<Longrightarrow> \<exists>e' s' b'. P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle>"
(*<*)
using progress[OF wf_prog_wwf_prog[OF wf]]
by(cases b) (auto simp:wf_config_def sconf_def)
(*>*)

corollary TypeSafety:
fixes s::state and e::expr
assumes wf: "wf_J_prog P" and sconf: "P,E \<turnstile> s \<surd>" and wt: "P,E \<turnstile> e::T"
  and \<D>: "\<D> e \<lfloor>dom(lcl s)\<rfloor>"
  and iconf: "iconf (shp s) e" and bconf: "P,(shp s) \<turnstile>\<^sub>b (e,b) \<surd>"
  and steps: "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle>"
  and nstep: "\<not>(\<exists>e'' s'' b''. P \<turnstile> \<langle>e',s',b'\<rangle> \<rightarrow> \<langle>e'',s'',b''\<rangle>)"
shows "(\<exists>v. e' = Val v \<and> P,hp s' \<turnstile> v :\<le> T) \<or>
      (\<exists>a. e' = Throw a \<and> a \<in> dom(hp s'))"
(*<*)
proof -
  have wwf: "wwf_J_prog P" by(rule wf_prog_wwf_prog[OF wf])
  have wfc: "P,E,s \<turnstile> e:T \<surd>" using WT_implies_WTrt[OF wt] sconf iconf
    by(simp add:wf_config_def)
  obtain T' where wfc': "P,E,s' \<turnstile> e' : T' \<surd>" and T': "P \<turnstile> T' \<le> T"
    using Subject_reductions[OF wf steps wfc] by clarsimp
  have \<D>': "\<D> e' \<lfloor>dom (lcl s')\<rfloor>"
    by(rule Red_preserves_defass[OF wf steps \<D>])
  have bconf': "P,(shp s') \<turnstile>\<^sub>b (e',b') \<surd>"
    by(rule Red_preserves_bconf[OF wwf steps iconf bconf])
  have fin': "final e'" using Progress[OF wf wfc' \<D>' bconf'] nstep by blast
  then show ?thesis using wfc wfc' T'
    by(fastforce simp:wf_config_def final_def conf_def)
qed
(*>*)


end
