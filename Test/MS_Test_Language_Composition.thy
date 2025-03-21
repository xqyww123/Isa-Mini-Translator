(*
Title: WHATandWHERE-Security
Authors: Sylvia Grewe, Alexander Lux, Heiko Mantel, Jens Sauer
*)
theory MS_Test_Language_Composition
imports WHATandWHERE_Security.WHATWHERE_Secure_Skip_Assign MS_Translator
begin

context WHATWHERE_Secure_Programs
begin

theorem Compositionality_Seq: 
  assumes WWs_part1: "WHATWHERE_Secure [c1]" 
  assumes WWs_part2: "WHATWHERE_Secure [c2]"
  assumes uniPPc1c2: "unique_PPc (c1;c2)"
  shows "WHATWHERE_Secure [c1;c2]"
proof (simp add: WHATWHERE_Secure_def, auto)
  fix d PP

  from uniPPc1c2 have nocommonPP: "set (PPc c1) \<inter> set (PPc c2) = {}"
    by (simp add: unique_PPV_def unique_PPc_def)
    
  from WWs_part1 obtain R1' where R1'assump: 
    "SdlHPPB d PP R1' \<and> ([c1],[c1]) \<in> R1'"
    by (simp add: WHATWHERE_Secure_def, auto)

  define R1 where "R1 = {(V,V'). (V,V') \<in> R1' \<and> set (PPV V) \<subseteq> set (PPc c1) 
    \<and> set (PPV V') \<subseteq> set (PPc c1)}"

  from R1'assump R1_def SdlHPPB_restricted_on_PP_is_SdlHPPB
  have SdlHPPR1: "SdlHPPB d PP R1"
    by force
    
  from WWs_part2 obtain R2' where R2'assump: 
    "SdlHPPB d PP R2' \<and> ([c2],[c2]) \<in> R2'"
    by (simp add: WHATWHERE_Secure_def, auto)

  define R2 where "R2 = {(V,V'). (V,V') \<in> R2' \<and> set (PPV V) \<subseteq> set (PPc c2) 
    \<and> set (PPV V') \<subseteq> set (PPc c2)}"

  from R2'assump R2_def SdlHPPB_restricted_on_PP_is_SdlHPPB
  have SdlHPPR2: "SdlHPPB d PP R2"
    by force

  from nocommonPP have nocommonDomain: "Domain R1 \<inter> Domain R2 \<subseteq> {[]}"
    by (simp add: R1_def R2_def, auto,
      metis inf_greatest inf_idem le_bot unique_V_uneq)

  with commonArefl_subset_commonDomain
  have Areflassump1: "Arefl R1 \<inter> Arefl R2 \<subseteq> {[]}"
    by force
     
  define R0 where "R0 = {(s1,s2). \<exists>c1 c1' c2 c2'. s1 = [c1;c2] \<and> s2 = [c1';c2'] \<and> 
    ([c1],[c1']) \<in> R1 \<and> ([c2],[c2']) \<in> R2}"

  with R1_def R1'assump R2_def R2'assump 
  have inR0: "([c1;c2],[c1;c2]) \<in> R0"
    by auto
  
  have "Domain R0 \<inter> Domain (R1 \<union> R2) = {}"
    by (simp add: R0_def R1_def R2_def, auto, metis Int_absorb1 Int_assoc Int_empty_left 
      nocommonPP unique_c_uneq, metis Int_absorb Int_absorb1 
      Int_assoc Int_empty_left nocommonPP unique_c_uneq)
    
  with commonArefl_subset_commonDomain
  have Areflassump2: "Arefl R0 \<inter> Arefl (R1 \<union> R2) \<subseteq> {[]}"
    by force

  have disjuptoR0: 
    "disj_dlHPP_Bisimulation_Up_To_R' d PP (R1 \<union> R2) R0"
    proof (simp add: disj_dlHPP_Bisimulation_Up_To_R'_def, auto)
        from Areflassump1 SdlHPPR1 SdlHPPR2 Union_Strong_dlHPP_Bisim
        show "SdlHPPB d PP (R1 \<union> R2)"
          by metis
      next
        from SdlHPPR1 have symR1: "sym R1" 
          by (simp add: Strong_dlHPP_Bisimulation_def)
        from SdlHPPR2 have symR2: "sym R2" 
          by (simp add: Strong_dlHPP_Bisimulation_def)
        with symR1 R0_def show "sym R0"
          by (simp add: sym_def, auto)
      next
        from SdlHPPR1 have transR1: "trans R1" 
          by (simp add: Strong_dlHPP_Bisimulation_def)
        from SdlHPPR2 have transR2: "trans R2" 
          by (simp add: Strong_dlHPP_Bisimulation_def)
        show "trans R0"
          proof -
            {
            fix V V' V''
            assume p1: "(V,V') \<in> R0"
            assume p2: "(V',V'') \<in> R0"
            have "(V,V'') \<in> R0"
              proof -
                from p1 R0_def obtain c1 c2 c1' c2' where p1assump:
                  "V = [c1;c2] \<and> V' = [c1';c2'] \<and>
                  ([c1],[c1']) \<in> R1 \<and> ([c2],[c2']) \<in> R2"
                  by auto
                with p2 R0_def obtain c1'' c2'' where p2assump:
                  "V'' = [c1'';c2''] \<and>
                  ([c1'],[c1'']) \<in> R1 \<and> ([c2'],[c2'']) \<in> R2"
                  by auto
                with p1assump transR1 transR2 have 
                  trans_assump: "([c1],[c1'']) \<in> R1 \<and> ([c2],[c2'']) \<in> R2"
                  by (simp add: trans_def, blast)
                with p1assump p2assump R0_def show ?thesis
                  by auto
              qed
             }
            thus ?thesis unfolding trans_def by blast
          qed
      next
        fix V V'
        assume "(V,V') \<in> R0"
        with R0_def show "length V = length V'"
          by auto
      next
        fix V V' i
        assume inR0: "(V,V') \<in> R0"
        assume irange: "i < length V"
        assume notIDC: "\<not> IDC d (V!i) (htchLoc (pp (V!i)))"
        from inR0 R0_def obtain c1 c2 c1' c2' where VV'assump:
          "V = [c1;c2] \<and> V' = [c1';c2'] \<and>
          ([c1],[c1']) \<in> R1 \<and> ([c2],[c2']) \<in> R2"
          by auto
        have eqnextmem: "\<And>m. \<lbrakk>c1;c2\<rbrakk>(m) = \<lbrakk>c1\<rbrakk>(m)"
          proof -
            fix m
            from nextmem_exists_and_unique obtain m' where c1nextmem:
              "\<exists>p \<alpha>. \<langle>c1,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m'\<rangle> 
              \<and> (\<forall>m''. (\<exists>p \<alpha>. \<langle>c1,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m''\<rangle>) \<longrightarrow> m'' = m')"
              by force

            hence eqdir1: "\<lbrakk>c1\<rbrakk>(m) = m'"
              by (simp add: NextMem_def, auto)
            
            from c1nextmem obtain p \<alpha> where "\<langle>c1,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m'\<rangle>"
              by auto

            with c1nextmem have "\<exists>p \<alpha>. \<langle>c1;c2,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m'\<rangle>
              \<and> (\<forall>m''. (\<exists>p \<alpha>. \<langle>c1;c2,m\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m''\<rangle>) \<longrightarrow> m'' = m')"
              by (auto, metis MWLsSteps_det.seq1 MWLsSteps_det.seq2 
                option.exhaust, metis MWLsSteps_det_cases(3))
                            
            hence eqdir2: "\<lbrakk>c1;c2\<rbrakk>(m) = m'"
              by (simp add: NextMem_def, auto)

            with eqdir1 show "\<lbrakk>c1;c2\<rbrakk>(m) = \<lbrakk>c1\<rbrakk>(m)" 
              by auto
          qed
            
        have eqpp: "pp (c1;c2) = pp c1"
          by simp
        from VV'assump SdlHPPR1 have "IDC d c1 (htchLoc (pp c1)) 
          \<or> NDC d c1"
          by (simp add: Strong_dlHPP_Bisimulation_def, auto)
        with eqnextmem eqpp have "IDC d (c1;c2)
          (htchLoc (pp (c1;c2))) \<or> NDC d (c1;c2)"
          by (simp add: IDC_def NDC_def)
        with inR0 irange notIDC VV'assump
        show "NDC d (V!i)"
          by (simp add: IDC_def, auto)
      next
        fix V V' m1 m1' m2 \<alpha> p i
        assume inR0: "(V,V') \<in> R0"
        assume irange: "i < length V"
        assume step: "\<langle>V!i,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m2\<rangle>"
        assume dhequal: "m1 \<sim>\<^bsub>d,htchLocSet PP\<^esub> m1'"

        from inR0 R0_def obtain c1 c1' c2 c2' where R0pair:
          "V = [c1;c2] \<and> V' = [c1';c2'] \<and> ([c1],[c1']) \<in> R1
          \<and> ([c2],[c2']) \<in> R2"
          by auto
 
       from R0pair irange have i0: "i = 0" by simp

       have eqpp: "pp (c1;c2) = pp c1"
         by simp

        \<comment> \<open>get the two different cases:\<close>
        from R0pair step i0 obtain c3 where case_distinction:
          "(p = Some c2 \<and> \<langle>c1,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>None,m2\<rangle>)
          \<or> (p = Some (c3;c2) \<and> \<langle>c1,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>Some c3,m2\<rangle>)"
          by (simp, insert MWLsSteps_det.simps[of "c1;c2" "m1"],
            auto)
        moreover
        \<comment> \<open>Case 1: first command terminates\<close>
        {
          assume passump: "p = Some c2"
          assume StepAssump: "\<langle>c1,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>None,m2\<rangle>"
          hence Vstep_case1:
            "\<langle>c1;c2,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>Some c2,m2\<rangle>"
            by (simp add: MWLsSteps_det.seq1)
          
          from SdlHPPR1 StepAssump R0pair dhequal
            strongdlHPPB_aux[of "d" "PP"
            "R1" "0" "[c1]" "[c1']" "m1" "\<alpha>" "None" "m2" "m1'"]
          obtain p' \<alpha>' m2' where c1c1'reason: 
            "p' = None \<and> \<langle>c1',m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and> (\<alpha>,\<alpha>') \<in> R1 \<and> 
            dhequality_alternative d PP (pp c1) m2 m2'"
            by (simp add: stepResultsinR_def, fastforce)
 
          with eqpp c1c1'reason have conclpart:
            "\<langle>c1';c2',m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>Some c2',m2'\<rangle> \<and> 
            dhequality_alternative d PP (pp (c1;c2)) m2 m2'"
            by (auto, simp add: MWLsSteps_det.seq1)

          with passump R0pair c1c1'reason i0
          have case1_concl: 
          "\<exists>p' \<alpha>' m2'.
             \<langle>V'!i,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and>
             stepResultsinR p p' (R0 \<union> (R1 \<union> R2)) \<and>
             ((\<alpha>,\<alpha>') \<in> R0 \<or> (\<alpha>,\<alpha>') \<in> R1 \<or> (\<alpha>,\<alpha>') \<in> R2) \<and>
             dhequality_alternative d PP (pp (V!i)) m2 m2'"
          by (simp add: stepResultsinR_def, auto)
        }
        moreover
        \<comment> \<open>Case 2: first command does not terminate\<close>
        {
          assume passump: "p = Some (c3;c2)"
          assume StepAssump: "\<langle>c1,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>Some c3,m2\<rangle>"

          hence Vstep_case2:  "\<langle>c1;c2,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>Some (c3;c2),m2\<rangle>"
            by (simp add: MWLsSteps_det.seq2)

          from SdlHPPR1 StepAssump R0pair dhequal
            strongdlHPPB_aux[of "d" "PP"
            "R1" "0" "[c1]" "[c1']" "m1" "\<alpha>" "Some c3" "m2" "m1'"]
          obtain p' c3' \<alpha>' m2' where c1c1'reason: 
            "p' = Some c3' \<and> \<langle>c1',m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and> 
            ([c3],[c3']) \<in> R1 \<and> (\<alpha>,\<alpha>') \<in> R1 \<and>
            dhequality_alternative d PP (pp c1) m2 m2'"
            by (simp add: stepResultsinR_def, fastforce)

          with eqpp c1c1'reason have conclpart:
            "\<langle>c1';c2',m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>Some (c3';c2'),m2'\<rangle> \<and> 
            dhequality_alternative d PP (pp (c1;c2)) m2 m2'"
            by (auto, simp add: MWLsSteps_det.seq2)

          from c1c1'reason R0pair R0_def have 
            "([c3;c2],[c3';c2']) \<in> R0"
            by auto
          
          with R0pair conclpart passump c1c1'reason i0
          have case1_concl: 
            "\<exists>p' \<alpha>' m2'. \<langle>V'!i,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and>
            stepResultsinR p p' (R0 \<union> (R1 \<union> R2)) \<and>
            ((\<alpha>,\<alpha>') \<in> R0 \<or> (\<alpha>,\<alpha>') \<in> R1 \<or> (\<alpha>,\<alpha>') \<in> R2) \<and>
            dhequality_alternative d PP (pp (V!i)) m2 m2'"
            by (simp add: stepResultsinR_def, auto)
        }
        ultimately
        show "\<exists>p' \<alpha>' m2'. \<langle>V'!i,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>'\<rhd> \<langle>p',m2'\<rangle> \<and>
             stepResultsinR p p' (R0 \<union> (R1 \<union> R2)) \<and>
             ((\<alpha>,\<alpha>') \<in> R0 \<or> (\<alpha>,\<alpha>') \<in> R1 \<or> (\<alpha>,\<alpha>') \<in> R2) \<and>
             dhequality_alternative d PP (pp (V!i)) m2 m2'"
          by blast
      qed
        
  with inR0 Areflassump2 Up_To_Technique
  have "SdlHPPB d PP (R0 \<union> (R1 \<union> R2))"
    by auto 

  with inR0 show "\<exists>R. SdlHPPB d PP R \<and> ([c1;c2],[c1;c2]) \<in> R"
    by auto

qed
 
       
theorem Compositionality_Spawn:
  assumes WWs_threads: "WHATWHERE_Secure V"
  assumes uniPPspawn: "unique_PPc (spawn\<^bsub>\<iota>\<^esub> V)"
  shows "WHATWHERE_Secure [spawn\<^bsub>\<iota>\<^esub> V]"  
ML_val \<open>val _ =  MinLang_Translator.translate'm  @{Isar.state} 
(File.read (Path.explode "./Translator/t2.txt"))\<close>

  sorry




declare [[ML_print_depth = 1000]]
  
theorem Compositionality_If:
  assumes dind: "\<forall>d. b \<equiv>\<^bsub>d\<^esub> b"
  assumes WWs_branch1: "WHATWHERE_Secure [c1]"
  assumes WWs_branch2: "WHATWHERE_Secure [c2]"
  assumes uniPPif: "unique_PPc (if\<^bsub>\<iota>\<^esub> b then c1 else c2 fi)"
  shows "WHATWHERE_Secure [if\<^bsub>\<iota>\<^esub> b then c1 else c2 fi]"      
ML_val \<open>val _ =  MinLang_Translator.translate'm @{Isar.state} 
(File.read (Path.explode "./Translator/t1.txt"))\<close>
sorry

theorem Compositionality_While:
  assumes dind: "\<forall>d. b \<equiv>\<^bsub>d\<^esub> b"
  assumes WWs_body: "WHATWHERE_Secure [c]"
  assumes uniPPwhile: "unique_PPc (while\<^bsub>\<iota>\<^esub> b do c od)"
  shows "WHATWHERE_Secure [while\<^bsub>\<iota>\<^esub> b do c od]" 
ML_val \<open>val _ =  MinLang_Translator.translate'm @{Isar.state} 
(File.read (Path.explode "./Translator/t3.txt"))\<close>
sorry
end

end
