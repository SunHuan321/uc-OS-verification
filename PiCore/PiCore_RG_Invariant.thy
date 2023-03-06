section \<open>Rely-guarantee-based Safety Reasoning\<close>

theory PiCore_RG_Invariant
imports PiCore_Hoare 
begin

type_synonym 's invariant = "'s \<Rightarrow> bool"

context event_hoare
begin

definition invariant_presv_pares::"'Env \<Rightarrow> 's invariant \<Rightarrow> ('l,'k,'s,'prog) paresys \<Rightarrow> 's set \<Rightarrow> ('s \<times> 's) set \<Rightarrow> bool"
  where "invariant_presv_pares \<Gamma> invar pares init R \<equiv> 
          \<forall>s0 x0 pesl. s0\<in>init \<and> pesl \<in> (cpts_of_pes \<Gamma> pares s0 x0 \<inter> assume_pes \<Gamma> (init, R))
                          \<longrightarrow> (\<forall>i<length pesl. invar (gets (pesl!i)))"

definition invariant_presv_pares2::"'Env \<Rightarrow> 's invariant \<Rightarrow> ('l,'k,'s,'prog) paresys \<Rightarrow> 's set \<Rightarrow> ('s \<times> 's) set \<Rightarrow> bool"
  where "invariant_presv_pares2 \<Gamma> invar pares init R \<equiv> 
          \<forall>s0 x0 pesl. pesl \<in> (cpts_of_pes \<Gamma> pares s0 x0 \<inter> assume_pes \<Gamma> (init, R))
                          \<longrightarrow> (\<forall>i<length pesl. invar (gets (pesl!i)))"

lemma "invariant_presv_pares \<Gamma> invar pares init R = invariant_presv_pares2 \<Gamma> invar pares init R"
apply(rule iffI)
apply(simp add:invariant_presv_pares_def invariant_presv_pares2_def cpts_of_pes_def assume_pes_def gets_def)
apply clarsimp 
apply(simp add:invariant_presv_pares_def invariant_presv_pares2_def cpts_of_pes_def assume_pes_def gets_def)
done

theorem invariant_theorem:
  assumes parsys_sat_rg: "\<Gamma> \<turnstile> pesf SAT [init, R, G, pst]"
    and   stb_rely: "stable_e (Collect invar) R"
    and   stb_guar: "stable_e (Collect invar) G"
    and   init_in_invar: "init \<subseteq> (Collect invar)"
  shows "invariant_presv_pares \<Gamma> invar (paresys_spec pesf) init R"
proof -
  from parsys_sat_rg have "\<Gamma> \<Turnstile> paresys_spec pesf SAT [init, R, G, pst]" using rgsound_pes by fast
  hence cpts_pes: "\<forall>s x. (cpts_of_pes \<Gamma> (paresys_spec pesf) s x) \<inter> assume_pes \<Gamma> (init, R) \<subseteq> commit_pes \<Gamma> (G, pst)"
    by (simp add:pes_validity_def)
  show ?thesis
  proof -
  {
    fix s0 x0 pesl
    assume a0: "s0\<in>init"
      and  a1: "pesl\<in>cpts_of_pes \<Gamma> (paresys_spec pesf) s0 x0 \<inter> assume_pes \<Gamma> (init, R)"
     from a1 have a3: "pesl!0 = (paresys_spec pesf, s0, x0) \<and> pesl\<in>cpts_pes \<Gamma>" by (simp add:cpts_of_pes_def)
    from a1 cpts_pes have pesl_in_comm: "pesl \<in> commit_pes \<Gamma> (G, pst)" by auto
    {
      fix i
      assume b0: "i<length pesl"
      then have "gets (pesl!i) \<in> (Collect invar)"
      proof(induct i)
        case 0 
        with a3 have "gets (pesl!0) = s0" by (simp add:gets_def)
        with a0 init_in_invar show ?case by auto
      next
        case (Suc ni)
        assume c0: "ni < length pesl \<Longrightarrow> gets (pesl ! ni) \<in> (Collect invar)"
          and  c1: "Suc ni < length pesl"
        then have c2: "gets (pesl ! ni) \<in> (Collect invar)" by auto
        from c1 have c3: "ni < length pesl" by simp
        with c0 have c4: "gets (pesl ! ni) \<in> (Collect invar)" by simp
        from a3 c1 have "\<Gamma> \<turnstile> pesl ! ni -pese\<rightarrow> pesl ! Suc ni \<or> (\<exists>et. \<Gamma> \<turnstile> pesl ! ni -pes-et\<rightarrow> pesl ! Suc ni)"
          using incpts_pes_impl_evnorcomptran by blast
        then show ?case
        proof
          assume d0: "\<Gamma> \<turnstile> pesl ! ni -pese\<rightarrow> pesl ! Suc ni"
          then show ?thesis using c3 c4 a1 c1 stb_rely by(simp add:assume_pes_def stable_e_def)
        next
          assume "\<exists>et. \<Gamma> \<turnstile> pesl ! ni -pes-et\<rightarrow> pesl ! Suc ni"
          then obtain et where d0: "\<Gamma> \<turnstile> pesl ! ni -pes-et\<rightarrow> pesl ! Suc ni" by auto
          then show ?thesis using c3 c4 c1 pesl_in_comm stb_guar apply(simp add:commit_pes_def stable_e_def)
            by blast 
        qed
      qed
    }
  }
  then show ?thesis using invariant_presv_pares_def by blast
  qed
qed

end

end