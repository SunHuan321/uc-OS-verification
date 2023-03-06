section \<open>Integrating the SIMP language into Picore\<close>

theory picore_SIMP
  imports "SIMP_plus" "PiCore/PiCore_RG_Invariant"
begin

print_locale event_validity
print_locale event_hoare

abbreviation ptranI :: "'Env \<Rightarrow> ('a conf \<times> 'a conf) set"
where "ptranI \<Gamma> \<equiv> ctran"

abbreviation petranI :: "'Env \<Rightarrow> 'a conf \<Rightarrow> 'a conf \<Rightarrow> bool"
where "petranI \<Gamma> \<equiv> etran'"

abbreviation cpts_pI :: "'Env \<Rightarrow> 'a confs set"
where "cpts_pI \<Gamma> \<equiv> cptn"

abbreviation cpts_of_pI :: "'Env \<Rightarrow> ('a com) option \<Rightarrow> 'a \<Rightarrow> ('a confs) set" where
  "cpts_of_pI \<Gamma> \<equiv> cp" 

abbreviation prog_validityI :: "'Env \<Rightarrow> ('a com) option \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow> bool"
where "prog_validityI \<Gamma> P \<equiv> prog_validity P"

abbreviation assume_pI :: "'Env \<Rightarrow> ('a set \<times> ('a \<times> 'a) set) \<Rightarrow> ('a confs) set" 
where "assume_pI \<Gamma> \<equiv> assum"

abbreviation commit_pI :: "'Env \<Rightarrow> (('a \<times> 'a) set \<times> 'a set) \<Rightarrow> ('a confs) set" 
where "commit_pI \<Gamma> \<equiv> comm"

abbreviation rghoare_pI :: "'Env \<Rightarrow> [('a com) option, 'a set, ('a \<times> 'a) set, ('a \<times> 'a) set, 'a set] \<Rightarrow> bool"
("_ \<turnstile>\<^sub>I _ sat\<^sub>p [_, _, _, _]" [60,0,0,0,0] 45)
where "rghoare_pI \<Gamma> \<equiv> rghoare_p"

lemma cpts_pI_ne_empty: "[] \<notin> cpts_pI \<Gamma>"
  by (simp)

lemma petran_simpsI:
"petranI \<Gamma> (a, b) (c, d) \<Longrightarrow> a = c" 
  by(simp add: etran.simps)

lemma none_no_tranI': "((Q, s),(P,t)) \<in> ptranI \<Gamma> \<Longrightarrow> Q \<noteq> None"
  apply (simp) apply(rule ctran.cases)
  by simp+

lemma none_no_tranI: "((None, s),(P,t)) \<notin> ptranI \<Gamma>"
  using none_no_tranI' 
  by fast

lemma ptran_neqI: "((P, s),(P,t)) \<notin> ptranI \<Gamma>"
  by (simp)

interpretation event ptranI petranI None
  using petran_simpsI none_no_tranI ptran_neqI 
        event.intro[of petranI None ptranI] by auto

thm ptran'_def

lemma cpts_p_simpsI:
  "((\<exists>P s. aa = [(P, s)]) \<or>
   (\<exists>P t xs s. aa = (P, s) # (P, t) # xs \<and> (P, t) # xs \<in> cpts_pI \<Gamma>) \<or>
   (\<exists>P s Q t xs. aa = (P, s) # (Q, t) # xs \<and> ptran' \<Gamma> (P, s) (Q, t) \<and> (Q, t) # xs \<in> cpts_pI \<Gamma>))
  \<Longrightarrow> (aa \<in> cpts_pI \<Gamma>)"
  apply(simp add: ptran'_def) using cptn.simps[of aa] by blast

(*lemma cpts_of_p_defI: "cpts_of_pI \<Gamma> P s \<equiv> {l. l!0=(P,s) \<and> l \<in> cpts_pI \<Gamma>}" 
  by(simp add:cpts_pI_def cpts_of_pI_def cpts_of_p_def)*)
lemma cpts_of_p_defI: "l!0=(P,s) \<and> l \<in> cpts_pI \<Gamma> \<Longrightarrow> l \<in> cpts_of_pI \<Gamma> P s" 
  by(simp add: cp_def)

interpretation event_comp ptranI petranI None cpts_pI cpts_of_pI
  using cpts_pI_ne_empty cpts_p_simpsI cpts_of_p_defI petran_simpsI none_no_tranI ptran_neqI 
        event_comp.intro[of ptranI petranI None cpts_pI cpts_of_pI] event.intro[of petranI None ptranI] 
        event_comp_axioms.intro[of cpts_pI ptranI cpts_of_pI]
  apply(simp add: ptran'_def) by blast

(*
lemma prog_validity_defI: "prog_validityI \<Gamma> P pre rely guar post \<equiv> 
   \<forall>s. cpts_of_pI \<Gamma> P s \<inter> assume_pI \<Gamma> (pre, rely) \<subseteq> commit_pI \<Gamma> (guar, post)"
by (simp add:prog_validityI_def cpts_of_pI_def assume_pI_def commit_pI_def prog_validity_def)
*)
lemma prog_validity_defI: "prog_validityI \<Gamma> P pre rely guar post \<Longrightarrow> 
   \<forall>s. cpts_of_pI \<Gamma> P s \<inter> assume_pI \<Gamma> (pre, rely) \<subseteq> commit_pI \<Gamma> (guar, post)"
by (simp add: prog_validity_def)

lemma assume_p_defI: "snd (c!0) \<in> pre \<and> (\<forall>i. Suc i<length c \<longrightarrow> 
               petranI \<Gamma> (c!i) (c!(Suc i)) \<longrightarrow> (snd (c!i), snd (c!Suc i)) \<in> rely) \<Longrightarrow> c \<in> assume_pI \<Gamma> (pre, rely)"
by(simp add: assum_def PiCore_Semantics.gets_p_def)

lemma commit_p_defI: "c \<in> commit_pI \<Gamma> (guar, post) \<Longrightarrow> (\<forall>i. Suc i<length c \<longrightarrow> 
               (c!i,c!(Suc i)) \<in> ptranI \<Gamma>  \<longrightarrow> (snd (c!i), snd (c!Suc i)) \<in> guar) \<and> 
               (fst (last c) = None \<longrightarrow> snd (last c) \<in> post)"
by(simp add: comm_def PiCore_Semantics.getspc_p_def 
      PiCore_Semantics.gets_p_def)

lemma rgsound_pI: "rghoare_pI \<Gamma> P pre rely guar post \<longrightarrow> prog_validityI \<Gamma> P pre rely guar post"
  using rgsound_p by blast

interpretation event_hoare ptranI petranI None cpts_pI cpts_of_pI prog_validityI assume_pI commit_pI rghoare_pI
  using cpts_pI_ne_empty cpts_p_simpsI cpts_of_p_defI petran_simpsI none_no_tranI ptran_neqI 
        prog_validity_defI assume_p_defI commit_p_defI rgsound_pI
        event_comp_axioms.intro[of cpts_pI ptranI cpts_of_pI]
        event_comp.intro[of ptranI petranI None cpts_pI cpts_of_pI] event.intro[of petranI None ptranI] 
        event_validity_axioms.intro[of prog_validityI cpts_of_pI assume_pI commit_pI petranI ptranI None] 
        event_validity.intro[of ptranI petranI None cpts_pI cpts_of_pI prog_validityI assume_pI commit_pI]
        event_hoare.intro[of ptranI petranI None cpts_pI cpts_of_pI prog_validityI assume_pI commit_pI rghoare_pI]
        event_hoare_axioms.intro[of rghoare_pI prog_validityI] 
  apply(simp add: ptran'_def gets_p_def getspc_p_def) by blast

thm invariant_theorem
(*print_theorems*)

lemma stable_eq[simp]: "stable_e = stable"
by(simp add:stable_e_def stable_def)

end