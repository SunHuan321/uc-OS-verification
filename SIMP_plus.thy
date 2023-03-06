section \<open>Integrating the SIMP language into Picore\<close>

theory SIMP_plus
imports "SIMP/RG_Hoare"
begin

inductive rghoare_p :: "['a com option, 'a set, ('a \<times> 'a) set, ('a \<times> 'a) set, 'a set] \<Rightarrow> bool"
    ("\<turnstile>\<^sub>I _ sat\<^sub>p [_, _, _, _]" [60,0,0,0,0] 45)
where 
(*  Some_hoare: "\<lbrakk> \<turnstile> Q sat [pre, rely, guar, post] \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>I (Some Q) sat\<^sub>p [pre, rely, guar, post]"*)
  Basic: "\<lbrakk> pre \<subseteq> {s. f s \<in> post}; {(s,t). s \<in> pre \<and> (t=f s)} \<subseteq> guar;
            stable pre rely; stable post rely \<rbrakk>
           \<Longrightarrow> \<turnstile>\<^sub>I Some (Basic f) sat\<^sub>p [pre, rely, guar, post]"

| Seq: "\<lbrakk> \<turnstile>\<^sub>I Some P sat\<^sub>p [pre, rely, guar, mid]; \<turnstile>\<^sub>I Some Q sat\<^sub>p [mid, rely, guar, post] \<rbrakk>
           \<Longrightarrow> \<turnstile>\<^sub>I Some (Seq P Q) sat\<^sub>p [pre, rely, guar, post]"

| Cond: "\<lbrakk> stable pre rely; \<turnstile>\<^sub>I Some P1 sat\<^sub>p [pre \<inter> b, rely, guar, post];
           \<turnstile>\<^sub>I Some P2 sat\<^sub>p [pre \<inter> -b, rely, guar, post]; \<forall>s. (s,s)\<in>guar \<rbrakk>
          \<Longrightarrow> \<turnstile>\<^sub>I Some (Cond b P1 P2) sat\<^sub>p [pre, rely, guar, post]"

| While: "\<lbrakk> stable pre rely; (pre \<inter> -b) \<subseteq> post; stable post rely;
            \<turnstile>\<^sub>I Some P sat\<^sub>p [pre \<inter> b, rely, guar, pre]; \<forall>s. (s,s)\<in>guar \<rbrakk>
          \<Longrightarrow> \<turnstile>\<^sub>I Some (While b P) sat\<^sub>p [pre, rely, guar, post]"

| Await: "\<lbrakk> stable pre rely; stable post rely;
            \<forall>V. \<turnstile>\<^sub>I Some P sat\<^sub>p [pre \<inter> b \<inter> {V}, {(s, t). s = t},
                UNIV, {s. (V, s) \<in> guar} \<inter> post] \<rbrakk>
           \<Longrightarrow> \<turnstile>\<^sub>I Some (Await b P) sat\<^sub>p [pre, rely, guar, post]"

| None_hoare: "\<lbrakk> stable pre rely; pre \<subseteq> post \<rbrakk>  \<Longrightarrow> \<turnstile>\<^sub>I None sat\<^sub>p [pre, rely, guar, post]"

| Conseq: "\<lbrakk> pre \<subseteq> pre'; rely \<subseteq> rely'; guar' \<subseteq> guar; post' \<subseteq> post;
             \<turnstile>\<^sub>I P sat\<^sub>p [pre', rely', guar', post'] \<rbrakk>
            \<Longrightarrow> \<turnstile>\<^sub>I P sat\<^sub>p [pre, rely, guar, post]"

| Unprecond: "\<lbrakk> \<turnstile>\<^sub>I P sat\<^sub>p [pre, rely, guar, post]; \<turnstile>\<^sub>I P sat\<^sub>p [pre', rely, guar, post] \<rbrakk>
            \<Longrightarrow> \<turnstile>\<^sub>I P sat\<^sub>p [pre \<union> pre', rely, guar, post]"

| Intpostcond: "\<lbrakk> \<turnstile>\<^sub>I P sat\<^sub>p [pre, rely, guar, post]; \<turnstile>\<^sub>I P sat\<^sub>p [pre, rely, guar, post'] \<rbrakk>
            \<Longrightarrow> \<turnstile>\<^sub>I P sat\<^sub>p [pre, rely, guar, post \<inter> post']"

| Allprecond: "\<forall>v\<in>U. \<turnstile>\<^sub>I P sat\<^sub>p [{v}, rely, guar, post]
            \<Longrightarrow> \<turnstile>\<^sub>I P sat\<^sub>p [U, rely, guar, post]"

| Emptyprecond: "\<turnstile>\<^sub>I P sat\<^sub>p [{}, rely, guar, post]"


definition prog_validity :: "'a com option \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a set \<Rightarrow> bool" 
                 ("\<Turnstile>\<^sub>I _ sat\<^sub>p [_, _, _, _]" [60,0,0,0,0] 45) where
  "\<Turnstile>\<^sub>I P sat\<^sub>p [pre, rely, guar, post] \<equiv> 
   \<forall>s. cp P s \<inter> assum(pre, rely) \<subseteq> comm(guar, post)"
 
(*
lemma Basic_imp: "\<turnstile> Basic x sat [pre, rely, guar, post] \<Longrightarrow> \<turnstile>\<^sub>I Some (Basic x) sat\<^sub>p [pre, rely, guar, post]"
apply(erule RG_Hoare.rghoare.induct) 
  using Basic apply blast
  using Seq apply blast
  using Cond apply blast
  using While apply blast
  using Await apply blast
  using Conseq apply blast
done

lemma Seq_imp: "(\<turnstile> P1 sat [pre, rely, guar, post] \<Longrightarrow> \<turnstile>\<^sub>I Some P1 sat\<^sub>p [pre, rely, guar, post]) \<Longrightarrow>
       (\<turnstile> P2 sat [pre, rely, guar, post] \<Longrightarrow> \<turnstile>\<^sub>I Some P2 sat\<^sub>p [pre, rely, guar, post]) \<Longrightarrow>
       \<turnstile> Seq P1 P2 sat [pre, rely, guar, post] \<Longrightarrow> \<turnstile>\<^sub>I Some (Seq P1 P2) sat\<^sub>p [pre, rely, guar, post]"
apply(erule RG_Hoare.rghoare.induct) 
  using Basic apply blast
  using Seq apply blast
  using Cond apply blast
  using While apply blast
  using Await apply blast
  using Conseq apply blast
done

lemma Cond_imp: "(\<turnstile> P1 sat [pre, rely, guar, post] \<Longrightarrow> \<turnstile>\<^sub>I Some P1 sat\<^sub>p [pre, rely, guar, post]) \<Longrightarrow>
       (\<turnstile> P2 sat [pre, rely, guar, post] \<Longrightarrow> \<turnstile>\<^sub>I Some P2 sat\<^sub>p [pre, rely, guar, post]) \<Longrightarrow>
       \<turnstile> Cond x1a P1 P2 sat [pre, rely, guar, post] \<Longrightarrow> \<turnstile>\<^sub>I Some (Cond x1a P1 P2) sat\<^sub>p [pre, rely, guar, post]"
apply(erule RG_Hoare.rghoare.induct) 
  using Basic apply blast
  using Seq apply blast
  using Cond apply blast
  using While apply blast
  using Await apply blast
  using Conseq apply blast
done

lemma While_imp: " (\<turnstile> P sat [pre, rely, guar, post] \<Longrightarrow> \<turnstile>\<^sub>I Some P sat\<^sub>p [pre, rely, guar, post]) \<Longrightarrow>
       \<turnstile> While x1a P sat [pre, rely, guar, post] \<Longrightarrow> \<turnstile>\<^sub>I Some (While x1a P) sat\<^sub>p [pre, rely, guar, post]"
apply(erule RG_Hoare.rghoare.induct) 
  using Basic apply blast
  using Seq apply blast
  using Cond apply blast
  using While apply blast
  using Await apply blast
  using Conseq apply blast
done

lemma Await_imp: " (\<turnstile> P sat [pre, rely, guar, post] \<Longrightarrow> \<turnstile>\<^sub>I Some P sat\<^sub>p [pre, rely, guar, post]) \<Longrightarrow>
       \<turnstile> Await x1a P sat [pre, rely, guar, post] \<Longrightarrow> \<turnstile>\<^sub>I Some (Await x1a P) sat\<^sub>p [pre, rely, guar, post]"
apply(erule RG_Hoare.rghoare.induct) 
  using Basic apply blast
  using Seq apply blast
  using Cond apply blast
  using While apply blast
  using Await apply blast
  using Conseq apply blast
done

lemma "\<turnstile> P sat [pre, rely, guar, post] \<Longrightarrow> \<turnstile>\<^sub>I (Some P) sat\<^sub>p [pre, rely, guar, post]"
apply(induct P) 
using Basic_imp apply blast
using Seq_imp apply blast
using Cond_imp apply blast
using While_imp apply blast
using Await_imp apply blast
done

thm rghoare_p.induct
*)

subsection \<open>lemmas of SIMP\<close>

lemma etran_or_ctran2_disjI3:
  "\<lbrakk> x\<in>cptn; Suc i<length x; \<not> x!i -c\<rightarrow> x!Suc i\<rbrakk> \<Longrightarrow> x!i -e\<rightarrow> x!Suc i"
apply(induct x arbitrary:i)
 apply simp
apply clarify
apply(rule cptn.cases)
  apply simp+
  using less_Suc_eq_0_disj etran.intros apply force
  apply(case_tac i,simp)
  by simp


lemma stable_id: "stable P Id"
  unfolding stable_def Id_def by auto

lemma stable_id2: "stable P {(s,t). s = t}"
  unfolding stable_def by auto

lemma stable_int2: "stable s r \<Longrightarrow> stable t r \<Longrightarrow> stable (s \<inter> t) r"
  by (metis (full_types) IntD1 IntD2 IntI stable_def)

lemma stable_int3: "stable k r \<Longrightarrow> stable s r \<Longrightarrow> stable t r \<Longrightarrow> stable (k \<inter> s \<inter> t) r"
  by (metis (full_types) IntD1 IntD2 IntI stable_def)

lemma stable_int4: "stable k r \<Longrightarrow> stable s r \<Longrightarrow> stable t r \<Longrightarrow> stable v r \<Longrightarrow>  
                    stable (k \<inter> s \<inter> t \<inter> v) r"
  by (metis (full_types) IntD1 IntD2 IntI stable_def)

lemma stable_int5: "stable k r \<Longrightarrow> stable s r \<Longrightarrow> stable t r \<Longrightarrow> stable v r \<Longrightarrow>  
                    stable y r \<Longrightarrow> stable (k \<inter> s \<inter> t \<inter> v \<inter> y) r"
  by (metis (full_types) IntD1 IntD2 IntI stable_def)

lemma stable_un2: "stable s r \<Longrightarrow> stable t r \<Longrightarrow> stable (s \<union> t) r"
  by (simp add: stable_def)

(*
lemma Seq2: "\<lbrakk> \<turnstile> P sat [pre, rely, guar, mida]; mida \<subseteq> midb; \<turnstile> Q sat [midb, rely, guar, post] \<rbrakk>
  \<Longrightarrow> \<turnstile>\<^sub>I Some (Seq P Q) sat\<^sub>p [pre, rely, guar, post]"
  using Seq[of P pre rely guar mida Q post] Some_hoare[of "Seq P Q" pre rely guar post]
        RG_Hoare.Conseq[of mida midb rely rely guar guar post post Q] 
  by blast*)

lemma Seq2: "\<lbrakk> \<turnstile>\<^sub>I Some P sat\<^sub>p [pre, rely, guar, mida]; mida \<subseteq> midb; \<turnstile>\<^sub>I Some Q sat\<^sub>p [midb, rely, guar, post] \<rbrakk>
  \<Longrightarrow> \<turnstile>\<^sub>I Some (Seq P Q) sat\<^sub>p [pre, rely, guar, post]"
  using Seq[of P pre rely guar mida Q post] 
        Conseq[of mida midb rely rely guar guar post post]
  by blast

(*
lemma Intpostcond_sound':
  assumes p0: " \<Turnstile> P sat [pre, rely, guar, post]"
    and  p1: " \<Turnstile> P sat [pre, rely, guar, post']"
   shows " \<Turnstile> P sat [pre, rely, guar, post \<inter> post']"
proof -
{
  fix s c
  assume a0: "c \<in> cp (Some P) s \<inter> assum(pre, rely)"
  with p0 have "c \<in> comm(guar, post)" unfolding com_validity_def by auto
  moreover
  from a0 p1 have "c \<in> comm(guar, post')" unfolding com_validity_def by auto
  ultimately have "c \<in> comm(guar, post \<inter> post')"
    by (simp add: comm_def) 
}
then show ?thesis unfolding com_validity_def by auto
qed

lemma "\<lbrakk> \<turnstile> P sat [pre, rely, guar, post]; \<turnstile> P sat [pre, rely, guar, post'] \<rbrakk>
            \<Longrightarrow> \<Turnstile> P sat [pre, rely, guar, post \<inter> post']"
using Intpostcond_sound' rgsound by blast
*)

subsection\<open>Soundness of the Rule of Consequence\<close>

lemma Conseq_sound:
  "\<lbrakk>pre \<subseteq> pre'; rely \<subseteq> rely'; guar' \<subseteq> guar; post' \<subseteq> post;
  \<Turnstile>\<^sub>I P sat\<^sub>p [pre', rely', guar', post']\<rbrakk>
  \<Longrightarrow> \<Turnstile>\<^sub>I P sat\<^sub>p [pre, rely, guar, post]"
apply(simp add:prog_validity_def assum_def comm_def)
apply clarify
apply(erule_tac x=s in allE)
apply(drule_tac c=x in subsetD)
 apply force
apply force
done

subsection\<open>Soundness of the Rule of Unprecond\<close>

lemma Unprecond_sound:
  assumes p0: " \<Turnstile>\<^sub>I P sat\<^sub>p [pre, rely, guar, post]"
    and  p1: " \<Turnstile>\<^sub>I P sat\<^sub>p [pre', rely, guar, post]"
   shows " \<Turnstile>\<^sub>I P sat\<^sub>p [pre \<union> pre', rely, guar, post]"
proof -
{
  fix s c
  assume "c \<in> cp P s \<inter> assum(pre \<union> pre', rely)"
  hence a1: "c \<in> cp P s" and
        a2: "c \<in> assum(pre \<union> pre', rely)" by auto
  hence "c \<in> assum(pre, rely) \<or> c \<in> assum(pre', rely)"
    by (metis (no_types, lifting) CollectD CollectI Un_iff assum_def prod.simps(2))
  hence "c \<in> comm(guar, post)"
    proof
      assume "c \<in> assum (pre, rely)"
      with p0 a1 show "c \<in> comm (guar, post)" 
        unfolding prog_validity_def by auto
    next
      assume "c \<in> assum (pre', rely)"
      with p1 a1 show "c \<in> comm (guar, post)" 
        unfolding prog_validity_def by auto
    qed
}
then show ?thesis unfolding prog_validity_def by auto
qed

subsection\<open>Soundness of the Rule of Intpostcond\<close>

lemma Intpostcond_sound:
  assumes p0: " \<Turnstile>\<^sub>I P sat\<^sub>p [pre, rely, guar, post]"
    and  p1: " \<Turnstile>\<^sub>I P sat\<^sub>p [pre, rely, guar, post']"
   shows " \<Turnstile>\<^sub>I P sat\<^sub>p [pre, rely, guar, post \<inter> post']"
proof -
{
  fix s c
  assume a0: "c \<in> cp P s \<inter> assum(pre, rely)"
  with p0 have "c \<in> comm(guar, post)" unfolding prog_validity_def by auto
  moreover
  from a0 p1 have "c \<in> comm(guar, post')" unfolding prog_validity_def by auto
  ultimately have "c \<in> comm(guar, post \<inter> post')"
    by (simp add: comm_def) 
}
then show ?thesis unfolding prog_validity_def by auto
qed

subsection\<open>Soundness of the Rule of Allprecond\<close>

lemma Allprecond_sound: 
  assumes p1: "\<forall>v\<in>U. \<Turnstile>\<^sub>I P sat\<^sub>p [{v}, rely, guar, post]"
    shows " \<Turnstile>\<^sub>I P sat\<^sub>p [U, rely, guar, post]"
proof -
{
  fix s c
  assume a0: "c \<in> cp P s \<inter> assum(U, rely)" 
  then obtain x where a1: "x\<in>U \<and> snd (c!0) = x"
    by (metis (no_types, lifting) CollectD IntD2 assum_def prod.simps(2))

  with p1 have "\<Turnstile>\<^sub>I P sat\<^sub>p [{x}, rely, guar, post]" by simp
  hence a2: "\<forall>s. cp P s \<inter> assum({x}, rely) \<subseteq> comm(guar, post)" unfolding prog_validity_def by simp

  from a0 have "c \<in> assum(U, rely)" by simp
  hence "snd (c!0) \<in> U \<and> (\<forall>i. Suc i<length c \<longrightarrow> 
               c!i -e\<rightarrow> c!(Suc i) \<longrightarrow> (snd (c!i), snd (c!Suc i)) \<in> rely)" by (simp add:assum_def)
  with a1 have "snd (c!0) \<in> {x} \<and> (\<forall>i. Suc i<length c \<longrightarrow> 
               c!i -e\<rightarrow> c!(Suc i) \<longrightarrow> (snd (c!i), snd (c!Suc i)) \<in> rely)" by simp

  hence "c\<in>assum({x}, rely)" by (simp add:assum_def)
  with a0 a2 have "c \<in> comm(guar, post)" by auto
}
then show ?thesis using prog_validity_def by blast
qed

subsection\<open>Soundness of the Rule of Emptyprecond\<close>

lemma Emptyprecond_sound: " \<Turnstile>\<^sub>I P sat\<^sub>p [{}, rely, guar, post]"
unfolding prog_validity_def by(simp add:assum_def)


subsection\<open>Soundness of None rule\<close>

lemma none_all_none: "c!0=(None,s) \<and> c \<in> cptn \<Longrightarrow> \<forall>i<length c. fst (c ! i) = None"
proof(induct c arbitrary:s)
  case Nil
  then show ?case by simp
next
  case (Cons a c)
  assume p1: "\<And>s. c ! 0 = (None, s) \<and> c \<in> cptn \<Longrightarrow> \<forall>i<length c. fst (c ! i) = None"
    and  p2: "(a # c) ! 0 = (None, s) \<and> a # c \<in> cptn"
  hence a0: "a = (None,s)" by simp
  thus ?case
    proof(cases "c = []")
      case True
      with a0 show ?thesis by auto
    next
      case False
      assume b0: "c \<noteq> []"
      with p2 have c_cpts: "c \<in> cptn" using tl_in_cptn by fast
      from b0 obtain c' and b where bc': "c = b # c'"
        using list.exhaust by blast 
      from a0 have "\<not> a -c\<rightarrow> b" by(force elim: ctran.cases)
      with p2 have "a -e\<rightarrow> b"  using bc' etran_or_ctran2_disjI3[of "a#c" 0] by auto
      hence "fst b = None" using etran.cases
        by (metis a0 prod.collapse) 
      with p1 bc' c_cpts have "\<forall>i<length c. fst (c ! i) = None"
        by (metis nth_Cons_0 prod.collapse)
      with a0 show ?thesis
        by (simp add: nth_Cons') 
    qed
      
qed

lemma None_sound_h: "\<forall>x. x \<in> pre \<longrightarrow> (\<forall>y. (x, y) \<in> rely \<longrightarrow> y \<in> pre) \<Longrightarrow>
         pre \<subseteq> post \<Longrightarrow>
         snd (c ! 0) \<in> pre \<Longrightarrow>
         c \<noteq> [] \<Longrightarrow> \<forall>i. Suc i < length c \<longrightarrow> (snd (c ! i), snd (c ! Suc i)) \<in> rely 
      \<Longrightarrow> i < length c \<Longrightarrow> snd (c ! i) \<in> pre"
apply(induct i) by auto

lemma None_sound:
  "\<lbrakk> stable pre rely; pre \<subseteq> post \<rbrakk>
  \<Longrightarrow> \<Turnstile>\<^sub>I None sat\<^sub>p [pre, rely, guar, post]"
proof -
  assume p0: "stable pre rely"
    and  p2: "pre \<subseteq> post"
  {
    fix s c
    assume a0: "c \<in> cp None s \<inter> assum(pre, rely)"
    hence c1: "c!0=(None,s) \<and> c \<in> cptn" by (simp add:cp_def)
    from a0 have c2: "snd (c!0) \<in> pre \<and> (\<forall>i. Suc i<length c \<longrightarrow> 
               c!i -e\<rightarrow> c!(Suc i) \<longrightarrow> (snd (c!i), snd (c!Suc i)) \<in> rely)"
      by (simp add:assum_def)
    from c1 have c_ne_empty: "c \<noteq> []"
      by auto 
    from c1 have c_all_none: "\<forall>i<length c. fst (c ! i) = None" using none_all_none by fast
   
    (* have "(\<forall>i. Suc i<length c \<longrightarrow> 
               c!i -impc\<rightarrow> c!(Suc i) \<longrightarrow> (gets_p (c!i), gets_p (c!Suc i)) \<in> guar)" *)
    {
      fix i
      assume suci: "Suc i<length c"
        and cc: "c!i -c\<rightarrow> c!(Suc i)"
      from suci c_all_none have "c!i -e\<rightarrow> c!(Suc i)"
        by (metis Suc_lessD etran.intros prod.collapse) 
      with cc have"(snd (c!i), snd (c!Suc i)) \<in> guar"
        using c1 etran_or_ctran2_disjI1 suci by auto
    } 
    moreover
    {
      assume last_none: "fst (last c) = None"
      from c2 c_all_none have "\<forall>i. Suc i<length c \<longrightarrow> (snd (c!i), snd (c!Suc i)) \<in> rely"
        by (metis Suc_lessD etran.intros prod.collapse) 
      with p0 p2 c2 c_ne_empty have "\<forall>i. i < length c \<longrightarrow> snd (c ! i) \<in> pre" 
        apply(simp add: stable_def) apply clarify using None_sound_h by blast
      with p2 c_ne_empty have "snd (last c) \<in> post"
        using One_nat_def c_ne_empty last_conv_nth by force           
    }
    ultimately have "c \<in> comm(guar, post)" by (simp add:comm_def)
  }
  thus "\<Turnstile>\<^sub>I None sat\<^sub>p [pre, rely, guar, post]" using prog_validity_def by blast
qed

subsection\<open>Soundness of the Await rule\<close>

lemma Await_sound:
  "\<lbrakk>stable pre rely; stable post rely;
  \<forall>V. \<turnstile>\<^sub>I Some P sat\<^sub>p [pre \<inter> b \<inter> {s. s = V}, {(s, t). s = t},
                 UNIV, {s. (V, s) \<in> guar} \<inter> post] \<and>
  \<Turnstile>\<^sub>I Some P sat\<^sub>p [pre \<inter> b \<inter> {s. s = V}, {(s, t). s = t},
                 UNIV, {s. (V, s) \<in> guar} \<inter> post] \<rbrakk>
  \<Longrightarrow> \<Turnstile>\<^sub>I Some (Await b P) sat\<^sub>p [pre, rely, guar, post]"
apply(unfold prog_validity_def)
apply clarify
apply(simp add:comm_def)
apply(rule conjI)
 apply clarify
 apply(simp add:cp_def assum_def)
 apply clarify
 apply(frule_tac j=0 and k=i and p=pre in stability,simp_all)
   apply(erule_tac x=ia in allE,simp)
  apply(subgoal_tac "x\<in> cp (Some(Await b P)) s")
  apply(erule_tac i=i in unique_ctran_Await,force,simp_all)
  apply(simp add:cp_def)
(*--\<open>here starts the different part.\<close>*)
 apply(erule ctran.cases,simp_all)
 apply(drule Star_imp_cptn)
 apply clarify
 apply(erule_tac x=sa in allE)
 apply clarify
 apply(erule_tac x=sa in allE)
 apply(drule_tac c=l in subsetD)
  apply (simp add:cp_def)
  apply clarify
  apply(erule_tac x=ia and P="\<lambda>i. H i \<longrightarrow> (J i, I i)\<in>ctran" for H J I in allE,simp)
  apply(erule etranE,simp)
 apply simp
apply clarify
apply(simp add:cp_def)
apply clarify
apply(frule_tac i="length x - 1" in exists_ctran_Await_None,force)
  apply (case_tac x,simp+)
 apply(rule last_fst_esp,simp add:last_length)
 apply(case_tac x, simp+)
apply clarify
apply(simp add:assum_def)
apply clarify
apply(frule_tac j=0 and k="j" and p=pre in stability,simp_all)
  apply(erule_tac x=i in allE,simp)
 apply(erule_tac i=j in unique_ctran_Await,force,simp_all)
apply(case_tac "x!j")
apply clarify
apply simp
apply(drule_tac s="Some (Await b P)" in sym,simp)
apply(case_tac "x!Suc j",simp)
apply(rule ctran.cases,simp)
apply(simp_all)
apply(drule Star_imp_cptn)
apply clarify
apply(erule_tac x=sa in allE)
apply clarify
apply(erule_tac x=sa in allE)
apply(drule_tac c=l in subsetD)
 apply (simp add:cp_def)
 apply clarify
 apply(erule_tac x=i and P="\<lambda>i. H i \<longrightarrow> (J i, I i)\<in>ctran" for H J I in allE,simp)
 apply(erule etranE,simp)
apply simp
apply clarify
apply(frule_tac j="Suc j" and k="length x - 1" and p=post in stability,simp_all)
 apply(case_tac x,simp+)
 apply(erule_tac x=i in allE)
apply(erule_tac i=j in unique_ctran_Await,force,simp_all)
 apply arith+
apply(case_tac x)
apply(simp add:last_length)+
done

theorem rgsound_p:
  "\<turnstile>\<^sub>I P sat\<^sub>p [pre, rely, guar, post] \<Longrightarrow> \<Turnstile>\<^sub>I P sat\<^sub>p [pre, rely, guar, post]"
apply(erule rghoare_p.induct)
using RG_Hoare.Basic_sound apply(simp add:prog_validity_def com_validity_def) apply blast
using RG_Hoare.Seq_sound apply(simp add:prog_validity_def com_validity_def) apply blast
using RG_Hoare.Cond_sound apply(simp add:prog_validity_def com_validity_def) apply blast
using RG_Hoare.While_sound apply(simp add:prog_validity_def com_validity_def) apply blast 
using Await_sound apply fastforce
apply(force elim:None_sound)
apply(erule Conseq_sound,simp+) 
apply(erule Unprecond_sound,simp+)
apply(erule Intpostcond_sound,simp+)
using Allprecond_sound apply force
using Emptyprecond_sound apply force
done


end