section \<open>Computations of PiCore Language\<close>

theory PiCore_Computation
imports PiCore_Semantics
begin

subsection \<open>Environment transitions\<close>

locale event_comp = event ptran petran fin_com
for ptran :: "'Env \<Rightarrow> (('s,'prog) pconf \<times> ('s,'prog) pconf) set" 
and petran :: "'Env \<Rightarrow> ('s,'prog) pconf \<Rightarrow> ('s,'prog) pconf \<Rightarrow> bool"  ("_ \<turnstile> _ -pe\<rightarrow> _" [81,81,81] 80)
and fin_com :: "'prog"
+
fixes cpts_p :: "'Env \<Rightarrow> ('s,'prog) pconfs set"
fixes cpts_of_p :: "'Env \<Rightarrow> 'prog \<Rightarrow> 's \<Rightarrow> (('s,'prog) pconfs) set"
(*assumes cpts_p_simps:
    "((\<exists>P s. aa = [(P, s)]) \<or>
     (\<exists>P t xs s. aa = (P, s) # (P, t) # xs \<and> \<Gamma> \<turnstile> (P, s) -pe\<rightarrow> (P, t) \<and> (P, t) # xs \<in> cpts_p \<Gamma>) \<or>
     (\<exists>P s Q t xs. aa = (P, s) # (Q, t) # xs \<and> \<Gamma> \<turnstile> (P, s) -c\<rightarrow> (Q, t) \<and> (Q, t) # xs \<in> cpts_p \<Gamma>)) \<Longrightarrow> (aa \<in> cpts_p \<Gamma>)"*)
assumes cpts_p_simps:
    "((\<exists>P s. aa = [(P, s)]) \<or>
     (\<exists>P t xs s. aa = (P, s) # (P, t) # xs \<and> (P, t) # xs \<in> cpts_p \<Gamma>) \<or>
     (\<exists>P s Q t xs. aa = (P, s) # (Q, t) # xs \<and> \<Gamma> \<turnstile> (P, s) -c\<rightarrow> (Q, t) \<and> (Q, t) # xs \<in> cpts_p \<Gamma>)) \<Longrightarrow> (aa \<in> cpts_p \<Gamma>)"
assumes cptn_not_empty [simp]:"[] \<notin> cpts_p \<Gamma>" 
(* assumes cpts_of_p_def: "cpts_of_p \<Gamma> P s \<equiv> {l. l!0=(P,s) \<and> l \<in> cpts_p \<Gamma>}" *)
assumes cpts_of_p_def: "l!0 = (P,s) \<and> l \<in> cpts_p \<Gamma> \<Longrightarrow> l \<in> cpts_of_p \<Gamma> P s" 

begin

lemma CptsPOne: "[(P,s)] \<in> cpts_p \<Gamma>"                      
  using cpts_p_simps[of "[(P,s)]" \<Gamma>] by auto

lemma CptsPEnv: "(P, t)#xs \<in> cpts_p \<Gamma> \<Longrightarrow> (P,s)#(P,t)#xs \<in> cpts_p \<Gamma>" 
  using cpts_p_simps[of "(P, s) # (P, t) # xs" \<Gamma>] by auto
 
lemma CptsPComp: "\<lbrakk>\<Gamma> \<turnstile> (P,s) -c\<rightarrow> (Q,t); (Q, t)#xs \<in> cpts_p \<Gamma>\<rbrakk> \<Longrightarrow> (P,s)#(Q,t)#xs \<in> cpts_p \<Gamma>"
  using cpts_p_simps[of "(P, s) # (Q, t) # xs" \<Gamma> ] by auto

subsection \<open>Sequential computations\<close>

subsubsection \<open>Sequential computations of programs\<close>

(*
lemma cptn_not_empty [simp]:"[] \<notin> cpts_p \<Gamma>" using cpts_p_simps by blast 
*)

inductive
  eetran :: "'Env \<Rightarrow> ('l,'k,'s,'prog) econf \<Rightarrow> ('l,'k,'s,'prog) econf \<Rightarrow> bool"  ("_ \<turnstile> _ -ee\<rightarrow> _" [81,81,81] 80)
for \<Gamma> :: 'Env
where (*EnvEP: "\<Gamma> \<turnstile> (P, s) -pe\<rightarrow> (P, t) \<Longrightarrow> \<Gamma> \<turnstile> (P, s, x) -ee\<rightarrow> (P, t, x)" |   (* simulate env tran of program*)
      EnvEE: "\<Gamma> \<turnstile> (P, s, x) -ee\<rightarrow> (P, s, y)" (* simulate event entry *)*)
 EnvE: "\<Gamma> \<turnstile> (P, s, x) -ee\<rightarrow> (P, t, y)"

lemma eetranE: "\<Gamma> \<turnstile> p -ee\<rightarrow> p' \<Longrightarrow> (\<And>P s t. p = (P, s) \<Longrightarrow> p' = (P, t) \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (induct p, induct p', erule eetran.cases, blast)

inductive
  esetran :: "'Env \<Rightarrow> ('l,'k,'s,'prog) esconf \<Rightarrow> ('l,'k,'s,'prog) esconf \<Rightarrow> bool"  ("_ \<turnstile> _ -ese\<rightarrow> _" [81,81,81] 80)
where
   EnvES: "\<Gamma> \<turnstile> (P, s, x) -ese\<rightarrow> (P, t, y)"

lemma esetranE: "\<Gamma> \<turnstile> p -ese\<rightarrow> p' \<Longrightarrow> (\<And>P s t. p = (P, s) \<Longrightarrow> p' = (P, t) \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (induct p, induct p', erule esetran.cases, blast)

inductive
  pesetran :: "'Env \<Rightarrow> ('l,'k,'s,'prog) pesconf \<Rightarrow> ('l,'k,'s,'prog) pesconf \<Rightarrow> bool"  ("_ \<turnstile> _ -pese\<rightarrow> _" [81,81,81] 80)
where
  EnvPES: "\<Gamma> \<turnstile> (P, s, x) -pese\<rightarrow> (P, t, y)"

lemma pesetranE: "\<Gamma> \<turnstile> p -pese\<rightarrow> p' \<Longrightarrow> (\<And>P s t. p = (P, s) \<Longrightarrow> p' = (P, t) \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (induct p, induct p', erule pesetran.cases, blast)

subsubsection \<open>Sequential computations of events\<close>

inductive_set cpts_ev :: "'Env \<Rightarrow> ('l,'k,'s,'prog) econfs set"
for \<Gamma> :: 'Env
where
  CptsEvOne: "[(e,s,x)] \<in> cpts_ev \<Gamma>"
| CptsEvEnv: "(e, t, x)#xs \<in> cpts_ev \<Gamma> \<Longrightarrow> (e, s, y)#(e, t, x)#xs \<in> cpts_ev \<Gamma>"
| CptsEvComp: "\<lbrakk>\<Gamma> \<turnstile> (e1,s,x) -et-ct\<rightarrow> (e2,t,y); (e2,t,y)#xs \<in> cpts_ev \<Gamma>\<rbrakk> \<Longrightarrow> (e1,s,x)#(e2,t,y)#xs \<in> cpts_ev \<Gamma>"

definition cpts_of_ev :: "'Env \<Rightarrow> ('l,'k,'s,'prog) event \<Rightarrow> 's \<Rightarrow> ('l,'k,'s,'prog) x \<Rightarrow> ('l,'k,'s,'prog) econfs set" where
  "cpts_of_ev \<Gamma> ev s x \<equiv> {l. l!0=(ev,(s,x)) \<and> l \<in> cpts_ev \<Gamma>}" 

subsubsection \<open>Sequential computations of event systems\<close>

inductive_set cpts_es :: "'Env \<Rightarrow> ('l,'k,'s,'prog) esconfs set"
for \<Gamma> :: 'Env
where
  CptsEsOne: "[(es,s,x)] \<in> cpts_es \<Gamma>"
| CptsEsEnv: "(es, t, x)#xs \<in> cpts_es \<Gamma> \<Longrightarrow> (es, s, y)#(es, t, x)#xs \<in> cpts_es \<Gamma>"
| CptsEsComp: "\<lbrakk>\<Gamma> \<turnstile> (es1,s,x) -es-ct\<rightarrow> (es2,t,y); (es2,t,y)#xs \<in> cpts_es \<Gamma>\<rbrakk> \<Longrightarrow> (es1,s,x)#(es2,t,y)#xs \<in> cpts_es \<Gamma>"

definition cpts_of_es :: "'Env \<Rightarrow> ('l,'k,'s,'prog) esys \<Rightarrow> 's \<Rightarrow> ('l,'k,'s,'prog) x \<Rightarrow> ('l,'k,'s,'prog) esconfs set" where
  "cpts_of_es \<Gamma> es s x \<equiv> {l. l!0=(es,s,x) \<and> l \<in> cpts_es \<Gamma>}" 

subsubsection \<open>Sequential computations of par event systems\<close>


inductive_set cpts_pes :: "'Env \<Rightarrow> ('l,'k,'s,'prog) pesconfs set"
for \<Gamma> :: 'Env
where
  CptsPesOne: "[(pes,s,x)] \<in> cpts_pes \<Gamma>"
| CptsPesEnv: "(pes, t, x)#xs \<in> cpts_pes \<Gamma> \<Longrightarrow> (pes, s, y)#(pes, t, x)#xs \<in> cpts_pes \<Gamma>"
| CptsPesComp: "\<lbrakk>\<Gamma> \<turnstile> (pes1,s,x) -pes-ct\<rightarrow> (pes2,t,y); (pes2,t,y)#xs \<in> cpts_pes \<Gamma>\<rbrakk> \<Longrightarrow> (pes1,s,x)#(pes2,t,y)#xs \<in> cpts_pes \<Gamma>"

definition cpts_of_pes :: "'Env \<Rightarrow> ('l,'k,'s,'prog) paresys \<Rightarrow> 's \<Rightarrow> ('l,'k,'s,'prog) x \<Rightarrow> ('l,'k,'s,'prog) pesconfs set" where
  "cpts_of_pes \<Gamma> pes s x \<equiv> {l. l!0=(pes,s,x) \<and> l \<in> cpts_pes \<Gamma>}" 

subsection \<open>Lemmas\<close>
(*
subsubsection \<open>Programs\<close>

lemma tl_in_cptn: "\<lbrakk> a#xs \<in>cpts_p \<Gamma>; xs\<noteq>[] \<rbrakk> \<Longrightarrow> xs\<in>cpts_p \<Gamma>"
  by (force elim: cpts_p.cases)

lemma tl_zero[rule_format]: 
  "P (ys!Suc j) \<longrightarrow> Suc j<length ys \<longrightarrow> ys\<noteq>[] \<longrightarrow> P (tl(ys)!j)"
  by (induct ys) simp_all
*)

subsubsection \<open>Events\<close>

lemma cpts_e_not_empty [simp]:"[] \<notin> cpts_ev \<Gamma>"
apply(force elim:cpts_ev.cases)
done

lemma eetran_eqconf: "\<Gamma> \<turnstile> (e1, s1, x1) -ee\<rightarrow> (e2, s2, x2) \<Longrightarrow> e1 = e2"
  apply(rule eetran.cases)
  apply(simp)+
  done

lemma eetran_eqconf1: "\<Gamma> \<turnstile> ec1 -ee\<rightarrow> ec2 \<Longrightarrow> getspc_e ec1 = getspc_e ec2"
  proof -
    assume a0: "\<Gamma> \<turnstile> ec1 -ee\<rightarrow> ec2"
    then obtain e1 and s1 and x1 and e2 and s2 and x2 where a1: "ec1 = (e1, s1, x1)" and a2: "ec2 = (e2, s2, x2)"
      by (meson prod_cases3) 
    then have "e1 = e2" using a0 eetran_eqconf by fastforce 
    with a1 show ?thesis by (simp add: a2 getspc_e_def) 
  qed

lemma eqconf_eetran1: "e1 = e2 \<Longrightarrow> \<Gamma> \<turnstile> (e1, s1, x1) -ee\<rightarrow> (e2, s2, x2)"
  by (simp add: eetran.intros) 

lemma eqconf_eetran: "getspc_e ec1 = getspc_e ec2 \<Longrightarrow> \<Gamma> \<turnstile> ec1 -ee\<rightarrow> ec2" 
  proof -
    assume "getspc_e ec1 = getspc_e ec2"
    then show ?thesis using getspc_e_def eetran.EnvE by (metis eq_fst_iff)
  qed


lemma cpts_ev_sub0: "\<lbrakk>el \<in> cpts_ev \<Gamma>; Suc 0 < length el\<rbrakk> \<Longrightarrow> drop (Suc 0) el \<in> cpts_ev \<Gamma>"
  apply(rule cpts_ev.cases)
  apply(simp)+
  done  

lemma cpts_ev_subi: "\<lbrakk>el \<in> cpts_ev \<Gamma>; Suc i < length el\<rbrakk> \<Longrightarrow> drop (Suc i) el \<in> cpts_ev \<Gamma>"
  proof -
    assume p0:"el \<in> cpts_ev \<Gamma>" and p1:"Suc i < length el"
    have "\<forall>el i. el \<in> cpts_ev \<Gamma> \<and> Suc i < length el \<longrightarrow> drop (Suc i) el \<in> cpts_ev \<Gamma>"
      proof -
      {
        fix el i
        have "el \<in> cpts_ev \<Gamma> \<and> Suc i < length el \<longrightarrow> drop (Suc i) el \<in> cpts_ev \<Gamma>"
          proof(induct i)
            case 0 show ?case by (simp add: cpts_ev_sub0) 
          next
            case (Suc j)
            assume b0: "el \<in> cpts_ev \<Gamma> \<and> Suc j < length el \<longrightarrow> drop (Suc j) el \<in> cpts_ev \<Gamma>"
            show ?case
              proof
                assume c0: "el \<in> cpts_ev \<Gamma> \<and> Suc (Suc j) < length el"
                with b0 have c1: "drop (Suc j) el \<in> cpts_ev \<Gamma>"
                  by (simp add: c0 Suc_lessD)                 
                then show "drop (Suc (Suc j)) el \<in> cpts_ev \<Gamma>"
                  using c0 cpts_ev_sub0 by fastforce 
              qed
          qed
      }
      then show ?thesis by auto
      qed
    with p0 p1 show ?thesis by auto
  qed
  
lemma notran_confeq0: "\<lbrakk>el \<in> cpts_ev \<Gamma>; Suc 0 < length el; \<not> (\<exists>t. \<Gamma> \<turnstile> el ! 0 -et-t\<rightarrow> el ! 1)\<rbrakk>
                      \<Longrightarrow> getspc_e (el ! 0) = getspc_e (el ! 1)"
  apply(simp)
  apply(rule cpts_ev.cases)
  apply(simp)+
  apply(simp add:getspc_e_def)+
  done

lemma notran_confeqi: "\<lbrakk>el \<in> cpts_ev \<Gamma>; Suc i < length el; \<not> (\<exists>t. \<Gamma> \<turnstile> el ! i -et-t\<rightarrow> el ! Suc i)\<rbrakk>
                      \<Longrightarrow> getspc_e (el ! i) = getspc_e (el ! (Suc i))"
  proof -
    assume p0: "el \<in> cpts_ev \<Gamma>" and
           p1: "Suc i < length el" and
           p2: "\<not> (\<exists>t. \<Gamma> \<turnstile> el ! i -et-t\<rightarrow> el ! Suc i)"
    have "\<forall>el i. el \<in> cpts_ev \<Gamma> \<and>  Suc i < length el \<and> \<not> (\<exists>t. \<Gamma> \<turnstile> el ! i -et-t\<rightarrow> el ! Suc i)
                \<longrightarrow> getspc_e (el ! i) = getspc_e (el ! (Suc i))"
      proof -
      {
        fix el i
        assume a0: "el \<in> cpts_ev \<Gamma> \<and>  Suc i < length el \<and> \<not> (\<exists>t. \<Gamma> \<turnstile> el ! i -et-t\<rightarrow> el ! Suc i)"
        then have "getspc_e (el ! i) = getspc_e (el ! (Suc i))"
          proof(induct i)
            case 0 then show ?case
              using notran_confeq0 by (metis One_nat_def)
          next
            case (Suc j)
            let ?subel = "drop (Suc j) el"
            assume b0: "el \<in> cpts_ev \<Gamma> \<and> Suc (Suc j) < length el \<and> \<not> (\<exists>t. \<Gamma> \<turnstile> el ! Suc j -et-t\<rightarrow> el ! Suc (Suc j))"            
            then have b1: "?subel \<in> cpts_ev \<Gamma>" by (simp add: Suc_lessD b0 cpts_ev_subi) 
            from b0 have b2: "Suc 0 < length ?subel" by auto 
            from b0 have b3: "\<not> (\<exists>t. \<Gamma> \<turnstile> ?subel ! 0 -et-t\<rightarrow> ?subel ! 1)" by auto
            with b1 b2 have b3: "getspc_e (?subel ! 0) = getspc_e (?subel ! 1)"
              using notran_confeq0 by blast
            then show ?case
              by (metis Cons_nth_drop_Suc One_nat_def Suc_lessD b0 nth_Cons_0 nth_Cons_Suc) 
          qed
      }
      then show ?thesis by auto
      qed
    with p0 p1 p2 show ?thesis by auto
  qed

lemma cpts_ev_onemore: "\<lbrakk>el \<in> cpts_ev \<Gamma>; length el > 0; \<Gamma> \<turnstile> el ! (length el - 1) -et-t\<rightarrow> ec\<rbrakk> \<Longrightarrow>
                          el @ [ec] \<in> cpts_ev \<Gamma>"
  proof -
    assume p0: "el \<in> cpts_ev \<Gamma>"
      and  p1: "length el > 0"
      and  p2: "\<Gamma> \<turnstile> el ! (length el - 1) -et-t\<rightarrow> ec"

    have "\<forall>el ec t \<Gamma>. el \<in> cpts_ev \<Gamma> \<and> length el > 0 \<and> \<Gamma> \<turnstile> el ! (length el - 1) -et-t\<rightarrow> ec \<longrightarrow> el @ [ec] \<in> cpts_ev \<Gamma>"
      proof -
      {
        fix el ec t \<Gamma>
        assume a0: "el \<in> cpts_ev \<Gamma>"
          and  a1: "length el > 0"
          and  a2: "\<Gamma> \<turnstile> el ! (length el - 1) -et-t\<rightarrow> ec"
        from a0 a1 a2 have "el @ [ec] \<in> cpts_ev \<Gamma>"
          proof(induct el)
            case (CptsEvOne e s x) 
            assume b0: "\<Gamma> \<turnstile> [(e, s, x)] ! (length [(e, s, x)] - 1) -et-t\<rightarrow> ec"
            then have "\<Gamma> \<turnstile> (e, s, x) -et-t\<rightarrow> ec" by simp
            then show ?case by (metis append_Cons append_Nil cpts_ev.CptsEvComp 
                  cpts_ev.CptsEvOne surj_pair) 
          next
            case (CptsEvEnv e s1 x xs s2 y)
            assume b0: "(e, s1, x) # xs \<in> cpts_ev \<Gamma>"
              and  b1: "0 < length ((e, s1, x) # xs) \<Longrightarrow>
                        \<Gamma> \<turnstile> ((e, s1, x) # xs) ! (length ((e, s1, x) # xs) - 1) -et-t\<rightarrow> ec 
                        \<Longrightarrow> ((e, s1, x) # xs) @ [ec] \<in> cpts_ev \<Gamma>"
              and  b2: "0 < length ((e, s2, y) # (e, s1, x) # xs)"
              and  b3: "\<Gamma> \<turnstile> ((e, s2, y) # (e, s1, x) # xs) ! (length ((e, s2, y) # (e, s1, x) # xs) - 1) -et-t\<rightarrow> ec"
            then show ?case 
              proof(cases "xs = []")
                assume c0: "xs = []"
                with b3 have "\<Gamma> \<turnstile> (e, s1, x)-et-t\<rightarrow> ec" by simp
                with b1 c0 have "((e, s1, x) # xs) @ [ec] \<in> cpts_ev \<Gamma>" by simp
                then show ?thesis by (simp add: cpts_ev.CptsEvEnv) 
              next
                assume c0: "xs \<noteq> []"
                with b3 have "\<Gamma> \<turnstile> last xs -et-t\<rightarrow> ec" by (simp add: last_conv_nth) 
                with b1 c0 have "((e, s1, x) # xs) @ [ec] \<in> cpts_ev \<Gamma>" using b3 by auto
                then show ?thesis by (simp add: cpts_ev.CptsEvEnv) 
              qed
          next
            case (CptsEvComp e1 s1 x1 et e2 t1 y1 xs1)
            assume b0: "\<Gamma> \<turnstile> (e1, s1, x1) -et-et\<rightarrow> (e2, t1, y1)"
              and  b1: "(e2, t1, y1) # xs1 \<in> cpts_ev \<Gamma>"
              and  b2: "0 < length ((e2, t1, y1) # xs1) \<Longrightarrow>
                \<Gamma> \<turnstile> ((e2, t1, y1) # xs1) ! (length ((e2, t1, y1) # xs1) - 1) -et-t\<rightarrow> ec 
                  \<Longrightarrow> ((e2, t1, y1) # xs1) @ [ec] \<in> cpts_ev \<Gamma>"
              and  b3: "0 < length ((e1, s1, x1) # (e2, t1, y1) # xs1)"
              and  b4: "\<Gamma> \<turnstile> ((e1, s1, x1) # (e2, t1, y1) # xs1) ! (length ((e1, s1, x1) # (e2, t1, y1) # xs1) - 1) -et-t\<rightarrow> ec"
            then show ?case 
              proof(cases "xs1 = []")
                assume c0: "xs1 = []"
                with b4 have "\<Gamma> \<turnstile> (e2, t1, y1)-et-t\<rightarrow> ec" by simp
                with b2 c0 have "((e2, t1, y1) # xs1) @ [ec] \<in> cpts_ev \<Gamma>" by simp
                with b0 show ?thesis using cpts_ev.CptsEvComp by fastforce 
              next
                assume c0: "xs1 \<noteq> []"
                with b4 have "\<Gamma> \<turnstile> last xs1 -et-t\<rightarrow> ec" by (simp add: last_conv_nth)
                with b2 c0 have "((e2, t1, y1) # xs1) @ [ec] \<in> cpts_ev \<Gamma>" using b4 by auto 
                then show ?thesis using b0 cpts_ev.CptsEvComp by fastforce 
              qed
          qed
      }
      then show ?thesis by auto
      qed

    then show "el @ [ec] \<in> cpts_ev \<Gamma>" using p0 p1 p2 by blast 
  qed

lemma cpts_ev_same: "\<lbrakk>length el > 0; \<forall>i. i < length el \<longrightarrow> getspc_e (el!i) = es\<rbrakk> \<Longrightarrow> el \<in> cpts_ev \<Gamma>"
  proof -
    assume p0: "length el > 0"
      and  p1: "\<forall>i. i < length el \<longrightarrow> getspc_e (el!i) = es"
    have "\<forall>el es. length el > 0 \<and> (\<forall>i. i < length el \<longrightarrow> getspc_e (el!i) = es) \<longrightarrow> el \<in> cpts_ev \<Gamma>"
      proof -
      {
        fix el es
        assume a0: "length (el :: ('l,'k,'s,'prog) econfs) > 0"
          and  a1: "\<forall>i. i < length el \<longrightarrow> getspc_e (el!i) = es"
        then have "el \<in> cpts_ev \<Gamma>"
          proof(induct el)
            case Nil show ?case using Nil.prems(1) by auto 
          next
            case (Cons a as)
            assume b0: "0 < length as \<Longrightarrow> \<forall>i<length as. getspc_e (as ! i) = es \<Longrightarrow> as \<in> cpts_ev \<Gamma>"
              and  b1: "0 < length (a # as)"
              and  b2: "\<forall>i<length (a # as). getspc_e ((a # as) ! i) = es"
            then show ?case
              proof(cases "as = []")
                assume c0: "as = []"
                then show ?thesis by (metis cpts_ev.CptsEvOne old.prod.exhaust) 
              next
                assume c0: "\<not>(as = [])"
                then obtain b and bs where c1: "as = b # bs" by (meson neq_Nil_conv) 
                from c0 have "0 < length as" by simp
                with b0 have "\<forall>i<length as. getspc_e (as ! i) = es \<Longrightarrow> as \<in> cpts_ev \<Gamma>" by simp
                with b2 have "as \<in> cpts_ev \<Gamma>" by force
                moreover from b2 have "getspc_e a = es" by auto
                moreover from b2 c1 have "getspc_e b = es" by auto
                ultimately show ?thesis using c1 getspc_e_def by (metis cpts_ev.CptsEvEnv fst_conv prod_cases3) 
              qed
          qed
      }
      then show ?thesis by auto
      qed

    then show ?thesis using p0 p1 by auto
  qed

subsubsection \<open>Event systems\<close>


lemma cpts_es_not_empty [simp]:"[] \<notin> cpts_es \<Gamma>"
apply(force elim:cpts_es.cases)
done


lemma esetran_eqconf: "\<Gamma> \<turnstile> (es1, s1, x1) -ese\<rightarrow> (es2, s2, x2) \<Longrightarrow> es1 = es2"
  apply(rule esetran.cases)
  apply(simp)+
  done

lemma esetran_eqconf1: "\<Gamma> \<turnstile> esc1 -ese\<rightarrow> esc2 \<Longrightarrow> getspc_es esc1 = getspc_es esc2"
  proof -
    assume a0: "\<Gamma> \<turnstile> esc1 -ese\<rightarrow> esc2"
    then obtain es1 and s1 and x1 and es2 and s2 and x2 where a1: "esc1 = (es1, s1, x1)" and a2: "esc2 = (es2, s2, x2)"
      by (meson prod_cases3) 
    then have "es1 = es2" using a0 esetran_eqconf by fastforce 
    with a1 show ?thesis by (simp add: a2 getspc_es_def) 
  qed

lemma eqconf_esetran1: "es1 = es2 \<Longrightarrow> \<Gamma> \<turnstile> (es1, s1, x1) -ese\<rightarrow> (es2, s2, x2)"
  by (simp add: esetran.intros) 


lemma eqconf_esetran: "getspc_es esc1 = getspc_es esc2 \<Longrightarrow> \<Gamma> \<turnstile> esc1 -ese\<rightarrow> esc2" 
  proof -
    assume a0: "getspc_es esc1 = getspc_es esc2"
    (*then show ?thesis using getspc_es_def esetran.EnvES by (metis eq_fst_iff)*)
    obtain es1 and s1 and x1 where a1: "esc1 = (es1, s1, x1)" using prod_cases3 by blast 
    obtain es2 and s2 and x2 where a2: "esc2 = (es2, s2, x2)" using prod_cases3 by blast 
    with a0 a1 have "es1 = es2" by (simp add:getspc_es_def)
    with a1 a2 have a3: "\<Gamma> \<turnstile> (es1, s1, x1) -ese\<rightarrow> (es2, s2, x2)" by (simp add:eqconf_esetran1)
    from a3 a1 a2 show ?thesis by simp
  qed

lemma exist_estran: "\<lbrakk>(es1, s1, x1) # (es, s, x) # esl \<in> cpts_es \<Gamma>; es1 \<noteq> es\<rbrakk> \<Longrightarrow> (\<exists>est. \<Gamma> \<turnstile> (es1, s1, x1) -es-est\<rightarrow> (es, s, x))"
  apply(rule cpts_es.cases)
  apply(simp)+
  by auto

lemma cpts_es_drop0: "\<lbrakk>el \<in> cpts_es \<Gamma>; Suc 0 < length el\<rbrakk> \<Longrightarrow> drop (Suc 0) el \<in> cpts_es \<Gamma>"
  apply(rule cpts_es.cases)
  apply(simp)+
  done  

lemma cpts_es_dropi: "\<lbrakk>el \<in> cpts_es \<Gamma>; Suc i < length el\<rbrakk> \<Longrightarrow> drop (Suc i) el \<in> cpts_es \<Gamma>"
  proof -
    assume p0:"el \<in> cpts_es \<Gamma>" and p1:"Suc i < length el"
    have "\<forall>el i. el \<in> cpts_es \<Gamma> \<and> Suc i < length el \<longrightarrow> drop (Suc i) el \<in> cpts_es \<Gamma>"
      proof -
      {
        fix el i
        have "el \<in> cpts_es \<Gamma> \<and> Suc i < length el \<longrightarrow> drop (Suc i) el \<in> cpts_es \<Gamma>"
          proof(induct i)
            case 0 show ?case by (simp add: cpts_es_drop0) 
          next
            case (Suc j)
            assume b0: "el \<in> cpts_es \<Gamma> \<and> Suc j < length el \<longrightarrow> drop (Suc j) el \<in> cpts_es \<Gamma>"
            show ?case
              proof
                assume c0: "el \<in> cpts_es \<Gamma> \<and> Suc (Suc j) < length el"
                with b0 have c1: "drop (Suc j) el \<in> cpts_es \<Gamma>"
                  by (simp add: c0 Suc_lessD)                 
                then show "drop (Suc (Suc j)) el \<in> cpts_es \<Gamma>"
                  using c0 cpts_es_drop0 by fastforce 
              qed
          qed
      }
      then show ?thesis by auto
      qed
    with p0 p1 show ?thesis by auto
  qed


lemma cpts_es_dropi2: "\<lbrakk>el \<in> cpts_es \<Gamma>; i < length el\<rbrakk> \<Longrightarrow> drop i el \<in> cpts_es \<Gamma>"
  using cpts_es_dropi by (metis (no_types, hide_lams) drop_0 lessI less_Suc_eq_0_disj) 

lemma cpts_es_take0: "\<lbrakk>el \<in> cpts_es \<Gamma>; i < length el; el1 = take (Suc i) el; j < length el1\<rbrakk> 
                        \<Longrightarrow> drop (length el1 - Suc j) el1 \<in> cpts_es \<Gamma>"
  proof -
    assume p0: "el \<in> cpts_es \<Gamma>"
      and  p1: "i < length el"
      and  p2: "el1 = take (Suc i) el"
      and  p3: "j < length el1"
    have "\<forall>i j. el \<in> cpts_es \<Gamma> \<and> i < length el \<and> el1 = take (Suc i) el \<and> j < length el1 
          \<longrightarrow> drop (length el1 - Suc j) el1 \<in> cpts_es \<Gamma>"
      proof -
      {
        fix i j
        assume a0: "el \<in> cpts_es \<Gamma>"
          and  a1: "i < length el"
          and  a2: "el1 = take (Suc i) el"
          and  a3: "j < length el1"
        then have "drop (length el1 - Suc j) el1 \<in> cpts_es \<Gamma>"
          proof(induct j)
            case 0 
            have "drop (length el1 - Suc 0) el1 = [el ! i]"
              by (simp add: a1 a2 take_Suc_conv_app_nth) 
            then show ?case by (metis cpts_es.CptsEsOne old.prod.exhaust) 
          next
            case (Suc jj)
            assume b0: "el \<in> cpts_es \<Gamma> \<Longrightarrow> i < length el \<Longrightarrow> el1 = take (Suc i) el 
                        \<Longrightarrow> jj < length el1 \<Longrightarrow> drop (length el1 - Suc jj) el1 \<in> cpts_es \<Gamma>"
              and  b1: "el \<in> cpts_es \<Gamma>"
              and  b2: "i < length el"
              and  b3: "el1 = take (Suc i) el"
              and  b4: "Suc jj < length el1"
            then have b5: "drop (length el1 - Suc jj) el1 \<in> cpts_es \<Gamma>"
              using Suc_lessD by blast 
            let ?el2 = "drop (Suc i) el"
            from a2 have b6: "el1 @ ?el2 = el" by simp
            let ?el1sht = "drop (length el1 - Suc jj) el1"
            let ?el1lng = "drop (length el1 - Suc (Suc jj)) el1"
            let ?elsht = "drop (length el1 - Suc jj) el"
            let ?ellng = "drop (length el1 - Suc (Suc jj)) el"
            from b6 have a7: "?el1sht @ ?el2 = ?elsht"
              by (metis diff_is_0_eq diff_le_self drop_0 drop_append) 
            from b6 have a8: "?el1lng @ ?el2 = ?ellng"
              by (metis (no_types, lifting) a7 append_eq_append_conv diff_is_0_eq' diff_le_self drop_append) 
            have a9: "?ellng = (el ! (length el1 - Suc (Suc jj))) # ?elsht"
              by (metis (no_types, lifting) Cons_nth_drop_Suc Suc_diff_Suc Suc_leI a8 
                  append_is_Nil_conv b4 diff_diff_cancel drop_all length_drop 
                  list.size(3) not_less old.nat.distinct(2)) 
            from b1 b4 have a10: "?elsht \<in> cpts_es \<Gamma>"
              by (metis a7 append_is_Nil_conv b5 cpts_es_dropi2 drop_all not_less)
            from b1 b4 have a11: "?ellng \<in> cpts_es \<Gamma>"
              by (metis a9 cpts_es_dropi2 drop_all list.simps(3) not_less)
            have a12: "?el1lng = (el ! (length el1 - Suc (Suc jj))) # ?el1sht"
              by (metis (no_types, lifting) Cons_nth_drop_Suc Suc_diff_Suc 
                b4 b6 diff_less gr_implies_not0 length_0_conv length_greater_0_conv 
                nth_append zero_less_Suc)
            from a11 have "?el1lng \<in> cpts_es \<Gamma>"
              proof(induct ?ellng)
                case CptsEsOne show ?case
                  using CptsEsOne.hyps a7 a9 by auto 
              next
                case (CptsEsEnv es1 t1 x1 xs1 s1 y1)
                assume c0: "(es1, t1, x1) # xs1 \<in> cpts_es \<Gamma>"
                  and  c1: "(es1, t1, x1) # xs1 = drop (length el1 - Suc (Suc jj)) el \<Longrightarrow>
                            drop (length el1 - Suc (Suc jj)) el1 \<in> cpts_es \<Gamma>"
                  and  c2: "(es1, s1, y1) # (es1, t1, x1) # xs1 = drop (length el1 - Suc (Suc jj)) el"
                from c0 have "(es1, s1, y1) # (es1, t1, x1) # xs1 \<in> cpts_es \<Gamma>"
                  by (simp add: a11 c2) 
                have c3: "?el1sht ! 0 = (es1, t1, x1)" by (metis (no_types, lifting) Suc_leI Suc_lessD a7 
                        a9 append_eq_Cons_conv b4 c2 diff_diff_cancel length_drop list.inject 
                        list.size(3) nth_Cons_0 old.nat.distinct(2)) 
                then have c4: "\<exists>el1sht'. ?el1sht = (es1, t1, x1) # el1sht'" by (metis Cons_nth_drop_Suc b4 
                    diff_diff_cancel drop_0 length_drop less_or_eq_imp_le zero_less_Suc) 
                have c5: "?el1lng = (es1, s1, y1) # ?el1sht" using a12 a9 c2 by auto 
                
                with b5 c4 show ?case using cpts_es.CptsEsEnv by fastforce 
              next
                case (CptsEsComp es1 s1 x1 et es2 t1 y1 xs1)
                assume c0: "\<Gamma> \<turnstile> (es1, s1, x1) -es-et\<rightarrow> (es2, t1, y1)"
                  and  c1: "(es2, t1, y1) # xs1 \<in> cpts_es \<Gamma>"
                  and  c2: "(es2, t1, y1) # xs1 = drop (length el1 - Suc (Suc jj)) el 
                            \<Longrightarrow> drop (length el1 - Suc (Suc jj)) el1 \<in> cpts_es \<Gamma>"
                  and  c3: "(es1, s1, x1) # (es2, t1, y1) # xs1 = drop (length el1 - Suc (Suc jj)) el"
                have c4: "?el1sht ! 0 = (es2, t1, y1)" by (metis (no_types, lifting) Suc_leI Suc_lessD a7 
                        a9 append_eq_Cons_conv b4 c3 diff_diff_cancel length_drop list.inject 
                        list.size(3) nth_Cons_0 old.nat.distinct(2)) 
                then have c5: "\<exists>el1sht'. ?el1sht = (es2, t1, y1) # el1sht'" by (metis Cons_nth_drop_Suc b4 
                    diff_diff_cancel drop_0 length_drop less_or_eq_imp_le zero_less_Suc) 
                have c6: "?el1lng = (es1, s1, x1) # ?el1sht" using a12 a9 c3 by auto
                with b5 c5  show ?case using c0 cpts_es.CptsEsComp by fastforce 
              qed

            then show ?case by simp
          qed
      }
      then show ?thesis by auto
      qed
    then show "drop (length el1 - Suc j) el1 \<in> cpts_es \<Gamma>"
      using p0 p1 p2 p3 by blast 
  qed


lemma cpts_es_take: "\<lbrakk>el \<in> cpts_es \<Gamma>; i < length el\<rbrakk> \<Longrightarrow> take (Suc i) el \<in> cpts_es \<Gamma>"
  using cpts_es_take0 gr_implies_not0 by fastforce

lemma cpts_es_seg: "\<lbrakk>el \<in> cpts_es \<Gamma>; m \<le> length el; n \<le> length el; m < n\<rbrakk> 
                    \<Longrightarrow> take (n - m) (drop m el) \<in> cpts_es \<Gamma>"
  proof -
    assume p0: "el \<in> cpts_es \<Gamma>"
      and  p1: "m \<le> length el"
      and  p2: "n \<le> length el"
      and  p3: "m < n"
    then have "drop m el \<in> cpts_es \<Gamma>" 
      using cpts_es_dropi by (metis (no_types, lifting) drop_0 le_0_eq le_SucE less_le_trans zero_induct) 
    then show ?thesis using cpts_es_take
      by (metis (no_types, lifting) cpts_es_dropi2 drop_take inc_induct 
        leD le_SucE length_take min.absorb2 p0 p1 p2 p3)
  qed

lemma cpts_es_seg2: "\<lbrakk>el \<in> cpts_es \<Gamma>; m \<le> length el; n \<le> length el; take (n - m) (drop m el) \<noteq> []\<rbrakk> 
                    \<Longrightarrow> take (n - m) (drop m el) \<in> cpts_es \<Gamma>"
  proof -
    assume p0: "el \<in> cpts_es \<Gamma>"
      and  p1: "m \<le> length el"
      and  p2: "n \<le> length el"
      and  p3: "take (n - m) (drop m el) \<noteq> []"
    from p3 have "m < n" by simp
    then show ?thesis using cpts_es_seg using p0 p1 p2 by blast
  qed

lemma cpts_es_same: "\<lbrakk>length el > 0; \<forall>i. i < length el \<longrightarrow> getspc_es (el!i) = es\<rbrakk> \<Longrightarrow> el \<in> cpts_es \<Gamma>"
  proof -
    assume p0: "length el > 0"
      and  p1: "\<forall>i. i < length el \<longrightarrow> getspc_es (el!i) = es"
    have "\<forall>el es. length el > 0 \<and> (\<forall>i. i < length el \<longrightarrow> getspc_es (el!i) = es) \<longrightarrow> el \<in> cpts_es \<Gamma>"
      proof -
      {
        fix el es
        assume a0: "length (el :: ('l,'k,'s,'prog) esconf list) > 0"
          and  a1: "\<forall>i. i < length el \<longrightarrow> getspc_es (el!i) = es"
        then have "el \<in> cpts_es \<Gamma>"
          proof(induct el)
            case Nil show ?case using Nil.prems(1) by auto 
          next
            case (Cons a as)
            assume b0: "0 < length as \<Longrightarrow> \<forall>i<length as. getspc_es (as ! i) = es \<Longrightarrow> as \<in> cpts_es \<Gamma>"
              and  b1: "0 < length (a # as)"
              and  b2: "\<forall>i<length (a # as). getspc_es ((a # as) ! i) = es"
            then show ?case
              proof(cases "as = []")
                assume c0: "as = []"
                then show ?thesis by (metis cpts_es.CptsEsOne old.prod.exhaust) 
              next
                assume c0: "\<not>(as = [])"
                then obtain b and bs where c1: "as = b # bs" by (meson neq_Nil_conv) 
                from c0 have "0 < length as" by simp
                with b0 have "\<forall>i<length as. getspc_es (as ! i) = es \<Longrightarrow> as \<in> cpts_es \<Gamma>" by simp
                with b2 have "as \<in> cpts_es \<Gamma>" by force
                moreover from b2 have "getspc_es a = es" by auto
                moreover from b2 c1 have "getspc_es b = es" by auto
                ultimately show ?thesis using c1 getspc_es_def by (metis cpts_es.CptsEsEnv fst_conv prod_cases3) 
              qed
          qed
      }
      then show ?thesis by auto
      qed

    then show ?thesis using p0 p1 by auto
  qed


lemma noevtent_inmid_eq: 
    "(\<not> (\<exists>j. j > 0 \<and> Suc j < length esl \<and> getspc_es (esl ! j) = EvtSys es \<and> getspc_es (esl ! Suc j) \<noteq> EvtSys es))
      = (\<forall>j. j > 0 \<and> Suc j < length esl \<longrightarrow> getspc_es (esl ! j) = EvtSys es \<longrightarrow> getspc_es (esl ! Suc j) = EvtSys es)"
      by blast

lemma evtseq_next_in_cpts:
  "esl\<in>cpts_es \<Gamma> \<Longrightarrow> \<forall>i. Suc i < length esl \<and> getspc_es (esl!i) = EvtSeq e esys
                       \<longrightarrow> getspc_es (esl!Suc i) = esys \<or> (\<exists>e. getspc_es (esl!Suc i) = EvtSeq e esys)"
  proof -
    assume p0: "esl\<in>cpts_es \<Gamma>"
    then show ?thesis
      proof -
      {
        fix i
        assume a0: "Suc i < length esl"
          and  a1: "getspc_es (esl!i) = EvtSeq e esys"
        let ?esl1 = "drop i esl"
        from p0 a0 have a2: "?esl1\<in>cpts_es \<Gamma>" by (metis (no_types, hide_lams) Suc_diff_1 Suc_lessD 
              cpts_es_dropi diff_diff_cancel drop_0 length_drop length_greater_0_conv 
              less_or_eq_imp_le list.size(3)) 
        from a0 a1 have "getspc_es (?esl1!0) = EvtSeq e esys" by auto 
        then obtain s1 and x1 where a3: "?esl1!0 = (EvtSeq e esys,s1,x1)" 
          using getspc_es_def by (metis fst_conv old.prod.exhaust)
        from a2 a1 have "getspc_es (?esl1!1) = esys \<or> (\<exists>e. getspc_es (?esl1!1) = EvtSeq e esys)"
          proof(induct ?esl1)
            case (CptsEsOne es' s' x')
            then show ?case by (metis One_nat_def Suc_eq_plus1_left Suc_lessD a0 
                le_add_diff_inverse2 length_Cons length_drop less_imp_le 
                list.size(3) not_less_iff_gr_or_eq)  
          next
            case (CptsEsEnv es' t' x' xs' s' y')
            assume b0: "(es', s', y') # (es', t', x') # xs' = drop i esl"
              and  b1: "getspc_es (esl ! i) = EvtSeq e esys"
            then have "es' = EvtSeq e esys" using getspc_es_def by (metis a3 fst_conv nth_Cons_0)
            with b0 have "getspc_es (drop i esl ! 1) = EvtSeq e esys" using getspc_es_def
              by (metis One_nat_def fst_conv nth_Cons_0 nth_Cons_Suc) 
            then show ?case by auto
          next
            case (CptsEsComp es1' s' x' et' es2' t' y' xs')
            assume b0: "\<Gamma> \<turnstile> (es1', s', x') -es-et'\<rightarrow> (es2', t', y')"
              and  b1: "(es1', s', x') # (es2', t', y') # xs' = drop i esl"
              and  b2: "getspc_es (esl ! i) = EvtSeq e esys"
            then have b3: "es1' = EvtSeq e esys" 
              by (metis Pair_inject a3 nth_Cons_0)
            from b0 b3 have "es2' = esys \<or> (\<exists>e. es2' = EvtSeq e esys)" 
              using evtseq_tran_sys_or_seq by simp
            with b1 show ?case using getspc_es_def
              by (metis One_nat_def fst_conv nth_Cons_0 nth_Cons_Suc) 
              
          qed

        then have "getspc_es (esl!Suc i) = esys \<or> (\<exists>e. getspc_es (esl!Suc i) = EvtSeq e esys)"
          using a0 by fastforce
      }
      then show ?thesis by auto
      qed
  qed

lemma evtseq_next_in_cpts_anony:
  "esl\<in>cpts_es \<Gamma> \<Longrightarrow> \<forall>i. Suc i < length esl \<and> getspc_es (esl!i) = EvtSeq e esys \<and> is_anonyevt e
                       \<longrightarrow> getspc_es (esl!Suc i) = esys 
                        \<or> (\<exists>e. getspc_es (esl!Suc i) = EvtSeq e esys \<and> is_anonyevt e)"
  proof -
    assume p0: "esl\<in>cpts_es \<Gamma>"
    then show ?thesis
      proof -
      {
        fix i
        assume a0: "Suc i < length esl"
          and  a1: "getspc_es (esl!i) = EvtSeq e esys \<and> is_anonyevt e"
        let ?esl1 = "drop i esl"
        from p0 a0 have a2: "?esl1\<in>cpts_es \<Gamma>" by (metis (no_types, hide_lams) Suc_diff_1 Suc_lessD 
              cpts_es_dropi diff_diff_cancel drop_0 length_drop length_greater_0_conv 
              less_or_eq_imp_le list.size(3)) 
        from a0 a1 have "getspc_es (?esl1!0) = EvtSeq e esys" by auto 
        then obtain s1 and x1 where a3: "?esl1!0 = (EvtSeq e esys,s1,x1)" 
          using getspc_es_def by (metis fst_conv old.prod.exhaust)
        from a2 a1 have "getspc_es (?esl1!1) = esys 
                        \<or> (\<exists>e. getspc_es (?esl1!1) = EvtSeq e esys \<and> is_anonyevt e)"
          proof(induct ?esl1)
            case (CptsEsOne es' s' x')
            then show ?case by (metis One_nat_def Suc_eq_plus1_left Suc_lessD a0 
                le_add_diff_inverse2 length_Cons length_drop less_imp_le 
                list.size(3) not_less_iff_gr_or_eq)  
          next
            case (CptsEsEnv es' t' x' xs' s' y')
            assume b0: "(es', s', y') # (es', t', x') # xs' = drop i esl"
              and  b1: "getspc_es (esl ! i) = EvtSeq e esys \<and> is_anonyevt e"
            then have "es' = EvtSeq e esys" using getspc_es_def by (metis a3 fst_conv nth_Cons_0)
            with b0 have "getspc_es (drop i esl ! 1) = EvtSeq e esys \<and> is_anonyevt e" 
              using getspc_es_def by (metis One_nat_def b1 fst_conv nth_Cons_0 nth_Cons_Suc)
            then show ?case by auto
          next
            case (CptsEsComp es1' s' x' et' es2' t' y' xs')
            assume b0: "\<Gamma> \<turnstile> (es1', s', x') -es-et'\<rightarrow> (es2', t', y')"
              and  b1: "(es1', s', x') # (es2', t', y') # xs' = drop i esl"
              and  b2: "getspc_es (esl ! i) = EvtSeq e esys \<and> is_anonyevt e"
            then have b3: "es1' = EvtSeq e esys" 
              by (metis Pair_inject a3 nth_Cons_0)
            from b0 b3 have "es2' = esys \<or> (\<exists>e. es2' = EvtSeq e esys \<and> is_anonyevt e)" 
              using evtseq_tran_sys_or_seq_anony
              by simp
            with b1 show ?case using getspc_es_def
              by (metis One_nat_def fst_conv nth_Cons_0 nth_Cons_Suc) 
              
          qed

        then have "getspc_es (esl!Suc i) = esys 
          \<or> (\<exists>e. getspc_es (esl!Suc i) = EvtSeq e esys \<and> is_anonyevt e)"
          using a0 by fastforce
      }
      then show ?thesis by auto
      qed
  qed

lemma evtsys_next_in_cpts:
  "esl\<in>cpts_es \<Gamma> \<Longrightarrow> \<forall>i. Suc i < length esl \<and> getspc_es (esl!i) = EvtSys es 
                       \<longrightarrow> getspc_es (esl!Suc i) = EvtSys es \<or> (\<exists>e. getspc_es (esl!Suc i) = EvtSeq e (EvtSys es))"
  proof -
    assume p0: "esl\<in>cpts_es \<Gamma>"
    then show ?thesis
      proof -
      {
        fix i
        assume a0: "Suc i < length esl"
          and  a1: "getspc_es (esl!i) = EvtSys es"
        let ?esl1 = "drop i esl"
        from p0 a0 have a2: "?esl1\<in>cpts_es \<Gamma>" by (metis (no_types, hide_lams) Suc_diff_1 Suc_lessD 
              cpts_es_dropi diff_diff_cancel drop_0 length_drop length_greater_0_conv 
              less_or_eq_imp_le list.size(3)) 
        from a0 a1 have "getspc_es (?esl1!0) = EvtSys es" by auto 
        then obtain s1 and x1 where a3: "?esl1!0 = (EvtSys es,s1,x1)" 
          using getspc_es_def by (metis fst_conv old.prod.exhaust)
        from a2 a1 have "getspc_es (?esl1!1) = EvtSys es \<or> (\<exists>e. getspc_es (?esl1!1) = EvtSeq e (EvtSys es))"
          proof(induct ?esl1)
            case (CptsEsOne es' s' x')
            then show ?case by (metis One_nat_def Suc_eq_plus1_left Suc_lessD a0 
                le_add_diff_inverse2 length_Cons length_drop less_imp_le 
                list.size(3) not_less_iff_gr_or_eq)  
          next
            case (CptsEsEnv es' t' x' xs' s' y')
            assume b0: "(es', s', y') # (es', t', x') # xs' = drop i esl"
              and  b1: "getspc_es (esl ! i) = EvtSys es"
            then have "es' = EvtSys es" using getspc_es_def by (metis a3 fst_conv nth_Cons_0)
            with b0 have "getspc_es (drop i esl ! 1) = EvtSys es" using getspc_es_def
              by (metis One_nat_def fst_conv nth_Cons_0 nth_Cons_Suc) 
            then show ?case by simp
          next
            case (CptsEsComp es1' s' x' et' es2' t' y' xs')
            assume b0: "\<Gamma> \<turnstile> (es1', s', x') -es-et'\<rightarrow> (es2', t', y')"
              and  b1: "(es1', s', x') # (es2', t', y') # xs' = drop i esl"
              and  b2: "getspc_es (esl ! i) = EvtSys es"
            then have b3: "es1' = EvtSys es" 
              by (metis Pair_inject a3 nth_Cons_0)
            from b0 b3 have "\<exists>e. es2' = EvtSeq e (EvtSys es)" using evtsys_evtent by simp
            then obtain e where "es2' = EvtSeq e (EvtSys es)" by auto
            with b1 have "\<exists>e. getspc_es (drop i esl ! 1) = EvtSeq e (EvtSys es)" 
              using getspc_es_def by (metis One_nat_def eq_fst_iff nth_Cons_0 nth_Cons_Suc)
            then show ?case by simp
          qed

        then have "getspc_es (esl!Suc i) = EvtSys es \<or> (\<exists>e. getspc_es (esl!Suc i) = EvtSeq e (EvtSys es))"
          using a0 by fastforce
      }
      then show ?thesis by auto
      qed
  qed

lemma evtsys_next_in_cpts_anony:
  "esl\<in>cpts_es \<Gamma> \<Longrightarrow> \<forall>i. Suc i < length esl \<and> getspc_es (esl!i) = EvtSys es 
                       \<longrightarrow> getspc_es (esl!Suc i) = EvtSys es 
                        \<or> (\<exists>e. getspc_es (esl!Suc i) = EvtSeq e (EvtSys es) \<and> is_anonyevt e)"
  proof -
    assume p0: "esl\<in>cpts_es \<Gamma>"
    then show ?thesis
      proof -
      {
        fix i
        assume a0: "Suc i < length esl"
          and  a1: "getspc_es (esl!i) = EvtSys es"
        let ?esl1 = "drop i esl"
        from p0 a0 have a2: "?esl1\<in>cpts_es \<Gamma>" by (metis (no_types, hide_lams) Suc_diff_1 Suc_lessD 
              cpts_es_dropi diff_diff_cancel drop_0 length_drop length_greater_0_conv 
              less_or_eq_imp_le list.size(3)) 
        from a0 a1 have "getspc_es (?esl1!0) = EvtSys es" by auto 
        then obtain s1 and x1 where a3: "?esl1!0 = (EvtSys es,s1,x1)" 
          using getspc_es_def by (metis fst_conv old.prod.exhaust)
        from a2 a1 have "getspc_es (?esl1!1) = EvtSys es 
          \<or> (\<exists>e. getspc_es (?esl1!1) = EvtSeq e (EvtSys es) \<and> is_anonyevt e)"
          proof(induct ?esl1)
            case (CptsEsOne es' s' x')
            then show ?case by (metis One_nat_def Suc_eq_plus1_left Suc_lessD a0 
                le_add_diff_inverse2 length_Cons length_drop less_imp_le 
                list.size(3) not_less_iff_gr_or_eq)  
          next
            case (CptsEsEnv es' t' x' xs' s' y')
            assume b0: "(es', s', y') # (es', t', x') # xs' = drop i esl"
              and  b1: "getspc_es (esl ! i) = EvtSys es"
            then have "es' = EvtSys es" using getspc_es_def by (metis a3 fst_conv nth_Cons_0)
            with b0 have "getspc_es (drop i esl ! 1) = EvtSys es" using getspc_es_def
              by (metis One_nat_def fst_conv nth_Cons_0 nth_Cons_Suc) 
            then show ?case by simp
          next
            case (CptsEsComp es1' s' x' et' es2' t' y' xs')
            assume b0: "\<Gamma> \<turnstile> (es1', s', x') -es-et'\<rightarrow> (es2', t', y')"
              and  b1: "(es1', s', x') # (es2', t', y') # xs' = drop i esl"
              and  b2: "getspc_es (esl ! i) = EvtSys es"
            then have b3: "es1' = EvtSys es" 
              by (metis Pair_inject a3 nth_Cons_0)
            from b0 b3 have "\<exists>e. es2' = EvtSeq e (EvtSys es)" using evtsys_evtent by simp
            then obtain e where "es2' = EvtSeq e (EvtSys es)" by auto
            with b0 b1 b3 have "\<exists>e. getspc_es (drop i esl ! 1) = EvtSeq e (EvtSys es) \<and> is_anonyevt e"
              using getspc_es_def  by (metis One_nat_def ent_spec2' evtsysent_evtent0 
                fst_conv is_anonyevt.simps(1) noevtent_notran nth_Cons_0 nth_Cons_Suc) 
              
            then show ?case by simp
          qed

        then have "getspc_es (esl!Suc i) = EvtSys es 
            \<or> (\<exists>e. getspc_es (esl!Suc i) = EvtSeq e (EvtSys es) \<and> is_anonyevt e)"
          using a0 by fastforce
      }
      then show ?thesis by auto
      qed
  qed

lemma evtsys_all_es_in_cpts:
  "\<lbrakk>esl\<in>cpts_es \<Gamma>; length esl > 0; getspc_es (esl!0) = EvtSys es \<rbrakk> \<Longrightarrow>
        \<forall>i. i < length esl \<longrightarrow> getspc_es (esl!i) = EvtSys es \<or> (\<exists>e. getspc_es (esl!i) = EvtSeq e (EvtSys es))"
  proof -
    assume p0: "esl\<in>cpts_es \<Gamma>"
      and  p1: "length esl > 0"
      and  p2: "getspc_es (esl!0) = EvtSys es"
    show ?thesis
      proof -
      {
        fix i
        assume a0: "i < length esl"
        then have "getspc_es (esl!i) = EvtSys es \<or> (\<exists>e. getspc_es (esl!i) = EvtSeq e (EvtSys es))"
          proof(induct i)
            case 0 from p2 show ?case by simp
          next
            case (Suc j)
            assume b0: "j < length esl \<Longrightarrow> 
                        getspc_es (esl ! j) = EvtSys es \<or> (\<exists>e. getspc_es (esl ! j) = EvtSeq e (EvtSys es))"
              and  b1: "Suc j < length esl"
            then have "getspc_es (esl ! j) = EvtSys es \<or> (\<exists>e. getspc_es (esl ! j) = EvtSeq e (EvtSys es))"
              by simp
            then show ?case
              proof 
                assume c0: "getspc_es (esl ! j) = EvtSys es"
                with p0 b1 show ?thesis using evtsys_next_in_cpts by auto
              next
                assume c0: "\<exists>e. getspc_es (esl ! j) = EvtSeq e (EvtSys es)"
                with p0 b1 show ?thesis using evtseq_next_in_cpts by blast
              qed
          qed
      }
      then show ?thesis by auto
      qed
  qed

lemma evtsys_all_es_in_cpts_anony:
  "\<lbrakk>esl\<in>cpts_es \<Gamma>; length esl > 0; getspc_es (esl!0) = EvtSys es \<rbrakk> \<Longrightarrow>
        \<forall>i. i < length esl \<longrightarrow> getspc_es (esl!i) = EvtSys es 
            \<or> (\<exists>e. getspc_es (esl!i) = EvtSeq e (EvtSys es) \<and> is_anonyevt e)"
  proof -
    assume p0: "esl\<in>cpts_es \<Gamma>"
      and  p1: "length esl > 0"
      and  p2: "getspc_es (esl!0) = EvtSys es"
    show ?thesis
      proof -
      {
        fix i
        assume a0: "i < length esl"
        then have "getspc_es (esl!i) = EvtSys es \<or> (\<exists>e. getspc_es (esl!i) = EvtSeq e (EvtSys es) \<and> is_anonyevt e)"
          proof(induct i)
            case 0 from p2 show ?case by simp
          next
            case (Suc j)
            assume b0: "j < length esl \<Longrightarrow> 
                        getspc_es (esl ! j) = EvtSys es 
                        \<or> (\<exists>e. getspc_es (esl ! j) = EvtSeq e (EvtSys es) \<and> is_anonyevt e)"
              and  b1: "Suc j < length esl"
            then have "getspc_es (esl ! j) = EvtSys es 
                    \<or> (\<exists>e. getspc_es (esl ! j) = EvtSeq e (EvtSys es) \<and> is_anonyevt e)"
              by simp
            then show ?case
              proof 
                assume c0: "getspc_es (esl ! j) = EvtSys es"
                with p0 b1 show ?thesis using evtsys_next_in_cpts_anony by auto
              next
                assume c0: "\<exists>e. getspc_es (esl ! j) = EvtSeq e (EvtSys es) \<and> is_anonyevt e"
                with p0 b1 show ?thesis using evtseq_next_in_cpts_anony by blast
              qed
          qed
      }
      then show ?thesis by auto
      qed
  qed

lemma not_anonyevt_none_in_evtseq:
    "\<lbrakk>esl\<in>cpts_es \<Gamma>; esl = (EvtSeq e es,s1,x1)#(es,s2,x2)#xs \<rbrakk> \<Longrightarrow> e \<noteq> AnonyEvent fin_com"
  apply(rule cpts_es.cases)
  apply(simp)+
  apply (metis Suc_eq_plus1 add.commute add.right_neutral esys.size(3) le_add1 lessI not_le) 
  apply(rule estran.cases)
  apply(simp)+
  apply (metis Suc_eq_plus1 add.commute add.right_neutral esys.size(3) le_add1 lessI not_le)
  apply(rule etran.cases)
  apply(simp)+
  prefer 2
  apply(simp) using ptran_not_none apply auto[1]
  done

lemma not_anonyevt_none_in_evtseq1:
    "\<lbrakk>esl\<in>cpts_es \<Gamma>; length esl > 1; getspc_es (esl!0) = EvtSeq e es;
      getspc_es (esl!1) = es \<rbrakk> \<Longrightarrow> e \<noteq> AnonyEvent fin_com"
  using getspc_es_def not_anonyevt_none_in_evtseq
    by (metis (no_types, hide_lams) Cons_nth_drop_Suc drop_0 eq_fst_iff less_Suc_eq less_Suc_eq_0_disj less_one)

lemma fst_esys_snd_eseq_exist_evtent:
    "\<lbrakk>esl\<in>cpts_es \<Gamma>; esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs\<rbrakk> \<Longrightarrow>
          \<exists>t. \<Gamma> \<turnstile> (EvtSys es, s, x) -es-t\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1)"
  apply(rule cpts_es.cases)
  apply(simp)+
  apply blast
  by blast

lemma fst_esys_snd_eseq_exist_evtent2:
    "\<lbrakk>esl\<in>cpts_es \<Gamma>; esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs\<rbrakk> \<Longrightarrow>
          \<exists>e k. \<Gamma> \<turnstile> (EvtSys es, s, x) -es-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1)"
  apply(rule cpts_es.cases)
  apply(simp)+
  apply blast
  by (metis (no_types, hide_lams) cmd_enable_impl_notesys2 estran_impl_evtentorcmd 
    evtent_is_basicevt fst_conv getspc_es_def nth_Cons_0 nth_Cons_Suc)

  
lemma fst_esys_snd_eseq_exist: 
  "\<lbrakk>esl\<in>cpts_es \<Gamma>; length esl \<ge> 2 \<and> getspc_es (esl!0) = EvtSys es \<and> getspc_es (esl!1) \<noteq> EvtSys es\<rbrakk>
    \<Longrightarrow> \<exists>s x ev s1 x1 xs. esl = (EvtSys es, s, x) # (EvtSeq ev (EvtSys es), s1,x1) # xs"
  proof -
    assume a0: "length esl \<ge> 2 \<and> getspc_es (esl!0) = EvtSys es \<and> getspc_es (esl!1) \<noteq> EvtSys es"
      and  c1: "esl\<in>cpts_es \<Gamma>"
    from a0 have b0: "getspc_es (esl!0) = EvtSys es \<and> getspc_es (esl!1) \<noteq> EvtSys es"
      by (metis (no_types, lifting))
    
    from a0 have b1: "2 \<le> length esl" by fastforce 
    moreover from b0 b1 have "\<exists>s x. esl!0 = (EvtSys es, s, x)" using getspc_es_def
      by (metis eq_fst_iff) 
    moreover have "\<exists>ev s1 x1. esl!1 = (EvtSeq ev (EvtSys es), s1,x1)" using getspc_es_def
      proof -
        from c1 a0 b0 have "\<exists>ev. getspc_es (esl!1) = EvtSeq ev (EvtSys es)" 
           by (metis One_nat_def Suc_1 Suc_le_lessD evtsys_next_in_cpts) 
        then show ?thesis using getspc_es_def by (metis fst_conv surj_pair) 
      qed
    ultimately show ?thesis by (metis (no_types, hide_lams) One_nat_def Suc_1 
      Suc_n_not_le_n diff_is_0_eq hd_Cons_tl hd_conv_nth length_tl 
      list.size(3) not_numeral_le_zero nth_Cons_Suc order_trans) 
  qed

  
lemma notevtent_cptses_isenvorcmd: 
  "\<lbrakk>esl\<in>cpts_es \<Gamma>; length esl \<ge> 2; \<not> (\<exists>e k. \<Gamma> \<turnstile> esl ! 0 -es-EvtEnt e\<sharp>k\<rightarrow> esl ! 1)\<rbrakk> 
    \<Longrightarrow> \<Gamma> \<turnstile> esl ! 0 -ese\<rightarrow> esl ! 1 \<or> (\<exists>c k. \<Gamma> \<turnstile> esl ! 0 -es-Cmd c\<sharp>k\<rightarrow> esl ! 1)"
  apply(rule cpts_es.cases)
  apply simp+
  apply (simp add: esetran.intros)
  using estran_impl_evtentorcmd2
  by (metis One_nat_def nth_Cons_0 nth_Cons_Suc) 
 
lemma only_envtran_to_basicevt:
  "esl\<in>cpts_es \<Gamma> \<Longrightarrow> \<forall>i. Suc i < length esl \<and> (\<exists>e. getspc_es (esl!i) = EvtSeq e esys) 
                      \<and> getspc_es (esl!Suc i) = EvtSeq (BasicEvent e) esys
                        \<longrightarrow> getspc_es (esl!i) = EvtSeq (BasicEvent e) esys"
  proof -
    assume p0: "esl\<in>cpts_es \<Gamma>"
    then show ?thesis
      proof -
      {
        fix i
        assume a0: "Suc i < length esl"
          and  a1: "getspc_es (esl!Suc i) = EvtSeq (BasicEvent e) esys"
          and  a00: "\<exists>e. getspc_es (esl!i) = EvtSeq e esys"
        let ?esl1 = "drop i esl"
        from p0 a0 have a2: "?esl1\<in>cpts_es \<Gamma>" by (metis (no_types, hide_lams) Suc_diff_1 Suc_lessD 
              cpts_es_dropi diff_diff_cancel drop_0 length_drop length_greater_0_conv 
              less_or_eq_imp_le list.size(3)) 
        from a0 a1 have "getspc_es (?esl1!1) = EvtSeq (BasicEvent e) esys" by auto 
        then obtain s1 and x1 where a3: "?esl1!1 = (EvtSeq (BasicEvent e) esys,s1,x1)" 
          using getspc_es_def by (metis fst_conv old.prod.exhaust)
        from a2 a1 have "getspc_es (?esl1!0) = EvtSeq (BasicEvent e) esys"
          proof(induct ?esl1)
            case (CptsEsOne es' s' x')
            then show ?case by (metis One_nat_def Suc_eq_plus1_left Suc_lessD a0 
                le_add_diff_inverse2 length_Cons length_drop less_imp_le 
                list.size(3) not_less_iff_gr_or_eq)  
          next
            case (CptsEsEnv es' t' x' xs' s' y')
            assume b0: "(es', s', y') # (es', t', x') # xs' = drop i esl"
              and  b1: "getspc_es (esl ! Suc i) = EvtSeq (BasicEvent e) esys"
            then have "es' = EvtSeq (BasicEvent e) esys" 
              by (metis One_nat_def a3 nth_Cons_0 nth_Cons_Suc prod.inject) 
            with b0 show ?case using getspc_es_def by (metis fst_conv nth_Cons_0) 
          next
            case (CptsEsComp es1' s' x' et' es2' t' y' xs')
            assume b0: "\<Gamma> \<turnstile> (es1', s', x') -es-et'\<rightarrow> (es2', t', y')"
              and  b1: "(es1', s', x') # (es2', t', y') # xs' = drop i esl"
              and  b2: "getspc_es (esl ! Suc i) = EvtSeq (BasicEvent e) esys"
            then have b3: "es2' = EvtSeq (BasicEvent e) esys"
              by (metis One_nat_def Pair_inject a3 nth_Cons_0 nth_Cons_Suc) 
            from a00 obtain e' where b4: "getspc_es (esl ! i) = EvtSeq e' esys" by auto
            then have "es1' = EvtSeq e' esys"
              by (metis (no_types, lifting) CptsEsComp.hyps(4) fst_conv getspc_es_def nth_via_drop) 
            with b0 b3 have "\<not> (\<exists>e. es2' = EvtSeq (BasicEvent e) esys)" 
              using notrans_to_basicevt_insameesys[of \<Gamma> es1' s' x' et' es2' t' y' esys] by auto
            with b3 show ?case by blast
          qed
      }
      then show ?thesis by auto
      qed
  qed

lemma incpts_es_impl_evnorcomptran:
  "esl\<in>cpts_es \<Gamma> \<Longrightarrow> \<forall>i. Suc i < length esl \<longrightarrow> \<Gamma> \<turnstile> esl ! i -ese\<rightarrow> esl ! Suc i \<or> (\<exists>et. \<Gamma> \<turnstile> esl ! i -es-et\<rightarrow> esl ! Suc i)" 
  proof -
    assume p0: "esl\<in>cpts_es \<Gamma>"
    {
      fix i
      assume a0: "Suc i < length esl"
      let ?esl1 = "take 2 (drop i esl)"
      from a0 p0 have "take (Suc (Suc i) - i) (drop i esl) \<in> cpts_es \<Gamma>" 
        using cpts_es_seg[of esl \<Gamma> i "Suc (Suc i)"] by simp
      then have "?esl1 \<in> cpts_es \<Gamma>" by auto
      moreover
      from a0 obtain esc1 and s1 and x1 where a1: "esl ! i = (esc1,s1,x1)"
        using prod_cases3 by blast  
      moreover
      from a0 obtain esc2 and s2 and x2 where a2: "esl ! Suc i = (esc2,s2,x2)"
        using prod_cases3 by blast  
      moreover
      from a0 have "esl ! i = ?esl1 ! 0" by (simp add: Cons_nth_drop_Suc Suc_lessD) 
      moreover
      from a0 have "esl ! Suc i = ?esl1 ! 1" by (simp add: Cons_nth_drop_Suc Suc_lessD) 
      ultimately have "(esc1, s1, x1)#[(esc2, s2, x2)] \<in> cpts_es \<Gamma>" 
        by (metis Cons_nth_drop_Suc Suc_lessD a0 numeral_2_eq_2 take_0 take_Suc_Cons)
      then have "\<Gamma> \<turnstile> (esc1, s1, x1) -ese\<rightarrow> (esc2, s2, x2) \<or> (\<exists>et. \<Gamma> \<turnstile> (esc1, s1, x1) -es-et\<rightarrow> (esc2, s2, x2))"
        apply(rule cpts_es.cases)
        apply simp+
        apply (simp add: esetran.intros)
        by auto
      with a1 a2 have "\<Gamma> \<turnstile> esl ! i -ese\<rightarrow> esl ! Suc i \<or> (\<exists>et. \<Gamma> \<turnstile> esl ! i -es-et\<rightarrow> esl ! Suc i)" by simp
    }
    then show ?thesis by auto
  qed

lemma incpts_es_eseq_not_evtent:
  "\<lbrakk>esl\<in>cpts_es \<Gamma>; Suc i < length esl; \<exists>e esys. getspc_es (esl!i) = EvtSeq e esys \<and> is_anonyevt e\<rbrakk> 
    \<Longrightarrow> \<not>(\<exists>e k. t = EvtEnt e \<and> \<Gamma> \<turnstile> esl!i -es-t\<sharp>k\<rightarrow> esl!Suc i)"
  proof -
    assume p0: "esl\<in>cpts_es \<Gamma>"
      and  a0: "Suc i < length esl"
      and  a1: "\<exists>e esys. getspc_es (esl!i) = EvtSeq e esys \<and> is_anonyevt e"
    let ?esl1 = "drop i esl"
    from p0 a0 have a2: "?esl1\<in>cpts_es \<Gamma>" by (metis (no_types, hide_lams) Suc_diff_1 Suc_lessD 
          cpts_es_dropi diff_diff_cancel drop_0 length_drop length_greater_0_conv 
          less_or_eq_imp_le list.size(3)) 
    from a0 a1 obtain e and esys where a3: "getspc_es (?esl1!0) = EvtSeq e esys" by auto 
    then obtain s1 and x1 where a4: "?esl1!0 = (EvtSeq e esys,s1,x1)" 
      using getspc_es_def by (metis fst_conv old.prod.exhaust)
    from a2 a3 have "\<not>(\<exists>e k. t = EvtEnt e \<and> \<Gamma> \<turnstile> ?esl1!0 -es-t\<sharp>k\<rightarrow> ?esl1!1)"
      proof(induct ?esl1)
          case (CptsEsOne es' s' x')
          then show ?case by (metis One_nat_def Suc_eq_plus1_left Suc_lessD a0 
              le_add_diff_inverse2 length_Cons length_drop less_imp_le 
              list.size(3) not_less_iff_gr_or_eq)  
        next
          case (CptsEsEnv es' t' x' xs' s' y')
          assume b0: "(es', s', y') # (es', t', x') # xs' = ?esl1"
            and  b1: "getspc_es (?esl1 ! 0) = EvtSeq e esys"
          then have "es' = EvtSeq e esys"
            by (metis Pair_inject a4 nth_Cons_0)  
          with b0 show ?case using getspc_es_def
            by (metis (mono_tags, lifting) a1 evtseq_no_evtent2 nth_Cons_0 nth_via_drop) 
        next
          case (CptsEsComp es1' s' x' et' es2' t' y' xs')
          assume b0: "\<Gamma> \<turnstile> (es1', s', x') -es-et'\<rightarrow> (es2', t', y')"
            and  b1: "(es1', s', x') # (es2', t', y') # xs' = drop i esl"
            and  b2: "getspc_es (?esl1 ! 0) = EvtSeq e esys"
          then have b3: "es1' = EvtSeq e esys"
             by (metis Pair_inject a4 nth_Cons_0)
          with b0 b1 show ?case using getspc_es_def
            by (metis (no_types, lifting) a1 evtseq_no_evtent2 nth_Cons_0 nth_via_drop) 
        qed
        
    with a0 show ?thesis by (simp add: Cons_nth_drop_Suc Suc_lessD) 
  qed

lemma evtsys_not_eq_in_tran_aux:"\<Gamma> \<turnstile> (P,s,x) -es-est\<rightarrow> (Q,t,y) \<Longrightarrow> P \<noteq> Q"
  apply(erule estran.cases)
  apply (simp add: evt_not_eq_in_tran_aux)
  apply (simp add: evt_not_eq_in_tran_aux)
  by (simp add: evtseq_ne_es)

lemma evtsys_not_eq_in_tran_aux1:"\<Gamma> \<turnstile> esc1 -es-est\<rightarrow> esc2 \<Longrightarrow> getspc_es esc1 \<noteq> getspc_es esc2"
  proof -
    assume p0: "\<Gamma> \<turnstile> esc1 -es-est\<rightarrow> esc2"
    obtain es1 and s1 and x1 and es2 and s2 and x2 where a0: "esc1 = (es1,s1,x1) \<and> esc2 = (es2,s2,x2)"
      by (metis prod.collapse)
    with p0 have "es1 \<noteq> es2" using evtsys_not_eq_in_tran_aux by simp
    with a0 show ?thesis by (simp add:getspc_es_def)
  qed

lemma evtsys_not_eq_in_tran [simp]: "\<not> \<Gamma> \<turnstile> (P,s,x) -es-est\<rightarrow> (P,t,y)"
  apply clarify
  apply(drule evtsys_not_eq_in_tran_aux)
  apply simp
  done

lemma evtsys_not_eq_in_tran2 [simp]: "\<not>(\<exists>est. \<Gamma> \<turnstile> (P,s,x) -es-est\<rightarrow> (P,t,y))" by simp

lemma es_tran_not_etran2: "\<Gamma> \<turnstile> (P,s,x) -es-pt\<rightarrow> (Q,t,y) \<Longrightarrow> \<not>(\<Gamma> \<turnstile> (P,s,x) -ese\<rightarrow>(Q,t,y))"
  by (metis esetran.cases evtsys_not_eq_in_tran_aux)

lemma es_tran_not_etran1: "\<Gamma> \<turnstile> esc1 -es-pt\<rightarrow> esc2 \<Longrightarrow> \<not>(\<Gamma> \<turnstile> esc1 -ese\<rightarrow>esc2)"
  using esetran_eqconf1 evtsys_not_eq_in_tran_aux1 by blast

subsubsection \<open>Parallel event systems\<close>

lemma cpts_pes_not_empty [simp]:"[] \<notin> cpts_pes \<Gamma>"
apply(force elim:cpts_pes.cases)
done

lemma pesetran_eqconf: "\<Gamma> \<turnstile> (es1, s1, x1) -pese\<rightarrow> (es2, s2, x2) \<Longrightarrow> es1 = es2"
  apply(rule pesetran.cases)
  apply(simp)+
  done

lemma pesetran_eqconf1: "\<Gamma> \<turnstile> esc1 -pese\<rightarrow> esc2 \<Longrightarrow> getspc esc1 = getspc esc2"
  proof -
    assume a0: "\<Gamma> \<turnstile> esc1 -pese\<rightarrow> esc2"
    then obtain es1 and s1 and x1 and es2 and s2 and x2 where a1: "esc1 = (es1, s1, x1)" and a2: "esc2 = (es2, s2, x2)"
      by (meson prod_cases3) 
    then have "es1 = es2" using a0 pesetran_eqconf by fastforce 
    with a1 show ?thesis by (simp add: a2 getspc_def) 
  qed

lemma eqconf_pesetran1: "es1 = es2 \<Longrightarrow> \<Gamma> \<turnstile> (es1, s1, x1) -pese\<rightarrow> (es2, s2, x2)"
  by (simp add: pesetran.intros) 


lemma eqconf_pesetran: "getspc esc1 = getspc esc2 \<Longrightarrow> \<Gamma> \<turnstile> esc1 -pese\<rightarrow> esc2" 
  proof -
    assume a0: "getspc esc1 = getspc esc2"
    obtain es1 and s1 and x1 where a1: "esc1 = (es1, s1, x1)" using prod_cases3 by blast 
    obtain es2 and s2 and x2 where a2: "esc2 = (es2, s2, x2)" using prod_cases3 by blast 
    with a0 a1 have "es1 = es2" by (simp add:getspc_def)
    with a1 a2 have a3: "\<Gamma> \<turnstile> (es1, s1, x1) -pese\<rightarrow> (es2, s2, x2)" by (simp add:eqconf_pesetran1)
    from a3 a1 a2 show ?thesis by simp
  qed

lemma pestran_cpts_pes: "\<lbrakk>\<Gamma> \<turnstile> C1 -pes-ct\<rightarrow> C2; C2#xs \<in> cpts_pes \<Gamma>\<rbrakk> \<Longrightarrow> C1#C2#xs \<in> cpts_pes \<Gamma>"
  proof -
    assume p0: "\<Gamma> \<turnstile> C1 -pes-ct\<rightarrow> C2"
      and  p1: "C2#xs \<in> cpts_pes \<Gamma>"
    moreover
    obtain pes1 and s1 and x1 where "C1 = (pes1,s1,x1)"
      using prod_cases3 by blast 
    moreover
    obtain pes2 and s2 and x2 where "C2 = (pes2,s2,x2)" 
      using prod_cases3 by blast 
    ultimately show ?thesis by (simp add: cpts_pes.CptsPesComp) 
  qed

lemma cpts_pes_onemore: "\<lbrakk>el \<in> cpts_pes \<Gamma>; (\<Gamma> \<turnstile> el ! (length el - 1) -pes-t\<rightarrow> ec) \<or> (\<Gamma> \<turnstile> el ! (length el - 1) -pese\<rightarrow> ec)\<rbrakk> \<Longrightarrow>
                          el @ [ec] \<in> cpts_pes \<Gamma>"
  proof -
    assume p0: "el \<in> cpts_pes \<Gamma>"
      and  p2: "(\<Gamma> \<turnstile> el ! (length el - 1) -pes-t\<rightarrow> ec) \<or> (\<Gamma> \<turnstile> el ! (length el - 1) -pese\<rightarrow> ec)"
    from p0 have p1: "el \<noteq> []"
      using cpts_pes.simps by blast
    have "\<forall>el ec t. el \<in> cpts_pes \<Gamma> \<and> ((\<Gamma> \<turnstile> el ! (length el - 1) -pes-t\<rightarrow> ec) \<or> (\<Gamma> \<turnstile> el ! (length el - 1) -pese\<rightarrow> ec)) 
      \<longrightarrow> el @ [ec] \<in> cpts_pes \<Gamma>"
      proof -
      {
        fix el ec t
        assume a0: "el \<in> cpts_pes \<Gamma>"
          and  a2: "(\<Gamma> \<turnstile> el ! (length el - 1) -pes-t\<rightarrow> ec) \<or> (\<Gamma> \<turnstile> el ! (length el - 1) -pese\<rightarrow> ec)"
        then have a1: "length el > 0"
          using cpts_pes.simps by blast
        from a0 a1 a2 have "el @ [ec] \<in> cpts_pes \<Gamma>"
          proof(induct el)
            case (CptsPesOne e s x) 
            assume b0: "(\<Gamma> \<turnstile> [(e, s, x)] ! (length [(e, s, x)] - 1) -pes-t\<rightarrow> ec) 
                          \<or> \<Gamma> \<turnstile> [(e, s, x)] ! (length [(e, s, x)] - 1) -pese\<rightarrow> ec"
            then have "(\<Gamma> \<turnstile> (e, s, x) -pes-t\<rightarrow> ec) \<or> (\<Gamma> \<turnstile> (e, s, x) -pese\<rightarrow> ec)" by simp
            then show ?case  
              proof
                assume "\<Gamma> \<turnstile> (e, s, x) -pes-t\<rightarrow> ec"
                then show ?thesis by (metis append_Cons append_Nil 
                    cpts_pes.CptsPesComp cpts_pes.CptsPesOne surj_pair)
              next
                assume "\<Gamma> \<turnstile> (e, s, x) -pese\<rightarrow> ec"
                then show ?thesis
                  by (metis append_Cons append_Nil cpts_pes.CptsPesEnv 
                      cpts_pes.CptsPesOne pesetranE surj_pair) 
              qed
          next
            case (CptsPesEnv e s1 x xs s2 y)
            assume b0: "(e, s1, x) # xs \<in> cpts_pes \<Gamma>"
              and  b1: "0 < length ((e, s1, x) # xs) \<Longrightarrow>
                          (\<Gamma> \<turnstile> ((e, s1, x) # xs) ! (length ((e, s1, x) # xs) - 1) -pes-t\<rightarrow> ec) \<or>
                          (\<Gamma> \<turnstile> ((e, s1, x) # xs) ! (length ((e, s1, x) # xs) - 1) -pese\<rightarrow> ec) \<Longrightarrow>
                          ((e, s1, x) # xs) @ [ec] \<in> cpts_pes \<Gamma>"
              and  b2: "0 < length ((e, s2, y) # (e, s1, x) # xs)"
              and  b3: "(\<Gamma> \<turnstile> ((e, s2, y) # (e, s1, x) # xs) ! (length ((e, s2, y) # (e, s1, x) # xs) - 1) -pes-t\<rightarrow> ec) \<or>
                        (\<Gamma> \<turnstile> ((e, s2, y) # (e, s1, x) # xs) ! (length ((e, s2, y) # (e, s1, x) # xs) - 1) -pese\<rightarrow> ec)"
            then show ?case 
              proof(cases "xs = []")
                assume c0: "xs = []"
                with b3 have "(\<Gamma> \<turnstile> (e, s1, x) -pes-t\<rightarrow> ec) \<or> (\<Gamma> \<turnstile> (e, s1, x) -pese\<rightarrow> ec)" by simp
                with b1 c0 have "((e, s1, x) # xs) @ [ec] \<in> cpts_pes \<Gamma>" by simp
                then show ?thesis by (simp add: cpts_pes.CptsPesEnv) 
              next
                assume c0: "xs \<noteq> []"
                with b3 have "(\<Gamma> \<turnstile> last xs -pes-t\<rightarrow> ec) \<or> (\<Gamma> \<turnstile> last xs -pese\<rightarrow> ec)" by (simp add: last_conv_nth) 
                with b1 c0 have "((e, s1, x) # xs) @ [ec] \<in> cpts_pes \<Gamma>" using b3 by auto
                then show ?thesis by (simp add: cpts_pes.CptsPesEnv) 
              qed
          next
            case (CptsPesComp e1 s1 x1 et e2 t1 y1 xs1)
            assume b0: "\<Gamma> \<turnstile> (e1, s1, x1) -pes-et\<rightarrow> (e2, t1, y1)"
              and  b1: "(e2, t1, y1) # xs1 \<in> cpts_pes \<Gamma>"
              and  b2: "0 < length ((e2, t1, y1) # xs1) \<Longrightarrow>
                        (\<Gamma> \<turnstile> ((e2, t1, y1) # xs1) ! (length ((e2, t1, y1) # xs1) - 1) -pes-t\<rightarrow> ec) \<or>
                        (\<Gamma> \<turnstile> ((e2, t1, y1) # xs1) ! (length ((e2, t1, y1) # xs1) - 1) -pese\<rightarrow> ec) \<Longrightarrow>
                        ((e2, t1, y1) # xs1) @ [ec] \<in> cpts_pes \<Gamma>"
              and  b3: "0 < length ((e1, s1, x1) # (e2, t1, y1) # xs1)"
              and  b4: "(\<Gamma> \<turnstile> ((e1, s1, x1) # (e2, t1, y1) # xs1) ! (length ((e1, s1, x1) # (e2, t1, y1) # xs1) - 1) -pes-t\<rightarrow> ec) \<or>
                        \<Gamma> \<turnstile> ((e1, s1, x1) # (e2, t1, y1) # xs1) ! (length ((e1, s1, x1) # (e2, t1, y1) # xs1) - 1) -pese\<rightarrow> ec"
            then show ?case 
              proof(cases "xs1 = []")
                assume c0: "xs1 = []"
                with b4 have "(\<Gamma> \<turnstile> (e2, t1, y1) -pes-t\<rightarrow> ec) \<or> (\<Gamma> \<turnstile> (e2, t1, y1) -pese\<rightarrow> ec)" by simp
                with b2 c0 have "((e2, t1, y1) # xs1) @ [ec] \<in> cpts_pes \<Gamma>" by simp
                with b0 show ?thesis using cpts_pes.CptsPesComp by fastforce 
              next
                assume c0: "xs1 \<noteq> []"
                with b4 have "(\<Gamma> \<turnstile> last xs1 -pes-t\<rightarrow> ec) \<or> (\<Gamma> \<turnstile> last xs1 -pese\<rightarrow> ec)" by (simp add: last_conv_nth)
                with b2 c0 have "((e2, t1, y1) # xs1) @ [ec] \<in> cpts_pes \<Gamma>" using b4 by auto 
                then show ?thesis using b0 cpts_pes.CptsPesComp by fastforce 
              qed
          qed
      }
      then show ?thesis by blast
      qed

    then show "el @ [ec] \<in> cpts_pes \<Gamma>" using p0 p1 p2 by blast 
  qed

lemma pes_not_eq_in_tran_aux:"\<Gamma> \<turnstile> (P,s,x) -pes-est\<rightarrow> (Q,t,y) \<Longrightarrow> P \<noteq> Q"
  apply(erule pestran.cases)
  by (metis Pair_inject evtsys_not_eq_in_tran fun_upd_same)
  
lemma pes_not_eq_in_tran [simp]: "\<not> \<Gamma> \<turnstile> (P,s,x) -pes-est\<rightarrow> (P,t,y)"
  apply clarify
  apply(drule pes_not_eq_in_tran_aux)
  apply simp
  done

lemma pes_tran_not_etran1: "\<Gamma> \<turnstile> pes1 -pes-t\<rightarrow> pes2 \<Longrightarrow> \<not>(\<Gamma> \<turnstile> pes1 -pese\<rightarrow>pes2)"
  by (metis pes_not_eq_in_tran pesetranE surj_pair)

lemma pes_tran_not_etran2: "\<Gamma> \<turnstile> (P,s,x) -pes-pt\<rightarrow> (Q,t,y) \<Longrightarrow> \<not>(\<Gamma> \<turnstile> (P,s,x) -pese\<rightarrow>(Q,t,y))"
  by (simp add: pes_tran_not_etran1)
  
lemma incpts_pes_impl_evnorcomptran:
  "esl\<in>cpts_pes \<Gamma> \<Longrightarrow> \<forall>i. Suc i < length esl \<longrightarrow> \<Gamma> \<turnstile> esl ! i -pese\<rightarrow> esl ! Suc i \<or> (\<exists>et. \<Gamma> \<turnstile> esl ! i -pes-et\<rightarrow> esl ! Suc i)" 
  proof -
    assume p0: "esl\<in>cpts_pes \<Gamma>"
    then show ?thesis
      proof(induct esl)
        case (CptsPesOne) show ?case by simp
      next
        case (CptsPesEnv pes t x xs s y)
        assume a0: "(pes, t, x) # xs \<in> cpts_pes \<Gamma>"
          and  a1: "\<forall>i. Suc i < length ((pes, t, x) # xs) \<longrightarrow>
                      \<Gamma> \<turnstile> ((pes, t, x) # xs) ! i -pese\<rightarrow> ((pes, t, x) # xs) ! Suc i \<or>
                      (\<exists>et. \<Gamma> \<turnstile> ((pes, t, x) # xs) ! i -pes-et\<rightarrow> ((pes, t, x) # xs) ! Suc i)"
        then show ?case 
          proof -
          {
            fix i
            assume b0: "Suc i < length ((pes, s, y) # (pes, t, x) # xs)"
            have "\<Gamma> \<turnstile> ((pes, s, y) # (pes, t, x) # xs) ! i -pese\<rightarrow> ((pes, s, y) # (pes, t, x) # xs) ! Suc i \<or>
                  (\<exists>et. \<Gamma> \<turnstile> ((pes, s, y) # (pes, t, x) # xs) ! i -pes-et\<rightarrow> ((pes, s, y) # (pes, t, x) # xs) ! Suc i)"
              proof(cases "i = 0")
                assume c0: "i = 0"
                then show ?thesis by (simp add: eqconf_pesetran1 nth_Cons') 
              next
                assume c0: "i \<noteq> 0"
                then have "i > 0" by auto
                with a1 b0 show ?thesis by (simp add: length_Cons) 
              qed
          }
          then show ?thesis by auto
          qed
      next
        case (CptsPesComp pes1 s x ct pes2 t y xs)
        assume a0: "\<Gamma> \<turnstile> (pes1, s, x) -pes-ct\<rightarrow> (pes2, t, y)"
          and  a1: "(pes2, t, y) # xs \<in> cpts_pes \<Gamma>"
          and  a2: "\<forall>i. Suc i < length ((pes2, t, y) # xs) \<longrightarrow>
                      \<Gamma> \<turnstile> ((pes2, t, y) # xs) ! i -pese\<rightarrow> ((pes2, t, y) # xs) ! Suc i \<or>
                      (\<exists>et. \<Gamma> \<turnstile> ((pes2, t, y) # xs) ! i -pes-et\<rightarrow> ((pes2, t, y) # xs) ! Suc i)"
        then show ?case 
          proof -
          {
            fix i
            assume b0: "Suc i < length ((pes1, s, x) # (pes2, t, y) # xs)"
            have "\<Gamma> \<turnstile> ((pes1, s, x) # (pes2, t, y) # xs) ! i -pese\<rightarrow> ((pes1, s, x) # (pes2, t, y) # xs) ! Suc i \<or>
                  (\<exists>et. \<Gamma> \<turnstile> ((pes1, s, x) # (pes2, t, y) # xs) ! i -pes-et\<rightarrow> ((pes1, s, x) # (pes2, t, y) # xs) ! Suc i)"
              proof(cases "i = 0")
                assume c0: "i = 0"
                with a0 show ?thesis using nth_Cons_0 nth_Cons_Suc by auto 
              next
                assume c0: "i \<noteq> 0"
                then have "i > 0" by auto
                with a2 b0 show ?thesis using Suc_inject Suc_less_eq2 Suc_pred 
                  length_Cons nth_Cons_Suc by auto 
              qed
          }
          then show ?thesis by auto
          qed
      qed
  qed

lemma cpts_pes_drop0: "\<lbrakk>el \<in> cpts_pes \<Gamma>; Suc 0 < length el\<rbrakk> \<Longrightarrow> drop (Suc 0) el \<in> cpts_pes \<Gamma>"
  apply(rule cpts_pes.cases)
  apply(simp)+
  done  

lemma cpts_pes_dropi: "\<lbrakk>el \<in> cpts_pes \<Gamma>; Suc i < length el\<rbrakk> \<Longrightarrow> drop (Suc i) el \<in> cpts_pes \<Gamma>"
  proof -
    assume p0:"el \<in> cpts_pes \<Gamma>" and p1:"Suc i < length el"
    have "\<forall>el i. el \<in> cpts_pes \<Gamma> \<and> Suc i < length el \<longrightarrow> drop (Suc i) el \<in> cpts_pes \<Gamma>"
      proof -
      {
        fix el i
        have "el \<in> cpts_pes \<Gamma> \<and> Suc i < length el \<longrightarrow> drop (Suc i) el \<in> cpts_pes \<Gamma>"
          proof(induct i)
            case 0 show ?case by (simp add: cpts_pes_drop0) 
          next
            case (Suc j)
            assume b0: "el \<in> cpts_pes \<Gamma> \<and> Suc j < length el \<longrightarrow> drop (Suc j) el \<in> cpts_pes \<Gamma>"
            show ?case
              proof
                assume c0: "el \<in> cpts_pes \<Gamma> \<and> Suc (Suc j) < length el"
                with b0 have c1: "drop (Suc j) el \<in> cpts_pes \<Gamma>"
                  by (simp add: c0 Suc_lessD)                 
                then show "drop (Suc (Suc j)) el \<in> cpts_pes \<Gamma>"
                  using c0 cpts_pes_drop0 by fastforce 
              qed
          qed
      }
      then show ?thesis by auto
      qed
    with p0 p1 show ?thesis by auto
  qed

lemma cpts_pes_take0: "\<lbrakk>el \<in> cpts_pes \<Gamma>; i < length el; el1 = take (Suc i) el; j < length el1\<rbrakk> 
                        \<Longrightarrow> drop (length el1 - Suc j) el1 \<in> cpts_pes \<Gamma>"
  proof -
    assume p0: "el \<in> cpts_pes \<Gamma>"
      and  p1: "i < length el"
      and  p2: "el1 = take (Suc i) el"
      and  p3: "j < length el1"
    have "\<forall>i j. el \<in> cpts_pes \<Gamma> \<and> i < length el \<and> el1 = take (Suc i) el \<and> j < length el1 
          \<longrightarrow> drop (length el1 - Suc j) el1 \<in> cpts_pes \<Gamma>"
      proof -
      {
        fix i j
        assume a0: "el \<in> cpts_pes \<Gamma>"
          and  a1: "i < length el"
          and  a2: "el1 = take (Suc i) el"
          and  a3: "j < length el1"
        then have "drop (length el1 - Suc j) el1 \<in> cpts_pes \<Gamma>"
          proof(induct j)
            case 0 
            have "drop (length el1 - Suc 0) el1 = [el ! i]"
              by (simp add: a1 a2 take_Suc_conv_app_nth) 
            then show ?case by (metis cpts_pes.CptsPesOne old.prod.exhaust) 
          next
            case (Suc jj)
            assume b0: "el \<in> cpts_pes \<Gamma> \<Longrightarrow> i < length el \<Longrightarrow> el1 = take (Suc i) el 
                        \<Longrightarrow> jj < length el1 \<Longrightarrow> drop (length el1 - Suc jj) el1 \<in> cpts_pes \<Gamma>"
              and  b1: "el \<in> cpts_pes \<Gamma>"
              and  b2: "i < length el"
              and  b3: "el1 = take (Suc i) el"
              and  b4: "Suc jj < length el1"
            then have b5: "drop (length el1 - Suc jj) el1 \<in> cpts_pes \<Gamma>"
              using Suc_lessD by blast 
            let ?el2 = "drop (Suc i) el"
            from a2 have b6: "el1 @ ?el2 = el" by simp
            let ?el1sht = "drop (length el1 - Suc jj) el1"
            let ?el1lng = "drop (length el1 - Suc (Suc jj)) el1"
            let ?elsht = "drop (length el1 - Suc jj) el"
            let ?ellng = "drop (length el1 - Suc (Suc jj)) el"
            from b6 have a7: "?el1sht @ ?el2 = ?elsht"
              by (metis diff_is_0_eq diff_le_self drop_0 drop_append) 
            from b6 have a8: "?el1lng @ ?el2 = ?ellng"
              by (metis (no_types, lifting) a7 append_eq_append_conv diff_is_0_eq' diff_le_self drop_append) 
            have a9: "?ellng = (el ! (length el1 - Suc (Suc jj))) # ?elsht"
              by (metis (no_types, lifting) Cons_nth_drop_Suc Suc_diff_Suc Suc_leI a8 
                  append_is_Nil_conv b4 diff_diff_cancel drop_all length_drop 
                  list.size(3) not_less old.nat.distinct(2)) 
            from b1 b4 have a10: "?elsht \<in> cpts_pes \<Gamma>"
              by (metis Suc_diff_Suc a7 append_is_Nil_conv b5 cpts_pes_dropi drop_all not_less)
            from b1 b4 have a11: "?ellng \<in> cpts_pes \<Gamma>"
              by (metis (no_types, lifting) Suc_diff_Suc a9 cpts_pes_dropi diff_is_0_eq 
                  drop_0 drop_all leI list.simps(3))
            have a12: "?el1lng = (el ! (length el1 - Suc (Suc jj))) # ?el1sht"
              by (metis (no_types, lifting) Cons_nth_drop_Suc Suc_diff_Suc b4 b6 diff_less 
                  gr_implies_not0 length_0_conv length_greater_0_conv nth_append zero_less_Suc)
            from a11 have "?el1lng \<in> cpts_pes \<Gamma>"
              proof(induct ?ellng)
                case CptsPesOne show ?case
                  using CptsPesOne.hyps a7 a9 by auto 
              next
                case (CptsPesEnv es1 t1 x1 xs1 s1 y1)
                assume c0: "(es1, t1, x1) # xs1 \<in> cpts_pes \<Gamma>"
                  and  c1: "(es1, t1, x1) # xs1 = drop (length el1 - Suc (Suc jj)) el \<Longrightarrow>
                            drop (length el1 - Suc (Suc jj)) el1 \<in> cpts_pes \<Gamma>"
                  and  c2: "(es1, s1, y1) # (es1, t1, x1) # xs1 = drop (length el1 - Suc (Suc jj)) el"
                from c0 have "(es1, s1, y1) # (es1, t1, x1) # xs1 \<in> cpts_pes \<Gamma>"
                  by (simp add: a11 c2) 
                have c3: "?el1sht ! 0 = (es1, t1, x1)" by (metis (no_types, lifting) Suc_leI Suc_lessD a7 
                        a9 append_eq_Cons_conv b4 c2 diff_diff_cancel length_drop list.inject 
                        list.size(3) nth_Cons_0 old.nat.distinct(2)) 
                then have c4: "\<exists>el1sht'. ?el1sht = (es1, t1, x1) # el1sht'" by (metis Cons_nth_drop_Suc b4 
                    diff_diff_cancel drop_0 length_drop less_or_eq_imp_le zero_less_Suc) 
                have c5: "?el1lng = (es1, s1, y1) # ?el1sht" using a12 a9 c2 by auto 
                
                with b5 c4 show ?case using cpts_pes.CptsPesEnv by fastforce 
              next
                case (CptsPesComp es1 s1 x1 et es2 t1 y1 xs1)
                assume c0: "\<Gamma> \<turnstile> (es1, s1, x1) -pes-et\<rightarrow> (es2, t1, y1)"
                  and  c1: "(es2, t1, y1) # xs1 \<in> cpts_pes \<Gamma>"
                  and  c2: "(es2, t1, y1) # xs1 = drop (length el1 - Suc (Suc jj)) el 
                            \<Longrightarrow> drop (length el1 - Suc (Suc jj)) el1 \<in> cpts_pes \<Gamma>"
                  and  c3: "(es1, s1, x1) # (es2, t1, y1) # xs1 = drop (length el1 - Suc (Suc jj)) el"
                have c4: "?el1sht ! 0 = (es2, t1, y1)" by (metis (no_types, lifting) Suc_leI Suc_lessD a7 
                        a9 append_eq_Cons_conv b4 c3 diff_diff_cancel length_drop list.inject 
                        list.size(3) nth_Cons_0 old.nat.distinct(2)) 
                then have c5: "\<exists>el1sht'. ?el1sht = (es2, t1, y1) # el1sht'" by (metis Cons_nth_drop_Suc b4 
                    diff_diff_cancel drop_0 length_drop less_or_eq_imp_le zero_less_Suc) 
                have c6: "?el1lng = (es1, s1, x1) # ?el1sht" using a12 a9 c3 by auto
                with b5 c5  show ?case using c0 cpts_pes.CptsPesComp by fastforce 
              qed

            then show ?case by simp
          qed
      }
      then show ?thesis by auto
      qed
    then show "drop (length el1 - Suc j) el1 \<in> cpts_pes \<Gamma>"
      using p0 p1 p2 p3 by blast 
  qed

lemma cpts_pes_take: "\<lbrakk>el \<in> cpts_pes \<Gamma>; i < length el\<rbrakk> \<Longrightarrow> take (Suc i) el \<in> cpts_pes \<Gamma>"
  using cpts_pes_take0 gr_implies_not0 by fastforce

lemma cpts_pes_seg: "\<lbrakk>el \<in> cpts_pes \<Gamma>; m \<le> length el; n \<le> length el; m < n\<rbrakk> 
                    \<Longrightarrow> take (n - m) (drop m el) \<in> cpts_pes \<Gamma>"
  proof -
    assume p0: "el \<in> cpts_pes \<Gamma>"
      and  p1: "m \<le> length el"
      and  p2: "n \<le> length el"
      and  p3: "m < n"
    then have "drop m el \<in> cpts_pes \<Gamma>" 
      using cpts_pes_dropi by (metis (no_types, lifting) drop_0 le_0_eq le_SucE less_le_trans zero_induct) 
    then show ?thesis using cpts_pes_take
      by (smt Suc_diff_Suc diff_diff_cancel diff_less_Suc diff_right_commute length_drop less_le_trans p2 p3)
  qed

lemma cpts_pes_seg2: "\<lbrakk>el \<in> cpts_pes \<Gamma>; m \<le> length el; n \<le> length el; take (n - m) (drop m el) \<noteq> []\<rbrakk> 
                    \<Longrightarrow> take (n - m) (drop m el) \<in> cpts_pes \<Gamma>"
  proof -
    assume p0: "el \<in> cpts_pes \<Gamma>"
      and  p1: "m \<le> length el"
      and  p2: "n \<le> length el"
      and  p3: "take (n - m) (drop m el) \<noteq> []"
    from p3 have "m < n" by simp
    then show ?thesis using cpts_pes_seg using p0 p1 p2 by blast
  qed

subsection \<open>Compositionality of the Semantics\<close>

subsubsection \<open>Definition of the conjoin operator\<close>

definition same_length :: "('l,'k,'s,'prog) pesconfs \<Rightarrow> ('k \<Rightarrow> ('l,'k,'s,'prog) esconfs) \<Rightarrow> bool" where
  "same_length c cs \<equiv> \<forall>k. length (cs k) = length c"
 
definition same_state :: "('l,'k,'s,'prog) pesconfs \<Rightarrow> ('k \<Rightarrow> ('l,'k,'s,'prog) esconfs) \<Rightarrow> bool" where
  "same_state c cs \<equiv> \<forall>k j. j < length c \<longrightarrow> gets (c!j) = gets_es ((cs k)!j) \<and> getx (c!j) = getx_es ((cs k)!j)"

definition same_spec :: "('l,'k,'s,'prog) pesconfs \<Rightarrow> ('k \<Rightarrow> ('l,'k,'s,'prog) esconfs) \<Rightarrow> bool" where
  "same_spec c cs \<equiv> \<forall>k j. j < length c \<longrightarrow> (getspc (c!j)) k = getspc_es ((cs k) ! j)"

definition compat_tran :: "'Env \<Rightarrow> ('l,'k,'s,'prog) pesconfs \<Rightarrow> ('k \<Rightarrow> ('l,'k,'s,'prog) esconfs) \<Rightarrow> bool" where
  "compat_tran \<Gamma> c cs \<equiv> \<forall>j. Suc j < length c \<longrightarrow> 
                              ((\<exists>t k. (\<Gamma> \<turnstile> c!j -pes-(t\<sharp>k)\<rightarrow> c!Suc j)) \<and>
                              (\<forall>k t. (\<Gamma> \<turnstile> c!j -pes-(t\<sharp>k)\<rightarrow> c!Suc j) \<longrightarrow> (\<Gamma> \<turnstile> cs k!j -es-(t\<sharp>k)\<rightarrow> cs k! Suc j) \<and>
                                      (\<forall>k'. k' \<noteq> k \<longrightarrow> (\<Gamma> \<turnstile> cs k'!j -ese\<rightarrow> cs k'! Suc j))))
                              \<or>
                              ((\<Gamma> \<turnstile> (c!j) -pese\<rightarrow> (c!Suc j)) \<and> (\<forall>k. (\<Gamma> \<turnstile> ((cs k)!j) -ese\<rightarrow> ((cs k)! Suc j))))"

definition conjoin :: "'Env \<Rightarrow> ('l,'k,'s,'prog) pesconfs \<Rightarrow> ('k \<Rightarrow> ('l,'k,'s,'prog) esconfs) \<Rightarrow> bool"  ("_ _ \<propto> _" [65,65] 64) where
  "\<Gamma> c \<propto> cs \<equiv> (same_length c cs) \<and> (same_state c cs) \<and> (same_spec c cs) \<and> (compat_tran \<Gamma> c cs)"

subsubsection \<open>Lemmas of conjoin\<close>

lemma acts_in_conjoin_cpts: "\<Gamma> c \<propto> cs \<Longrightarrow> \<forall>i. Suc i < length (cs k) \<longrightarrow> \<Gamma> \<turnstile> ((cs k)!i) -ese\<rightarrow> ((cs k)! Suc i) 
        \<or> (\<exists>e. \<Gamma> \<turnstile> ((cs k)!i) -es-(EvtEnt e\<sharp>k)\<rightarrow> ((cs k)! Suc i))
        \<or> (\<exists>c. \<Gamma> \<turnstile> ((cs k)!i) -es-(Cmd c\<sharp>k)\<rightarrow> ((cs k)! Suc i))"
  proof -
    assume p0: "\<Gamma> c \<propto> cs"
    {
      fix i
      assume a0: "Suc i < length (cs k)"
      from p0 have a1: "length c = length (cs k)" by (simp add:conjoin_def same_length_def)
      from p0 have "compat_tran \<Gamma> c cs" by (simp add:conjoin_def)
      with a0 a1 have "(\<exists>t k. (\<Gamma> \<turnstile> c!i -pes-(t\<sharp>k)\<rightarrow> c!Suc i) \<and>
                          (\<forall>k t. (\<Gamma> \<turnstile> c!i -pes-(t\<sharp>k)\<rightarrow> c!Suc i) \<longrightarrow> (\<Gamma> \<turnstile> cs k!i -es-(t\<sharp>k)\<rightarrow> cs k! Suc i) \<and>
                                  (\<forall>k'. k' \<noteq> k \<longrightarrow> (\<Gamma> \<turnstile> cs k'!i -ese\<rightarrow> cs k'! Suc i))))
                          \<or>
                          ((\<Gamma> \<turnstile> (c!i) -pese\<rightarrow> (c!Suc i)) \<and> (\<forall>k. (\<Gamma> \<turnstile> ((cs k)!i) -ese\<rightarrow> ((cs k)! Suc i))))" 
        by (simp add: compat_tran_def)
      then have "\<Gamma> \<turnstile> ((cs k)!i) -ese\<rightarrow> ((cs k)! Suc i) 
              \<or> (\<exists>e. \<Gamma> \<turnstile> ((cs k)!i) -es-(EvtEnt e\<sharp>k)\<rightarrow> ((cs k)! Suc i))
              \<or> (\<exists>c. \<Gamma> \<turnstile> ((cs k)!i) -es-(Cmd c\<sharp>k)\<rightarrow> ((cs k)! Suc i))"
        proof
          assume b0: "\<exists>t k. (\<Gamma> \<turnstile> c!i -pes-(t\<sharp>k)\<rightarrow> c!Suc i) \<and>
                          (\<forall>k t. (\<Gamma> \<turnstile> c!i -pes-(t\<sharp>k)\<rightarrow> c!Suc i) \<longrightarrow> (\<Gamma> \<turnstile> cs k!i -es-(t\<sharp>k)\<rightarrow> cs k! Suc i) \<and>
                                  (\<forall>k'. k' \<noteq> k \<longrightarrow> (\<Gamma> \<turnstile> cs k'!i -ese\<rightarrow> cs k'! Suc i)))"
          then obtain t and k1 where b1: "(\<Gamma> \<turnstile> c!i -pes-(t\<sharp>k1)\<rightarrow> c!Suc i) \<and>
                          (\<forall>k t. (\<Gamma> \<turnstile> c!i -pes-(t\<sharp>k)\<rightarrow> c!Suc i) \<longrightarrow> (\<Gamma> \<turnstile> cs k!i -es-(t\<sharp>k)\<rightarrow> cs k! Suc i) \<and>
                                  (\<forall>k'. k' \<noteq> k \<longrightarrow> (\<Gamma> \<turnstile> cs k'!i -ese\<rightarrow> cs k'! Suc i)))" by auto
          then show ?thesis
            proof(cases "k = k1")
              assume c0: "k = k1"
              with b1 show ?thesis by (meson estran_impl_evtentorcmd2') 
            next
              assume c0: "k \<noteq> k1"
              with b1 show ?thesis by auto
            qed
        next
          assume b0: "(\<Gamma> \<turnstile> (c!i) -pese\<rightarrow> (c!Suc i)) \<and> (\<forall>k. (\<Gamma> \<turnstile> ((cs k)!i) -ese\<rightarrow> ((cs k)! Suc i)))"
          then show ?thesis by simp
        qed
    }
    then show ?thesis by simp
  qed

lemma entevt_in_conjoin_cpts: 
  "\<lbrakk>\<Gamma> c \<propto> cs; Suc i < length (cs k); getspc_es ((cs k)!i) = EvtSys es; 
    getspc_es ((cs k)!Suc i) \<noteq> EvtSys es \<rbrakk>
    \<Longrightarrow> (\<exists>e. \<Gamma> \<turnstile> ((cs k)!i) -es-(EvtEnt e\<sharp>k)\<rightarrow> ((cs k)! Suc i))"
  proof -
    assume p0: "\<Gamma> c \<propto> cs"
      and  p1: "Suc i < length (cs k)"
      and  p2: "getspc_es ((cs k)!i) = EvtSys es"
      and  p3: "getspc_es ((cs k)!Suc i) \<noteq> EvtSys es"
    then have "\<Gamma> \<turnstile> ((cs k)!i) -ese\<rightarrow> ((cs k)! Suc i) 
        \<or> (\<exists>e. \<Gamma> \<turnstile> ((cs k)!i) -es-(EvtEnt e\<sharp>k)\<rightarrow> ((cs k)! Suc i))
        \<or> (\<exists>c. \<Gamma> \<turnstile> ((cs k)!i) -es-(Cmd c\<sharp>k)\<rightarrow> ((cs k)! Suc i))"
      using acts_in_conjoin_cpts by fastforce 
    then show ?thesis
      proof
        assume "\<Gamma> \<turnstile> ((cs k)!i) -ese\<rightarrow> ((cs k)! Suc i)"
        with p2 p3 show ?thesis by (simp add: esetran_eqconf1) 
      next
        assume "(\<exists>e. \<Gamma> \<turnstile> cs k ! i -es-EvtEnt e\<sharp>k\<rightarrow> cs k ! Suc i) 
              \<or> (\<exists>c. \<Gamma> \<turnstile> cs k ! i -es-Cmd c\<sharp>k\<rightarrow> cs k ! Suc i)"
        then show ?thesis 
          proof
            assume "\<exists>e. \<Gamma> \<turnstile> cs k ! i -es-EvtEnt e\<sharp>k\<rightarrow> cs k ! Suc i"
            then show ?thesis by simp
          next
            assume "\<exists>c. \<Gamma> \<turnstile> cs k ! i -es-Cmd c\<sharp>k\<rightarrow> cs k ! Suc i"
            with p2 p3 show ?thesis 
              by (meson cmd_enable_impl_anonyevt2 esys_not_eseq) 
          qed
      qed
  qed

lemma notentevt_in_conjoin_cpts: 
  "\<lbrakk>\<Gamma> c \<propto> cs; Suc i < length (cs k); \<not>(getspc_es ((cs k)!i) = EvtSys es \<and> getspc_es ((cs k)!Suc i) \<noteq> EvtSys es);
    \<forall>i < length (cs k). getspc_es ((cs k) ! i) = EvtSys es 
                        \<or> (\<exists>e. is_anonyevt e \<and> getspc_es ((cs k) ! i) = EvtSeq e (EvtSys es))\<rbrakk>
    \<Longrightarrow> \<not>(\<exists>e. \<Gamma> \<turnstile> ((cs k)!i) -es-(EvtEnt e\<sharp>k)\<rightarrow> ((cs k)! Suc i))"
  proof -
    assume p0: "\<Gamma> c \<propto> cs"
      and  p1: "Suc i < length (cs k)"
      and  p2: "\<not>(getspc_es ((cs k)!i) = EvtSys es \<and> getspc_es ((cs k)!Suc i) \<noteq> EvtSys es)"
      and  p3: "\<forall>i < length (cs k). getspc_es ((cs k) ! i) = EvtSys es 
                    \<or> (\<exists>e. is_anonyevt e \<and> getspc_es ((cs k) ! i) = EvtSeq e (EvtSys es))"
    from p2 have "getspc_es ((cs k)!i) \<noteq> EvtSys es \<or> getspc_es ((cs k)!Suc i) = EvtSys es" by simp
    with p3 have "(\<exists>e. is_anonyevt e \<and> getspc_es ((cs k) ! i) = EvtSeq e (EvtSys es)) 
                  \<or> getspc_es ((cs k)!Suc i) = EvtSys es"
      using Suc_lessD p1 by blast
    then show ?thesis
      proof
        assume "\<exists>e. is_anonyevt e \<and> getspc_es ((cs k) ! i) = EvtSeq e (EvtSys es)"
        then obtain e1 where "is_anonyevt e1 \<and> getspc_es ((cs k) ! i) = EvtSeq e1 (EvtSys es)" by auto
        then show ?thesis using evtent_is_basicevt_inevtseq2 by fastforce
      next
        assume "getspc_es ((cs k)!Suc i) = EvtSys es"
        then show ?thesis by (metis Suc_lessD evtseq_no_evtent2 evtsys_not_eq_in_tran_aux1 p1 p3) 
      qed
  qed

lemma take_n_conjoin: "\<lbrakk>\<Gamma> c \<propto> cs; n \<le> length c; c1 = take n c; cs1 = (\<lambda>k. take n (cs k))\<rbrakk> 
    \<Longrightarrow> \<Gamma> c1 \<propto> cs1"
  proof -
    assume p0: "\<Gamma> c \<propto> cs"
      and  p1: "n \<le> length c"
      and  p2: "c1 = take n c"
      and  p3: "cs1 = (\<lambda>k. take n (cs k))"
    have a0: "same_length c1 cs1" by (metis conjoin_def length_take p0 p2 p3 same_length_def) 
    then have a1: "\<forall>k. length (cs1 k) = length c1" by (simp add:same_length_def)
    
    have "same_state c1 cs1"
      proof -
      {
        fix k j
        assume b0: "j < length c1"
        from p1 p3 a1 have b1: "cs1 k = take n (cs k)" by simp 
        from p0 have b2[rule_format]: "\<forall>k j. j < length c 
              \<longrightarrow> gets (c!j) = gets_es ((cs k)!j) \<and> getx (c!j) = getx_es ((cs k)!j)"
          by (simp add:conjoin_def same_state_def)
        from p2 b1 b0 have "gets (c ! j) = gets (c1 ! j) \<and> gets_es ((cs k)!j) = gets_es ((cs1 k)!j)
          \<and> getx (c!j) = getx (c1!j)"
          by (simp add: nth_append)
        with p1 p2 b1 b2[of j k] b0 have "gets (c1!j) = gets_es ((cs1 k)!j) \<and> getx (c1!j) = getx_es ((cs1 k)!j)"
          by simp
      }
      then show ?thesis by (simp add:same_state_def)
      qed
    moreover
    have "same_spec c1 cs1" 
      proof -
      {
        fix k j
        assume b0: "j < length c1"
        from p1 p3 a1 have b1: "cs1 k = take n (cs k)" by simp 
        from p0 have b2[rule_format]: "\<forall>k j. j < length c 
              \<longrightarrow> (getspc (c!j)) k = getspc_es ((cs k) ! j)"
          by (simp add:conjoin_def same_spec_def)
        from p2 b1 b0 have "getspc (c1!j) = getspc (c!j) 
          \<and> getspc_es ((cs k) ! j) = getspc_es ((cs1 k) ! j)" 
          by (simp add: nth_append)
        then have "(getspc (c1!j)) k = getspc_es ((cs1 k) ! j)"
          using b0 b2 p2 by auto 
      }
      then show ?thesis by (simp add:same_spec_def)
      qed
    moreover
    have "compat_tran \<Gamma> c1 cs1"
      proof -
      {
        fix j
        assume b0: "Suc j < length c1"
        with p0 p2 have "((\<exists>t k. (\<Gamma> \<turnstile> c!j -pes-(t\<sharp>k)\<rightarrow> c!Suc j)) \<and>
                        (\<forall>k t. (\<Gamma> \<turnstile> c!j -pes-(t\<sharp>k)\<rightarrow> c!Suc j) \<longrightarrow> (\<Gamma> \<turnstile> cs k!j -es-(t\<sharp>k)\<rightarrow> cs k! Suc j) \<and>
                                (\<forall>k'. k' \<noteq> k \<longrightarrow> (\<Gamma> \<turnstile> cs k'!j -ese\<rightarrow> cs k'! Suc j))))
                        \<or>
                        ((\<Gamma> \<turnstile> (c!j) -pese\<rightarrow> (c!Suc j)) \<and> (\<forall>k. (\<Gamma> \<turnstile> ((cs k)!j) -ese\<rightarrow> ((cs k)! Suc j))))"
          by (simp add:conjoin_def compat_tran_def)
        moreover
        from p2 b0 have "c!j = c1!j" by simp
        moreover
        from p2 b0 have "c!Suc j = c1!Suc j" by simp
        moreover
        from p1 p2 p3 a1 b0 have "\<forall>k. cs1 k!j = cs k!j"
          by (simp add: Suc_lessD) 
        moreover
        from p1 p2 p3 a1 b0 have "\<forall>k. cs1 k!Suc j = cs k!Suc j"
          by (simp add: Suc_lessD) 
        ultimately
        have "((\<exists>t k. (\<Gamma> \<turnstile> c1!j -pes-(t\<sharp>k)\<rightarrow> c1!Suc j)) \<and>
                    (\<forall>k t. (\<Gamma> \<turnstile> c1!j -pes-(t\<sharp>k)\<rightarrow> c1!Suc j) \<longrightarrow> (\<Gamma> \<turnstile> cs1 k!j -es-(t\<sharp>k)\<rightarrow> cs1 k! Suc j) \<and>
                            (\<forall>k'. k' \<noteq> k \<longrightarrow> (\<Gamma> \<turnstile> cs1 k'!j -ese\<rightarrow> cs1 k'! Suc j))))
                    \<or>
                    ((\<Gamma> \<turnstile> (c1!j) -pese\<rightarrow> (c1!Suc j)) \<and> (\<forall>k. (\<Gamma> \<turnstile> ((cs1 k)!j) -ese\<rightarrow> ((cs1 k)! Suc j))))" by simp
      }
      then show ?thesis by (simp add:compat_tran_def)
      qed
    ultimately show ?thesis by (simp add:conjoin_def a0)
  qed

lemma drop_n_conjoin: "\<lbrakk>\<Gamma> c \<propto> cs; n \<le> length c; c1 = drop n c; cs1 = (\<lambda>k. drop n (cs k))\<rbrakk> 
    \<Longrightarrow> \<Gamma> c1 \<propto> cs1"
  proof -
    assume p0: "\<Gamma> c \<propto> cs"
      and  p1: "n \<le> length c"
      and  p2: "c1 = drop n c"
      and  p3: "cs1 = (\<lambda>k. drop n (cs k))"
    have a0: "same_length c1 cs1" by (metis conjoin_def length_drop p0 p2 p3 same_length_def) 
    then have a1: "\<forall>k. length (cs1 k) = length c1" by (simp add:same_length_def)
    
    have "same_state c1 cs1"
      proof -
      {
        fix k j
        assume b0: "j < length c1"
        from p1 p3 a1 have b1: "cs1 k = drop n (cs k)" by simp 
        from p0 have b2[rule_format]: "\<forall>k j. j < length c 
              \<longrightarrow> gets (c!j) = gets_es ((cs k)!j) \<and> getx (c!j) = getx_es ((cs k)!j)"
          by (simp add:conjoin_def same_state_def)
        from p2 b1 b0 have "gets (c ! (n + j)) = gets (c1 ! j) \<and> gets_es ((cs k)!(n + j)) = gets_es ((cs1 k)!j)
          \<and> getx (c!(n + j)) = getx (c1!j)"
          proof -
            have f1: "n + j \<le> length c"
              using b0 p2 by auto
            then have "n + j \<le> length (cs k)"
              by (metis (no_types) conjoin_def p0 same_length_def)
            then show ?thesis
              using f1 by (simp add: b1 p2)
          qed
          
        with p1 p2 b1 b2[of "n + j" k] b0 have "gets (c1!j) = gets_es ((cs1 k)!j) \<and> getx (c1!j) = getx_es ((cs1 k)!j)"
          by (smt a1 add_diff_cancel_left' drop_eq_Nil length_drop less_diff_conv2 list.size(3) 
              nat_le_linear nat_neq_iff not_less_zero nth_drop order.asym semiring_normalization_rules(24))
          
      }
      then show ?thesis by (simp add:same_state_def)
      qed
    moreover
    have "same_spec c1 cs1" 
      proof -
      {
        fix k j
        assume b0: "j < length c1"
        from p1 p3 a1 have b1: "cs1 k = drop n (cs k)" by simp 
        from p0 have b2[rule_format]: "\<forall>k j. j < length c 
              \<longrightarrow> (getspc (c!j)) k = getspc_es ((cs k) ! j)"
          by (simp add:conjoin_def same_spec_def)
        from p2 b1 b0 have "getspc (c1!j) = getspc (c!(n+j)) 
          \<and> getspc_es ((cs k) ! (n+j)) = getspc_es ((cs1 k) ! j)" 
          proof -
            have f1: "n + j \<le> length c"
              using b0 p2 by auto
            then have "n + j \<le> length (cs k)"
              by (metis (no_types) conjoin_def p0 same_length_def)
            then show ?thesis
              using f1 by (simp add: b1 p2)
          qed
        then have "(getspc (c1!j)) k = getspc_es ((cs1 k) ! j)"
          using b0 b2 p2 by auto 
      }
      then show ?thesis by (simp add:same_spec_def)
      qed
    moreover
    have "compat_tran \<Gamma> c1 cs1"
      proof -
      {
        fix j
        assume b0: "Suc j < length c1"
        with p0 p2 have "((\<exists>t k. (\<Gamma> \<turnstile> c!(n+j) -pes-(t\<sharp>k)\<rightarrow> c!Suc (n+j))) \<and>
                        (\<forall>k t. (\<Gamma> \<turnstile> c!(n+j) -pes-(t\<sharp>k)\<rightarrow> c!Suc (n+j)) \<longrightarrow> (\<Gamma> \<turnstile> cs k!(n+j) -es-(t\<sharp>k)\<rightarrow> cs k! Suc (n+j)) \<and>
                                (\<forall>k'. k' \<noteq> k \<longrightarrow> (\<Gamma> \<turnstile> cs k'!(n+j) -ese\<rightarrow> cs k'! Suc (n+j)))))
                        \<or>
                        ((\<Gamma> \<turnstile> (c!(n+j)) -pese\<rightarrow> (c!Suc (n+j))) \<and> (\<forall>k. (\<Gamma> \<turnstile> ((cs k)!(n+j)) -ese\<rightarrow> ((cs k)! Suc (n+j)))))"
          by (simp add:conjoin_def compat_tran_def)
        moreover
        from p2 b0 have "c!(n+j) = c1!j" by simp
        moreover
        from p2 b0 have "c!Suc (n+j) = c1!Suc j" by simp
        moreover
        from p1 p2 p3 a1 b0 have "\<forall>k. cs1 k!j = cs k!(n+j)"
          by (metis drop_eq_Nil length_greater_0_conv less_imp_Suc_add linear nth_drop zero_less_Suc)
        moreover
        from p1 p2 p3 a1 b0 have "\<forall>k. cs1 k!Suc j = cs k!Suc (n+j)"
          by (smt Suc_lessE add_Suc_right drop_eq_Nil length_greater_0_conv linear nth_drop zero_less_Suc)
        ultimately
        have "((\<exists>t k. (\<Gamma> \<turnstile> c1!j -pes-(t\<sharp>k)\<rightarrow> c1!Suc j)) \<and>
                    (\<forall>k t. (\<Gamma> \<turnstile> c1!j -pes-(t\<sharp>k)\<rightarrow> c1!Suc j) \<longrightarrow> (\<Gamma> \<turnstile> cs1 k!j -es-(t\<sharp>k)\<rightarrow> cs1 k! Suc j) \<and>
                            (\<forall>k'. k' \<noteq> k \<longrightarrow> (\<Gamma> \<turnstile> cs1 k'!j -ese\<rightarrow> cs1 k'! Suc j))))
                    \<or>
                    ((\<Gamma> \<turnstile> (c1!j) -pese\<rightarrow> (c1!Suc j)) \<and> (\<forall>k. (\<Gamma> \<turnstile> ((cs1 k)!j) -ese\<rightarrow> ((cs1 k)! Suc j))))" by simp
      }
      then show ?thesis by (simp add:compat_tran_def)
      qed
    ultimately show ?thesis by (simp add:conjoin_def a0)
  qed

lemma conjoin_imp_cptses_k_help: "\<lbrakk>c \<in> cpts_pes \<Gamma>\<rbrakk> \<Longrightarrow> 
      \<forall>cs k. \<Gamma> c \<propto> cs \<longrightarrow> (cs k \<in> cpts_es \<Gamma>)" 
  proof -
    assume p0: "c \<in> cpts_pes \<Gamma>"
    {
      fix k
      from p0 have "\<forall>cs. c \<in> cpts_pes \<Gamma> \<and> \<Gamma> c \<propto> cs \<longrightarrow> (cs k \<in> cpts_es \<Gamma>)"
        proof(induct c)
          case (CptsPesOne pes s x)

          {
            fix cs
            assume a0: "\<Gamma> [(pes, s, x)] \<propto> cs"
            then have p3:"length (cs k) = 1" by (simp add:conjoin_def same_length_def)
            from a0 have p5: "same_spec [(pes, s, x)] cs \<and> same_state [(pes, s, x)] cs" by (simp add:conjoin_def)
            with a0 p3 have "cs k ! 0  = (pes k, s, x)" 
              using esconf_trip pesconf_trip same_spec_def same_state_def
                by (metis One_nat_def length_Cons list.size(3) nth_Cons_0 prod.sel(1) prod.sel(2) zero_less_one) 
            with p3 have "cs k \<in> cpts_es \<Gamma>"
              by (metis (no_types, hide_lams) One_nat_def Suc_less_eq cpts_es.CptsEsOne length_0_conv length_Cons neq0_conv neq_Nil_conv prod_cases3)
          }
          then show ?case by auto
        next
          case (CptsPesEnv pes t x xs s y)
          assume a0: "(pes, t, x) # xs \<in> cpts_pes \<Gamma>"
            and  a1[rule_format]: "\<forall>cs. (pes, t, x) # xs \<in> cpts_pes \<Gamma> \<and> \<Gamma> (pes, t, x) # xs \<propto> cs \<longrightarrow> cs k \<in> cpts_es \<Gamma>"
          {
            fix cs
            assume b0: "(pes, s, y) # (pes, t, x) # xs \<in> cpts_pes \<Gamma>"
              and  b1: "\<Gamma> (pes, s, y) # (pes, t, x) # xs \<propto> cs"
            let ?esl = "(pes, t, x) # xs"
            let ?esllon = "(pes, s, y) # (pes, t, x) # xs"
            let ?cs = "(\<lambda>k. drop 1 (cs k))"
            from b1 have "\<Gamma> ?esl \<propto> ?cs" using drop_n_conjoin[of \<Gamma> ?esllon cs 1 ?esl ?cs] by auto
            with a0 a1[of ?cs] have b2: "?cs k \<in> cpts_es \<Gamma>" by simp
            from b1 have b3: "cs k ! 0 = (pes k, s, y)" 
              using conjoin_def[of \<Gamma> ?esllon cs] same_state_def[of ?esllon cs] same_spec_def[of ?esllon cs]
                by (metis esconf_trip gets_def getspc_def getx_def length_greater_0_conv 
                  list.simps(3) nth_Cons_0 prod.sel(1) prod.sel(2)) 

            from b1 have "getspc_es (cs k ! 1) = (getspc (?esllon ! 1)) k" 
              using conjoin_def[of \<Gamma> ?esllon cs] same_spec_def[of ?esllon cs]
                by (metis diff_Suc_1 length_Cons zero_less_Suc zero_less_diff) 
            moreover
            from b1 have "gets (?esllon ! 1) = gets_es ((cs k)!1) \<and> getx (?esllon ! 1) = getx_es ((cs k)!1)"
              using conjoin_def[of \<Gamma> ?esllon cs] same_state_def[of ?esllon cs]
                 diff_Suc_1 length_Cons zero_less_Suc zero_less_diff by fastforce
            ultimately have "cs k ! 1 = (pes k, t, x)" 
              using b0 getspc_def gets_def getx_def
                by (metis One_nat_def esconf_trip fst_conv nth_Cons_0 nth_Cons_Suc snd_conv) 
            
            with b2 b3 have "cs k \<in> cpts_es \<Gamma>" using CptsEsEnv
              by (metis Cons_nth_drop_Suc One_nat_def Suc_lessD cpts_es_not_empty 
                    drop_0 drop_eq_Nil not_le) 
          }
          then show ?case by auto
        next
          case (CptsPesComp pes1 s y ct pes2 t x xs)
          assume a0: "\<Gamma> \<turnstile> (pes1, s, y) -pes-ct\<rightarrow> (pes2, t, x)"
            and  a1: "(pes2, t, x) # xs \<in> cpts_pes \<Gamma>"
            and  a2[rule_format]: "\<forall>cs. (pes2, t, x) # xs \<in> cpts_pes \<Gamma> \<and> \<Gamma> (pes2, t, x) # xs \<propto> cs \<longrightarrow> cs k \<in> cpts_es \<Gamma>"
          {
            fix cs
            assume b0: "(pes1, s, y) # (pes2, t, x) # xs \<in> cpts_pes \<Gamma>"
              and  b1: "\<Gamma> (pes1, s, y) # (pes2, t, x) # xs \<propto> cs"
            let ?esl = "(pes2, t, x) # xs"
            let ?esllon = "(pes1, s, y) # (pes2, t, x) # xs"
            let ?cs = "(\<lambda>k. drop 1 (cs k))"
            from b1 have "\<Gamma> ?esl \<propto> ?cs" using drop_n_conjoin[of \<Gamma> ?esllon cs 1 ?esl ?cs] by auto
            with a1 a2[of ?cs] have b2: "?cs k \<in> cpts_es \<Gamma>" by simp
            from b1 have b3: "cs k ! 0 = (pes1 k, s, y)" 
              using conjoin_def[of \<Gamma> ?esllon cs] same_state_def[of ?esllon cs] same_spec_def[of ?esllon cs]
                by (metis esconf_trip gets_def getspc_def getx_def length_greater_0_conv 
                  list.simps(3) nth_Cons_0 prod.sel(1) prod.sel(2)) 

            from b1 have "getspc_es (cs k ! 1) = (getspc (?esllon ! 1)) k" 
              using conjoin_def[of \<Gamma> ?esllon cs] same_spec_def[of ?esllon cs]
                by (metis diff_Suc_1 length_Cons zero_less_Suc zero_less_diff) 
            moreover
            from b1 have "gets (?esllon ! 1) = gets_es ((cs k)!1) \<and> getx (?esllon ! 1) = getx_es ((cs k)!1)"
              using conjoin_def[of \<Gamma> ?esllon cs] same_state_def[of ?esllon cs]
                 diff_Suc_1 length_Cons zero_less_Suc zero_less_diff by fastforce
            ultimately have b4: "cs k ! 1 = (pes2 k, t, x)" 
              using b0 getspc_def gets_def getx_def
                by (metis One_nat_def esconf_trip fst_conv nth_Cons_0 nth_Cons_Suc snd_conv) 
            
            from b1 have "compat_tran \<Gamma> ?esllon cs" by (simp add:conjoin_def)
            then have "((\<exists>t k. (\<Gamma> \<turnstile> ?esllon!0 -pes-(t\<sharp>k)\<rightarrow> ?esllon!Suc 0)) \<and>
                                (\<forall>k t. (\<Gamma> \<turnstile> ?esllon!0 -pes-(t\<sharp>k)\<rightarrow> ?esllon!Suc 0) \<longrightarrow> (\<Gamma> \<turnstile> cs k!0 -es-(t\<sharp>k)\<rightarrow> cs k! Suc 0) \<and>
                                        (\<forall>k'. k' \<noteq> k \<longrightarrow> (\<Gamma> \<turnstile> cs k'!0 -ese\<rightarrow> cs k'! Suc 0))))
                                \<or>
                                ((\<Gamma> \<turnstile> (?esllon!0) -pese\<rightarrow> (?esllon!Suc 0)) \<and> (\<forall>k. (\<Gamma> \<turnstile> ((cs k)!0) -ese\<rightarrow> ((cs k)! Suc 0))))"
               using compat_tran_def[of \<Gamma> ?esllon cs] by fastforce
            then have "cs k \<in> cpts_es \<Gamma>" 
              proof
                assume c0: "(\<exists>t k. (\<Gamma> \<turnstile> ?esllon!0 -pes-(t\<sharp>k)\<rightarrow> ?esllon!Suc 0)) \<and>
                                (\<forall>k t. (\<Gamma> \<turnstile> ?esllon!0 -pes-(t\<sharp>k)\<rightarrow> ?esllon!Suc 0) \<longrightarrow> (\<Gamma> \<turnstile> cs k!0 -es-(t\<sharp>k)\<rightarrow> cs k! Suc 0) \<and>
                                        (\<forall>k'. k' \<noteq> k \<longrightarrow> (\<Gamma> \<turnstile> cs k'!0 -ese\<rightarrow> cs k'! Suc 0)))"
                then obtain t1 and k1 where c1: "(\<Gamma> \<turnstile> ?esllon!0 -pes-(t1\<sharp>k1)\<rightarrow> ?esllon!Suc 0)" by auto
                with c0 have c2: "(\<Gamma> \<turnstile> cs k1!0 -es-(t1\<sharp>k1)\<rightarrow> cs k1! Suc 0) \<and>
                                   (\<forall>k'. k' \<noteq> k1 \<longrightarrow> (\<Gamma> \<turnstile> cs k'!0 -ese\<rightarrow> cs k'! Suc 0))" by auto
                show ?thesis
                  proof(cases "k = k1")
                    assume d0: "k = k1"
                    with c2 have "(\<Gamma> \<turnstile> cs k!0 -es-(t1\<sharp>k)\<rightarrow> cs k! Suc 0)" by auto
                    with b2 b3 b4 show ?thesis using CptsEsComp
                      by (metis Cons_nth_drop_Suc One_nat_def Suc_lessD cpts_es_not_empty drop_0 drop_eq_Nil not_le)
                  next
                    assume d0: "k \<noteq> k1"
                    with c2 have "\<Gamma> \<turnstile> cs k!0 -ese\<rightarrow> cs k! Suc 0" by auto
                    with b2 b3 b4 show ?thesis using CptsEsEnv
                      by (metis Cons_nth_drop_Suc One_nat_def Suc_lessD cpts_es_not_empty 
                        drop_0 drop_eq_Nil esetran_eqconf not_le) 
                  qed
              next
                assume c0: "(\<Gamma> \<turnstile> (?esllon!0) -pese\<rightarrow> (?esllon!Suc 0)) \<and> (\<forall>k. (\<Gamma> \<turnstile> ((cs k)!0) -ese\<rightarrow> ((cs k)! Suc 0)))"
                then have "\<Gamma> \<turnstile> ((cs k)!0) -ese\<rightarrow> ((cs k)! Suc 0)" by simp
                with b2 b3 b4 show ?thesis using CptsEsEnv a0 c0 pes_tran_not_etran1 by fastforce 
              qed
          }
          then show ?case by auto
        qed
    }
    with p0 show ?thesis by simp 
  qed

lemma conjoin_imp_cptses_k: 
      "\<lbrakk>c \<in> cpts_of_pes \<Gamma> pes s x; \<Gamma> c \<propto> cs\<rbrakk> 
        \<Longrightarrow> cs k \<in> cpts_of_es \<Gamma> (pes k) s x" 
  proof -
    assume p0: "c \<in> cpts_of_pes \<Gamma> pes s x"
      and  p1: "\<Gamma> c \<propto> cs"
    from p0 have a1: "c\<in>cpts_pes \<Gamma> \<and> c!0 = (pes,s,x)" by (simp add:cpts_of_pes_def)
    from a1 p1 have "cs k \<in> cpts_es \<Gamma>" using conjoin_imp_cptses_k_help by auto
    moreover
    from p0 p1 have "cs k ! 0 = (pes k,s,x)"
      by (metis a1 conjoin_def cpts_pes_not_empty esconf_trip fst_conv gets_def 
        getspc_def getx_def length_greater_0_conv same_spec_def same_state_def snd_conv) 
    ultimately show ?thesis by (simp add:cpts_of_es_def)
  qed

subsubsection \<open>Semantics is Compositional\<close>

lemma conjoin_cs_imp_cpt: "\<lbrakk>\<exists>k p. pes k = p; (\<exists>cs. (\<forall>k. (cs k) \<in> cpts_of_es \<Gamma> (pes k) s x) \<and> \<Gamma> c \<propto> cs)\<rbrakk>
                                \<Longrightarrow> c \<in> cpts_of_pes \<Gamma> pes s x"
  proof -
    assume p0: "\<exists>cs. (\<forall>k. (cs k) \<in> cpts_of_es \<Gamma> (pes k) s x) \<and> \<Gamma> c \<propto> cs"
      and  p1: "\<exists>k p. pes k = p"
    then obtain cs where "(\<forall>k. (cs k) \<in> cpts_of_es \<Gamma> (pes k) s x) \<and> \<Gamma> c \<propto> cs" by auto
    then have a0: "(\<forall>k. (cs k)!0=(pes k,s,x) \<and> (cs k) \<in> cpts_es \<Gamma>) \<and> \<Gamma> c \<propto> cs" by (simp add:cpts_of_es_def)
    from p1 obtain p and k where a1: "pes k = p" by auto

    from p1 obtain k and p where "pes k = p" by auto
    with a0 have a2: "(cs k)!0=(pes k,s,x) \<and> (cs k) \<in> cpts_es \<Gamma>" by auto
    then have "(cs k) \<noteq> []"  by auto
    moreover
    from a0 have "same_length c cs" by (simp add:conjoin_def)
    ultimately have a3: "c \<noteq> []" using same_length_def by force 

    have g0: "c!0 = (pes,s,x)"
      proof -
        from a3 a0 have "same_spec c cs" by (simp add:conjoin_def)
        with a3 have b2: "\<forall>k. (getspc (c!0)) k = getspc_es ((cs k) ! 0)" by (simp add:same_spec_def)
        with a0 have "\<forall>k. (getspc (c!0)) k = pes k" by (simp add:getspc_es_def)
        then have b3: "getspc (c!0) = pes" by auto

        from a0 have "same_state c cs"  by (simp add:conjoin_def)
        with a3 have "gets (c!0) = gets_es ((cs k)!0) \<and> getx (c!0) = getx_es ((cs k)!0)" 
          by (simp add:same_state_def)
        with a2 have "gets (c!0) = s \<and> getx (c!0) = x" 
          by (simp add:gets_def getx_def gets_es_def getx_es_def)
        with b3 show ?thesis using gets_def getx_def getspc_def by (metis prod.collapse)
      qed
    have "\<forall>i. i > 0 \<and> i \<le> length c \<longrightarrow> take i c \<in> cpts_pes \<Gamma>"
      proof -
      {
        fix i
        assume b0: "i > 0 \<and> i \<le> length c"
        then have "take i c \<in> cpts_pes \<Gamma>"
          proof(induct i)
            case 0 show ?case using "0.prems" by auto 
          next
            case (Suc j)
            assume c0: "0 < j \<and> j \<le> length c \<Longrightarrow> take j c \<in> cpts_pes \<Gamma>"
              and  c1: "0 < Suc j \<and> Suc j \<le> length c"
            show ?case
              proof(cases "j = 0")
                assume d0: "j = 0"
                with c0 show ?case by (simp add: a3 cpts_pes.CptsPesOne g0 hd_conv_nth take_Suc) 
              next
                assume d0: "j \<noteq> 0"
                from a0 have d1: "compat_tran \<Gamma> c cs" by (simp add:conjoin_def)
                then have d2: "\<forall>j. Suc j < length c \<longrightarrow> 
                              (\<exists>t k. (\<Gamma> \<turnstile> c!j -pes-(t\<sharp>k)\<rightarrow> c!Suc j) \<and>
                              (\<forall>k t. (\<Gamma> \<turnstile> c!j -pes-(t\<sharp>k)\<rightarrow> c!Suc j) \<longrightarrow> (\<Gamma> \<turnstile> cs k!j -es-(t\<sharp>k)\<rightarrow> cs k! Suc j) \<and>
                                      (\<forall>k'. k' \<noteq> k \<longrightarrow> (\<Gamma> \<turnstile> cs k'!j -ese\<rightarrow> cs k'! Suc j))))
                              \<or>
                              ((\<Gamma> \<turnstile> (c!j) -pese\<rightarrow> (c!Suc j)) \<and> (\<forall>k. (\<Gamma> \<turnstile> ((cs k)!j) -ese\<rightarrow> ((cs k)! Suc j))))"
                  by (simp add:compat_tran_def)
                
                from d0 have d3: "j - 1 \<ge> 0" by simp
                from c1 have d6: "Suc (j - 1) < length c" using d0 by auto 
                
                with d3 have d4: "(\<exists>t k. (\<Gamma> \<turnstile> c!(j-1) -pes-(t\<sharp>k)\<rightarrow> c!Suc (j-1)) \<and>
                              (\<forall>k t. (\<Gamma> \<turnstile> c!(j-1) -pes-(t\<sharp>k)\<rightarrow> c!Suc (j-1)) \<longrightarrow> (\<Gamma> \<turnstile> cs k!(j-1) -es-(t\<sharp>k)\<rightarrow> cs k! Suc (j-1)) \<and>
                                      (\<forall>k'. k' \<noteq> k \<longrightarrow> (\<Gamma> \<turnstile> cs k'!(j-1) -ese\<rightarrow> cs k'! Suc (j-1)))))
                              \<or>
                              ((\<Gamma> \<turnstile> (c!(j-1)) -pese\<rightarrow> (c!Suc (j-1))) \<and> (\<forall>k. (\<Gamma> \<turnstile> ((cs k)!(j-1)) -ese\<rightarrow> ((cs k)!Suc (j-1)))))"
                   using d2 by auto
                from c0 c1 d0 have d5: "take j c \<in> cpts_pes \<Gamma>" by auto
                from d4 show ?case
                  proof 
                    assume "(\<exists>t k. (\<Gamma> \<turnstile> c!(j-1) -pes-(t\<sharp>k)\<rightarrow> c!Suc (j-1)) \<and>
                              (\<forall>k t. (\<Gamma> \<turnstile> c!(j-1) -pes-(t\<sharp>k)\<rightarrow> c!Suc (j-1)) \<longrightarrow> (\<Gamma> \<turnstile> cs k!(j-1) -es-(t\<sharp>k)\<rightarrow> cs k! Suc (j-1)) \<and>
                                      (\<forall>k'. k' \<noteq> k \<longrightarrow> (\<Gamma> \<turnstile> cs k'!(j-1) -ese\<rightarrow> cs k'! Suc (j-1)))))"
                    then obtain t and k where e0: "(\<Gamma> \<turnstile> (c!(j-1)) -pes-(t\<sharp>k)\<rightarrow> (c!Suc (j-1)))" by auto
                    then have "\<Gamma> \<turnstile> ((take j c) ! (length (take j c) - 1)) -pes-(t\<sharp>k)\<rightarrow> (c!Suc (j-1))"
                      by (metis (no_types, lifting) Suc_diff_1 Suc_leD Suc_lessD 
                        d6 butlast_take c1 d0 length_butlast neq0_conv nth_append_length take_Suc_conv_app_nth) 
                    with d5 have "(take j c) @ [c!Suc (j-1)] \<in> cpts_pes \<Gamma>" using cpts_pes_onemore by blast
                    then show ?thesis using d0 d6 take_Suc_conv_app_nth by fastforce
                  next
                    assume "(\<Gamma> \<turnstile> (c!(j-1)) -pese\<rightarrow> (c!Suc (j-1))) \<and> (\<forall>k. (\<Gamma> \<turnstile> ((cs k)!(j-1)) -ese\<rightarrow> ((cs k)!Suc (j-1))))"
                    then have "\<Gamma> \<turnstile> ((take j c) ! (length (take j c) - 1)) -pese\<rightarrow> (c!Suc (j-1))" 
                      by (metis (no_types, lifting) Suc_diff_1 Suc_leD Suc_lessD 
                        d6 butlast_take c1 d0 length_butlast neq0_conv nth_append_length take_Suc_conv_app_nth) 
                    with d5 have "(take j c) @ [c!Suc (j-1)] \<in> cpts_pes \<Gamma>" using cpts_pes_onemore by blast
                    then show ?thesis using d0 d6 take_Suc_conv_app_nth by fastforce
                  qed
                    
              qed
          qed
      }
      then show ?thesis by auto
      qed

    with a3 have g1: "c\<in>cpts_pes \<Gamma>" by auto
    from g0 g1 show ?thesis by (simp add:cpts_of_pes_def)
  qed

lemma comp_tran_env: "\<lbrakk>(\<forall>k. cs k \<in> cpts_of_es \<Gamma> (pes k) t1 x1); c = (pes, t1, x1) # xs; c\<in>cpts_pes \<Gamma>; 
                        \<Gamma> c \<propto> cs; c' = (pes, s1, y1) # (pes, t1, x1) # xs\<rbrakk> \<Longrightarrow> 
      compat_tran \<Gamma> c' (\<lambda>k. (pes k, s1, y1) # cs k)"
  proof -
    let ?cs' = "\<lambda>k. (pes k, s1, y1) # cs k"
    assume p0: "\<forall>k. cs k \<in> cpts_of_es \<Gamma> (pes k) t1 x1"
      and  p1: "c \<in> cpts_pes \<Gamma>"
      and  p2: "\<Gamma> c \<propto> cs"
      and  p3: "c' = (pes, s1, y1) # (pes, t1, x1) # xs"
      and  p4: "c = (pes, t1, x1) # xs"
    from p0 have b3: "\<forall>k. cs k \<in> cpts_es \<Gamma> \<and> (cs k)!0 = (pes k,t1,x1)" by (simp add:cpts_of_es_def)
    show "compat_tran \<Gamma> c' ?cs'"
      proof -
      {
        fix j
        assume dd0: "Suc j < length c'"
        have "(\<exists>t k. (\<Gamma> \<turnstile> (c'!j) -pes-(t\<sharp>k)\<rightarrow> (c'!Suc j)) \<and>
                      (\<forall>k t. (\<Gamma> \<turnstile> c'!j -pes-(t\<sharp>k)\<rightarrow> c'!Suc j) \<longrightarrow> (\<Gamma> \<turnstile> ?cs' k!j -es-(t\<sharp>k)\<rightarrow> ?cs' k! Suc j) \<and>
                                      (\<forall>k'. k' \<noteq> k \<longrightarrow> (\<Gamma> \<turnstile> ?cs' k'!j -ese\<rightarrow> ?cs' k'! Suc j))))
                      \<or>
                      ((\<Gamma> \<turnstile> (c'!j) -pese\<rightarrow> (c'!Suc j)) \<and> (\<forall>k. (\<Gamma> \<turnstile> ((?cs' k)!j) -ese\<rightarrow> ((?cs' k)! Suc j))))"
          proof(cases "j = 0")
            assume d0: "j = 0"
            from p3 have "(\<Gamma> \<turnstile> (c'!0) -pese\<rightarrow> (c'!1))"
              by (simp add: pesetran.intros) 
            moreover
            have "\<forall>k. (\<Gamma> \<turnstile> ((?cs' k)!0) -ese\<rightarrow> ((?cs' k)!1))"
              by (simp add: b3 esetran.intros) 
            ultimately show ?thesis using d0 by simp
          next
            assume d0: "j \<noteq> 0"
            then have d0_1: "j > 0" by simp
            from p2 have "compat_tran \<Gamma> c cs" by (simp add:conjoin_def)
            then have d1: "\<forall>j. Suc j < length c \<longrightarrow> 
                              (\<exists>t k. (\<Gamma> \<turnstile> c!j -pes-(t\<sharp>k)\<rightarrow> c!Suc j) \<and>
                              (\<forall>k t. (\<Gamma> \<turnstile> c!j -pes-(t\<sharp>k)\<rightarrow> c!Suc j) \<longrightarrow> (\<Gamma> \<turnstile> cs k!j -es-(t\<sharp>k)\<rightarrow> cs k! Suc j) \<and>
                                      (\<forall>k'. k' \<noteq> k \<longrightarrow> (\<Gamma> \<turnstile> cs k'!j -ese\<rightarrow> cs k'! Suc j))))
                              \<or>
                              ((\<Gamma> \<turnstile> (c!j) -pese\<rightarrow> (c!Suc j)) \<and> (\<forall>k. (\<Gamma> \<turnstile> ((cs k)!j) -ese\<rightarrow> ((cs k)! Suc j))))"
               by (simp add:compat_tran_def)
            from p3 p4 dd0 d0 have d2: "Suc (j-1) < length c" by auto
            let ?j1 = "j - 1"
            from d1 d2 have d3: "(\<exists>t k. (\<Gamma> \<turnstile> c!(j-1) -pes-(t\<sharp>k)\<rightarrow> c!Suc (j-1)) \<and>
                              (\<forall>k t. (\<Gamma> \<turnstile> c!(j-1) -pes-(t\<sharp>k)\<rightarrow> c!Suc (j-1)) \<longrightarrow> (\<Gamma> \<turnstile> cs k!(j-1) -es-(t\<sharp>k)\<rightarrow> cs k! Suc (j-1)) \<and>
                                      (\<forall>k'. k' \<noteq> k \<longrightarrow> (\<Gamma> \<turnstile> cs k'!(j-1) -ese\<rightarrow> cs k'! Suc (j-1)))))
                              \<or>
                              ((\<Gamma> \<turnstile> (c!(j-1)) -pese\<rightarrow> (c!Suc (j-1))) \<and> (\<forall>k. (\<Gamma> \<turnstile> ((cs k)!(j-1)) -ese\<rightarrow> ((cs k)!Suc (j-1)))))"
               by auto
            from p3 p4 d0 dd0 have d4: "c'!j = c!(j-1) \<and> c'!Suc j = c!Suc (j-1)" by simp
            have d5: "(\<forall>k. (?cs' k) ! j= (cs k)! (j-1)) \<and> (\<forall>k. (?cs' k) ! Suc j= (cs k)! Suc (j-1))" 
              by (simp add: d0_1) 
            with d3 d4 show ?thesis by auto
          qed
        
      }
      then show ?thesis by (simp add:compat_tran_def)
      qed
  qed

lemma comp_tran_pestran: "\<lbrakk>(\<forall>k. cs k \<in> cpts_of_es \<Gamma> (pes2 k) t1 x1); c = (pes2, t1, x1) # xs; c\<in>cpts_pes \<Gamma>; 
                       \<Gamma> c \<propto> cs; c' = (pes1, s1, y1) # (pes2, t1, x1) # xs; \<Gamma> \<turnstile> (pes1, s1, y1) -pes-ct\<rightarrow> (pes2, t1, x1)\<rbrakk>
                        \<Longrightarrow> compat_tran \<Gamma> c' (\<lambda>k. (pes1 k, s1, y1) # cs k)"
  proof -
    let ?cs' = "\<lambda>k. (pes1 k, s1, y1) # cs k"
    assume p0: "\<forall>k. cs k \<in> cpts_of_es \<Gamma> (pes2 k) t1 x1"
      and  p1: "c \<in> cpts_pes \<Gamma>"
      and  p2: "\<Gamma> c \<propto> cs"
      and  p3: "c' = (pes1, s1, y1) # (pes2, t1, x1) # xs"
      and  p4: "c = (pes2, t1, x1) # xs"
      and  p5: "\<Gamma> \<turnstile> (pes1, s1, y1) -pes-ct\<rightarrow> (pes2, t1, x1)"
    from p0 have b3: "\<forall>k. cs k \<in> cpts_es \<Gamma> \<and> (cs k)!0 = (pes2 k,t1,x1)" by (simp add:cpts_of_es_def)
    show "compat_tran \<Gamma> c' ?cs'"
      proof -
      {
        fix j
        assume dd0: "Suc j < length c'"
        have "(\<exists>t k. (\<Gamma> \<turnstile> (c'!j) -pes-(t\<sharp>k)\<rightarrow> (c'!Suc j)) \<and>
                      (\<forall>k t. (\<Gamma> \<turnstile> c'!j -pes-(t\<sharp>k)\<rightarrow> c'!Suc j) \<longrightarrow> (\<Gamma> \<turnstile> ?cs' k!j -es-(t\<sharp>k)\<rightarrow> ?cs' k! Suc j) \<and>
                                      (\<forall>k'. k' \<noteq> k \<longrightarrow> (\<Gamma> \<turnstile> ?cs' k'!j -ese\<rightarrow> ?cs' k'! Suc j))))
                      \<or>
                      ((\<Gamma> \<turnstile> (c'!j) -pese\<rightarrow> (c'!Suc j)) \<and> (\<forall>k. (\<Gamma> \<turnstile> ((?cs' k)!j) -ese\<rightarrow> ((?cs' k)! Suc j))))"
          proof(cases "j = 0")
            assume d0: "j = 0"
            from p5 obtain k and aa where c0: "ct = (aa\<sharp>k)" using get_actk_def by (metis cases) 
            with p5 have "\<exists>es'. (\<Gamma> \<turnstile> (pes1 k, s1, y1) -es-(aa\<sharp>k)\<rightarrow> (es', t1, x1)) \<and> pes2 = pes1(k:=es')" 
              using pestran_estran by auto
            then obtain es' where c1: "(\<Gamma> \<turnstile> (pes1 k, s1, y1) -es-(aa\<sharp>k)\<rightarrow> (es', t1, x1)) \<and> pes2 = pes1(k:=es')"
              by auto
            from b3 have c2: "cs k \<in>cpts_es \<Gamma> \<and> (cs k)!0 = (pes2 k,t1,x1)" by auto
            then obtain xs1 where c4: "(cs k) = (pes2 k,t1,x1)#xs1"
              by (metis cpts_es_not_empty neq_Nil_conv nth_Cons_0) 
            then have c3: "?cs' k = (pes1 k, s1, y1) # (pes2 k,t1,x1)#xs1" by simp

            from p3 p5 c0 have g0: "\<Gamma> \<turnstile> (c'!0) -pes-(aa\<sharp>k)\<rightarrow> (c'!Suc 0)" by auto
            moreover
            have "\<forall>k1 t1. (\<Gamma> \<turnstile> c'!0 -pes-(t1\<sharp>k1)\<rightarrow> c'!Suc 0) \<longrightarrow> (\<Gamma> \<turnstile> ?cs' k1!0 -es-(t1\<sharp>k1)\<rightarrow> ?cs' k1! Suc 0) \<and>
                                      (\<forall>k'. k' \<noteq> k1 \<longrightarrow> (\<Gamma> \<turnstile> ?cs' k'!0 -ese\<rightarrow> ?cs' k'! Suc 0))"
              proof -
              {
                fix k1 t1
                assume d0: "\<Gamma> \<turnstile> c'!0 -pes-(t1\<sharp>k1)\<rightarrow> c'!Suc 0"
                with p3 have "\<Gamma> \<turnstile> ?cs' k1!0 -es-(t1\<sharp>k1)\<rightarrow> ?cs' k1! Suc 0"
                  using b3 fun_upd_apply nth_Cons_0 nth_Cons_Suc pestran_estran by fastforce
                moreover
                from d0 have "\<forall>k'. k' \<noteq> k1 \<longrightarrow> (\<Gamma> \<turnstile> ?cs' k'!0 -ese\<rightarrow> ?cs' k'! Suc 0)"
                  using b3 esetran.intros fun_upd_apply nth_Cons_0 nth_Cons_Suc p3 pestran_estran by fastforce
                ultimately have "(\<Gamma> \<turnstile> c'!0 -pes-(t1\<sharp>k1)\<rightarrow> c'!Suc 0) \<longrightarrow> (\<Gamma> \<turnstile> ?cs' k1!0 -es-(t1\<sharp>k1)\<rightarrow> ?cs' k1! Suc 0) \<and>
                                      (\<forall>k'. k' \<noteq> k1 \<longrightarrow> (\<Gamma> \<turnstile> ?cs' k'!0 -ese\<rightarrow> ?cs' k'! Suc 0))" by simp
              }
              then show ?thesis by auto
              qed
            ultimately show ?thesis using d0 by auto
          next
            assume d0: "j \<noteq> 0"
            then have d0_1: "j > 0" by simp
            from p2 have "compat_tran \<Gamma> c cs" by (simp add:conjoin_def)
            then have d1: "\<forall>j. Suc j < length c \<longrightarrow> 
                              (\<exists>t k. (\<Gamma> \<turnstile> c!j -pes-(t\<sharp>k)\<rightarrow> c!Suc j) \<and>
                              (\<forall>k t. (\<Gamma> \<turnstile> c!j -pes-(t\<sharp>k)\<rightarrow> c!Suc j) \<longrightarrow> (\<Gamma> \<turnstile> cs k!j -es-(t\<sharp>k)\<rightarrow> cs k! Suc j) \<and>
                                      (\<forall>k'. k' \<noteq> k \<longrightarrow> (\<Gamma> \<turnstile> cs k'!j -ese\<rightarrow> cs k'! Suc j))))
                              \<or>
                              ((\<Gamma> \<turnstile> (c!j) -pese\<rightarrow> (c!Suc j)) \<and> (\<forall>k. (\<Gamma> \<turnstile> ((cs k)!j) -ese\<rightarrow> ((cs k)! Suc j))))"
               by (simp add:compat_tran_def)
            from p3 p4 dd0 d0 have d2: "Suc (j-1) < length c" by auto
            with d0 d0_1 d1 have d3: "(\<exists>t k. (\<Gamma> \<turnstile> c!(j-1) -pes-(t\<sharp>k)\<rightarrow> c!Suc (j-1)) \<and>
                              (\<forall>k t. (\<Gamma> \<turnstile> c!(j-1) -pes-(t\<sharp>k)\<rightarrow> c!Suc (j-1)) \<longrightarrow> (\<Gamma> \<turnstile> cs k!(j-1) -es-(t\<sharp>k)\<rightarrow> cs k! Suc (j-1)) \<and>
                                      (\<forall>k'. k' \<noteq> k \<longrightarrow> (\<Gamma> \<turnstile> cs k'!(j-1) -ese\<rightarrow> cs k'! Suc (j-1)))))
                              \<or>
                              ((\<Gamma> \<turnstile> (c!(j-1)) -pese\<rightarrow> (c!Suc (j-1))) \<and> (\<forall>k. (\<Gamma> \<turnstile> ((cs k)!(j-1)) -ese\<rightarrow> ((cs k)!Suc (j-1)))))"
              by blast
            from p3 p4 d0 dd0 have d4: "c'!j = c!(j-1) \<and> c'!Suc j = c!Suc (j-1)" by simp
            have d5: "(\<forall>k. (?cs' k) ! j= (cs k)! (j-1)) \<and> (\<forall>k. (?cs' k) ! Suc j= (cs k)! Suc (j-1))" 
              by (simp add: d0_1) 
            with d3 d4 show ?thesis by auto
          qed
        
      }
      then show ?thesis by (simp add:compat_tran_def)
      qed
  qed

lemma cpt_imp_exist_conjoin_cs0: 
    "\<forall>c. c \<in> cpts_pes \<Gamma> \<longrightarrow>
                (\<exists>cs. (\<forall>k. (cs k) \<in> cpts_of_es \<Gamma> ((getspc (c!0)) k) (gets (c!0)) (getx (c!0))) \<and> \<Gamma> c \<propto> cs)"
  proof -
  {
    fix c
    assume p0: "c \<in> cpts_pes \<Gamma>"
    then have "\<exists>cs. (\<forall>k. (cs k) \<in> cpts_of_es \<Gamma> ((getspc (c!0)) k) (gets (c!0)) (getx (c!0))) \<and> \<Gamma> c \<propto> cs"
      proof(induct c)
        case (CptsPesOne pes1 s1 x1)
        let ?cs = "\<lambda>k. [(pes1 k, s1,x1)]" 
        let ?c = "[(pes1, s1, x1)]"
        have "\<forall>k. ?cs k \<in> cpts_of_es \<Gamma> (getspc (?c ! 0) k) (gets (?c ! 0)) (getx (?c ! 0))"
          proof -
          {
            fix k
            have "?cs k = [(pes1 k,s1,x1)]" by simp
            moreover
            have "?cs k \<in> cpts_es \<Gamma>" by (simp add: cpts_es.CptsEsOne) 
            ultimately have "?cs k \<in> cpts_of_es \<Gamma> (pes1 k) s1 x1" by (simp add: cpts_of_es_def)
          }
          then show ?thesis by (simp add: gets_def getspc_def getx_def) 
          qed
        moreover
        have "\<Gamma> ?c \<propto> ?cs"
          proof -
            have "same_length ?c ?cs" by (simp add: same_length_def) 
            moreover
            have "same_state ?c ?cs" using same_state_def gets_def gets_es_def getx_def getx_es_def
              by (smt length_Cons less_Suc0 list.size(3) nth_Cons_0 snd_conv) 
            moreover
            have "same_spec ?c ?cs" using same_spec_def getspc_def getspc_es_def
              by (metis (mono_tags, lifting) fst_conv length_Cons less_Suc0 list.size(3) nth_Cons_0)
            moreover
            have "compat_tran \<Gamma> ?c ?cs" by (simp add: compat_tran_def) 
            ultimately show ?thesis by (simp add:conjoin_def)
          qed
        ultimately show ?case by auto
      next
        case (CptsPesEnv pes1 t1 x1 xs s1 y1)
        let ?c = "(pes1, t1, x1) # xs"
        assume b0: "?c\<in> cpts_pes \<Gamma>"
          and  b1: "\<exists>cs. (\<forall>k. cs k \<in> cpts_of_es \<Gamma> (getspc (?c ! 0) k) (gets (?c ! 0))
                       (getx (?c ! 0))) \<and> \<Gamma> ?c \<propto> cs"
        then obtain cs where b2: "(\<forall>k. cs k \<in> cpts_of_es \<Gamma> (pes1 k) t1 x1) \<and> \<Gamma> ?c \<propto> cs" 
          using getspc_def gets_def getx_def by (metis fst_conv nth_Cons_0 snd_conv) 
        then have b3: "\<forall>k. cs k \<in> cpts_es \<Gamma> \<and> (cs k)!0 = (pes1 k,t1,x1)" by (simp add:cpts_of_es_def)
        let ?c' = "(pes1, s1, y1) # (pes1, t1, x1) # xs"
        let ?cs' = "\<lambda>k. (pes1 k,s1,y1)#(cs k)" 
        have g0: "\<forall>k. ?cs' k \<in> cpts_of_es \<Gamma> (getspc (?c' ! 0) k)  (gets (?c' ! 0)) (getx (?c' ! 0))" 
          proof -
          {
            fix k
            from b3 have c0: "cs k \<in>cpts_es \<Gamma> \<and> (cs k)!0 = (pes1 k,t1,x1)" by auto
            then obtain xs1 where "(cs k) = (pes1 k,t1,x1)#xs1"
              by (metis cpts_es_not_empty neq_Nil_conv nth_Cons_0) 
            with c0 have c1: "?cs' k \<in> cpts_es \<Gamma>" by (simp add: cpts_es.CptsEsEnv) 
            then have "?cs' k \<in> cpts_of_es \<Gamma> (getspc (?c' ! 0) k)  (gets (?c' ! 0)) (getx (?c' ! 0))" 
              by (simp add: cpts_of_es_def gets_def getspc_def getx_def) 
          }
          then show ?thesis by auto
          qed
        from b2 have b4: "\<Gamma> ?c \<propto> cs" by simp
        from b1 have g1: "\<Gamma> ?c' \<propto> ?cs'"
          proof -
            from b4 have "same_length ?c' ?cs'"
              by (simp add: conjoin_def same_length_def) 
            moreover
            have "same_state ?c' ?cs'"
              proof -
              {
                fix k' j
                assume c0: "j < length ?c'"
                have "gets (?c'!j) = gets_es ((?cs' k')!j) \<and> getx (?c'!j) = getx_es ((?cs' k')!j)"
                  proof(cases "j = 0")
                    assume d0: "j = 0"
                    then show ?thesis by (simp add:gets_def gets_es_def getx_def getx_es_def) 
                  next
                    assume d0: "j \<noteq> 0"
                    with b4 show ?thesis using same_state_def gets_def gets_es_def getx_def getx_es_def
                      using c0 conjoin_def length_Cons less_Suc_eq_0_disj nth_Cons_Suc by fastforce
                  qed
              }
              then show ?thesis by (simp add: same_state_def) 
              qed

            moreover 
            have "same_spec ?c' ?cs'"
              proof -
              {
                fix k' j
                assume c0: "j < length ?c'"
                have "(getspc (?c'!j)) k' = getspc_es ((?cs' k') ! j)"
                  proof(cases "j = 0")
                    assume d0: "j = 0"
                    then show ?thesis by (simp add:getspc_def getspc_es_def) 
                  next
                    assume d0: "j \<noteq> 0"
                    with b4 show ?thesis using same_spec_def getspc_def getspc_es_def
                      by (metis (no_types, lifting) Nat.le_diff_conv2 One_nat_def c0 conjoin_def 
                        less_Suc0 list.size(4) not_less nth_Cons')
                  qed
              }
              then show ?thesis by (simp add: same_spec_def) 
              qed
            moreover
            from b0 b2 b4 have "compat_tran \<Gamma> ?c' ?cs'" 
              using comp_tran_env [of cs \<Gamma> pes1 t1 x1 ?c xs ?c' s1 y1] by simp
            ultimately show ?thesis by (simp add:conjoin_def)
          qed
        from g0 g1 show ?case by auto
      next
        case (CptsPesComp pes1 s1 y1 ct pes2 t1 x1 xs)
        let ?c = "(pes2, t1, x1) # xs"
        assume b0: "?c\<in> cpts_pes \<Gamma>"
          and  b1: "\<exists>cs. (\<forall>k. cs k \<in> cpts_of_es \<Gamma> (getspc (?c ! 0) k) (gets (?c ! 0))
                       (getx (?c ! 0))) \<and> \<Gamma> ?c \<propto> cs"
          and  b00: "\<Gamma> \<turnstile> (pes1, s1, y1) -pes-ct\<rightarrow> (pes2, t1, x1)"
        then obtain cs where b2: "(\<forall>k. cs k \<in> cpts_of_es \<Gamma> (pes2 k) t1 x1) \<and> \<Gamma> ?c \<propto> cs" 
          using getspc_def gets_def getx_def by (metis fst_conv nth_Cons_0 snd_conv) 
        then have b3: "\<forall>k. cs k \<in> cpts_es \<Gamma> \<and> (cs k)!0 = (pes2 k,t1,x1)" by (simp add:cpts_of_es_def)
        let ?c' = "(pes1, s1, y1) # (pes2, t1, x1) # xs"
        let ?cs' = "\<lambda>k. (pes1 k,s1,y1)#(cs k)" 
        have g0: "\<forall>k. ?cs' k \<in> cpts_of_es \<Gamma> (getspc (?c' ! 0) k)  (gets (?c' ! 0)) (getx (?c' ! 0))" 
          proof -
          {
            fix k
            obtain ka and aa where c0: "ct = (aa\<sharp>ka)" using get_actk_def by (metis cases) 
            with b00 have "\<exists>es'. (\<Gamma> \<turnstile> (pes1 ka, s1, y1) -es-(aa\<sharp>ka)\<rightarrow> (es', t1, x1)) \<and> pes2 = pes1(ka:=es')" 
              using pestran_estran by auto
            then obtain es' where c1: "(\<Gamma> \<turnstile> (pes1 ka, s1, y1) -es-(aa\<sharp>ka)\<rightarrow> (es', t1, x1)) \<and> pes2 = pes1(ka:=es')"
              by auto
            from b3 have c2: "cs k \<in>cpts_es \<Gamma> \<and> (cs k)!0 = (pes2 k,t1,x1)" by auto
            then obtain xs1 where c4: "(cs k) = (pes2 k,t1,x1)#xs1"
              by (metis cpts_es_not_empty neq_Nil_conv nth_Cons_0) 
            then have c3: "?cs' k = (pes1 k, s1, y1) # (pes2 k,t1,x1)#xs1" by simp
            have "?cs' k \<in> cpts_of_es \<Gamma> (getspc (?c' ! 0) k)  (gets (?c' ! 0)) (getx (?c' ! 0))" 
              proof(cases "k = ka")
                assume d0: "k = ka"
                with c1 have "\<Gamma> \<turnstile> (pes1 k, s1, y1) -es-(aa\<sharp>k)\<rightarrow> (pes2 k, t1, x1)" by auto
                with c2 c3 d0 have "?cs' k \<in> cpts_es \<Gamma>"
                  using cpts_es.CptsEsComp by fastforce 
                then show ?thesis by (simp add: cpts_of_es_def gets_def getspc_def getx_def)
              next
                assume d0: "k \<noteq> ka"
                with c1 have "pes1 k = pes2 k" by simp
                with c2 c3 have d1: "?cs' k \<in> cpts_es \<Gamma>"
                  by (simp add: cpts_es.CptsEsEnv)  
                then show ?thesis by (simp add: cpts_of_es_def gets_def getspc_def getx_def) 
              qed
          }
          then show ?thesis by auto
          qed
        from b2 have b4: "\<Gamma> ?c \<propto> cs" by simp
        from b1 have g1: "\<Gamma> ?c' \<propto> ?cs'"
          proof -
            from b4 have "same_length ?c' ?cs'"
              by (simp add: conjoin_def same_length_def) 
            moreover
            have "same_state ?c' ?cs'"
              proof -
              {
                fix k' j
                assume c0: "j < length ?c'"
                have "gets (?c'!j) = gets_es ((?cs' k')!j) \<and> getx (?c'!j) = getx_es ((?cs' k')!j)"
                  proof(cases "j = 0")
                    assume d0: "j = 0"
                    then show ?thesis by (simp add:gets_def gets_es_def getx_def getx_es_def) 
                  next 
                    assume d0: "j \<noteq> 0"
                    with b4 show ?thesis using same_state_def gets_def gets_es_def getx_def getx_es_def
                      using c0 conjoin_def length_Cons less_Suc_eq_0_disj nth_Cons_Suc by fastforce
                  qed
              }
              then show ?thesis by (simp add: same_state_def) 
              qed

            moreover 
            have "same_spec ?c' ?cs'"
              proof -
              {
                fix k' j
                assume c0: "j < length ?c'"
                have "(getspc (?c'!j)) k' = getspc_es ((?cs' k') ! j)"
                  proof(cases "j = 0")
                    assume d0: "j = 0"
                    then show ?thesis by (simp add:getspc_def getspc_es_def) 
                  next
                    assume d0: "j \<noteq> 0"
                    with b4 show ?thesis using same_spec_def getspc_def getspc_es_def
                      by (metis (no_types, lifting) Nat.le_diff_conv2 One_nat_def Suc_leI c0 conjoin_def 
                        list.size(4) neq0_conv not_less nth_Cons')
                  qed
              }
              then show ?thesis by (simp add: same_spec_def) 
              qed
            moreover
            from b0 b00 b2 b4 have "compat_tran \<Gamma> ?c' ?cs'" 
              using comp_tran_pestran [of cs \<Gamma> pes2 t1 x1 ?c xs ?c' pes1 s1 y1 ct] by simp

            ultimately show ?thesis by (simp add:conjoin_def)
          qed
        from g0 g1 show ?case by auto
      qed
      
  }
  then show ?thesis by (metis (mono_tags, lifting)) 
  qed


lemma cpt_imp_exist_conjoin_cs: "c \<in> cpts_of_pes \<Gamma> pes s x
                \<Longrightarrow> \<exists>cs. (\<forall>k. (cs k) \<in> cpts_of_es \<Gamma> (pes k) s x) \<and> \<Gamma> c \<propto> cs"
  proof -
    assume p0: "c \<in> cpts_of_pes \<Gamma> pes s x"
    then have "c!0=(pes,s,x) \<and> c \<in> cpts_pes \<Gamma>" by (simp add:cpts_of_pes_def)
    then show ?thesis 
      using cpt_imp_exist_conjoin_cs0 getspc_def gets_def getx_def
        by (metis fst_conv snd_conv) 
  qed

theorem par_evtsys_semantics_comp: 
  "cpts_of_pes \<Gamma> pes s x = {c. \<exists>cs. (\<forall>k. (cs k) \<in> cpts_of_es \<Gamma> (pes k) s x) \<and> \<Gamma> c \<propto> cs}"
  proof -
    have "\<forall>c. c\<in>cpts_of_pes \<Gamma> pes s x \<longrightarrow> (\<exists>cs. (\<forall>k. (cs k) \<in> cpts_of_es \<Gamma> (pes k) s x) \<and> \<Gamma> c \<propto> cs)"
      proof -
      {
        fix c
        assume a0: "c\<in>cpts_of_pes \<Gamma> pes s x"
        then have "\<exists>cs. (\<forall>k. (cs k) \<in> cpts_of_es \<Gamma> (pes k) s x) \<and> \<Gamma> c \<propto> cs"
          using cpt_imp_exist_conjoin_cs cpts_of_pes_def getx_def mem_Collect_eq prod.sel(2) by fastforce 
      }
      then show ?thesis by auto
      qed
    moreover
    have "\<forall>c. (\<exists>cs. (\<forall>k. (cs k) \<in> cpts_of_es \<Gamma> (pes k) s x) \<and> \<Gamma> c \<propto> cs) \<longrightarrow> c\<in>cpts_of_pes \<Gamma> pes s x"
      proof -
      {
        fix c
        assume a0: "\<exists>cs. (\<forall>k. (cs k) \<in> cpts_of_es \<Gamma> (pes k) s x) \<and> \<Gamma> c \<propto> cs"
        then have "c\<in>cpts_of_pes \<Gamma> pes s x"
          using conjoin_cs_imp_cpt by fastforce 
      }
      then show ?thesis by auto
      qed
    ultimately show ?thesis by auto
  qed

end

end (*end of theory Computation*)