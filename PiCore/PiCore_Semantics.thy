section \<open>Small-step Operational Semantics of PiCore Language\<close>

theory PiCore_Semantics
imports PiCore_Language
begin

subsection \<open>Datatypes for Semantics\<close>

datatype cmd = CMP

datatype ('l,'k,'s,'prog) act = Cmd cmd      
    | EvtEnt "('l,'k,'s,'prog) event" 

record ('l,'k,'s,'prog) actk =  Act  :: "('l,'k,'s,'prog) act" 
                              K   :: "'k"

definition get_actk :: "('l,'k,'s,'prog) act \<Rightarrow> 'k \<Rightarrow> ('l,'k,'s,'prog) actk" ("_\<sharp>_" [91,91] 90)
  where "get_actk a k \<equiv> \<lparr>Act=a, K=k\<rparr>"

type_synonym ('l,'k,'s,'prog) x = "'k \<Rightarrow> ('l,'k,'s,'prog) event" 

type_synonym ('s,'prog) pconf = "'prog \<times> 's"

type_synonym ('s,'prog) pconfs = "('s,'prog) pconf list"

definition getspc_p :: "('s,'prog) pconf \<Rightarrow> 'prog" where
  "getspc_p conf \<equiv> fst conf"

definition gets_p :: "('s,'prog) pconf \<Rightarrow> 's" where
  "gets_p conf \<equiv> snd conf"

type_synonym ('l,'k,'s,'prog) econf = "(('l,'k,'s,'prog) event) \<times> ('s \<times> (('l,'k,'s,'prog) x) )"

type_synonym ('l,'k,'s,'prog) econfs = "('l,'k,'s,'prog) econf list"

definition getspc_e :: "('l,'k,'s,'prog) econf \<Rightarrow> ('l,'k,'s,'prog) event" where
  "getspc_e conf \<equiv> fst conf"

definition gets_e :: "('l,'k,'s,'prog) econf \<Rightarrow> 's" where
  "gets_e conf \<equiv> fst (snd conf)"

definition getx_e :: "('l,'k,'s,'prog) econf \<Rightarrow> ('l,'k,'s,'prog) x" where
  "getx_e conf \<equiv> snd (snd conf)"

type_synonym ('l,'k,'s,'prog) esconf = "(('l,'k,'s,'prog) esys) \<times> ('s \<times> (('l,'k,'s,'prog) x) )"

type_synonym ('l,'k,'s,'prog) esconfs = "('l,'k,'s,'prog) esconf list"


definition getspc_es :: "('l,'k,'s,'prog) esconf \<Rightarrow> ('l,'k,'s,'prog) esys" where
  "getspc_es conf \<equiv> fst conf"

definition gets_es :: "('l,'k,'s,'prog) esconf \<Rightarrow> 's" where
  "gets_es conf \<equiv> fst (snd conf)"

definition getx_es :: "('l,'k,'s,'prog) esconf \<Rightarrow> ('l,'k,'s,'prog) x" where
  "getx_es conf \<equiv> snd (snd conf)"

type_synonym ('l,'k,'s,'prog) pesconf = "(('l,'k,'s,'prog) paresys) \<times> ('s \<times> (('l,'k,'s,'prog) x) )"

type_synonym ('l,'k,'s,'prog) pesconfs = "('l,'k,'s,'prog) pesconf list"

definition getspc :: "('l,'k,'s,'prog) pesconf \<Rightarrow> ('l,'k,'s,'prog) paresys" where
  "getspc conf \<equiv> fst conf"

definition gets :: "('l,'k,'s,'prog) pesconf \<Rightarrow> 's" where
  "gets conf \<equiv> fst (snd conf)"

definition getx :: "('l,'k,'s,'prog) pesconf \<Rightarrow> ('l,'k,'s,'prog) x" where
  "getx conf \<equiv> snd (snd conf)"

definition getact :: "('l,'k,'s,'prog) actk \<Rightarrow> ('l,'k,'s,'prog) act" where
  "getact a \<equiv> Act a"

definition getk :: "('l,'k,'s,'prog) actk \<Rightarrow> 'k" where
  "getk a \<equiv> K a"


(* 'Env: type of context, such as procedures defined in a system *)
locale event =
fixes ptran :: "'Env \<Rightarrow> (('s,'prog) pconf \<times> ('s,'prog) pconf) set" 
fixes petran :: "'Env \<Rightarrow> ('s,'prog) pconf \<Rightarrow> ('s,'prog) pconf \<Rightarrow> bool"  ("_ \<turnstile> _ -pe\<rightarrow> _" [81,81,81] 80)
fixes fin_com :: "'prog" (* final command of imperative language, such as Skip in CSimpl and None in SIMP *)
(*assumes EnvP: "\<Gamma> \<turnstile> (P, s) -pe\<rightarrow> (P, t)" *)
assumes petran_simps:
    "\<Gamma> \<turnstile> (a, b) -pe\<rightarrow> (c, d) \<Longrightarrow> a = c"
assumes none_no_tran': "((fin_com, s),(P,t)) \<notin> ptran \<Gamma>"
assumes ptran_neq: "((P, s),(P,t)) \<notin> ptran \<Gamma>"
begin

definition ptran' :: "'Env \<Rightarrow> ('s,'prog) pconf \<Rightarrow> ('s,'prog) pconf \<Rightarrow> bool"   ("_ \<turnstile> _ -c\<rightarrow> _" [81,81] 80)
where "\<Gamma> \<turnstile> P -c\<rightarrow> Q \<equiv> (P,Q) \<in> ptran \<Gamma>"

definition ptrans :: "'Env \<Rightarrow> ('s,'prog) pconf \<Rightarrow> ('s,'prog) pconf \<Rightarrow> bool"   ("_ \<turnstile> _ -c*\<rightarrow> _" [81,81,81] 80)
where "\<Gamma> \<turnstile> P -c*\<rightarrow> Q \<equiv> (P,Q) \<in>(ptran \<Gamma>)^*" 

lemma none_no_tran: "\<not>(\<Gamma> \<turnstile> (fin_com,s) -c\<rightarrow> (P,t))"
  using none_no_tran' by(simp add:ptran'_def)

lemma none_no_tran2: "\<not>(\<Gamma> \<turnstile> (fin_com,s) -c\<rightarrow> Q)"
  using none_no_tran by (metis prod.collapse) 

lemma ptran_not_none: "(\<Gamma> \<turnstile> (Q,s) -c\<rightarrow> (P,t)) \<Longrightarrow> Q \<noteq> fin_com"
  using none_no_tran apply(simp add:ptran'_def) using not_None_eq by metis

subsection \<open>Semantics of Events\<close>

inductive etran ::  "'Env \<Rightarrow> ('l,'k,'s,'prog) econf \<Rightarrow> ('l,'k,'s,'prog) actk \<Rightarrow> ('l,'k,'s,'prog) econf \<Rightarrow> bool"   
("_ \<turnstile> _ -et-_\<rightarrow> _" [81,81,81] 80)
where
  AnonyEvent: "\<Gamma> \<turnstile> (P, s) -c\<rightarrow> (Q, t) \<Longrightarrow> \<Gamma> \<turnstile> (AnonyEvent P, s, x) -et-(Cmd CMP)\<sharp>k\<rightarrow> (AnonyEvent Q, t, x)"
| EventEntry: "\<lbrakk>P = body e; P \<noteq> fin_com; s \<in> guard e; x' = x(k:= BasicEvent e)\<rbrakk> 
                \<Longrightarrow> \<Gamma> \<turnstile> (BasicEvent e, s, x) -et-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> ((AnonyEvent P), s, x')"
(* we add P \<noteq> fin_com on 2019-01-31 *)

subsection \<open>Semantics of Event Systems\<close>

inductive estran :: "'Env \<Rightarrow> ('l,'k,'s,'prog) esconf \<Rightarrow> ('l,'k,'s,'prog) actk \<Rightarrow> ('l,'k,'s,'prog) esconf \<Rightarrow> bool"  
("_ \<turnstile> _ -es-_\<rightarrow> _" [81,81] 80)
where
  EvtOccur: "\<lbrakk>evt\<in> evts; \<Gamma> \<turnstile> (evt, (s, x)) -et-(EvtEnt evt)\<sharp>k\<rightarrow> (e, (s, x')) \<rbrakk> 
              \<Longrightarrow> \<Gamma> \<turnstile> (EvtSys evts, (s, x)) -es-(EvtEnt evt)\<sharp>k\<rightarrow> (EvtSeq e (EvtSys evts), (s, x'))"
| EvtSeq1:  "\<lbrakk>\<Gamma> \<turnstile> (e, s, x) -et-act\<sharp>k\<rightarrow>(e', s', x'); e' \<noteq> AnonyEvent fin_com\<rbrakk> 
              \<Longrightarrow> \<Gamma> \<turnstile> (EvtSeq e es, s, x) -es-act\<sharp>k\<rightarrow> (EvtSeq e' es, s', x')"
| EvtSeq2:  "\<lbrakk>\<Gamma> \<turnstile> (e, s, x) -et-act\<sharp>k\<rightarrow> (e', s', x'); e' = AnonyEvent fin_com\<rbrakk> 
              \<Longrightarrow> \<Gamma> \<turnstile> (EvtSeq e es, s, x) -es-act\<sharp>k\<rightarrow> (es, s', x')"

subsection \<open>Semantics of Parallel Event Systems\<close>

inductive
  pestran :: "'Env \<Rightarrow> ('l,'k,'s,'prog) pesconf \<Rightarrow> ('l,'k,'s,'prog) actk 
                      \<Rightarrow> ('l,'k,'s,'prog) pesconf \<Rightarrow> bool"  ("_ \<turnstile> _ -pes-_\<rightarrow> _" [70,70] 60)
where
  ParES:  "\<Gamma> \<turnstile> (pes(k), (s, x)) -es-(a\<sharp>k)\<rightarrow> (es', (s', x')) \<Longrightarrow> \<Gamma> \<turnstile> (pes, (s, x)) -pes-(a\<sharp>k)\<rightarrow> (pes(k:=es'), (s', x'))"

subsection \<open>Lemmas\<close>
subsubsection \<open>programs\<close>
lemma list_eq_if [rule_format]: 
  "\<forall>ys. xs=ys \<longrightarrow> (length xs = length ys) \<longrightarrow> (\<forall>i<length xs. xs!i=ys!i)"
  by (induct xs) auto

lemma list_eq: "(length xs = length ys \<and> (\<forall>i<length xs. xs!i=ys!i)) = (xs=ys)"
apply(rule iffI)
 apply clarify
 apply(erule nth_equalityI)
 apply simp+
done

lemma nth_tl: "\<lbrakk> ys!0=a; ys\<noteq>[] \<rbrakk> \<Longrightarrow> ys=(a#(tl ys))"
  by (cases ys) simp_all

lemma nth_tl_if [rule_format]: "ys\<noteq>[] \<longrightarrow> ys!0=a \<longrightarrow> P ys \<longrightarrow> P (a#(tl ys))"
  by (induct ys) simp_all

lemma nth_tl_onlyif [rule_format]: "ys\<noteq>[] \<longrightarrow> ys!0=a \<longrightarrow> P (a#(tl ys)) \<longrightarrow> P ys"
  by (induct ys) simp_all

lemma prog_not_eq_in_ctran_aux:
  assumes c: "\<Gamma> \<turnstile> (P,s) -c\<rightarrow> (Q,t)"
  shows "P\<noteq>Q" using c
  using ptran_neq apply(simp add:ptran'_def) apply auto
done

lemma prog_not_eq_in_ctran [simp]: "\<not> \<Gamma> \<turnstile> (P,s) -c\<rightarrow> (P,t)"
apply clarify using ptran_neq apply(simp add:ptran'_def)
done


subsubsection \<open>Events\<close>
lemma ent_spec1: "\<Gamma> \<turnstile> (ev, s, x) -et-(EvtEnt be)\<sharp>k\<rightarrow> (e2, s1, x1) \<Longrightarrow> ev = be" 
  apply(rule etran.cases)
  apply(simp)
  apply(simp add:get_actk_def)
  apply(simp add:get_actk_def)
  done

lemma ent_spec: "\<Gamma> \<turnstile> ec1 -et-(EvtEnt (BasicEvent ev))\<sharp>k\<rightarrow> ec2 \<Longrightarrow> getspc_e ec1 = BasicEvent ev"
  by (metis ent_spec1 getspc_e_def prod.collapse) 

lemma ent_spec2': "\<Gamma> \<turnstile> (ev, s, x) -et-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> (e2, s1, x1) 
                    \<Longrightarrow> s \<in> guard e \<and> s = s1
                                \<and> e2 = AnonyEvent ((body e)) \<and> x1 = x (k := BasicEvent e)"
  apply(rule etran.cases)
  apply(simp)
  apply(simp add:get_actk_def)+
  done

lemma ent_spec2: "\<Gamma> \<turnstile> ec1 -et-(EvtEnt (BasicEvent ev))\<sharp>k\<rightarrow> ec2 
                    \<Longrightarrow> gets_e ec1 \<in> guard ev \<and> gets_e ec1 = gets_e ec2
                                \<and> getspc_e ec2 = AnonyEvent ((body ev)) \<and> getx_e ec2 = (getx_e ec1) (k := BasicEvent ev)"
  using getspc_e_def getx_e_def gets_e_def ent_spec2' by (metis surjective_pairing) 

lemma no_tran2basic0: "\<Gamma> \<turnstile> (e1, s, x) -et-t\<rightarrow> (e2, s1, x1) \<Longrightarrow> \<not>(\<exists>e. e2 = BasicEvent e)"
  apply(rule etran.cases)
  apply(simp)+
  done

lemma no_tran2basic: "\<not>(\<exists>t ec1. \<Gamma> \<turnstile> ec1 -et-t\<rightarrow> (BasicEvent ev, s, x))"
  using no_tran2basic0 by (metis prod.collapse) 

lemma noevtent_notran0: "\<Gamma> \<turnstile> (BasicEvent e, s, x) -et-(a\<sharp>k)\<rightarrow> (e2, s1, x1) \<Longrightarrow> a = EvtEnt (BasicEvent e)"
  apply(rule etran.cases)
  apply(simp)+
  apply(simp add:get_actk_def)
  done

lemma noevtent_notran: "ec1 = (BasicEvent e, s, x) \<Longrightarrow> \<not> (\<exists>k. \<Gamma> \<turnstile> ec1 -et-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> ec2) 
                        \<Longrightarrow> \<not> (\<Gamma> \<turnstile> ec1 -et-t\<rightarrow> ec2)"
  proof -
    assume p0: "ec1 = (BasicEvent e, s, x)" and
           p1: "\<not> (\<exists>k. \<Gamma> \<turnstile> ec1 -et-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> ec2)"
    then show "\<not> (\<Gamma> \<turnstile> ec1 -et-t\<rightarrow> ec2)"
      proof -
      {
        assume a0: "\<Gamma> \<turnstile> ec1 -et-t\<rightarrow> ec2"
        with p0 have a1: "getact t = EvtEnt (BasicEvent e)"  using getact_def noevtent_notran0 get_actk_def
          by (metis cases prod_cases3 select_convs(1))
        from a0 obtain k where "k = getk t" by auto
        with p1 a0 a1 have "\<Gamma> \<turnstile> ec1 -et-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> ec2" using get_actk_def getact_def 
          by (metis cases select_convs(1))
        with p1 have False by auto
      }
      then show ?thesis by auto
      qed
  qed


lemma evt_not_eq_in_tran_aux:"\<Gamma> \<turnstile> (P,s,x) -et-et\<rightarrow> (Q,t,y) \<Longrightarrow> P \<noteq> Q"
  apply(erule etran.cases)
  apply (simp add: prog_not_eq_in_ctran_aux)
  by simp


lemma evt_not_eq_in_tran [simp]: "\<not> \<Gamma> \<turnstile> (P,s,x) -et-et\<rightarrow> (P,t,y)"
apply clarify
apply(drule evt_not_eq_in_tran_aux)
apply simp
done

lemma evt_not_eq_in_tran2 [simp]: "\<not>(\<exists>et. \<Gamma> \<turnstile> (P,s,x) -et-et\<rightarrow> (P,t,y))" by simp


subsubsection \<open>Event Systems\<close>

lemma esconf_trip: "\<lbrakk>gets_es c = s; getspc_es c = spc; getx_es c = x\<rbrakk> \<Longrightarrow> c = (spc,s,x)"
  by (metis gets_es_def getspc_es_def getx_es_def prod.collapse)

lemma evtseq_tran_evtseq: 
  "\<lbrakk>\<Gamma> \<turnstile> (EvtSeq e1 es, s1, x1) -es-et\<rightarrow> (es2, t1, y1); es2 \<noteq> es\<rbrakk> \<Longrightarrow> \<exists>e. es2 = EvtSeq e es"
  apply(rule estran.cases)
  apply(simp)+
  done

lemma evtseq_tran_evtseq_anony: 
  "\<lbrakk>\<Gamma> \<turnstile> (EvtSeq e1 es, s1, x1) -es-et\<rightarrow> (es2, t1, y1); es2 \<noteq> es\<rbrakk> \<Longrightarrow> \<exists>e. es2 = EvtSeq e es \<and> is_anonyevt e"
  apply(rule estran.cases)
  apply(simp)+
  apply (metis event.exhaust is_anonyevt.simps(1) no_tran2basic0)
  by simp 

lemma evtseq_tran_evtsys: 
  "\<lbrakk>\<Gamma> \<turnstile> (EvtSeq e1 es, s1, x1) -es-et\<rightarrow> (es2, t1, y1); \<not>(\<exists>e. es2 = EvtSeq e es)\<rbrakk> \<Longrightarrow> es2 = es"
  apply(rule estran.cases)
  apply(simp)+
  done

lemma evtseq_tran_exist_etran: 
  "\<Gamma> \<turnstile> (EvtSeq e1 es, s1, x1) -es-et\<rightarrow> (EvtSeq e2 es, t1, y1) \<Longrightarrow> \<exists>t. \<Gamma> \<turnstile> (e1, s1, x1) -et-t\<rightarrow> (e2, t1, y1)"
  apply(rule estran.cases)
  apply(simp)+
  apply blast
  by (simp add: evtseq_ne_es)

lemma evtseq_tran_0_exist_etran: 
  "\<Gamma> \<turnstile> (EvtSeq e1 es, s1, x1) -es-et\<rightarrow> (es, t1, y1) \<Longrightarrow> \<exists>t. \<Gamma> \<turnstile> (e1, s1, x1) -et-t\<rightarrow> (AnonyEvent fin_com, t1, y1)"
  apply(rule estran.cases)
  apply(simp)+
  apply (metis (no_types, hide_lams) add.commute add_Suc_right esys.size(3) not_less_eq trans_less_add2)
  by auto
  

lemma notrans_to_basicevt_insameesys: 
  "\<lbrakk>\<Gamma> \<turnstile> (es1, s1, x1) -es-et\<rightarrow> (es2, s2, x2); \<exists>e. es1 = EvtSeq e esys\<rbrakk> \<Longrightarrow> \<not>(\<exists>e. es2 = EvtSeq (BasicEvent e) esys)"
  apply(rule estran.cases)
  apply simp
  apply(rule etran.cases)
  apply (simp add: get_actk_def)+
  apply(rule etran.cases)
  apply (simp add: get_actk_def)+
  by (metis evtseq_tran_exist_etran no_tran2basic)
  
lemma evtseq_tran_sys_or_seq:
  "\<Gamma> \<turnstile> (EvtSeq e1 es, s1, x1) -es-et\<rightarrow> (es2, t1, y1) \<Longrightarrow> es2 = es \<or> (\<exists>e. es2 = EvtSeq e es)"
  by (meson evtseq_tran_evtseq)

lemma evtseq_tran_sys_or_seq_anony:
  "\<Gamma> \<turnstile> (EvtSeq e1 es, s1, x1) -es-et\<rightarrow> (es2, t1, y1) \<Longrightarrow> es2 = es \<or> (\<exists>e. es2 = EvtSeq e es \<and> is_anonyevt e)"
  by (meson evtseq_tran_evtseq_anony)

lemma evtseq_no_evtent:
  "\<lbrakk>\<Gamma> \<turnstile> (EvtSeq e1 es, s1, x1) -es-t\<sharp>k\<rightarrow> (es2, s2, x2);is_anonyevt e1\<rbrakk> \<Longrightarrow> \<not>(\<exists>e. t = EvtEnt e)"
  apply(rule estran.cases)
  apply(simp)+
  apply(rule etran.cases)
  apply(simp add:get_actk_def)+
  apply(rule etran.cases)
  apply(simp add:get_actk_def)+
  done

lemma evtseq_no_evtent2:
  "\<lbrakk>\<Gamma> \<turnstile> esc1 -es-t\<sharp>k\<rightarrow> esc2; getspc_es esc1 = EvtSeq e esys; is_anonyevt e\<rbrakk> \<Longrightarrow> \<not>(\<exists>e. t = EvtEnt e)"
  proof -
    assume p0: "\<Gamma> \<turnstile> esc1 -es-t\<sharp>k\<rightarrow> esc2"
      and  p1: "getspc_es esc1 = EvtSeq e esys"
      and  p2: "is_anonyevt e"
    then obtain es1 and s1 and x1 where a1: "esc1 = (es1,s1,x1)"
      using prod_cases3 by blast 
    from p0 obtain es2 and s2 and x2 where a2: "esc2 = (es2,s2,x2)"
      using prod_cases3 by blast 
    from p1 a1 have "es1 = EvtSeq e esys" by (simp add:getspc_es_def)
    with p0 p2 a1 a2 show ?thesis using evtseq_no_evtent[of \<Gamma> e esys s1 x1 t k es2 s2 x2]
      by simp
  qed

lemma esys_not_eseq: "getspc_es esc = EvtSys es \<Longrightarrow> \<not>(\<exists>e esys. getspc_es esc = EvtSeq e esys)"
  by(simp add:getspc_es_def)
  
lemma eseq_not_esys: "getspc_es esc = EvtSeq e esys \<Longrightarrow> \<not>(\<exists>es. getspc_es esc = EvtSys es)"
  by(simp add:getspc_es_def)

lemma evtent_is_basicevt: "\<Gamma> \<turnstile> (es, s, x) -es-EvtEnt e\<sharp>k\<rightarrow> (es', s', x') \<Longrightarrow> \<exists>e'. e = BasicEvent e'"
  apply(rule estran.cases)
  apply(simp add:get_actk_def)+
  apply(rule etran.cases)
  apply(simp add:get_actk_def)+
  apply(rule etran.cases)
  apply simp+
  apply(rule etran.cases)
  apply simp+
  apply auto[1]
  apply (metis ent_spec1 event.exhaust evtseq_no_evtent get_actk_def is_anonyevt.simps(1))+  
  done
  
lemma evtent_is_basicevt_inevtseq: "\<lbrakk>\<Gamma> \<turnstile> (EvtSeq e es,s1,x1) -es-EvtEnt e1\<sharp>k\<rightarrow> (esc2,s2,x2)\<rbrakk> 
    \<Longrightarrow> e = e1 \<and> (\<exists>e'. e = BasicEvent e')"
  apply(rule estran.cases)
  apply(simp add:get_actk_def)
  apply(rule etran.cases)
  apply(simp add:get_actk_def)+
  apply(rule etran.cases)
  apply(simp add:get_actk_def)+
  apply(rule etran.cases)
  apply(simp add:get_actk_def)
  apply(simp add:get_actk_def)
  apply auto[1]
  by (metis Pair_inject ent_spec1 esys.inject(1) evtent_is_basicevt get_actk_def)
  
lemma evtent_is_basicevt_inevtseq2: "\<lbrakk>\<Gamma> \<turnstile> esc1 -es-EvtEnt e1\<sharp>k\<rightarrow> esc2; getspc_es esc1 = EvtSeq e es\<rbrakk> 
    \<Longrightarrow> e = e1 \<and> (\<exists>e'. e = BasicEvent e')"
  proof -
    assume p0: "\<Gamma> \<turnstile> esc1 -es-EvtEnt e1\<sharp>k\<rightarrow> esc2"
      and  p1: "getspc_es esc1 = EvtSeq e es"
    then obtain es1 and s1 and x1 where a0: "esc1 = (es1,s1,x1)"
      using prod_cases3 by blast 
    moreover
    from p0 obtain es2 and s2 and x2 where a1: "esc2 = (es2,s2,x2)"
      using prod_cases3 by blast 
    ultimately show ?thesis 
      using p0 p1 evtent_is_basicevt_inevtseq[of \<Gamma> e es s1 x1 e1 k es2 s2 x2] getspc_es_def[of esc1] by auto
  qed

lemma evtsysent_evtent0: "\<Gamma> \<turnstile> (EvtSys es, s, x) -es-t\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1) \<Longrightarrow>
        s = s1 \<and> (\<exists>evt e. evt \<in> es \<and> evt = BasicEvent e \<and> Act t = EvtEnt (BasicEvent e) \<and>
            \<Gamma> \<turnstile> (BasicEvent e, s, x) -et-t\<rightarrow> (ev, s1, x1))"
  apply(rule estran.cases)
  apply(simp)
  prefer 2
  apply(simp)
  prefer 2
  apply(simp)
  apply(rule etran.cases)
  apply(simp)
  apply(simp add:get_actk_def)
  apply(rule conjI)
  apply(simp)
  using get_actk_def
  by (metis Pair_inject esys.inject(1) esys.inject(2) select_convs(1))

lemma evtsysent_evtent: "\<Gamma> \<turnstile> (EvtSys es, s, x) -es-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> (EvtSeq ev (EvtSys es), s1,x1) \<Longrightarrow>
        s = s1 \<and> BasicEvent e \<in> es \<and> \<Gamma> \<turnstile> (BasicEvent e, s, x) -et-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> (ev, s1, x1)"
  apply(rule estran.cases)
  apply(simp)+
  apply (metis ent_spec1)
  apply(simp)+
  done

lemma evtsysent_evtent2: "\<Gamma> \<turnstile> (EvtSys es, s, x) -es-(EvtEnt ev)\<sharp>k\<rightarrow> (esc2, s1,x1) \<Longrightarrow>
        s = s1 \<and> (ev\<in>es)"
  apply(rule estran.cases)
  apply(simp)+
  apply (metis ent_spec1)
  apply(simp)+
  done

lemma evtsysent_evtent3: "\<lbrakk>\<Gamma> \<turnstile> esc1 -es-(EvtEnt ev)\<sharp>k\<rightarrow> esc2; getspc_es esc1 = EvtSys es\<rbrakk> \<Longrightarrow>
        (ev\<in>es)"
  proof -
    assume p0: "\<Gamma> \<turnstile> esc1 -es-(EvtEnt ev)\<sharp>k\<rightarrow> esc2"
      and  p1: "getspc_es esc1 = EvtSys es"
    then obtain es1 and s1 and x1 where a0: "esc1 = (es1,s1,x1)"
      using prod_cases3 by blast 
    moreover
    from p0 obtain es2 and s2 and x2 where a1: "esc2 = (es2,s2,x2)"
      using prod_cases3 by blast 
    from p1 a0 have "es1 = EvtSys es" by (simp add:getspc_es_def)
    with a0 a1 p0 show ?thesis using evtsysent_evtent2[of \<Gamma> es s1 x1 ev k es2 s2 x2] by simp
  qed


lemma evtsys_evtent: "\<Gamma> \<turnstile> (EvtSys es, s, x) -es-t\<rightarrow> (es2, s1,x1) \<Longrightarrow> \<exists>e. es2 = EvtSeq e (EvtSys es)"
  apply(rule estran.cases)
  apply(simp)+
  done

lemma act_in_es_notchgstate: "\<lbrakk>\<Gamma> \<turnstile> (es, s, x) -es-(Cmd c)\<sharp>k\<rightarrow> (es', s', x')\<rbrakk> \<Longrightarrow> x = x'"
  apply(rule estran.cases)
  apply (simp add: get_actk_def)+
  apply(rule etran.cases)
  apply (simp add: get_actk_def)+
  apply(rule etran.cases)
  by (simp add: get_actk_def)+

lemma cmd_enable_impl_anonyevt: 
    "\<lbrakk>\<Gamma> \<turnstile> (es, s, x) -es-(Cmd c)\<sharp>k\<rightarrow> (es', s', x')\<rbrakk> 
        \<Longrightarrow> \<exists>e e' es1. es = EvtSeq e es1 \<and> e = AnonyEvent e'"
  apply(rule estran.cases)
  apply (simp add: get_actk_def)+
  apply(rule etran.cases)
  apply (simp add: get_actk_def)+
  apply(rule etran.cases)
  apply (simp add: get_actk_def)+
  done

lemma cmd_enable_impl_notesys: 
    "\<lbrakk>\<Gamma> \<turnstile> (es, s, x) -es-(Cmd c)\<sharp>k\<rightarrow> (es', s', x')\<rbrakk> 
        \<Longrightarrow> \<not>(\<exists>ess. es = EvtSys ess)"
  apply(rule estran.cases)
  apply (simp add: get_actk_def)+
  done

lemma cmd_enable_impl_notesys2: 
    "\<lbrakk>\<Gamma> \<turnstile> esc1 -es-(Cmd c)\<sharp>k\<rightarrow> esc2\<rbrakk> 
        \<Longrightarrow> \<not>(\<exists>ess. getspc_es esc1 = EvtSys ess)"
  proof -
    assume p0: "\<Gamma> \<turnstile> esc1 -es-(Cmd c)\<sharp>k\<rightarrow> esc2"
    then obtain es1 and s1 and x1 where a0: "esc1 = (es1,s1,x1)"
      using prod_cases3 by blast 
    moreover
    from p0 obtain es2 and s2 and x2 where a1: "esc2 = (es2,s2,x2)"
      using prod_cases3 by blast 
    ultimately show ?thesis using p0 cmd_enable_impl_notesys[of \<Gamma> es1 s1 x1 c k es2 s2 x2] getspc_es_def[of esc1]
      by simp
  qed

lemma cmd_enable_impl_anonyevt2: 
    "\<lbrakk>\<Gamma> \<turnstile> esc1 -es-(Cmd c)\<sharp>k\<rightarrow> esc2\<rbrakk> 
        \<Longrightarrow> \<exists>e e' es1. getspc_es esc1 = EvtSeq e es1 \<and> e = AnonyEvent e'"
  proof -
    assume p0: "\<Gamma> \<turnstile> esc1 -es-(Cmd c)\<sharp>k\<rightarrow> esc2"
    then obtain es1 and s1 and x1 where a0: "esc1 = (es1,s1,x1)"
      using prod_cases3 by blast 
    moreover
    from p0 obtain es2 and s2 and x2 where a1: "esc2 = (es2,s2,x2)"
      using prod_cases3 by blast 
    ultimately show ?thesis using p0 cmd_enable_impl_anonyevt[of \<Gamma> es1 s1 x1 c k es2 s2 x2] getspc_es_def[of esc1]
      by simp
  qed

lemma entevt_notchgstate: "\<lbrakk>\<Gamma> \<turnstile> (es, s, x) -es-(EvtEnt (BasicEvent e))\<sharp>k\<rightarrow> (es', s', x')\<rbrakk> \<Longrightarrow> s = s'"
  apply(rule estran.cases)
  apply(simp)+
  apply(rule etran.cases)
  apply (simp add: get_actk_def)+
  apply auto
  using ent_spec2' get_actk_def by metis 

lemma entevt_ines_notchg_otherx: "\<lbrakk>\<Gamma> \<turnstile> (es, s, x) -es-(EvtEnt e)\<sharp>k\<rightarrow> (es', s', x')\<rbrakk> \<Longrightarrow> (\<forall>k'. k'\<noteq>k \<longrightarrow> x k' = x' k')"
  apply(rule estran.cases)
  apply(simp)+
  apply(rule etran.cases)
  apply (simp add: get_actk_def)+
  apply(rule etran.cases)
  apply (simp add: get_actk_def)+
  apply(rule etran.cases)
  apply (simp add: get_actk_def)+
  done

lemma entevt_ines_notchg_otherx2: "\<lbrakk>\<Gamma> \<turnstile> esc1 -es-(EvtEnt e)\<sharp>k\<rightarrow> esc2\<rbrakk> 
          \<Longrightarrow> (\<forall>k'. k'\<noteq>k \<longrightarrow> (getx_es esc1) k' = (getx_es esc2) k')"
  proof -
    assume p0: "\<Gamma> \<turnstile> esc1 -es-(EvtEnt e)\<sharp>k\<rightarrow> esc2"
    then obtain es1 and s1 and x1 where a0: "esc1 = (es1,s1,x1)"
      using prod_cases3 by blast 
    moreover
    from p0 obtain es2 and s2 and x2 where a1: "esc2 = (es2,s2,x2)"
      using prod_cases3 by blast 
    ultimately have "\<forall>k'. k'\<noteq>k \<longrightarrow> x1 k' = x2 k'" 
      using entevt_ines_notchg_otherx[of \<Gamma> es1 s1 x1 e k es2 s2 x2] p0 by simp
    with a0 a1 show ?thesis using getx_es_def by (metis snd_conv) 
  qed

lemma cmd_ines_nchg_x: "\<lbrakk>\<Gamma> \<turnstile> (es, s, x) -es-(Cmd c)\<sharp>k\<rightarrow> (es', s', x')\<rbrakk> \<Longrightarrow> (\<forall>k. x' k = x k)"
  apply(rule estran.cases)
  apply(simp)+
  apply(rule etran.cases)
  apply (simp add: get_actk_def)+
  apply(rule etran.cases)
  apply (simp add: get_actk_def)+ 
  apply(rule etran.cases)
  apply (simp add: get_actk_def)+
  done

lemma cmd_ines_nchg_x2: "\<lbrakk>\<Gamma> \<turnstile> esc1 -es-(Cmd c)\<sharp>k\<rightarrow> esc2\<rbrakk> \<Longrightarrow> (\<forall>k. (getx_es esc2) k = (getx_es esc1) k)" 
  proof -
    assume p0: "\<Gamma> \<turnstile> esc1 -es-(Cmd c)\<sharp>k\<rightarrow> esc2"
    then obtain es1 and s1 and x1 where a0: "esc1 = (es1,s1,x1)"
      using prod_cases3 by blast 
    moreover
    from p0 obtain es2 and s2 and x2 where a1: "esc2 = (es2,s2,x2)"
      using prod_cases3 by blast 
    ultimately have "\<forall>k. x1 k = x2 k" using cmd_ines_nchg_x [of \<Gamma> es1 s1 x1 c k es2 s2 x2] p0 by simp
    with a0 a1 show ?thesis using getx_es_def by (metis snd_conv) 
  qed

lemma entevt_ines_chg_selfx: "\<lbrakk>\<Gamma> \<turnstile> (es, s, x) -es-(EvtEnt e)\<sharp>k\<rightarrow> (es', s', x')\<rbrakk> \<Longrightarrow> x' k = e"
  apply(rule estran.cases)
  apply(simp)+
  apply(rule etran.cases)
  apply (simp add: get_actk_def)+
  apply(rule etran.cases)
  apply (simp add: get_actk_def)+
  apply(rule etran.cases)
  apply (simp add: get_actk_def)+
  done

lemma entevt_ines_chg_selfx2: "\<lbrakk>\<Gamma> \<turnstile> esc1 -es-(EvtEnt e)\<sharp>k\<rightarrow> esc2\<rbrakk> \<Longrightarrow> (getx_es esc2) k = e" 
  proof -
    assume p0: "\<Gamma> \<turnstile> esc1 -es-(EvtEnt e)\<sharp>k\<rightarrow> esc2"
    then obtain es1 and s1 and x1 where a0: "esc1 = (es1,s1,x1)"
      using prod_cases3 by blast 
    moreover
    from p0 obtain es2 and s2 and x2 where a1: "esc2 = (es2,s2,x2)"
      using prod_cases3 by blast 
    ultimately have "x2 k = e" using entevt_ines_chg_selfx p0 by auto
    with a1 show ?thesis using getx_es_def by (metis snd_conv) 
  qed

lemma estran_impl_evtentorcmd: "\<lbrakk>\<Gamma> \<turnstile> (es, s, x) -es-t\<rightarrow> (es', s', x')\<rbrakk> 
  \<Longrightarrow> (\<exists>e k. \<Gamma> \<turnstile> (es, s, x) -es-EvtEnt e\<sharp>k\<rightarrow> (es', s', x')) \<or> (\<exists>c k. \<Gamma> \<turnstile> (es, s, x) -es-Cmd c\<sharp>k\<rightarrow> (es', s', x'))" 
  apply(rule estran.cases)
    apply (simp add: get_actk_def)
    apply(rule etran.cases)
      apply (simp add: get_actk_def)+
      apply auto[1]
    apply(rule etran.cases)
      apply (simp add: get_actk_def)+
      apply auto[1]
      apply (metis get_actk_def)
    apply(rule etran.cases)
      apply (simp add: get_actk_def) 
      apply (metis get_actk_def) 
      apply (metis get_actk_def)
  done

lemma estran_impl_evtentorcmd': "\<lbrakk>\<Gamma> \<turnstile> (es, s, x) -es-t\<sharp>k\<rightarrow> (es', s', x')\<rbrakk> 
  \<Longrightarrow> (\<exists>e. \<Gamma> \<turnstile> (es, s, x) -es-EvtEnt e\<sharp>k\<rightarrow> (es', s', x')) \<or> (\<exists>c. \<Gamma> \<turnstile> (es, s, x) -es-Cmd c\<sharp>k\<rightarrow> (es', s', x'))" 
  apply(rule estran.cases)
  apply simp
  apply (metis get_actk_def iffs)
  apply(rule etran.cases)
  apply simp
  apply (metis get_actk_def iffs)
  apply (metis get_actk_def iffs)
  apply(rule etran.cases)
  apply simp
  apply (metis get_actk_def iffs)
  apply (metis get_actk_def iffs)
  done

lemma estran_impl_evtentorcmd2: "\<lbrakk>\<Gamma> \<turnstile> esc1 -es-t\<rightarrow> esc2\<rbrakk> 
  \<Longrightarrow> (\<exists>e k. \<Gamma> \<turnstile> esc1 -es-EvtEnt e\<sharp>k\<rightarrow> esc2) \<or> (\<exists>c k. \<Gamma> \<turnstile> esc1 -es-Cmd c\<sharp>k\<rightarrow> esc2)" 
  proof -
    assume p0: "\<Gamma> \<turnstile> esc1 -es-t\<rightarrow> esc2"
    then obtain es1 and s1 and x1 where a0: "esc1 = (es1,s1,x1)"
      using prod_cases3 by blast 
    moreover
    from p0 obtain es2 and s2 and x2 where a1: "esc2 = (es2,s2,x2)"
      using prod_cases3 by blast 
    ultimately show ?thesis using p0 estran_impl_evtentorcmd[of \<Gamma> es1 s1 x1 t es2 s2 x2] by simp 
  qed

lemma estran_impl_evtentorcmd2': "\<lbrakk>\<Gamma> \<turnstile> esc1 -es-t\<sharp>k\<rightarrow> esc2\<rbrakk> 
  \<Longrightarrow> (\<exists>e. \<Gamma> \<turnstile> esc1 -es-EvtEnt e\<sharp>k\<rightarrow> esc2) \<or> (\<exists>c. \<Gamma> \<turnstile> esc1 -es-Cmd c\<sharp>k\<rightarrow> esc2)" 
  proof -
    assume p0: "\<Gamma> \<turnstile> esc1 -es-t\<sharp>k\<rightarrow> esc2"
    then obtain es1 and s1 and x1 where a0: "esc1 = (es1,s1,x1)"
      using prod_cases3 by blast 
    moreover
    from p0 obtain es2 and s2 and x2 where a1: "esc2 = (es2,s2,x2)"
      using prod_cases3 by blast 
    ultimately show ?thesis using p0 estran_impl_evtentorcmd'[of \<Gamma> es1 s1 x1 t k es2 s2 x2] by simp 
  qed

  
subsubsection \<open>Parallel Event Systems\<close>

lemma pesconf_trip: "\<lbrakk>gets c = s; getspc c = spc; getx c = x\<rbrakk> \<Longrightarrow> c = (spc,s,x)"
  by (metis gets_def getspc_def getx_def prod.collapse)

lemma pestran_estran: "\<lbrakk>\<Gamma> \<turnstile> (pes, s, x) -pes-(a\<sharp>k)\<rightarrow> (pes', s', x')\<rbrakk> \<Longrightarrow> 
              \<exists>es'. (\<Gamma> \<turnstile> (pes k, s, x) -es-(a\<sharp>k)\<rightarrow> (es', s', x')) \<and> pes' = pes(k:=es')"
  apply(rule pestran.cases)
  apply(simp)
  apply(simp add:get_actk_def)
  by auto

lemma act_in_pes_notchgstate: "\<lbrakk>\<Gamma> \<turnstile> (pes, s, x) -pes-(Cmd c)\<sharp>k\<rightarrow> (pes', s', x')\<rbrakk> \<Longrightarrow> x = x'"
  apply(rule pestran.cases)
  apply (simp add: get_actk_def)+
  apply(rule estran.cases)
  apply (simp add: get_actk_def)+
  apply(rule etran.cases)
  apply (simp add: get_actk_def)+
  apply(rule etran.cases)
  apply (simp add: get_actk_def)+
  done

lemma evtent_in_pes_notchgstate: "\<lbrakk>\<Gamma> \<turnstile> (pes, s, x) -pes-(EvtEnt e)\<sharp>k\<rightarrow> (pes', s', x')\<rbrakk> \<Longrightarrow> s = s'"
  apply(rule pestran.cases)
  apply (simp add: get_actk_def)+
  apply(rule estran.cases)
  apply (simp add: get_actk_def)+
  apply (metis entevt_notchgstate evtent_is_basicevt get_actk_def)
  by (metis entevt_notchgstate evtent_is_basicevt get_actk_def)
  
lemma evtent_in_pes_notchgstate2: "\<lbrakk>\<Gamma> \<turnstile> esc1 -pes-(EvtEnt e)\<sharp>k\<rightarrow> esc2\<rbrakk> \<Longrightarrow> gets esc1 = gets esc2"
  using evtent_in_pes_notchgstate by (metis pesconf_trip) 

end

end