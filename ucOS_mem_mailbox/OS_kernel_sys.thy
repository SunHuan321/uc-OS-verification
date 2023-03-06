theory OS_kernel_sys
  imports func_cor_other func_cor_OSMemGet func_cor_OSMemPut func_cor_OSMboxPend 
          func_cor_OSMboxAccept func_cor_OSMboxPost
begin

section \<open> formal specification of ucOS memory management \<close>

definition OSMemGet_RGF :: "Thread \<Rightarrow> OS_MEM_ref \<Rightarrow> (EventLabel, Core, State, State com option) rgformula_e"
  where "OSMemGet_RGF t p 
  \<equiv> (OSMemGet t p, OSMemGet_RGCond t)"

definition OSMemPut_RGF :: "Thread \<Rightarrow> OS_MEM_ref \<Rightarrow> mem_ref  \<Rightarrow> 
                            (EventLabel, Core, State, State com option) rgformula_e"
  where "OSMemPut_RGF t p b \<equiv> (OSMemPut t p b,OSMemPut_RGCond t)"

definition OSMboxPend_RGF :: "Thread \<Rightarrow>  mailbox_ref \<Rightarrow> int \<Rightarrow> 
                              (EventLabel, Core, State, State com option) rgformula_e"
  where "OSMboxPend_RGF t pevent timeout  \<equiv> (OSMboxPend t pevent timeout, OSMboxPend_RGCond t)"

definition OSMboxPost_RGF :: "Thread \<Rightarrow> mailbox_ref \<Rightarrow> Message option \<Rightarrow> 
                              (EventLabel, Core, State, State com option) rgformula_e"
where "OSMboxPost_RGF t pevent msg  \<equiv> (OSMboxPost t pevent msg, OSMboxPost_RGCond t)"

definition OSMboxAccept_RGF :: "Thread \<Rightarrow> mailbox_ref \<Rightarrow>  
                                (EventLabel, Core, State, State com option) rgformula_e"
 where "OSMboxAccept_RGF t pevent \<equiv> (OSMboxAccept t pevent, OSMboxAccept_RGCond t)"

definition Schedule_RGF :: "Thread \<Rightarrow> (EventLabel, Core, State, State com option) rgformula_e"
where "Schedule_RGF t \<equiv> (Schedule t, Schedule_RGCond t)"

definition Tick_RGF :: "(EventLabel, Core, State, State com option) rgformula_e"
  where "Tick_RGF \<equiv> (Tick, Tick_RGCond)"

definition Thread_RGF :: "Thread \<Rightarrow> (EventLabel, Core, State, State com option) rgformula_es"
  where "Thread_RGF t \<equiv>  (rgf_EvtSys ((\<Union>p. {OSMemGet_RGF t p}) \<union> (\<Union>(p1,b) . {OSMemPut_RGF t p1 b})
  \<union> (\<Union>(pevent, timeout).{OSMboxPend_RGF t pevent timeout}) \<union> (\<Union>(pevent, msg).
  {OSMboxPost_RGF t pevent msg}) \<union> (\<Union>(pevent). {OSMboxAccept_RGF t pevent})),
          RG[(OSMemPut_pre t \<inter> OSMemGet_pre t \<inter> OSMboxPost_pre t \<inter> OSMboxAccept_pre t \<inter> OSMboxPend_pre t),
             (OSMemPut_rely t \<inter> OSMemGet_rely t \<inter> OSMboxPost_rely t \<inter> OSMboxAccept_rely t \<inter> OSMboxPend_rely t),
             (OSMemPut_guar t \<union> OSMemPut_guar t \<union> OSMboxPost_guar t \<union> OSMboxAccept_guar t \<union> OSMboxPend_guar t),
             (OSMemPut_post t \<union>  OSMemGet_post t \<union> OSMboxPost_post t \<union> OSMboxAccept_post t \<union> OSMboxPend_post t)])"

definition Timer_RGF :: "(EventLabel, Core, State, State com option) rgformula_es"
where "Timer_RGF \<equiv>  (rgf_EvtSys {Tick_RGF},
         RG[\<lbrace>True\<rbrace>, Tick_rely, Tick_guar, \<lbrace>True\<rbrace>])"

definition Scheduler_RGF :: "(EventLabel, Core, State, State com option) rgformula_es"
where "Scheduler_RGF \<equiv>  (rgf_EvtSys (\<Union>t. {Schedule_RGF t}),
         RG[{s. inv s}, Schedule_rely, Schedule_guar, {s. inv s}])"

definition Memory_manage_system_Spec :: "(EventLabel, Core, State, State com option) rgformula_par"
where "Memory_manage_system_Spec k \<equiv> 
    case k of (\<T> t) \<Rightarrow> Thread_RGF t
            | \<S> \<Rightarrow> Scheduler_RGF
            | Timer \<Rightarrow> Timer_RGF"

section \<open> functional correctness of the whole specification\<close>

definition "sys_rely \<equiv> {}"
(*definition "sys_rely \<equiv> {(s,t). inv s \<longrightarrow> inv t}"*)
(*definition "sys_rely \<equiv> (\<Inter>t. lvars_nochange_rel t) \<inter> gvars_conf_stable \<inter> {(s,t). inv s \<longrightarrow> inv t}"*)


definition "sys_guar \<equiv>  Schedule_guar \<union> Tick_guar \<union> (\<Union>t. (OSMemGet_guar t \<union> OSMemPut_guar t))"

lemma scheduler_esys_sat: "\<Gamma> \<turnstile> fst (Memory_manage_system_Spec \<S>) 
  sat\<^sub>s [Pre\<^sub>e\<^sub>s (Memory_manage_system_Spec \<S>), 
        Rely\<^sub>e\<^sub>s (Memory_manage_system_Spec \<S>), 
        Guar\<^sub>e\<^sub>s (Memory_manage_system_Spec \<S>), 
        Post\<^sub>e\<^sub>s (Memory_manage_system_Spec \<S>)]"
apply(simp add:Memory_manage_system_Spec_def Scheduler_RGF_def Schedule_RGF_def)
  apply(rule EvtSys_h)
    apply auto[1] apply(simp add:E\<^sub>e_def Pre\<^sub>e_def Rely\<^sub>e_def Guar\<^sub>e_def Post\<^sub>e_def)
    using Schedule_satRG apply(simp add:Schedule_RGCond_def Evt_sat_RG_def Pre\<^sub>f_def Rely\<^sub>f_def Guar\<^sub>f_def Post\<^sub>f_def)
    apply fast
    apply(simp add:Pre\<^sub>e\<^sub>s_def Pre\<^sub>e_def Schedule_RGCond_def)
    apply(simp add:Rely\<^sub>e\<^sub>s_def Rely\<^sub>e_def Schedule_RGCond_def)
    apply(simp add:Guar\<^sub>e\<^sub>s_def Guar\<^sub>e_def Schedule_RGCond_def)
    apply(simp add:Post\<^sub>e\<^sub>s_def Post\<^sub>e_def Schedule_RGCond_def)
    apply(simp add:Post\<^sub>e_def Pre\<^sub>e_def Schedule_RGCond_def getrgformula_def) 
    apply(simp add:Pre\<^sub>e\<^sub>s_def Rely\<^sub>e\<^sub>s_def getrgformula_def)
      using stable_inv_sched_rely apply(simp add:stable_def)
    apply(simp add:Guar\<^sub>e\<^sub>s_def getrgformula_def Schedule_guar_def) 
      done

lemma timer_esys_sat: "\<Gamma> \<turnstile> fst (Memory_manage_system_Spec Timer) 
  sat\<^sub>s [Pre\<^sub>e\<^sub>s (Memory_manage_system_Spec Timer), 
        Rely\<^sub>e\<^sub>s (Memory_manage_system_Spec Timer), 
        Guar\<^sub>e\<^sub>s (Memory_manage_system_Spec Timer), 
        Post\<^sub>e\<^sub>s (Memory_manage_system_Spec Timer)]"
  apply(simp add:Memory_manage_system_Spec_def Timer_RGF_def Tick_RGF_def)
  apply(rule EvtSys_h)
         apply auto[1] apply(simp add:E\<^sub>e_def Pre\<^sub>e_def Rely\<^sub>e_def Guar\<^sub>e_def Post\<^sub>e_def)
  using Tick_satRG apply(simp add:Tick_RGCond_def Evt_sat_RG_def Pre\<^sub>f_def Rely\<^sub>f_def Guar\<^sub>f_def Post\<^sub>f_def) 
         apply fast
        apply(simp add:Pre\<^sub>e\<^sub>s_def Pre\<^sub>e_def Tick_RGCond_def)
       apply(simp add:Rely\<^sub>e\<^sub>s_def Rely\<^sub>e_def Tick_RGCond_def)
      apply(simp add:Guar\<^sub>e\<^sub>s_def Guar\<^sub>e_def Tick_RGCond_def)
     apply(simp add:Post\<^sub>e\<^sub>s_def Post\<^sub>e_def Tick_RGCond_def)
    apply(simp add:Post\<^sub>e_def Pre\<^sub>e_def Tick_RGCond_def getrgformula_def) 
   apply(simp add:Pre\<^sub>e\<^sub>s_def Rely\<^sub>e\<^sub>s_def getrgformula_def)
  using stable_inv_sched_rely apply(simp add:stable_def)
  apply(simp add:Guar\<^sub>e\<^sub>s_def getrgformula_def Tick_guar_def) 
  done

lemma thread_esys_sat: "\<Gamma> \<turnstile> fst (Memory_manage_system_Spec (\<T> x)) 
  sat\<^sub>s [Pre\<^sub>e\<^sub>s (Memory_manage_system_Spec (\<T> x)), 
        Rely\<^sub>e\<^sub>s (Memory_manage_system_Spec (\<T> x)), 
        Guar\<^sub>e\<^sub>s (Memory_manage_system_Spec (\<T> x)), 
        Post\<^sub>e\<^sub>s (Memory_manage_system_Spec (\<T> x))]"
  apply(simp add:Memory_manage_system_Spec_def Thread_RGF_def OSMemGet_RGF_def OSMemPut_RGF_def)
  apply (simp add: OSMboxPend_RGF_def OSMboxPost_RGF_def OSMboxAccept_RGF_def)
  apply(rule EvtSys_h)
         apply auto[1]
             apply(simp add:E\<^sub>e_def Pre\<^sub>e_def Rely\<^sub>e_def Guar\<^sub>e_def Post\<^sub>e_def getrgformula_def)
  using OSMemGet_satRG apply(simp add:Evt_sat_RG_def OSMemGet_RGCond_def getrgformula_def 
                            Pre\<^sub>f_def Rely\<^sub>f_def Guar\<^sub>f_def Post\<^sub>f_def) 
          apply fast
    apply(simp add:E\<^sub>e_def Pre\<^sub>e_def Rely\<^sub>e_def Guar\<^sub>e_def Post\<^sub>e_def getrgformula_def)
  using OSMemPut_satRG apply(simp add:Evt_sat_RG_def OSMemPut_RGCond_def getrgformula_def 
                             Pre\<^sub>f_def Rely\<^sub>f_def Guar\<^sub>f_def Post\<^sub>f_def) 
            apply fast
           apply (simp add: E\<^sub>e_def Pre\<^sub>e_def Rely\<^sub>e_def Guar\<^sub>e_def Post\<^sub>e_def getrgformula_def)
  using OSMboxPend_satRG apply(simp add: Evt_sat_RG_def OSMboxPend_RGCond_def getrgformula_def 
                                Pre\<^sub>f_def Rely\<^sub>f_def Guar\<^sub>f_def Post\<^sub>f_def)
           apply fast
           apply (simp add: E\<^sub>e_def Pre\<^sub>e_def Rely\<^sub>e_def Guar\<^sub>e_def Post\<^sub>e_def getrgformula_def )
  using OSMboxPost_satRG apply(simp add: Evt_sat_RG_def OSMboxPost_RGCond_def getrgformula_def 
                                Pre\<^sub>f_def Rely\<^sub>f_def Guar\<^sub>f_def Post\<^sub>f_def)
          apply fast
           apply (simp add: E\<^sub>e_def Pre\<^sub>e_def Rely\<^sub>e_def Guar\<^sub>e_def Post\<^sub>e_def getrgformula_def)
  using OSMboxAccept_satRG apply(simp add: Evt_sat_RG_def OSMboxPost_RGCond_def getrgformula_def 
                                Pre\<^sub>f_def Rely\<^sub>f_def Guar\<^sub>f_def Post\<^sub>f_def OSMboxAccept_RGCond_def)
  apply fast
        apply auto[1]
            apply(simp add:Pre\<^sub>e\<^sub>s_def Pre\<^sub>e_def getrgformula_def OSMemGet_RGCond_def)
           apply(simp add:Pre\<^sub>e\<^sub>s_def Pre\<^sub>e_def getrgformula_def OSMemPut_RGCond_def)
          apply(simp add:Pre\<^sub>e\<^sub>s_def Pre\<^sub>e_def getrgformula_def OSMboxPend_RGCond_def)
         apply(simp add:Pre\<^sub>e\<^sub>s_def Pre\<^sub>e_def getrgformula_def OSMboxPost_RGCond_def)
        apply(simp add:Pre\<^sub>e\<^sub>s_def Pre\<^sub>e_def getrgformula_def OSMboxAccept_RGCond_def)
       apply auto[1]
        apply(simp add:Rely\<^sub>e\<^sub>s_def Rely\<^sub>e_def getrgformula_def OSMemGet_RGCond_def)
          apply(simp add:Rely\<^sub>e\<^sub>s_def Rely\<^sub>e_def getrgformula_def OSMemPut_RGCond_def)
         apply(simp add:Rely\<^sub>e\<^sub>s_def Rely\<^sub>e_def getrgformula_def OSMboxPend_RGCond_def)
        apply(simp add:Rely\<^sub>e\<^sub>s_def Rely\<^sub>e_def getrgformula_def OSMboxPost_RGCond_def)
       apply(simp add:Rely\<^sub>e\<^sub>s_def Rely\<^sub>e_def getrgformula_def OSMboxAccept_RGCond_def)
      apply auto[1]
       apply(simp add:Guar\<^sub>e\<^sub>s_def Guar\<^sub>e_def getrgformula_def OSMemGet_RGCond_def)
       apply (simp add: OSMem_eq_guar)
         apply(simp add:Guar\<^sub>e\<^sub>s_def Guar\<^sub>e_def getrgformula_def OSMemPut_RGCond_def)
        apply(simp add:Guar\<^sub>e\<^sub>s_def Guar\<^sub>e_def getrgformula_def OSMboxPend_RGCond_def)
       apply(simp add:Guar\<^sub>e\<^sub>s_def Guar\<^sub>e_def getrgformula_def OSMboxPost_RGCond_def)
      apply(simp add:Guar\<^sub>e\<^sub>s_def Guar\<^sub>e_def getrgformula_def OSMboxAccept_RGCond_def)
     apply auto[1]
         apply(simp add:Post\<^sub>e\<^sub>s_def Post\<^sub>e_def getrgformula_def OSMemGet_RGCond_def)
        apply(simp add:Post\<^sub>e\<^sub>s_def Post\<^sub>e_def getrgformula_def OSMemPut_RGCond_def)
       apply(simp add:Post\<^sub>e\<^sub>s_def Post\<^sub>e_def getrgformula_def OSMboxPend_RGCond_def)
      apply(simp add:Post\<^sub>e\<^sub>s_def Post\<^sub>e_def getrgformula_def OSMboxPost_RGCond_def)
     apply(simp add:Post\<^sub>e\<^sub>s_def Post\<^sub>e_def getrgformula_def OSMboxAccept_RGCond_def)
    apply (simp add: OSMemGet_RGCond_def OSMemPut_RGCond_def OSMboxPend_RGCond_def
           OSMboxPost_RGCond_def OSMboxAccept_RGCond_def)
    apply (simp add: Post\<^sub>e_def Pre\<^sub>e_def getrgformula_def)
    apply (simp add: OSMemGet_pre_def OSMemGet_post_def OSMemPut_pre_def OSMemPut_post_def
    OSMboxPend_pre_def OSMboxPend_post_def OSMboxPost_pre_def OSMboxPost_post_def 
    OSMboxAccept_pre_def OSMboxAccept_post_def)
    apply auto[1]
   apply(simp add:Pre\<^sub>e\<^sub>s_def Rely\<^sub>e\<^sub>s_def getrgformula_def)
   apply (simp add: OSMemPut_pre_def OSMemGet_pre_def OSMboxPend_pre_def OSMboxPost_pre_def
      OSMboxAccept_pre_def)
   apply (simp add: stable_def)
  using stable_inv_free_rely apply auto[1]
  apply(simp add:Pre\<^sub>e\<^sub>s_def Guar\<^sub>e\<^sub>s_def getrgformula_def OSMemPut_rely_def OSMemGet_rely_def)
  by (simp add: OSMemPut_guar_def)

lemma esys_sat: "\<Gamma> \<turnstile> fst (Memory_manage_system_Spec k) 
  sat\<^sub>s [Pre\<^sub>e\<^sub>s (Memory_manage_system_Spec k), 
        Rely\<^sub>e\<^sub>s (Memory_manage_system_Spec k), 
        Guar\<^sub>e\<^sub>s (Memory_manage_system_Spec k), 
        Post\<^sub>e\<^sub>s (Memory_manage_system_Spec k)]"
  apply(induct k)
  apply (simp add: scheduler_esys_sat) 
  apply (simp add: thread_esys_sat) 
  apply (simp add: timer_esys_sat)
  done

lemma s0_esys_pre: "{s0} \<subseteq> Pre\<^sub>e\<^sub>s (Memory_manage_system_Spec k)"
  apply(induct k)
    apply(simp add:Memory_manage_system_Spec_def Pre\<^sub>e\<^sub>s_def Scheduler_RGF_def getrgformula_def)
    using s0_inv apply fast
  apply(simp add:Memory_manage_system_Spec_def Pre\<^sub>e\<^sub>s_def Thread_RGF_def getrgformula_def)
     apply (simp add: OSMemGet_pre_def OSMemPut_pre_def OSMboxPost_pre_def OSMboxAccept_pre_def 
            OSMboxPend_pre_def s0_inv)
    apply(simp add:Memory_manage_system_Spec_def Pre\<^sub>e\<^sub>s_def Thread_RGF_def getrgformula_def)
    by (simp add: Timer_RGF_def getrgformula_def)


lemma esys_guar_in_other:
  "jj \<noteq> k \<longrightarrow> Guar\<^sub>e\<^sub>s (Memory_manage_system_Spec jj) \<subseteq> Rely\<^sub>e\<^sub>s (Memory_manage_system_Spec k)"
  apply auto
  apply(induct jj)
    apply(induct k)
      apply simp
     apply(simp add:Guar\<^sub>e\<^sub>s_def Rely\<^sub>e\<^sub>s_def Memory_manage_system_Spec_def Scheduler_RGF_def 
          Thread_RGF_def getrgformula_def)
  using OSMem_eq_rely Schedguar_in_OSMemGetrely Schedule_guar_in_OSMboxAccept_rely 
  Schedule_guar_in_OSMboxPend_rely Schedule_guar_in_OSMboxPost_rely apply blast
  using OSMem_eq_rely Schedguar_in_OSMemGetrely apply auto[1]
     apply(simp add:Guar\<^sub>e\<^sub>s_def Rely\<^sub>e\<^sub>s_def Memory_manage_system_Spec_def Scheduler_RGF_def 
          Timer_RGF_def getrgformula_def)
  using Schedule_guar_in_Tick_rely apply auto[1]
    apply(induct k)
      apply(simp add:Guar\<^sub>e\<^sub>s_def Rely\<^sub>e\<^sub>s_def Memory_manage_system_Spec_def Scheduler_RGF_def 
            Thread_RGF_def getrgformula_def)
  using OSMboxAccept_guar_in_Schedule_rely OSMboxPend_guar_in_Schedule_rely 
        OSMboxPost_guar_in_Schedule_rely OSMemGetguar_in_schedrely OSMem_eq_guar apply blast
    apply(simp add:Guar\<^sub>e\<^sub>s_def Rely\<^sub>e\<^sub>s_def Memory_manage_system_Spec_def Thread_RGF_def getrgformula_def)
  using OSMemGetguar_in_OSMemGetrely OSMem_eq_guar OSMem_eq_rely OSMbox_eq_guar OSMbox_eq_rely 
        OSMboxguar_in_OSMboxrely OSMboxguar_in_OSMemrely OSMemguar_in_OSMboxrely apply auto[1]
      apply (meson contra_subsetD)
     apply (meson contra_subsetD)
    apply (meson contra_subsetD)
   apply(simp add:Guar\<^sub>e\<^sub>s_def Rely\<^sub>e\<^sub>s_def Memory_manage_system_Spec_def Thread_RGF_def 
      Timer_RGF_def getrgformula_def)
  using OSMemPut_guar_in_Tick_rely apply auto[1]
     apply(induct k)
       apply (metis OSMboxPost_guar_def OSMemPut_guar_def contra_subsetD)
      apply (metis OSMboxPost_guar_def OSMemPut_guar_def contra_subsetD)
     apply (metis OSMboxPost_guar_def OSMemPut_guar_def contra_subsetD)
    apply (metis OSMboxAccept_guar_def OSMemPut_guar_def contra_subsetD)
   apply (metis OSMboxPend_guar_def OSMemPut_guar_def contra_subsetD)
      apply(simp add:Guar\<^sub>e\<^sub>s_def Rely\<^sub>e\<^sub>s_def Memory_manage_system_Spec_def)
  apply (induct k)
  apply (simp add: Timer_RGF_def Scheduler_RGF_def getrgformula_def)
  using Tick_guar_in_Schedule_rely apply auto[1]
   apply (simp add: Timer_RGF_def Thread_RGF_def getrgformula_def)
  using OSMbox_eq_rely1 OSMbox_eq_rely3 OSMem_eq_rely Tick_guar_in_OSMboxrely 
  Tick_guar_in_OSMemPut_rely apply blast
   apply auto[1]
  done

lemma esys_guar_in_sys: "Guar\<^sub>e\<^sub>s (Memory_manage_system_Spec k) \<subseteq> sys_guar"
  apply(induct k)
    apply(simp add:Guar\<^sub>e\<^sub>s_def Memory_manage_system_Spec_def Scheduler_RGF_def getrgformula_def sys_guar_def) 
   apply auto[1]
   apply(simp add:Guar\<^sub>e\<^sub>s_def Memory_manage_system_Spec_def Thread_RGF_def getrgformula_def sys_guar_def)
   apply (metis (mono_tags) OSMboxAccept_guar_def OSMboxPend_guar_def OSMbox_eq_guar1 
        OSMemGet_guar_def OSMem_eq_guar SUP_le_iff UNIV_I sup.idem sup_ge2 sys_guar_def)
  apply(simp add:Guar\<^sub>e\<^sub>s_def Memory_manage_system_Spec_def Timer_RGF_def getrgformula_def sys_guar_def)
  apply auto[1]
  done

lemma mem_sys_sat: "\<Gamma> \<turnstile> Memory_manage_system_Spec SAT [{s0}, sys_rely, sys_guar, UNIV]"
  apply(rule ParallelESys[of \<Gamma> Memory_manage_system_Spec"{s0}" sys_rely sys_guar UNIV])
  apply clarify using esys_sat apply fast
  using s0_esys_pre apply fast
  apply(simp add:sys_rely_def)
  using esys_guar_in_other apply fast
  using esys_guar_in_sys apply fast
  apply simp
  done

end