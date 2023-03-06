theory rg_cond
  imports invariant
begin

section \<open>Rely-guarantee condition of events\<close>

subsection \<open>defs of rely-guarantee conditions\<close>

text \<open>local variables do not change\<close>
definition lvars_nochange :: "Thread \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool"
  where "lvars_nochange t r s \<equiv> 
  (ret r t = ret s t) \<and> (ret_mem r t = ret_mem s t) (*\<and> (tmout r t = tmout s t) *)
\<and> (endt r t = endt s t) \<and> (posting_msg r t = posting_msg s t) (*\<and> (get_msg r t = get_msg s t)*)
\<and> (th r t = th s t) \<and> (need_resched r t = need_resched s t) (*\<and> (statPend r t = statPend s t) *)"

definition lvars_nochange_rel :: "Thread \<Rightarrow> (State \<times> State) set"
  where "lvars_nochange_rel t \<equiv> {(s,r). lvars_nochange t s r}"

definition lvars_nochange_4all :: "(State \<times> State) set"
  where "lvars_nochange_4all \<equiv> {(s,r). \<forall>t. lvars_nochange t s r}"

definition timestat_nochange :: "Thread \<Rightarrow> State \<Rightarrow> State \<Rightarrow> bool"
  where "timestat_nochange t r s \<equiv> (tmout r t = tmout s t) \<and> (statPend r t = statPend s t)"

definition timestat_nochange_rel :: "Thread \<Rightarrow> (State \<times> State) set"
  where "timestat_nochange_rel t \<equiv> {(s,r). timestat_nochange t s r}"

definition timestat_nochange_4all :: "(State \<times> State) set"
  where "timestat_nochange_4all \<equiv> {(s,r). \<forall>t. timestat_nochange t s r}"

text \<open>global variables do not change\<close>
definition gvars_nochange :: "State \<Rightarrow> State \<Rightarrow> bool"
  where "gvars_nochange s r \<equiv> cur r = cur s \<and> tick r = tick s \<and> thd_state r = thd_state s 
                            \<and> OS_MEMs r = OS_MEMs s \<and> OS_MEM_info r = OS_MEM_info s
                            \<and> OSMailBoxs r = OSMailBoxs s \<and> OSMailbox_info r = OSMailbox_info s"

definition gvars_nochange_rel :: "(State \<times> State) set"
  where "gvars_nochange_rel \<equiv> {(s,r). gvars_nochange s r}"

text \<open>static configurations of the OS_MEM do not change\<close>

definition gvars_conf :: "State \<Rightarrow> State \<Rightarrow> bool"
where "gvars_conf s r \<equiv> 
           OS_MEMs r = OS_MEMs s \<and> OSMailBoxs r = OSMailBoxs s
         \<and> (\<forall>p. OSMemAddr (OS_MEM_info s p) = OSMemAddr (OS_MEM_info r p)
            \<and> OSMemBlkSize (OS_MEM_info s p) = OSMemBlkSize (OS_MEM_info r p)
            \<and> OSMemNBlks (OS_MEM_info s p) = OSMemNBlks (OS_MEM_info r p))
         \<and> (\<forall>p. buf (OSMailbox_info s p) = buf (OSMailbox_info r p))"

definition gvars_conf_stable :: "(State \<times> State) set"
  where "gvars_conf_stable \<equiv> {(s,r). gvars_conf s r}"

definition Schedule_rely :: "(State \<times> State) set" 
  where "Schedule_rely \<equiv> {(s,r). inv s \<longrightarrow> inv r} \<union> Id"

definition Schedule_guar :: "(State \<times> State) set" 
  where "Schedule_guar \<equiv> ({(s,r). inv s \<longrightarrow> inv r} 
         \<inter> \<lbrace>\<ordmasculine>OS_MEMs = \<ordfeminine>OS_MEMs \<and> \<ordmasculine>OS_MEM_info = \<ordfeminine>OS_MEM_info \<and> 
            \<ordmasculine>tick = \<ordfeminine>tick \<and> \<ordmasculine>OSMailBoxs = \<ordfeminine>OSMailBoxs \<and> 
            \<ordmasculine>OSMailbox_info = \<ordfeminine>OSMailbox_info\<rbrace>
         \<inter> (\<Inter>t. lvars_nochange_rel t)) \<union> Id"

definition Schedule_RGCond :: "Thread \<Rightarrow> (State) PiCore_Hoare.rgformula"
  where "Schedule_RGCond t \<equiv> 
          RG[{s. inv s},
          Schedule_rely,  Schedule_guar,
  {s. inv s}]"

definition Tick_rely :: "(State \<times> State) set"
where "Tick_rely \<equiv> \<lbrace>\<ordmasculine>tick = \<ordfeminine>tick\<rbrace> \<union> Id"

definition Tick_guar :: "(State \<times> State) set"
where "Tick_guar \<equiv> (\<lbrace>\<ordfeminine>tick = \<ordmasculine>tick + 1 \<and> \<ordmasculine>cur = \<ordfeminine>cur \<and> \<ordmasculine>thd_state = \<ordfeminine>thd_state
                      \<and> \<ordmasculine>OSMailBoxs = \<ordfeminine>OSMailBoxs \<and> \<ordmasculine>OSMailbox_info = \<ordfeminine>OSMailbox_info
                      \<and> \<ordmasculine>OS_MEMs = \<ordfeminine>OS_MEMs \<and> \<ordmasculine>OS_MEM_info = \<ordfeminine>OS_MEM_info\<rbrace>
                      \<inter> (\<Inter>t. lvars_nochange_rel t)) \<union> Id"

definition Tick_RGCond :: "(State) PiCore_Hoare.rgformula"
  where "Tick_RGCond \<equiv> 
          RG[\<lbrace>True\<rbrace>, Tick_rely, Tick_guar, \<lbrace>True\<rbrace>]"

definition OSMemGet_pre ::  "Thread \<Rightarrow> State set"
  where "OSMemGet_pre t \<equiv> {s. inv s}"

definition OSMemGet_rely ::  "Thread \<Rightarrow> (State \<times> State) set"
  where "OSMemGet_rely t \<equiv>    
   ((lvars_nochange_rel t \<inter> gvars_conf_stable
    \<inter> {(s,r). inv s \<longrightarrow> inv r}
    \<inter> {(s,r).(cur s = Some t \<longrightarrow> OS_MEM_info s = OS_MEM_info r
                  \<and> (\<forall>t'. t' \<noteq> t \<longrightarrow> lvars_nochange t' s r))}) \<union> Id)  
"

definition OSMemGet_guar ::  "Thread \<Rightarrow> (State \<times> State) set"
  where "OSMemGet_guar t \<equiv> 
        ((gvars_conf_stable \<inter>
        {(s,r). (cur s \<noteq> Some t \<longrightarrow> gvars_nochange s r \<and> lvars_nochange t s r)
                 \<and> (cur s = Some t \<longrightarrow> inv s \<longrightarrow> inv r)
                 \<and> (\<forall>t'. t' \<noteq> t \<longrightarrow> lvars_nochange t' s r)} \<inter> \<lbrace>\<ordmasculine>tick = \<ordfeminine>tick\<rbrace>) \<union> Id)
"

definition OSMemGet_post ::  "Thread \<Rightarrow> State set"
  where "OSMemGet_post t \<equiv> {s. inv s 
                            \<and> (ret s t = OS_ERR_NONE \<longrightarrow> (\<exists>blk. ret_mem s t = Some blk))
                            \<and> (ret s t = OS_ERR_MEM_NO_FREE_BLKS \<longrightarrow> ret_mem s t = None)}"

definition OSMemGet_RGCond :: "Thread \<Rightarrow>(State) PiCore_Hoare.rgformula"
  where "OSMemGet_RGCond t  \<equiv> RG[OSMemGet_pre t, 
                                OSMemGet_rely t,
                                OSMemGet_guar t,
                                OSMemGet_post t]"

definition OSMemPut_pre ::  "Thread \<Rightarrow> State set"
  where "OSMemPut_pre t \<equiv> {s. inv s}"

definition OSMemPut_rely ::  "Thread \<Rightarrow>(State \<times> State) set"
  where "OSMemPut_rely t \<equiv> 
   ((lvars_nochange_rel t \<inter> gvars_conf_stable
    \<inter> {(s,r). inv s \<longrightarrow> inv r}
    \<inter> {(s,r).(cur s = Some t \<longrightarrow> OS_MEM_info s = OS_MEM_info r
                  \<and> (\<forall>t'. t' \<noteq> t \<longrightarrow> lvars_nochange t' s r))}) \<union> Id)
"
definition OSMemPut_guar ::  "Thread \<Rightarrow>(State \<times> State) set"
  where "OSMemPut_guar t \<equiv>
  ((gvars_conf_stable \<inter>
  {(s,r). (cur s \<noteq> Some t \<longrightarrow> gvars_nochange s r \<and> lvars_nochange t s r)
     \<and> (cur s = Some t \<longrightarrow> inv s \<longrightarrow> inv r)
     \<and> (\<forall>t'. t' \<noteq> t \<longrightarrow> lvars_nochange t' s r)} \<inter> \<lbrace>\<ordmasculine>tick = \<ordfeminine>tick\<rbrace>) \<union> Id)
"

definition OSMemPut_post ::  "Thread \<Rightarrow> State set"
  where "OSMemPut_post t \<equiv> {s. inv s}"

definition OSMemPut_RGCond :: "Thread \<Rightarrow> (State) PiCore_Hoare.rgformula"
  where "OSMemPut_RGCond t  \<equiv> RG[OSMemPut_pre t,
                                OSMemPut_rely t,
                                OSMemPut_guar t,
                                OSMemPut_post t]" 

lemma OSMem_eq_guar: "OSMemPut_guar x = OSMemGet_guar x"
  by(simp add:OSMemPut_guar_def OSMemGet_guar_def)

lemma OSMem_eq_rely: "OSMemPut_rely x = OSMemGet_rely x"
  by(simp add:OSMemPut_rely_def OSMemGet_rely_def)

definition 
OSMboxPost_pre :: "Thread \<Rightarrow> State set"
  where "OSMboxPost_pre t \<equiv> {s. inv s}"

definition OSMboxPost_guar :: "Thread \<Rightarrow> (State \<times> State) set"  
where "OSMboxPost_guar t \<equiv> 
        ((gvars_conf_stable \<inter> 
          {(s,r). (cur s \<noteq> Some t \<longrightarrow> gvars_nochange s r \<and> lvars_nochange t s r)
                  \<and> (cur s = Some t \<longrightarrow> inv s \<longrightarrow> inv r) 
                  \<and> (\<forall>t'. t' \<noteq> t \<longrightarrow> lvars_nochange t' s r) }
          \<inter> \<lbrace>\<ordmasculine>tick = \<ordfeminine>tick\<rbrace>) \<union> Id)"

definition OSMboxPost_rely :: "Thread \<Rightarrow> (State \<times> State) set"
where "OSMboxPost_rely t \<equiv> 
   ((lvars_nochange_rel t \<inter> gvars_conf_stable
    \<inter> {(s,r). inv s \<longrightarrow> inv r}
    \<inter> {(s,r).(cur s = Some t \<longrightarrow> OSMailbox_info s = OSMailbox_info r
                  \<and> (\<forall>t'. t' \<noteq> t \<longrightarrow> lvars_nochange t' s r))}) \<union> Id)"

definition OSMboxPost_post :: "Thread \<Rightarrow> State set"
  where "OSMboxPost_post t \<equiv> {s. inv s}"

definition OSMboxPost_RGCond :: "Thread \<Rightarrow>  (State) PiCore_Hoare.rgformula"
  where "OSMboxPost_RGCond t  \<equiv> 
          RG[OSMboxPost_pre t,
             OSMboxPost_rely t,
              OSMboxPost_guar t,
              OSMboxPost_post t]"

definition OSMboxAccept_pre :: "Thread \<Rightarrow> State set"
  where "OSMboxAccept_pre t \<equiv> {s. inv s}"

definition OSMboxAccept_rely :: "Thread \<Rightarrow> (State \<times> State) set"
  where "OSMboxAccept_rely t \<equiv> 
   ((lvars_nochange_rel t \<inter> gvars_conf_stable
    \<inter> {(s,r). inv s \<longrightarrow> inv r}
    \<inter> {(s,r).(cur s = Some t \<longrightarrow> OSMailbox_info s = OSMailbox_info r
                  \<and> (\<forall>t'. t' \<noteq> t \<longrightarrow> lvars_nochange t' s r))}) \<union> Id)"     \<comment> \<open>The rely condition of Mem_alloc is the same as one of Mem_free \<close>

definition OSMboxAccept_guar :: "Thread \<Rightarrow> (State \<times> State) set"  
  where "OSMboxAccept_guar t \<equiv> 
        ((gvars_conf_stable \<inter> 
          {(s,r). (cur s \<noteq> Some t \<longrightarrow> gvars_nochange s r \<and> lvars_nochange t s r)
                  \<and> (cur s = Some t \<longrightarrow> inv s \<longrightarrow> inv r) 
                  \<and> (\<forall>t'. t' \<noteq> t \<longrightarrow> lvars_nochange t' s r) }
          \<inter> \<lbrace>\<ordmasculine>tick = \<ordfeminine>tick\<rbrace>) \<union> Id)"

definition OSMboxAccept_post :: "Thread \<Rightarrow> State set"
  where "OSMboxAccept_post t \<equiv> {s. inv s}"

definition OSMboxAccept_RGCond :: "Thread \<Rightarrow>  (State) PiCore_Hoare.rgformula"
  where "OSMboxAccept_RGCond t  \<equiv> 
          RG[OSMboxAccept_pre t,
             OSMboxAccept_rely t,
              OSMboxAccept_guar t,
              OSMboxAccept_post t]"

definition OSMboxPend_pre :: "Thread \<Rightarrow> State set"
where "OSMboxPend_pre t \<equiv> {s. inv s }"

definition OSMboxPend_rely :: "Thread \<Rightarrow> (State \<times> State) set"
where "OSMboxPend_rely t \<equiv> 
   ((lvars_nochange_rel t  \<inter>  gvars_conf_stable
    \<inter> {(s,r). inv s \<longrightarrow> inv r}
    \<inter> {(s,r).(cur s = Some t \<longrightarrow> OSMailbox_info s = OSMailbox_info r
                  \<and> (\<forall>t'. t' \<noteq> t \<longrightarrow> lvars_nochange t' s r))}) \<union> Id)"

definition OSMboxPend_guar :: "Thread \<Rightarrow> (State \<times> State) set"
  where "OSMboxPend_guar t \<equiv> 
        ((gvars_conf_stable \<inter> 
          {(s,r). (cur s \<noteq> Some t \<longrightarrow> gvars_nochange s r \<and> lvars_nochange t s r)
                  \<and> (cur s = Some t \<longrightarrow> inv s \<longrightarrow> inv r) 
                  \<and> (\<forall>t'. t' \<noteq> t \<longrightarrow> lvars_nochange t' s r) }
          \<inter> \<lbrace>\<ordmasculine>tick = \<ordfeminine>tick\<rbrace>) \<union> Id)"

lemma OSMbox_eq_rely1 : "OSMboxPost_rely t = OSMboxAccept_rely t"
  by (simp add: OSMboxPost_rely_def OSMboxAccept_rely_def)

lemma OSMbox_eq_rely2 : "OSMboxPost_rely t = OSMboxPend_rely t"
  by (simp add: OSMboxPost_rely_def OSMboxPend_rely_def)

lemma OSMbox_eq_rely3 : "OSMboxPend_rely t = OSMboxAccept_rely t"
  by (simp add: OSMboxAccept_rely_def OSMboxPend_rely_def)

lemmas OSMbox_eq_rely = OSMbox_eq_rely1 OSMbox_eq_rely2 OSMbox_eq_rely3

lemma OSMbox_eq_guar1 : "OSMboxPost_guar t = OSMboxAccept_guar t"
  by (simp add: OSMboxPost_guar_def OSMboxAccept_guar_def)

lemma OSMbox_eq_guar2 : "OSMboxPost_guar t = OSMboxPend_guar t"
  by (simp add: OSMboxPost_guar_def OSMboxPend_guar_def)

lemma OSMbox_eq_guar3 : "OSMboxPend_guar t = OSMboxAccept_guar t"
  by (simp add: OSMboxAccept_guar_def OSMboxPend_guar_def)

lemmas OSMbox_eq_guar = OSMbox_eq_guar1 OSMbox_eq_guar2 OSMbox_eq_guar3

definition OSMboxPend_post :: "Thread \<Rightarrow> State set"
  where "OSMboxPend_post t \<equiv> {s. inv s }"

definition OSMboxPend_RGCond :: "Thread \<Rightarrow>  (State) PiCore_Hoare.rgformula"
  where "OSMboxPend_RGCond t  \<equiv> 
          RG[OSMboxPend_pre t,
             OSMboxPend_rely t,
              OSMboxPend_guar t,
              OSMboxPend_post t]"

subsection \<open>stablility, subset relations of rely-guarantee conditions\<close>

lemma stable_inv_free_rely:
  "(s,r) \<in> OSMemPut_rely t \<Longrightarrow> inv s \<Longrightarrow> inv r"
  using OSMemPut_rely_def by blast

lemma stable_inv_free_rely1: "stable \<lbrace> \<acute>inv \<rbrace> (OSMemPut_rely t)"
  using stable_inv_free_rely unfolding stable_def by auto

lemma stable_inv_alloc_rely:
  "(s,r) \<in> OSMemGet_rely t \<Longrightarrow> inv s \<Longrightarrow> inv r"
  using OSMemGet_rely_def by blast

lemma stable_inv_alloc_rely1: "stable \<lbrace> \<acute>inv \<rbrace> (OSMemGet_rely t)"
  by (simp add: stable_def stable_inv_alloc_rely)

lemma stable_inv_sched_rely:
  "(s,r) \<in> Schedule_rely \<Longrightarrow> inv s \<Longrightarrow> inv r"
  using Schedule_rely_def by blast

lemma stable_inv_sched_rely1: "stable \<lbrace>\<acute>inv\<rbrace> Schedule_rely"
  by (simp add: stable_def stable_inv_sched_rely)

lemma OSMemPut_guar_stb_inv: "stable \<lbrace>\<acute>inv \<rbrace> (OSMemPut_guar t)"
proof-
  { 
    fix x
    assume a0: "inv x"
    {
      fix y 
      assume b0: "(x,y) \<in> OSMemPut_guar t"
      hence "(x,y) \<in> {(s,r). (cur s \<noteq> Some t \<longrightarrow> gvars_nochange s r \<and> lvars_nochange t s r)
             \<and> (cur s = Some t \<longrightarrow> inv s \<longrightarrow> inv r)
             \<and> (\<forall>t'. t' \<noteq> t \<longrightarrow> lvars_nochange t' s r)}"
        using OSMemPut_guar_def gvars_nochange_def lvars_nochange_def by auto
      hence "(cur x \<noteq> Some t \<longrightarrow> gvars_nochange x y \<and> lvars_nochange t x y)
              \<and> (cur x = Some t \<longrightarrow> inv x \<longrightarrow>inv y)
              \<and> (\<forall>t' . t' \<noteq> t \<longrightarrow> lvars_nochange t' x y)" by simp
      hence "inv y"
        apply(case_tac "cur x \<noteq> Some t", simp)
         apply (simp add: gvars_nochange_def lvars_nochange_def) using a0 apply clarify
         apply(simp add:inv_def)
         apply (rule conjI) apply(simp add:inv_cur_def)
         apply (rule conjI, simp add: inv_OS_Mem_info_def inv_OS_Mem_info_mp_def)
        apply (simp add: inv_thd_waitq_def) apply blast
        using a0 by auto
    }
  }
  then show ?thesis by (simp add:stable_def)
qed

lemma OSMemGet_guar_stb_inv: "stable \<lbrace> \<acute>inv \<rbrace> (OSMemGet_guar t)"
  apply(subgoal_tac "OSMemGet_guar t = OSMemPut_guar t")
  using OSMemPut_guar_stb_inv apply simp
  by (simp add: OSMemGet_guar_def OSMemPut_guar_def) 

lemma sched_guar_stb_inv:
  "(s,r)\<in>Schedule_guar \<Longrightarrow> inv s \<Longrightarrow> inv r"
  apply(simp add: Schedule_guar_def)
  apply(erule disjE) by auto

lemma Tick_guar_stb_inv: "(s,r) \<in> Tick_guar \<Longrightarrow> inv s \<Longrightarrow> inv r"
  apply (simp add: Tick_guar_def)
  apply (erule disjE)
   apply (simp add: inv_def inv_cur_def inv_OS_Mem_info_def  inv_OS_Mem_info_mp_def inv_thd_waitq_def)
   apply auto
  done

lemma OSMemGet_pre_stb: "stable (OSMemGet_pre t) (OSMemGet_rely t)"
  by (simp add: OSMemGet_pre_def stable_inv_alloc_rely1)

lemma OSMemGet_post_stb: "stable (OSMemGet_post t) (OSMemGet_rely t)"
  apply (simp add: OSMemGet_post_def stable_def OSMemGet_rely_def, clarsimp)
  apply (case_tac "ret x t = OS_ERR_NONE", clarsimp)
   apply (simp add: lvars_nochange_def lvars_nochange_rel_def)
   apply (metis zero_neq_neg_numeral)
  apply (case_tac "ret x t = OS_ERR_MEM_NO_FREE_BLKS", clarsimp)
   apply (simp add: lvars_nochange_def lvars_nochange_rel_def)
   apply auto[1]
  using lvars_nochange_def lvars_nochange_rel_def by auto

lemma OSMemPut_pre_stb: "stable (OSMemPut_pre t) (OSMemPut_rely t)"
  by (simp add: OSMemPut_pre_def stable_inv_free_rely1)

lemma OSMemPut_post_stb: "stable (OSMemPut_pre t) (OSMemPut_rely t)"
  by (simp add: OSMemPut_pre_stb)

lemma OSMboxPend_pre_stable:" stable (OSMboxPend_pre t) (OSMboxPend_rely t) "
  by(simp add:OSMboxPend_pre_def OSMboxPend_rely_def stable_def gvars_conf_stable_def gvars_conf_def)

lemma OSMboxPend_post_stable:" stable (OSMboxPend_post t) (OSMboxPend_rely t) "
  by(simp add:OSMboxPend_post_def OSMboxPend_rely_def stable_def)

lemma OSMboxPost_pre_stable:" stable (OSMboxPost_pre t) (OSMboxPost_rely t) "
  by(simp add:OSMboxPost_pre_def OSMboxPost_rely_def stable_def gvars_conf_stable_def gvars_conf_def)

lemma OSMboxPost_post_stable:" stable (OSMboxPost_post t) (OSMboxPost_rely t) "
  by(simp add:OSMboxPost_post_def OSMboxPost_rely_def stable_def)

lemma OSMboxAccept_pre_stable:" stable (OSMboxAccept_pre t) (OSMboxAccept_rely t) "
  by(simp add:OSMboxAccept_pre_def OSMboxAccept_rely_def stable_def gvars_conf_stable_def gvars_conf_def)

lemma OSMboxAccept_post_stable:" stable (OSMboxAccept_post t) (OSMboxAccept_rely t) "
  by(simp add:OSMboxAccept_post_def OSMboxAccept_rely_def stable_def)

lemma OSMemGetguar_in_OSMemGetrely: "t1 \<noteq> t2 \<Longrightarrow> OSMemGet_guar t1 \<subseteq> OSMemGet_rely t2"
  apply clarify
proof - 
  fix a b
  assume p0: "t1 \<noteq> t2"
    and  p1: "(a,b) \<in> OSMemGet_guar t1"
  hence p2: "(a,b) \<in> gvars_conf_stable
                \<and> (cur a \<noteq> Some t1 \<longrightarrow> gvars_nochange a b \<and> lvars_nochange t1 a b)
                \<and> (cur a = Some t1 \<longrightarrow> inv a \<longrightarrow> inv b)
                \<and> (\<forall>t'. t' \<noteq> t1 \<longrightarrow> lvars_nochange t' a b) \<and> (tick a = tick b)  \<or> a = b"
    by (simp add: OSMemGet_guar_def)
  from p0 and p2 have
  "(a,b) \<in> lvars_nochange_rel t2 \<and> (a,b) \<in> gvars_conf_stable
    \<and> (inv a \<longrightarrow> inv b)
    \<and> (cur a = Some t2 \<longrightarrow> OS_MEM_info a = OS_MEM_info b
            \<and> (\<forall>t'. t' \<noteq> t2 \<longrightarrow> lvars_nochange t' a b))
    \<or> a = b"
    apply clarify
    apply(rule conjI) apply (simp add:lvars_nochange_rel_def)
    apply(rule conjI) apply simp
    apply(rule conjI) apply (metis CollectI OSMemGet_guar_stb_inv mem_Collect_eq p1 stable_def)
    apply clarify
    apply (rule conjI) apply(simp add:gvars_nochange_def)
    by auto
  thus "(a,b) \<in> OSMemGet_rely t2" unfolding OSMemGet_rely_def by simp
qed

lemma Schedguar_in_OSMemGetrely: "Schedule_guar \<subseteq> OSMemGet_rely t2"
  apply clarify
proof-
  fix a b
  assume p0: "(a,b) \<in> Schedule_guar"
  hence p1: "(inv a \<longrightarrow> inv b) \<and> OS_MEMs a = OS_MEMs b \<and> OS_MEM_info a = OS_MEM_info b
            \<and> OSMailBoxs a = OSMailBoxs b \<and> OSMailbox_info a = OSMailbox_info b 
            \<and> (a,b)\<in>(\<Inter>t. lvars_nochange_rel t) \<or> a = b"
    apply (clarsimp)
    by (intro conjI, simp_all add: Schedule_guar_def)
  hence "(a,b) \<in> lvars_nochange_rel t2 \<and> (a,b) \<in> gvars_conf_stable
         \<and> (inv a \<longrightarrow> inv b)
         \<and> (cur a = Some t2 \<longrightarrow> OS_MEM_info a = OS_MEM_info b
                \<and> (\<forall>t'. t' \<noteq> t2 \<longrightarrow> lvars_nochange t' a b))
         \<or> a = b"
    apply clarify
    apply (rule conjI, simp add: lvars_nochange_rel_def)
    apply(rule conjI, simp add: gvars_conf_stable_def gvars_conf_def)
    apply (rule conjI, simp, clarsimp)
    by (simp add: lvars_nochange_rel_def mem_Collect_eq)
  thus "(a,b) \<in> OSMemGet_rely t2" by(simp add: OSMemGet_rely_def)
qed

lemma OSMemGetguar_in_schedrely: "OSMemGet_guar t \<subseteq> Schedule_rely"
  apply(simp add:OSMemGet_guar_def Schedule_rely_def)
  apply clarify
  apply(case_tac "cur a = Some t")
    apply simp
  apply clarify
  apply (simp add: gvars_nochange_def inv_OS_Mem_info_def inv_OS_Mem_info_mp_def inv_cur_def 
      inv_thd_waitq_def inv_def)
  by blast

lemma Schedule_guar_in_Tick_rely : "Schedule_guar \<subseteq> Tick_rely"
  apply (simp add: Schedule_guar_def Tick_rely_def)
  apply auto[1]
  done

lemma OSMemPut_guar_in_Tick_rely:  "OSMemPut_guar t \<subseteq> Tick_rely"
  apply (simp add: OSMemPut_guar_def Tick_rely_def)
  apply auto[1]
  done

lemma Tick_guar_in_OSMemPut_rely: "Tick_guar \<subseteq> OSMemPut_rely t"
  apply (simp add: Tick_guar_def OSMemPut_rely_def)
  apply auto
  apply (simp add: gvars_conf_stable_def gvars_conf_def)
   apply (simp add: inv_def inv_cur_def inv_OS_Mem_info_def inv_OS_Mem_info_mp_def inv_thd_waitq_def)
   apply auto[1]
  apply (simp add: lvars_nochange_def lvars_nochange_rel_def)
  done

lemma Tick_guar_in_Schedule_rely: "Tick_guar \<subseteq> Schedule_rely"
  apply (simp add: Tick_guar_def Schedule_rely_def)
  apply (simp add: lvars_nochange_def lvars_nochange_rel_def)
  apply (simp add: inv_def inv_cur_def inv_OS_Mem_info_def inv_OS_Mem_info_mp_def inv_thd_waitq_def)
  apply auto
  done

lemma Schedule_guar_in_OSMboxPost_rely : "Schedule_guar \<subseteq> OSMboxPost_rely t"
  apply (simp add: Schedule_guar_def OSMboxPost_rely_def)
  apply (simp add: gvars_conf_stable_def gvars_conf_def lvars_nochange_def lvars_nochange_rel_def)
  apply auto
  done

lemma Schedule_guar_in_OSMboxPend_rely : "Schedule_guar \<subseteq> OSMboxPend_rely t"
  apply (simp add: Schedule_guar_def OSMboxPend_rely_def)
  apply (simp add: gvars_conf_stable_def gvars_conf_def lvars_nochange_def lvars_nochange_rel_def)
  apply auto
  done

lemma Schedule_guar_in_OSMboxAccept_rely : "Schedule_guar \<subseteq> OSMboxAccept_rely t"
    apply (simp add: Schedule_guar_def OSMboxAccept_rely_def)
  apply (simp add: gvars_conf_stable_def gvars_conf_def lvars_nochange_def lvars_nochange_rel_def)
  apply auto
  done

lemma OSMboxPost_guar_in_Schedule_rely : "OSMboxPost_guar t \<subseteq> Schedule_rely"
  apply (simp add: OSMboxPost_guar_def Schedule_rely_def)
  apply auto
  apply (simp add: gvars_nochange_def gvars_conf_stable_def gvars_conf_def lvars_nochange_def)
  apply (simp add: inv_def inv_cur_def inv_OS_Mem_info_def inv_OS_Mem_info_mp_def inv_thd_waitq_def)
  by blast

lemma OSMboxPend_guar_in_Schedule_rely : "OSMboxPend_guar t \<subseteq> Schedule_rely"
  apply (simp add: OSMboxPend_guar_def Schedule_rely_def)
  apply auto
  apply (simp add: gvars_nochange_def gvars_conf_stable_def gvars_conf_def lvars_nochange_def)
  apply (simp add: inv_def inv_cur_def inv_OS_Mem_info_def inv_OS_Mem_info_mp_def inv_thd_waitq_def)
  by blast

lemma OSMboxAccept_guar_in_Schedule_rely : "OSMboxAccept_guar t \<subseteq> Schedule_rely"
  apply (simp add: OSMboxAccept_guar_def Schedule_rely_def)
  apply auto
  apply (simp add: gvars_nochange_def gvars_conf_stable_def gvars_conf_def lvars_nochange_def)
  apply (simp add: inv_def inv_cur_def inv_OS_Mem_info_def inv_OS_Mem_info_mp_def inv_thd_waitq_def)
  by blast
                                         
lemma OSMboxguar_in_OSMboxrely : "t1 \<noteq> t2 \<Longrightarrow> OSMboxPost_guar t1 \<subseteq> OSMboxPost_rely t2"
  apply clarify
proof - 
  fix a b
  assume p0: "t1 \<noteq> t2"
    and  p1: "(a,b) \<in> OSMboxPost_guar t1"
  hence p2: "(a,b) \<in> gvars_conf_stable
                \<and> (cur a \<noteq> Some t1 \<longrightarrow> gvars_nochange a b \<and> lvars_nochange t1 a b)
                \<and> (cur a = Some t1 \<longrightarrow> inv a \<longrightarrow> inv b)
                \<and> (\<forall>t'. t' \<noteq> t1 \<longrightarrow> lvars_nochange t' a b) \<and> (tick a = tick b)  \<or> a = b"
    by (simp add: OSMboxPost_guar_def)
  from p0 and p2 have
  "(a,b) \<in> lvars_nochange_rel t2 \<and> (a,b) \<in> gvars_conf_stable
    \<and> (inv a \<longrightarrow> inv b)
    \<and> (cur a = Some t2 \<longrightarrow> OSMailbox_info a = OSMailbox_info b
            \<and> (\<forall>t'. t' \<noteq> t2 \<longrightarrow> lvars_nochange t' a b))
    \<or> a = b"
    apply clarify
    apply(rule conjI) apply (simp add:lvars_nochange_rel_def)
    apply(rule conjI) apply simp
    apply(rule conjI)
    apply (meson OSMboxPost_guar_in_Schedule_rely contra_subsetD p1 stable_inv_sched_rely)
    apply clarify
    apply (rule conjI) apply(simp add:gvars_nochange_def)
    by auto
  thus "(a,b) \<in> OSMboxPost_rely t2" unfolding OSMboxPost_rely_def by simp
qed
  
lemma OSMboxguar_in_OSMemrely : "t1 \<noteq> t2 \<Longrightarrow> OSMboxPost_guar t1 \<subseteq> OSMemPut_rely t2"
  apply clarify
proof - 
  fix a b
  assume p0: "t1 \<noteq> t2"
    and  p1: "(a,b) \<in> OSMboxPost_guar t1"
  hence p2: "(a,b) \<in> gvars_conf_stable
                \<and> (cur a \<noteq> Some t1 \<longrightarrow> gvars_nochange a b \<and> lvars_nochange t1 a b)
                \<and> (cur a = Some t1 \<longrightarrow> inv a \<longrightarrow> inv b)
                \<and> (\<forall>t'. t' \<noteq> t1 \<longrightarrow> lvars_nochange t' a b) \<and> (tick a = tick b)  \<or> a = b"
    by (simp add: OSMboxPost_guar_def)
  from p0 and p2 have
  "(a,b) \<in> lvars_nochange_rel t2 \<and> (a,b) \<in> gvars_conf_stable
    \<and> (inv a \<longrightarrow> inv b)
    \<and> (cur a = Some t2 \<longrightarrow> OS_MEM_info a = OS_MEM_info b
            \<and> (\<forall>t'. t' \<noteq> t2 \<longrightarrow> lvars_nochange t' a b))
    \<or> a = b"
    apply clarify
    apply(rule conjI) apply (simp add:lvars_nochange_rel_def)
    apply(rule conjI) apply simp
    apply(rule conjI)
    apply (meson OSMboxPost_guar_in_Schedule_rely contra_subsetD p1 stable_inv_sched_rely)
    apply clarify
    apply (rule conjI) apply(simp add:gvars_nochange_def)
    by auto
  thus "(a,b) \<in> OSMemPut_rely t2" unfolding OSMemPut_rely_def by simp
qed

lemma OSMemguar_in_OSMboxrely : "t1 \<noteq> t2 \<Longrightarrow> OSMemPut_guar t1 \<subseteq> OSMboxPost_rely t2"
  apply clarify
proof - 
  fix a b
  assume p0: "t1 \<noteq> t2"
    and  p1: "(a,b) \<in> OSMemPut_guar t1"
  hence p2: "(a,b) \<in> gvars_conf_stable
                \<and> (cur a \<noteq> Some t1 \<longrightarrow> gvars_nochange a b \<and> lvars_nochange t1 a b)
                \<and> (cur a = Some t1 \<longrightarrow> inv a \<longrightarrow> inv b)
                \<and> (\<forall>t'. t' \<noteq> t1 \<longrightarrow> lvars_nochange t' a b) \<and> (tick a = tick b)  \<or> a = b"
    by (simp add: OSMemPut_guar_def)
  from p0 and p2 have
  "(a,b) \<in> lvars_nochange_rel t2 \<and> (a,b) \<in> gvars_conf_stable
    \<and> (inv a \<longrightarrow> inv b)
    \<and> (cur a = Some t2 \<longrightarrow> OSMailbox_info a = OSMailbox_info b
            \<and> (\<forall>t'. t' \<noteq> t2 \<longrightarrow> lvars_nochange t' a b))
    \<or> a = b"
    apply clarify
    apply(rule conjI) apply (simp add:lvars_nochange_rel_def)
    apply(rule conjI) apply simp
    apply(rule conjI)
    using OSMemGetguar_in_schedrely OSMem_eq_guar p1 stable_inv_sched_rely apply blast
    apply clarify
    apply (rule conjI) apply(simp add:gvars_nochange_def)
    by auto
  thus "(a,b) \<in> OSMboxPost_rely t2" unfolding OSMboxPost_rely_def by simp
qed

lemma Tick_guar_in_OSMboxrely : "Tick_guar \<subseteq> OSMboxPost_rely x"
  apply (simp add: Tick_guar_def OSMboxPost_rely_def)
  apply (simp add: gvars_conf_stable_def gvars_conf_def lvars_nochange_def lvars_nochange_rel_def)
  apply (simp add: inv_def inv_cur_def inv_OS_Mem_info_def inv_OS_Mem_info_mp_def inv_thd_waitq_def)
  by auto

end