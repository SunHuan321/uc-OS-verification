theory invariant
  imports kernel_spec "HOL-Eisbach.Eisbach_Tools"
begin

section \<open>invariants\<close>

subsection \<open>defs of invariants\<close>
text\<open>
we consider multi-threaded execution on mono-core.
A thread is the currently executing thread iff it is in RUNNING state.
\<close>
definition inv_cur :: "State \<Rightarrow> bool"
  where "inv_cur s \<equiv> \<forall>t. cur s = Some t \<longleftrightarrow> thd_state s t = RUNNING"

abbreviation dist_list :: "'a list \<Rightarrow> bool"
  where "dist_list l \<equiv> \<forall>i j. i < length l \<and> j < length l \<and> i \<noteq> j \<longrightarrow> l!i \<noteq> l!j" 
                     \<comment> \<open> elements in a list are different with each other    \<close>

text\<open>
the relation of thread state and wait queue.
here we dont consider other modules of zephyr, so blocked thread is in wait que of mailboxs. 
\<close>

definition inv_thd_waitq :: "State \<Rightarrow> bool"
where "inv_thd_waitq s \<equiv> 
  (\<forall>p\<in>OSMailBoxs s. \<forall>t\<in> set (wait_q (OSMailbox_info s p)). thd_state s t = BLOCKED)                 
  \<comment> \<open> thread in waitq is BLOCKED    \<close>
 \<and> (\<forall>t. thd_state s t = BLOCKED \<longrightarrow> (\<exists>p\<in>OSMailBoxs s. t \<in> set (wait_q (OSMailbox_info s p))))      
   \<comment> \<open> BLOCKED thread is in a waitq    \<close>
 \<and> (\<forall>p\<in>OSMailBoxs s. dist_list (wait_q (OSMailbox_info s p)))                                 
   \<comment> \<open>  threads in a waitq are different with each other, which means  a thread could not waiting 
      for the same pool two times    \<close>
 \<and> (\<forall>p q. p\<in>OSMailBoxs s \<and> q\<in>OSMailBoxs s \<and> p \<noteq> q \<longrightarrow> (\<nexists>t. t \<in> set (wait_q (OSMailbox_info s p)) 
                                                  \<and> t\<in> set (wait_q (OSMailbox_info s q))))"      
 \<comment> \<open>threads of two waitqs are different, which means a thread could not waiting for two pools \<close>

definition inv_OS_Mem_info_mp :: "State \<Rightarrow> OS_MEM_ref \<Rightarrow> bool"
  where "inv_OS_Mem_info_mp s p \<equiv> let mp = OS_MEM_info s p in
       OSMemNBlks mp \<ge> 0 \<and> OSMemNFree mp \<ge> 0 
     \<and> OSMemNBlks mp \<ge> OSMemNFree mp
     \<and> OSMemNFree mp = int (length (OSMemFreeList mp))  
"

definition inv_OS_Mem_info :: "State \<Rightarrow> bool"
  where "inv_OS_Mem_info s \<equiv> \<forall> p \<in> OS_MEMs s. inv_OS_Mem_info_mp s p"

definition inv :: "State \<Rightarrow> bool"
  where "inv s \<equiv> inv_cur s \<and> inv_OS_Mem_info s \<and> inv_thd_waitq s"

subsection \<open>initial state s0\<close>

text\<open>
we dont consider OSMemCreate, only define s0 to show the state after memory pool initialization.\<close>

axiomatization s0 :: State where
  s0a1: "cur s0 = None" and
  s0a2: "tick s0 = 0" and
  s0a3: "thd_state s0 = (\<lambda>t. READY)" and
  s0a4: "OS_MEMs s0 \<noteq> {}" and 
  s0a5: "\<forall> p \<in> OS_MEMs s0. let mp = OS_MEM_info s0 p in
         OSMemNBlks mp \<ge> 0 \<and> OSMemNFree mp \<ge>0 
       \<and> OSMemNBlks mp = OSMemNFree mp
       \<and> OSMemNFree mp = int (length (OSMemFreeList mp))" and
  s0a6: "OSMailBoxs s0 \<noteq> {}" and
  s0a7: "\<forall>p\<in>OSMailBoxs s0. wait_q (OSMailbox_info s0 p) = []" and
  s0a8: "\<forall>p\<in>OSMailBoxs s0. let mp = OSMailbox_info s0 p in  msgPtr mp = None"

lemma s0_inv_cur: "inv_cur s0"
  by (simp add: inv_cur_def s0a1 s0a3)

lemma s0_inv_OS_Mem_info: "inv_OS_Mem_info s0"
  apply(simp add: inv_OS_Mem_info_def)
  apply(simp add: inv_OS_Mem_info_mp_def)  
  by (metis order_refl s0a5)

lemma s0_inv: "inv s0"
  apply(unfold inv_def)
  using s0_inv_cur apply simp
  using s0_inv_OS_Mem_info apply simp
  by (simp add: inv_thd_waitq_def s0a3 s0a7)

end

