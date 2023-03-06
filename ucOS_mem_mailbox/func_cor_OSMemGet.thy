theory func_cor_OSMemGet
  imports func_cor_other
begin
thm OSMemGet_pre_def

definition inv_OS_Mem_info_mp1 :: "State \<Rightarrow> OS_MEM_ref \<Rightarrow> bool"
  where "inv_OS_Mem_info_mp1 s p \<equiv> let mp = OS_MEM_info s p in
       OSMemNBlks mp \<ge> 0 \<and> OSMemNFree mp \<ge> 0 
     \<and> OSMemNBlks mp \<ge> OSMemNFree mp
     \<and> OSMemNFree mp = int (length (OSMemFreeList mp)) + 1   
"

definition inv_OS_Mem_info1 :: "State \<Rightarrow> OS_MEM_ref \<Rightarrow> bool"
  where "inv_OS_Mem_info1 s pmem \<equiv>  (inv_OS_Mem_info_mp1 s pmem)
         \<and>(\<forall> p \<in> OS_MEMs s - {pmem}. inv_OS_Mem_info_mp s p)"

definition inv1 :: "State \<Rightarrow> OS_MEM_ref \<Rightarrow> bool"
  where "inv1 s pmem \<equiv> inv_cur s \<and> inv_OS_Mem_info1 s pmem"
                        
definition Cond1 ::  "Thread \<Rightarrow> OS_MEM_ref \<Rightarrow> State set"
  where "Cond1 t pmem \<equiv> {s. inv1 s pmem}"

lemma stable_pmem :  "stable  \<lbrace>pmem \<in> \<acute>OS_MEMs\<rbrace> (OSMemGet_rely t)"
  by (simp add: stable_def OSMemGet_rely_def  gvars_conf_def gvars_conf_stable_def)

lemma OSMemGet_satRG_h1_cond1 : "inv V \<Longrightarrow> 
               \<turnstile>\<^sub>I (W\<acute>ret_mem := \<acute>ret_mem(t \<mapsto> hd (OSMemFreeList (\<acute>OS_MEM_info pmem)));;
              \<acute>OS_MEM_info := \<acute>OS_MEM_info(pmem := \<acute>OS_MEM_info pmem\<lparr>OSMemFreeList := 
               tl (OSMemFreeList (\<acute>OS_MEM_info pmem))\<rparr>);;
              \<acute>OS_MEM_info := \<acute>OS_MEM_info(pmem := \<acute>OS_MEM_info pmem\<lparr>OSMemNFree := 
               OSMemNFree (\<acute>OS_MEM_info pmem) - 1\<rparr>);;
              \<acute>ret := \<acute>ret (t := OS_ERR_NONE)) 
               sat\<^sub>p [{V\<lparr>ret_mem := (ret_mem V)(t := None)\<rparr>} \<inter> \<lbrace>\<acute>cur = Some t\<rbrace> \<inter> {Va} \<inter> {Vaa} \<inter>
                      \<lbrace>OS_ERR_NONE < OSMemNFree (\<acute>OS_MEM_info pmem)\<rbrace>, 
                      {(s, t). s = t}, UNIV, \<lbrace>\<acute>(Pair V) \<in> OSMemGet_guar t\<rbrace> \<inter> OSMemGet_post t]"
  apply (case_tac "{V\<lparr>ret_mem := (ret_mem V)(t := None)\<rparr>} \<inter> \<lbrace>\<acute>cur = Some t\<rbrace> \<inter> {Va} 
                   \<inter> {Vaa} \<inter> \<lbrace>OS_ERR_NONE < OSMemNFree (\<acute>OS_MEM_info pmem)\<rbrace> = {}")
   apply (simp add: Emptyprecond)
  apply (rule Seq[where mid = "{V\<lparr>ret_mem := (ret_mem V)(t := Some (hd (OSMemFreeList ((OS_MEM_info V) pmem)))),
                 OS_MEM_info := (OS_MEM_info V)(pmem := OS_MEM_info V pmem
                 \<lparr>OSMemFreeList := tl (OSMemFreeList (OS_MEM_info V pmem)),
                  OSMemNFree := OSMemNFree (OS_MEM_info V pmem) - 1\<rparr>)\<rparr>}"])
  apply (rule Seq[where mid = "{V\<lparr>ret_mem := (ret_mem V)(t := Some (hd (OSMemFreeList ((OS_MEM_info V) pmem)))),
                 OS_MEM_info := (OS_MEM_info V)(pmem := OS_MEM_info V pmem
                  \<lparr>OSMemFreeList := tl (OSMemFreeList (OS_MEM_info V pmem))\<rparr>)\<rparr>}"])
  apply (rule Seq[where mid = "{V\<lparr>ret_mem := (ret_mem V)(t := Some (hd (OSMemFreeList ((OS_MEM_info V) pmem))))\<rparr>}"])
     apply (rule Basic, simp add:OSMemGet_pre_def inv_def Cond1_def) 
         apply auto[1]
  using subset_UNIV apply blast
  using stable_id2 apply blast
     apply (simp add: stable_id2)
    apply (rule Basic)
       apply auto[1]
  using subset_UNIV apply blast
  using stable_id2 apply blast
  using stable_id2 apply blast
   apply (rule Basic)
      apply auto[1]
  using subset_UNIV apply blast
  using stable_id2 apply blast
  using stable_id2 apply blast
  apply (rule Basic)
     apply auto[1]
      apply (simp add: OSMemGet_guar_def, clarsimp)
      apply (rule conjI, simp add: gvars_conf_stable_def gvars_conf_def)
      apply (simp add: inv_def inv_cur_def inv_OS_Mem_info_def inv_OS_Mem_info_mp_def inv_thd_waitq_def)
      apply auto[1]
         apply meson 
        apply (smt One_nat_def int_ops(6) of_nat_1)
       apply (smt One_nat_def int_ops(6) of_nat_1)
      apply (simp add: lvars_nochange_def)
     apply (simp add: OSMemGet_post_def)
     apply (simp add: inv_def inv_cur_def inv_OS_Mem_info_def inv_OS_Mem_info_mp_def inv_thd_waitq_def)
     apply auto[1]
       apply meson
      apply (metis diff_mono diff_zero of_nat_0_le_iff of_nat_1)
  defer
  using stable_id2 apply blast
  using stable_id2 apply blast
  using stable_id2 apply blast
proof -
  assume a1: "OS_ERR_NONE < OSMemNFree (OS_MEM_info V pmem)"
  assume a2: "\<forall>p\<in>OS_MEMs V. let mp = OS_MEM_info V p in OS_ERR_NONE \<le> OSMemNBlks mp \<and> OS_ERR_NONE 
    \<le> OSMemNFree mp \<and> OSMemNFree mp \<le> OSMemNBlks mp \<and> OSMemNFree mp = int (length (OSMemFreeList mp))"
assume a3: "pmem \<in> OS_MEMs V"
  have "\<not> OSMemNFree (OS_MEM_info V pmem) < 1"
    using a1 by auto
  then show "OSMemNFree (OS_MEM_info V pmem) - 1 = int (length (OSMemFreeList (OS_MEM_info V pmem)) - Suc NULL)"
    using a3 a2 by (metis (no_types) One_nat_def int_ops(6) of_nat_1)
qed

lemma OSMemGet_satRG_h1_cond2:  "inv V \<Longrightarrow> 
     \<turnstile>\<^sub>I (W\<acute>ret := \<acute>ret (t := OS_ERR_TIMEOUT)) sat\<^sub>p 
     [{V\<lparr>ret_mem := (ret_mem V)(t := None)\<rparr>} \<inter> \<lbrace>\<acute>cur = Some t\<rbrace> \<inter> {Va} \<inter> {Vaa} \<inter>
      - \<lbrace>OS_ERR_NONE < OSMemNFree (\<acute>OS_MEM_info pmem)\<rbrace>, {(s, t). s = t}, UNIV, 
        \<lbrace>\<acute>(Pair V) \<in> OSMemGet_guar t\<rbrace> \<inter> OSMemGet_post t]"
  apply (rule Basic)
     apply auto[1]
      apply (simp add: OSMemGet_guar_def, clarsimp)
      apply (rule conjI, simp add: gvars_conf_stable_def gvars_conf_def)
      apply (simp add: inv_def inv_cur_def inv_OS_Mem_info_def inv_OS_Mem_info_mp_def inv_thd_waitq_def)
      apply auto[1]
      apply (simp add: lvars_nochange_def)
     apply (simp add: OSMemGet_post_def)
     apply (simp add: inv_def inv_cur_def inv_OS_Mem_info_def inv_OS_Mem_info_mp_def inv_thd_waitq_def)
  apply auto[1]
    apply simp
  using stable_id2 apply blast
  using stable_id2 apply blast
  done

lemma OSMemGet_satRG_h1: "  \<turnstile>\<^sub>I (W\<acute>ret_mem := \<acute>ret_mem(t := None);;
               AWAIT \<acute>cur = Some t THEN 
               Await UNIV
                (IF OS_ERR_NONE < OSMemNFree (\<acute>OS_MEM_info pmem)
                 THEN \<acute>ret_mem := \<acute>ret_mem(t \<mapsto> hd (OSMemFreeList (\<acute>OS_MEM_info pmem)));;
                      \<acute>OS_MEM_info := \<acute>OS_MEM_info
                      (pmem := \<acute>OS_MEM_info pmem\<lparr>OSMemFreeList := tl (OSMemFreeList (\<acute>OS_MEM_info pmem))\<rparr>);;
                      \<acute>OS_MEM_info := \<acute>OS_MEM_info(pmem := \<acute>OS_MEM_info pmem\<lparr>OSMemNFree := OSMemNFree (\<acute>OS_MEM_info pmem) - 1\<rparr>);;
                      \<acute>ret := \<acute>ret(t := OS_ERR_NONE)
                 ELSE \<acute>ret := \<acute>ret(t := OS_ERR_TIMEOUT)FI) 
               END) sat\<^sub>p [OSMemGet_pre t \<inter> \<lbrace>pmem \<in> \<acute>OS_MEMs\<rbrace> \<inter> \<lbrace>\<acute>cur = Some t\<rbrace> \<inter>
                           {V}, {(s, t). s = t}, UNIV, \<lbrace>\<acute>(Pair V) \<in> OSMemGet_guar t\<rbrace> \<inter> OSMemGet_post t]"
  apply (case_tac "\<not> inv V")
   apply (simp add: OSMemGet_pre_def  Emptyprecond)
  apply (rule Seq[where mid = "{V\<lparr>ret_mem := (ret_mem V)(t := None)\<rparr>}"])
   apply (rule Basic, simp add:OSMemGet_pre_def inv_def Cond1_def)
      apply (simp add: inv_cur_def inv1_def inv_OS_Mem_info_def inv_OS_Mem_info_mp_def inv_thd_waitq_def)
      apply auto[1]
     apply simp
    apply (simp add: stable_id2)
  apply (simp add: stable_id2)
  apply (rule Await)
    apply (simp add: stable_id2)
   apply (simp add: stable_id2, clarsimp)
  apply (rule Await)
  using stable_id2 apply blast
   apply (simp add: stable_id2, clarsimp)
  apply (rule Cond)
  using stable_id2 apply blast
    apply (simp add: OSMemGet_satRG_h1_cond1)
   apply (simp add: OSMemGet_satRG_h1_cond2)
  by simp

lemma OSMemGet_satRG: "\<Gamma> (OSMemGet t pmem) \<turnstile> OSMemGet_RGCond t"
  apply (simp add:Evt_sat_RG_def)
  apply (simp add:OSMemGet_def OSMemGet_RGCond_def)
  apply (rule BasicEvt)
  apply(simp add:body_def Pre\<^sub>f_def Post\<^sub>f_def guard_def
                 Rely\<^sub>f_def Guar\<^sub>f_def getrgformula_def)
    apply(unfold stm_def)[1]
    apply (rule Await)
      apply (simp add: OSMemGet_pre_stb stable_int2 stable_pmem)
  apply (simp add: OSMemGet_post_stb)
    apply (simp add: OSMemGet_satRG_h1)
  apply(simp add:body_def Pre\<^sub>f_def Post\<^sub>f_def guard_def
                  Rely\<^sub>f_def Guar\<^sub>f_def getrgformula_def)
  using OSMemGet_pre_stb apply simp
  apply (simp add:getrgformula_def OSMemGet_guar_def)
  apply(simp add:body_def Pre\<^sub>f_def Post\<^sub>f_def guard_def
                  Rely\<^sub>f_def Guar\<^sub>f_def getrgformula_def)
  done

end