theory func_cor_OSMemPut
  imports func_cor_other
begin

lemma OSMemPut_satRG1: " \<turnstile>\<^sub>I (W\<acute>OS_MEM_info := \<acute>OS_MEM_info(pmem := \<acute>OS_MEM_info pmem\<lparr>OSMemFreeList := pblk # OSMemFreeList (\<acute>OS_MEM_info pmem)\<rparr>);;
              \<acute>OS_MEM_info := \<acute>OS_MEM_info(pmem := \<acute>OS_MEM_info pmem\<lparr>OSMemNFree := OSMemNFree (\<acute>OS_MEM_info pmem) + 1\<rparr>);;
              \<acute>ret := \<acute>ret
              (t := OS_ERR_NONE)) sat\<^sub>p [OSMemPut_pre t \<inter> \<lbrace>pmem \<in> \<acute>OS_MEMs\<rbrace> \<inter> \<lbrace>\<acute>cur = Some t\<rbrace> \<inter> {V} \<inter> {Va} \<inter>
                                         - \<lbrace>OSMemNBlks (\<acute>OS_MEM_info pmem)
                                            \<le> OSMemNFree
                                                (\<acute>OS_MEM_info pmem)\<rbrace>, {(s, t). s = t}, UNIV, \<lbrace>\<acute>(Pair V) \<in> OSMemPut_guar t\<rbrace> \<inter> OSMemPut_post t]"
  apply (case_tac "OSMemPut_pre t \<inter> \<lbrace>pmem \<in> \<acute>OS_MEMs\<rbrace> \<inter> \<lbrace>\<acute>cur = Some t\<rbrace> \<inter> {V} \<inter> {Va} \<inter>
                                         - \<lbrace>OSMemNBlks (\<acute>OS_MEM_info pmem)
                                            \<le> OSMemNFree
                                                (\<acute>OS_MEM_info pmem)\<rbrace> = {}")
  using Emptyprecond apply auto[1]
   apply (simp add: Emptyprecond)
  apply (rule Seq[where mid = "{V\<lparr>OS_MEM_info := (OS_MEM_info V)(pmem := OS_MEM_info V
                                  pmem \<lparr>OSMemFreeList := pblk # OSMemFreeList (OS_MEM_info V pmem),
                                  OSMemNFree := OSMemNFree (OS_MEM_info V pmem) + 1\<rparr>)\<rparr>}"])
   apply (rule Seq[where mid = " {V\<lparr>OS_MEM_info := (OS_MEM_info V)(pmem := OS_MEM_info V
                                  pmem\<lparr>OSMemFreeList := pblk # OSMemFreeList (OS_MEM_info V pmem)\<rparr>)\<rparr>}"])
    apply (rule Basic)
        apply(simp add:OSMemPut_pre_def inv_def)
       apply (simp add: inv_cur_def)
       apply (simp add:inv_OS_Mem_info_def inv_OS_Mem_info_mp_def)
  apply clarify
     apply (simp add: stable_id2)
     apply (simp add: stable_id2)
  using stable_id2 apply blast
   apply (rule Basic)
        apply(simp add:OSMemPut_pre_def inv_def)
     apply (simp add: inv_cur_def)
  using stable_id2 apply blast
  using stable_id2 apply blast
  apply (rule Basic)
     apply (simp add: OSMemPut_guar_def)
     apply (case_tac "cur V \<noteq> Some t")
      apply auto
       apply (simp add: gvars_conf_stable_def gvars_conf_def)
       apply (simp add: inv_def inv_cur_def  inv_OS_Mem_info_def inv_OS_Mem_info_mp_def inv_thd_waitq_def)
      apply auto
        apply meson
       apply smt
      apply meson
     apply (simp add: lvars_nochange_def)
    apply (simp add: OSMemPut_pre_def OSMemPut_post_def)
    apply (simp add: inv_def  inv_cur_def inv_OS_Mem_info_def inv_OS_Mem_info_mp_def inv_thd_waitq_def)
    apply auto
      apply meson
     apply smt
     apply meson
   apply (simp add: stable_id2)
  by (simp add: stable_id2)

lemma OSMemPut_satRG: "\<Gamma> (OSMemPut t pmem pblk) \<turnstile> OSMemPut_RGCond t"
  apply (simp add:Evt_sat_RG_def)
  apply (simp add:OSMemPut_def OSMemPut_RGCond_def)
  apply (rule BasicEvt)
  apply(simp add:body_def Pre\<^sub>f_def Post\<^sub>f_def guard_def
                 Rely\<^sub>f_def Guar\<^sub>f_def getrgformula_def)
    apply(unfold stm_def)[1]
    apply(rule Await)
      apply (simp add: OSMemPut_pre_def OSMemPut_rely_def gvars_conf_def gvars_conf_stable_def stable_def)
     apply (simp add: OSMemPut_post_def stable_inv_free_rely1)
    apply (rule allI)
    apply(rule Await)
      apply (simp add: stable_id2)
     apply (simp add: stable_id2)
    apply (rule allI)
    apply (rule Cond)
  using stable_id2 apply blast
  apply (rule Basic)
     apply (simp add: OSMemPut_post_def OSMemPut_guar_def)
     apply(simp add:gvars_nochange_def lvars_nochange_def)
     apply(simp add:inv_def inv_cur_def gvars_conf_stable_def)
     apply(simp add:inv_OS_Mem_info_def inv_OS_Mem_info_mp_def inv_thd_waitq_def)
     apply auto
       apply (simp add: gvars_conf_def)
  using OSMemPut_pre_def inv_cur_def invariant.inv_def apply blast
     apply (simp add: OSMemPut_pre_def inv_cur_def inv_def)
           apply (simp add: OSMemPut_pre_def inv_OS_Mem_info_def inv_OS_Mem_info_mp_def inv_def inv_thd_waitq_def)
  using OSMemPut_pre_def inv_thd_waitq_def invariant.inv_def apply blast
         apply (simp add: OSMemPut_pre_def inv_thd_waitq_def invariant.inv_def)
  using OSMemPut_pre_def inv_thd_waitq_def invariant.inv_def apply blast
  using OSMemPut_pre_def inv_thd_waitq_def invariant.inv_def apply blast
  using stable_id2 apply blast
     apply (simp add: stable_id2)
  using OSMemPut_satRG1 apply simp
  apply(simp add:body_def Pre\<^sub>f_def Post\<^sub>f_def guard_def
                  Rely\<^sub>f_def Guar\<^sub>f_def getrgformula_def)
  using OSMemPut_pre_stb apply simp
  apply (simp add:getrgformula_def OSMemPut_guar_def)
  apply(simp add:body_def Pre\<^sub>f_def Post\<^sub>f_def guard_def
                  Rely\<^sub>f_def Guar\<^sub>f_def getrgformula_def)
  done

end