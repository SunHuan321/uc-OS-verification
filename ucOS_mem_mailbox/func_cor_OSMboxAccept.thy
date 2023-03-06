theory func_cor_OSMboxAccept
  imports rg_cond
begin

lemma OSMboxAccept_stable_pevent :  "stable \<lbrace>pevent \<in> \<acute>OSMailBoxs\<rbrace> (OSMboxAccept_rely t)"
  by (simp add: OSMboxAccept_rely_def gvars_conf_def gvars_conf_stable_def stable_def)

lemma OSMboxAccept_satRG_h1:"
   \<turnstile>\<^sub>I (W\<acute>get_msg := \<acute>get_msg(t := msgPtr (\<acute>OSMailbox_info pevent));;
               \<acute>OSMailbox_info := \<acute>OSMailbox_info
               (pevent :=
                  msgPtr_update Map.empty
                   (\<acute>OSMailbox_info
                     pevent))) sat\<^sub>p [OSMboxAccept_pre t \<inter> \<lbrace>pevent \<in> \<acute>OSMailBoxs\<rbrace> \<inter> \<lbrace>\<acute>cur = Some t\<rbrace> \<inter>
                                      {V}, {(x, y). x = y}, UNIV, \<lbrace>\<acute>(Pair V) \<in> OSMboxAccept_guar t\<rbrace> \<inter> OSMboxAccept_post t]"

apply(case_tac "OSMboxAccept_pre t \<inter> \<lbrace>pevent \<in> \<acute>OSMailBoxs\<rbrace> \<inter> \<lbrace>\<acute>cur = Some t\<rbrace> \<inter>
                                      {V} = {}")
     apply(simp add:Emptyprecond)   
  apply(rule Seq[where mid = "{V\<lparr>get_msg := (get_msg V)(t := msgPtr (OSMailbox_info V pevent))\<rparr>}"])
   apply(rule Basic)
      apply auto[1] 
    apply(simp add:stable_id2)
    apply(simp add:stable_id2)
  apply (simp add: stable_id2)
  apply(rule Basic)
     apply(simp add:OSMboxAccept_pre_def OSMboxAccept_guar_def gvars_conf_stable_def gvars_conf_def)
     apply (simp add: OSMboxAccept_post_def lvars_nochange_def)
     apply (simp add:  inv_def inv_cur_def inv_OS_Mem_info_def inv_OS_Mem_info_mp_def inv_thd_waitq_def)
  apply auto[1]
    apply simp
  apply(simp add:stable_id2)
  apply(simp add:stable_id2)
  done

lemma OSMboxAccept_satRG: "\<Gamma> (OSMboxAccept t pevent) \<turnstile> OSMboxAccept_RGCond t"
  apply (simp add:Evt_sat_RG_def)
  apply (simp add:OSMboxAccept_def OSMboxAccept_RGCond_def)
  apply(simp add:body_def Pre\<^sub>f_def Post\<^sub>f_def guard_def
                 Rely\<^sub>f_def Guar\<^sub>f_def getrgformula_def)
  apply(unfold stm_def)
  apply (rule BasicEvt)
     apply(simp add:body_def guard_def)
  apply(rule Await)
      apply (metis OSMboxAccept_pre_stable inf_set_def stable_int2 OSMboxAccept_stable_pevent)
  apply (simp add: OSMboxAccept_post_stable)
    apply auto
         apply(rule Await)
    apply(simp add:stable_id2)
  apply(simp add:stable_id2)
    apply auto
    apply(case_tac "{V} \<inter> {Va}={}")
   apply auto
     apply(simp add:Emptyprecond)      (* satRG_h1*)
    apply(simp add:OSMboxAccept_satRG_h1)
   apply(simp add:OSMboxAccept_pre_stable)
  apply(simp add:OSMboxAccept_guar_def)
  done

end