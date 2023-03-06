theory func_cor_OSMboxPost
  imports rg_cond
begin
  
lemma OSMboxPost_stable_pevent: "stable  \<lbrace>pevent \<in> \<acute>OSMailBoxs\<rbrace> (OSMboxPost_rely t)"
  by(simp add:OSMboxPost_pre_def OSMboxPost_rely_def stable_def gvars_conf_stable_def gvars_conf_def)              

lemma OSMboxPost_satRG_cond1_inv_stb : " \<lbrakk>inv V; cur V = Some t;  pevent \<in> OSMailBoxs V; 
                                         wait_q (OSMailbox_info V pevent) \<noteq> []\<rbrakk> \<Longrightarrow>
     inv  (V\<lparr>th := (th V)(t := hd (wait_q (OSMailbox_info V pevent))),
          tmout := (tmout V)(hd (wait_q (OSMailbox_info V pevent)) := OS_ERR_NONE),
          get_msg := get_msg V(hd (wait_q (OSMailbox_info V pevent)) \<mapsto> y),
          statPend := (statPend V)(hd (wait_q (OSMailbox_info V pevent)) := OS_STAT_PEND_OK),
          OSMailbox_info := (OSMailbox_info V)(pevent := OSMailbox_info V pevent\<lparr>wait_q := tl (wait_q (OSMailbox_info V pevent))\<rparr>),
          need_resched := (need_resched V)(t := True),
          cur := Some (SOME ta. ta \<noteq> hd (wait_q (OSMailbox_info V pevent)) \<longrightarrow> ta \<noteq> t \<longrightarrow> thd_state V ta = READY),
          thd_state := (thd_state V)
            (hd (wait_q (OSMailbox_info V pevent)) := READY, t := READY,
             SOME ta. ta \<noteq> hd (wait_q (OSMailbox_info V pevent)) \<longrightarrow> ta \<noteq> t \<longrightarrow> thd_state V ta = READY := RUNNING),
          ret := (ret V)(t := OS_ERR_NONE)\<rparr>)"
  apply (simp add: inv_def)
  apply (rule conjI, simp add: inv_cur_def)
   apply auto[1]
  apply (rule conjI, simp add: inv_OS_Mem_info_def inv_OS_Mem_info_mp_def)
  apply (simp add: inv_thd_waitq_def)
  apply auto
            apply (metis List.nth_tl Nitpick.size_list_simp(2) Suc_mono hd_conv_nth in_set_conv_nth 
            length_pos_if_in_set lessI list.set_sel(1) not_less_zero)
           apply (metis Thread_State_Type.distinct(5) inv_cur_def list.set_sel(2))
          apply (smt Thread_State_Type.distinct(3) list.set_sel(2) set_conv_nth tfl_some tl_def)
         apply (simp add: list.set_sel(2))
  using list.set_sel(1) apply blast
       apply (metis Thread_State_Type.distinct(5) inv_cur_def)
      apply (smt Thread_State_Type.distinct(3) set_conv_nth tfl_some)
     apply (metis hd_Cons_tl set_ConsD)
    apply (simp add: List.nth_tl Nitpick.size_list_simp(2))
   apply (meson list.set_sel(2))
  by (meson list.set_sel(2))


lemma OSMboxPost_satRG_cond1: "msg = Some y  \<Longrightarrow>
       \<turnstile>\<^sub>I (W\<acute>th := \<acute>th(t := hd (wait_q (\<acute>OSMailbox_info pevent)));; \<acute>tmout := \<acute>tmout(\<acute>th t := OS_ERR_NONE);;
              \<acute>get_msg := \<acute>get_msg(\<acute>th t \<mapsto> y);;
              \<acute>statPend := \<acute>statPend(\<acute>th t := OS_STAT_PEND_OK);;
              \<acute>OSMailbox_info := \<acute>OSMailbox_info(pevent := \<acute>OSMailbox_info pevent\<lparr>wait_q := tl (wait_q (\<acute>OSMailbox_info pevent))\<rparr>);;
              \<acute>thd_state := \<acute>thd_state(\<acute>th t := READY);;
              \<acute>need_resched := \<acute>need_resched(t := True);;
              IF \<acute>need_resched t THEN reschedule FI;;
              \<acute>ret := \<acute>ret (t := OS_ERR_NONE)) 
               sat\<^sub>p [OSMboxPost_pre t \<inter> \<lbrace>pevent \<in> \<acute>OSMailBoxs\<rbrace> \<inter> \<lbrace>\<acute>cur = Some t\<rbrace> \<inter> 
                {V} \<inter> {Va} \<inter> \<lbrace>wait_q (\<acute>OSMailbox_info pevent) \<noteq> []\<rbrace>, {(s, t). s = t}, UNIV, 
               \<lbrace>\<acute>(Pair V) \<in> OSMboxPost_guar t\<rbrace> \<inter> OSMboxPost_post t]"
  apply (case_tac "(wait_q (OSMailbox_info V pevent) = [])")
  apply (smt CollectD Emptyprecond Int_insert_right_if1 disjoint_iff_not_equal inf_bot_right singletonD)
  apply (case_tac "(pevent \<notin> OSMailBoxs V)")
   apply (simp add: Emptyprecond)
  apply (case_tac "V \<notin> OSMboxPost_pre t \<or> cur V \<noteq> Some t")
   apply (simp add: Emptyprecond, clarsimp)
  apply(simp add:reschedule_def)   
    \<comment> \<open>use this method to extract the assumption "wait_q (\<acute>OSMailbox_info pevent) \<noteq> []" \<close>
  apply(rule Seq[where mid = "let V9 = V\<lparr>th := (th V)(t := hd (wait_q (OSMailbox_info V pevent))), 
  tmout := (tmout V)(hd (wait_q (OSMailbox_info V pevent)) := OS_ERR_NONE),
 get_msg := get_msg V(hd (wait_q (OSMailbox_info V pevent)) \<mapsto> y),
                                    statPend := (statPend V)(hd (wait_q (OSMailbox_info V pevent))
                                     := OS_STAT_PEND_OK),
                                    OSMailbox_info := (OSMailbox_info V)(pevent := OSMailbox_info V 
                                    pevent\<lparr>wait_q := tl (wait_q (OSMailbox_info V pevent))\<rparr>),
                                    need_resched := (need_resched V)(t := True),
                                    thd_state := (thd_state V)(hd (wait_q (OSMailbox_info V pevent))  
                                    := READY, t := READY),
                                    cur := Some (SOME ta. ta \<noteq> hd (wait_q (OSMailbox_info V pevent)) \<longrightarrow>
                                    ta \<noteq> t \<longrightarrow> thd_state V ta = READY)\<rparr> in
                                    {V9\<lparr>thd_state := (thd_state V9)(the (cur V9) := RUNNING)\<rparr>}"]) 
   apply(rule Seq[where mid = "let V6 = V\<lparr>th := (th V)(t := hd (wait_q (OSMailbox_info V pevent))), 
                                   tmout := (tmout V)(hd (wait_q (OSMailbox_info V pevent)) := OS_ERR_NONE),
                                   get_msg := get_msg V(hd (wait_q (OSMailbox_info V pevent)) \<mapsto> y),
                                   statPend := (statPend V)(hd (wait_q (OSMailbox_info V pevent)) := 
                                   OS_STAT_PEND_OK),
                                   OSMailbox_info := (OSMailbox_info V)(pevent := OSMailbox_info V 
                                    pevent\<lparr>wait_q := tl (wait_q (OSMailbox_info V pevent))\<rparr>),
                                   thd_state := (thd_state V) (hd (wait_q (OSMailbox_info V pevent))
                                    :=  READY)\<rparr>  in
                                    {V6\<lparr>need_resched := (need_resched V6)( t := True)\<rparr>}"]) 
    apply(rule Seq[where mid = "let V5 = V\<lparr>th := (th V)(t := hd (wait_q (OSMailbox_info V pevent))), 
                                  tmout := (tmout V)(hd (wait_q (OSMailbox_info V pevent)) := OS_ERR_NONE),
                                  get_msg := get_msg V(hd (wait_q (OSMailbox_info V pevent)) \<mapsto> y),
                                  statPend := (statPend V)(hd (wait_q (OSMailbox_info V pevent)) := 
                                  OS_STAT_PEND_OK),
                                  OSMailbox_info := (OSMailbox_info V) (pevent := OSMailbox_info V pevent
                                  \<lparr>wait_q :=  tl (wait_q (OSMailbox_info V pevent))\<rparr>)\<rparr>  in
                                  {V5\<lparr>thd_state := (thd_state V5)((th V5) t := READY)\<rparr>}"]) 
     apply(rule Seq[where mid = "let V4 = V\<lparr>th := (th V)(t := hd (wait_q (OSMailbox_info V pevent))),
                                 tmout := (tmout V)(hd (wait_q (OSMailbox_info V pevent)) := OS_ERR_NONE),
                                 get_msg := get_msg V(hd (wait_q (OSMailbox_info V pevent)) \<mapsto> y),
                                 statPend := (statPend V)(hd (wait_q (OSMailbox_info V pevent)) := 
                                 OS_STAT_PEND_OK)\<rparr> in
                                 {V4\<lparr>OSMailbox_info := (OSMailbox_info V4)(pevent := OSMailbox_info 
                                  V4 pevent \<lparr>wait_q := tl (wait_q (OSMailbox_info V4 pevent))\<rparr>)\<rparr>} 
                                  (* \<inter> \<lbrace>wait_q (\<acute>OSMailbox_info pevent) \<noteq> []\<rbrace>*)"])  
      apply(rule Seq[where mid = "let V3 = V\<lparr>th := (th V)(t := hd (wait_q (OSMailbox_info V pevent))), 
                                  tmout := (tmout V)(hd (wait_q (OSMailbox_info V pevent)) := OS_ERR_NONE),
                                   get_msg := get_msg V(hd (wait_q (OSMailbox_info V pevent)) \<mapsto> y)\<rparr> 
                                   in  {V3\<lparr>statPend := (statPend V3)((th V3) t := OS_STAT_PEND_OK)\<rparr>} 
                                        \<inter> \<lbrace>wait_q (\<acute>OSMailbox_info pevent) \<noteq> []\<rbrace>"]) 
       apply(rule Seq[where mid = "let V2 = V\<lparr>th := (th V)(t := hd (wait_q (OSMailbox_info V pevent))), 
                                   tmout := (tmout V)(hd (wait_q (OSMailbox_info V pevent)) := OS_ERR_NONE)\<rparr> 
                                   in {V2\<lparr>get_msg := (get_msg V2)((th V2) t := msg)\<rparr>} \<inter> 
                                   \<lbrace>wait_q (\<acute>OSMailbox_info pevent) \<noteq> []\<rbrace>"]) 
        apply(rule Seq[where mid = "let V1 = V\<lparr>th := (th V)(t :=  hd (wait_q((OSMailbox_info V) pevent)))\<rparr> in
                                      {V1\<lparr>tmout := (tmout V1)((th V1) t := OS_ERR_NONE)\<rparr>} \<inter> 
                                      \<lbrace>wait_q (\<acute>OSMailbox_info pevent) \<noteq> []\<rbrace>"]) 
         apply(rule Seq[where mid = "{V\<lparr>th := (th V)(t :=  hd (wait_q((OSMailbox_info V) pevent)))\<rparr>} 
                                    \<inter> \<lbrace>wait_q (\<acute>OSMailbox_info pevent) \<noteq> []\<rbrace>"]) 
          apply(rule Basic) 
             apply auto 
           apply(simp add:stable_id2)  
          apply(simp add:stable_id2)
         apply(rule Basic)
            apply auto
          apply(simp add:stable_id2)
         apply(simp add:stable_id2)
        apply(rule Basic)
           apply auto
         apply(simp add:stable_id2) 
        apply(simp add:stable_id2)
       apply(rule Basic)
          apply auto
        apply(simp add:stable_id2) 
       apply(simp add:stable_id2)
      apply(rule Basic)
         apply auto
       apply(simp add:stable_id2)
      apply(simp add:stable_id2)
     apply(rule Basic)
        apply auto
      apply(simp add:stable_id2) 
     apply(simp add:stable_id2)
    apply(rule Basic)
       apply auto
     apply(simp add:stable_id2) 
    apply(simp add:stable_id2)
   apply(rule Cond)  
   apply(simp add:stable_id2)
     apply(rule Seq[where mid = "let V8 = V\<lparr>th := (th V)(t := hd (wait_q (OSMailbox_info V pevent))), 
                                tmout := (tmout V)(hd (wait_q (OSMailbox_info V pevent)) := OS_ERR_NONE),
                                    get_msg := get_msg V(hd (wait_q (OSMailbox_info V pevent)) \<mapsto> y),
                                    statPend := (statPend V)(hd (wait_q (OSMailbox_info V pevent)) 
                                    := OS_STAT_PEND_OK),
                                    OSMailbox_info := (OSMailbox_info V)(pevent := OSMailbox_info V 
                                    pevent\<lparr>wait_q := tl (wait_q (OSMailbox_info V pevent))\<rparr>),
                                    need_resched := (need_resched V)(t := True),
                                    thd_state := (thd_state V)
                                    (hd (wait_q (OSMailbox_info V pevent)) := READY, t := READY)\<rparr>  in
                                 {V8 \<lparr>cur :=  Some (SOME t. (thd_state V8) t = READY)\<rparr>}"]) 
      apply(rule Seq[where mid = "let V7 = V\<lparr>th := (th V)(t := hd (wait_q (OSMailbox_info V pevent))), 
                                  tmout := (tmout V)(hd (wait_q (OSMailbox_info V pevent)) := OS_ERR_NONE),
                                  get_msg := get_msg V(hd (wait_q (OSMailbox_info V pevent)) \<mapsto> y),
                                  statPend := (statPend V)(hd (wait_q (OSMailbox_info V pevent)) 
                                  := OS_STAT_PEND_OK),
                                  OSMailbox_info := (OSMailbox_info V)(pevent := OSMailbox_info V 
                                  pevent\<lparr>wait_q := tl (wait_q (OSMailbox_info V pevent))\<rparr>),
                                  thd_state := (thd_state V)(hd (wait_q (OSMailbox_info V pevent)) 
                                  := READY), need_resched := (need_resched V)(t := True)\<rparr>  in
                                  {V7  \<lparr>thd_state := (thd_state V7)((the (cur V7)) := READY)\<rparr>}"]) 
       apply(rule Basic) apply auto
       apply(simp add:stable_id2) apply(simp add:stable_id2)
     apply(rule Basic) apply auto
      apply(simp add:stable_id2) apply(simp add:stable_id2)
 apply(rule Basic) apply auto
     apply(simp add:stable_id2) apply(simp add:stable_id2)
   apply(simp add:Emptyprecond)
  apply(rule Basic)
     apply(simp add:OSMboxPost_pre_def OSMboxPost_post_def OSMboxPost_guar_def)
     apply (simp add: gvars_conf_stable_def gvars_conf_def)
     apply auto[1]
  using OSMboxPost_satRG_cond1_inv_stb apply blast
      apply (simp add: lvars_nochange_def)
     apply (simp add: OSMboxPost_satRG_cond1_inv_stb)
    apply (simp add: stable_id2)
   apply (simp add: stable_id2)
  apply (simp add: stable_id2)
  done

lemma OSMboxPost_satRG_cond2: "
    msg = Some y \<Longrightarrow>  \<turnstile>\<^sub>I (W IF \<exists>y. msgPtr (\<acute>OSMailbox_info pevent) = Some y 
                            THEN \<acute>ret := \<acute>ret(t := OS_ERR_MBOX_FULL)
                            ELSE \<acute>OSMailbox_info := \<acute>OSMailbox_info(pevent := \<acute>OSMailbox_info 
                            pevent\<lparr>msgPtr := Some y\<rparr>);; 
                            \<acute>ret := \<acute>ret(t := OK) 
                            FI) sat\<^sub>p  [OSMboxPost_pre t \<inter> \<lbrace>pevent \<in> \<acute>OSMailBoxs\<rbrace> \<inter> \<lbrace>\<acute>cur = Some t\<rbrace> \<inter> {V} \<inter> {Va} \<inter>
                         - \<lbrace>wait_q (\<acute>OSMailbox_info pevent) \<noteq> []\<rbrace>, {(s, t). s = t}, UNIV, 
                            \<lbrace>\<acute>(Pair V) \<in> OSMboxPost_guar t\<rbrace> \<inter> OSMboxPost_post t]"
  apply (case_tac "cur V \<noteq> Some t")
   apply (simp add: Emptyprecond)
  apply (case_tac "V \<notin> OSMboxPost_pre t")
  apply (simp add: Emptyprecond)
  apply (rule Cond)
    apply (simp add: stable_id2)
    apply (rule Basic)
       apply (simp add: OSMboxPost_guar_def gvars_conf_stable_def inv_def OSMboxPost_post_def 
       gvars_conf_def OSMboxPost_pre_def lvars_nochange_def)
          apply (simp add: inv_cur_def inv_OS_Mem_info_def inv_OS_Mem_info_mp_def inv_thd_waitq_def)
       apply auto[1]
      apply simp
     apply (simp add: stable_id2)
    apply (simp add: stable_id2)
   apply(rule Seq[where mid = "{V\<lparr> OSMailbox_info := (OSMailbox_info V)(pevent := OSMailbox_info V pevent\<lparr>msgPtr := Some y\<rparr>) \<rparr>}"])
    apply (rule Basic)
       apply (simp add: OSMboxPost_guar_def gvars_conf_stable_def inv_def OSMboxPost_post_def 
       gvars_conf_def OSMboxPost_pre_def lvars_nochange_def)
       apply (simp add: inv_cur_def inv_OS_Mem_info_def inv_OS_Mem_info_mp_def inv_thd_waitq_def)
       apply auto[1]
      apply simp
     apply (simp add: stable_id2)
    apply (simp add: stable_id2)
   apply (rule Basic)
      apply auto[1]
       apply (simp add: OSMboxPost_guar_def gvars_conf_stable_def inv_def OSMboxPost_post_def 
       gvars_conf_def OSMboxPost_pre_def lvars_nochange_def)
       apply (simp add: inv_cur_def inv_OS_Mem_info_def inv_OS_Mem_info_mp_def inv_thd_waitq_def)
       apply auto[1]
      apply (simp add: OSMboxPost_post_def OSMboxPost_pre_def)
      apply (simp add: inv_def inv_cur_def inv_OS_Mem_info_def inv_OS_Mem_info_mp_def inv_thd_waitq_def)
      apply auto[1]
     apply simp
    apply (simp add: stable_id2)
   apply (simp add: stable_id2)
  apply simp
  done

lemma OSMboxPost_satRG: "\<Gamma> (OSMboxPost t pevent msg) \<turnstile> OSMboxPost_RGCond t"
  apply (simp add:Evt_sat_RG_def)
  apply (simp add:OSMboxPost_def OSMboxPost_RGCond_def)
  apply(simp add:body_def Pre\<^sub>f_def Post\<^sub>f_def guard_def
                 Rely\<^sub>f_def Guar\<^sub>f_def getrgformula_def)
  apply(unfold stm_def)
  apply auto  
   apply (rule BasicEvt)
     apply(simp add:body_def guard_def)
     apply (rule Cond)
        apply (simp add: OSMboxPost_pre_stable OSMboxPost_stable_pevent stable_int2)
       apply (rule Await)
         apply (simp add: OSMboxPost_pre_stable OSMboxPost_stable_pevent stable_int2)
        apply (simp add: OSMboxPost_post_stable, clarsimp)
       apply (rule Basic)
     apply (simp add:guard_def OSMboxPost_guar_def gvars_conf_stable_def inv_def 
           OSMboxPost_post_def gvars_conf_def  OSMboxPost_pre_def lvars_nochange_def)
          apply (simp add: inv_cur_def inv_OS_Mem_info_def inv_OS_Mem_info_mp_def inv_thd_waitq_def)
          apply auto[1]
         apply simp                                           
        apply (simp add: stable_id2)
       apply (simp add: stable_id2)
      apply (simp add: Emptyprecond)
     apply (simp add: OSMboxPost_guar_def)
    apply (simp add: OSMboxPost_pre_stable)
   apply (simp add: OSMboxPost_guar_def) 
  apply (rule BasicEvt)
    apply(simp add:body_def guard_def)
    apply (rule Cond)
       apply (simp add: OSMboxPost_pre_stable OSMboxPost_stable_pevent stable_int2)
      apply (simp add: Emptyprecond)
     apply (rule Await)
       apply (simp add: OSMboxPost_pre_stable OSMboxPost_stable_pevent stable_int2)
      apply (simp add: OSMboxPost_post_stable, clarsimp)
     apply (rule Await)
       apply (simp add: stable_id2)
      apply (simp add: stable_id2, clarsimp)
     apply (rule Cond)
  using stable_id2 apply blast
       apply (simp add: OSMboxPost_satRG_cond1)
      apply (simp add: OSMboxPost_satRG_cond2)
     apply simp
    apply (simp add: OSMboxPost_guar_def)
   apply (simp add: OSMboxPost_pre_stable)
  apply (simp add: OSMboxPost_guar_def)
  done

end