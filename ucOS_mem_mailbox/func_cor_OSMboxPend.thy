theory func_cor_OSMboxPend
  imports rg_cond (* func_cor_lemma*)
begin                 

lemma OSMboxPend_stable_pevent:" stable  \<lbrace>pevent \<in> \<acute>OSMailBoxs\<rbrace> (OSMboxPend_rely t)"
  by(simp add:OSMboxPend_pre_def OSMboxPend_rely_def stable_def gvars_conf_stable_def gvars_conf_def)

lemma OSMboxPend_stable_endt: "stable  \<lbrace>\<acute>endt t = end\<rbrace> (OSMboxPend_rely t)"
 apply(simp add:stable_def, clarify)
  apply(simp add:OSMboxPend_rely_def gvars_conf_stable_def gvars_conf_def) 
  apply(simp add:stable_def OSMboxPend_rely_def lvars_nochange_rel_def gvars_conf_stable_def)
  apply(simp add:lvars_nochange_def)
  apply auto
  done

lemma OSMboxPend_stable_ret: "stable \<lbrace>\<acute>ret t = res\<rbrace> (OSMboxPend_rely t)"
 apply(simp add:stable_def, clarify)
  apply(simp add:OSMboxPend_rely_def gvars_conf_stable_def gvars_conf_def) 
  apply(simp add:stable_def OSMboxPend_rely_def lvars_nochange_rel_def gvars_conf_stable_def)
  apply(simp add:lvars_nochange_def)
  apply auto
  done

(*
lemma OSMboxPend_stable_statPend:" stable  \<lbrace>\<acute>statPend t = stat\<rbrace> (OSMboxPend_rely t)"
 apply(simp add:stable_def, clarify)
  apply(simp add:OSMboxPend_rely_def gvars_conf_stable_def gvars_conf_def) 
  apply(simp add:stable_def OSMboxPend_rely_def lvars_nochange_rel_def gvars_conf_stable_def)
  apply(simp add:timestat_nochange_rel_def timestat_nochange_def)
  apply auto
  done
*)

abbreviation " precond1 t pevent  \<equiv> OSMboxPend_pre t \<inter> \<lbrace>pevent \<in> \<acute>OSMailBoxs\<rbrace>" 
abbreviation " precond2 t pevent timeout \<equiv> precond1 t pevent " 
abbreviation " precond3 t pevent timeout \<equiv> precond2 t pevent timeout \<inter> \<lbrace>\<acute>endt t = NULL\<rbrace> "
abbreviation " precond4 t pevent timeout \<equiv> precond2 t pevent timeout "
abbreviation " precond5 t pevent timeout \<equiv> precond4 t pevent timeout \<inter> \<lbrace>\<acute>ret t = ETIMEOUT\<rbrace> "
abbreviation " precond6 t pevent timeout \<equiv> precond5 t pevent timeout "
abbreviation " precond7 t pevent timeout \<equiv> precond1 t pevent"
abbreviation " precond8 t  \<equiv> OSMboxPend_post t"

lemma precond1_to_precond2 :"  \<turnstile>\<^sub>I (W AWAIT \<acute>cur = Some t THEN \<acute>tmout := \<acute>tmout(t := timeout) 
           END) sat\<^sub>p [OSMboxPend_pre t \<inter>
                       \<lbrace>pevent \<in> \<acute>OSMailBoxs\<rbrace>, OSMboxPend_rely t, OSMboxPend_guar t,
                         OSMboxPend_pre t \<inter> \<lbrace>pevent \<in> \<acute>OSMailBoxs\<rbrace>]"
  apply(rule Await)
    apply (simp add: OSMboxPend_pre_stable OSMboxPend_stable_pevent stable_int2)
  apply (simp add: OSMboxPend_pre_stable OSMboxPend_stable_pevent stable_int2)
  apply auto[1]
  apply(rule Basic)
     apply auto[1]
       apply(simp add:OSMboxPend_guar_def OSMboxPend_pre_def gvars_conf_stable_def inv_OS_Mem_info_def
             lvars_nochange_def gvars_conf_def inv_def inv_cur_def inv_thd_waitq_def inv_OS_Mem_info_mp_def)
     apply(simp add:OSMboxPend_pre_def inv_def inv_cur_def inv_thd_waitq_def inv_OS_Mem_info_def
      inv_OS_Mem_info_mp_def)
  apply auto[1]
    apply(simp add:stable_id2)
   apply(simp add:stable_id2)
  apply (simp add: stable_id2)
  done


lemma precond2_to_precond3:" 
    \<turnstile>\<^sub>I (W AWAIT \<acute>cur = Some t THEN \<acute>endt := \<acute>endt(t := NULL) 
           END) sat\<^sub>p [OSMboxPend_pre t \<inter> \<lbrace>pevent \<in> \<acute>OSMailBoxs\<rbrace>, OSMboxPend_rely t, 
                      OSMboxPend_guar t, OSMboxPend_pre t \<inter> \<lbrace>pevent \<in> \<acute>OSMailBoxs\<rbrace> 
                      \<inter> \<lbrace>\<acute>endt t = NULL\<rbrace>]"
  apply(rule Await)
    apply (simp add: OSMboxPend_pre_stable OSMboxPend_stable_pevent stable_int2)
   apply (simp add: OSMboxPend_pre_stable OSMboxPend_stable_pevent OSMboxPend_stable_endt stable_int3)
  apply auto
  apply(rule Basic)
       apply(simp add:OSMboxPend_guar_def OSMboxPend_pre_def gvars_conf_stable_def inv_OS_Mem_info_def
             lvars_nochange_def gvars_conf_def inv_def inv_cur_def inv_thd_waitq_def inv_OS_Mem_info_mp_def)
  apply auto[1]
     apply(simp add:OSMboxPend_pre_def inv_def inv_cur_def inv_thd_waitq_def inv_OS_Mem_info_def
      inv_OS_Mem_info_mp_def)
    apply(simp add:stable_id2)
   apply(simp add:stable_id2)
  done

lemma precond3_to_precond4:"OK < timeout \<Longrightarrow>
    \<turnstile>\<^sub>I (W AWAIT \<acute>cur = Some t THEN Cond UNIV (\<acute>endt := \<acute>endt(t := \<acute>tick + nat timeout)) SKIP 
           END) sat\<^sub>p [OSMboxPend_pre t \<inter> \<lbrace>pevent \<in> \<acute>OSMailBoxs\<rbrace> \<inter> \<lbrace>\<acute>endt t = NULL\<rbrace>,
                       OSMboxPend_rely t, OSMboxPend_guar t, OSMboxPend_pre t \<inter> 
                       \<lbrace>pevent \<in> \<acute>OSMailBoxs\<rbrace>] "
  apply(rule Await)
    apply (simp add: OSMboxPend_pre_stable OSMboxPend_stable_pevent OSMboxPend_stable_endt stable_int3)
   apply (simp add: OSMboxPend_pre_stable OSMboxPend_stable_pevent  stable_int2)
  apply auto[1]
  apply(rule Cond)              
     apply(simp add:stable_id2)
    apply(rule Basic)
       apply(simp add:OSMboxPend_guar_def OSMboxPend_pre_def gvars_conf_stable_def inv_OS_Mem_info_def
       lvars_nochange_def gvars_conf_def inv_def inv_cur_def inv_thd_waitq_def inv_OS_Mem_info_mp_def)
       apply auto[1]
    apply(simp add:stable_id2)
     apply(simp add:stable_id2)
    apply(simp add:stable_id2)
   apply(simp add:Emptyprecond)
  apply simp
  done

lemma precond3_to_precond4_timout_less_OK:" \<not> OK < timeout \<Longrightarrow>
    \<turnstile>\<^sub>I (W AWAIT \<acute>cur = Some t THEN Cond {} (\<acute>endt := \<acute>endt(t := \<acute>tick)) SKIP 
           END) sat\<^sub>p [OSMboxPend_pre t \<inter> \<lbrace>pevent \<in> \<acute>OSMailBoxs\<rbrace> \<inter> \<lbrace>\<acute>endt t = NULL\<rbrace>, 
                      OSMboxPend_rely t, OSMboxPend_guar t, OSMboxPend_pre t \<inter> \<lbrace>pevent \<in> \<acute>OSMailBoxs\<rbrace> ] "
  apply(rule Await)
      apply (simp add: OSMboxPend_pre_stable OSMboxPend_stable_pevent OSMboxPend_stable_endt stable_int3)
  apply (simp add: OSMboxPend_pre_stable OSMboxPend_stable_pevent  stable_int2)
  apply auto[1]
   apply(rule Cond) 
     apply(simp add:stable_id2)
    apply(rule Basic)
 apply(simp add:OSMboxPend_guar_def OSMboxPend_pre_def gvars_conf_stable_def
             lvars_nochange_def gvars_conf_def inv_def inv_cur_def inv_thd_waitq_def)
      apply auto
    apply(simp add:stable_id2)
   apply(simp add:stable_id2)
  apply(simp add:Skip_def) 
  apply(rule Basic)
     apply auto[1]
    apply(simp add:OSMboxPend_pre_def OSMboxPend_guar_def)
   apply(simp add:stable_def)
   apply(simp add:stable_def)
  apply(simp add:stable_def)
  done

lemma precond4_to_precond5:"
    \<turnstile>\<^sub>I (W AWAIT \<acute>cur = Some t THEN \<acute>ret := \<acute>ret(t := ETIMEOUT) 
           END) sat\<^sub>p [OSMboxPend_pre t \<inter> \<lbrace>pevent \<in> \<acute>OSMailBoxs\<rbrace>, OSMboxPend_rely t, 
                      OSMboxPend_guar t, OSMboxPend_pre t \<inter> \<lbrace>pevent \<in> \<acute>OSMailBoxs\<rbrace> \<inter> \<lbrace>\<acute>ret t = ETIMEOUT\<rbrace>] "
  apply(rule Await)
    apply (simp add: OSMboxPend_pre_stable OSMboxPend_stable_pevent stable_int2)
      apply (simp add: OSMboxPend_pre_stable OSMboxPend_stable_pevent OSMboxPend_stable_ret stable_int3)
  apply auto[1]
  apply(rule Basic)
       apply(simp add:OSMboxPend_guar_def OSMboxPend_pre_def gvars_conf_stable_def inv_OS_Mem_info_def
       lvars_nochange_def gvars_conf_def inv_def inv_cur_def inv_thd_waitq_def inv_OS_Mem_info_mp_def)
     apply auto[1]
    apply(simp add:stable_id2)
   apply(simp add:stable_id2)
  apply(simp add:stable_id2)
  done

lemma precond5_to_precond6:"
    \<turnstile>\<^sub>I (W AWAIT \<acute>cur = Some t THEN \<acute>statPend := \<acute>statPend(t := OS_STAT_PEND_OK) 
           END) sat\<^sub>p [OSMboxPend_pre t \<inter> \<lbrace>pevent \<in> \<acute>OSMailBoxs\<rbrace> \<inter> \<lbrace>\<acute>ret t = ETIMEOUT\<rbrace>, 
                      OSMboxPend_rely t, OSMboxPend_guar t, OSMboxPend_pre t \<inter> 
                      \<lbrace>pevent \<in> \<acute>OSMailBoxs\<rbrace> \<inter> \<lbrace>\<acute>ret t = ETIMEOUT\<rbrace>] "
  apply(rule Await)
      apply (simp add: OSMboxPend_pre_stable OSMboxPend_stable_pevent OSMboxPend_stable_ret stable_int3)
      apply (simp add: OSMboxPend_pre_stable OSMboxPend_stable_pevent OSMboxPend_stable_ret stable_int3)
  apply auto[1]
  apply(rule Basic)
       apply(simp add:OSMboxPend_guar_def OSMboxPend_pre_def gvars_conf_stable_def inv_OS_Mem_info_def
       lvars_nochange_def gvars_conf_def inv_def inv_cur_def inv_thd_waitq_def inv_OS_Mem_info_mp_def)
  apply auto[1]
    apply(simp add:stable_id2)
   apply(simp add:stable_id2)
  apply(simp add:stable_id2)
  done

lemma test:"
         \<turnstile>\<^sub>I (W\<acute>get_msg := \<acute>get_msg(t := msgPtr (\<acute>OSMailbox_info pevent));; \<acute>ret := \<acute>ret(t := OK);;
                AWAIT \<acute>cur = Some t THEN \<acute>OSMailbox_info := \<acute>OSMailbox_info(pevent := msgPtr_update Map.empty (\<acute>OSMailbox_info pevent)) 
                END) sat\<^sub>p [OSMboxPend_pre t \<inter> \<lbrace>pevent \<in> \<acute>OSMailBoxs\<rbrace> \<inter> \<lbrace>\<acute>ret t = ETIMEOUT\<rbrace> \<inter> 
                          \<lbrace>\<acute>cur = Some t\<rbrace> \<inter>  {V} \<inter> - \<lbrace>pevent \<notin> \<acute>OSMailBoxs\<rbrace> \<inter> 
                            \<lbrace>\<exists>y. msgPtr (\<acute>OSMailbox_info pevent) =  Some y\<rbrace>, {(s, t). s = t}, UNIV, 
                            \<lbrace>\<acute>(Pair V) \<in> OSMboxPend_guar t\<rbrace> \<inter>  (OSMboxPend_pre t \<inter> \<lbrace>pevent \<in> \<acute>OSMailBoxs\<rbrace>)]
"
  apply(rule Seq [where mid =" let V2 = V\<lparr>get_msg := (get_msg V)(t := msgPtr (OSMailbox_info V pevent))\<rparr> in
                                                      precond1 t pevent  \<inter> {V2\<lparr>ret := (ret V2)(t := OK)\<rparr>} "])
   apply(rule Seq [where mid ="precond1 t pevent \<inter> {V\<lparr>get_msg := (get_msg V)(t := msgPtr (OSMailbox_info V pevent))\<rparr>}"])
  apply auto
  apply(rule Basic)
       apply auto
       apply(simp add:OSMboxPend_guar_def OSMboxPend_pre_def gvars_conf_stable_def inv_OS_Mem_info_def
       lvars_nochange_def gvars_conf_def inv_def inv_cur_def inv_thd_waitq_def inv_OS_Mem_info_mp_def)
      apply auto[1]
     apply(simp add:stable_id2)
    apply(simp add:stable_id2)
   apply(rule Basic)
      apply auto[1]
       apply(simp add:OSMboxPend_guar_def OSMboxPend_pre_def gvars_conf_stable_def inv_OS_Mem_info_def
       lvars_nochange_def gvars_conf_def inv_def inv_cur_def inv_thd_waitq_def inv_OS_Mem_info_mp_def)
     apply auto[1]
  apply(simp add:stable_id2)
    apply(simp add:stable_id2)
  apply (simp add: stable_id2)
  apply(rule Await)
  apply(simp add:stable_id2)
 apply(simp add:stable_id2)
  apply auto
  apply(rule Basic) apply auto
       apply(simp add:OSMboxPend_guar_def OSMboxPend_pre_def gvars_conf_stable_def inv_OS_Mem_info_def
       lvars_nochange_def gvars_conf_def inv_def inv_cur_def inv_thd_waitq_def inv_OS_Mem_info_mp_def)
     apply auto[1]
    apply(simp add:OSMboxPend_pre_def inv_def inv_cur_def inv_thd_waitq_def inv_OS_Mem_info_def
      inv_OS_Mem_info_mp_def) 
    apply auto[1]
  apply(simp add:stable_id2)
  apply(simp add:stable_id2)
  done
 
lemma mid:"  cur V = Some t \<Longrightarrow>
    pevent \<in> OSMailBoxs V \<Longrightarrow>
    V \<in> OSMboxPend_pre t \<Longrightarrow>
    msgPtr (OSMailbox_info V pevent) = None \<Longrightarrow>  cur (V\<lparr>thd_state := (thd_state V)(t := BLOCKED),
                             OSMailbox_info := (OSMailbox_info V)
                               (pevent := OSMailbox_info V pevent
                                  \<lparr>wait_q :=
                                     wait_q (OSMailbox_info V pevent) @
                                     [t]\<rparr>)\<rparr> ) \<noteq> Some t \<Longrightarrow>   (*It is critical that the cur V'\<noteq> t anymore *)
    V\<lparr>thd_state := (thd_state V)(t := BLOCKED),
                             OSMailbox_info := (OSMailbox_info V)
                               (pevent := OSMailbox_info V pevent
                                  \<lparr>wait_q :=
                                     wait_q (OSMailbox_info V pevent) @
                                     [t]\<rparr>)\<rparr> \<in> OSMboxPend_pre t "
  apply(simp add:OSMboxPend_pre_def)
  oops


lemma precond6_to_precond7_swap_ifbody_inv:"
          cur V = Some t \<Longrightarrow>
          pevent \<in> OSMailBoxs V \<Longrightarrow>
          ret V t = ETIMEOUT \<Longrightarrow>
          V \<in> OSMboxPend_pre t \<Longrightarrow>
          msgPtr (OSMailbox_info V pevent) = None \<Longrightarrow>
          (if ta = t then BLOCKED else thd_state V ta) = READY \<Longrightarrow>
          invariant.inv V \<Longrightarrow> invariant.inv
           (V\<lparr>OSMailbox_info := (OSMailbox_info V)(pevent := OSMailbox_info V pevent\<lparr>wait_q := wait_q 
            (OSMailbox_info V pevent) @ [t]\<rparr>),
                cur := Some (SOME ta. ta \<noteq> t \<and> (ta \<noteq> t \<longrightarrow> thd_state V ta = READY)),
                thd_state :=
                  \<lambda>x. if x = (SOME ta. ta \<noteq> t \<and> (ta \<noteq> t \<longrightarrow> thd_state V ta = READY)) then RUNNING
                      else thd_state
                            (V\<lparr>thd_state := (thd_state V)(t := BLOCKED),
                                 OSMailbox_info := (OSMailbox_info V)(pevent := OSMailbox_info V 
                                 pevent\<lparr>wait_q := wait_q (OSMailbox_info V pevent) @ [t]\<rparr>),
                                 cur := Some (SOME ta. (ta = t \<longrightarrow> BLOCKED = READY) \<and> (ta \<noteq> t \<longrightarrow> thd_state V ta = READY))\<rparr>)
                            x\<rparr>) "
  apply(subgoal_tac "thd_state V t = RUNNING")
   prefer 2 apply(simp add:inv_def inv_cur_def) apply auto[1]
  apply(subgoal_tac "ta \<noteq> t \<and> thd_state V ta = READY")
   prefer 2 apply auto[1] using Thread_State_Type.distinct(3) apply presburger
  apply(subgoal_tac "(SOME ta. ta \<noteq> t \<and> (ta \<noteq> t \<longrightarrow> thd_state V ta = READY)) \<noteq> t")
   prefer 2 using exE_some[where P="\<lambda>tb. tb \<noteq> t \<and> (tb \<noteq> t \<longrightarrow> thd_state V tb = READY)"
                    and c="SOME tb. tb \<noteq> t \<and> (tb \<noteq> t \<longrightarrow> thd_state V tb = READY)"] apply auto[1]
  apply(subgoal_tac "thd_state V (SOME ta. ta \<noteq> t \<and> (ta \<noteq> t \<longrightarrow> thd_state V ta = READY)) = READY")
    prefer 2 using exE_some[where P="\<lambda>tb. tb \<noteq> t \<and> (tb \<noteq> t \<longrightarrow> thd_state V tb = READY)"
                    and c="SOME tb. tb \<noteq> t \<and> (tb \<noteq> t \<longrightarrow> thd_state V tb = READY)"] apply auto[1]
  apply(simp add:inv_def)
  apply(rule conjI, simp add:inv_cur_def) 
  apply auto[1]
  apply (rule conjI, simp add: inv_OS_Mem_info_def inv_OS_Mem_info_mp_def) 
  apply auto[1]
  apply(simp add:inv_thd_waitq_def) 
  apply(rule conjI) 
   apply auto[1]
  apply(rule conjI) 
   apply auto[1]
  apply(rule conjI) 
   apply (metis (no_types, lifting) Thread_State_Type.distinct(5) diff_is_0_eq' 
                        less_Suc_eq less_Suc_eq_le nth_Cons_0 nth_append nth_mem)
  apply auto[1]
  done

lemma precond6_to_precond7_swap_inv2:"
          cur V = Some t \<Longrightarrow>
          pevent \<in> OSMailBoxs V \<Longrightarrow>
          ret V t = ETIMEOUT \<Longrightarrow>
          invariant.inv V \<Longrightarrow>
          msgPtr (OSMailbox_info V pevent) = None \<Longrightarrow>
          (if ta = t then BLOCKED else thd_state V ta) = READY \<Longrightarrow>
          invariant.inv
           (V\<lparr>OSMailbox_info := (OSMailbox_info V)(pevent := OSMailbox_info V pevent\<lparr>wait_q := wait_q (OSMailbox_info V pevent) @ [t]\<rparr>),
                cur := Some (SOME ta. ta \<noteq> t \<and> (ta \<noteq> t \<longrightarrow> thd_state V ta = READY)),
                thd_state :=
                  \<lambda>x. if x = (SOME ta. ta \<noteq> t \<and> (ta \<noteq> t \<longrightarrow> thd_state V ta = READY)) then RUNNING
                      else thd_state
                            (V\<lparr>thd_state := (thd_state V)(t := BLOCKED),
                                 OSMailbox_info := (OSMailbox_info V)(pevent := OSMailbox_info V pevent\<lparr>wait_q := wait_q (OSMailbox_info V pevent) @ [t]\<rparr>),
                                 cur := Some (SOME ta. (ta = t \<longrightarrow> BLOCKED = READY) \<and> (ta \<noteq> t \<longrightarrow> thd_state V ta = READY))\<rparr>)
                            x\<rparr>)"

  apply(subgoal_tac "thd_state V t = RUNNING")
    prefer 2 apply(simp add:inv_def inv_cur_def) apply auto[1]
  apply(subgoal_tac "ta \<noteq> t \<and> thd_state V ta = READY")
    prefer 2 apply auto[1] using Thread_State_Type.distinct(3) apply presburger 
  apply(subgoal_tac "(SOME ta. ta \<noteq> t \<and> (ta \<noteq> t \<longrightarrow> thd_state V ta = READY)) \<noteq> t")
    prefer 2 using exE_some[where P="\<lambda>tb. tb \<noteq> t \<and> (tb \<noteq> t \<longrightarrow> thd_state V tb = READY)"
                    and c="SOME tb. tb \<noteq> t \<and> (tb \<noteq> t \<longrightarrow> thd_state V tb = READY)"] apply auto[1]
  apply(subgoal_tac "thd_state V (SOME ta. ta \<noteq> t \<and> (ta \<noteq> t \<longrightarrow> thd_state V ta = READY)) = READY")
    prefer 2 using exE_some[where P="\<lambda>tb. tb \<noteq> t \<and> (tb \<noteq> t \<longrightarrow> thd_state V tb = READY)"
                    and c="SOME tb. tb \<noteq> t \<and> (tb \<noteq> t \<longrightarrow> thd_state V tb = READY)"] apply auto[1]

  apply(simp add:inv_def)
  apply(rule conjI, simp add:inv_cur_def) 
  apply auto[1]
  apply (rule conjI, simp add: inv_OS_Mem_info_def inv_OS_Mem_info_mp_def) 
  apply auto[1]
  apply(simp add:inv_thd_waitq_def) 
    apply(rule conjI) apply auto[1]
    apply(rule conjI) apply auto[1]
  apply(rule conjI) 
  apply (metis (no_types, lifting) Thread_State_Type.distinct(5) diff_is_0_eq' 
                        less_Suc_eq less_Suc_eq_le nth_Cons_0 nth_append nth_mem)
  apply auto[1]
  done 

lemma precond6_to_precond7_swap_inv3:" 
    cur V = Some t \<Longrightarrow>
    pevent \<in> OSMailBoxs V \<Longrightarrow>
    ret V t = ETIMEOUT \<Longrightarrow>
    V \<in> OSMboxPend_pre t \<Longrightarrow>
    msgPtr (OSMailbox_info V pevent) = None \<Longrightarrow>
    \<forall>ta. (if ta = t then BLOCKED else thd_state V ta) \<noteq> READY \<Longrightarrow>
    V \<noteq>
    cur_update Map.empty
     (V\<lparr>thd_state := (thd_state V)(t := BLOCKED),
          OSMailbox_info := (OSMailbox_info V)(pevent := OSMailbox_info V 
          pevent\<lparr>wait_q := wait_q (OSMailbox_info V pevent) @ [t]\<rparr>)\<rparr>) \<Longrightarrow>
    invariant.inv V \<Longrightarrow>
    invariant.inv
     (cur_update Map.empty
       (V\<lparr>thd_state := (thd_state V)(t := BLOCKED),
            OSMailbox_info := (OSMailbox_info V)(pevent := OSMailbox_info V
             pevent\<lparr>wait_q := wait_q (OSMailbox_info V pevent) @ [t]\<rparr>)\<rparr>))  "
  apply(subgoal_tac "thd_state V t = RUNNING")
    prefer 2 apply(simp add:inv_def inv_cur_def) apply auto[1]
  apply(simp add:inv_def)
  apply(rule conjI, simp add:inv_cur_def) 
   apply auto[1]
  apply(rule conjI, simp add: inv_OS_Mem_info_def inv_OS_Mem_info_mp_def) 
   apply auto[1]
  apply(simp add:inv_thd_waitq_def) 
  apply(rule conjI)
   apply auto
    apply (metis (no_types, lifting) Thread_State_Type.distinct(5) diff_is_0_eq' 
                        less_Suc_eq less_Suc_eq_le nth_Cons_0 nth_append nth_mem)
  done

lemma precond6_to_precond7_swap_inv4:"
    cur V = Some t \<Longrightarrow>
    pevent \<in> OSMailBoxs V \<Longrightarrow>
    ret V t = ETIMEOUT \<Longrightarrow>
    invariant.inv V \<Longrightarrow>
    msgPtr (OSMailbox_info V pevent) = None \<Longrightarrow>
    \<forall>ta. (if ta = t then BLOCKED else thd_state V ta) \<noteq> READY \<Longrightarrow>
    invariant.inv
     (cur_update Map.empty
       (V\<lparr>thd_state := (thd_state V)(t := BLOCKED),
            OSMailbox_info := (OSMailbox_info V)(pevent := OSMailbox_info V pevent\<lparr>wait_q := wait_q (OSMailbox_info V pevent) @ [t]\<rparr>)\<rparr>)) "
  apply(subgoal_tac "thd_state V t = RUNNING")
    prefer 2 apply(simp add:inv_def inv_cur_def) apply auto[1]
  apply(simp add:inv_def)
  apply(rule conjI, simp add:inv_cur_def) 
   apply auto[1]
  apply(rule conjI,  simp add: inv_OS_Mem_info_def inv_OS_Mem_info_mp_def) 
   apply auto[1]
  apply(simp add:inv_thd_waitq_def) 
  apply(rule conjI) 
   apply auto
    apply (metis (no_types, lifting) Thread_State_Type.distinct(5) diff_is_0_eq' 
                        less_Suc_eq less_Suc_eq_le nth_Cons_0 nth_append nth_mem)
  done

(*lemma key is the essential part in proof *)
lemma key:"     
         \<turnstile>\<^sub>I (W AWAIT \<acute>cur = Some t THEN 
                Await UNIV
                 (\<acute>thd_state := \<acute>thd_state(the \<acute>cur := BLOCKED);;
                  \<acute>OSMailbox_info := \<acute>OSMailbox_info(pevent := \<acute>OSMailbox_info pevent\<lparr>wait_q := wait_q (\<acute>OSMailbox_info pevent) @ [the \<acute>cur]\<rparr>);;
                  swap) 
                END) sat\<^sub>p [OSMboxPend_pre t \<inter> \<lbrace>pevent \<in> \<acute>OSMailBoxs\<rbrace> \<inter> \<lbrace>\<acute>ret t = ETIMEOUT\<rbrace> \<inter>
                            \<lbrace>\<acute>cur = Some t\<rbrace> \<inter> {V} \<inter> - \<lbrace>pevent \<notin> \<acute>OSMailBoxs\<rbrace> \<inter>
                            - \<lbrace>\<exists>y. msgPtr (\<acute>OSMailbox_info pevent) =  Some y\<rbrace>, 
                          {(s, t). s = t}, UNIV, \<lbrace>\<acute>(Pair V) \<in> OSMboxPend_guar t\<rbrace> 
                          \<inter> (OSMboxPend_pre t \<inter> \<lbrace>pevent \<in> \<acute>OSMailBoxs\<rbrace>)]"
  apply(rule Await)
    apply(simp add:stable_id2)
  apply(simp add:stable_id2)
  apply auto
  apply(rule Await)
  apply(simp add:stable_id2)
  apply(simp add:stable_id2)
  apply clarify
  apply(case_tac "OSMboxPend_pre t \<inter> \<lbrace>pevent \<in> \<acute>OSMailBoxs\<rbrace>  \<inter> \<lbrace>\<acute>ret t = ETIMEOUT\<rbrace> \<inter>
                           \<lbrace>\<acute>cur = Some t\<rbrace> \<inter> {V} \<inter> - \<lbrace>pevent \<notin> \<acute>OSMailBoxs\<rbrace> \<inter>
                           - \<lbrace>\<exists>y. msgPtr (\<acute>OSMailbox_info pevent) = Some y\<rbrace> \<inter>
                           \<lbrace>\<acute>cur = Some t\<rbrace> \<inter> {Va} \<inter>  UNIV \<inter> {Vaa} = {}")
   apply(simp add:Emptyprecond)
  apply auto
  apply(rule Seq [where mid ="let V2 = V\<lparr>thd_state := (thd_state V)(the (cur V) := BLOCKED)\<rparr> in {V2\<lparr>OSMailbox_info := (OSMailbox_info V2)(pevent := (OSMailbox_info V2 pevent)\<lparr>wait_q := (wait_q (OSMailbox_info V2 pevent))@ [the (cur V2)]\<rparr>)\<rparr>}"])
 apply(rule Seq [where mid ="{V\<lparr>thd_state := (thd_state V)(the (cur V) := BLOCKED)\<rparr>}"])apply auto
    apply(rule Basic)
       apply(simp add:OSMboxPend_pre_def inv_def inv_cur_def inv_thd_waitq_def)
       apply auto
     apply(simp add:stable_id2)
    apply(simp add:stable_id2)
   apply(rule Basic)
      apply auto
  apply(simp add:stable_id2)
   apply(simp add:stable_id2)
  apply(simp add:swap_def)
  apply(rule Cond)
     apply(simp add:stable_id2)
  apply(case_tac "{V\<lparr>thd_state := (thd_state V)(t := BLOCKED),
                                    OSMailbox_info := (OSMailbox_info V)(pevent := OSMailbox_info V 
                                    pevent\<lparr>wait_q := wait_q (OSMailbox_info V pevent) @ [t]\<rparr>)\<rparr>} \<inter>
                                    \<lbrace>\<exists>t. \<acute>thd_state t = READY\<rbrace>={} ")
     apply simp using Emptyprecond apply metis
      apply(rule subst[where t="{V\<lparr>thd_state := (thd_state V)(t := BLOCKED),
                                OSMailbox_info := (OSMailbox_info V)
                                  (pevent := OSMailbox_info V pevent\<lparr>wait_q := wait_q (OSMailbox_info V pevent) @ [t]\<rparr>)\<rparr>} \<inter>
                          \<lbrace>\<exists>t. \<acute>thd_state t = READY\<rbrace>" and s="{V\<lparr>thd_state := (thd_state V)(t := BLOCKED),
                                OSMailbox_info := (OSMailbox_info V)
                                  (pevent := OSMailbox_info V pevent\<lparr>wait_q := wait_q (OSMailbox_info V pevent) @ [t]\<rparr>)\<rparr>}"])
  apply simp
 apply(rule Seq [where mid ="let V3 = V\<lparr>thd_state := (thd_state V)(the (cur V) := BLOCKED),
                                    OSMailbox_info := (OSMailbox_info V)
                                      (pevent := OSMailbox_info V pevent\<lparr>wait_q := wait_q (OSMailbox_info V pevent) @ [the (cur V)]\<rparr>)\<rparr>
  in {V3\<lparr>cur := Some (SOME t. (thd_state V3) t = READY) \<rparr>}"])
     apply(rule Basic) (*\<acute>cur :=  Some (SOME t. \<acute>thd_state t =  READY)*)
        apply auto[1] apply simp apply(simp add:stable_def) apply(simp add:stable_def)
 apply(rule Basic) (* swap: \<acute>thd_state := \<acute>thd_state(the \<acute>cur := RUNNING) *)
        apply auto[1] 
        apply(simp add:OSMboxPend_guar_def)  (* \<in> Mem_pool_alloc_guar t *)
        apply(rule disjI1)
        apply(rule conjI)
          apply(simp add:gvars_conf_stable_def gvars_conf_def)
        apply(rule conjI)
  apply auto
       apply(simp add:precond6_to_precond7_swap_ifbody_inv)
  apply(simp add:lvars_nochange_def)
     apply(simp add:OSMboxPend_pre_def) 
     apply(simp add:precond6_to_precond7_swap_inv2)
    apply(simp add:stable_def)
  apply(simp add:stable_def)
  apply(rule Basic)
     apply auto
     apply(simp add:OSMboxPend_guar_def) (*\<in>OSMboxPend_guar *)
     apply auto
       apply(simp add:gvars_conf_stable_def gvars_conf_def)
  apply(simp add:precond6_to_precond7_swap_inv3)
     apply(simp add:lvars_nochange_def)
    apply(simp add:OSMboxPend_pre_def)
    apply(simp add:precond6_to_precond7_swap_inv4)
   apply(simp add:stable_id2)
  apply(simp add:stable_id2)
  done

lemma precond6_to_precond7:"
    \<turnstile>\<^sub>I (W AWAIT \<acute>cur = Some t THEN 
           IF pevent \<notin> \<acute>OSMailBoxs THEN \<acute>ret := \<acute>ret(t := ETIMEOUT)
           ELSE IF \<exists>y. msgPtr (\<acute>OSMailbox_info pevent) = Some y
                THEN \<acute>get_msg := \<acute>get_msg(t := msgPtr (\<acute>OSMailbox_info pevent));; \<acute>ret := \<acute>ret(t := OK);;
                     AWAIT \<acute>cur = Some t THEN \<acute>OSMailbox_info := \<acute>OSMailbox_info(pevent := msgPtr_update 
                            Map.empty (\<acute>OSMailbox_info pevent)) END
                ELSE AWAIT \<acute>cur = Some t THEN 
                     Await UNIV
                      (\<acute>thd_state := \<acute>thd_state(the \<acute>cur := BLOCKED);;
                       \<acute>OSMailbox_info := \<acute>OSMailbox_info(pevent := \<acute>OSMailbox_info pevent\<lparr>wait_q 
                        := wait_q (\<acute>OSMailbox_info pevent) @ [the \<acute>cur]\<rparr>);;
                       swap) 
                     END
                FI
           FI 
           END) sat\<^sub>p [OSMboxPend_pre t \<inter> \<lbrace>pevent \<in> \<acute>OSMailBoxs\<rbrace> \<inter> \<lbrace>\<acute>ret t = ETIMEOUT\<rbrace>, 
                      OSMboxPend_rely t, OSMboxPend_guar t, OSMboxPend_pre t \<inter> \<lbrace>pevent \<in> \<acute>OSMailBoxs\<rbrace>] "
  apply(rule Await)           (*pre6_to_pre7 *)
      apply (simp add: OSMboxPend_pre_stable OSMboxPend_stable_pevent OSMboxPend_stable_ret stable_int3)
  apply (simp add:  OSMboxPend_pre_stable OSMboxPend_stable_pevent  stable_int2)
       apply auto
       apply(rule Cond)
          apply(simp add:stable_id2)
         apply(rule Basic)
            apply(simp add:stable_def OSMboxPend_rely_def lvars_nochange_rel_def gvars_conf_stable_def)
            apply auto
         apply(simp add:stable_id2)
  apply(simp add:stable_id2)
       apply (rule Cond)
     apply(simp add:stable_id2) apply auto
        apply(simp add:test)
  apply(simp add:key)
  done

lemma precond7_to_precond8:"
 \<turnstile>\<^sub>I (W AWAIT \<acute>cur = Some t THEN Await UNIV (IF \<acute>statPend t = OS_STAT_PEND_OK THEN \<acute>ret := \<acute>ret(t := OK) ELSE \<acute>ret := \<acute>ret(t := OS_ERR_TIMEOUT)FI) 
           END) sat\<^sub>p [OSMboxPend_pre t \<inter> \<lbrace>pevent \<in> \<acute>OSMailBoxs\<rbrace>, OSMboxPend_rely t, OSMboxPend_guar t, OSMboxPend_post t] "
  apply(rule Await)
    apply (simp add: OSMboxPend_pre_stable OSMboxPend_stable_pevent stable_int2)
   apply(simp add: OSMboxPend_post_stable)
  apply auto[1]
  apply(rule Await)
    apply(simp add:stable_def)
   apply(simp add:stable_def)
  apply auto
  apply(rule Cond)
     apply(simp add:stable_def)
     apply auto
   apply(rule Basic)
      apply auto
      apply(simp add:OSMboxPend_guar_def)
      apply auto
        apply(simp add:gvars_conf_stable_def gvars_conf_def)
       apply(simp add:inv_def inv_cur_def inv_thd_waitq_def)
  apply (simp add: inv_OS_Mem_info_def inv_OS_Mem_info_mp_def)
       apply auto
  apply(simp add:lvars_nochange_def)
  apply(simp add:OSMboxPend_post_def)
  apply(simp add:inv_def inv_cur_def inv_thd_waitq_def)
  apply auto
           apply(simp add:OSMboxPend_pre_def inv_def inv_cur_def inv_thd_waitq_def)
           apply auto    
          apply(simp add:OSMboxPend_pre_def inv_def inv_cur_def inv_thd_waitq_def)
         apply(simp add:OSMboxPend_pre_def inv_def inv_cur_def inv_thd_waitq_def)
         apply (simp add: inv_OS_Mem_info_def inv_OS_Mem_info_mp_def)
        apply(simp add:OSMboxPend_pre_def inv_def inv_cur_def inv_thd_waitq_def)
       apply(simp add:OSMboxPend_pre_def inv_def inv_cur_def inv_thd_waitq_def)
      apply(simp add:OSMboxPend_pre_def inv_def inv_cur_def inv_thd_waitq_def)
     apply (simp add: OSMboxPend_pre_def inv_thd_waitq_def invariant.inv_def)
    apply(simp add:stable_def)
    apply(simp add:OSMboxPend_pre_def inv_def inv_cur_def inv_thd_waitq_def) 
    apply auto[1]
   apply(simp add:stable_def)
  apply(rule Basic)
     apply(simp add:OSMboxPend_pre_def OSMboxPend_post_def inv_def inv_cur_def inv_thd_waitq_def)
     apply (simp add: inv_OS_Mem_info_def inv_OS_Mem_info_mp_def)
     apply auto[1]
     apply(simp add:OSMboxPend_guar_def)
     apply auto[1]
       apply(simp add:gvars_conf_stable_def gvars_conf_def)
      apply(simp add:inv_def inv_cur_def inv_thd_waitq_def)
      apply (simp add: inv_OS_Mem_info_def inv_OS_Mem_info_mp_def)
  apply(simp add:lvars_nochange_def)
    apply(simp add:stable_def)
  using stable_id2 apply blast
  apply (simp add: stable_id2)
  done

lemma precond8_to_post:" \<turnstile>\<^sub>I (W IF \<acute>tmout t \<noteq>
              ETIMEOUT THEN AWAIT \<acute>cur = Some t THEN \<acute>tmout := \<acute>tmout(t := int (\<acute>endt t) - int \<acute>tick) END;;
                            IF \<acute>tmout t
                               < OK THEN AWAIT \<acute>cur = Some t THEN \<acute>ret := \<acute>ret(t := OS_ERR_TIMEOUT) 
                              END FI FI) sat\<^sub>p [OSMboxPend_post t, OSMboxPend_rely t, 
                             OSMboxPend_guar t, OSMboxPend_post t] "
  apply(rule Cond)
     apply (simp add: OSMboxPend_post_stable)
    apply (rule Seq [where mid = "precond8 t"])
     apply (rule_tac pre' = "precond8 t" and rely' = "OSMboxPend_rely t" and guar' = "OSMboxPend_guar t" 
      and post' = "precond8 t"  in  Conseq, simp_all)
     apply (rule Await)
       apply (simp add:  OSMboxPend_post_stable)
      apply (simp add: OSMboxPend_post_stable, clarify)
        apply(rule Basic)
        apply(simp add:OSMboxPend_guar_def)
        apply auto[1]
            apply(simp add:gvars_conf_stable_def gvars_conf_def)
         apply(simp add:inv_def inv_cur_def inv_thd_waitq_def inv_OS_Mem_info_def 
          inv_OS_Mem_info_mp_def)
            apply auto[1]
         apply(simp add:lvars_nochange_def)
        apply (simp add: OSMboxPend_post_def inv_def inv_OS_Mem_info_def inv_OS_Mem_info_mp_def 
              inv_cur_def inv_thd_waitq_def)
          apply auto[1]
         apply(simp add:stable_def)
      apply(simp add:stable_def)
  apply (simp add: stable_id2)
    apply(rule Cond)
       apply(simp add:OSMboxPend_post_stable)
  apply (rule_tac pre' = "precond8 t" and rely' = "OSMboxPend_rely t" and guar' = "OSMboxPend_guar t"
         and post' = "precond8 t" in Conseq, simp_all)
      apply(rule Await)
        apply(simp add:OSMboxPend_post_stable)
         apply(simp add:OSMboxPend_post_stable, clarsimp)
      apply(rule Basic)
         apply(simp add:OSMboxPend_guar_def)
         apply auto[1]
            apply(simp add:gvars_conf_stable_def gvars_conf_def)
           apply(simp add:inv_def inv_cur_def inv_thd_waitq_def)
           apply (simp add: inv_OS_Mem_info_def inv_OS_Mem_info_mp_def)
           apply auto[1]
           apply(simp add:lvars_nochange_def)
          apply(simp add:OSMboxPend_post_def)
         apply(simp add:inv_def inv_cur_def inv_thd_waitq_def)
         apply (simp add: inv_OS_Mem_info_def inv_OS_Mem_info_mp_def)
          apply auto[1]
         apply(simp add:stable_def)
       apply(simp add:stable_def)
      apply (simp add: stable_id2) 
     apply(simp add:Skip_def)
  apply (rule_tac pre' = "precond8 t" and rely' = "OSMboxPend_rely t" and guar' = "OSMboxPend_guar t"
         and post' = "precond8 t" in Conseq, simp_all)
     apply(rule Basic)
        apply auto[1]
       apply(simp add:OSMboxPend_guar_def)
       apply auto[1]
      apply(simp add:OSMboxPend_post_stable)
  apply(simp add:OSMboxPend_post_stable)
    apply(simp add:OSMboxPend_guar_def)
   apply(simp add:Skip_def)
  apply (rule_tac pre' = "precond8 t" and rely' = "OSMboxPend_rely t" and guar' = "OSMboxPend_guar t"
         and post' = "precond8 t" in Conseq, simp_all)
   apply(rule Basic)
      apply auto[1]
     apply(simp add:OSMboxPend_guar_def)
     apply auto[1]
    apply(simp add:OSMboxPend_post_stable)
  apply(simp add:OSMboxPend_post_stable)
     apply(simp add:OSMboxPend_guar_def)
  done

lemma OSMboxPend_satRG: "\<Gamma> (OSMboxPend t pevent timeout) \<turnstile> OSMboxPend_RGCond t"
  apply (simp add:Evt_sat_RG_def)
  apply (simp add:OSMboxPend_def OSMboxPend_RGCond_def)
  apply(simp add:body_def Pre\<^sub>f_def Post\<^sub>f_def guard_def
                 Rely\<^sub>f_def Guar\<^sub>f_def getrgformula_def)
  apply(unfold stm_def)
    apply auto  apply (rule BasicEvt)
     apply(simp add:body_def guard_def)
      apply(rule Seq [where mid ="precond8 t"])
       apply(rule Seq [where mid ="precond7 t pevent timeout"])
        apply(rule Seq [where mid ="precond6 t pevent timeout"])
         apply(rule Seq [where mid ="precond5 t pevent timeout"])
          apply(rule Seq [where mid ="precond4 t pevent timeout"])
           apply(rule Seq [where mid ="precond3 t pevent timeout"])
            apply(rule Seq [where mid ="precond2 t pevent timeout"])
             apply(simp add:precond1_to_precond2)
            apply(simp add:precond2_to_precond3)
          apply(simp add:precond3_to_precond4)
         apply(simp add:precond4_to_precond5)
        apply(simp add:precond5_to_precond6)
       apply(simp add:precond6_to_precond7)
      apply(simp add:precond7_to_precond8)
     apply(simp add:precond8_to_post)
  apply (simp add: OSMboxPend_pre_stable)
   apply(simp add:OSMboxPend_guar_def)
    apply (rule BasicEvt)
     apply(simp add:body_def guard_def)
      apply(rule Seq [where mid ="precond8 t"])
       apply(rule Seq [where mid ="precond7 t pevent timeout"])
        apply(rule Seq [where mid ="precond6 t pevent timeout"])
         apply(rule Seq [where mid ="precond5 t pevent timeout"])
          apply(rule Seq [where mid ="precond4 t pevent timeout"])
           apply(rule Seq [where mid ="precond3 t pevent timeout"])
            apply(rule Seq [where mid ="precond2 t pevent timeout"])
           apply(simp add:precond1_to_precond2)
            apply(simp add:precond2_to_precond3)
         apply(simp add:precond3_to_precond4_timout_less_OK)
         apply(simp add:precond4_to_precond5)
        apply(simp add:precond5_to_precond6)
       apply(simp add:precond6_to_precond7)
      apply(simp add:precond7_to_precond8)
     apply(simp add:precond8_to_post)
  apply(simp add:OSMboxPend_pre_stable)
  apply(simp add:OSMboxPend_guar_def)
  done

end