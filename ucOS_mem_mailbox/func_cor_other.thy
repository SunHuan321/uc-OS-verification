theory func_cor_other
  imports rg_cond
begin

section \<open>Functional correctness of Schedule\<close>

lemma Schedule_satRG_h1: 
  "\<Gamma> \<turnstile>\<^sub>I Some (IF \<exists>y. \<acute>cur = Some y THEN \<acute>thd_state := \<acute>thd_state(the \<acute>cur := READY);; Basic (cur_update Map.empty) FI;;
           Basic (cur_update (\<lambda>_. Some t));;
           \<acute>thd_state := \<acute>thd_state
           (t := RUNNING)) sat\<^sub>p [\<lbrace>\<acute>inv\<rbrace> \<inter> \<lbrace>\<acute>thd_state t = READY\<rbrace> \<inter>
                                 {V}, {(s, t). s = t}, UNIV, \<lbrace>\<acute>(Pair V) \<in> Schedule_guar\<rbrace> \<inter> \<lbrace>\<acute>inv\<rbrace>]"
  apply(case_tac "\<lbrace>\<acute>inv \<rbrace> \<inter> \<lbrace> \<acute>thd_state t = READY\<rbrace> \<inter> {V} = {}")
    using Emptyprecond apply auto[1]
    apply simp
    apply(case_tac "\<exists>y. cur V = Some y")    
    apply(rule Seq[where mid = "{V\<lparr>thd_state := (thd_state V)(the (cur V) := READY)\<rparr>\<lparr>cur := None\<rparr>\<lparr>cur := Some t\<rparr>}"])
      apply(rule Seq[where mid = "{V\<lparr>thd_state := (thd_state V)(the (cur V) := READY)\<rparr>\<lparr>cur := None\<rparr>}"])
        apply(rule Cond)
          apply(simp add:stable_def)
          apply(rule Seq[where mid = "{V\<lparr>thd_state := (thd_state V)(the (cur V) := READY)\<rparr>}"])
          apply(rule Basic)
            apply auto[1]
            apply(simp add:stable_def)+
          apply(rule Basic)
            apply auto[1]
            apply(simp add:stable_def)+
          apply(simp add:Skip_def) apply(rule Basic) apply(simp add:stable_def)+
        apply(rule Basic)
         apply auto[1]
          apply(simp add:stable_def)+
        apply(rule Basic)
        apply(simp add:Schedule_guar_def)
        apply(subgoal_tac "inv (V\<lparr>cur := Some t, thd_state := (thd_state V)(the (cur V) := READY, t := RUNNING)\<rparr>) \<and>
               (\<forall>x. (V, V\<lparr>cur := Some t, thd_state := (thd_state V)(the (cur V) := READY, t := RUNNING)\<rparr>) \<in> lvars_nochange_rel x)")
         apply simp
        apply(rule conjI) apply(simp add: inv_def) apply clarify
         apply(rule conjI) apply(simp add: inv_cur_def) apply force
         apply (simp add: inv_OS_Mem_info_def inv_OS_Mem_info_mp_def inv_thd_waitq_def inv_thd_waitq_def)
         apply auto[1] using lvars_nochange_rel_def lvars_nochange_def apply simp
         apply (metis Thread_State_Type.distinct(5) inv_cur_def)
    apply (simp add: lvars_nochange_rel_def lvars_nochange_def, clarify)
       apply(simp add: stable_def)+
    apply(rule Seq[where mid = "{V\<lparr>cur := Some t\<rparr>}"])
      apply(rule Seq[where mid = "{V}"])
        apply(rule Cond)
          apply(simp add:stable_def)
          apply(rule Seq[where mid = "{}"])
          apply(rule Basic)
            apply auto[1]
            apply(simp add:stable_def)+
          apply(rule Basic)
            apply auto[1]
            apply(simp add:stable_def)+
          apply(simp add:Skip_def) apply(rule Basic) apply(simp add:stable_def)+
        apply(rule Basic)
         apply auto[1]
          apply(simp add:stable_def)+
         apply(rule Basic)
           apply(simp add:Schedule_guar_def)
           apply(subgoal_tac "inv (V\<lparr>cur := Some t, thd_state := (thd_state V)(t := RUNNING)\<rparr>) \<and>
              (\<forall>x. (V, V\<lparr>cur := Some t, thd_state := (thd_state V)(t := RUNNING)\<rparr>) \<in> lvars_nochange_rel x)")
        apply simp
        apply(rule conjI, simp add:inv_def) apply clarify
        apply(rule conjI, simp add:inv_cur_def)
        apply (rule conjI, simp add: inv_OS_Mem_info_def inv_OS_Mem_info_mp_def)
    apply (simp add: inv_thd_waitq_def) 
    apply auto[1]
       apply auto[1] using lvars_nochange_rel_def lvars_nochange_def apply simp
      apply(simp add:stable_def)+
    done

lemma Schedule_satRG: "\<Gamma> (Schedule t) \<turnstile> Schedule_RGCond t"
  apply(simp add:Evt_sat_RG_def) 
  apply (simp add: Schedule_def Schedule_RGCond_def)
  apply(rule BasicEvt)
    apply(simp add:body_def Pre\<^sub>f_def Post\<^sub>f_def guard_def
                  Rely\<^sub>f_def Guar\<^sub>f_def getrgformula_def)
    apply(rule Await)
  using stable_inv_sched_rely1 apply simp using stable_inv_sched_rely1 apply simp
      using Schedule_satRG_h1 apply simp   
    apply(simp add:Pre\<^sub>f_def Rely\<^sub>f_def getrgformula_def)
    using stable_inv_sched_rely1 apply simp
    by(simp add:Guar\<^sub>f_def getrgformula_def Schedule_guar_def)

section \<open>Functional correctness of Tick\<close>
lemma Tick_satRG: "\<Gamma> Tick \<turnstile> Tick_RGCond"
  apply(simp add:Evt_sat_RG_def) 
  apply (simp add: Tick_def Tick_RGCond_def Tick_rely_def Tick_guar_def)
  apply(rule BasicEvt)
    apply(simp add:body_def Pre\<^sub>f_def Post\<^sub>f_def guard_def
                  Rely\<^sub>f_def Guar\<^sub>f_def getrgformula_def)
    apply(rule Basic)
      apply simp
      using lvars_nochange_rel_def lvars_nochange_def apply simp apply auto[1]
      apply(simp add:stable_def)+
    apply(simp add: stable_def Pre\<^sub>f_def getrgformula_def Rely\<^sub>f_def) apply auto[1]
      by (simp add: Guar\<^sub>f_def getrgformula_def)

end