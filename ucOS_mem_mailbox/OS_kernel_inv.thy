theory OS_kernel_inv
  imports OS_kernel_sys 
begin

section \<open> invariant verification \<close>

theorem "invariant_presv_pares \<Gamma> inv (paresys_spec Memory_manage_system_Spec) {s0} sys_rely"
  apply(rule invariant_theorem[where G="sys_guar" and pst = UNIV])
  using mem_sys_sat apply fast
    apply(simp add:sys_rely_def stable_def)
    apply(simp add:sys_guar_def)
   apply(rule stable_un_R) 
    apply(rule stable_un_R)
     apply (simp add: sched_guar_stb_inv stable_def)
    apply (simp add: Tick_guar_stb_inv stable_def)
  apply (simp add: OSMemGet_guar_stb_inv OSMem_eq_guar stable_un_S)
  using s0_inv apply simp
  done
                     
end                      