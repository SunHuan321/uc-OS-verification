section \<open>Lemmas of Picore-SIMP\<close>

theory picore_SIMP_lemma
imports "picore_SIMP_Syntax" "picore_SIMP"

begin

lemma id_belong[simp]: "Id \<subseteq>\<lbrace>\<ordfeminine>x= \<ordmasculine>x\<rbrace>"
  by (simp add: Collect_mono Id_fstsnd_eq)

lemma allpre_eq_pre: "(\<forall>v\<in>U. \<turnstile>\<^sub>I P sat\<^sub>p [{v}, rely, guar, post]) \<longleftrightarrow> \<turnstile>\<^sub>I P sat\<^sub>p [U, rely, guar, post]"
  apply auto using Allprecond apply blast
  using Conseq[of _ _ rely rely guar guar post post P] by auto

lemma sat_pre_imp_allinpre: " \<turnstile>\<^sub>I P sat\<^sub>p [U, rely, guar, post] \<Longrightarrow> v\<in>U \<Longrightarrow> \<turnstile>\<^sub>I P sat\<^sub>p [{v}, rely, guar, post]"
  using Conseq[of _ _ rely rely guar guar post post P] by auto

lemma stable_int_col2: "stable \<lbrace>s\<rbrace> r \<Longrightarrow> stable \<lbrace>t\<rbrace> r \<Longrightarrow> stable \<lbrace>s \<and> t\<rbrace> r"
  by auto

lemma stable_int_col3: "stable \<lbrace>k\<rbrace> r \<Longrightarrow> stable \<lbrace>s\<rbrace> r \<Longrightarrow> stable \<lbrace>t\<rbrace> r \<Longrightarrow> stable \<lbrace>k \<and> s \<and> t\<rbrace> r"
  by auto

lemma stable_int_col4: "stable \<lbrace>m\<rbrace> r \<Longrightarrow> stable \<lbrace>k\<rbrace> r \<Longrightarrow> stable \<lbrace>s\<rbrace> r 
  \<Longrightarrow> stable \<lbrace>t\<rbrace> r \<Longrightarrow> stable \<lbrace>m \<and> k \<and> s \<and> t\<rbrace> r"
  by auto

lemma stable_int_col5: "stable \<lbrace>q\<rbrace> r \<Longrightarrow> stable \<lbrace>m\<rbrace> r \<Longrightarrow>  stable \<lbrace>k\<rbrace> r 
  \<Longrightarrow> stable \<lbrace>s\<rbrace> r \<Longrightarrow> stable \<lbrace>t\<rbrace> r \<Longrightarrow> stable \<lbrace>q \<and> m \<and> k \<and> s \<and> t\<rbrace> r"
  by auto

lemma stable_un2: "stable s r \<Longrightarrow> stable t r \<Longrightarrow> stable (s \<union> t) r"
  by (simp add: stable_def)

lemma stable_un_R: "stable s r \<Longrightarrow> stable s r' \<Longrightarrow> stable s (r \<union> r')"
  by (meson UnE stable_def)  

lemma stable_un_S: "\<forall>t. stable s (P t) \<Longrightarrow> stable s (\<Union>t. P t)" 
apply(simp add:stable_def) by auto

lemma stable_un_S2: "\<forall>t x. stable s (P t x) \<Longrightarrow> stable s (\<Union>t x. P t x)" 
apply(simp add:stable_def) by auto

lemma pairv_IntI:
"y \<in> \<lbrace>\<acute>(Pair V) \<in> A\<rbrace> \<Longrightarrow> y \<in> \<lbrace>\<acute>(Pair V) \<in> B\<rbrace> \<Longrightarrow> y \<in> \<lbrace>\<acute>(Pair V) \<in> A \<inter> B\<rbrace>"
by auto

lemma pairv_rId:
"y \<in> \<lbrace>\<acute>(Pair V) \<in> A\<rbrace> \<Longrightarrow> y \<in> \<lbrace>\<acute>(Pair V) \<in> A \<union> Id\<rbrace>"
by auto

end