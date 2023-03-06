section \<open>Concrete Syntax of PiCore-SIMP\<close>

theory picore_SIMP_Syntax 
imports picore_SIMP (*PiCore_RG_IFS *)

(*keywords "procedures" :: thy_decl*)

begin

syntax
  "_quote"     :: "'b \<Rightarrow> ('s \<Rightarrow> 'b)"                ("(\<guillemotleft>_\<guillemotright>)" [0] 1000)
  "_antiquote" :: "('s \<Rightarrow> 'b) \<Rightarrow> 'b"                ("\<acute>_" [1000] 1000)
  "_Assert"    :: "'s \<Rightarrow> 's set"                    ("(\<lbrace>_\<rbrace>)" [0] 1000)

translations
  "\<lbrace>b\<rbrace>" \<rightharpoonup> "CONST Collect \<guillemotleft>b\<guillemotright>"

parse_translation \<open>
  let
    fun quote_tr [t] = Syntax_Trans.quote_tr @{syntax_const "_antiquote"} t
      | quote_tr ts = raise TERM ("quote_tr", ts);
  in [(@{syntax_const "_quote"}, K quote_tr)] end
\<close>

definition Skip :: "'s com"  ("SKIP")
  where "SKIP \<equiv> Basic id"

abbreviation Wrap_prog :: "'s com \<Rightarrow> 's com option" ("W(_)" 0)
where "Wrap_prog p \<equiv> Some p"

notation Seq  ("(_;;/ _)" [60,61] 60)

(* denotate the syntex in RG-hoare here *)
syntax
rghoare_p :: "'Env \<Rightarrow> 'prog \<Rightarrow> ['s set, ('s \<times> 's) set, ('s \<times> 's) set, 's set] \<Rightarrow> bool"
    ("_ \<turnstile> _ sat\<^sub>p [_, _, _, _]" [60,60,0,0,0,0] 45)
rghoare_e :: "'Env \<Rightarrow> ('l,'k,'s,'prog) event \<Rightarrow> ['s set, ('s \<times> 's) set, ('s \<times> 's) set, 's set] \<Rightarrow> bool"
    ("_ \<turnstile> _ sat\<^sub>e [_, _, _, _]" [60,60,0,0,0,0] 45)
Evt_sat_RG:: "'Env \<Rightarrow> ('l,'k,'s,'prog) event \<Rightarrow> 's rgformula \<Rightarrow> bool" ("(_ _\<turnstile>_)" [60,60,60] 61)
rghoare_es :: "'Env \<Rightarrow> ('l,'k,'s,'prog) rgformula_ess \<Rightarrow> ['s set, ('s \<times> 's) set, ('s \<times> 's) set, 's set] \<Rightarrow> bool"
    ("_ \<turnstile> _ sat\<^sub>s [_, _, _, _]" [60,60,0,0,0,0] 45)
rghoare_pes :: "'Env \<Rightarrow> ('l,'k,'s,'prog) rgformula_par \<Rightarrow> ['s set, ('s \<times> 's) set, ('s \<times> 's) set, 's set] \<Rightarrow> bool"
          ("_ \<turnstile> _ SAT [_, _, _, _]" [60,60,0,0,0,0] 45)
Evt_sat_RG:: "'Env \<Rightarrow> ('l,'k,'s,'prog) event \<Rightarrow> 's rgformula \<Rightarrow> bool" ("(_ _\<turnstile>_)" [60,60,60] 61)
Esys_sat_RG :: "'Env \<Rightarrow> ('l,'k,'s,'prog) rgformula_ess \<Rightarrow> 's rgformula \<Rightarrow> bool" ("(_ _\<turnstile>\<^sub>e\<^sub>s_)" [60,60,60] 61)

syntax
  "_Assign"    :: "idt \<Rightarrow> 'b \<Rightarrow> 's com"                      ("(\<acute>_ :=/ _)" [70, 65] 61)
  "_Cond"      :: "'s bexp \<Rightarrow> 's com \<Rightarrow> 's com \<Rightarrow> 's com"  ("(0IF _/ THEN _/ ELSE _/FI)" [0, 0, 0] 61)
  "_Cond2"     :: "'s bexp \<Rightarrow> 's com \<Rightarrow> 's com"             ("(0IF _ THEN _ FI)" [0,0] 62(*56*))
  "_While"     :: "'s bexp \<Rightarrow> 's com \<Rightarrow> 's com"             ("(0WHILE _ /DO _ /OD)"  [0, 0] 61)
  "_Await"     :: "'s bexp \<Rightarrow> 's com \<Rightarrow> 's com"             ("(0AWAIT _ /THEN /_ /END)"  [0,0] 61)
  "_Atom"      :: "'s com \<Rightarrow> 's com"                        ("(0ATOMIC _ END)" 61)(*("(\<langle> _ \<rangle>)" 61)*)
  "_Wait"      :: "'s bexp \<Rightarrow> 's com"                       ("(0WAIT _ END)" 61)
  "_For"       :: "'s com \<Rightarrow> 's bexp \<Rightarrow> 's com \<Rightarrow> 's com \<Rightarrow> 's com" ("(0FOR _;/ _;/ _/ DO _/ ROF)")
  "_Event"     :: "['a, 'a, 'a] \<Rightarrow> ('l,'k,'s,'s com option) event" ("(EVENT _ WHEN _ THEN _ END)" [0,0,0] 61)
  "_Event2"     :: "['a, 'a] \<Rightarrow> ('l,'k,'s,'s com option) event" ("(EVENT _ THEN _ END)" [0,0] 61)
  "_Event_a"     :: "['a, 'a, 'a] \<Rightarrow> ('l,'k,'s,'s com option) event" ("(EVENT\<^sub>A _ WHEN _ THEN _ END)" [0,0,0] 61)

translations
  "\<acute>x := a" \<rightharpoonup> "CONST Basic \<guillemotleft>\<acute>(_update_name x (\<lambda>_. a))\<guillemotright>"
  "IF b THEN c1 ELSE c2 FI" \<rightharpoonup> "CONST Cond \<lbrace>b\<rbrace> c1 c2"
  "IF b THEN c FI" \<rightleftharpoons> "IF b THEN c ELSE SKIP FI"
  "WHILE b DO c OD" \<rightharpoonup> "CONST While \<lbrace>b\<rbrace> c"
  "AWAIT b THEN c END" \<rightleftharpoons> "CONST Await \<lbrace>b\<rbrace> c"
  (*"\<langle>c\<rangle>" \<rightleftharpoons> "AWAIT CONST True THEN c END"*)
  "ATOMIC c END" \<rightleftharpoons> "AWAIT CONST True THEN c END"
  "WAIT b END" \<rightleftharpoons> "AWAIT b THEN SKIP END"
  "FOR a; b; c DO p ROF" \<rightharpoonup> "a;; WHILE b DO p;;c OD"
  "EVENT l WHEN g THEN bd END" \<rightharpoonup> "CONST BasicEvent (l,(\<lbrace>g\<rbrace>, W(bd)))"
  "EVENT l THEN bd END" \<rightleftharpoons> "EVENT l WHEN CONST True THEN bd END"
  "EVENT\<^sub>A l WHEN g THEN bd END" \<rightleftharpoons> "EVENT l THEN (AWAIT g THEN bd END) END"

text \<open>Translations for variables before and after a transition:\<close>

syntax
  "_before" :: "id \<Rightarrow> 'a" ("\<ordmasculine>_")
  "_after"  :: "id \<Rightarrow> 'a" ("\<ordfeminine>_")

translations
  "\<ordmasculine>x" \<rightleftharpoons> "x \<acute>CONST fst"
  "\<ordfeminine>x" \<rightleftharpoons> "x \<acute>CONST snd"

print_translation \<open>
  let
    fun quote_tr' f (t :: ts) =
          Term.list_comb (f $ Syntax_Trans.quote_tr' @{syntax_const "_antiquote"} t, ts)
      | quote_tr' _ _ = raise Match;

    val assert_tr' = quote_tr' (Syntax.const @{syntax_const "_Assert"});

    fun bexp_tr' name ((Const (@{const_syntax Collect}, _) $ t) :: ts) =
          quote_tr' (Syntax.const name) (t :: ts)
      | bexp_tr' _ _ = raise Match;

    fun assign_tr' (Abs (x, _, f $ k $ Bound 0) :: ts) =
          quote_tr' (Syntax.const @{syntax_const "_Assign"} $ Syntax_Trans.update_name_tr' f)
            (Abs (x, dummyT, Syntax_Trans.const_abs_tr' k) :: ts)
      | assign_tr' _ = raise Match;
  in
   [(@{const_syntax Collect}, K assert_tr'),
    (@{const_syntax Basic}, K assign_tr'),
    (@{const_syntax Cond}, K (bexp_tr' @{syntax_const "_Cond"})),
    (@{const_syntax While}, K (bexp_tr' @{syntax_const "_While"}))]
  end
\<close>


lemma colltrue_eq_univ[simp]: "\<lbrace>True\<rbrace> = UNIV" by auto

end