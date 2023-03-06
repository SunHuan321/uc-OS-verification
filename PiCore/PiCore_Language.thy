section \<open>Abstract Syntax of PiCore Language\<close>

theory PiCore_Language 
imports Main begin

type_synonym 's bexp = "'s set"

type_synonym 's guard = "'s set"

(* 'prog: the type of program command *)
type_synonym ('l,'s,'prog) event' = "'l \<times> ('s guard \<times> 'prog)"

definition guard :: "('l,'s,'prog) event' \<Rightarrow> 's guard" where
  "guard ev \<equiv> fst (snd ev)"

definition body :: "('l,'s,'prog) event' \<Rightarrow> 'prog" where
  "body ev \<equiv> snd (snd ev)"

datatype ('l,'k,'s,'prog) event =
      AnonyEvent "'prog" 
    | BasicEvent "('l,'s,'prog) event'" 

datatype ('l,'k,'s,'prog) esys = 
      EvtSeq "('l,'k,'s,'prog) event" "('l,'k,'s,'prog) esys"
    | EvtSys "('l,'k,'s,'prog) event set" 

type_synonym ('l,'k,'s,'prog) paresys = "'k \<Rightarrow> ('l,'k,'s,'prog) esys"

section \<open>Some Lemmas of Abstract Syntax\<close>

primrec is_basicevt :: "('l,'k,'s,'prog) event \<Rightarrow> bool"
  where "is_basicevt (AnonyEvent _) = False" |
        "is_basicevt (BasicEvent _) = True"

primrec is_anonyevt :: "('l,'k,'s,'prog) event \<Rightarrow> bool"
  where "is_anonyevt (AnonyEvent _) = True" |
        "is_anonyevt (BasicEvent _) = False"

lemma basicevt_isnot_anony: "is_basicevt e \<Longrightarrow> \<not> is_anonyevt e"
  by (metis event.exhaust is_anonyevt.simps(2) is_basicevt.simps(1)) 

lemma anonyevt_isnot_basic: "is_anonyevt e \<Longrightarrow> \<not> is_basicevt e"
  using basicevt_isnot_anony by auto

lemma evtseq_ne_es: "EvtSeq e es \<noteq> es"
  apply(induct es)
  apply auto[1]
  by simp

end