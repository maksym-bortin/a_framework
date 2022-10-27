(* *********************************************************************

    Theory SmallSteps.thy is part of a framework for modelling,
    verification and transformation of concurrent imperative
    programs. Copyright (c) 2021  M. Bortin

    The framework is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
    For more details see the license agreement (LICENSE) you should have
    received along with the framework.
    
   ******************************************************************* *)

theory SmallSteps
imports LA
begin


section "The fine-grained (small) computation steps"

type_synonym 's config = "'s LA \<times> 's"


abbreviation stateOf :: "'s config \<times> bool \<Rightarrow> 's"
  where "stateOf cf \<equiv> snd(fst cf)"

abbreviation progOf :: "'s config \<times> bool \<Rightarrow> 's LA"
  where "progOf cf \<equiv> fst(fst cf)"

abbreviation tkOf :: "'s config \<times> bool \<Rightarrow> bool"
  where "tkOf cf \<equiv> snd(cf)"



definition estep :: "'s config \<Rightarrow> 's config \<Rightarrow> bool"
                   ("\<turnstile> (_ -e\<rightarrow>/ _)" [81,81] 100)
                   where
"(\<turnstile> cf -e\<rightarrow> cf') = (fst cf = fst cf')"

lemma estep_eq[simp] :
"(\<turnstile> (p, s) -e\<rightarrow> (p', t)) = (p = p')"
  by(simp add: estep_def)

(* \<rho> is a 'code retrieving' function *)
inductive pstep :: "(nat \<Rightarrow> 's LA) \<Rightarrow> 's config \<Rightarrow> 's config \<Rightarrow> bool"
                        ("_ \<turnstile> (_ -p\<rightarrow>/ _)" [81,81,81] 100)
for \<rho> :: "nat \<Rightarrow> 's LA" 
where
  Basic : "\<rho> \<turnstile> (Basic f, s) -p\<rightarrow> (Skip, f s)"
| 
  CJumpT : "s \<in> C \<Longrightarrow>
            \<rho> \<turnstile> (CJUMP C TO j OTHERWISE p END, s) -p\<rightarrow> (\<rho> j, s)"
| 
  CJumpF : "s \<notin> C \<Longrightarrow>
            \<rho> \<turnstile> (CJUMP C TO j OTHERWISE p END, s) -p\<rightarrow> (p, s)"
|
  Seq : "\<rho> \<turnstile> (p\<^sub>1, s) -p\<rightarrow> (p\<^sub>1',s') \<Longrightarrow> 
         \<rho> \<turnstile> (p\<^sub>1;p\<^sub>2, s) -p\<rightarrow> (p\<^sub>1';p\<^sub>2, s')"
| 
  SeqSkip : "\<rho> \<turnstile> (SKIP;p, s) -p\<rightarrow> (p, s)"
| 
  CondT :  "s \<in> C \<Longrightarrow> \<rho> \<turnstile> (IF C THEN p ELSE q FI, s) -p\<rightarrow> (p, s)"
| 
  CondF :  "s \<notin> C \<Longrightarrow> \<rho> \<turnstile> (IF C THEN p ELSE q FI, s) -p\<rightarrow> (q, s)"
| 
  WhileT : "s \<in> C \<Longrightarrow> \<rho> \<turnstile> (WHILE C \<lbrakk>inv: I\<rbrakk> DO p SUBSEQUENTLY q OD, s) -p\<rightarrow> 
                          (p ; (SKIP ; WHILE C \<lbrakk>inv: I\<rbrakk> DO p SUBSEQUENTLY q OD), s)"
| 
  WhileF : "s \<notin> C \<Longrightarrow> \<rho> \<turnstile> (WHILE C \<lbrakk>inv: I\<rbrakk> DO p SUBSEQUENTLY q OD, s) -p\<rightarrow> (q, s)"
| 
  Parallel : "\<rho> \<turnstile> (fst(ps!i), s) -p\<rightarrow> (p, s') \<Longrightarrow> i < length ps \<Longrightarrow>
              \<rho> \<turnstile> (Parallel ps, s) -p\<rightarrow> (Parallel (ps[i := (p, snd(ps!i))]), s')"

| 
  ParallelSkip : "\<forall>p \<in> set ps. fst p = SKIP \<Longrightarrow> 
                  \<rho> \<turnstile> (Parallel ps, s) -p\<rightarrow> (SKIP, s)"
| 
  Await : "s \<in> C \<Longrightarrow> (pstep \<rho>)\<^sup>*\<^sup>* (p, s) (SKIP, t) \<Longrightarrow> 
           \<rho> \<turnstile> (AWAIT C \<lbrakk> ann: a \<rbrakk> THEN p END, s) -p\<rightarrow> (SKIP, t)"


abbreviation 
 "pstep_rtrancl" :: "(nat \<Rightarrow> 's LA) \<Rightarrow> 's config \<Rightarrow> 's config \<Rightarrow> bool"
                                ("_ \<turnstile> (_ -p\<rightarrow>\<^sup>*/ _)" [81,81,81] 100)
 where
  "\<rho> \<turnstile> cf0 -p\<rightarrow>\<^sup>* cf1 \<equiv> (pstep \<rho>)\<^sup>*\<^sup>* cf0 cf1"

abbreviation 
 "pstep_N" :: "(nat \<Rightarrow> 's LA) \<Rightarrow> 's config \<Rightarrow> nat \<Rightarrow> 's config \<Rightarrow> bool"
                                ("_ \<turnstile> (_ -p\<rightarrow>\<^sup>_/ _)" [81,81,82,81] 100)
 where
  "\<rho> \<turnstile> cf0 -p\<rightarrow>\<^sup>N cf1 \<equiv> (CONST pstep \<rho> ^^ N) cf0 cf1"



section "Some properties"


lemma pstep_Jump :
"\<rho> \<turnstile> (Jump i, s) -p\<rightarrow> (\<rho> i, s)"
  apply(simp add: Jump_def)
  apply(rule pstep.CJumpT, simp)
  done


lemma jumpfree_pstep' :
"\<rho> \<turnstile> cf -p\<rightarrow> cf' \<Longrightarrow>
 jumpfree (fst cf) \<Longrightarrow>
 jumpfree (fst cf')"
  apply(induct cf cf' rule: pstep.induct, simp_all)
  apply clarsimp
  apply(drule mem_nth)
  apply clarify
  apply(rename_tac j)
  apply(case_tac "i=j", simp)
  apply simp
  apply(drule_tac n=j in nth_mem)
  apply(drule bspec, assumption)
  apply(drule sym, clarsimp)
  done

corollary jumpfree_pstep :
"\<rho> \<turnstile> (p, s) -p\<rightarrow> (q, t) \<Longrightarrow>
 jumpfree p \<Longrightarrow>
 jumpfree q"
  by(drule jumpfree_pstep', simp_all)



lemma Skip_pstep :
"\<rho> \<turnstile> (SKIP, s) -p\<rightarrow> (p, t) \<Longrightarrow> P"
  by(erule pstep.cases, simp_all)

lemma Skip_pstepsN :
"\<rho> \<turnstile> (SKIP, s) -p\<rightarrow>\<^sup>n (p, t) \<Longrightarrow> n = 0"
  apply(induct n arbitrary: p t, clarsimp+)
  apply(drule meta_spec, drule meta_spec, drule meta_mp, assumption)
  apply clarsimp
  by(erule Skip_pstep)


lemma Skip_psteps :
"\<rho> \<turnstile> (SKIP, s) -p\<rightarrow>\<^sup>* (p, t) \<Longrightarrow> p = SKIP \<and> s = t"
  apply(subst (asm) rtranclp_power, clarify)
  apply(frule Skip_pstepsN)
  by simp


lemma Basic_pstep :
"\<rho> \<turnstile> (Basic f, s) -p\<rightarrow> (p', t) \<Longrightarrow> p' = SKIP \<and> t = f s"    
  by(erule pstep.cases, simp_all)  

 

lemma CJump_pstep :
"\<rho> \<turnstile> (CJUMP C TO j OTHERWISE p END, s) -p\<rightarrow> (p', t) \<Longrightarrow>
 s = t \<and> ((s \<in> C \<and> p' = \<rho> j) \<or> (s \<notin> C \<and> p' = p))"
  by(erule pstep.cases, simp_all)  

lemma Jump_pstep :
"\<rho> \<turnstile> (JUMP j, s) -p\<rightarrow> (p', t) \<Longrightarrow> 
 p' = \<rho> j \<and> s = t"
  apply(simp add: Jump_def)
  by(drule CJump_pstep, simp)


lemma Cond_pstep :
"\<rho> \<turnstile> (IF C THEN p ELSE q FI, s) -p\<rightarrow> (p', t) \<Longrightarrow>
 s = t \<and> ((s \<in> C \<and> p' = p) \<or> (s \<notin> C \<and> p' = q))"
  by(erule pstep.cases, simp_all)

lemma While_pstep :
"\<rho> \<turnstile> (WHILE C \<lbrakk>inv: I\<rbrakk> DO p SUBSEQUENTLY q OD, s) -p\<rightarrow> (p', t) \<Longrightarrow>  
  s = t \<and> ((s \<in> C \<and> p' = p ; (SKIP ; WHILE C \<lbrakk>inv: I\<rbrakk> DO p SUBSEQUENTLY q OD)) \<or>
           (s \<notin> C \<and> p' = q))"
  by(erule pstep.cases, simp_all)

lemma Seq_pstep :
"\<rho> \<turnstile> (p\<^sub>1 ; p\<^sub>2, s) -p\<rightarrow> (p', t) \<Longrightarrow> 
 p\<^sub>1 \<noteq> SKIP \<Longrightarrow> 
 \<exists>p\<^sub>1'. \<rho> \<turnstile> (p\<^sub>1, s) -p\<rightarrow> (p\<^sub>1', t) \<and> p' = p\<^sub>1' ; p\<^sub>2"
  by(erule pstep.cases, simp_all)

    
lemma Seq_pstep_Skip :
"\<rho> \<turnstile> (SKIP ; p, s) -p\<rightarrow> (p', t) \<Longrightarrow> 
 p' = p \<and> s = t"
  apply(erule pstep.cases, simp_all)
  by(erule Skip_pstep)


lemma Parallel_pstep :
"\<rho> \<turnstile> (Parallel ps, s) -p\<rightarrow> (p', t) \<Longrightarrow> 
(\<exists>i < length ps. \<exists>p''. \<rho> \<turnstile> (fst(ps!i), s) -p\<rightarrow> (p'', t) \<and> 
                p' = Parallel (ps[i := (p'', snd(ps!i))])) \<or>
((\<forall>p \<in> set ps. fst p = SKIP) \<and> p' = SKIP \<and> s = t)"
  apply(erule pstep.cases, simp_all)
  by fast

lemma Parallel_pstep_Skip :
"\<rho> \<turnstile> (Parallel ps, s) -p\<rightarrow> (p', t) \<Longrightarrow> 
 \<forall>p \<in> set ps. fst p = SKIP \<Longrightarrow> p' = SKIP \<and> s = t"
  apply(drule Parallel_pstep)
  apply(erule disjE, clarsimp)
   apply(erule Skip_pstep)
  by clarsimp


lemma Parallel_pstep_to_Skip :
"\<rho> \<turnstile> (Parallel ps, s) -p\<rightarrow> (SKIP, t) \<Longrightarrow> 
      s = t \<and> (\<forall>p \<in> set ps. fst p = Skip)"
  by(erule pstep.cases, simp_all)


lemma Await_pstep :
"\<rho> \<turnstile> (AWAIT C \<lbrakk> ann: a \<rbrakk> THEN p END, s) -p\<rightarrow> (p', t) \<Longrightarrow>
 s \<in> C \<and> \<rho> \<turnstile> (p, s) -p\<rightarrow>\<^sup>* (SKIP, t) \<and> p' = SKIP"
  by(erule pstep.cases, simp_all)



end