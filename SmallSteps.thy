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


abbreviation confOf :: "'s config \<times> bool \<Rightarrow> 's config"
  where "confOf cf \<equiv> fst(cf)"

abbreviation progOf :: "'s config \<times> bool \<Rightarrow> 's LA"
  where "progOf cf \<equiv> fst(confOf cf)"

abbreviation stateOf :: "'s config \<times> bool \<Rightarrow> 's"
  where "stateOf cf \<equiv> snd(confOf cf)"

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
"\<rho> \<turnstile> cf -p\<rightarrow> cf' \<Longrightarrow> jumpfree (fst cf) \<Longrightarrow>
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
"\<rho> \<turnstile> (p, s) -p\<rightarrow> (q, t) \<Longrightarrow> jumpfree p \<Longrightarrow>
 jumpfree q"
  by(drule jumpfree_pstep', simp_all)


lemma jumpfree_locally_seq_pstep' :
"\<rho> \<turnstile> cf -p\<rightarrow> cf' \<Longrightarrow> jumpfree (fst cf) \<Longrightarrow> locally_seq (fst cf) \<Longrightarrow>
 locally_seq (fst cf')"
  by(induct cf cf' rule: pstep.induct, simp_all)

corollary jumpfree_locally_seq_pstep :
"\<rho> \<turnstile> (p, s) -p\<rightarrow> (q, t) \<Longrightarrow> jumpfree p \<Longrightarrow> locally_seq p \<Longrightarrow>
 locally_seq q"
  by(drule jumpfree_locally_seq_pstep', simp_all)



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


lemma locally_seq_jumpfree_pstep_unq_aux :
"(\<lambda>x1 x2. \<rho> \<turnstile> x1 -p\<rightarrow> x2 \<and> (\<forall>a b. \<rho> \<turnstile> x1 -p\<rightarrow> (a, b) \<longrightarrow> locally_seq (fst x1) \<longrightarrow> jumpfree (fst x1) \<longrightarrow> x2 = (a, b)))\<^sup>*\<^sup>* cf cf' \<Longrightarrow>
 \<rho> \<turnstile> cf -p\<rightarrow>\<^sup>* cf'' \<Longrightarrow> 
 locally_seq (fst cf) \<Longrightarrow>
 jumpfree (fst cf) \<Longrightarrow>
 fst cf' = Skip \<Longrightarrow>
 fst cf'' = Skip \<Longrightarrow>
 cf' = cf''"
  apply(induct cf arbitrary: cf'' rule: converse_rtranclp_induct)
   apply(case_tac cf', clarsimp)
   apply(subst (asm) rtranclp_power)
   apply clarify
   apply(case_tac n, clarsimp)
   apply clarify
   apply(erule relpowp_Suc_E2)
   apply(clarsimp, erule Skip_pstep)
  apply clarify
  apply(rename_tac p1 s1 p2 s2 p3 s3)
  apply(drule_tac x=p3 in meta_spec)
  apply(drule_tac x=s3 in meta_spec)
  apply(drule meta_mp)
   apply(subst (asm) rtranclp_power)+
   apply clarify
   apply(rename_tac m)
   apply(case_tac m)
    apply(thin_tac "\<forall>a. _ a")
    apply clarsimp
    apply(erule Skip_pstep)
   apply clarify
   apply(rename_tac m')
   apply(erule relpowp_Suc_E2, clarify)
   apply(rename_tac p s)
   apply(drule_tac x=p in spec, drule_tac x=s in spec)
   apply clarsimp
   apply(subst rtranclp_power, fast)
  apply(thin_tac "\<forall>a. _ a")
  apply(drule meta_mp, simp)
   apply(erule jumpfree_locally_seq_pstep, assumption+)
  apply(drule meta_mp, simp)
   apply(erule jumpfree_pstep, assumption)
  apply simp
  done



lemma locally_seq_jumpfree_pstep_unq' :
"\<rho> \<turnstile> cf -p\<rightarrow> cf' \<Longrightarrow> \<rho> \<turnstile> cf -p\<rightarrow> cf'' \<Longrightarrow> locally_seq (fst cf) \<Longrightarrow> jumpfree (fst cf) \<Longrightarrow>
 cf' = cf''"
  apply(induct cf cf' arbitrary: cf'' rule: pstep.induct, simp_all)
         apply clarsimp
         apply(drule Basic_pstep, clarsimp)
        apply(case_tac "p\<^sub>1 = Skip", clarify)
         apply(erule Skip_pstep)
        apply clarify
        apply(drule Seq_pstep, assumption)
        apply blast
       apply clarify
       apply(drule Seq_pstep_Skip, clarsimp+)
      apply(drule Cond_pstep, clarsimp+)+
    apply(drule While_pstep, clarsimp+)+
  apply(drule Await_pstep, clarsimp)
  apply(drule locally_seq_jumpfree_pstep_unq_aux, assumption)
  by simp+


corollary locally_seq_jumpfree_pstep_unq :
"\<rho> \<turnstile> (p, s) -p\<rightarrow> (p1, t1) \<Longrightarrow> \<rho> \<turnstile> (p, s) -p\<rightarrow> (p2, t2) \<Longrightarrow> locally_seq p \<Longrightarrow> jumpfree p \<Longrightarrow>
  p1 = p2 \<and> t1 = t2"
  apply(drule locally_seq_jumpfree_pstep_unq')
     apply assumption
  by simp+


end