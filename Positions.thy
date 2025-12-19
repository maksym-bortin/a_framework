(* *********************************************************************

    Theory Positions.thy is part of a framework for modelling,
    verification and transformation of concurrent imperative
    programs. Copyright (c) 2021  M. Bortin

    The framework is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
    For more details see the license agreement (LICENSE) you should have
    received along with the framework.
    
   ******************************************************************* *)

theory Positions
imports Computations
begin


type_synonym pos = "nat list"


fun lookup_pos :: "'a LA \<Rightarrow> pos \<Rightarrow> 'a LA option"  ("_|\<^bsub>_\<^esub>" [1000, 10] 100)
  where
"p|\<^bsub>[]\<^esub> = None" |
"p|\<^bsub>[x]\<^esub> = (if x=0 then Some p else None)" |
"p|\<^bsub>x#xs\<^esub> = (if x=0 then (case p of u;v \<Rightarrow> u|\<^bsub>xs\<^esub>
                                  | _ \<Rightarrow> None)
             else (case p of Parallel ps \<Rightarrow> if x \<le> length ps then (fst(ps!(x-1)))|\<^bsub>xs\<^esub>
                                            else None
                           | _ \<Rightarrow> None))"


text "mixfix syntax avoiding plain square brackets for better readability"  
fun subst_pos :: "'a LA \<Rightarrow> 'a LA \<Rightarrow> pos \<Rightarrow> 'a LA" ("_\<lbrakk>_\<rbrakk>\<^bsub>_\<^esub>" [1000, 10, 10] 1000)
  where
"p\<lbrakk>q\<rbrakk>\<^bsub>[]\<^esub> = p" |
"p\<lbrakk>q\<rbrakk>\<^bsub>[x]\<^esub> = (if x=0 then q else p)" |
"p\<lbrakk>q\<rbrakk>\<^bsub>x#xs\<^esub> = (if x=0 then (case p of u;v \<Rightarrow> u\<lbrakk>q\<rbrakk>\<^bsub>xs\<^esub>;v
                                   | _ \<Rightarrow> p)
              else (case p of Parallel ps \<Rightarrow> (if x\<le>length ps 
                                              then Parallel (ps[(x-1) := ((fst(ps!(x-1)))\<lbrakk>q\<rbrakk>\<^bsub>xs\<^esub>, snd(ps!(x-1)))])
                                              else p)
                            | _ \<Rightarrow> p))"

 

text "(reducible) program positions"
function (sequential) rpos :: "'a LA \<Rightarrow> pos list"
  where 
"rpos Skip = []" |
"rpos (p;q) = (if p=Skip then [[0]] else (map (\<lambda>x. 0#x) (rpos p)))" |
"rpos (Parallel ps) = 
  (if \<forall>(p,a)\<in>set ps. p=Skip 
   then [[0]]
   else concat (map (\<lambda>i. map (\<lambda>x. (i+1)#x) (rpos (fst (ps!i)))) [0..<length ps]))" |
"rpos x = [[0]]"
  by pat_completeness auto

termination
  apply(relation "measure size")
           apply(rule wf_measure)
          apply simp_all
  apply(subgoal_tac "\<forall>i<length ps. size (fst (ps!i)) < Suc (size_list (size_prod size (\<lambda>x. 0)) ps)")
   apply fast
  apply(induct_tac ps)
   apply simp
  apply clarsimp
  apply(case_tac i, clarsimp)
  apply(rename_tac n)
  apply(drule_tac x=n in spec, simp)
  done




lemma rpos_noNil :
"[] \<in> set(rpos p) \<Longrightarrow> False"
  by(induct p rule: rpos.induct, (clarsimp split: if_splits)+)

lemma rpos_empty :
"set(rpos p) = {} \<Longrightarrow> p = Skip"
  apply(induct p rule: rpos.induct, simp_all) 
   apply(clarsimp split: if_splits)+
  by (metis fstI mem_nth)


lemma rpos_last :
"xs \<in> set(rpos p) \<Longrightarrow> last xs = 0"
  apply(induct p arbitrary: xs rule: rpos.induct, simp_all) 
   apply(clarsimp split: if_splits)+
  apply(drule rpos_noNil, clarify)
  done


lemma rpos_singleton :
"[x] \<in> set (rpos p) \<Longrightarrow> x = 0"
  apply(induct p rule: rpos.induct, simp_all)
   apply(clarsimp split: if_splits)+
  by(erule rpos_noNil)


lemma rpos_singleton_unq :
"[x] \<in> set (rpos p) \<Longrightarrow> \<forall>xs\<in>set(rpos p). xs = [0]"
  apply(induct p rule: rpos.induct, simp_all)
   apply(clarsimp split: if_splits)+
   apply(drule rpos_noNil, clarify)
  apply(clarsimp split: if_splits)
  apply(drule rpos_noNil, clarify)
  done

lemma rpos_singleton_eq :
"[x] \<in> set (rpos p) \<Longrightarrow> set(rpos p) = {[0]}"
  apply(frule rpos_singleton, clarify)
  apply(frule rpos_singleton_unq)
  by(rule set_eqI, fast)



lemma rpos_lookup_subst :
"xs \<in> set(rpos p) \<Longrightarrow> \<exists>q. p|\<^bsub>xs\<^esub> = Some q \<and> p\<lbrakk>q\<rbrakk>\<^bsub>xs\<^esub> = p"
  apply(induct p arbitrary:xs rule: rpos.induct, simp_all)
   apply(clarsimp split: if_splits)
   apply(case_tac x, clarsimp+)
  apply(clarsimp split: if_splits)
  apply(rename_tac xs, case_tac xs)
   apply clarsimp
   apply(erule rpos_noNil)
  apply((drule meta_spec)+, (drule meta_mp, assumption)+)
  apply clarsimp
  done


corollary rpos_lookup :
"xs \<in> set(rpos p) \<Longrightarrow> \<exists>q. p|\<^bsub>xs\<^esub> = Some q"
  by(drule rpos_lookup_subst, fast)


lemma rpos_subst_lookup_same :
"xs \<in> set(rpos p) \<Longrightarrow> p\<lbrakk>q\<rbrakk>\<^bsub>xs\<^esub>|\<^bsub>xs\<^esub> = Some q"
  apply(induct p q xs rule: subst_pos.induct)
    apply(drule rpos_noNil, simp+)
   apply(erule rpos_singleton)
  apply clarsimp
  apply(rule conjI, clarsimp)
   apply(case_tac p, simp_all)
    apply(clarsimp split: if_splits)+
  apply(case_tac p, (clarsimp split: if_splits)+)
  done


lemma rpos_subst_lookup_neq :
"xs \<in> set(rpos p) \<Longrightarrow> xs' \<in> set(rpos p) \<Longrightarrow> 
 xs' \<noteq> xs \<Longrightarrow>
 p\<lbrakk>q\<rbrakk>\<^bsub>xs\<^esub>|\<^bsub>xs'\<^esub> = p|\<^bsub>xs'\<^esub>"
  apply(induct p q xs arbitrary: xs' rule: subst_pos.induct)
    apply(drule rpos_noNil, clarsimp+)
   apply(case_tac xs', simp)
   apply(rename_tac x xs)
   apply(case_tac xs, simp+)
   apply(case_tac p, simp_all)
    apply(case_tac q, simp_all)
            apply(clarsimp split: if_splits, drule rpos_noNil, simp)+
   apply(case_tac q, simp_all)
           apply(clarsimp split: if_splits)+
  apply(case_tac p, simp_all)
   apply(clarsimp split: if_splits)
   apply(rename_tac xs)
   apply(case_tac xs, simp)
    apply(drule rpos_noNil, simp)
   apply clarsimp
  apply(clarsimp split: if_splits)
  apply(rename_tac u v a b w)
  apply(case_tac v, clarsimp+)
  apply(case_tac "u = w", clarsimp+)
  done


lemma lookup_pos_jumpfree :
"p|\<^bsub>xs\<^esub> = Some q \<Longrightarrow> jumpfree p \<Longrightarrow> jumpfree q"
  apply(induct p xs rule: lookup_pos.induct, simp_all split: if_splits)
   apply(case_tac p, simp_all)
  apply(case_tac p, simp_all split: if_splits)
  done

lemma lookup_pos_locally_seq :
"p|\<^bsub>xs\<^esub> = Some q \<Longrightarrow> locally_seq p \<Longrightarrow> locally_seq q"
  apply(induct p xs rule: lookup_pos.induct, simp_all split: if_splits)
   apply(case_tac p, simp_all)
  apply(case_tac p, simp_all)
  done

lemma rpos_lookup_rpos :
"xs \<in> set(rpos p) \<Longrightarrow> rpos(the(p|\<^bsub>xs\<^esub>)) = [[0]]"
  apply(induct p arbitrary:xs rule: rpos.induct, simp_all)
   apply(simp split: if_splits)
   apply clarsimp
   apply(rename_tac xs)
   apply(case_tac xs, simp)
    apply(drule rpos_noNil)
   apply(clarsimp split: if_splits)+
  apply(rename_tac xs)
  apply(case_tac xs, simp)
   apply(drule rpos_noNil, clarify)
  apply clarsimp
  done


lemma lookup_pos_Skip :
"length xs \<noteq> 1 \<Longrightarrow> Skip|\<^bsub>xs\<^esub> = None"
  apply(case_tac xs, clarsimp+)
  apply(rename_tac x xs', case_tac xs')
  by clarsimp+



lemma eq_lookup_rpos_retain :
"xs \<in> set(rpos p) \<Longrightarrow> p|\<^bsub>xs\<^esub> = p'|\<^bsub>xs\<^esub> \<Longrightarrow> xs \<in> set(rpos p')"
  apply(induct xs arbitrary: p p')
   apply(drule rpos_noNil, clarify)
  apply(case_tac xs, clarsimp)
   apply(frule rpos_singleton, clarsimp)
  apply(rename_tac x xs p p' x' ys)
  apply(case_tac "x = 0", clarsimp)
   apply(subgoal_tac "\<exists>u v. p = u;v")
    apply(subgoal_tac "\<exists>u' v'. p' = u';v'")
     apply clarify
     apply(drule_tac x=u in meta_spec)
     apply(drule_tac x=u' in meta_spec)
     apply(clarsimp split: if_splits)
    apply(case_tac p', simp_all)
          apply(clarsimp split: if_splits)
          apply(drule rpos_lookup, (clarsimp split: if_splits)+)+
   apply(case_tac p, simp_all)
  apply(clarsimp split: if_splits)
  apply(subgoal_tac "\<exists>ps. p = Parallel ps")
   apply(subgoal_tac "\<exists>ps'. p' = Parallel ps'")
    apply clarify
    apply(drule_tac x="fst(ps!(x-1))" in meta_spec)
    apply(drule_tac x="fst(ps'!(x-1))" in meta_spec)
    apply(clarsimp split: if_splits)
     apply(rename_tac x)
     apply(rule conjI)
      apply(rule ccontr, simp)
      apply(drule_tac x="ps'!x" in bspec)
       apply(rule nth_mem, clarsimp+)
     apply fastforce
    apply(drule rpos_lookup, clarsimp)
   apply(case_tac p', simp_all)
         apply(clarsimp split: if_splits)
          apply(drule rpos_lookup, (clarsimp split: if_splits)+)+
  apply(case_tac p, simp_all)
  done


lemma rpos_subst_lb :
"xs\<in>set(rpos p) \<Longrightarrow> set(rpos p) - {xs} \<subseteq> set(rpos(p\<lbrakk>q\<rbrakk>\<^bsub>xs\<^esub>))"
  apply clarsimp
  apply(rule ccontr, erule notE)
  apply(rule eq_lookup_rpos_retain, assumption)
  apply(subst rpos_subst_lookup_neq, assumption+)
  by(rule refl)


corollary rpos_subst_retain :
"xs\<in>set(rpos p) \<Longrightarrow> xs'\<in>set(rpos p) \<Longrightarrow> xs \<noteq> xs' \<Longrightarrow> 
 xs\<in>set(rpos(p\<lbrakk>q\<rbrakk>\<^bsub>xs'\<^esub>))"
 by(drule_tac xs=xs' and q=q in rpos_subst_lb, fast)


lemma lookup_jumpfree :
"p|\<^bsub>xs\<^esub> = Some(CJump C j p') \<Longrightarrow> xs \<in> set(rpos p) \<Longrightarrow> jumpfree p \<Longrightarrow> False"
  apply(induct p arbitrary: xs rule: rpos.induct, simp+)
       apply(clarsimp split: if_splits)+
       apply(case_tac x, simp+)
       apply fast
      apply(clarsimp split: if_splits)+
      apply(rename_tac xs)
      apply(case_tac xs, simp+)
      apply fast
     apply simp+
  done



lemma locally_seq_rpos_unq :
"locally_seq p \<Longrightarrow> xs\<in>set(rpos p) \<Longrightarrow> xs'\<in>set(rpos p) \<Longrightarrow>
 xs = xs'"
  apply(induct p arbitrary:xs xs' rule: rpos.induct, simp_all)
  by(clarsimp split: if_splits)


lemma subst_pos2 :
"xs \<in> set(rpos p) \<Longrightarrow> (p\<lbrakk>q'\<rbrakk>\<^bsub>xs\<^esub>)\<lbrakk>q\<rbrakk>\<^bsub>xs\<^esub> = p\<lbrakk>q\<rbrakk>\<^bsub>xs\<^esub>"
  apply(induct p arbitrary: xs rule: rpos.induct)
         apply simp+
       apply(clarsimp split: if_splits)
       apply(case_tac x, clarsimp+)
      apply(clarsimp split: if_splits)
      apply(rename_tac xs)
      apply(case_tac xs, simp+)
  done


lemma subst_pos_comm :
"xs \<in> set(rpos p) \<Longrightarrow> xs' \<in> set(rpos p) \<Longrightarrow> xs \<noteq> xs' \<Longrightarrow>
 (p\<lbrakk>q'\<rbrakk>\<^bsub>xs'\<^esub>)\<lbrakk>q\<rbrakk>\<^bsub>xs\<^esub> = (p\<lbrakk>q\<rbrakk>\<^bsub>xs\<^esub>)\<lbrakk>q'\<rbrakk>\<^bsub>xs'\<^esub>"
  apply(induct p arbitrary: xs xs' rule: rpos.induct)
         apply simp+
       apply(clarsimp split: if_splits)
       apply(rename_tac xs xs')
       apply(case_tac xs, simp+)
        apply(drule rpos_noNil, clarify)
       apply(case_tac xs', simp+)
        apply(drule rpos_noNil, clarsimp+)
       apply fast
      apply(clarsimp split: if_splits)
      apply(rename_tac xs p a x' xs')
      apply(case_tac xs, simp+)
      apply(case_tac xs', simp+)
      apply(case_tac "x = x'", simp)
       apply fastforce
      apply simp
      apply (subst (asm) list_update_swap, simp+)
  done


lemma subst_rpos_fix :
"xs \<in> set(rpos p) \<Longrightarrow> (p|\<^bsub>xs\<^esub> = Some q) = (p\<lbrakk>q\<rbrakk>\<^bsub>xs\<^esub> = p)"
  apply(rule iffI)
   apply(induct p q xs rule: subst_pos.induct)
     apply(drule rpos_noNil, clarify)
    apply(frule rpos_singleton, clarsimp+)
   apply(rule conjI, clarsimp)
    apply(case_tac p, simp_all)
    apply(clarsimp split: if_splits)+
   apply(case_tac p, simp_all)
   apply(clarsimp split: if_splits)+
  apply(erule subst)
  by(subst rpos_subst_lookup_same, simp+)



lemma subst_neq_Skip :
"xs\<in>set(rpos p) \<Longrightarrow> length xs > 1 \<Longrightarrow> p\<lbrakk>q\<rbrakk>\<^bsub>xs\<^esub> \<noteq> Skip"
  apply(induct p q xs rule: subst_pos.induct, simp_all)
  apply(rule conjI, clarsimp)
   apply(case_tac p, simp_all)
  apply clarsimp
  apply(case_tac p, simp_all)
  apply(clarsimp split: if_splits)
  done


lemma subst_seq :
"x \<in> set(rpos p1) \<Longrightarrow> (p1;p2)\<lbrakk>q\<rbrakk>\<^bsub>0 # x\<^esub> = p1\<lbrakk>q\<rbrakk>\<^bsub>x\<^esub> ; p2"
  apply(case_tac x, simp)
   apply(drule rpos_noNil, clarify)
  by clarsimp


lemma subst_Parallel :
"x \<in> set(rpos(fst(ps!i))) \<Longrightarrow> 
 (Parallel ps)\<lbrakk>q\<rbrakk>\<^bsub>Suc i # x\<^esub> = Parallel (ps[i := ((fst(ps!i))\<lbrakk>q\<rbrakk>\<^bsub>x\<^esub>, snd(ps!i))])"
  by(case_tac x, simp_all add: list_update_beyond)



subsection "The connection between @{term rpos} and program steps"

lemma pstep_rpos' :
"\<rho> \<turnstile> cf -p\<rightarrow> cf' \<Longrightarrow> 
 \<exists>xs\<in>set(rpos (fst cf)). 
  \<exists>p p'. (fst cf)|\<^bsub>xs\<^esub> = Some p \<and> \<rho> \<turnstile> (p, snd cf) -p\<rightarrow> (p', snd cf') \<and> 
  fst(cf') = (fst cf)\<lbrakk>p'\<rbrakk>\<^bsub>xs\<^esub>"
  apply(erule pstep.induct)
             apply(rule_tac x="[0]" in bexI, simp)
              apply(rule pstep.Basic)
             apply simp
            apply(rule_tac x="[0]" in bexI, simp)
             apply(erule pstep.CJumpT)
            apply simp
           apply(rule_tac x="[0]" in bexI, simp)
            apply(erule pstep.CJumpF)
           apply simp
          apply clarsimp
          apply(rule conjI, clarify)
           apply(erule Skip_pstep)
          apply clarify
          apply(rule_tac x=xs in bexI)
           apply(rule_tac x=p in exI)
           apply(rule conjI)
            apply(case_tac xs, simp, simp)
           apply(rule exI, rule conjI, assumption)
           apply(case_tac xs, simp, simp)
          apply assumption
         apply clarsimp
         apply(rule pstep.SeqSkip)
        apply(rule_tac x="[0]" in bexI, simp)
         apply(erule pstep.CondT)
        apply simp
       apply(rule_tac x="[0]" in bexI, simp)
        apply(erule pstep.CondF)
       apply simp
      apply(rule_tac x="[0]" in bexI, simp)
       apply(erule pstep.WhileT)
      apply simp
     apply(rule_tac x="[0]" in bexI, simp)
      apply(erule pstep.WhileF)
     apply simp
    apply clarsimp
    apply(rename_tac p p')
    apply(rule conjI, clarsimp)
     apply(drule_tac x="ps!i" in bspec)
      apply(erule nth_mem)
     apply clarsimp
    apply clarsimp
    apply(rule_tac x=i in bexI)
     apply(rule_tac x=xs in bexI)
      apply(rule_tac x=p in exI)
      apply(rule conjI)
       apply(case_tac xs, simp, simp)
      apply(rule exI, erule conjI)
      apply(case_tac xs, simp, simp)
     apply assumption
    apply simp
   apply(rule_tac x="[0]" in bexI, simp)
    apply(erule pstep.ParallelSkip)
   apply fastforce
  apply clarsimp
  apply(erule pstep.Await)
  apply(erule rtranclp_sub, simp)
  done


corollary pstep_rpos :
"\<rho> \<turnstile> (p, s) -p\<rightarrow> (p', t) \<Longrightarrow> 
 \<exists>xs\<in>set(rpos p). \<exists>p1 p2. p|\<^bsub>xs\<^esub> = Some p1 \<and> \<rho> \<turnstile> (p1, s) -p\<rightarrow> (p2, t) \<and> p' = p\<lbrakk>p2\<rbrakk>\<^bsub>xs\<^esub>"
  by(drule pstep_rpos', fastforce)



lemma rpos_pstep :
"xs\<in>set(rpos p) \<Longrightarrow> \<rho> \<turnstile> (the(p|\<^bsub>xs\<^esub>), s) -p\<rightarrow> (p', t) \<Longrightarrow>
 \<rho> \<turnstile> (p, s) -p\<rightarrow> (p\<lbrakk>p'\<rbrakk>\<^bsub>xs\<^esub>, t)"
  apply(induct p arbitrary:xs rule: rpos.induct)
          apply simp_all
   apply(simp split: if_splits)
   apply clarsimp
   apply(case_tac x, simp, clarsimp)
   apply(drule meta_spec, (drule meta_mp, assumption)+)
   apply(erule pstep.Seq)
  apply(simp split: if_splits)
  apply clarsimp
  apply(rename_tac xs)
  apply(case_tac xs, simp)
   apply(drule rpos_noNil, clarify)
  apply clarsimp
  apply(drule meta_spec, drule meta_spec, (drule meta_mp, assumption)+)
  apply(erule pstep.Parallel, assumption)
  done



lemma pstep_rpos_retain :
"\<rho> \<turnstile> (p, s) -p\<rightarrow> (p', t) \<Longrightarrow> xs\<in>set(rpos p) \<Longrightarrow> 
 \<forall>p2. \<rho> \<turnstile> (the(p|\<^bsub>xs\<^esub>), s) -p\<rightarrow> (p2, t) \<longrightarrow> p' \<noteq> p\<lbrakk>p2\<rbrakk>\<^bsub>xs\<^esub> \<Longrightarrow>
 xs\<in>set(rpos p') \<and> p'|\<^bsub>xs\<^esub> = p|\<^bsub>xs\<^esub>"
  apply(frule pstep_rpos, clarify)
  by (metis option.sel rpos_subst_lookup_neq rpos_subst_retain)




subsection "The position fired by a program step"


definition "fair_ret \<rho> = (\<forall>i C p. \<rho> i \<noteq> CJump C i p)" 

lemma fair_retI :
"(\<And>i C p. \<rho> i = CJump C i p \<or> \<rho> i = Jump i \<Longrightarrow> False) \<Longrightarrow>
 fair_ret \<rho>"
  by(simp add: fair_ret_def Jump_def, fast)

lemma fair_ret_skips[simp] :
"fair_ret (\<lambda>i. Skip)"
  by(simp add: fair_ret_def)


lemma fair_ret_pstep_noid' :
"\<rho> \<turnstile> cf -p\<rightarrow> cf' \<Longrightarrow> fst cf = fst cf' \<Longrightarrow> fair_ret \<rho> \<Longrightarrow> False"
  apply(induct cf cf' rule: pstep.induct, simp_all)
   apply(simp add: fair_ret_def)
   apply((drule spec)+, erule notE, erule sym)
  by (metis fstI nth_list_update_eq)


corollary fair_ret_pstep_noid :
"\<rho> \<turnstile> (p, s) -p\<rightarrow> (p, t) \<Longrightarrow> fair_ret \<rho> \<Longrightarrow> False"
  by(drule fair_ret_pstep_noid', simp_all)


lemma jumpfree_pstep_noid' :
"\<rho> \<turnstile> cf -p\<rightarrow> cf' \<Longrightarrow> fst cf = fst cf' \<Longrightarrow> jumpfree(fst cf) \<Longrightarrow> False"
  apply(induct cf cf' rule: pstep.induct, simp_all)
   apply(drule sym, simp)+
  by (metis fstI nth_list_update_eq nth_mem)


corollary jumpfree_pstep_noid :
"\<rho> \<turnstile> (p, s) -p\<rightarrow> (p, t) \<Longrightarrow> jumpfree p \<Longrightarrow> False"
  by(drule jumpfree_pstep_noid', simp_all)



lemma pstep_rpos_unq :
"\<rho> \<turnstile> (p, s) -p\<rightarrow> (p', t) \<Longrightarrow> p \<noteq> p' \<Longrightarrow>
 \<exists>!xs. xs \<in> set(rpos p) \<and> (\<exists>p1. \<rho> \<turnstile> (the(p|\<^bsub>xs\<^esub>), s) -p\<rightarrow> (p1, t) \<and> p' = p\<lbrakk>p1\<rbrakk>\<^bsub>xs\<^esub>)"
  apply(drule pstep_rpos, clarify)
  apply(rule_tac a=xs in ex1I, fastforce)
  by (metis rpos_lookup_subst subst_pos2 subst_pos_comm)


corollary fair_ret_pstep_rpos_unq :
"\<rho> \<turnstile> (p, s) -p\<rightarrow> (p', t) \<Longrightarrow> fair_ret \<rho> \<Longrightarrow>
 \<exists>!xs. xs \<in> set(rpos p) \<and> (\<exists>p1. \<rho> \<turnstile> (the(p|\<^bsub>xs\<^esub>), s) -p\<rightarrow> (p1, t) \<and> p' = p\<lbrakk>p1\<rbrakk>\<^bsub>xs\<^esub>)"
  apply(frule pstep_rpos_unq)
   apply clarify
   apply(erule fair_ret_pstep_noid, assumption+)
  done



text "the actual definition"
definition 
"fpos_of \<rho> = (\<lambda>(p, s) (p', t). (THE xs. xs \<in> set(rpos p) \<and> (\<exists>p1. \<rho> \<turnstile> (the(p|\<^bsub>xs\<^esub>), s) -p\<rightarrow> (p1, t) \<and>
                                p' = p\<lbrakk>p1\<rbrakk>\<^bsub>xs\<^esub>)))"



lemma fpos_of_in :
"\<rho> \<turnstile> (p, s) -p\<rightarrow> (p', t) \<Longrightarrow> fair_ret \<rho> \<Longrightarrow>
 fpos_of \<rho> (p, s) (p', t) \<in> set(rpos p) \<and> 
 (\<exists>p1. \<rho> \<turnstile> (the(p|\<^bsub>fpos_of \<rho> (p, s) (p', t)\<^esub>), s) -p\<rightarrow> (p1, t) \<and>
 p' = p\<lbrakk>p1\<rbrakk>\<^bsub>fpos_of \<rho> (p, s) (p', t)\<^esub>)"
  apply(drule fair_ret_pstep_rpos_unq, assumption)
  apply(erule ex1E)
  apply(unfold fpos_of_def, clarify)
  apply(rule_tac a=xs in theI, fast)
  apply fast
  done



lemma fpos_of_eq :
"\<rho> \<turnstile> (p, s) -p\<rightarrow> (p', t) \<Longrightarrow> fair_ret \<rho> \<Longrightarrow>
 xs \<in> set(rpos p) \<Longrightarrow> \<rho> \<turnstile> (the(p|\<^bsub>xs\<^esub>), s) -p\<rightarrow> (p1, t) \<Longrightarrow> p' = p\<lbrakk>p1\<rbrakk>\<^bsub>xs\<^esub> \<Longrightarrow>
 fpos_of \<rho> (p, s) (p', t) = xs"
  apply(unfold fpos_of_def, clarify)
  apply(rule the_equality, fast)
  apply(drule fair_ret_pstep_rpos_unq, assumption)
  apply(rename_tac xs')
  apply(erule ex1E)
  apply(frule_tac x=xs' in spec)
  apply(drule_tac x=xs in spec)
  apply fast
  done


corollary fpos_univ_prop :
"\<rho> \<turnstile> (p, s) -p\<rightarrow> (p', t) \<Longrightarrow> fair_ret \<rho> \<Longrightarrow>
 (fpos_of \<rho> (p, s) (p', t) = xs) = 
 (xs \<in> set(rpos p) \<and> (\<exists>p1. \<rho> \<turnstile> (the(p|\<^bsub>xs\<^esub>), s) -p\<rightarrow> (p1, t) \<and> p' = p\<lbrakk>p1\<rbrakk>\<^bsub>xs\<^esub>))"
  by (meson fpos_of_eq fpos_of_in)


lemma fpos_of_Parallel_step :
"\<rho> \<turnstile> (Parallel ps, s) -p\<rightarrow> (p, t) \<Longrightarrow> fair_ret \<rho> \<Longrightarrow>
 ((\<forall>i<length ps. fst(ps!i) = SKIP) \<and> fpos_of \<rho> (Parallel ps, s) (p, t) = [0] \<and> p = Skip \<and> s = t) \<or>
 (\<exists>i<length ps. \<exists>p'. fpos_of \<rho> (Parallel ps, s) (p, t) = (i+1)#fpos_of \<rho> (fst(ps!i), s) (p', t) \<and>
                     p = Parallel (ps[i := (p', snd(ps!i))]) \<and>
                     \<rho> \<turnstile> (fst(ps!i), s) -p\<rightarrow> (p', t))"
  apply(case_tac "fpos_of \<rho> (Parallel ps, s) (p, t)")
   apply(drule fpos_of_in, assumption)
   apply (metis rpos_noNil)
  apply(rename_tac x xs)
  apply(case_tac "xs = []")
   apply(rule disjI1)
   apply(drule fpos_of_in, assumption)
   apply(clarsimp split: if_splits)
    apply(drule Parallel_pstep_Skip, fastforce)
    apply clarsimp
    apply(drule_tac x="ps!i" in bspec)
     apply(erule nth_mem)
    apply clarsimp
   apply(drule rpos_noNil, clarify)
  apply(rule disjI2)
  apply(frule fpos_of_in, assumption)
  apply(clarsimp split: if_splits)
  apply(rename_tac q a i xs p1)
  apply(case_tac xs, clarsimp+)
  apply(rule exI, subst conj_commute)
  apply((rule conjI)+, rule refl)
   apply(erule rpos_pstep, assumption)
  apply(rule sym, rule fpos_of_eq)
      apply(erule rpos_pstep, assumption+)
  by(rule refl)


lemma fpos_of_Seq_step :
"\<rho> \<turnstile> (p;q, s) -p\<rightarrow> (u, t) \<Longrightarrow> fair_ret \<rho> \<Longrightarrow>
 (fpos_of \<rho> (p;q, s) (u, t) = [0] \<and> p = Skip \<and> u = q \<and> s = t) \<or>  
 (\<exists>p'. fpos_of \<rho> (p;q, s) (u, t) = 0#(fpos_of \<rho> (p, s) (p', t)) \<and> u = p';q \<and> \<rho> \<turnstile> (p, s) -p\<rightarrow> (p', t))"
  apply(case_tac "fpos_of \<rho> (p;q, s) (u, t)")
   apply(drule fpos_of_in, assumption)
   apply (metis rpos_noNil)
  apply(rename_tac x xs)
  apply(case_tac "xs = []")
   apply(rule disjI1)
   apply(drule fpos_of_in, assumption)
   apply(clarsimp split: if_splits)
    apply(drule Seq_pstep_Skip, simp+)
   apply(drule rpos_noNil, clarify)
  apply(rule disjI2)
  apply(frule fpos_of_in, assumption)
  apply(clarsimp split: if_splits)
  apply(rename_tac xs p1)
  apply(rule_tac x="p\<lbrakk>p1\<rbrakk>\<^bsub>xs\<^esub>" in exI)
  apply(case_tac xs, clarsimp+)
  apply(rule conjI)
   apply(rule sym, rule fpos_of_eq)
       apply(erule rpos_pstep, assumption+)
   apply(rule refl)
  apply(erule rpos_pstep, assumption+)
  done



lemma pstep_rpos_retain' :
"\<rho> \<turnstile> (p, s) -p\<rightarrow> (p', t) \<Longrightarrow> xs\<in>set(rpos p) \<Longrightarrow> fair_ret \<rho> \<Longrightarrow>
 fpos_of \<rho> (p, s) (p', t) \<noteq> xs \<Longrightarrow>
 xs\<in>set(rpos p') \<and> p'|\<^bsub>xs\<^esub> = p|\<^bsub>xs\<^esub>"
  apply(frule pstep_rpos_retain, assumption+)
  apply clarsimp
   apply(erule notE)
   apply(erule fpos_of_eq, assumption+)
   apply(rule refl)
  by clarify


text "The following lemma can thus establish that
   if the program part of the i-th configuration on sq (i.e. of sq i) has a reducible position xs
   and no program step from sq k to sq k+1 (with i <= k < j) has xs as its fired position then the 
   program part of sq j has the position xs pointing to the same subterm as in sq i."

lemma iCOMP_rpos_retain :
"sq \<in> iCOMP \<rho> \<Longrightarrow> fair_ret \<rho> \<Longrightarrow> xs\<in>set(rpos(progOf(sq i))) \<Longrightarrow> i < j \<Longrightarrow>
 \<forall>k\<ge>i. k < j \<longrightarrow> tkOf(sq(k+1)) \<longrightarrow> (progOf(sq k))|\<^bsub>xs\<^esub> = (progOf(sq i))|\<^bsub>xs\<^esub> \<longrightarrow> 
        fpos_of \<rho> (confOf(sq k)) (confOf(sq(k+1))) \<noteq> xs \<Longrightarrow>
 xs\<in>set(rpos(progOf(sq j))) \<and> (progOf(sq i))|\<^bsub>xs\<^esub> = (progOf(sq j))|\<^bsub>xs\<^esub>"
  apply(induct j, simp)
  apply clarsimp
  apply(subgoal_tac "xs \<in> set(rpos (progOf (sq j))) \<and> (progOf(sq i))|\<^bsub>xs\<^esub> = (progOf(sq j))|\<^bsub>xs\<^esub>")
   apply(drule_tac x=j in spec, simp)
   apply(drule_tac i=j in iCOMP_D)
   apply(clarsimp simp: stepR_def split: if_splits)
   apply(erule disjE, clarsimp)
    apply(drule pstep_rpos_retain', assumption+)
    apply clarsimp+
  apply(case_tac "i=j", clarsimp)
  apply(drule meta_mp, simp+)
  done


end