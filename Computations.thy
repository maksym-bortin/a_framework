(* *********************************************************************

    Theory Computations.thy is part of a framework for modelling,
    verification and transformation of concurrent imperative
    programs. Copyright (c) 2021  M. Bortin

    The framework is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
    For more details see the license agreement (LICENSE) you should have
    received along with the framework.
    
   ******************************************************************* *)

theory Computations
imports SmallSteps
begin


text "A Boolean value amends configurations to indicate what kind of transition 
      (i.e. env. or program) leads to it. 
      For instance, if (cf2, b2) follows (cf1, b1) then cf1 -p-> cf2 
      when b2 is True and cf1 -e-> cf2 otherwise. "
definition stepR :: "(nat \<Rightarrow> 's LA) \<Rightarrow> (('s config \<times> bool) \<times> ('s config \<times> bool)) set"
where "stepR \<rho> = {(((p, s), tk), ((p', t), tk')) | p s tk p' t tk'. 
                   if tk' then \<rho> \<turnstile> (p, s) -p\<rightarrow> (p', t) else \<turnstile> (p, s) -e\<rightarrow> (p', t)}"



lemma stepR_D1 :
"(((p, s), tk), ((p', t), True)) \<in> stepR \<rho> \<Longrightarrow>
 \<rho> \<turnstile> (p, s) -p\<rightarrow> (p', t)"
  by(simp add: stepR_def, fastforce)


lemma stepR_D2 :
"(((p, s), tk), ((p', t), False)) \<in> stepR \<rho> \<Longrightarrow>
 p = p'"
  by(simp add: stepR_def, fastforce)


lemma stepR_exch :
"(cf, cf') \<in> stepR \<rho> \<Longrightarrow> fst cf = fst cf'' \<Longrightarrow>
 (cf'', cf') \<in> stepR \<rho>"
  by(case_tac cf, case_tac cf', case_tac cf'', clarsimp simp: stepR_def)


section "Infinite computations"

text \<open>An infinite computation is an infinite sequence of tuples (config, bool) successively 
        related by @{term "stepR"}.\<close>

definition iCOMP :: "(nat \<Rightarrow> 's LA) \<Rightarrow> (nat \<Rightarrow> 's config \<times> bool) set"
where "iCOMP \<rho> = {sq. \<forall>i. (sq i, sq(i+1)) \<in> stepR \<rho>}" 


lemma iCOMP_D :
"sq \<in> iCOMP \<rho> \<Longrightarrow>
 (sq i, sq(i+1)) \<in> stepR \<rho>"
  by(simp add: iCOMP_def)


lemma iCOMP_jumpfree :
"sq \<in> iCOMP \<rho> \<Longrightarrow> jumpfree(progOf(sq j)) \<Longrightarrow>
 \<forall>i>j. jumpfree(progOf(sq i))"
  apply(rule allI)
  apply(induct_tac i, simp)
  apply clarify
  apply(subgoal_tac "jumpfree (progOf(sq n))")
   apply(clarsimp simp: iCOMP_def)
   apply(drule_tac x=n in spec)
   apply(case_tac "sq n")
   apply(case_tac "sq(n+1)", clarsimp)
   apply(rename_tac tk)
   apply(case_tac tk, simp)
    apply(drule stepR_D1)
    apply(erule jumpfree_pstep, assumption)
   apply simp
   apply(drule stepR_D2, simp)
  apply(case_tac "j=n", simp_all)
  done


lemma iCOMP_Skip :
"sq \<in> iCOMP \<rho> \<Longrightarrow> progOf(sq j) = Skip \<Longrightarrow>
 \<forall>i>j. progOf(sq i) = Skip \<and> \<not> snd(sq i)"
  apply(rule allI)
  apply(induct_tac i, simp)
  apply clarify
  apply(subgoal_tac "progOf(sq n) = Skip")
   apply(clarsimp simp: iCOMP_def)
   apply(drule_tac x=n in spec)
   apply(case_tac "sq n")
   apply(case_tac "sq(n+1)", clarsimp)
   apply(rename_tac tk)
   apply(case_tac tk, simp)
    apply(drule stepR_D1)
    apply(erule Skip_pstep)
   apply simp
   apply(drule stepR_D2, simp)
  apply(case_tac "j=n", simp_all)
  done


lemma iCOMP_Skip' :
"sq \<in> iCOMP \<rho> \<Longrightarrow> progOf(sq j) = Skip \<Longrightarrow>
 \<forall>i\<ge>j. progOf(sq i) = Skip"
  apply(drule iCOMP_Skip, assumption)
  apply clarsimp
  apply(case_tac "i=j", simp)
  by fastforce


lemma iCOMP_estepsG :
"sq \<in> iCOMP \<rho> \<Longrightarrow> \<forall>k<j. i < k \<longrightarrow> progOf(sq(k-1)) = progOf(sq i) \<longrightarrow> \<not>tkOf(sq k) \<Longrightarrow>
 \<forall>k<j. i \<le> k \<longrightarrow> progOf(sq k) = progOf(sq i)"
  apply(rule allI)
  apply(induct_tac k, simp)
  apply clarsimp
  apply(case_tac "i=n+1", clarsimp)
  apply(drule mp, simp)
  apply(drule spec, drule mp, assumption)
  apply(drule mp, simp)
  apply(drule mp, simp)
  apply(erule subst)
  apply(case_tac "sq n")
  apply(case_tac "sq(n+1)", clarsimp simp: iCOMP_def)
  apply(drule_tac x=n in spec, simp)
  apply(drule stepR_D2)
  by(erule sym)


lemma iCOMP_esteps :
"sq \<in> iCOMP \<rho> \<Longrightarrow> \<forall>k<j. i < k \<longrightarrow> \<not>tkOf(sq k) \<Longrightarrow>
 \<forall>k<j. i \<le> k \<longrightarrow> progOf(sq k) = progOf(sq i)"
  by(drule_tac i=i and j=j in iCOMP_estepsG, simp, assumption)


text "Finite prefixes"
definition fprefix :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a list"
  where "fprefix sq n = map sq [0..<n]"


lemma fprefix_length :
"length(fprefix sq n) = n"
  by(simp add: fprefix_def)

lemma fprefix_nth :
"i < n \<Longrightarrow> (fprefix sq n)!i = sq i"
  by(simp add: fprefix_def)

lemma fprefix_take :
"m \<le> n \<Longrightarrow> fprefix sq m = take m (fprefix sq n)"
  apply(simp add: fprefix_def)
  apply(induct n, simp)
  by(case_tac "m = n + 1", simp+)



definition
"isuffix sq d = (\<lambda>(i::nat). sq (i + d))"

lemma isuffix_add :
"isuffix(isuffix sq d) d' = isuffix sq (d' + d)"
  apply(simp add: isuffix_def, rule ext)
  apply(subst add.assoc, rule refl)
  done


lemma iCOMP_isuffix :
"sq \<in> iCOMP \<rho> \<Longrightarrow> isuffix sq d \<in> iCOMP \<rho>"
  by(simp add: iCOMP_def isuffix_def)



text "Relating consecutive computation steps."  
definition cstep_cond :: "bool \<Rightarrow> 's staterel \<Rightarrow> 
                          's config \<times> bool \<Rightarrow> 's config \<times> bool \<Rightarrow> bool"
where "cstep_cond K R = (\<lambda>((p, s), tk) ((p', t), tk'). tk' = K \<longrightarrow> (s, t) \<in> R)" 


lemma cstep_cond_D :
"cstep_cond K R cf cf' \<Longrightarrow> cf = ((p, s), tk) \<Longrightarrow> cf' = ((p', t), K) \<Longrightarrow>
 (s, t) \<in> R"
  by(simp add: cstep_cond_def)

lemma not_cstep_cond_D :
"\<not> cstep_cond K R cf cf' \<Longrightarrow> 
 \<exists>p s tk p' t. cf = ((p, s), tk) \<and> cf' = ((p', t), K) \<and> (s, t) \<notin> R"
  by(clarsimp simp add: cstep_cond_def)


lemma cstep_cond_mono :
"cstep_cond K R cf cf' \<Longrightarrow> R \<subseteq> R' \<Longrightarrow>
 cstep_cond K R' cf cf'"
  by(clarsimp simp add: cstep_cond_def, force)


definition EnvCond_i :: "(nat \<Rightarrow> 's LA)  \<Rightarrow> 's staterel \<Rightarrow> (nat \<Rightarrow> 's config \<times> bool) set"
where "EnvCond_i \<rho> R = {sq |sq. sq \<in> iCOMP \<rho> \<and> (\<forall>i. 0 < i \<longrightarrow> cstep_cond False R (sq (i-1)) (sq i))}"

definition ProgCond_i :: "(nat \<Rightarrow> 's LA)  \<Rightarrow> 's staterel \<Rightarrow> (nat \<Rightarrow> 's config \<times> bool) set"
where "ProgCond_i \<rho> R = {sq |sq. sq \<in> iCOMP \<rho> \<and> (\<forall>i. 0 < i \<longrightarrow> cstep_cond True R (sq (i-1)) (sq i))}"

definition "InitCond_i \<rho> P = {sq |sq c s tk. sq \<in> iCOMP \<rho> \<and> sq 0 = ((c, s), tk) \<and> s \<in> P}"

definition "TermCond_i \<rho> Q = {sq |sq. sq \<in> iCOMP \<rho> \<and> 
                                  (\<forall>j. progOf(sq j) = Skip \<longrightarrow> 
                                        (\<exists>i s tk. i \<le> j \<and> sq i = ((Skip, s), tk) \<and> s \<in> Q))}"


lemma EnvCond_i_suffix :
"sq \<in> EnvCond_i \<rho> R \<Longrightarrow> isuffix sq d \<in> EnvCond_i \<rho> R"
  apply(clarsimp simp: EnvCond_i_def)
  apply(rule conjI)
  apply(erule iCOMP_isuffix)
  apply(clarsimp simp: isuffix_def)
  done

lemma ProgCond_i_suffix :
"sq \<in> ProgCond_i \<rho> R \<Longrightarrow> isuffix sq d \<in> ProgCond_i \<rho> R"
  apply(clarsimp simp: ProgCond_i_def)
  apply(rule conjI)
  apply(erule iCOMP_isuffix)
  apply(clarsimp simp: isuffix_def)
  done



section "Finite computations"


definition COMP :: "(nat \<Rightarrow> 's LA) \<Rightarrow> ('s config \<times> bool) list set"
  where "COMP \<rho> = {sq. sq \<noteq> [] \<and> (\<forall>i<length sq - 1. (sq!i, sq!(i+1)) \<in> stepR \<rho>)}"


lemma COMP_eq :
"(sq \<in> COMP \<rho>) = (sq \<noteq> [] \<and> (\<forall>i<length sq - 1. (sq!i, sq!(i+1)) \<in> stepR \<rho>))"
  by(simp add: COMP_def)


lemma COMP_fprefix :
"COMP \<rho> = {fprefix sq (n+1) |sq n. sq \<in> iCOMP \<rho>}"
  apply(rule set_eqI)
  apply(rename_tac sq)
  apply(subst COMP_eq)
  apply(rule iffI, clarsimp)
   apply(rule_tac x="\<lambda>i. if i<length sq then sq!i 
                        else (fst(sq!(length sq - 1)), False)" in exI)
   apply(rule conjI)
    apply(rule_tac x="length sq - 1" in exI)
    apply(rule nth_equalityI, simp add: fprefix_length, simp add: fprefix_nth)
   apply(clarsimp simp: iCOMP_def)
   apply(case_tac "sq!(length sq - 1)")
   apply(rule conjI, clarsimp)
    apply(drule leI)
    apply(subgoal_tac "i = length sq - 1")
     apply(subst stepR_def, clarsimp, rule_tac x=False in exI, simp)
    apply fastforce
   apply(subst stepR_def, clarsimp, rule_tac x=False in exI, clarsimp+)
  apply(clarsimp simp: fprefix_length fprefix_nth)
  by (metis Suc_eq_plus1 fprefix_length iCOMP_D length_0_conv nat.simps(3))


corollary fprefix_COMP' :
"sq \<in> iCOMP \<rho> \<Longrightarrow> fprefix sq (n+1) \<in> COMP \<rho>"
  by(subst COMP_fprefix, fast)

corollary fprefix_COMP :
"sq \<in> iCOMP \<rho> \<Longrightarrow> n > 0 \<Longrightarrow> fprefix sq n \<in> COMP \<rho>"
  by (metis Suc_eq_plus1 Suc_pred' fprefix_COMP')

corollary fprefix_COMP_D :
"fprefix sq n \<in> COMP \<rho> \<Longrightarrow> n > 0"
  apply(subst (asm) COMP_fprefix, clarsimp)
  apply(drule_tac f=length in arg_cong)
  by(simp add: fprefix_length)



text "Finite potential computations of a program"
definition pcs :: "'s LA \<Rightarrow> (nat \<Rightarrow> 's LA) \<Rightarrow> ('s config \<times> bool) list set" 
("\<lbrakk>_\<rbrakk>\<^sub>_" [100,101] 100)
where "\<lbrakk>p\<rbrakk>\<^sub>\<rho> = {sq |sq s tk. sq \<in> COMP \<rho> \<and> hd sq = ((p, s), tk)}"



text "Picking actual computations, i.e. those where no env. transitions occur"
definition acs :: "'s LA \<Rightarrow> (nat \<Rightarrow> 's LA) \<Rightarrow> ('s config \<times> bool) list set" 
("\<^sup>A\<lbrakk>_\<rbrakk>\<^sub>_" [100,101] 100)
where "\<^sup>A\<lbrakk>p\<rbrakk>\<^sub>\<rho> = {sq. sq \<in> \<lbrakk>p\<rbrakk>\<^sub>\<rho> \<and> (\<forall>i < length sq. 0 < i \<longrightarrow> snd(sq!i))}"


section "Properties"

corollary COMP_noNil :
"sq \<in> COMP \<rho> \<Longrightarrow> sq \<noteq> []"
  by(subst (asm) COMP_eq, simp)


corollary COMP_nth :
"sq \<in> COMP \<rho> \<Longrightarrow> i < length sq \<Longrightarrow> 0 < i \<Longrightarrow>
 (sq!(i-1), sq!i) \<in> stepR \<rho>"
  by(subst (asm) COMP_eq, clarsimp, drule_tac x="i-1" in spec, simp)


corollary nth_COMP[rule_format] :
"\<forall>i<length sq. 0 < i \<longrightarrow> (sq!(i-1), sq!i) \<in> stepR \<rho> \<Longrightarrow> sq \<noteq> [] \<Longrightarrow>
 sq \<in> COMP \<rho>"
  by(subst COMP_eq, clarsimp, drule_tac x="i+1" in spec, simp)


lemma COMP_compose' :
"sq \<in> COMP \<rho> \<Longrightarrow> sq' \<in> COMP \<rho> \<Longrightarrow>
 fst(last sq) = fst(hd sq') \<Longrightarrow> (sq @ tl sq') \<in> COMP \<rho>"
  apply(case_tac "tl sq' = []", simp)
  apply(clarsimp simp: COMP_eq)
  apply(case_tac "i<length sq - 1", clarsimp simp: nth_append, fastforce)
  apply(drule leI)
  apply(case_tac "i=length sq - 1", clarsimp simp: nth_append)
   apply(subst (asm) last_conv_nth, assumption)
   apply(subst (asm) hd_conv_nth, assumption)
   apply(subst nth_tl, simp)
   apply(case_tac "sq!(length sq - 1)", clarsimp)
   apply(drule_tac x=0 in spec)+
   apply(drule mp, fastforce)
   apply(clarsimp simp: stepR_def, fastforce)
  apply(clarsimp simp: nth_append)
  apply(rule conjI, fastforce)
  apply(subst nth_tl, simp)+
  apply(drule_tac x="i - length sq + 1" in spec)+
  apply(drule mp, fastforce)
  apply clarsimp
  by (metis Suc_diff_le less_eq_Suc_le not_less_eq_eq)


lemma COMP_compose2' :
"sq \<in> COMP \<rho> \<Longrightarrow> (fst(last sq), tk) # sq' \<in> COMP \<rho> \<Longrightarrow>
 (sq @ sq') \<in> COMP \<rho>"
  by(drule COMP_compose', assumption, simp+)

lemma COMP_compose :
"sq \<in> COMP \<rho> \<Longrightarrow> sq' \<in> COMP \<rho> \<Longrightarrow>
 last sq = hd sq' \<Longrightarrow> (sq @ tl sq') \<in> COMP \<rho>"
by(erule COMP_compose', simp_all)


lemma COMP_compose2 :
"sq \<in> COMP \<rho> \<Longrightarrow> last sq # sq' \<in> COMP \<rho> \<Longrightarrow>
 (sq @ sq') \<in> COMP \<rho>"
  by(drule COMP_compose, assumption, simp+)



lemma iCOMP_pow :
"sq \<in> iCOMP \<rho> \<Longrightarrow> (sq 0, sq i) \<in> stepR \<rho> ^^ i"
  apply(induct_tac i, simp_all)
  apply(erule relcompI)
  by(simp add: iCOMP_def)


lemma COMP_pow :
"sq \<in> COMP \<rho> \<Longrightarrow> 
 \<forall>i<length sq. (sq!0, sq!i) \<in> (stepR \<rho>)^^i" 
  apply(subst (asm) COMP_fprefix, clarsimp simp: fprefix_length fprefix_nth)
  by(erule iCOMP_pow)



lemma pow_COMP[rule_format] :
"\<forall>cf cf'. (cf, cf') \<in> (stepR \<rho>)^^i \<longrightarrow>
 (\<exists>sq. length sq = Suc i \<and> sq \<in> COMP \<rho> \<and> sq!0 = cf \<and> sq!i = cf')"
  apply(induct_tac i)
   apply clarsimp
   apply(rename_tac p s tk)
   apply(rule_tac x="[((p, s), tk)]" in exI, simp add: COMP_eq)
  apply clarsimp
  apply((drule spec)+, drule mp, assumption)
  apply clarify
  apply(rename_tac p s tk sq)
  apply(rule_tac x="sq@[((p, s), tk)]" in exI, simp)
  apply(frule COMP_noNil)
  apply(subst nth_append, simp)
  apply(subst nth_append, simp)
  apply(erule COMP_compose2)
  apply(subst last_conv_nth, assumption)
  by(clarsimp simp: COMP_eq)


lemma pstep_pow_COMP[rule_format] :
"\<forall>cf cf'. ((pstep \<rho>)^^i) cf cf' \<longrightarrow>
 (\<exists>sq. length sq = Suc i \<and> sq \<in> COMP \<rho> \<and> fst(sq!0) = cf \<and> fst(sq!i) = cf' \<and>
    (\<forall>j<length sq. snd(sq!j)))"
  apply(induct_tac i)
   apply clarsimp
   apply(rename_tac p s)
   apply(rule_tac x="[((p, s), True)]" in exI, simp add: COMP_eq)
  apply clarsimp
  apply((drule spec)+, drule mp, assumption)
  apply clarify
  apply(rename_tac p' t p s sq)
  apply(rule_tac x="sq@[((p', t), True)]" in exI, simp)
  apply(frule COMP_noNil)
  apply(subst nth_append, simp)
  apply(subst nth_append, simp)
  apply(rule conjI)
   apply(erule COMP_compose2)
   apply(subst last_conv_nth, assumption)
   apply(case_tac "sq!n", clarsimp simp: COMP_eq)
   apply(simp add: stepR_def, rule_tac x=True in exI, simp (no_asm))
  apply clarsimp
  apply(case_tac "j = Suc n", clarsimp)
  apply(subst nth_append, simp)
  apply(subst nth_append, simp)
 done


lemma COMP_pstep_pow[rule_format] :
"sq \<in> COMP \<rho> \<Longrightarrow> \<forall>j<length sq. 0 < j \<longrightarrow> snd(sq!j) \<Longrightarrow>
 \<forall>i<length sq. ((pstep \<rho>)^^i) (fst(sq!0)) (fst(sq!i))"
  apply(rule allI)
  apply(induct_tac i, clarsimp+)
  apply(erule relcomppI)
  apply(drule spec, drule mp, assumption)
  apply(case_tac "sq!n", case_tac "sq!(n+1)", clarsimp)
  apply(drule_tac i="n+1" in COMP_nth, clarsimp+)
  by(erule stepR_D1)


lemma esteps_COMP[rule_format] :
"sq \<in> COMP \<rho> \<Longrightarrow> 
 \<forall>i < length sq. 0 < i \<longrightarrow> \<not>tkOf(sq!i) \<and> (stateOf(sq!(i - 1)) \<in> S \<longrightarrow> stateOf(sq!i) \<in> S) \<Longrightarrow> 
  stateOf(sq!0) \<in> S \<Longrightarrow> i < length sq \<Longrightarrow> 
 progOf(sq!i) = progOf(sq!0) \<and> stateOf(sq!i) \<in> S"
  apply(induct i, simp_all)
  apply(drule spec, drule mp, assumption)
  apply clarsimp
  apply(drule_tac i="i+1" in COMP_nth, simp, simp)
  apply(clarsimp simp: stepR_def)
  done



lemma Skip_COMP[rule_format] :
"sq \<in> COMP \<rho> \<Longrightarrow> \<forall>i < length sq. \<forall>s t p tk. 0 < i \<longrightarrow> sq!(i - 1) = ((Skip, s), tk) \<longrightarrow> 
               sq!i = ((p, t), False) \<longrightarrow> s \<in> Q \<longrightarrow> t \<in> Q \<Longrightarrow>
 progOf(sq!0) = Skip \<Longrightarrow> stateOf(sq!0) \<in> Q \<Longrightarrow>
 i < length sq \<Longrightarrow> progOf(sq!i) = Skip \<and> stateOf(sq!i) \<in> Q" 
  apply(induct i, simp_all)
  apply(drule_tac x="i+1" in spec, simp)
  apply(case_tac "sq!i")
  apply(case_tac "sq!(i+1)", clarsimp)
  apply(drule_tac i="i+1" in COMP_nth, simp, simp)
  apply(rename_tac tk)
  apply(case_tac tk)
   apply clarsimp
   apply(drule stepR_D1)
   apply(erule Skip_pstep)
  apply clarsimp
  apply(drule stepR_D2, simp)
  done



lemma Skip_COMP_pstep :
"sq \<in> COMP \<rho> \<Longrightarrow> 
 progOf(sq!0) = Skip \<Longrightarrow> i < length sq \<Longrightarrow> 0 < i \<Longrightarrow> tkOf(sq!i) \<Longrightarrow> P"
  apply(frule_tac i="i-1" and Q=UNIV in Skip_COMP, clarsimp, assumption, simp, simp)
  apply(case_tac "sq!(i-1)", clarsimp)
  apply(case_tac "sq!i", clarsimp)
  apply(drule_tac i=i in COMP_nth, assumption+)
  apply clarsimp
  apply(drule stepR_D1)
  by(erule Skip_pstep) 

    


section "Prefixes and suffixes of finite computations"

definition "prefix pr sq = (\<exists>s. sq = pr@s)"

lemma prefix_length :
"prefix pr sq \<Longrightarrow> length pr \<le> length sq"
  by(clarsimp simp add: prefix_def)


lemma prefix_take :
"prefix (take i sq) sq"
  apply(simp add: prefix_def)
  apply(rule_tac x="drop i sq" in exI)
  by(rule sym, rule append_take_drop_id)


lemma prefix_nth :
"prefix pr sq \<Longrightarrow> i < length pr \<Longrightarrow> 
 pr!i = sq!i"
  apply(clarsimp simp add: prefix_def)
  apply(subst nth_append, simp)
  done

lemma prefix_appendI :
"prefix pr xs \<Longrightarrow> prefix pr (xs @ zs)" 
  apply(simp add: prefix_def, fastforce)
  done
    
    
lemma prefix_appendD :
"prefix pr (xs @ zs) \<Longrightarrow> prefix pr xs \<or> (\<exists>pr1. pr1 \<noteq> [] \<and> pr = xs @ pr1 \<and> prefix pr1 zs)"
  apply(simp add: prefix_def)
  apply(erule exE)
  apply(subst (asm) append_eq_append_conv2)
  apply(erule exE)
  apply(erule disjE, fastforce)
  apply fastforce
  done


corollary prefix_snoc :
"prefix pr (xs @ [a]) \<Longrightarrow> pr = (xs @ [a]) \<or> prefix pr xs"
  by(drule prefix_appendD, erule disjE, clarsimp+, case_tac pr1, (clarsimp simp: prefix_def)+)


lemma prefix_length_eqD :
"prefix pr xs \<Longrightarrow> length pr = length xs \<Longrightarrow> pr = xs" 
  by(clarsimp simp: prefix_def)  
   
    

lemma COMP_prefix_cls :
"sq \<in> COMP \<rho> \<Longrightarrow> prefix pr sq \<Longrightarrow> pr \<noteq> [] \<Longrightarrow> pr \<in> COMP \<rho>"
  apply(clarsimp simp: COMP_eq)
  apply(subst prefix_nth, assumption, simp)+
  apply(drule_tac x=i in spec)
  apply(drule mp, erule less_le_trans, drule prefix_length)
  by fastforce



definition "suffix su sq = (\<exists>x. sq = x@su)"

lemma suffix_length :
"suffix su sq \<Longrightarrow> length su \<le> length sq"
  by(clarsimp simp add: suffix_def)


lemma suffix_drop :
"suffix (drop i sq) sq"
  apply(simp add: suffix_def)
  apply(rule_tac x="take i sq" in exI)
  by(rule sym, rule append_take_drop_id)


lemma suffix_nth :
"suffix su sq \<Longrightarrow> i < length su \<Longrightarrow> 
 su!i = sq!(i + (length sq - length su))"
  apply(clarsimp simp add: suffix_def)
  apply(subst nth_append, simp)
  done


lemma COMP_suffix_cls :
"sq \<in> COMP \<rho> \<Longrightarrow> suffix su sq \<Longrightarrow> su \<noteq> [] \<Longrightarrow> su \<in> COMP \<rho>"
  apply(clarsimp simp: COMP_eq)
  apply(subst suffix_nth, assumption, simp)+
  apply(drule_tac x="i + (length sq - length su)" in spec, simp)
  apply(drule mp, drule suffix_length)
  by fastforce


lemma COMP_decomp :
"(sq @ sq') \<in> COMP \<rho> \<Longrightarrow> sq \<noteq> [] \<Longrightarrow> 
 sq \<in> COMP \<rho> \<and> (last sq # sq') \<in> COMP \<rho>"
  apply(rule conjI)
   apply(erule COMP_prefix_cls)
    apply(simp add: prefix_def)
   apply assumption
  apply(erule COMP_suffix_cls)
   apply(simp add: suffix_def)
   apply(rule_tac x="butlast sq" in exI)
  by simp+


lemma Skip_COMP'[rule_format] :
"sq \<in> COMP \<rho> \<Longrightarrow> (\<forall>i < length sq. \<forall>s t p tk. 0 < i \<longrightarrow> sq!(i - 1) = ((Skip, s), tk) \<longrightarrow> 
               sq!i = ((p, t), False) \<longrightarrow> s \<in> Q \<longrightarrow> t \<in> Q) \<Longrightarrow>
 progOf(sq!i) = Skip \<Longrightarrow> stateOf(sq!i) \<in> Q \<Longrightarrow> i < length sq \<Longrightarrow>
 \<forall>j<length sq. i\<le>j \<longrightarrow> progOf(sq!j) = Skip \<and> stateOf(sq!j) \<in> Q"
  apply(drule_tac su="drop i sq" in COMP_suffix_cls)
    apply(rule suffix_drop, simp)
  apply clarsimp
  apply(drule_tac Q=Q and i="j-i" in Skip_COMP)
      apply clarsimp
      apply(rename_tac k s t p tk)
      apply(drule_tac x="i+k" in spec, simp)
     apply clarsimp+
   apply fastforce
  apply clarsimp
  done




subsection "Properties of finite potential computations of a program"

lemma pcs_noNil :
"sq \<in> \<lbrakk>p\<rbrakk>\<^sub>\<rho> \<Longrightarrow> sq \<noteq> []"
  apply(clarsimp simp add: pcs_def) 
  by(drule COMP_noNil, clarify)

lemma pcsD :
"sq \<in> \<lbrakk>p\<rbrakk>\<^sub>\<rho> \<Longrightarrow> sq \<in> COMP \<rho>"
  by(simp add: pcs_def)

lemma pcs_nth :
"sq \<in> \<lbrakk>p\<rbrakk>\<^sub>\<rho> \<Longrightarrow> i < length sq \<Longrightarrow> 0 < i \<Longrightarrow> (sq!(i-1), sq!i) \<in> stepR \<rho>"
  apply(clarsimp simp: pcs_def)
  by(erule COMP_nth[simplified], assumption+)

lemma pcs0 :
"sq \<in> \<lbrakk>p\<rbrakk>\<^sub>\<rho> \<Longrightarrow> \<exists>s tk. sq!0 = ((p, s), tk)"
  apply(clarsimp simp add: pcs_def)
  apply(drule COMP_noNil)
  apply(subst (asm) hd_conv_nth, simp)
  by fastforce



lemma esteps_pcs :
"sq \<in> \<lbrakk>p\<rbrakk>\<^sub>\<rho> \<Longrightarrow> 
 \<forall>i<length sq. 0 < i \<longrightarrow> \<not>tkOf(sq!i) \<and> (stateOf(sq!(i - 1)) \<in> P \<longrightarrow> stateOf(sq!i) \<in> P) \<Longrightarrow> 
 stateOf(sq!0) \<in> P \<Longrightarrow>
 \<forall>i < length sq. progOf(sq!i) = p \<and> stateOf(sq!i) \<in> P" 
  apply(clarsimp simp add: pcs_def)
  apply(frule COMP_noNil)
  apply(subst (asm) hd_conv_nth, assumption)
  apply(drule_tac i=i and S=P in esteps_COMP, simp, assumption+)
  by simp




lemma Skip_pcs :
"sq \<in> \<lbrakk>Skip\<rbrakk>\<^sub>\<rho> \<Longrightarrow> \<forall>i < length sq. \<forall>s t p' tk. 0 < i \<longrightarrow> sq!(i - 1) = ((Skip, s), tk) \<longrightarrow> 
                  sq!i = ((p', t), False) \<longrightarrow> s \<in> Q \<longrightarrow> t \<in> Q \<Longrightarrow>
 stateOf(sq!0) \<in> Q \<Longrightarrow>
 \<forall>i < length sq. progOf(sq!i) = Skip \<and> stateOf(sq!i) \<in> Q" 
  apply(clarsimp simp add: pcs_def)
  apply(frule COMP_noNil)
  apply(subst (asm) hd_conv_nth, assumption)
  apply(drule_tac i=i and Q=Q in Skip_COMP)
      apply force
     apply simp_all
  done

lemma Skip_pcs_pstep[rule_format] :
"sq \<in> \<lbrakk>Skip\<rbrakk>\<^sub>\<rho> \<Longrightarrow> i < length sq \<Longrightarrow> 0 < i \<Longrightarrow> snd(sq!i) \<Longrightarrow> P"
  apply(clarsimp simp: pcs_def)
  apply(subst (asm) hd_conv_nth, erule COMP_noNil)
  apply(drule Skip_COMP_pstep, simp, assumption+)
done



lemma pcs_prefix_cls :
"sq \<in> \<lbrakk>p\<rbrakk>\<^sub>\<rho> \<Longrightarrow> prefix pr sq \<Longrightarrow> pr \<noteq> [] \<Longrightarrow> 
 pr \<in> \<lbrakk>p\<rbrakk>\<^sub>\<rho>"
  apply(clarsimp simp add: pcs_def)
  apply(drule COMP_prefix_cls, assumption+)
  apply(simp add: prefix_def)
  apply clarify
  apply(rule_tac x=s in exI)
  apply(rule_tac x=tk in exI)
  apply(case_tac pr, simp_all)
  done


lemma pcs_suffix_cls :
"sq \<in> \<lbrakk>p\<rbrakk>\<^sub>\<rho> \<Longrightarrow> suffix su sq \<Longrightarrow> su \<noteq> [] \<Longrightarrow> 
 su \<in> \<lbrakk>progOf(sq!(length sq - length su))\<rbrakk>\<^sub>\<rho>"
  apply(clarsimp simp add: pcs_def)
  apply(drule COMP_suffix_cls, assumption+)
   apply(drule_tac i=0 in suffix_nth)
   apply simp
  apply clarsimp
  apply(erule_tac s="su!0" in subst)
  apply(case_tac su, clarify)
  apply clarsimp
  done


lemma acs_noNil :
"[] \<in> \<^sup>A\<lbrakk>p\<rbrakk>\<^sub>\<rho> \<Longrightarrow> P"
  by(simp add: acs_def, drule pcs_noNil, clarify)


lemma acs_prefix_cls :
"sq \<in> \<^sup>A\<lbrakk>p\<rbrakk>\<^sub>\<rho> \<Longrightarrow> prefix pr sq \<Longrightarrow> pr \<noteq> [] \<Longrightarrow> 
 pr \<in> \<^sup>A\<lbrakk>p\<rbrakk>\<^sub>\<rho>"
  apply(clarsimp simp add: acs_def)
  apply(rule conjI)
   apply(erule pcs_prefix_cls, assumption+)
  apply(clarsimp simp: prefix_def)
  apply(drule_tac x=i in spec, simp)
  apply(subst (asm) nth_append, simp)
  done


section "Pcs, constrained by conditions"


text "Computations where all environment transitions satisfy a state relation"
definition EnvCond :: "(nat \<Rightarrow> 's LA) \<Rightarrow> 's staterel \<Rightarrow> 
                      ('s config \<times> bool) list set"
where "EnvCond \<rho> R = {sq |sq p. sq \<in> \<lbrakk>p\<rbrakk>\<^sub>\<rho> \<and> (\<forall>i. i < length sq \<longrightarrow> 0 < i \<longrightarrow>
                                             cstep_cond False R (sq!(i-1)) (sq!i))}"



definition EnvCond_br :: "(nat \<Rightarrow> 's LA)\<Rightarrow> 's staterel \<Rightarrow> ('s config \<times> bool) list \<Rightarrow>
                           nat \<Rightarrow> bool"
  where "EnvCond_br \<rho> R sq i = 
  (\<exists>c s c' t tk. sq!(i - 1) = ((c, s), tk) \<and> sq!i = ((c', t), False) \<and> (s, t) \<notin> R)"


lemma EnvCond_D :
"sq \<in> EnvCond \<rho> R \<Longrightarrow> 
 i < length sq \<Longrightarrow> 0 < i \<Longrightarrow>
 sq!(i - Suc 0) = ((c, s), tk) \<Longrightarrow> sq!i = ((c', t), False) \<Longrightarrow> (s, t) \<in> R"
  apply(clarsimp simp add: EnvCond_def)
  apply(drule_tac x=i in spec, simp)
  by(erule cstep_cond_D, rule refl, rule refl)

lemma not_EnvCond_D :
"sq \<notin> EnvCond \<rho> R \<Longrightarrow> sq \<in> \<lbrakk>p\<rbrakk>\<^sub>\<rho> \<Longrightarrow> 
 \<exists>i. i < length sq \<and> 0 < i \<and> \<not> cstep_cond False R (sq!(i-1)) (sq!i)"
  by(clarsimp simp add: EnvCond_def)


lemma not_EnvCond_D' :
"sq \<notin> EnvCond \<rho> R \<Longrightarrow> sq \<in> \<lbrakk>p\<rbrakk>\<^sub>\<rho> \<Longrightarrow> 
 \<exists>i c s c' t tk. i < length sq \<and> 0 < i \<and>
 sq!(i - 1) = ((c, s), tk) \<and> sq!i = ((c', t), False) \<and> (s, t) \<notin> R"
  apply(clarsimp simp add: EnvCond_def)
  apply(erule disjE, simp)
  apply clarsimp
  apply(rule_tac x=i in exI, simp)
  apply(case_tac "sq!i", case_tac "sq!(i-1)")
  apply(clarsimp simp add: cstep_cond_def)
  done


lemma EnvCond_prefix_cls :
"sq \<in> EnvCond \<rho> R' \<Longrightarrow> prefix pr sq \<Longrightarrow> pr \<noteq> [] \<Longrightarrow> R' \<subseteq> R \<Longrightarrow>
 pr \<in> EnvCond \<rho> R"
  apply(clarsimp simp add: EnvCond_def)
  apply(rule conjI)
   apply(rule exI, erule pcs_prefix_cls, assumption+)
  apply clarsimp
  apply(subst prefix_nth, assumption, simp)+
  apply(drule prefix_length)
  apply(drule_tac x=i in spec, simp)
  by(erule cstep_cond_mono)


lemma EnvCond_suffix_cls :
"sq \<in> EnvCond \<rho> R' \<Longrightarrow> suffix sf sq \<Longrightarrow> sf \<noteq> [] \<Longrightarrow> R' \<subseteq> R \<Longrightarrow>
 sf \<in> EnvCond \<rho> R"
  apply(clarsimp simp add: EnvCond_def)
  apply(rule conjI)
   apply(rule exI, erule pcs_suffix_cls, assumption+)
  apply clarsimp
  apply(subst suffix_nth, assumption, simp)+
  apply(drule suffix_length)
  apply(drule_tac x="i + (length sq - length sf)" in spec, simp)
  apply(drule mp, force)
  by(erule cstep_cond_mono, assumption)



lemma EnvCond_compose :
"sq \<in> EnvCond \<rho> R \<Longrightarrow> sq' \<in> EnvCond \<rho> R \<Longrightarrow>
 fst(last sq) = fst(hd sq') \<Longrightarrow> 
 (sq @ tl sq') \<in> EnvCond \<rho> R"
  apply(case_tac "length sq' = 1")
   apply(case_tac sq', clarsimp, clarsimp)
  apply(subgoal_tac "0 < length sq \<and> 1 < length sq'")
   prefer 2
   apply(rule ccontr, simp)
   apply(clarsimp simp: EnvCond_def)
   apply(drule pcs_noNil)+
   apply(case_tac sq', clarsimp, clarsimp)
  apply(subst EnvCond_def, simp)
  apply(rule conjI)
   apply(clarsimp simp: EnvCond_def pcs_def)
   apply(frule COMP_noNil)
   apply(drule COMP_compose', assumption, simp)
   apply simp
  apply(clarsimp simp: cstep_cond_def)
  apply(drule_tac t="(sq @ tl sq') ! (i - Suc 0)" in sym)
  apply(subst (asm) nth_append)+
  apply(simp split: if_splits)
    apply(erule_tac i=i in EnvCond_D, assumption+)
   apply(subgoal_tac "i = length sq", clarsimp)
    apply(subst (asm) last_conv_nth, simp)
    apply(subst (asm) hd_conv_nth, fastforce)
    apply(subst (asm) nth_tl, simp)
    apply(case_tac "sq'!0", clarsimp)
    apply(erule_tac i=1 and sq=sq' in EnvCond_D, simp, simp (no_asm), simp, simp)
   apply fastforce
  apply(drule leI)+
  apply(subst (asm) nth_tl, simp)+
  apply(subgoal_tac " Suc (i - Suc (length sq)) = i - length sq", simp)
   apply(erule_tac sq=sq' and i="i - length sq + 1" in EnvCond_D, simp+)
  done





text "Computations where all program transitions satisfy a state relation"
definition ProgCond :: "(nat \<Rightarrow> 's LA) \<Rightarrow> 's staterel \<Rightarrow> ('s config \<times> bool) list set"
where "ProgCond \<rho> R = {sq |sq p. sq \<in> \<lbrakk>p\<rbrakk>\<^sub>\<rho> \<and> (\<forall>i. i < length sq \<longrightarrow> 0 < i \<longrightarrow>
                                                 cstep_cond True R (sq!(i-1)) (sq!i))}"


lemma ProgCond_D :
"sq \<in> ProgCond \<rho> R \<Longrightarrow> 
 i < length sq \<Longrightarrow> 0 < i \<Longrightarrow>
 sq!(i - Suc 0) = ((c, s), tk) \<Longrightarrow> sq!i = ((c', t), True) \<Longrightarrow> (s, t) \<in> R"
  apply(clarsimp simp add: ProgCond_def)
  apply(drule_tac x=i in spec, simp)
  by(erule cstep_cond_D, rule refl, rule refl)


lemma not_ProgCond_D :
"sq \<notin> ProgCond \<rho> R \<Longrightarrow> sq \<in> \<lbrakk>p\<rbrakk>\<^sub>\<rho> \<Longrightarrow> 
 \<exists>i c s c' t tk. i < length sq \<and> 0 < i \<and> \<not> cstep_cond True R (sq!(i-1)) (sq!i)"
  by(clarsimp simp add: ProgCond_def)


lemma not_ProgCond_D' :
"sq \<notin> ProgCond \<rho> R \<Longrightarrow> sq \<in> \<lbrakk>p\<rbrakk>\<^sub>\<rho> \<Longrightarrow> 
 \<exists>i c s c' t tk. i < length sq \<and> 0 < i \<and>
 sq!(i - 1) = ((c, s), tk) \<and> sq!i = ((c', t), True) \<and> (s, t) \<notin> R"
  apply(simp add: ProgCond_def)
  apply(erule disjE, simp)
  apply clarsimp
  apply(rule_tac x=i in exI, simp)
  apply(case_tac "sq!i", case_tac "sq!(i-1)")
  apply(clarsimp simp add: cstep_cond_def)
  done

lemma ProgCond_prefix_cls :
"sq \<in> ProgCond \<rho> R' \<Longrightarrow> prefix pr sq \<Longrightarrow> pr \<noteq> [] \<Longrightarrow> R' \<subseteq> R \<Longrightarrow>
 pr \<in> ProgCond \<rho> R"
  apply(clarsimp simp add: ProgCond_def)
  apply(rule conjI)
   apply(rule exI, erule pcs_prefix_cls, assumption+)
  apply clarsimp
  apply(subst prefix_nth, assumption, simp)+
  apply(drule prefix_length)
  apply(drule_tac x=i in spec, simp)
  by(erule cstep_cond_mono)
    
    
lemma ProgCond_suffix_cls :
"sq \<in> ProgCond \<rho> R' \<Longrightarrow> suffix su sq \<Longrightarrow> su \<noteq> [] \<Longrightarrow> R' \<subseteq> R \<Longrightarrow>
 su \<in> ProgCond \<rho> R"
  apply(clarsimp simp add: ProgCond_def)
  apply(rule conjI)
   apply(rule exI, erule pcs_suffix_cls, assumption+)
  apply clarsimp
  apply(subst suffix_nth, assumption, simp)+
  apply(drule suffix_length)
  apply(drule_tac x="i + (length sq - length su)" in spec, simp)
  apply(drule mp, fastforce)    
  by(erule cstep_cond_mono)    



lemma ProgCond_compose :
"sq \<in> ProgCond \<rho> R \<Longrightarrow> sq' \<in> ProgCond \<rho> R \<Longrightarrow>
 fst(last sq) = fst(hd sq') \<Longrightarrow> 
 (sq @ tl sq') \<in> ProgCond \<rho> R"
  apply(case_tac "length sq' = 1")
   apply(case_tac sq', clarsimp, clarsimp)
  apply(subgoal_tac "0 < length sq \<and> 1 < length sq'")
   prefer 2
   apply(rule ccontr, simp)
   apply(clarsimp simp: ProgCond_def)
   apply(drule pcs_noNil)+
   apply(case_tac sq', clarsimp, clarsimp)
  apply(subst ProgCond_def, simp)
  apply(rule conjI)
   apply(clarsimp simp: ProgCond_def pcs_def)
   apply(frule COMP_noNil)
   apply(drule COMP_compose', assumption, simp)
   apply simp
  apply(clarsimp simp: cstep_cond_def)
  apply(drule_tac t="(sq @ tl sq') ! (i - Suc 0)" in sym)
  apply(subst (asm) nth_append)+
  apply(simp split: if_splits)
    apply(erule_tac i=i in ProgCond_D, assumption+)
   apply(subgoal_tac "i = length sq", clarsimp)
    apply(subst (asm) last_conv_nth, simp)
    apply(subst (asm) hd_conv_nth, fastforce)
    apply(subst (asm) nth_tl, simp)
    apply(case_tac "sq'!0", clarsimp)
    apply(erule_tac i=1 and sq=sq' in ProgCond_D, simp, simp (no_asm), simp, simp)
   apply fastforce
  apply(drule leI)+
  apply(subst (asm) nth_tl, simp)+
  apply(subgoal_tac " Suc (i - Suc (length sq)) = i - length sq", simp)
   apply(erule_tac sq=sq' and i="i - length sq + 1" in ProgCond_D, simp+)
  done



lemma ProgCond_decompose :
"(sq @ tl sq') \<in> ProgCond \<rho> R \<Longrightarrow>
 0 < length sq \<Longrightarrow>
 0 < length sq' \<Longrightarrow>
 fst(last sq) = fst(hd sq') \<Longrightarrow> 
 sq \<in> ProgCond \<rho> R \<and> sq' \<in> ProgCond \<rho> R"
  apply(rule conjI)
   apply(erule ProgCond_prefix_cls, simp add: prefix_def, fast, rule subset_refl)
  apply(subst ProgCond_def, simp)
  apply(rule conjI)
   apply(rule_tac x="progOf(sq'!0)" in exI)
   apply(clarsimp simp: ProgCond_def pcs_def)
   apply(rule conjI)
    apply(drule COMP_decomp, assumption)
    apply(subst (asm) hd_conv_nth, assumption)+
    apply(subst (asm) last_conv_nth, assumption)+
    apply(clarsimp simp: COMP_eq)
    apply(case_tac i, clarsimp)
     apply(drule_tac x=0 in spec)+
     apply clarsimp
     apply(subst (asm) nth_tl, simp)
     apply(erule stepR_exch, assumption)
    apply(drule_tac x=i in spec, drule mp, assumption)
    apply clarsimp
    apply(subst (asm) nth_tl, simp)+
    apply assumption
   apply(subst hd_conv_nth, assumption)
   apply(case_tac "sq'!0", clarsimp)
  apply(clarsimp simp: cstep_cond_def)
  apply(drule_tac t="sq' ! (i - Suc 0)" in sym)
  apply(case_tac "i = 1", clarsimp)
   apply(subst (asm) last_conv_nth, assumption)
   apply(subst (asm) hd_conv_nth, assumption)
   apply(case_tac "sq!(length sq - 1)", clarsimp)
   apply(drule_tac i="length sq" in ProgCond_D, simp, simp)
     apply(subst nth_append, simp)
    apply(subst nth_append, simp)
    apply(subst nth_tl, simp, assumption+)
   apply(drule_tac i="length sq + i - 1" in ProgCond_D, simp, simp)
    apply(subst nth_append, simp)
    apply(rule conjI, fastforce)
    apply clarsimp
    apply(subst nth_tl, simp)
    apply(case_tac i, simp, simp)
   apply(subst nth_append, simp)
   apply(rule conjI, fastforce)
   apply clarsimp
   apply(subst nth_tl, simp)
   apply(case_tac i, simp, simp)
  by assumption




text "Computations where the initial state satisfies a state predicate"
definition "InitCond \<rho> A = {sq |sq p c s tk. sq \<in> \<lbrakk>p\<rbrakk>\<^sub>\<rho> \<and> hd sq = ((c, s), tk) \<and> s \<in> A}"

lemma InitCond_mono :
"sq \<in> InitCond \<rho> A' \<Longrightarrow> A' \<subseteq> A \<Longrightarrow> sq \<in> InitCond \<rho> A"
  by(clarsimp simp add: InitCond_def, fastforce)


lemma InitCond_prefix_cls :
"sq \<in> InitCond \<rho> A' \<Longrightarrow> prefix pr sq \<Longrightarrow> pr \<noteq> [] \<Longrightarrow> A' \<subseteq> A \<Longrightarrow>
 pr \<in> InitCond \<rho> A"
  apply(clarsimp simp add: InitCond_def)
  apply(rule conjI)
   apply(rule exI, erule pcs_prefix_cls, assumption+)
  apply(subst hd_conv_nth, assumption)
  apply(subst prefix_nth, assumption, simp)
  apply(subst hd_conv_nth[THEN sym])
  apply(drule prefix_length, force)
  apply force
  done



text "condition upon termination"
definition "TermCond \<rho> Q = {sq |sq p. sq \<in> \<lbrakk>p\<rbrakk>\<^sub>\<rho> \<and> 
                                  (\<forall>j<length sq. progOf(sq!j) = Skip \<longrightarrow> 
                                        (\<exists>i t tk. i \<le> j \<and> sq!i = ((Skip, t), tk) \<and> t \<in> Q))}"

lemma TermCond_D :
"sq \<in> TermCond \<rho> Q \<Longrightarrow> 
 (\<forall>j < length sq. progOf(sq!j) = Skip \<longrightarrow> 
 (\<exists>i t tk. i \<le> j \<and> sq!i = ((Skip, t), tk) \<and> t \<in> Q))"
  by(simp add: TermCond_def)





end


