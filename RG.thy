(* *********************************************************************

    Theory RG.thy is part of a framework for modelling,
    verification and transformation of concurrent imperative
    programs. Copyright (c) 2021  M. Bortin

    The framework is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
    For more details see the license agreement (LICENSE) you should have
    received along with the framework.
    
   ******************************************************************* *)

theory RG
imports Computations
begin

section "Extended Hoare-triples"

definition HoareTripleRG :: "(nat \<Rightarrow> 's LA) \<Rightarrow> 's staterel \<Rightarrow> 's set \<Rightarrow> 's LA \<Rightarrow>
                              's set \<Rightarrow> 's staterel \<Rightarrow> bool"
("_ \<Turnstile> {_ , _} _ {_ , _}" [40, 20, 20, 71, 20, 20] 71) 
where "\<rho> \<Turnstile> {R, P} p {Q, G} = 
(EnvCond \<rho> R \<inter> InitCond \<rho> P \<inter> \<lbrakk>p\<rbrakk>\<^sub>\<rho> \<subseteq> TermCond \<rho> Q \<inter> ProgCond \<rho> G)"


definition HoareTripleRG2 :: "(nat \<Rightarrow> 's LA) \<Rightarrow> 's staterel \<Rightarrow> 's staterel \<Rightarrow>  
                              's LA \<Rightarrow>
                              's staterel \<Rightarrow> 's staterel \<Rightarrow> bool"
("_ \<Turnstile>\<^sub>2 {_ , _} _ {_ , _}" [40, 20, 20, 71, 20, 20] 71)
where "\<rho> \<Turnstile>\<^sub>2 {R, P} p {Q, G} = (\<forall>\<sigma>. \<rho> \<Turnstile> {R, P `` {\<sigma>}} p {Q `` {\<sigma>}, G})" 


abbreviation HoareTripleRGjf :: "'s staterel \<Rightarrow> 's set \<Rightarrow> 's LA \<Rightarrow>
                                 's set \<Rightarrow> 's staterel \<Rightarrow> bool"
(" \<Turnstile> {_ , _} _ {_ , _}" [20, 20, 71, 20, 20] 71) 
where "\<Turnstile> {R, P} p {Q, G} \<equiv> (\<lambda>x. Skip) \<Turnstile> {R, P} p {Q, G}"

abbreviation HoareTripleRG2jf :: "'s staterel \<Rightarrow> 's staterel \<Rightarrow>  
                              's LA \<Rightarrow>
                              's staterel \<Rightarrow> 's staterel \<Rightarrow> bool"
("\<Turnstile>\<^sub>2 {_ , _} _ {_ , _}" [20, 20, 71, 20, 20] 71)
where "\<Turnstile>\<^sub>2 {R, P} p {Q, G} \<equiv> (\<lambda>x. Skip) \<Turnstile>\<^sub>2 {R, P} p {Q, G}"


lemma HoareTripleRG_subset_eq :
"\<rho> \<Turnstile> {R, P} p {Q, G} =
 (\<forall>P' \<subseteq> P. \<rho> \<Turnstile> {R, P'} p {Q, G})"
  apply(rule iffI)
   apply clarify
   apply(subst HoareTripleRG_def) 
   apply clarify
   apply(rename_tac sq)
   apply(subst (asm) HoareTripleRG_def)
   apply(erule subsetD, simp add: InitCond_def)
   apply fastforce
  apply(drule spec, drule mp, rule subset_refl)
  by assumption
 

lemma HoareTripleRG_singleton_eq :
"\<rho> \<Turnstile> {R, P} p {Q, G} =
 (\<forall>s \<in> P. \<rho> \<Turnstile> {R, {s}} p {Q, G})"
  apply(rule iffI)
   apply clarify
   apply(subst (asm) HoareTripleRG_subset_eq)
   apply(drule spec, erule mp, clarsimp)
  apply(subst HoareTripleRG_def)
  apply clarify
  apply(rename_tac sq)
  apply(clarsimp simp: InitCond_def)
  apply(drule_tac x="s" in bspec)
   apply(subst (asm) hd_conv_nth, erule pcs_noNil)
   apply simp
  apply(subst (asm) HoareTripleRG_def)
  apply(drule_tac c=sq in subsetD, simp add: InitCond_def, erule exI)
  apply clarsimp
 done


subsection "Properties of finite and infinite computations"


definition HoareTripleRG_i :: "(nat \<Rightarrow> 's LA) \<Rightarrow> 's staterel \<Rightarrow> 's set \<Rightarrow> 's LA \<Rightarrow>
                              's set \<Rightarrow> 's staterel \<Rightarrow> bool"
("_ \<Turnstile>i {_ , _} _ {_ , _}" [40, 20, 20, 71, 20, 20] 71) 
where "\<rho> \<Turnstile>i {R, P} p {Q, G} \<equiv> 
(EnvCond \<rho> R \<inter> InitCond \<rho> P \<inter> \<lbrakk>p\<rbrakk>\<^sub>\<rho> \<subseteq> TermCond \<rho> Q \<inter> ProgCond \<rho> G) \<and>
(EnvCond_i \<rho> R \<inter> InitCond_i \<rho> P \<inter> iCOMP \<rho> \<inter> {sq. progOf(sq 0) = p} \<subseteq> 
 TermCond_i \<rho> Q \<inter> ProgCond_i \<rho> G)"


abbreviation HoareTripleRGjf_i :: "'s staterel \<Rightarrow> 's set \<Rightarrow> 's LA \<Rightarrow>
                              's set \<Rightarrow> 's staterel \<Rightarrow> bool"
("\<Turnstile>i {_ , _} _ {_ , _}" [20, 20, 71, 20, 20] 71) 
where "\<Turnstile>i {R, P} p {Q, G} \<equiv> (\<lambda>x. Skip) \<Turnstile>i {R, P} p {Q, G}"



theorem HoareTripleRG_i :
"\<rho> \<Turnstile> {R, P} p {Q, G} \<Longrightarrow>
 \<rho> \<Turnstile>i {R, P} p {Q, G}" 
  apply(subst HoareTripleRG_i_def)
  apply(rule conjI)
   apply(simp add: HoareTripleRG_def)
  apply clarify
  apply(rename_tac isq)
  apply simp
  apply(case_tac "isq 0", clarsimp)
  apply(rename_tac s0 tk0)
  apply(subgoal_tac "\<forall>j. fprefix isq j \<in> TermCond \<rho> Q \<inter> ProgCond \<rho> G")
   apply(rule conjI)
    apply(clarsimp simp: TermCond_i_def)
    apply(drule_tac x=j in spec, clarify)
    apply(drule TermCond_D)
    apply(simp add: fprefix_length)
    apply(drule_tac x=j in spec, clarsimp simp: fprefix_nth)
    apply fast
   apply(clarsimp simp: ProgCond_i_def cstep_cond_def)
   apply(drule_tac x=i in spec, clarify)
   apply(erule_tac i=i in ProgCond_D)
      apply(simp add: fprefix_length)
     apply assumption
    apply(simp add: fprefix_nth)
    apply(erule sym)
   apply(simp add: fprefix_nth)
  apply(rule allI)
  apply(frule_tac n=j in fprefix_COMP)
  apply(subst (asm) HoareTripleRG_def)
  apply(drule_tac c="fprefix isq j" in subsetD)
   apply simp
   apply(rule conjI)
    apply(simp add: EnvCond_def)
    apply(rule conjI)
     apply(rule_tac x="progOf(isq 0)" in exI, simp add: pcs_def)
     apply(subst hd_conv_nth, erule COMP_noNil)
     apply(simp add: fprefix_nth)
    apply(clarsimp simp: fprefix_length fprefix_nth)
    apply(clarsimp simp: EnvCond_i_def)
   apply(rule conjI)
    apply(simp add: InitCond_def)
    apply(rule conjI)
     apply(rule_tac x="progOf(isq 0)" in exI, simp add: pcs_def)
     apply(subst hd_conv_nth, erule COMP_noNil)
     apply(simp add: fprefix_nth)
    apply(subst hd_conv_nth, erule COMP_noNil)
    apply(simp add: fprefix_nth InitCond_i_def)
   apply(simp add: pcs_def)
   apply(subst hd_conv_nth, erule COMP_noNil)
   apply(simp add: fprefix_nth)
  by assumption



section "Syntactic sugaring"

syntax
   "_rg" :: "(nat \<Rightarrow> 's LA) \<Rightarrow> 's LA \<Rightarrow> 's staterel \<Rightarrow> 's set \<Rightarrow> 's set \<Rightarrow>'s staterel \<Rightarrow> bool"  
    ("(4_)/ \<Turnstile> _//RELY _//PRE _//POST _//GUAR _" [60,0,0,0,0] 45)
translations
"_rg \<rho> p R P Q G" \<rightharpoonup> "\<rho> \<Turnstile> {R, P} p {Q, G}"


ML \<open> val syntax_debug = false \<close>

print_translation \<open> 
   let
    fun rg_tr (rho :: R :: P :: p :: Q :: G :: ts) =
        let val _ = if syntax_debug then writeln "rg" else ()
          in Syntax.const @{syntax_const "_rg"} $
               rho $ p $ R $ P $ Q $ G
          end
      | rg_tr x = let val _ = writeln (@{make_string} {x = x}) 
            in raise Match end;

  in
   [(@{const_syntax HoareTripleRG}, K rg_tr)]
  end
\<close>

syntax
   "_rgjf" :: "'s LA \<Rightarrow> 's staterel \<Rightarrow> 's set \<Rightarrow> 's set \<Rightarrow>'s staterel \<Rightarrow> bool"  
    ("\<Turnstile> _//RELY _//PRE _//POST _//GUAR _" [0,0,0,0] 45)
translations
"_rgjf p R P Q G" \<rightharpoonup> "\<Turnstile> {R, P} p {Q, G}"


print_translation \<open> 
   let
    fun rgjf_tr (R :: P :: p :: Q :: G :: ts) =
        let val _ = if syntax_debug then writeln "rgjf" else ()
          in Syntax.const @{syntax_const "_rgjf"} $
               p $ R $ P $ Q $ G
          end
      | rgjf_tr x = let val _ = writeln (@{make_string} {x = x}) 
            in raise Match end;

  in
   [(@{const_syntax HoareTripleRGjf}, K rgjf_tr)]
  end
\<close>

syntax
   "_rgi" :: "(nat \<Rightarrow> 's LA) \<Rightarrow> 's LA \<Rightarrow> 's staterel \<Rightarrow> 's set \<Rightarrow> 's set \<Rightarrow>'s staterel \<Rightarrow> bool"  
    ("(4_)/ \<Turnstile>i _//RELY _//PRE _//POST _//GUAR _" [60,0,0,0,0] 45)
translations
"_rgi \<rho> p R P Q G" \<rightharpoonup> "\<rho> \<Turnstile>i {R, P} p {Q, G}"

print_translation \<open> 
   let
    fun rgi_tr (rho :: R :: P :: p :: Q :: G :: ts) =
        let val _ = if syntax_debug then writeln "rgi" else ()
          in Syntax.const @{syntax_const "_rgi"} $
               rho $ p $ R $ P $ Q $ G
          end
      | rgi_tr x = let val _ = writeln (@{make_string} {x = x}) 
            in raise Match end;

  in
   [(@{const_syntax HoareTripleRG_i}, K rgi_tr)]
  end
\<close>


syntax
   "_rgijf" :: "'s LA \<Rightarrow> 's staterel \<Rightarrow> 's set \<Rightarrow> 's set \<Rightarrow>'s staterel \<Rightarrow> bool"  
    ("\<Turnstile>i _//RELY _//PRE _//POST _//GUAR _" [0,0,0,0] 45)
translations
"_rgijf p R P Q G" \<rightharpoonup> "\<Turnstile>i {R, P} p {Q, G}"

print_translation \<open> 
   let
    fun rgijf_tr (R :: P :: p :: Q :: G :: ts) =
        let val _ = if syntax_debug then writeln "rgijf" else ()
          in Syntax.const @{syntax_const "_rgijf"} $
               p $ R $ P $ Q $ G
          end
      | rgijf_tr x = let val _ = writeln (@{make_string} {x = x}) 
            in raise Match end;

  in
   [(@{const_syntax HoareTripleRGjf_i}, K rgijf_tr)]
  end
\<close>






syntax
   "_rg2" :: "(nat \<Rightarrow> 's LA) \<Rightarrow> 's LA \<Rightarrow> 's staterel \<Rightarrow> 
             's staterel \<Rightarrow> 's staterel \<Rightarrow> 's staterel \<Rightarrow> bool"  
    ("(4_)/ \<Turnstile>\<^sub>2 _//RELY _//PRE _//POST _//GUAR _" [60,0,0,0,0] 45)
translations
"_rg2 \<rho> p R P Q G" \<rightharpoonup> "\<rho> \<Turnstile>\<^sub>2 {R, P} p {Q, G}"


ML \<open> val syntax_debug = false \<close>
print_translation \<open> let
    fun rg2_tr (rho :: R :: P :: p :: Q :: G :: ts) =
        let val _ = if syntax_debug then writeln "rg2" else ()
          in Syntax.const @{syntax_const "_rg2"} $
               rho $ p $ R $ P $ Q $ G
          end
      | rg2_tr x = let val _ = writeln (@{make_string} {x = x})
            in raise Match end;

  in
   [(@{const_syntax HoareTripleRG2}, K rg2_tr)]
  end
\<close>

syntax
   "_rg2jf" :: "'s LA \<Rightarrow> 's staterel \<Rightarrow> 
                's staterel \<Rightarrow> 's staterel \<Rightarrow> 's staterel \<Rightarrow> bool"  
    ("\<Turnstile>\<^sub>2 _//RELY _//PRE _//POST _//GUAR _" [0,0,0,0] 45)
translations
"_rg2jf p R P Q G" \<rightharpoonup> "\<Turnstile>\<^sub>2 {R, P} p {Q, G}"

print_translation \<open> let
    fun rg2jf_tr (R :: P :: p :: Q :: G :: ts) =
        let val _ = if syntax_debug then writeln "rg2jf" else ()
          in Syntax.const @{syntax_const "_rg2jf"} $
               p $ R $ P $ Q $ G
          end
      | rg2jf_tr x = let val _ = writeln (@{make_string} {x = x})
            in raise Match end;

  in
   [(@{const_syntax HoareTripleRG2jf}, K rg2jf_tr)]
  end
\<close>



end

