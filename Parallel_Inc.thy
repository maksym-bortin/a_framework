(* *********************************************************************

    Theory Parallel_Inc.thy is part of a framework for modelling,
    verification and transformation of concurrent imperative
    programs. Copyright (c) 2021  M. Bortin

    The framework is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
    For more details see the license agreement (LICENSE) you should have
    received along with the framework.
    
   ******************************************************************* *)

theory Parallel_Inc
imports RG_tactics
begin

section \<open>Increment a variable in parallel\<close>

record state =
  x  :: int
  a0 :: int
  a1 :: int


definition "inc_aux = 
INTERLEAVING-BEGIN
    \<lbrakk> rely: \<lbrace>\<ordmasculine>a0 = \<ordfeminine>a0 \<and> (\<ordmasculine>x = \<ordmasculine>a0 + \<ordmasculine>a1 \<longrightarrow> \<ordfeminine>x = \<ordfeminine>a0 + \<ordfeminine>a1)\<rbrace>,
      pre: \<lbrace> \<acute>x = \<acute>a0 + \<acute>a1 \<and> \<acute>a0=0 \<rbrace>,
      post: \<lbrace>\<acute>x = \<acute>a0 + \<acute>a1 \<and> \<acute>a0=1 \<rbrace>
    \<rbrakk>
 \<langle> \<acute>x:=\<acute>x+1; \<acute>a0:=\<acute>a0 + 1 \<rangle>   
  \<parallel>
    \<lbrakk> rely: \<lbrace>\<ordmasculine>a1 = \<ordfeminine>a1 \<and> (\<ordmasculine>x = \<ordmasculine>a0 + \<ordmasculine>a1 \<longrightarrow> \<ordfeminine>x = \<ordfeminine>a0 + \<ordfeminine>a1)\<rbrace>,
      pre: \<lbrace> \<acute>x = \<acute>a0 + \<acute>a1 \<and> \<acute>a1=0 \<rbrace>,
      post: \<lbrace>\<acute>x = \<acute>a0 + \<acute>a1 \<and> \<acute>a1=1 \<rbrace>
    \<rbrakk>
 \<langle> \<acute>x:=\<acute>x+1; \<acute>a1:=\<acute>a1+1 \<rangle>
INTERLEAVING-END"


definition "inc = 
INTERLEAVING-BEGIN
 \<acute>x:=\<acute>x+1 \<parallel> \<acute>x:=\<acute>x+1
INTERLEAVING-END"



lemma inc_aux:
 "\<Turnstile> inc_aux
 RELY \<lbrace>\<ordmasculine>x=\<ordfeminine>x \<and> \<ordmasculine>a0=\<ordfeminine>a0 \<and> \<ordmasculine>a1=\<ordfeminine>a1\<rbrace>
 PRE  \<lbrace>\<acute>x=0 \<and> \<acute>a0=0 \<and> \<acute>a1=0 \<rbrace>
 POST \<lbrace>\<acute>x=2 \<and> \<acute>a0=1 \<and> \<acute>a1=1 \<rbrace>
 GUAR \<lbrace>True\<rbrace>"
  by(unfold inc_aux_def, rg_tac)


definition "r = {(u :: 'a state_scheme, v :: 'a state_scheme) | u v. x u = x v}"

lemma inc_corr :
"\<Turnstile> inc_aux \<sqsupseteq>\<^bsub>r\<^esub> inc"
  apply(simp add: inc_aux_def inc_def r_def)
  by plain_prog_corr_tac


lemma inc :
 "\<Turnstile> inc 
 RELY \<lbrace>\<ordmasculine>x=\<ordfeminine>x\<rbrace>
 PRE  \<lbrace>\<acute>x=0\<rbrace>
 POST \<lbrace>\<acute>x=2\<rbrace>
 GUAR UNIV"
  apply(rule prog_corr_RG, rule inc_corr, rule inc_aux)
     apply clarsimp
     apply(rename_tac s t t')
     apply(rule_tac b=s in relcompI, simp)
     apply(clarsimp simp: r_def)
    apply clarify
    apply(rename_tac u)
    apply(rule_tac a="u\<lparr> a0 := 0, a1 := 0 \<rparr>" in ImageI)
  by(clarsimp simp: r_def)+


end
