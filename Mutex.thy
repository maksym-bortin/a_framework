(* *********************************************************************

    Theory Mutex.thy is part of a framework for modelling,
    verification and transformation of concurrent imperative
    programs. Copyright (c) 2021  M. Bortin

    The framework is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
    For more details see the license agreement (LICENSE) you should have
    received along with the framework.
    
   ******************************************************************* *)

theory Mutex
imports RG_tactics
begin


section "Modelling the mutual exclusion algorithm by G. L. Peterson"
  
record 'a mutex =
 flag0     :: bool
 flag1     :: bool
 turn      :: bool
 turn_aux0 :: bool
 turn_aux1 :: bool
 shared    :: "'a"
 local0    :: "'a"
 local1    :: "'a"
 
 
definition "inv0 s \<equiv> turn_aux0 s \<longrightarrow> flag0 s \<longrightarrow> turn s"
  
definition "inv1 s \<equiv> turn_aux1 s \<longrightarrow> flag1 s \<longrightarrow> \<not> turn s"
   
    

    
section "The model with auxiliaries"    

definition 
"thread0_aux cs P \<equiv>
  \<acute>flag0 := True;
   \<lbrakk>ann: \<lbrace> \<acute>flag0 \<and> \<not>\<acute>turn_aux0 \<and> P \<acute>shared \<rbrace> \<rbrakk>\<langle>\<acute>turn := True;
                                                 \<acute>turn_aux0 := True\<rangle>;
  WHILE \<lbrace>\<acute>flag1 \<and> \<acute>turn\<rbrace> 
  \<lbrakk> inv: \<lbrace> \<acute>flag0 \<and> \<acute>turn_aux0 \<and> P \<acute>shared \<rbrace> \<rbrakk>
  DO SKIP OD; 
  cs;
  \<acute>flag0 := False"
 
definition 
"thread1_aux cs P \<equiv>
  \<acute>flag1 := True;
   \<lbrakk>ann: \<lbrace> \<acute>flag1 \<and> \<not>\<acute>turn_aux1 \<and> P \<acute>shared \<rbrace> \<rbrakk>\<langle>\<acute>turn := False;
                                                 \<acute>turn_aux1 := True\<rangle>;
  WHILE \<lbrace> \<acute>flag0 \<and> \<not>\<acute>turn \<rbrace> 
   \<lbrakk> inv: \<lbrace> \<acute>flag1 \<and> \<acute>turn_aux1 \<and> P \<acute>shared \<rbrace> \<rbrakk>
  DO SKIP OD;
  cs;
  \<acute>flag1 := False" 
    
    
definition
"mutex_aux P0 cs0 Q0 P1 cs1 Q1 \<equiv>
   INTERLEAVING-BEGIN
    \<lbrakk> rely: \<lbrace> \<ordmasculine>flag0 = \<ordfeminine>flag0 \<and> \<ordmasculine>turn_aux0 = \<ordfeminine>turn_aux0 \<and> \<ordmasculine>local0 = \<ordfeminine>local0 \<and>
             (\<ordmasculine>turn_aux0 \<longrightarrow> \<ordmasculine>flag0 \<longrightarrow> \<ordmasculine>inv1 \<longrightarrow> \<ordmasculine>shared = \<ordfeminine>shared) \<and>
             (\<ordmasculine>inv1 \<longrightarrow> \<ordfeminine>inv1) \<and>
             (P0 \<ordmasculine>shared \<longrightarrow> P0 \<ordfeminine>shared) \<and> (Q0 \<ordmasculine>shared \<longrightarrow> Q0 \<ordfeminine>shared) \<rbrace>,
      pre:  \<lbrace> \<not>\<acute>turn_aux0 \<and> P0 \<acute>shared \<rbrace>,
      post: \<lbrace>  Q0 \<acute>shared \<rbrace> 
     \<rbrakk>
    thread0_aux cs0 P0 
  \<parallel>
    \<lbrakk> rely: \<lbrace> \<ordmasculine>flag1 = \<ordfeminine>flag1 \<and> \<ordmasculine>turn_aux1 = \<ordfeminine>turn_aux1 \<and> \<ordmasculine>local1 = \<ordfeminine>local1 \<and>
             (\<ordmasculine>turn_aux1 \<longrightarrow> \<ordmasculine>flag1 \<longrightarrow> \<ordmasculine>inv0 \<longrightarrow> \<ordmasculine>shared = \<ordfeminine>shared) \<and>
             (\<ordmasculine>inv0 \<longrightarrow> \<ordfeminine>inv0) \<and> 
             (P1 \<ordmasculine>shared \<longrightarrow> P1 \<ordfeminine>shared) \<and> (Q1 \<ordmasculine>shared \<longrightarrow> Q1 \<ordfeminine>shared) \<rbrace>,
     pre:  \<lbrace> \<not>\<acute>turn_aux1 \<and> P1 \<acute>shared \<rbrace>,
     post: \<lbrace>  Q1 \<acute>shared \<rbrace>
     \<rbrakk>
    thread1_aux cs1 P1 
   INTERLEAVING-END" 


section "The model without auxiliaries"    


definition 
"thread0 cs \<equiv>
  \<acute>flag0 := True;
  \<acute>turn := True;
  WHILE  \<lbrace>\<acute>flag1 \<and> \<acute>turn\<rbrace> 
  DO SKIP OD; 
  cs;
  \<acute>flag0 := False"

definition 
"thread1 cs \<equiv>
  \<acute>flag1 := True;
  \<acute>turn := False;
  WHILE \<lbrace>\<acute>flag0 \<and> \<not>\<acute>turn\<rbrace> 
  DO SKIP OD;
  cs;
  \<acute>flag1 := False" 


definition
"mutex cs0 cs1 \<equiv>
   INTERLEAVING-BEGIN
    thread0 cs0 
  \<parallel>
    thread1 cs1
   INTERLEAVING-END" 



section "Properties"
  
definition "mutexR0 = {((s :: ('a, 'b) mutex_scheme), (t :: ('a, 'b) mutex_scheme)). 
                       turn_aux0 t \<and> flag0 t \<and> inv1 t \<and> s = t}"  

lemma thread0_aux:
" \<rho> \<Turnstile> cs0 
  RELY \<lbrace> \<ordmasculine>local0 = \<ordfeminine>local0 \<and> \<ordmasculine>shared = \<ordfeminine>shared \<rbrace>
  PRE  \<lbrace> P0 \<acute>shared \<rbrace>
  POST \<lbrace> Q0 \<acute>shared \<rbrace> 
  GUAR \<lbrace> \<ordmasculine>flag0 = \<ordfeminine>flag0 \<and> \<ordmasculine>flag1 = \<ordfeminine>flag1 \<and> \<ordmasculine>turn = \<ordfeminine>turn \<and>   
         \<ordmasculine>turn_aux0 = \<ordfeminine>turn_aux0 \<and> \<ordmasculine>turn_aux1 = \<ordfeminine>turn_aux1 \<and> \<ordmasculine>local1 = \<ordfeminine>local1 \<and>
         (P1 \<ordmasculine>shared \<longrightarrow> P1 \<ordfeminine>shared) \<and> (Q1 \<ordmasculine>shared \<longrightarrow> Q1 \<ordfeminine>shared)  \<rbrace> \<Longrightarrow>

 \<rho> \<Turnstile> cs0 \<sqsupseteq>\<^bsub>mutexR0\<^esub> cs0 \<Longrightarrow>

 \<rho> \<Turnstile> thread0_aux cs0 P0 
 RELY \<lbrace> \<ordmasculine>flag0 = \<ordfeminine>flag0 \<and> \<ordmasculine>turn_aux0 = \<ordfeminine>turn_aux0 \<and> \<ordmasculine>local0 = \<ordfeminine>local0 \<and>
        (\<ordmasculine>turn_aux0 \<longrightarrow> \<ordmasculine>flag0 \<longrightarrow> \<ordmasculine>inv1 \<longrightarrow> \<ordmasculine>shared = \<ordfeminine>shared) \<and>
        (\<ordmasculine>inv1 \<longrightarrow> \<ordfeminine>inv1) \<and> 
        (P0 \<ordmasculine>shared \<longrightarrow> P0 \<ordfeminine>shared) \<and> (Q0 \<ordmasculine>shared \<longrightarrow> Q0 \<ordfeminine>shared)  \<rbrace>
  PRE  \<lbrace> \<not>\<acute>turn_aux0 \<and> P0 \<acute>shared \<rbrace> 
  POST \<lbrace> Q0 \<acute>shared \<rbrace>
 GUAR \<lbrace> \<ordmasculine>flag1 = \<ordfeminine>flag1 \<and> \<ordmasculine>turn_aux1 = \<ordfeminine>turn_aux1 \<and> \<ordmasculine>local1 = \<ordfeminine>local1 \<and>
        (\<ordmasculine>turn_aux1 \<longrightarrow> \<ordmasculine>flag1 \<longrightarrow> \<ordmasculine>inv0 \<longrightarrow> \<ordmasculine>shared = \<ordfeminine>shared) \<and>
        (\<ordmasculine>inv0 \<longrightarrow> \<ordfeminine>inv0) \<and> 
        (P1 \<ordmasculine>shared \<longrightarrow> P1 \<ordfeminine>shared) \<and> (Q1 \<ordmasculine>shared \<longrightarrow> Q1 \<ordfeminine>shared)  \<rbrace>"
  unfolding thread0_aux_def
  apply rg_tac
     apply(simp (no_asm) add: inv0_def)
    apply(erule prog_corr_RG, assumption)
       apply(thin_tac _)+
       apply clarsimp
       apply(rename_tac s t t')
       apply(clarsimp simp: mutexR0_def)
       apply(rule_tac b=t' in relcompI, simp, simp)
      apply(clarsimp simp: mutexR0_def inv1_def)
     apply(clarsimp simp: mutexR0_def) 
     apply(simp (no_asm) add: inv0_def)
    apply(thin_tac _)+
    apply(clarsimp simp: mutexR0_def)
    apply(rule conjI)
     apply(simp add: inv0_def inv1_def)
    apply(simp add: inv0_def)+
  done

    

definition "mutexR1 = {((s :: ('a, 'b) mutex_scheme), (t :: ('a, 'b) mutex_scheme)). 
                       s = t \<and> turn_aux1 t \<and> flag1 t \<and> inv0 t}"  
    
lemma thread1_aux:
" \<rho> \<Turnstile> cs1 
  RELY \<lbrace> \<ordmasculine>local1 = \<ordfeminine>local1 \<and> \<ordmasculine>shared = \<ordfeminine>shared \<rbrace>
  PRE  \<lbrace> P1 \<acute>shared \<rbrace>
  POST \<lbrace> Q1 \<acute>shared \<rbrace> 
  GUAR \<lbrace> \<ordmasculine>flag0 = \<ordfeminine>flag0 \<and> \<ordmasculine>flag1 = \<ordfeminine>flag1 \<and> \<ordmasculine>turn = \<ordfeminine>turn \<and>   
         \<ordmasculine>turn_aux0 = \<ordfeminine>turn_aux0 \<and> \<ordmasculine>turn_aux1 = \<ordfeminine>turn_aux1 \<and> \<ordmasculine>local0 = \<ordfeminine>local0 \<and>
         (P0 \<ordmasculine>shared \<longrightarrow> P0 \<ordfeminine>shared) \<and> (Q0 \<ordmasculine>shared \<longrightarrow> Q0 \<ordfeminine>shared)  \<rbrace> \<Longrightarrow>

 \<rho> \<Turnstile> cs1 \<sqsupseteq>\<^bsub>mutexR1\<^esub> cs1 \<Longrightarrow>

 \<rho> \<Turnstile> thread1_aux cs1 P1 
 RELY \<lbrace> \<ordmasculine>flag1 = \<ordfeminine>flag1 \<and> \<ordmasculine>turn_aux1 = \<ordfeminine>turn_aux1 \<and> \<ordmasculine>local1 = \<ordfeminine>local1 \<and>
        (\<ordmasculine>turn_aux1 \<longrightarrow> \<ordmasculine>flag1 \<longrightarrow> \<ordmasculine>inv0 \<longrightarrow> \<ordmasculine>shared = \<ordfeminine>shared) \<and>
        (\<ordmasculine>inv0 \<longrightarrow> \<ordfeminine>inv0) \<and> 
        (P1 \<ordmasculine>shared \<longrightarrow> P1 \<ordfeminine>shared) \<and> (Q1 \<ordmasculine>shared \<longrightarrow> Q1 \<ordfeminine>shared)  \<rbrace> 
  PRE  \<lbrace> \<not>\<acute>turn_aux1 \<and> P1 \<acute>shared \<rbrace> 
  POST \<lbrace> Q1 \<acute>shared \<rbrace> 
  GUAR \<lbrace> \<ordmasculine>flag0 = \<ordfeminine>flag0 \<and> \<ordmasculine>turn_aux0 = \<ordfeminine>turn_aux0 \<and> \<ordmasculine>local0 = \<ordfeminine>local0 \<and>
        (\<ordmasculine>turn_aux0 \<longrightarrow> \<ordmasculine>flag0 \<longrightarrow> \<ordmasculine>inv1 \<longrightarrow> \<ordmasculine>shared = \<ordfeminine>shared) \<and>
        (\<ordmasculine>inv1 \<longrightarrow> \<ordfeminine>inv1) \<and> 
        (P0 \<ordmasculine>shared \<longrightarrow> P0 \<ordfeminine>shared) \<and> (Q0 \<ordmasculine>shared \<longrightarrow> Q0 \<ordfeminine>shared)  \<rbrace>"
  unfolding thread1_aux_def
  apply rg_tac
     apply(simp (no_asm) add: inv1_def)
    apply(erule prog_corr_RG, assumption)
       apply(thin_tac _)+
       apply clarsimp
       apply(rename_tac s t t')
       apply(clarsimp simp: mutexR1_def)
       apply(rule_tac b=t' in relcompI, simp, simp)
      apply(clarsimp simp: mutexR1_def inv0_def)
     apply(clarsimp simp: mutexR1_def) 
     apply(simp (no_asm) add: inv1_def)
    apply(thin_tac _)+
    apply(clarsimp simp: mutexR1_def)
    apply(rule conjI)
     apply(simp add: inv0_def inv1_def)
    apply(simp add: inv1_def)+
  done


    
lemma mutex_aux :
" \<rho> \<Turnstile> cs0 
  RELY \<lbrace> \<ordmasculine>local0 = \<ordfeminine>local0 \<and> \<ordmasculine>shared = \<ordfeminine>shared \<rbrace>
  PRE  \<lbrace> P0 \<acute>shared \<rbrace>
  POST \<lbrace> Q0 \<acute>shared \<rbrace> 
  GUAR \<lbrace> \<ordmasculine>flag0 = \<ordfeminine>flag0 \<and> \<ordmasculine>flag1 = \<ordfeminine>flag1 \<and> \<ordmasculine>turn = \<ordfeminine>turn \<and>   
         \<ordmasculine>turn_aux0 = \<ordfeminine>turn_aux0 \<and> \<ordmasculine>turn_aux1 = \<ordfeminine>turn_aux1 \<and> \<ordmasculine>local1 = \<ordfeminine>local1 \<and>
         (P1 \<ordmasculine>shared \<longrightarrow> P1 \<ordfeminine>shared) \<and> (Q1 \<ordmasculine>shared \<longrightarrow> Q1 \<ordfeminine>shared)  \<rbrace> \<Longrightarrow>

  \<rho> \<Turnstile> cs1 
  RELY \<lbrace> \<ordmasculine>local1 = \<ordfeminine>local1 \<and> \<ordmasculine>shared = \<ordfeminine>shared \<rbrace>
  PRE  \<lbrace> P1 \<acute>shared \<rbrace>
  POST \<lbrace> Q1 \<acute>shared \<rbrace> 
  GUAR \<lbrace> \<ordmasculine>flag0 = \<ordfeminine>flag0 \<and> \<ordmasculine>flag1 = \<ordfeminine>flag1 \<and> \<ordmasculine>turn = \<ordfeminine>turn \<and>   
         \<ordmasculine>turn_aux0 = \<ordfeminine>turn_aux0 \<and> \<ordmasculine>turn_aux1 = \<ordfeminine>turn_aux1 \<and> \<ordmasculine>local0 = \<ordfeminine>local0 \<and>
         (P0 \<ordmasculine>shared \<longrightarrow> P0 \<ordfeminine>shared) \<and> (Q0 \<ordmasculine>shared \<longrightarrow> Q0 \<ordfeminine>shared)  \<rbrace> \<Longrightarrow>

  \<rho> \<Turnstile> cs0 \<sqsupseteq>\<^bsub>mutexR0\<^esub> cs0 \<Longrightarrow>
  \<rho> \<Turnstile> cs1 \<sqsupseteq>\<^bsub>mutexR1\<^esub> cs1 \<Longrightarrow>

  \<rho> \<Turnstile> mutex_aux P0 cs0 Q0 P1 cs1 Q1  
  RELY Id
  PRE  \<lbrace> P0 \<acute>shared \<and> P1 \<acute>shared \<and> \<not> \<acute>turn_aux0 \<and> \<not> \<acute>turn_aux1  \<rbrace>
  POST \<lbrace> Q0 \<acute>shared \<and> Q1 \<acute>shared \<rbrace>
  GUAR \<lbrace> True \<rbrace>"
  unfolding mutex_aux_def  
  apply(rg_tac thread0_aux thread1_aux)
      apply fast
     apply simp+
  done


    
    
section "The property of mutex by program correspondence"
  
definition "mutexR = {((s :: ('a, 'b) mutex_scheme), (t :: ('a, 'b) mutex_scheme)). 
                       flag0 s = flag0 t \<and>
                       flag1 s = flag1 t \<and>
                       turn s = turn t \<and>
                       shared s = shared t \<and>
                       local0 s = local0 t \<and>
                       local1 s = local1 t}"
  
  
 
  
lemma mutex :
" \<rho> \<Turnstile> cs0 
  RELY \<lbrace> \<ordmasculine>local0 = \<ordfeminine>local0 \<and> \<ordmasculine>shared = \<ordfeminine>shared \<rbrace>
  PRE  \<lbrace> P0 \<acute>shared \<rbrace>
  POST \<lbrace> Q0 \<acute>shared \<rbrace> 
  GUAR \<lbrace> \<ordmasculine>flag0 = \<ordfeminine>flag0 \<and> \<ordmasculine>flag1 = \<ordfeminine>flag1 \<and> \<ordmasculine>turn = \<ordfeminine>turn \<and>   
         \<ordmasculine>turn_aux0 = \<ordfeminine>turn_aux0 \<and> \<ordmasculine>turn_aux1 = \<ordfeminine>turn_aux1 \<and> \<ordmasculine>local1 = \<ordfeminine>local1 \<and>
         (P1 \<ordmasculine>shared \<longrightarrow> P1 \<ordfeminine>shared) \<and> (Q1 \<ordmasculine>shared \<longrightarrow> Q1 \<ordfeminine>shared)  \<rbrace> \<Longrightarrow>

  \<rho> \<Turnstile> cs1 
  RELY \<lbrace> \<ordmasculine>local1 = \<ordfeminine>local1 \<and> \<ordmasculine>shared = \<ordfeminine>shared \<rbrace>
  PRE  \<lbrace> P1 \<acute>shared \<rbrace>
  POST \<lbrace> Q1 \<acute>shared \<rbrace> 
  GUAR \<lbrace> \<ordmasculine>flag0 = \<ordfeminine>flag0 \<and> \<ordmasculine>flag1 = \<ordfeminine>flag1 \<and> \<ordmasculine>turn = \<ordfeminine>turn \<and>   
         \<ordmasculine>turn_aux0 = \<ordfeminine>turn_aux0 \<and> \<ordmasculine>turn_aux1 = \<ordfeminine>turn_aux1 \<and> \<ordmasculine>local0 = \<ordfeminine>local0 \<and>
         (P0 \<ordmasculine>shared \<longrightarrow> P0 \<ordfeminine>shared) \<and> (Q0 \<ordmasculine>shared \<longrightarrow> Q0 \<ordfeminine>shared)  \<rbrace> \<Longrightarrow>

  \<rho> \<Turnstile> cs0 \<sqsupseteq>\<^bsub>mutexR0\<^esub> cs0 \<Longrightarrow>
  \<rho> \<Turnstile> cs1 \<sqsupseteq>\<^bsub>mutexR1\<^esub> cs1 \<Longrightarrow>
  \<rho> \<Turnstile> cs0 \<sqsupseteq>\<^bsub>mutexR\<^esub> cs0 \<Longrightarrow>
  \<rho> \<Turnstile> cs1 \<sqsupseteq>\<^bsub>mutexR\<^esub> cs1 \<Longrightarrow>

  \<rho> \<Turnstile> mutex cs0 cs1  
  RELY Id 
  PRE  \<lbrace> P0 \<acute>shared \<and> P1 \<acute>shared \<rbrace>
  POST \<lbrace> Q0 \<acute>shared \<and> Q1 \<acute>shared \<rbrace>
  GUAR \<lbrace> True \<rbrace>"
  apply(rule_tac r=mutexR in prog_corr_RG[rotated 1])
       apply(erule mutex_aux, assumption+)
      apply fast
     apply clarsimp
     apply(rule_tac a="x\<lparr> turn_aux0 := False, turn_aux1 := False \<rparr>" in ImageI)
     apply(clarsimp simp: mutexR_def)+
  apply(simp add: mutex_aux_def mutex_def)
  apply plain_prog_corr_tac
   apply(clarsimp simp: thread1_aux_def thread1_def)
   apply plain_prog_corr_tac
  apply(clarsimp simp: thread0_aux_def thread0_def)
  apply plain_prog_corr_tac
  done


section "An example instantiation"
  
    
definition
  "shared_upd0 \<equiv> \<acute>local0 := \<acute>shared;
                 \<acute>local0 := {0} \<union> \<acute>local0;
                  \<acute>shared := \<acute>local0"
        
definition
  "shared_upd1 \<equiv> \<acute>local1 := \<acute>shared;
                 \<acute>local1 := {1} \<union> \<acute>local1;
                  \<acute>shared := \<acute>local1"
  
lemma shared_upd0 :
"\<rho> \<Turnstile> shared_upd0
 RELY \<lbrace> \<ordmasculine>local0 = \<ordfeminine>local0 \<and> \<ordmasculine>shared = \<ordfeminine>shared \<rbrace>
  PRE  UNIV
  POST \<lbrace> 0 \<in> \<acute>shared \<rbrace> 
  GUAR \<lbrace> \<ordmasculine>flag0 = \<ordfeminine>flag0 \<and> \<ordmasculine>flag1 = \<ordfeminine>flag1 \<and> \<ordmasculine>turn = \<ordfeminine>turn \<and>   
         \<ordmasculine>turn_aux0 = \<ordfeminine>turn_aux0 \<and> \<ordmasculine>turn_aux1 = \<ordfeminine>turn_aux1 \<and> \<ordmasculine>local1 = \<ordfeminine>local1 \<and>
         ((1 \<in> \<ordmasculine>shared) \<longrightarrow> (1 \<in> \<ordfeminine>shared)) \<rbrace> " 
  unfolding shared_upd0_def
  by rg_tac

lemma shared_upd1 :
"\<rho> \<Turnstile> shared_upd1
 RELY \<lbrace> \<ordmasculine>local1 = \<ordfeminine>local1 \<and> \<ordmasculine>shared = \<ordfeminine>shared \<rbrace>
  PRE  UNIV
  POST \<lbrace> 1 \<in> \<acute>shared \<rbrace> 
  GUAR \<lbrace> \<ordmasculine>flag0 = \<ordfeminine>flag0 \<and> \<ordmasculine>flag1 = \<ordfeminine>flag1 \<and> \<ordmasculine>turn = \<ordfeminine>turn \<and>   
         \<ordmasculine>turn_aux0 = \<ordfeminine>turn_aux0 \<and> \<ordmasculine>turn_aux1 = \<ordfeminine>turn_aux1 \<and> \<ordmasculine>local0 = \<ordfeminine>local0 \<and>
         ((0 \<in> \<ordmasculine>shared) \<longrightarrow> (0 \<in> \<ordfeminine>shared)) \<rbrace> " 
  unfolding shared_upd1_def
  by rg_tac

   

    
definition
  "concurrent_upds \<equiv> mutex shared_upd0 shared_upd1" 
    

lemma concurrent_upds[simplified] :
"\<rho> \<Turnstile> concurrent_upds
  RELY Id
  PRE  \<lbrace> True \<and> True \<rbrace>
  POST \<lbrace> (0 \<in> \<acute>shared) \<and> (1 \<in> \<acute>shared) \<rbrace>
  GUAR \<lbrace> True \<rbrace>"
  unfolding concurrent_upds_def
  apply(rule mutex)
       apply(simp, rule shared_upd0)
      apply(simp, rule shared_upd1)
     apply(simp_all add: shared_upd0_def shared_upd1_def mutexR0_def mutexR1_def mutexR_def inv0_def inv1_def)
     apply plain_prog_corr_tac+
  done




section "Deriving the global guarantees for liveness"


definition 
"cs_cond \<rho> cs = 
(\<rho> \<Turnstile> cs 
  RELY \<lbrace> True \<rbrace>
  PRE  \<lbrace> True \<rbrace>
  POST \<lbrace> True \<rbrace> 
  GUAR \<lbrace> \<ordmasculine>flag0 = \<ordfeminine>flag0 \<and> \<ordmasculine>flag1 = \<ordfeminine>flag1 \<and> \<ordmasculine>turn = \<ordfeminine>turn \<and>   
         \<ordmasculine>turn_aux0 = \<ordfeminine>turn_aux0 \<and> \<ordmasculine>turn_aux1 = \<ordfeminine>turn_aux1 \<rbrace>)"


text "Note that the rely condition \<ordmasculine>flag0 = \<ordfeminine>flag0 in thread0_auxG below
      is solely due to the annotations in the definition of thread0_aux 
      which are too detailed for the current setting. 
      This condition could be simply discarded if the annotations would be 
      adjusted accordingly."
 
lemma thread0_auxG:
"cs_cond \<rho> cs0 \<Longrightarrow> 
 \<rho> \<Turnstile> thread0_aux cs0 (\<lambda>a. True)
 RELY \<lbrace> \<ordmasculine>flag0 = \<ordfeminine>flag0 \<and> \<ordmasculine>turn_aux0 = \<ordfeminine>turn_aux0 \<rbrace>
  PRE \<lbrace> \<not>\<acute>turn_aux0 \<rbrace> 
  POST \<lbrace> True \<rbrace>
 GUAR \<lbrace> \<ordmasculine>flag1 = \<ordfeminine>flag1 \<and> \<ordmasculine>turn_aux1 = \<ordfeminine>turn_aux1 \<and>
        (\<ordmasculine>turn_aux0 \<longrightarrow> \<ordfeminine>turn_aux0) \<and>
        (\<ordmasculine>turn_aux0 \<longrightarrow> \<ordmasculine>turn = \<ordfeminine>turn) \<and>
        (\<ordmasculine>turn_aux0 \<longrightarrow> \<ordfeminine>flag0 \<longrightarrow> \<ordmasculine>flag0) \<rbrace>"
  unfolding thread0_aux_def cs_cond_def 
  apply rg_tac
  apply(erule ConseqRG, clarsimp+)
  done



lemma thread1_auxG:
"cs_cond \<rho> cs1 \<Longrightarrow> 
 \<rho> \<Turnstile> thread1_aux cs1 (\<lambda>a. True)
 RELY \<lbrace> \<ordmasculine>flag1 = \<ordfeminine>flag1 \<and> \<ordmasculine>turn_aux1 = \<ordfeminine>turn_aux1 \<rbrace>
  PRE  \<lbrace> \<not>\<acute>turn_aux1 \<rbrace> 
  POST \<lbrace> True \<rbrace>
 GUAR \<lbrace> \<ordmasculine>flag0 = \<ordfeminine>flag0 \<and> \<ordmasculine>turn_aux0 = \<ordfeminine>turn_aux0 \<and>
        (\<ordmasculine>turn_aux1 \<longrightarrow> \<ordfeminine>turn_aux1) \<and>
        (\<ordmasculine>turn_aux1 \<longrightarrow> \<ordmasculine>turn = \<ordfeminine>turn) \<and>
        (\<ordmasculine>turn_aux1 \<longrightarrow> \<ordfeminine>flag1 \<longrightarrow> \<ordmasculine>flag1) \<rbrace>"
  unfolding thread1_aux_def cs_cond_def 
  apply rg_tac
  apply(erule ConseqRG, clarsimp+)
  done

   


definition
"mutex_auxG cs0 cs1 \<equiv>
   INTERLEAVING-BEGIN
    \<lbrakk> rely: \<lbrace> \<ordmasculine>flag0 = \<ordfeminine>flag0 \<and> \<ordmasculine>turn_aux0 = \<ordfeminine>turn_aux0 \<rbrace>,
      pre:  \<lbrace> \<not>\<acute>turn_aux0 \<rbrace>,
      post: UNIV 
     \<rbrakk>
    thread0_aux cs0 (\<lambda>a. True)  
  \<parallel>
    \<lbrakk> rely: \<lbrace> \<ordmasculine>flag1 = \<ordfeminine>flag1 \<and> \<ordmasculine>turn_aux1 = \<ordfeminine>turn_aux1 \<rbrace>,
     pre:  \<lbrace> \<not>\<acute>turn_aux1 \<rbrace>,
     post: UNIV
     \<rbrakk>
    thread1_aux cs1 (\<lambda>a. True)
   INTERLEAVING-END" 


    
lemma mutex_auxG :
"cs_cond \<rho> cs0 \<Longrightarrow> 
 cs_cond \<rho> cs1 \<Longrightarrow> 
  \<rho> \<Turnstile>i mutex_auxG cs0 cs1  
  RELY Id
  PRE  \<lbrace> \<not>\<acute>turn_aux0 \<and> \<not>\<acute>turn_aux1  \<rbrace>
  POST \<lbrace> True \<rbrace>
  GUAR \<lbrace> (\<ordmasculine>turn_aux0 \<longrightarrow> \<ordmasculine>turn_aux1 \<longrightarrow> \<ordmasculine>turn = \<ordfeminine>turn) \<and>
         (\<ordmasculine>turn_aux0 \<longrightarrow> \<ordfeminine>turn_aux0) \<and>
         (\<ordmasculine>turn_aux0 \<longrightarrow> \<ordfeminine>flag0 \<longrightarrow> \<ordmasculine>flag0) \<and>
         (\<ordmasculine>turn_aux1 \<longrightarrow> \<ordfeminine>turn_aux1) \<and>
         (\<ordmasculine>turn_aux1 \<longrightarrow> \<ordfeminine>flag1 \<longrightarrow> \<ordmasculine>flag1) \<rbrace>"
  unfolding mutex_auxG_def 
  apply rg_tac
   apply(rule ConseqRG, rule thread1_auxG, simp, simp, clarsimp, clarsimp)
   apply clarsimp
   apply(rule conjI, clarsimp)
    apply(case_tac j, simp)
    apply simp
   apply clarsimp
   apply(rule ConseqRG, rule thread0_auxG, simp, simp, clarsimp, clarsimp)
  apply clarsimp
  apply(rule conjI, clarsimp+)
  done

end