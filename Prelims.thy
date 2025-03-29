(* *********************************************************************

    Theory Prelims.thy is part of a framework for modelling,
    verification and transformation of concurrent imperative
    programs. Copyright (c) 2021  M. Bortin

    The framework is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
    For more details see the license agreement (LICENSE) you should have
    received along with the framework.
    
   ******************************************************************* *)

theory Prelims
imports Main
begin

lemma choice' :
"\<exists>f. \<forall>x. P x (f x) \<Longrightarrow> \<forall>x. \<exists>y. P x y"
by force

lemma choice'' :
"\<forall>i. P i \<longrightarrow> (\<exists>j. Q i j) \<Longrightarrow> \<exists>\<phi>. \<forall>i. P i \<longrightarrow> Q i (\<phi> i)"
  by(rule choice, fast)



lemma least_ix :
"P (j :: nat) \<Longrightarrow>
 \<exists>i\<le>j. P i \<and> (\<forall>k<i. \<not> P k)" 
  apply(rule_tac x="LEAST j. P j" in exI)
  apply(rule conjI)
   apply(erule Least_le)
  apply(rule conjI)
   apply(erule LeastI)
  apply clarify
  apply(drule not_less_Least)
  by clarify


lemma Int_Image :
"(R \<inter> S) `` A \<subseteq> (R `` A) \<inter> (S `` A)"
  apply clarify
  apply simp
  apply(rule conjI)
   apply(erule ImageI, assumption)+
  done

lemma Int_Image_singleton_sub :
"(R `` {a}) \<inter> (S `` {a}) \<subseteq> (R \<inter> S) `` {a}"
  by blast

lemma Int_Image_singleton :
"(R \<inter> S) `` {a} = (R `` {a}) \<inter> (S `` {a})"
  apply(rule equalityI)
   apply(rule Int_Image)
  by(rule Int_Image_singleton_sub)


lemma pred_less :
"(0::nat) < x \<Longrightarrow> x - 1 < x"
  by simp


   
lemma inj_on_imp_surj :
"inj_on \<sigma> A \<Longrightarrow>
 finite A \<Longrightarrow>
 \<forall>a\<in>A. \<sigma> a \<in> A \<Longrightarrow>
 \<forall>b\<in>A. \<exists>a\<in>A. \<sigma> a = b"
  apply clarsimp
  apply(rule ccontr, simp)
  apply(subgoal_tac "\<sigma> ` A \<subset> A")
   apply(frule psubset_card_mono, assumption)
   apply(drule card_image)
   apply simp
  apply(rule psubsetI)
   apply fastforce
  apply(rule notI)
  apply(drule equalityD2)
  apply(drule subsetD, assumption)
  apply fastforce
  done
    
    

corollary inj_on_surj_set_intv :
"inj_on \<sigma> {0..<(n :: nat)} \<Longrightarrow>
 \<forall>i<n. \<sigma> i < n \<Longrightarrow>
 \<forall>j<n. \<exists>i<n. \<sigma> i = j"
  apply(drule inj_on_imp_surj, simp, simp)
  by fastforce


lemma mem_nth :
"x \<in> set xs \<Longrightarrow> \<exists>i<length xs. x = xs!i"
  apply(induct xs, simp_all)
  apply(erule disjE, clarsimp)
   apply(rule_tac x=0 in exI, simp)
  apply clarsimp
  apply(rule_tac x="Suc i" in exI, simp)
  done


lemma zip_nthD :
"(a, b) \<in> set(zip xs zs) \<Longrightarrow> 
 \<exists>i<length xs. a = xs!i \<and> b = zs!i"
  apply(induct zs arbitrary: a b xs)
   apply simp
  apply(case_tac xs, simp)
  apply clarsimp
  apply(erule disjE, clarsimp)
  apply(rule_tac x=0 in exI, simp)
  by fastforce


lemma map_zip_aux :
"\<forall>sq \<in> set sqs. length sq = n \<Longrightarrow> length ps = length sqs \<Longrightarrow>
 map (\<lambda>x. (case x of (x, sq) \<Rightarrow> sq @ [x]) ! n) (zip ps sqs) = ps"
  apply(induct ps arbitrary: sqs)
   apply simp
  apply clarsimp
  apply(case_tac sqs, simp)
  apply clarsimp
 done

lemma map_zip_aux2 :
"\<forall>sq \<in> set sqs. length sq = n \<Longrightarrow> m < n \<Longrightarrow> length ps = length sqs \<Longrightarrow>
 map ((\<lambda>x. x ! m) \<circ> (\<lambda>(x, sq). sq @ [x])) (zip ps sqs) = map (\<lambda>x. x ! m) sqs"
  apply(induct ps arbitrary: sqs)
   apply simp
  apply clarsimp
  apply(case_tac sqs, simp)
  apply clarsimp
  apply(subst nth_append, simp)
 done


lemma rtranclp_sub :
"r\<^sup>*\<^sup>* u v \<Longrightarrow> \<forall>u v. r u v \<longrightarrow> s u v \<Longrightarrow> s\<^sup>*\<^sup>* u v"
  by(erule rtranclp.induct, fastforce+)

lemma rtranclp_sub2 :
"r\<^sup>*\<^sup>* u v \<Longrightarrow> \<forall>u v. r u v \<longrightarrow> s\<^sup>*\<^sup>* u v \<Longrightarrow> s\<^sup>*\<^sup>* u v"
  by(erule rtranclp.induct, fastforce+)



end