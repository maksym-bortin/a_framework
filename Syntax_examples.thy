(* *********************************************************************

    Theory Syntax_examples.thy is part of a framework for modelling,
    verification and transformation of concurrent imperative
    programs. Copyright (c) 2021  M. Bortin

    The framework is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
    For more details see the license agreement (LICENSE) you should have
    received along with the framework.
    
   ******************************************************************* *)

theory Syntax_examples
imports LA
begin


term "\<acute>a := v;
      \<acute>b := \<acute>a + 1"

text "the annotated invariant condition is needed to control the VCG:"
term "WHILE \<lbrace>\<acute>x > 0 \<rbrace> 
      \<lbrakk> inv: \<lbrace> \<acute>x \<ge> 0 \<rbrace>\<rbrakk> 
      DO \<acute>z := 1;
         \<acute>x := \<acute>x - 1 OD"

text "but it can in principle be omitted too:"
term "SKIP ; WHILE \<lbrace>\<acute>x > 0 \<rbrace> DO \<acute>z := 1;
                                \<acute>x := \<acute>x - 1 SUBSEQUENTLY \<acute>x := \<acute>z + 1;
                                                          \<acute>x := \<acute>x + 1 OD"

term "\<acute>x := v; IF \<lbrace>\<acute>x > 0 \<rbrace> THEN \<acute>x := 1 ELSE \<acute>x := 0 FI"

term  "AWAIT \<lbrace>\<acute>x > 0 \<rbrace> THEN \<acute>x := \<acute>x - 1  END"

text "annotating preconditions for await-statements (an atomic section here);
      this is an additional way to control the VCG:"  
term "\<lbrakk> ann: \<lbrace> \<acute>a = True \<rbrace> \<rbrakk>\<langle>\<acute>x := 1;\<acute>x := \<acute>x - 1\<rangle>"

term  "WAIT \<lbrace>\<acute>x > 0 \<rbrace> \<lbrakk> ann: \<lbrace> \<acute>a = True \<rbrace> \<rbrakk> END"

text "actually the same as above but without annotations:"
term  "AWAIT \<lbrace>\<acute>x > 0 \<rbrace> THEN SKIP END"


text "conditional jumps:"
term "CJUMP \<lbrace>\<acute>x > 0 \<rbrace> TO n OTHERWISE \<acute>x := \<acute>x + 1;
                                     \<acute>a := \<acute>b END"
text "and unconditional jumps:"
term "JUMP n"

text "annotated interleaving construction for two threads:"
term "INTERLEAVING-BEGIN \<lbrakk>rely: a, pre: b, post: s\<rbrakk> \<acute>x := b \<parallel>  
                         \<lbrakk>rely: u, pre: v, post: t\<rbrakk> \<acute>x := c 
      INTERLEAVING-END"

text "interleaving construction for three threads (annotations omitted):"
term "INTERLEAVING-BEGIN 
       (\<acute>a := True; \<acute>x := a) \<parallel> \<acute>x := b \<parallel> \<acute>x := c
      INTERLEAVING-END"

text "an assignment followed by a 'fork':" 
term "\<acute>a := True; 
      INTERLEAVING-BEGIN 
       \<acute>x := a \<parallel> \<acute>x := b \<parallel> \<acute>x := c
      INTERLEAVING-END"

text "a scheme is by contrast parameterised by the number of threads:"
term "INTERLEAVING-BEGIN 
       SCHEME-BEGIN [m\<le>i<m'] 
        \<lbrakk>rely: r i, pre: p i, post: q i\<rbrakk> 
         SKIP ; (c i)
       SCHEME-END
      INTERLEAVING-END"


term "INTERLEAVING-BEGIN 
       SCHEME-BEGIN [m\<le>i<m'] c i SCHEME-END
      INTERLEAVING-END"


end