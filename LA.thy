(* *********************************************************************

    Theory LA.thy is part of a framework for modelling,
    verification and transformation of concurrent imperative
    programs. Copyright (c) 2021  M. Bortin

    The framework is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
    For more details see the license agreement (LICENSE) you should have
    received along with the framework.
    
   ******************************************************************* *)
   
theory LA
imports Prelims
begin

text "highlighting the type of relations between (abstract) states"
type_synonym 'a staterel = "('a \<times> 'a) set"


text "an auxiliary annotation structure for the parallel components"
record 's annpar =
  ap_rely :: "'s staterel"
  ap_precond :: "'s set"
  ap_postcond :: "'s set"


section "A generic imperative language"


datatype 's LA =
    Skip 
  | Basic "'s \<Rightarrow> 's"
  | Seq "'s LA" "'s LA"  
  | Cond "'s set" "'s LA" "'s LA"
  | While "'s set" "'s set" "'s LA" "'s LA" 
  | Parallel "('s LA \<times> 's annpar) list"
  | Await "'s set" "'s set" "'s LA"
  | CJump "'s set" nat "'s LA"


text "the unconditional jump instruction"
definition "Jump i = CJump UNIV i Skip"


fun jumpfree :: "'s LA \<Rightarrow> bool"
where "jumpfree Skip = True" |
      "jumpfree (Basic f) = True" |
      "jumpfree (Seq p1 p2) = (jumpfree p1 \<and> jumpfree p2)" |
      "jumpfree (Parallel ps) = (\<forall>p\<in>set ps. jumpfree (fst p))" |
      "jumpfree (Cond c p1 p2) = (jumpfree p1 \<and> jumpfree p2)" |
      "jumpfree (Await c a p) = jumpfree p" |
      "jumpfree (While c i p q) = (jumpfree p \<and> jumpfree q)" |
      "jumpfree _ = False"


lemma jumpfree_Jump[simp] :
"jumpfree (Jump i) = False"
  by(simp add: Jump_def)


text "locally sequential programs"
fun locally_seq :: "'s LA \<Rightarrow> bool"
where "locally_seq (Seq p1 p2) = (locally_seq p1 \<and> locally_seq p2)" |
      "locally_seq (Parallel ps) = False" |
      "locally_seq (Cond c p1 p2) = (locally_seq p1 \<and> locally_seq p2)" |
      "locally_seq (Await c a p) = locally_seq p" |
      "locally_seq (While c i p q) = (locally_seq p \<and> locally_seq q)" |
      "locally_seq (CJump C i p) = locally_seq p" |
      "locally_seq _ = True" 


lemma locally_seq_Jump[simp] :
"locally_seq (Jump i) = True"
  by(simp add: Jump_def)



text "the set of local jumps"
fun ljumps :: "'s LA \<Rightarrow> nat set"
where "ljumps Skip = {}" |
      "ljumps (Basic f) = {}" |
      "ljumps (CJump C i p) = {i} \<union> ljumps p" |
      "ljumps (Seq p1 p2) = (ljumps p1 \<union> ljumps p2)" |
      "ljumps (Parallel ps) = (\<Union>((ljumps \<circ> fst) ` set ps))" |
      "ljumps (Cond c p1 p2) = (ljumps p1 \<union> ljumps p2)" |
      "ljumps (Await c a p) = ljumps p" |
      "ljumps (While c i p q) = (ljumps p \<union> ljumps q)"  


lemma ljumps_Jump[simp] :
"ljumps (Jump i) = {i}"
  by(simp add: Jump_def)






section "Concrete syntax for the LA programs"

syntax
  "_quote"     :: "'b \<Rightarrow> ('a \<Rightarrow> 'b)"                ("(\<guillemotleft>_\<guillemotright>)" [0] 1000)
  "_antiquote" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b"                ("\<acute>_" [1000] 1000)
  "_Assert"    :: "'a \<Rightarrow> 'a set"                    ("(\<lbrace>_\<rbrace>)" [0] 1000)

translations
  "\<lbrace>b\<rbrace>" \<rightharpoonup> "CONST Collect \<guillemotleft>b\<guillemotright>"

parse_translation \<open>
  let
    fun quote_tr [t] = Syntax_Trans.quote_tr @{syntax_const "_antiquote"} t
      | quote_tr ts = raise TERM ("quote_tr", ts);
  in [(@{syntax_const "_quote"}, K quote_tr)] end
\<close>

lemma neg_Collect[simp] :
"- Collect P = Collect (\<lambda>x. \<not> P x)"
  by fast


syntax
  "_fst" :: "'a \<times> 'b \<Rightarrow> 'a"  ("_\<^sub>," [60] 61)
  "_snd" :: "'a \<times> 'b \<Rightarrow> 'b"  ("_\<^sub>." [60] 61)


parse_translation \<open>
  let
    fun fst_tr ((Const (@{const_syntax Pair}, _) $ p $ c)
          :: ts) = p;

    fun snd_tr ((Const (@{const_syntax Pair}, _) $ p $ c)
          :: ts) = c;
  in
   [(@{syntax_const "_fst"}, K fst_tr),
    (@{syntax_const "_snd"}, K snd_tr)]
  end
\<close>


syntax
  "_Assign"    :: "idt \<Rightarrow> 'b \<Rightarrow> 's LA"
                   ("(\<acute>_ :=/ _)" [70, 65] 61)

translations
  "\<acute>x := a" \<rightleftharpoons> "(CONST Basic \<guillemotleft>\<acute>(_update_name x (\<lambda>_. a))\<guillemotright>)"

syntax
  "_before" :: "id \<Rightarrow> 'a" ("\<ordmasculine>_")
  "_after"  :: "id \<Rightarrow> 'a" ("\<ordfeminine>_")

translations
  "\<ordmasculine>x" \<rightleftharpoons> "x \<acute> CONST fst"
  "\<ordfeminine>x" \<rightleftharpoons> "x \<acute> CONST snd"


syntax
  "_Seq"  :: "'s LA \<Rightarrow> 's LA \<Rightarrow> 's LA"
            ("(_;//_)" [56, 55] 55)
            

  "_Cond"        :: "'s set  \<Rightarrow> 's LA  \<Rightarrow> 's LA \<Rightarrow> 's LA"
                    ("(IF _//(2THEN/ (_))//(2ELSE/ (_))//FI)" [0, 0, 0] 61)
  "_Cond2"       :: "'s set  \<Rightarrow> 's LA  \<Rightarrow> 's LA"
                    ("(IF _//(2THEN/ (_))//FI)" [0,0] 56)


  "_While_inv"   :: "'s set  \<Rightarrow> 's set \<Rightarrow> 's LA  \<Rightarrow> 's LA  \<Rightarrow> 's LA"
  ("(WHILE _/ \<lbrakk> inv: _/\<rbrakk>//(2DO/ (_))//SUBSEQUENTLY _//OD)"  [0, 0, 0, 0] 61)

  "_While"       :: "'s set  \<Rightarrow> 's LA  \<Rightarrow> 's LA \<Rightarrow> 's LA"
                    ("(WHILE _//(2DO/ (_))//SUBSEQUENTLY _//OD)"  [0, 0, 0] 61)

  "_WhileS"      :: "'s set  \<Rightarrow> 's set \<Rightarrow> 's LA  \<Rightarrow> 's LA"
                    ("(WHILE _/ \<lbrakk> inv: _/\<rbrakk>//(2DO/ (_))//OD)"  [0, 0, 0] 61)
  "_WhileS5"     :: "'s set  \<Rightarrow> 's LA  \<Rightarrow> 's LA"
                    ("(WHILE _//(2DO/ (_))//OD)"  [0, 0] 61)

  "_AwaitA"       :: "'s set  \<Rightarrow> 's set \<Rightarrow> 's LA  \<Rightarrow> 's LA"
                    ("(AWAIT _/ \<lbrakk> ann: _/\<rbrakk>//(2THEN/ (_))/ END)"  [0,0,0] 61)
  "_AtomA"        :: "'s set  \<Rightarrow> 's LA  \<Rightarrow> 's LA"
                    ("(\<lbrakk> ann: _/\<rbrakk>\<langle>_\<rangle>)" [0,0] 61)
  "_WaitA"        :: "'s set  \<Rightarrow> 's set  \<Rightarrow> 's LA"
                    ("(WAIT _/ \<lbrakk> ann: _/\<rbrakk> END)" [0,0] 61)

  "_Await"       :: "'s set  \<Rightarrow> 's LA  \<Rightarrow> 's LA"
                    ("(AWAIT _/ (2THEN/ (_))/ END)"  [0,0] 61)
  "_Atom"        :: "'s set  \<Rightarrow> 's LA  \<Rightarrow> 's LA"
                    ("(\<langle>_\<rangle>)" [0] 61)
  "_Wait"        :: "'s set  \<Rightarrow> 's LA"
                    ("(WAIT _/ END)" [0] 61)  


  "_Jump"        :: "nat \<Rightarrow> 's LA" ("JUMP _/" [0] 61)

  "_CJump"       :: "'s set \<Rightarrow> nat \<Rightarrow> 's LA \<Rightarrow> 's LA" 
                    ("CJUMP _/ TO/ _//(2OTHERWISE/ (_))//END " [0,0,0] 61)

  "_Skip"        :: "'s LA" ("SKIP" 61)


translations
  "p1;p2" \<rightleftharpoons> "CONST Seq p1 p2" 

  "IF b THEN c1 ELSE c2 FI" \<rightleftharpoons> "CONST Cond b c1 c2"
  "IF b THEN c FI" \<rightleftharpoons> "IF b THEN c ELSE SKIP FI"


  "WHILE b \<lbrakk>inv: i\<rbrakk> DO p SUBSEQUENTLY q OD" \<rightleftharpoons> "CONST While b i p q"
  "WHILE b DO p SUBSEQUENTLY q OD" \<rightleftharpoons> "WHILE b \<lbrakk>inv: CONST UNIV\<rbrakk> DO p SUBSEQUENTLY q OD"

  "WHILE b \<lbrakk>inv: i\<rbrakk> DO p OD" \<rightleftharpoons> "WHILE b \<lbrakk>inv: i\<rbrakk> DO p SUBSEQUENTLY SKIP OD"
  "WHILE b DO p OD" \<rightleftharpoons> "WHILE b DO p SUBSEQUENTLY SKIP OD"

  "AWAIT b \<lbrakk>ann: a\<rbrakk> THEN c END" \<rightleftharpoons> "CONST Await b a c"
  "\<lbrakk>ann: a\<rbrakk>\<langle>c\<rangle>" \<rightleftharpoons> "AWAIT CONST UNIV \<lbrakk>ann: a\<rbrakk> THEN c END"
  "WAIT b \<lbrakk>ann: a\<rbrakk> END" \<rightleftharpoons> "AWAIT b \<lbrakk>ann: a\<rbrakk> THEN SKIP END"


  "AWAIT b THEN c END" \<rightleftharpoons> "CONST Await b (CONST UNIV) c"
  "\<langle>c\<rangle>" \<rightleftharpoons> "AWAIT CONST UNIV THEN c END"
  "WAIT b END" \<rightleftharpoons> "AWAIT b THEN SKIP END"
  "JUMP j"  \<rightleftharpoons> "CONST Jump j"
  "CJUMP b TO j OTHERWISE p END" \<rightleftharpoons> "CONST CJump b j p"
  "SKIP" \<rightleftharpoons> "CONST Skip"    


nonterminal prgs
syntax
  "_PAR" :: "prgs \<Rightarrow> 'a"
            ("(INTERLEAVING-BEGIN//_//INTERLEAVING-END)" [57] 56)
  "_AnnPrg" :: "['a, 'a, 'a, 'a] \<Rightarrow> prgs"
               ("(2 \<lbrakk> rely: _,/ pre: _,/ post: _ \<rbrakk>//_)" [90, 90, 90, 60] 57)
  "_AnnPrgs" :: "['a, 'a, 'a, 'a, prgs] \<Rightarrow> prgs"
                ("(2 \<lbrakk> rely: _,/ pre: _,/ post: _ \<rbrakk>//_)//\<parallel>//_" [90, 90, 90, 60, 57] 57)
  "_AnnPrgScheme" :: "['a, 'a, 'a, 'a, 'a, 'a, 'a] \<Rightarrow> prgs"
  ("  (2SCHEME-BEGIN [_ \<le> _ < _]//\<lbrakk> rely: _,/ pre: _,/ post: _ \<rbrakk>//_//SCHEME-END)" [0,0,0,90,90,90,0] 57)

  "_Prg" :: "['a] \<Rightarrow> prgs"
            ("(2  _)" [60] 57)
  "_Prgs" :: "['a, prgs] \<Rightarrow> prgs"
             ("(2  _)//\<parallel>//_" [60,57] 57)
  "_PrgScheme" :: "['a, 'a, 'a, 'a] \<Rightarrow> prgs"  
                  ("  (2SCHEME-BEGIN [_ \<le> _ < _]//_//SCHEME-END)" [0,0,0,60] 57)

translations
  "_PAR ps" \<rightharpoonup> "CONST Parallel ps"
  "_AnnPrg r p q c" \<rightharpoonup> "([(c, \<lparr>ap_rely=r, ap_precond=p, ap_postcond=q\<rparr>)])"
  "_AnnPrgs r p q c ps" \<rightharpoonup> "((c, \<lparr>ap_rely=r, ap_precond=p, ap_postcond=q\<rparr>) # ps)"
  "_AnnPrgScheme j i k r p q c" \<rightharpoonup>
    "(CONST map (\<lambda>i. (c, \<lparr>ap_rely=r, ap_precond=p, ap_postcond=q\<rparr>)) [j..<k])"

  "_Prg c" \<rightharpoonup>
    "([(c, \<lparr>ap_rely=CONST UNIV, ap_precond=CONST UNIV, ap_postcond=CONST UNIV\<rparr>)])"
  "_Prgs c ps" \<rightharpoonup>
    "((c, \<lparr>ap_rely=CONST UNIV, ap_precond=CONST UNIV, ap_postcond=CONST UNIV\<rparr>) # ps)"
  "_PrgScheme j i k c" \<rightharpoonup>
    "(CONST map (\<lambda>i. (c, \<lparr>ap_rely=CONST UNIV, ap_precond=CONST UNIV, ap_postcond=CONST UNIV\<rparr> )) [j..<k])"





ML \<open> 

fun dest_absL (x, T, body) =
  let
    fun name_clash (Free (y, _)) = (x = y)
      | name_clash (t $ u) = name_clash t orelse name_clash u
      | name_clash (Abs (_, _, t)) = name_clash t
      | name_clash _ = false;
  in
    if name_clash body then
      dest_absL (singleton (Name.variant_list [x]) x, T, body)    (*potentially slow*)
    else (x, subst_bound (Free (x, T), body))
  end;

  fun quote_tr' f (t :: ts) =
        Term.list_comb (f $ Syntax_Trans.quote_tr' @{syntax_const "_antiquote"} t, ts)
    | quote_tr' _ _ = raise Match;

  fun annquote_tr' f (r :: t :: ts) =
        Term.list_comb (f $ r $ Syntax_Trans.quote_tr' @{syntax_const "_antiquote"} t, ts)
    | annquote_tr' _ _ = raise Match;

  val assert_tr' = quote_tr' (Syntax.const @{syntax_const "_Assert"});

  fun annbexp_tr' name (r :: (Const (@{const_syntax Collect}, _) $ t) :: ts) =
        annquote_tr' (Syntax.const name) (r :: t :: ts)
    | annbexp_tr' name (r :: Const (@{const_syntax UNIV}, _) :: ts) =
        annquote_tr' (Syntax.const name)
                     (r :: Abs ("s", dummyT, Const (@{const_syntax True}, dummyT)) :: ts)
    | annbexp_tr' name (r :: Const (@{const_syntax Set.empty}, _) :: ts) =
        annquote_tr' (Syntax.const name)
                     (r :: Abs ("s", dummyT, Const (@{const_syntax False}, dummyT)) :: ts)
    | annbexp_tr' _ _ = raise Match;

  fun annassign_tr' (r :: Abs (x, _, f $ k $ Bound 0) :: ts) =
        quote_tr' (Syntax.const @{syntax_const "_Assign"} $ r $ Syntax_Trans.update_name_tr' f)
          (Abs (x, dummyT, Syntax_Trans.const_abs_tr' k) :: ts)
    | annassign_tr' _ = raise Match;

  fun dest_list (Const (@{const_syntax Nil}, _)) = []
    | dest_list (Const (@{const_syntax Cons}, _) $ x $ xs) = x :: dest_list xs
    | dest_list xs = [xs];

  fun new_Pair a b =
    (Const (@{const_syntax Pair}, dummyT) $ a $ b)

  fun dest_prod (Const (@{const_syntax Pair}, _) $ a $ b) = (a, b)
    | dest_prod _ = raise Match;

  fun dest_upt (Const (@{const_syntax upt},_) $ m $ n) = (m, n)
    | dest_upt _ = raise Match;

  fun dest_apar (Const (@{const_syntax annpar_ext}, _) $ r $ p $ q $ _) = (r, p, q)
    | dest_apar _ = raise Match;

  fun prg_tr' const aconst xs pqa =
        let val (c, apr) = dest_prod pqa
            val (R, P, Q) = dest_apar apr
            fun fake (Const (@{const_syntax UNIV},_)) = true
              | fake _ = false
            val const' = if fake R then const else aconst
            val ys = if fake R then [] else [R, P, Q]
        in list_comb (Syntax.const const', xs @ ys @ [c])
        end

  fun prgs_lst_tr'
            [Const (@{const_syntax map}, _) $ Abs (i, T, p) $ upt] =
        let val (j, k) = dest_upt upt
        in prg_tr' @{syntax_const "_PrgScheme"} @{syntax_const "_AnnPrgScheme"}
                 [j, Free (i, T), k] (snd(dest_absL (i, T, p)))
        end
    | prgs_lst_tr' [p] =
        prg_tr' @{syntax_const "_Prg"} @{syntax_const "_AnnPrg"} [] p
    | prgs_lst_tr' (p :: ps)  =
        prg_tr' @{syntax_const "_Prgs"} @{syntax_const "_AnnPrgs"} [] p $
          prgs_lst_tr' ps 
    | prgs_lst_tr' _ = raise Match

  fun Parallel_tr (cs :: _) =
        let val cs' = dest_list cs
        in Syntax.const @{syntax_const "_PAR"} $
             prgs_lst_tr' cs' end
    | Parallel_tr _ = raise Match;

  fun Basic_tr (Abs (x, _, f $ k $ Bound 0) :: ts) =
      quote_tr' (Syntax.const @{syntax_const "_Assign"} $ Syntax_Trans.update_name_tr' f)
          (Abs (x, dummyT, Syntax_Trans.const_abs_tr' k) :: ts) 
    | Basic_tr ((f $ k) :: ts) = quote_tr' (Syntax.const @{syntax_const "_Assign"} $ Syntax_Trans.update_name_tr' f)
          (k :: ts) 
    | Basic_tr _ = raise Match;

\<close>

print_translation \<open>
  [(@{const_syntax Collect}, K assert_tr'),
   (@{const_syntax Basic}, K Basic_tr),
   (@{const_syntax Parallel}, K Parallel_tr)]
\<close>



end