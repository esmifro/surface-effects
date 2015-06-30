Require Import Coq.Arith.Minus.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Definitions.
Require Import Environment.
Require Import Keys.
Require Import Ascii.
Require Import Coq.ZArith.Znat.
Require Import Coq.Arith.Peano_dec.
         
Import EvalBigStep.
Import Expressions.
Import Effects.  
 
Open Scope list_scope.

Fixpoint factorial (n : nat) : nat :=
match n with
  | O => S O
  | S n' => mult n (factorial n')
end.

Fixpoint fact (x : nat) : Exp :=
  match x with
    | 0 => pure (S 0)
    | S n => (pure x) Times (fact n)
  end.                    

   
Definition Fact : Exp
  := If (var "x") Equals (pure 0) Then pure 1
     Else ((var "x") Times (capp  (var "f")((var "x") Minus (pure 1)))).


Definition MuFact : Exp
  := mu "f" • lambda "x" • Fact.

Definition LetFactEff : Exp
  := Let (var "y") As (eapp (MuFact {{ Top }}) (pure 5 {{ Top }})) In (var "y").


Lemma e_rec_aux :
  forall (facts aacts bacts : Phi) 
         (f x : ascii)
         (ef ea e': Exp)
         (v v' : Val) 
         (env env': Env)
         (heap fheap aheap bheap : Heap)
         (acts : Phi),
    (heap, env, proj_c ef) ⇓ (fheap, Cls (env', Mu f x e'), facts) ->
    (fheap, env, proj_c ea) ⇓ (aheap, v, aacts) ->
    (aheap, update_rec_E (f, Cls (env', Mu f x e')) (x, v) env', e') ⇓ (bheap, v', bacts) ->
    acts = facts ++ aacts ++ bacts ->
    (heap, env, capp (ef) (ea)) ⇓ (bheap, v', acts).
Proof.
  intros. subst. eapply E_Capp; eauto.
Qed.

Lemma e_rec_eff_aux :
  forall (facts aacts bacts : Phi)
         (ef ea : Exp)
         (vef vea : EffSpec) 
         (env: Env)
         (heap fheap aheap bheap : Heap)
         (acts : Phi)
         (spec : Val),
    (heap, env, proj_e ef) ⇓ (fheap, Eff vef, facts) ->
    (fheap, env, proj_e ea) ⇓ (aheap, Eff vea, aacts) ->
    acts = facts ++ aacts ++ bacts ->
    spec =  Eff (vef ⊕ vea) ->
    (heap, env, eapp (ef) (ea)) ⇓ (bheap, spec, acts).
Proof.
  intros. subst. eapply E_Eapp; eauto.
Qed.

Lemma e_false_aux :
  forall (cacts facts : Phi)
         (e e1 e2 : Exp)
         (v : Val)
         (env : Env)
         (heap cheap fheap : Heap)
         (b : bool) (acts : Phi),
    (heap, env, e) ⇓ (cheap, (Bit b), cacts) -> 
    (cheap, env, e2) ⇓ (fheap, v, facts) -> 
    b = false ->
    acts = cacts ++ facts ->
    (heap, env, If e Then e1 Else e2 {{ Top }} ) ⇓ (fheap, v, acts).
Proof.
  intros. subst.  eapply E_False; eauto.
Qed.

Lemma e_true_aux :
  forall (cacts facts : Phi)
         (e e1 e2 : Exp)
         (v : Val)
         (env : Env)
         (heap cheap theap : Heap)
         (b : bool) (acts : Phi),
    (heap, env, e) ⇓ (cheap, (Bit b), cacts) -> 
    (cheap, env, e1) ⇓ (theap, v, facts) -> 
    b = true ->
    acts = cacts ++ facts ->
    (heap, env, If e Then e1 Else e2 {{Top }} ) ⇓ (theap, v, acts).
Proof.
  intros. subst. eapply E_True; eauto.
Qed.


Hint Constructors Dynamic.
Hint Resolve R_same_key R_diff_key_2 EProofs.add_bst.

Lemma example :
  forall env heap,
    E.Raw.bst env ->
    Dynamic (heap, env, capp (mu "f" • lambda "x" • Fact {{ Top }} ) (pure 5 {{ Top }} ))
                 (heap, Num 120, nil).
Proof.
  intros env heap bst. 
  assert (x_neq_f: "x"%char <> "f"%char) by (unfold not; intro H; inversion H).
  assert (f_neq_x: "f"%char <> "x"%char) by (unfold not; intro H; inversion H).
  replace (Num 120) with (Num (5 * (4 * (3 * (2 * (1 * 1)))))) by (simpl; reflexivity).
  unfold Fact.
  
  eapply e_rec_aux; 
    repeat (eapply E_Abs || eapply E_Cnt || eapply E_Minus || (eapply E_Var; unfold find_E; eauto) || reflexivity ).
  unfold update_rec_E, find_E, fst, snd.
  eapply e_false_aux with (b := beq_nat 5 0); auto.  
  eapply E_Beq; repeat (eapply E_Abs || eapply E_Cnt || eapply E_Minus || (eapply E_Var; unfold find_E; eauto) ).
  eapply E_Times; repeat (eapply E_Abs || eapply E_Cnt || eapply E_Minus || (eapply E_Var; unfold find_E; eauto) ).

  eapply e_rec_aux;
    repeat (eapply E_Abs || eapply E_Cnt || eapply E_Minus || (eapply E_Var; unfold find_E; eauto) || reflexivity). 
  unfold update_rec_E, fst, snd.
  eapply e_false_aux with (b := beq_nat 4 0); auto.
  eapply E_Beq; repeat (eapply E_Abs || eapply E_Cnt || (eapply E_Var; unfold find_E; eauto)). 
  eapply E_Times; repeat (eapply E_Abs || eapply E_Cnt || (eapply E_Var; unfold find_E; eauto)).

  eapply e_rec_aux;
    repeat (eapply E_Abs || eapply E_Cnt || eapply E_Minus ||  (eapply E_Var; unfold find_E; eauto) || reflexivity).
  unfold update_rec_E, fst, snd.
  eapply e_false_aux with (b := beq_nat 3 0); auto.
  eapply E_Beq; (eapply E_Abs || eapply E_Cnt || (eapply E_Var; unfold find_E; eauto)).
  eapply E_Times; repeat (eapply E_Abs || eapply E_Cnt ||  (eapply E_Var; unfold find_E; eauto)).

  eapply e_rec_aux;
    repeat (eapply E_Abs || eapply E_Cnt || eapply E_Minus || (eapply E_Var; unfold find_E; eauto) || reflexivity).
  unfold update_rec_E, fst, snd.
  eapply e_false_aux with (b := beq_nat 2 0);auto.
  eapply E_Beq; (eapply E_Abs || eapply E_Cnt || (eapply E_Var; unfold find_E; eauto)).
  eapply E_Times; repeat (eapply E_Abs || eapply E_Cnt ||  (eapply E_Var; unfold find_E; eauto)).

  eapply e_rec_aux;
    repeat (eapply E_Abs || eapply E_Cnt || eapply E_Minus || (eapply E_Var; unfold find_E; eauto) || reflexivity).
  unfold update_rec_E, fst, snd.
  eapply e_false_aux with (b := beq_nat 1 0);auto.
  eapply E_Beq; (eapply E_Abs || eapply E_Cnt || (eapply E_Var; unfold find_E; eauto)).
  eapply E_Times; repeat (eapply E_Abs || eapply E_Cnt ||  (eapply E_Var; unfold find_E; eauto)).

  eapply e_rec_aux;
   repeat (eapply E_Abs || eapply E_Cnt || eapply E_Minus || (eapply E_Var; unfold find_E; eauto) || reflexivity).
  unfold update_rec_E, fst, snd.
  eapply e_true_aux with (b := beq_nat 0 0);auto.
  eapply E_Beq; (eapply E_Abs || eapply E_Cnt || (eapply E_Var; unfold find_E; eauto)). 

  simpl; reflexivity. 
Qed.

Lemma example2 :
  forall env heap,
    E.Raw.bst env ->
    Dynamic (heap, env, LetFactEff)
            (heap, Eff Top, nil).
Proof.
  intros env heap bst.
  apply E_Let. unfold MuFact.

  eapply e_rec_eff_aux; simpl.
  - eapply E_Eff.
  - eapply E_Eff.
  - now simpl.
  - admit.
Qed.    
