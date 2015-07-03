Require Import Coq.Program.Equality.
Require Import Coq.Sets.Ensembles.
Require Import Coq.FSets.FMapAVL. 
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Arith.Peano_dec.
Require Import Ascii String.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Mult.
Require Import Coq.Arith.Plus.
Require Import Coq.Arith.Minus.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Compare_dec.
Require Import Keys.
Require Import Heap.
Require Import Effects.
Require Import Environment.
Require Import TypeSystem.
Require Import Definitions2.

Import TypeSoundness.



Theorem DynamicDeterminism :
  forall heap rgns env exp heap1 heap2 val1 val2 acts1 acts2,
    (heap, rgns, env, exp) ⇓ (heap1, val1, acts1) ->
    (heap, rgns, env, exp) ⇓ (heap2, val2, acts2) ->
    (heap1, val1, acts1) = (heap2, val2, acts2).
Proof.
  intros heap rgns env exp heap1 heap2 val1 val2 acts1 acts2 Dyn1.
  generalize dependent acts2; generalize dependent val2; generalize dependent heap2.
  dependent induction Dyn1; intros heap2 val2 acts2 Dyn2; inversion Dyn2; subst;
  try reflexivity.   
  - rewrite H in H1. inversion H1. reflexivity.
  -  assert ( RH1 : (fheap, Cls (env', rho', Mu f x ec' ee'), facts) = (fheap0, Cls (env'0, rho'0, Mu f0 x0 ec'0 ee'0), facts0) )
      by (eapply IHDyn1_1; [ reflexivity | assumption]); inversion RH1; subst.
    assert ( RH2 : (aheap, v, aacts) = (aheap0, v0, aacts0) ) by (apply IHDyn1_2; assumption); inversion RH2; subst.
    assert ( RH3 :  (heap1, val1, bacts) = (heap2, val2, bacts0) ) by (eapply IHDyn1_3; [ reflexivity | reflexivity |  assumption]). 
    now inversion_clear RH3.
  -  assert ( RH1 : (fheap, Cls (env', rho', Lambda x eb), facts) = (fheap0, Cls (env'0, rho'0, Lambda x0 eb0), facts0) )
      by (eapply IHDyn1_1; [ reflexivity | assumption]); inversion RH1; subst. 
     rewrite H in H9. inversion H9; subst.
     assert ( RH2 : (heap1, val1, bacts) = (heap2, val2, bacts0)) by (eapply IHDyn1_2; eauto); inversion RH2; subst; auto.
  - assert (HR1 : (heap2, Cls (env'0, rho'0, Mu f0 x0 ec'0 ee'0), facts0) = (heap2, Cls (env', rho', Mu f x ec' ee'), facts)) 
      by (eapply IHDyn1_1; eauto); inversion HR1; subst.
    assert ( HR2 : (heap2, v', aacts) =  (heap2, v'0, aacts0)) by (eapply IHDyn1_2; eauto); inversion HR2; subst.
    assert ( HR3 : (heap2, val1, bacts) = (heap2, val2, bacts0)) by (eapply IHDyn1_3; eauto); inversion HR3; subst.
    reflexivity.
  - assert (HR1 : (heap, Eff theta1, acts_eff1) =  (heap, Eff theta0, acts_eff0)) by (eapply IHDyn1_1; eauto); inversion HR1; subst.
    assert (HR2 : (heap, Eff theta2, acts_eff2) = (heap, Eff theta3, acts_eff3)) by (eapply IHDyn1_2; eauto); inversion HR2; subst.
    assert (HR3 : (heap_mu1, Num v1, acts_mu1) = (heap_mu0, Num v0, acts_mu0))  by (eapply IHDyn1_3; eauto); inversion HR3; subst.
    assert (HR4 :  (heap_mu2, Num v2, acts_mu2) = (heap_mu3, Num v3, acts_mu3)) by (eapply IHDyn1_4; eauto); inversion HR4; subst.
    assert (HR5 : heap2 = heap1).
    inversion H0; inversion H16; subst.
    + reflexivity.
    + admit.
    + admit. 
    + reflexivity.
    + rewrite HR5. reflexivity.
  - assert ( RH1 : (cheap, Bit true, cacts) = (cheap0, Bit true, cacts0))
      by (eapply IHDyn1_1; [ reflexivity | assumption] ); inversion RH1; subst.
    assert ( RH2 : (heap1, val1, tacts) = (heap2, val2, tacts0)) by (apply IHDyn1_2; assumption).
    now inversion_clear RH2.
  -  assert ( RH1 : (cheap, Bit true, cacts) = (cheap0, Bit false, cacts0) ). apply IHDyn1_1; auto.
     discriminate RH1.
  - assert ( RH1 : (cheap, Bit false, cacts) = (cheap0, Bit true, cacts0) ). apply IHDyn1_1; auto.
    discriminate RH1.
  - assert ( RH1 : (cheap, Bit false, cacts) = (cheap0, Bit false, cacts0))
      by (eapply IHDyn1_1; [ reflexivity | assumption] ); inversion RH1; subst.
    assert ( RH2 : (heap1, val1, facts) = (heap2, val2, facts0)) by (apply IHDyn1_2; assumption).
    now inversion_clear RH2.
  - assert (HR1 : (heap', v, vacts) = (heap'0, v0, vacts0)) by (eapply IHDyn1; eauto); inversion HR1; subst.
    rewrite H in H10. inversion H10; subst.
    rewrite <- H11 in H0. unfold find_H in H0. assert (Hl : l = l0) by admit. rewrite Hl.
    reflexivity.
  - assert ( RH1 : (heap1, Loc w l, aacts) = (heap2, Loc w l0, aacts0))
      by (apply IHDyn1; [reflexivity | assumption]); inversion RH1; subst.
    rewrite H in H10. inversion H10; subst.
    rewrite H11 in H0. now inversion_clear H0.
  - assert ( RH1 : (heap', Loc w l, aacts) = (heap'0, Loc w l0, aacts0))
      by (apply IHDyn1_1 ; [reflexivity | assumption]); inversion RH1; subst.
    assert ( RH2 : (heap'', v, vacts) = (heap''0, v0, vacts0))
      by (apply IHDyn1_2; assumption).
    rewrite H11 in H. inversion H; subst.
    now inversion_clear RH2.
  - assert ( RH1 : (lheap, Num va, lacts) = (lheap0, Num va0, lacts0) )
      by (apply IHDyn1_1 ;  [reflexivity | assumption]); inversion RH1; subst.
    assert ( RH2 :  (heap1, Num vb, racts) = (heap2, Num vb0, racts0))
      by (apply IHDyn1_2;  [reflexivity | assumption]); now inversion_clear RH2.
  - assert ( RH1 : (lheap, Num va, lacts) = (lheap0, Num va0, lacts0) )
      by (apply IHDyn1_1 ;  [reflexivity | assumption]); inversion RH1; subst.
    assert ( RH2 :  (heap1, Num vb, racts) = (heap2, Num vb0, racts0))
      by (apply IHDyn1_2;  [reflexivity | assumption]); now inversion_clear RH2.
  - assert ( RH1 : (lheap, Num va, lacts) = (lheap0, Num va0, lacts0) )
      by (apply IHDyn1_1 ;  [reflexivity | assumption]); inversion RH1; subst.
    assert ( RH2 :  (heap1, Num vb, racts) = (heap2, Num vb0, racts0))
      by (apply IHDyn1_2;  [reflexivity | assumption]); now inversion_clear RH2.
  -  assert ( RH1 : (lheap, Num va, lacts) = (lheap0, Num va0, lacts0) )
      by (apply IHDyn1_1 ;  [reflexivity | assumption]); inversion RH1; subst.
    assert ( RH2 :  (heap1, Num vb, racts) = (heap2, Num vb0, racts0))
       by (apply IHDyn1_2;  [reflexivity | assumption]); now inversion_clear RH2.
  - rewrite H in H1. inversion H1; subst. reflexivity.
  - rewrite H in H1. inversion H1; subst. reflexivity.
  - rewrite H in H1. inversion H1; subst. reflexivity.
  - assert (HR1 : (heap1, Loc (Rgn2_Const true false r) l, Phi_Nil) =  (heap2, Loc (Rgn2_Const true false r0) l0, Phi_Nil)) by
        (apply IHDyn1; auto); inversion HR1.
    reflexivity.
  -  assert (HR1 : (heap1, Loc (Rgn2_Const true false r) l, Phi_Nil) =  (heap2, Loc (Rgn2_Const true false r0) l0, Phi_Nil)) by
        (apply IHDyn1; auto); inversion HR1.
     reflexivity.
  - assert ( HR1 :  (heap2, Eff effa0, phia0) = (heap2, Eff effa, phia) ) by (apply IHDyn1_1; auto).
    assert ( HR2 :  (heap2, Eff effb0, phib0) = (heap2, Eff effb, phib) ) by (apply IHDyn1_2; auto).
    inversion HR1; inversion HR2; now subst.
Qed.