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
Require Import CorrectnessLemmas.

Import TypeSoundness.

Inductive Atom_Heap : (DynamicAction * Heap) -> Prop :=
| PH_Alloc : forall r l v (heap : Heap), Atom_Heap (DA_Alloc r l, update_H ((r,l), v) heap)
| PH_Read : forall r l v (heap : Heap), find_H (r,l) heap = Some v -> Atom_Heap (DA_Read r l, heap)                                                
| PH_Write : forall r l v (heap : Heap), find_H (r,l) heap = Some v -> Atom_Heap (DA_Write r l, update_H ((r, l), v) heap). 

Inductive Phi_Heap : (Phi * Heap) -> (Phi * Heap) -> Prop :=
| PH_Nil    : forall heap,
                Phi_Heap (Phi_Nil, heap) (Phi_Nil, heap)
| PH_Atom   : forall i heap',
                Atom_Heap (i, heap') ->
                forall phi heap, Phi_Heap (Phi_Seq (Phi_Elem i) phi, heap)  (phi, heap') 
| PH_Seq_1  : forall phi1 phi1' heap heap',
                Phi_Heap (phi1, heap) (phi1', heap') ->
                forall phi2, Phi_Heap (Phi_Seq phi1 phi2, heap)  (Phi_Seq phi1' phi2, heap')
| PH_Seq_2  : forall phi2 phi2' heap heap',
                Phi_Heap (phi2, heap) (phi2', heap') ->
                forall phi1, Phi_Heap (Phi_Seq phi1 phi2, heap)  (Phi_Seq phi1 phi2', heap')
| PH_Seq_3  : forall phi2 phi2' heap heap',
                Phi_Heap (phi2, heap) (phi2', heap') ->
                Phi_Heap (Phi_Seq Phi_Nil phi2, heap)  (Phi_Seq Phi_Nil phi2', heap')
| PH_Seq_4  : forall heap,
                Phi_Heap (Phi_Seq Phi_Nil Phi_Nil, heap)  (Phi_Par Phi_Nil Phi_Nil, heap)
| PH_Par_1  : forall phi1 phi1' heap heap',
                Phi_Heap (phi1, heap) (phi1', heap') ->
                forall phi2, Phi_Heap (Phi_Par phi1 phi2, heap)  (Phi_Par phi1' phi2, heap')
| PH_Par_2  : forall phi2 phi2' heap heap',
                Phi_Heap (phi2, heap) (phi2', heap') ->
                forall phi1, Phi_Heap (Phi_Par phi1 phi2, heap)  (Phi_Par phi1 phi2', heap')
| PH_Par_3  : forall phi2 phi2' heap heap',
                Phi_Heap (phi2, heap) (phi2', heap') ->
                Phi_Heap (Phi_Par Phi_Nil phi2, heap)  (Phi_Par Phi_Nil  phi2', heap')
| PH_Par_4  : forall heap,
                Phi_Heap (Phi_Par Phi_Nil Phi_Nil, heap)  (Phi_Par Phi_Nil Phi_Nil, heap).                         
                        

Lemma unique_heap :
  forall (eff1 eff2 e1 e2: Expr) (heap heap_mu1 heap_mu2 heap_a heap_b : Heap)
         (env : Env) (rho : Rho) (acts_eff1 acts_eff2 acts_mu1 acts_mu2: Phi)
         (v1 v2 : Val) (theta1 theta2 : Theta),
                        (heap, env, rho, eff1) ⇓ (heap, Eff theta1, acts_eff1) ->
                        (heap, env, rho, eff2) ⇓ (heap, Eff theta2, acts_eff2) ->
                        (heap, env, rho, e1) ⇓ (heap_mu1, v1, acts_mu1) ->
                        (heap, env, rho, e2) ⇓ (heap_mu2, v2, acts_mu2) ->
                        acts_mu1 ⊑ theta1 ->
                        acts_mu2 ⊑ theta2 ->
                        Disjointness theta1 theta1 /\ not (Conflictness theta1 theta2) ->
                        Phi_Heap (Phi_Par acts_mu1 acts_mu2, heap)  (Phi_Par Phi_Nil Phi_Nil, heap_a) -> 
                        Phi_Heap (Phi_Seq acts_mu1 acts_mu2, heap)  (Phi_Seq Phi_Nil Phi_Nil, heap_b) ->
                        heap_a = heap_b.
Proof.
  intros eff1 eff2 e1 e2
         heap heap_mu1 heap_mu2 heap_a heap_b
         env rho
         acts_eff1 acts_eff2 acts_mu1 acts_mu2
         v1 v2
         theta1 theta2.
  intros H1 H2 H3 H4 H5 H6 H7 H8 H9.
  generalize dependent eff1.
  generalize dependent eff2.
  generalize dependent theta1.
  generalize dependent theta2.
  generalize dependent heap_a.
  generalize dependent heap_b. 
  generalize dependent acts_eff2.
  generalize dependent acts_eff1.
  induction acts_mu1, acts_mu2;
    try (solve [ intros acts_eff1 acts_eff2 heap_b HPhi2 heap_a HPhi1;
                 intros theta2 HTheta2 theta1 HTheta1;
                 intros HDisj; intros eff2 HEff2 eff1 HEff1;
                 inversion HPhi1; subst; inversion HPhi2; subst
               | intros acts_eff1 acts_eff2 heap_b HPhi2 heap_a HPhi1;
                 intros theta2 HTheta2 theta1 HTheta1;
                 intros HDisj; intros eff2 HEff2 eff1 HEff1;
                 inversion HPhi1; subst; inversion HPhi2; subst;
                 inversion H1; inversion H0; subst
               | intros acts_eff1 acts_eff2 heap_b HPhi2 heap_a HPhi1;
                 intros theta2 HTheta2 theta1 HTheta1;
                 intros HDisj; intros eff2 HEff2 eff1 HEff1;
                 inversion HPhi1; subst; inversion HPhi2; subst;
                 try (solve [inversion H1; inversion H0; subst; symmetry; assumption | inversion H0; subst; reflexivity])
               ]).
  - intros acts_eff1 acts_eff2 heap_b HPhi2 heap_a HPhi1;
    intros theta2 HTheta2 theta1 HTheta1;
    intros HDisj; intros eff2 HEff2 eff1 HEff1;
    inversion HPhi1; subst; inversion HPhi2; subst;
    inversion H1; inversion H0; subst; inversion H9; subst.
    + admit.
    + admit.
    + admit.
    + admit.
  - intros acts_eff1 acts_eff2 heap_b HPhi2 heap_a HPhi1;
    intros theta2 HTheta2 theta1 HTheta1;
    intros HDisj; intros eff2 HEff2 eff1 HEff1;
    inversion HPhi1; subst; inversion HPhi2; subst.
    inversion H1; inversion H0; subst; inversion H9; subst.
    admit.
Qed.        
    


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
