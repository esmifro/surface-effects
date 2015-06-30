Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.DecidableTypeEx.
Require Import Coq.Structures.DecidableType.
Require Import Coq.ZArith.Znat.
Require Import Coq.FSets.FSetWeakList.
Require Import Coq.FSets.FSetFacts.
Require Import Coq.MSets.MSetProperties.
Require Import Coq.Arith.Peano_dec.
Require Import Definitions.

Import Effects.
Import Expressions.

Inductive ApproxEff : EffSpec -> EffSpec -> Prop :=
  | TopApprox  : forall (eff : EffSpec), eff <> Top -> ApproxEff eff Top                                                                   
  | SelfApprox : forall (eff : EffSpec), eff = eff -> ApproxEff eff eff.

Definition maximal_eff (n m : EffSpec) :=
  match n, m with
    | Top, _ => Top
    | _, Top => Top
    | Atom a, Atom b => Atom a ⊕ Atom b
    | Atom a,  x ⊕ y => Atom a ⊕ x ⊕ y
    | x ⊕ y, Atom a => Atom a ⊕ x ⊕ y
    | a ⊕ b, x ⊕ y => a ⊕ b ⊕ x ⊕ y                         
  end.                        

Definition eff_compare (n m : EffSpec) :=
  match n, m with
    | Top, _ => Gt
    | _, Top => Lt
    | _, _   => Eq              
  end. 

Module Eff_as_DT <: DecidableType.

  Definition t := EffSpec.

  Definition eq (x y: t) := x = y.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Lemma eq_dec : forall x y, { eq x y } + { ~ eq x y }.
  Proof.
    intros x y. unfold eq. decide equality. decide equality.
  Qed.  

  Definition eq_equiv := @eq_equivalence EffSpec.

End Eff_as_DT.


Module EffSet := MSetWeakList.Make (Eff_as_DT).
Module EffSetFacts := MSetFacts.Facts EffSet.
Module EffSetProps := MSetProperties.Properties EffSet.

SearchAbout EffSet.t.

Definition example1 := EffSet.empty.
Print example1.

Definition example2 := EffSet.singleton (Atom A).
Print example2.
 
(*Module Eff_as_OT <: OrderedType.

  Definition t := EffSet.t.

  Definition eq := @eq t.
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.

  Definition lt (x y : t) := EffSet.Subset x y /\ ~  EffSet.Equal x y.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    intros x y z. unfold lt. intuition. 
    - eapply EffSetProps.subset_trans; eauto.
    - apply H2. eapply EffSetProps.subset_equal with (s':=y) in H1; eauto. unfold EffSet.Equal. 
  Admitted.
  
  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    intros x y. intro.
    unfold eq; red; intro. subst.
    unfold lt in H. destruct H. contradict H0. intuition.
  Qed.   

  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    intros x y.  case_eq (EffSet.equal x y); intros.
    - apply EQ. unfold eq. admit. (*now apply EffSetFacts.equal_iff.*)
    - apply LT. unfold lt. split.
  Admitted.

  Lemma eq_dec : forall x y, { eq x y } + { ~ eq x y }.
  Proof.
    intros x y. unfold eq. admit.
  Qed.  

  Definition eq_equiv := @eq_equivalence t.
  
End Eff_as_OT.
 *)

Hypothesis TopApprox':
   Eff Top = Eff (Top ⊕ Top).       