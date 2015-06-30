Require Import Arith.
Require Import ZArith.
Require Import Coq.Program.Equality.
Require Import Coq.Sets.Ensembles.
Require Import Ascii.
Require Import Keys.
Require Import Definitions.

Inductive lc  : type -> Prop :=
  | lc_fvar   : forall x, lc (Fvar x)
  | lc_arrow  : forall t1 t2, lc t1 -> lc t2 -> lc (Arrow_t t1 t2)
  | lc_forall : forall L t, (forall x, not_set_elem L x -> lc (open_var t x)) -> lc (Forall t).

Definition body t :=
  exists L, forall x, not_set_elem L x -> lc (open_var t x).

Definition closed t := 
  fv t = empty_set.

Lemma CLOSE_OPEN_VAR : forall t x, not_set_elem (fv t) x -> close_var x (open_var t x) = t.
Proof. 
  intros t x H.  unfold close_var, open_var. generalize 0.
  dependent induction t; simpl in *; intuition. 
  - case (AsciiVars.eq_dec n x); intros.
    * inversion e. subst. unfold not_set_elem in H. contradict H.  intuition.
    * reflexivity.
  - case_eq (beq_nat n n0); intros; simpl.
    * apply beq_nat_true in H0; subst.
      destruct (AsciiVars.eq_dec x x);  [reflexivity | contradict n; reflexivity].
    * reflexivity.
  - unfold close_var, open_var in *.
    assert (Ht1 : close_subst n x (open_subst n (Fvar x) t1 ) = t1)
     by (apply IHt1; unfold not_set_elem in *; unfold Complement in *; intuition).
    assert (Ht2 : close_subst n  x (open_subst n (Fvar x) t2) = t2)
     by (apply IHt2; unfold not_set_elem in *; unfold Complement in *; intuition).
    rewrite Ht1. rewrite Ht2. reflexivity.
  - rewrite IHt. reflexivity. assumption.
Qed.

Lemma OPEN_VAR_INJ : forall x t1 t2,
                       not_set_elem (fv t1) x -> not_set_elem (fv t2) x -> 
                       (open_var t1 x = open_var t2 x) -> (t1 = t2).
Proof.
  intros x t1 t2 HF1 HF2 HEq.
  rewrite <- (CLOSE_OPEN_VAR t1 x); auto.
  rewrite <- (CLOSE_OPEN_VAR t2 x); auto.
  f_equal. assumption.
Qed.

Lemma OPEN_CLOSE_VAR_ON_OPEN_VAR : forall (x y z : Name) t (i j : nat),
                                     i <> j -> y <> x -> not_set_elem (fv t) y ->
                                     open_subst i (Fvar y) (open_subst j (Fvar z) (close_subst j x t))
                                     = open_subst j (Fvar z) (close_subst j x (open_subst i (Fvar y) t)).
Proof.
  induction t; intros; simpl.
  - case_eq (AsciiVars.eq_dec n x); auto.
    intros; simpl. destruct (beq_nat j j); simpl; auto.
    case_eq (beq_nat j i); intros; auto. symmetry in H3. apply beq_nat_eq in H3. intuition.
  - case_eq (beq_nat n i); intros; simpl.
    assert (~ AsciiVars.eq y x). intros. unfold AsciiVars.eq. assumption.
    destruct  (AsciiVars.eq_dec y x); intuition. simpl.
    + case_eq (beq_nat n j); intros; simpl.
      * apply beq_nat_true in H2. apply beq_nat_true in H4. subst. intuition.
      * rewrite H2. reflexivity.
    + case_eq (beq_nat n j); intros; simpl.
      * reflexivity.
      * rewrite H2. reflexivity.
  - f_equal.
    + apply IHt1; auto. unfold not_set_elem, Complement, not in *.
      intros. apply H1. simpl. now apply Union_introl. 
    + apply IHt2; auto. unfold not_set_elem, Complement, not in *.
      intros. apply H1. simpl. now apply Union_intror.    
  - f_equal. apply IHt.  intuition. assumption. simpl in H1. assumption.
Qed.
  
Axiom PICK_SECOND_FRESH:
  forall L x t t', exists y, t' = t' /\ not_set_elem L x /\ y <> x /\
                             not_set_elem (set_union (set_union L (set_union (singleton_set x) (fv t))) (fv t')) y.
                                          
Lemma OPEN_CLOSE_VAR : forall x t, lc t -> open_var (close_var x t) x = t.
Proof.
  intros x t H. unfold open_var, close_var. generalize 0.
  induction H; intros; simpl.
  - destruct (AsciiVars.eq_dec x0 x); simpl; auto.
    assert (beq_nat n n = true) by (apply NPeano.Nat.eqb_refl). rewrite H.
    now inversion e.
  - f_equal. apply IHlc1. apply IHlc2.
  - f_equal. 
    edestruct PICK_SECOND_FRESH with (L:= L)
                                     (x := x)  
                                     (t := t)
                                     (t':= open_subst (S n) (Fvar x) (close_subst (S n) x t))
      as [y [goal [H_x_fresh [y_diff_x H_y_fresh]]]].
    
    apply (OPEN_VAR_INJ y).
    +  unfold not_set_elem, Complement, not in *.
       intros. apply H_y_fresh. now apply Union_intror. 
    +  unfold not_set_elem, Complement, not in *.
       intros. apply H_y_fresh. apply Union_introl. apply Union_intror. now apply Union_intror.
    + set (M := OPEN_CLOSE_VAR_ON_OPEN_VAR). unfold open_var in *.
      rewrite M; intuition.
      * apply H0. unfold not_set_elem, Complement, not in *.
        intros. apply H_y_fresh. apply Union_introl. now apply Union_introl.        
      * unfold not_set_elem, Complement, not in *.
        intros. apply H_y_fresh. apply Union_introl. apply Union_intror. now apply Union_intror.
Qed.


Lemma CLOSE_VAR_INJ : forall x t1 t2, lc t1 -> lc t2 -> (close_var x t1 = close_var x t2) -> (t1 = t2).
Proof.
  intros x t1 t2 Hlc1 Hlc2 Eq.
  rewrite <- (OPEN_CLOSE_VAR x t1); auto.
  rewrite <- (OPEN_CLOSE_VAR x t2); auto.
  now f_equal.
Qed.

Lemma LC_ABS_IFF_BODY : forall t, lc (Forall t) <-> body t.
Proof.
  intros. unfold body. intuition.
  - inversion H.  now exists L.
  - destruct H. econstructor; eauto.
Qed.

Lemma FV_OPEN : forall t u, included (fv (open u t)) (set_union (fv u) (fv t)).
Proof.
  intros t x. unfold open. generalize 0.
  induction t; unfold included, Included; intuition; simpl in *.
  - destruct (beq_nat n n0) in H; [ apply Union_introl; assumption | simpl in H; contradiction].
  - destruct H.
    + apply IHt1 in H.
      destruct H.
      * now apply Union_introl.
      * apply Union_intror. now apply Union_introl.
    + apply IHt2 in H.
      destruct H.
      *  now apply Union_introl.
      * apply Union_intror. now apply Union_intror.
  - unfold included, Included in IHt. apply IHt in H. assumption.   
Qed.

Lemma OPEN_VAR_FV : forall t x, included (fv (open_var t x)) (set_union (singleton_set x) (fv t)).
Proof.
  intros t x. unfold open_var. generalize 0.
  induction t; unfold included, Included; intuition; simpl in *.
  - destruct (AsciiVars.eq_dec x x0). inversion e; subst. 
    + destruct (beq_nat n n0) in H; [ apply Union_introl; assumption | simpl in H; contradiction].
    + destruct (beq_nat n n0) in H.
      * simpl in H. inversion H. contradiction.
      * simpl in H. contradiction.
  - destruct H.
    + apply IHt1 in H.
      destruct H.
      * now apply Union_introl.
      * apply Union_intror. now apply Union_introl.
    + apply IHt2 in H.
      destruct H.
      *  now apply Union_introl.
      * apply Union_intror. now apply Union_intror.
  - unfold included, Included in IHt. apply IHt in H. assumption.   
Qed.

Lemma CLOSE_VAR_FV : forall t x,  (fv (close_var x t)) = set_minus (fv t) x.
Proof.
  intros t x. unfold close_var. generalize 0.
  induction t; intros; unfold close_var, set_minus, set_union; simpl.
  - destruct (AsciiVars.eq_dec n x); simpl.
    inversion e; subst; simpl.
    + unfold empty_set, Subtract, Setminus. cbv.
      apply Extensionality_Ensembles. unfold Same_set, Included; intuition.
      * contradiction.
      * destruct H. apply H0 in H. contradiction.
    + unfold singleton_set, Subtract, Setminus. cbv.
      apply Extensionality_Ensembles.  unfold Same_set, Included. intuition.
      * econstructor; auto. intros. destruct H. contradict n1.  inversion H0. reflexivity.
      * destruct H. auto.
  - apply Extensionality_Ensembles.
    unfold Same_set, Subtract, Setminus, Included. intuition; cbv.
    * intuition. contradiction.
    * destruct H. contradiction.
  - unfold set_minus, close_var in IHt1. 
    unfold set_minus, close_var in IHt2.
    rewrite IHt1. rewrite IHt2. clear IHt1. clear IHt2. 
    unfold set_union. apply Extensionality_Ensembles.
    unfold Same_set, Subtract, Setminus, Included in *.
    intuition. destruct H.
    + destruct H; econstructor; auto. now apply Union_introl.
    + destruct H; econstructor; auto. now apply Union_intror. 
    + destruct H; destruct H.
      * apply Union_introl;  econstructor; auto.
      * apply Union_intror;  econstructor; auto.
 - unfold set_minus, close_var in IHt. rewrite IHt. reflexivity.   
Qed.      


Lemma OPEN_SUBST_LC_IND : forall t j v i u, i <> j ->
                                          open_subst i u (open_subst j v t) = open_subst j v t ->
                                          open_subst i u t = t.
Proof.
  intros t j v i u HDiff HEq. 
  generalize dependent i. generalize dependent j. generalize dependent u. generalize dependent v.
  induction t; simpl; intuition.
  - case_eq (beq_nat n i); intros; simpl; try reflexivity.
    case_eq (beq_nat n j); intros.
    + apply beq_nat_true in H.
      apply beq_nat_true in H0. subst. omega.
    + rewrite H0 in HEq. simpl in HEq. now rewrite H in HEq.
  - inversion HEq. f_equal. eapply IHt1; eauto. eapply IHt2; eauto.
  - inversion HEq. f_equal. apply IHt in H0. assumption. intuition. 
Qed.

Definition var : Name := ascii_of_nat 0.

Lemma OPEN_SUBST_LC : forall u t k, lc t -> open_subst k u t = t.
Proof.
  intros u t k Hlc. 
  generalize k. induction Hlc; intros; simpl.
  - reflexivity.
  - f_equal. apply IHHlc1. apply IHHlc2.
  - f_equal. unfold open_var in H0.
    pose (some := var). 
    edestruct PICK_SECOND_FRESH with (L:= L)
                                     (x:= some)  
                                     (t := t)
                                     (t':= t)
      as [y [goal [H_x_fresh [y_diff_x H_y_fresh]]]].
   apply (OPEN_SUBST_LC_IND t 0 (Fvar y)); [ omega| ].
   apply H0. unfold not_set_elem, Complement, not in *.
   intros. apply H_y_fresh. apply Union_introl. now apply Union_introl. 
Qed.


Lemma SUBST_OPEN : forall x u t v, lc u -> 
                                   subst x u (open v t) = open (subst x u v) (subst x u t).
Proof.
  intros. unfold open. generalize 0.
  induction t; intros; simpl. 
  - destruct (AsciiVars.eq_dec n x); simpl; [ | reflexivity].
    symmetry. now apply OPEN_SUBST_LC.
  - destruct (beq_nat n n0); simpl; reflexivity.  
  - f_equal. apply IHt1. apply IHt2.
  - f_equal. apply IHt.
Qed.


Lemma SUBST_OPEN_VAR : forall x y u t, y <> x -> lc u -> 
                                       subst x u (open_var t y) = open_var (subst x u t) y.
Proof.
  intros x y u t H Hlc.
  unfold open_var.
  replace (open_subst 0 (Fvar y) t) with (open (Fvar y) t) by (now unfold open).
  replace (open_subst 0 (Fvar y) (subst x u t)) with (open (Fvar y)  (subst x u t)) by (now unfold open).
  rewrite SUBST_OPEN.
  - f_equal; simpl.
    assert (~ AsciiVars.eq y x). intros. unfold AsciiVars.eq. assumption.
    destruct  (AsciiVars.eq_dec y x); intuition.
  - assumption.
Qed.

Lemma CLOSE_VAR_SUBST_FRESH : forall k x t, not_set_elem (fv t) x -> close_subst k x t = t.
Proof.
  intros k n t H. generalize k. induction t; intros; simpl.
  - unfold not_set_elem, Complement, not in *. simpl in *.
    destruct (AsciiVars.eq_dec n0 n).
    + inversion e; subst. contradict H. apply In_singleton.
    + reflexivity.
  - reflexivity.
  - f_equal.
    + apply IHt1. unfold not_set_elem, Complement, not in *. simpl in *.
      intros. apply H. now apply  Union_introl.
    + apply IHt2. unfold not_set_elem, Complement, not in *. simpl in *.
      intuition.
  - f_equal. apply IHt.
    unfold not_set_elem, Complement, not in *. simpl in *.
    intuition.
Qed.


Lemma SUBST_CLOSE_VAR : forall x y u t, y <> x ->
                                        not_set_elem (fv u) y -> 
                                        subst x u (close_var y t) = close_var y (subst x u t).
Proof.
  intros x y u t H1 H2.
  unfold not_set_elem, Complement, not in H2.
  unfold close_var. generalize 0.
  induction t; intros; simpl. 
  - case_eq  (AsciiVars.eq_dec n y); intros.
    + case_eq  (AsciiVars.eq_dec n x); intros.
      * inversion e; inversion e0; subst; intuition.
      *  inversion e; subst; simpl.
         destruct (AsciiVars.eq_dec y y); [reflexivity | intuition].
    + case_eq  (AsciiVars.eq_dec n x); intros.
      * unfold subst.
        rewrite CLOSE_VAR_SUBST_FRESH.
        rewrite H0. reflexivity. intuition.
      * unfold subst. rewrite H0.
        rewrite CLOSE_VAR_SUBST_FRESH; [reflexivity | ].
        unfold not_set_elem, Complement, not. simpl. intros.
        destruct H3. intuition.
  - reflexivity.
  - f_equal. apply IHt1. apply IHt2.
  - f_equal. apply IHt.
Qed.

Lemma SUBST_FRESH : forall x t u, not_set_elem (fv t) x -> subst x u t = t.
Proof.
  intros x. induction t; intros u H; simpl.
  - unfold not_set_elem, Complement in H.
    case (AsciiVars.eq_dec n x); intros.
    * contradict H. inversion e; subst. apply In_singleton.
    * reflexivity.
  - reflexivity.
  - f_equal; [apply IHt1 | apply IHt2];
    unfold not_set_elem, Complement, not, fv in *; fold fv in *;
    intros; apply H; [now apply  Union_introl | now apply  Union_intror].
  - f_equal. apply IHt. unfold not_set_elem, Complement, not in *; intros.
    apply H. now simpl.
Qed.


Lemma SUBST_INTRO : forall x t u, not_set_elem (fv t) x ->
                                  lc u ->
                                  open u t = subst x u (open_var t x).
Proof.
  intros x t u Hfv Hlc. unfold open_var.
  replace (open_subst 0 (Fvar x) t) with (open (Fvar x) t) by (now unfold open).
  rewrite SUBST_OPEN; auto. f_equal.
  - simpl in *; destruct (AsciiVars.eq_dec x x); intros;
    [reflexivity | unfold AsciiVars.eq in n; contradict n; reflexivity ].
  - symmetry. now apply SUBST_FRESH.
Qed.

Lemma CLOSE_VAR_RENAME : forall x y t, not_set_elem (fv t) x ->
                                       close_var y t = close_var x (subst y (Fvar x) t).
Proof.
  intros x y t. unfold close_var.
  generalize x. generalize 0.
  induction t; intros; simpl. 
  - destruct (AsciiVars.eq_dec n y); simpl.
    + destruct (AsciiVars.eq_dec x0 x0); simpl; [reflexivity | intuition].
    + unfold not_set_elem, Complement, not, fv in H. 
      destruct (AsciiVars.eq_dec n x0); simpl; [ |reflexivity ]. 
      unfold AsciiVars.eq in e. subst. contradict H.
      apply In_singleton.
  - reflexivity.
  - f_equal; [apply IHt1 | apply IHt2];
    unfold not_set_elem, Complement, not, fv in *; fold fv in *;
    intros; apply H; [now apply  Union_introl | now apply  Union_intror].
  - f_equal. apply IHt. unfold not_set_elem, Complement, not in *; intros.
    apply H. now simpl.   
Qed.

Inductive lc_at  : type * nat -> Prop :=
  | lc_at_bvar   : forall i k, i < k -> lc_at (Bvar i, k)
  | lc_at_fvar   : forall x, lc_at (Fvar x, 0)
  | lc_at_arrow  : forall t1 t2 k, lc_at (t1, k) /\ lc_at (t2,k) -> lc_at (Arrow_t t1 t2, k)
  | lc_at_forall : forall t k, lc_at (t, k+1) -> lc_at (Forall t, k).

Lemma LC_FROM_LC_AT : forall t, lc t <-> lc_at (t, 0).
Proof.
  intro t. intuition.
  - dependent induction t.
    + constructor.
    + inversion H.
    + inversion H; subst. constructor. split.
      * apply IHt1. assumption.
      * apply IHt2. assumption.
    + constructor.
      inversion H.
Admitted.  