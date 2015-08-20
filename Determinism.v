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
Require Import Environment.
Require Import Definitions2.
Require Import CorrectnessLemmas.

Lemma Seq_Left_Pres :
  forall phi1 phi1' heap1 heap1' n1 phi2,
    (phi1, heap1) =a=>* (phi1', heap1', n1) ->
    (Phi_Seq phi1 phi2, heap1) =a=>* (Phi_Seq phi1' phi2, heap1', n1).
Proof.
  intros phi1 phi1' heap1 heap1' n1 phi2 HSteps.
  dependent induction HSteps; repeat econstructor; eassumption.
Qed.

Lemma Seq_Right_Pres :
  forall phi2 phi2' heap2 heap2' n2,
    (phi2, heap2) =a=>* (phi2', heap2', n2) ->
    (Phi_Seq Phi_Nil phi2, heap2) =a=>* (Phi_Seq Phi_Nil phi2', heap2', n2).
Proof.
  intros phi2 phi2' heap2 heap2' n2 HSteps.
  dependent induction HSteps; repeat econstructor; eassumption.
Qed.

Lemma Par_Left_Pres :
  forall phi1 phi1' heap1 heap1' n1 phi2,
    (phi1, heap1) =a=>* (phi1', heap1', n1) ->
    (Phi_Par phi1 phi2, heap1) =a=>* (Phi_Par phi1' phi2, heap1', n1).
Proof.
  intros phi1 phi1' heap1 heap1' n1 phi2 HSteps.
  dependent induction HSteps; repeat econstructor; eassumption.
Qed.

Lemma Par_Right_Pres :
  forall phi2 phi2' heap2 heap2' n2 phi1 ,
    (phi2, heap2) =a=>* (phi2', heap2', n2) ->
    (Phi_Par phi1 phi2, heap2) =a=>* (Phi_Par phi1 phi2', heap2', n2).
Proof.
  intros phi2 phi2' heap2 heap2' n2 phi1 HSteps.
  dependent induction HSteps; repeat econstructor; eassumption.
Qed.



Lemma H_same_key:
  forall t x v e, 
    H.find (elt := t) x (H.add x v e) = Some v.
Proof.
  intros. rewrite <- HMapP.find_mapsto_iff. rewrite -> HMapP.add_mapsto_iff.
  left. intuition. 
Qed.  

Lemma H_diff_key_1:
  forall t a b v v' e,   
    a <> b ->
    H.find (elt := t) a (H.add b v e) = Some v' -> 
    H.find (elt := t) a e = Some v'.
Proof.
  intros. 
  rewrite <- HMapP.find_mapsto_iff in H0. rewrite -> HMapP.add_mapsto_iff in H0.
  destruct H0 as [ [[? ?] ?] |  [ ? ?]].
  - destruct a. destruct b. simpl in *. destruct H. subst. reflexivity.
  - rewrite -> HMapP.find_mapsto_iff in H1. assumption. 
Qed.

Lemma H_diff_key_2:
  forall t a b v v' e,   
    b <> a ->
    H.find (elt := t) a e = Some v' ->
    H.find (elt := t) a (H.add b v e) = Some v'.
Proof.
  intros. 
  rewrite <- HMapP.find_mapsto_iff.  rewrite -> HMapP.add_mapsto_iff.
  right; split.
  - intuition. apply H. destruct a. destruct b. simpl in *. subst. reflexivity.
  - now rewrite HMapP.find_mapsto_iff.
Qed.

Lemma H_same_key_add_twice_1 :
  forall r0 l0 r l v v0 heap, 
    H.find (elt:=Val) (r0, l0) (H.add (r0, l0) v0 (H.add (r, l) v heap)) = H.find (elt:=Val) (r0, l0) (H.add (r0, l0) v0 heap).
Proof.
  intros. rewrite H_same_key. rewrite H_same_key. reflexivity.
Qed. 

Lemma H_same_key_add_twice_2 :
  forall k k0 v v0 heap,
    k <> k0 ->
    H.find (elt:=Val) k0 (H.add k v (H.add k0 v0 heap)) = H.find (elt:=Val) k0 (H.add k0 v0 heap).
Proof.
  intros. rewrite H_same_key. apply H_diff_key_2; [assumption | apply H_same_key]. 
Qed.

Lemma H_same_key_add_twice_3 :
  forall k k0 v v0 heap,
    H.find (elt:=Val) k0 (H.add k0 v0 (H.add k v heap)) = H.find (elt:=Val) k0 (H.add k0 v0 heap).
Proof.
  intros. rewrite H_same_key. symmetry. apply H_same_key. 
Qed. 

Lemma H_diff_key_add_twice_1 :
  forall k0 k heap (v v0 e: Val), 
    H.find (elt:=Val) k0 (H.add k0 v0 heap) = Some e ->
    H.find (elt:=Val) k0 (H.add k0 v0 (H.add k v heap)) = Some e.
Proof.
  intros k0 k heap v v0 e H.
  rewrite H_same_key_add_twice_3. assumption.
Qed.

Lemma H_diff_key_add_twice_2 :
  forall k0 k heap (v v0 e: Val),
    k <> k0 ->
    H.find (elt:=Val) k (H.add k v heap) = Some e ->
    H.find (elt:=Val) k (H.add k v (H.add k0 v0 heap)) = Some e.
Proof.
  intros k0 k heap v v0 e H. intro. 
  rewrite H_same_key_add_twice_3. auto. 
Qed.

Lemma H_diff_key_add_comm_1:
  forall k k1 k0 heap e v v0,
    k1 <> k ->
    k <> k0 ->
    H.find (elt:=Val) k (H.add k0 v0 (H.add k1 v heap)) = Some e ->
    H.find (elt:=Val) k (H.add k1 v heap) = Some e. 
Proof.
  intros  k k1 k0 heap e v v0 H1 H2 H3.
  rewrite <- HMapP.find_mapsto_iff.  rewrite -> HMapP.add_mapsto_iff.
  right. split.
  - contradict H1. destruct k1; destruct k.  unfold fst, snd in *. intuition.
  - apply  H_diff_key_1 in H3; auto. apply  H_diff_key_1 in H3; auto. now rewrite HMapP.find_mapsto_iff.
Qed.

Lemma H_diff_key_add_comm_2:
  forall k k1 k0 heap e v v0,
    k1 <> k ->
    k <> k0 ->
    H.find (elt:=Val) k (H.add k1 v heap) = Some e ->
    H.find (elt:=Val) k (H.add k1 v (H.add k0 v0 heap)) = Some e. 
Proof.
  intros  k k1 k0 heap e v v0 H1 H2 H3.
  rewrite <- HMapP.find_mapsto_iff.  rewrite -> HMapP.add_mapsto_iff.
  right. split.
  - contradict H1. destruct k1; destruct k.  unfold fst, snd in *. intuition.
  - apply  H_diff_key_1 in H3; auto. rewrite HMapP.find_mapsto_iff. apply  H_diff_key_2; auto. 
Qed.


Lemma H_diff_keys_same_outer_k_2 :
  forall r r0 r1 l l0 l1 v v0  heap e, 
    (r0, l0) <> (r, l) -> 
    H.find (elt:=Val) (r1, l1) (H.add (r, l) v (H.add (r0, l0) v0 heap)) = Some e ->
    H.find (elt:=Val) (r1, l1) (update_H (r0, l0, v0) (update_H (r, l, v) heap)) = Some e.
Proof.
  intros  r r0 r1 l l0 l1 v v0 heap e H1 H2. 
  destruct (RegionVars.eq_dec (r1, l1) (r0, l0)); destruct (RegionVars.eq_dec (r1, l1) (r, l)).
  - destruct e0. simpl in *. subst. unfold update_H in *; simpl in *.
    apply  H_diff_key_add_twice_2; auto.
    apply  H_diff_key_1 in H2; auto.
  - destruct e0. simpl in *. rewrite H in *.  rewrite H0 in *.
    apply  H_diff_key_1 in H2; auto. apply H_diff_key_add_twice_2; auto.
  - destruct e0. simpl in *. rewrite H in *.  rewrite H0 in *.
    apply  H_diff_key_2; auto.
    rewrite  H_same_key_add_twice_3 in H2; auto.
  - apply  H_diff_key_2; auto. 
    + unfold  RegionVars.eq in n. contradict n. inversion n. intuition.
    + apply  H_diff_key_2; auto.
      * unfold  RegionVars.eq in n0. contradict n0. inversion n0. intuition.
      * apply  H_diff_key_1 in H2. apply  H_diff_key_1 in H2; auto.
        { unfold  RegionVars.eq in n. contradict n. inversion n. intuition. }
        { unfold  RegionVars.eq in n0. contradict n0. inversion n0. intuition. }
Qed.

Lemma Read_Preserved :
  forall r1 l1 v1 phi2 phi2' heap0 heap2',
    H.find (r1, l1) heap0 = Some v1 ->
    Disjoint_Traces (phi_as_list (Phi_Elem (DA_Read r1 l1 v1))) (phi_as_list phi2) ->
    (phi2, heap0) ===> (phi2', heap2') ->
    H.find (r1, l1) heap2' = Some v1.
Proof.
  intros r1 l1 v1 phi2 phi2' heap0 heap2' HFind HDisj HStep.
  dependent induction HStep.
  - assert (Disjoint_Dynamic (DA_Read r1 l1 v1) (DA_Alloc r l v))
      by (inversion HDisj; apply H; simpl; intuition).
    inversion H; subst.
    apply H_diff_key_2; auto.
  - assumption.
  - assert (Disjoint_Dynamic (DA_Read r1 l1 v1) (DA_Write r l v))
      by (inversion HDisj; apply H0; simpl; intuition).
    inversion H0; subst.
    apply H_diff_key_2; auto.
  - eapply IHHStep; try reflexivity.
    + eassumption.
    + replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0) in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj; intuition.
  - eapply IHHStep; try reflexivity.
    + eassumption.
    + replace (phi_as_list (Phi_Seq Phi_Nil phi0)) with (phi_as_list Phi_Nil ++ phi_as_list phi0) in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj; intuition.
  - assumption.
  - eapply IHHStep; try reflexivity.
    + eassumption.
    + replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0) in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj; intuition.
  - eapply IHHStep; try reflexivity.
    + eassumption.
    + replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0) in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj; intuition.
  - assumption.
Qed.

Lemma Disjointness_Preserves_Update_Alloc:
  forall phi1 phi1' heap heap' r l v, 
  (phi1, heap) ===> (phi1', heap') ->
  Disjoint_Traces (DA_Alloc r l v :: nil) (phi_as_list phi1) ->
  exists heapA,
    H.Equal heapA (update_H (r, l, v) heap') /\
    (phi1, update_H (r, l, v) heap) ===> (phi1', heapA).
Proof.
  intros phi1 phi1' heap heap' r l v H1 H2.
  generalize dependent r.
  generalize dependent l.
  generalize dependent v. 
  dependent induction H1; intros; inversion H2; subst; simpl in H.
  - assert (Disjoint_Dynamic (DA_Alloc r0 l0 v0) (DA_Alloc r l v)) by (apply H; intuition).
    inversion H0; subst. 
    exists (update_H (r, l, v) (update_H (r0, l0, v0) heap)). split. 
    + apply HMapP.Equal_mapsto_iff; intros. split; intros. 
      * apply HMapP.find_mapsto_iff. apply HMapP.find_mapsto_iff in H1.
        destruct k; apply H_diff_keys_same_outer_k_2; auto.
      * apply HMapP.find_mapsto_iff. apply HMapP.find_mapsto_iff in H1.
        destruct k.  apply H_diff_keys_same_outer_k_2; auto.
    + constructor.
  - assert (Disjoint_Dynamic (DA_Alloc r0 l0 v0) (DA_Read r l v)) by (apply H0; apply in_eq).
    inversion H1; subst. exists ( update_H (r0, l0, v0) heap'). split.
    + apply HMapP.Equal_refl.
    + constructor.
      apply  H_diff_key_2; [ simpl | ]; assumption.
  - assert (Disjoint_Dynamic (DA_Alloc r0 l0 v0) (DA_Write r l v)) by (apply H0; apply in_eq).
    inversion H1; subst. unfold update_H; simpl. 
    exists (H.add (r, l) v ( H.add (r0, l0) v0 heap)). split. 
    + apply HMapP.Equal_mapsto_iff; intros. split; intros. 
      * apply HMapP.find_mapsto_iff. apply HMapP.find_mapsto_iff in H3.
        destruct k; apply H_diff_keys_same_outer_k_2; auto.
      * apply HMapP.find_mapsto_iff. apply HMapP.find_mapsto_iff in H3.
        destruct k; apply H_diff_keys_same_outer_k_2; auto.
    + constructor.
      apply HMapP.add_neq_in_iff; auto. simpl. intuition.
      (*eapply H_diff_key_2; eauto.*)
  - simpl in H2. replace (DA_Alloc r l v :: nil) with (phi_as_list (Phi_Elem (DA_Alloc r l v))) in H2
      by (simpl; reflexivity).
    apply Disjointness_app_app_and_l in H2. destruct H2.
    destruct (IHPhi_Heap_Step  v l r H0). exists x; intuition.
    constructor; assumption.
  - destruct (IHPhi_Heap_Step  v l r H2). exists x; intuition.
    constructor; assumption.
  - exists (update_H (r, l, v) heap'). split; [apply HMapP.Equal_refl | constructor ].
  - simpl in H2. replace (DA_Alloc r l v :: nil) with (phi_as_list (Phi_Elem (DA_Alloc r l v))) in H2
      by (simpl; reflexivity).
    apply Disjointness_app_app_and_l in H2. destruct H2.
    destruct (IHPhi_Heap_Step  v l r H0). exists x; intuition.
    constructor; assumption.
  -  simpl in H2. replace (DA_Alloc r l v :: nil) with (phi_as_list (Phi_Elem (DA_Alloc r l v))) in H2
      by (simpl; reflexivity).
    apply Disjointness_app_app_and_l in H2. destruct H2.
    destruct (IHPhi_Heap_Step  v l r H2). exists x; intuition.
    constructor; assumption.
  - exists (update_H (r, l, v) heap'). split; [apply HMapP.Equal_refl | constructor ].
Qed.

Lemma Disjointness_Preserves_Update_Write:
  forall phi1 phi1' heap heap' r l v, 
  (phi1, heap) ===> (phi1', heap') ->
  Disjoint_Traces (DA_Write r l v :: nil) (phi_as_list phi1) ->
  exists heapA,
    H.Equal heapA (update_H (r, l, v) heap') /\
    (phi1, update_H (r, l, v) heap) ===> (phi1', heapA).
Proof.
  intros phi1 phi1' heap heap' r l v H1 H2.
  generalize dependent r.
  generalize dependent l.
  generalize dependent v.
  dependent induction H1; intros; inversion H2; subst; simpl in H.
  - assert (Disjoint_Dynamic (DA_Write r0 l0 v0) (DA_Alloc r l v)) by (apply H; intuition).
    inversion H0; subst. 
    exists (update_H (r, l, v) (update_H (r0, l0, v0) heap)). split. 
    + apply HMapP.Equal_mapsto_iff; intros. split; intros. 
      * apply HMapP.find_mapsto_iff. apply HMapP.find_mapsto_iff in H1.
        destruct k; apply H_diff_keys_same_outer_k_2; auto.
      * apply HMapP.find_mapsto_iff. apply HMapP.find_mapsto_iff in H1.
        destruct k.  apply H_diff_keys_same_outer_k_2; auto.
    + constructor.
  - assert (Disjoint_Dynamic (DA_Write r0 l0 v0) (DA_Read r l v)) by (apply H0; apply in_eq).
    inversion H1; subst. exists ( update_H (r0, l0, v0) heap'). split.
    + apply HMapP.Equal_refl.
    + constructor.
      apply  H_diff_key_2; [ intuition | assumption ]. 
  - assert (Disjoint_Dynamic (DA_Write r0 l0 v0) (DA_Write r l v)) by (apply H0; apply in_eq).
    inversion H1; subst. unfold update_H; simpl. 
    exists (H.add (r, l) v ( H.add (r0, l0) v0 heap)). split. 
    + apply HMapP.Equal_mapsto_iff; intros. split; intros. 
      * apply HMapP.find_mapsto_iff. apply HMapP.find_mapsto_iff in H3.
        destruct k; apply H_diff_keys_same_outer_k_2; auto.
      * apply HMapP.find_mapsto_iff. apply HMapP.find_mapsto_iff in H3.
        destruct k; apply H_diff_keys_same_outer_k_2; auto.
    + constructor.
      apply HMapP.add_neq_in_iff; auto. simpl. intuition.
      (*eapply H_diff_key_2; eauto.*)
  - simpl in H2. replace (DA_Write r l v :: nil) with (phi_as_list (Phi_Elem (DA_Write r l v))) in H2
      by (simpl; reflexivity).
    apply Disjointness_app_app_and_l in H2. destruct H2.
    destruct (IHPhi_Heap_Step  v l r H0). exists x; intuition.
    constructor; assumption.
  - destruct (IHPhi_Heap_Step  v l r H2). exists x; intuition.
    constructor; assumption.
  - exists (update_H (r, l, v) heap'). split; [apply HMapP.Equal_refl | constructor ].
  - simpl in H2. replace (DA_Write r l v :: nil) with (phi_as_list (Phi_Elem (DA_Write r l v))) in H2
      by (simpl; reflexivity).
    apply Disjointness_app_app_and_l in H2. destruct H2.
    destruct (IHPhi_Heap_Step  v l r H0). exists x; intuition.
    constructor; assumption.
  -  simpl in H2. replace (DA_Write r l v :: nil) with (phi_as_list (Phi_Elem (DA_Write r l v))) in H2
      by (simpl; reflexivity).
    apply Disjointness_app_app_and_l in H2. destruct H2.
    destruct (IHPhi_Heap_Step  v l r H2). exists x; intuition.
    constructor; assumption.
  - exists (update_H (r, l, v) heap'). split; [apply HMapP.Equal_refl | constructor ].
Qed.

Lemma Aux_Aux_Step_Ext_Heap :
forall phi heapA heapB phi' heapA',
   (phi, heapA) ===> (phi', heapA') ->
   H.Equal heapA heapB ->
   exists heapB',
     H.Equal heapA' heapB' /\
     (phi, heapB) ===> (phi', heapB').
Proof.
  intros phi heapA heapB phi' heapA' HStep.
  generalize dependent heapB.
  dependent induction HStep; intros heapB HEqual.
  - { exists (update_H (r, l, v) heapB). split.
      - unfold H.Equal in *; unfold update_H in *; simpl in *.
        intros [r' l'].
        destruct (RegionVars.eq_dec (r', l') (r, l)).
        * inversion_clear e; simpl in *; subst.
          do 2 rewrite H_same_key_1. reflexivity.
        * unfold RegionVars.eq in *; simpl in *.
          rewrite HMapP.add_neq_o by (contradict n; intuition).
          rewrite HMapP.add_neq_o by (contradict n; intuition).
          apply HEqual.
      - constructor. }
  - { exists heapB. split.
      - assumption.
      - constructor.
        unfold find_H in *. unfold H.Equal in HEqual.
        rewrite <- H. symmetry. apply HEqual. }
  - { exists (update_H (r, l, v) heapB). split.
      - unfold H.Equal in *; unfold update_H in *; simpl in *.
        intros [r' l'].
        destruct (RegionVars.eq_dec (r', l') (r, l)).
        * inversion_clear e; simpl in *; subst.
          do 2 rewrite H_same_key_1. reflexivity.
        * unfold RegionVars.eq in *; simpl in *.
          rewrite HMapP.add_neq_o by (contradict n; intuition).
          rewrite HMapP.add_neq_o by (contradict n; intuition).
          apply HEqual.
      - constructor.
        eapply Heap.HMapP.In_m; eauto using HMapP.Equal_sym. }
  - destruct (IHHStep heapB HEqual) as [heapB' [? ?]].
    exists heapB'; split; [assumption | constructor; auto].
  - destruct (IHHStep heapB HEqual) as [heapB' [? ?]].
    exists heapB'; split; [assumption | constructor; auto].
  - exists heapB; split; [assumption | constructor].
  - destruct (IHHStep heapB HEqual) as [heapB' [? ?]].
    exists heapB'; split; [assumption | constructor; auto].
  - destruct (IHHStep heapB HEqual) as [heapB' [? ?]].
    exists heapB'; split; [assumption | constructor; auto].
  - exists heapB; split; [assumption | constructor].
Qed.

Lemma Aux_Step_Ext_Heap :
forall phi heapA heapB phi' heapA' n',
   (phi, heapA) =a=>* (phi', heapA', n') ->
   H.Equal heapA heapB ->
   exists heapB',
     H.Equal heapA' heapB' /\
     (phi, heapB) =a=>* (phi', heapB', n').
Proof.
  intros  phi heapA heapB phi' heapA' n' H1 H2 .  
  generalize dependent heapB. 
  dependent induction H1; intros.
  - { exists heapB. intuition. constructor. }
  - edestruct Aux_Aux_Step_Ext_Heap as [heapB' [? ?]]; eauto.
    exists heapB'; split; [assumption | constructor; assumption].
  - edestruct (IHPhi_Heap_StepsAux1 heapB H2) as [heap1 [? ?]].
    edestruct (IHPhi_Heap_StepsAux2 heap1 H) as [heap2 [? ?]].
    exists heap2. intuition.
    replace (S (n'0 + n'')) with (1 + n'0 + n'') by (simpl; reflexivity).
    econstructor. eassumption. assumption.
Qed.

Lemma Par_Step_Alloc_Alloc :
  forall phi1 r1 l1 v1 phi2 r2 l2 v2 phi1' phi2' heapa heapb heap1' heap2',
    phi1 = Phi_Elem (DA_Alloc r1 l1 v1) ->
    phi2 = Phi_Elem (DA_Alloc r2 l2 v2) ->
    Det_Trace phi1 ->
    Det_Trace phi2 ->
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    ~ Conflict_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    H.Equal heapa heapb ->
    (phi1, heapa) ===> (phi1', heap1') ->
    (phi2, heapb) ===> (phi2', heap2') ->
    exists heapA, exists heapB,
      H.Equal heapA heapB /\
      (Phi_Par phi1' phi2, heap1') ===> (Phi_Par phi1' phi2', heapA) /\
      (Phi_Par phi1 phi2', heap2') ===> (Phi_Par phi1' phi2', heapB).
Proof.
  intros  phi1 r l v phi2 r0 l0 v0 phi1' phi2' heapa heapb heap1' heap2'
          H1 H2 Det1 HDet2 HDisj HConf HEqual HStep1 HStep2; subst.
  inversion HStep1; inversion HStep2; subst.
  exists (update_H (r0, l0, v0) (update_H (r, l, v) heapa)). exists (update_H (r, l, v) (update_H (r0, l0, v0) heapb)). repeat split. 
  - inversion HDisj; subst. simpl in H. 
    assert (Disjoint_Dynamic (DA_Alloc r l v) (DA_Alloc r0 l0 v0)) by (apply H; left; reflexivity).
    inversion H0; subst. unfold update_H in *. simpl in *.
    inversion H0; subst. unfold update_H in *. simpl in *. 

    destruct (RegionVars.eq_dec (r, l) (r0, l0)).
    + inversion e. unfold fst, snd in *; subst.
      destruct H2. reflexivity.
    + clear n. 
      apply HMapP.Equal_mapsto_iff; intros. destruct k.
      destruct (RegionVars.eq_dec (n, n0) (r0, l0)); destruct (RegionVars.eq_dec (n, n0) (r, l)); split.
      * inversion e0; inversion e1. unfold fst, snd in *; subst.
        destruct H2. subst; reflexivity.
      * inversion e0; inversion e1. unfold fst, snd in *; subst.
        destruct H2. subst; reflexivity.
      * unfold RegionVars.eq in *. unfold fst, snd in *; subst. destruct e0; subst.
        intro. apply  HMapP.find_mapsto_iff in H1.
        rewrite H_same_key_add_twice_1 in H1. rewrite H_same_key in H1.
        apply HMapP.add_mapsto_iff. right; simpl. split; [ intuition | ].
        apply HMapP.find_mapsto_iff. rewrite H_same_key. assumption.
      * unfold RegionVars.eq in *. unfold fst, snd in *; subst. destruct e0; subst. 
        intro. apply  HMapP.find_mapsto_iff in H1. rewrite H_same_key_add_twice_2 in H1; [| assumption].
        { rewrite H_same_key in H1.  apply  HMapP.find_mapsto_iff.
          inversion H1; subst. rewrite H_same_key_add_twice_1. rewrite H_same_key. assumption. }
      * unfold RegionVars.eq in *. unfold fst, snd in *; subst. destruct e0; subst.  
        intro. apply HMapP.add_mapsto_iff. left. simpl. split; auto.   
        apply  HMapP.find_mapsto_iff in H1.  rewrite H_same_key_add_twice_2 in H1; [| intuition].
        rewrite HMapP.add_o in H1. 
        destruct (HMapP.eq_dec (r, l) (r, l)) in H1. 
        { inversion H1; subst. auto.  }
        { simpl in *. contradict n. auto. } 
      * unfold RegionVars.eq in *. unfold fst, snd in *; subst. destruct e0; subst. 
        intro.  apply HMapP.add_mapsto_iff. right. split; simpl; [intuition |].
        apply HMapP.add_mapsto_iff. left; simpl; split; auto.
        apply HMapP.add_mapsto_iff in H1.
        destruct H1 as [[? ?]| ?]; [assumption | destruct H1 as [? ?  ?]; contradict H1; auto].
      * unfold RegionVars.eq in *. unfold fst, snd in *; subst.
        intro. apply  HMapP.find_mapsto_iff in H1.
        apply  HMapP.find_mapsto_iff.
        { eapply H_diff_key_add_comm_2.
          - contradict n2. inversion n2. auto.
          - contradict n1. inversion n1. auto.
          - apply H_diff_key_2.
            + contradict n2. inversion n2. auto.
            + rewrite <- H1. unfold H.Equal in HEqual. rewrite <- HEqual.
              rewrite H1. apply H_diff_key_1 in H1.
              * apply H_diff_key_1 in H1; [assumption | contradict n1; inversion n1; intuition].
              * contradict n1; inversion n1; intuition.
        }
      * unfold RegionVars.eq in *. unfold fst, snd in *; subst.
        intro. apply  HMapP.find_mapsto_iff in H1.
        apply  HMapP.find_mapsto_iff.
        { eapply H_diff_key_add_comm_2.
          - contradict n1. inversion n1. auto.
          - contradict n2. inversion n2. auto.
          - apply H_diff_key_2.
            + contradict n1. inversion n1. auto.
            + rewrite <- H1. unfold H.Equal in HEqual. rewrite HEqual.
              rewrite H1. apply H_diff_key_1 in H1.
              * apply H_diff_key_1 in H1; [assumption | contradict n1; inversion n1; intuition].
              * contradict n1; inversion n1; intuition.
        }
  - do 2 constructor.    
  - econstructor. inversion HDisj; subst.
    assert (Disjoint_Dynamic (DA_Alloc r l v) (DA_Alloc r0 l0 v0)) by (apply H; simpl; auto).
    inversion H0; subst. 
    eapply Disjointness_Preserves_Update_Alloc in HStep2; eauto.
    destruct HStep2 as [heap' [? ?]]. inversion H0; subst. unfold H.Equal in H1.
    inversion H3; subst.
    unfold update_H in *; simpl in *.
    admit.  
Qed.

Lemma Par_Step_Write_Write :
  forall phi1 r1 l1 v1 phi2 r2 l2 v2 phi1' phi2' heapa heapb heap1' heap2',
    phi1 = Phi_Elem (DA_Write r1 l1 v1) ->
    phi2 = Phi_Elem (DA_Write r2 l2 v2) ->
    Det_Trace phi1 ->
    Det_Trace phi2 ->
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    ~ Conflict_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    H.Equal heapa heapb ->
    (phi1, heapa) ===> (phi1', heap1') ->
    (phi2, heapb) ===> (phi2', heap2') ->
    exists heapA, exists heapB,
      H.Equal heapA heapB /\
      (Phi_Par phi1' phi2, heap1') ===> (Phi_Par phi1' phi2', heapA) /\
      (Phi_Par phi1 phi2', heap2') ===> (Phi_Par phi1' phi2', heapB).
Proof.
  intros  phi1 r l v phi2 r0 l0 v0 phi1' phi2' heapa heapb heap1' heap2'
          H1 H2 Det1 HDet2 HDisj HConf HEqual HStep1 HStep2; subst.
  inversion HStep1; inversion HStep2; subst.
  exists (update_H (r0, l0, v0) (update_H (r, l, v) heapa)). exists (update_H (r, l, v) (update_H (r0, l0, v0) heapb)). repeat split. 
  -  inversion HDisj; subst. simpl in H. 
    assert (Disjoint_Dynamic (DA_Write r l v) (DA_Write r0 l0 v0)) by (apply H; left; reflexivity).
    inversion H1; subst. unfold update_H in *. simpl in *.
    inversion H1; subst. unfold update_H in *. simpl in *. 
    destruct (RegionVars.eq_dec (r, l) (r0, l0)).
    + inversion e. unfold fst, snd in *; subst.
      inversion H1; subst. contradict H5. intuition.
    + clear n. 
      apply HMapP.Equal_mapsto_iff; intros. destruct k.
      destruct (RegionVars.eq_dec (n, n0) (r0, l0)); destruct (RegionVars.eq_dec (n, n0) (r, l)); split.
      * inversion e0; inversion e1. unfold fst, snd in *; subst.
        inversion H1; subst. contradict H5. intuition.
      * inversion e0; inversion e1. unfold fst, snd in *; subst.
        inversion H1; subst. contradict H5. intuition.
      * unfold RegionVars.eq in *. unfold fst, snd in *; subst. destruct e0; subst.
        intro. apply  HMapP.find_mapsto_iff in H2.
        rewrite H_same_key_add_twice_1 in H2. rewrite H_same_key in H2.
        apply HMapP.add_mapsto_iff. right; simpl. split; [ intuition | ].
        apply HMapP.find_mapsto_iff. rewrite H_same_key. assumption.
      * unfold RegionVars.eq in *. unfold fst, snd in *; subst. destruct e0; subst.
        intro. apply  HMapP.find_mapsto_iff in H2. rewrite H_same_key_add_twice_2 in H2.
        { rewrite H_same_key in H2.  apply  HMapP.find_mapsto_iff.
          inversion H2; subst. rewrite H_same_key_add_twice_1. rewrite H_same_key. assumption. }
        { contradict n1. inversion n1. intuition. }
      * unfold RegionVars.eq in *. unfold fst, snd in *; subst. destruct e0; subst.
        intro. apply  HMapP.find_mapsto_iff in H2. rewrite H_same_key_add_twice_2 in H2.
        { apply HMapP.add_mapsto_iff. left. simpl. split; auto.
          rewrite HMapP.add_o in H2. 
          destruct (HMapP.eq_dec (r, l) (r, l)) in H2;
          [inversion H2; subst;  reflexivity |  simpl in n; contradict n; auto]. }
        { contradict n1. inversion n1. intuition. }
      * unfold RegionVars.eq in *. unfold fst, snd in *; subst. destruct e0; subst.
        intro. apply  HMapP.find_mapsto_iff in H2. rewrite H_same_key_add_twice_1 in H2. apply  HMapP.find_mapsto_iff in H2.  
        apply  HMapP.find_mapsto_iff.
        apply H_diff_key_2; [contradict H3; assumption | ].
        apply HMapP.find_mapsto_iff.
        apply HMapP.add_mapsto_iff. left; simpl. split; auto.
        apply HMapP.add_mapsto_iff in H2.
        destruct H2 as [ [ ?  ?] | [? ?] ]; [assumption | contradict H2; intuition]. 
      * unfold RegionVars.eq in *. unfold fst, snd in *; subst.
        intro. apply  HMapP.find_mapsto_iff in H2.
        apply  HMapP.find_mapsto_iff.
        { eapply H_diff_key_add_comm_2.
          - contradict n2. inversion n2. auto.
          - contradict n1. inversion n1. auto.
          - apply H_diff_key_2.
            + contradict n2. inversion n2. auto.
            + unfold H.Equal in HEqual. rewrite <- HEqual.
              apply H_diff_key_1 in H2.
              * apply H_diff_key_1 in H2; [assumption | contradict n2; inversion n2; auto]. 
              * contradict n1; inversion n1; auto.
        }
      * unfold RegionVars.eq in *. unfold fst, snd in *; subst.
        intro. apply  HMapP.find_mapsto_iff in H2.
        apply  HMapP.find_mapsto_iff.
        { eapply H_diff_key_add_comm_2.
          - contradict n1. inversion n1. auto.
          - contradict n2. inversion n2. auto.
          - apply H_diff_key_2.
            + contradict n1. inversion n1. auto.
            +unfold H.Equal in HEqual. rewrite HEqual.
              apply H_diff_key_1 in H2.
              * apply H_diff_key_1 in H2; [assumption | contradict n1; inversion n1; intuition].
              * contradict n1; inversion n1; intuition.
        }        
  - do 2 constructor.
    inversion HDisj; subst. simpl in H. 
    assert (Disjoint_Dynamic (DA_Write r l v) (DA_Write r0 l0 v0)) by (apply H; left; reflexivity).
    inversion H1; subst. apply HMapP.add_neq_in_iff; auto; [simpl; intuition | ].
    apply HMapP.Equal_Equiv in HEqual. inversion HEqual. apply H2. assumption.
  - do 2 constructor.
    inversion HDisj; subst. simpl in H. 
    assert (Disjoint_Dynamic (DA_Write r l v) (DA_Write r0 l0 v0)) by (apply H; left; reflexivity).
    inversion H1; subst. apply HMapP.add_neq_in_iff; auto; [simpl; intuition | ].
    apply HMapP.Equal_Equiv in HEqual. inversion HEqual. apply H2. assumption.
Qed.

Lemma Par_Step_Alloc_Read :
  forall phi1 r l v phi2 r0 l0 v0 phi1' phi2' heapa heapb heap1' heap2',
    phi1 = Phi_Elem (DA_Alloc r l v) ->
    phi2 = Phi_Elem (DA_Read r0 l0 v0) -> 
    Det_Trace phi1 ->
    Det_Trace phi2 ->
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    ~ Conflict_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    H.Equal heapa heapb ->
    (phi1, heapa) ===> (phi1', heap1') ->
    (phi2, heapb) ===> (phi2', heap2') ->
    exists heapA heapB,
      H.Equal heapA heapB /\
      (Phi_Par phi1' phi2, heap1') ===> (Phi_Par phi1' phi2', heapA) /\
      (Phi_Par phi1 phi2', heap2') ===> (Phi_Par phi1' phi2', heapB).
Proof.
  intros  phi1 r l v phi2 r0 l0 v0 phi1' phi2' heapa heapb heap1' heap2'
          H1 H2 Det1 HDet2 HDisj HConf HEqual HStep1 HStep2; subst.
  inversion HStep1; inversion HStep2; subst.
  edestruct Aux_Aux_Step_Ext_Heap as [heapB' [? ?]]; eauto. 
  exists (update_H (r, l, v) heapa); exists heapB'; repeat split.
  - assumption.
  - do 2 constructor.
    inversion HDisj; subst. simpl in H. 
    assert (Disjoint_Dynamic (DA_Alloc r l v) (DA_Read r0 l0 v0)) by (apply H1; left; reflexivity).
    inversion H2; subst. eapply H_diff_key_2; eauto.
    unfold H.Equal in HEqual. rewrite HEqual. assumption.
  - constructor. assumption.
Qed.

Lemma Par_Step_Write_Read :
  forall phi1 r l v phi2 r0 l0 v0 phi1' phi2' heapa heapb heap1' heap2',
    phi1 = Phi_Elem (DA_Write r l v) ->
    phi2 = Phi_Elem (DA_Read r0 l0 v0) -> 
    Det_Trace phi1 ->
    Det_Trace phi2 ->
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    ~ Conflict_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    H.Equal heapa heapb ->
    (phi1, heapa) ===> (phi1', heap1') ->
    (phi2, heapb) ===> (phi2', heap2') ->
    exists heapA heapB,
      H.Equal heapA heapB /\
      (Phi_Par phi1' phi2, heap1') ===> (Phi_Par phi1' phi2', heapA) /\
      (Phi_Par phi1 phi2', heap2') ===> (Phi_Par phi1' phi2', heapB).
Proof.
  intros  phi1 r l v phi2 r0 l0 v0 phi1' phi2' heapa heapb heap1' heap2'
          H1 H2 Det1 HDet2 HDisj HConf HEqual HStep1 HStep2; subst.
  inversion HStep1; inversion HStep2; subst.
  edestruct Aux_Aux_Step_Ext_Heap as [heapB' [? ?]]; eauto. 
  exists (update_H (r, l, v) heapa); exists heapB'; repeat split.
  - assumption.
  - do 2 constructor. 
    inversion HDisj; subst. simpl in H. 
    assert (Disjoint_Dynamic (DA_Write r l v) (DA_Read r0 l0 v0)) by (apply H2; left; reflexivity).
    inversion H3; subst. eapply H_diff_key_2; eauto.
    unfold H.Equal in HEqual. rewrite HEqual. assumption.
  - constructor. assumption.
Qed.

Lemma Par_Step_Read_Alloc :
  forall phi1 r l v phi2 r0 l0 v0 phi1' phi2' heapa heapb heap1' heap2',
    phi1 = Phi_Elem (DA_Read r l v) ->
    phi2 = Phi_Elem (DA_Alloc r0 l0 v0) -> 
    Det_Trace phi1 ->
    Det_Trace phi2 ->
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    ~ Conflict_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    H.Equal heapa heapb ->
    (phi1, heapa) ===> (phi1', heap1') ->
    (phi2, heapb) ===> (phi2', heap2') ->
    exists heapA heapB,
      H.Equal heapA heapB /\
      (Phi_Par phi1' phi2, heap1') ===> (Phi_Par phi1' phi2', heapA) /\
      (Phi_Par phi1 phi2', heap2') ===> (Phi_Par phi1' phi2', heapB).
Proof.
  intros  phi1 r l v phi2 r0 l0 v0 phi1' phi2' heapa heapb heap1' heap2'
          H1 H2 Det1 HDet2 HDisj HConf HEqual HStep1 HStep2; subst.
  inversion HStep1; inversion HStep2; subst. 
  edestruct Aux_Aux_Step_Ext_Heap as [heapB' [? ?]]; eauto.
  apply HMapP.Equal_sym in HEqual. assert (H.Equal heapb heapB') by (eapply HMapP.Equal_trans; eauto).
  exists (update_H (r0, l0, v0) heap1'); exists (update_H (r0, l0, v0) heapb); repeat split.
  - unfold H.Equal; intros [r1 l1]. apply HMapP.Equal_sym in HEqual. unfold H.Equal in HEqual.
    destruct (RegionVars.eq_dec (r1, l1) (r0, l0));  unfold update_H; simpl.
    + inversion e; simpl in *; subst. rewrite H_same_key. rewrite H_same_key. reflexivity.
    + unfold RegionVars.eq in n.  simpl in n.
      rewrite HMapP.add_neq_o.
      * rewrite HMapP.add_neq_o; simpl; [apply HEqual | contradict n; intuition].
      * contradict n; intuition.
  - inversion HDisj; subst. simpl in H. 
    assert (Disjoint_Dynamic (DA_Read r l v) (DA_Alloc r0 l0 v0)) by (apply H3; left; reflexivity).
    inversion H4; subst. constructor. constructor.
  - do 2 constructor. inversion HStep2; subst.
    inversion HDisj; subst. simpl in H. 
    assert (Disjoint_Dynamic (DA_Read r l v) (DA_Alloc r0 l0 v0)) by (apply H3; left; reflexivity).
    inversion H4; subst.
    eapply H_diff_key_2; auto.
    unfold H.Equal in HEqual. rewrite HEqual. assumption.
Qed.

Lemma Par_Step_Read_Write :
  forall phi1 r l v phi2 r0 l0 v0 phi1' phi2' heapa heapb heap1' heap2',
    phi1 = Phi_Elem (DA_Read r l v) ->
    phi2 = Phi_Elem (DA_Write r0 l0 v0) -> 
    Det_Trace phi1 ->
    Det_Trace phi2 ->
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    ~ Conflict_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    H.Equal heapa heapb ->
    (phi1, heapa) ===> (phi1', heap1') ->
    (phi2, heapb) ===> (phi2', heap2') ->
    exists heapA heapB,
      H.Equal heapA heapB /\
      (Phi_Par phi1' phi2, heap1') ===> (Phi_Par phi1' phi2', heapA) /\
      (Phi_Par phi1 phi2', heap2') ===> (Phi_Par phi1' phi2', heapB).
Proof.
  intros  phi1 r l v phi2 r0 l0 v0 phi1' phi2' heapa heapb heap1' heap2'
          H1 H2 Det1 HDet2 HDisj HConf HEqual HStep1 HStep2; subst.
  inversion HStep1; inversion HStep2; subst.
  edestruct Aux_Aux_Step_Ext_Heap as [heapB' [? ?]]; eauto.
  exists (update_H (r0, l0, v0) heap1'); exists (update_H (r0, l0, v0) heapb); repeat split.
  -  unfold H.Equal; intros [r1 l1]. unfold H.Equal in HEqual.
    destruct (RegionVars.eq_dec (r1, l1) (r0, l0));  unfold update_H; simpl.
    + inversion e; simpl in *; subst. rewrite H_same_key. rewrite H_same_key. reflexivity.
    + unfold RegionVars.eq in n.  simpl in n.
      rewrite HMapP.add_neq_o.
      * rewrite HMapP.add_neq_o; simpl; [apply HEqual | contradict n; intuition].
      * contradict n; intuition.
  - inversion HDisj; subst. simpl in H. 
    assert (Disjoint_Dynamic (DA_Read r l v) (DA_Write r0 l0 v0)) by (apply H2; left; reflexivity).
    inversion H3; subst. constructor.  constructor.
    apply HMapP.Equal_sym in HEqual.
    apply HMapP.Equal_Equiv in HEqual. inversion HEqual. now apply HEqual.
  - do 2 constructor. inversion HStep2; subst.
    inversion HDisj; subst. simpl in H. 
    assert (Disjoint_Dynamic (DA_Read r l v) (DA_Write r0 l0 v0)) by (apply H2; left; reflexivity).
    inversion H4; subst.
    eapply H_diff_key_2; auto. unfold H.Equal in HEqual. rewrite <- H0.
    symmetry; apply HEqual.
Qed.

Lemma Par_Step_Alloc_Write :
  forall phi1 r l v phi2 r0 l0 v0 phi1' phi2' heapa heapb heap1' heap2',
    phi1 = Phi_Elem (DA_Alloc r l v) ->
    phi2 = Phi_Elem (DA_Write r0 l0 v0) -> 
    Det_Trace phi1 ->
    Det_Trace phi2 ->
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    ~ Conflict_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    H.Equal heapa heapb ->
    (phi1, heapa) ===> (phi1', heap1') ->
    (phi2, heapb) ===> (phi2', heap2') ->
    exists heapA heapB,
      H.Equal heapA heapB /\
      (Phi_Par phi1' phi2, heap1') ===> (Phi_Par phi1' phi2', heapA) /\
      (Phi_Par phi1 phi2', heap2') ===> (Phi_Par phi1' phi2', heapB).
Proof.
  intros  phi1 r l v phi2 r0 l0 v0 phi1' phi2' heapa heapb heap1' heap2'
          H1 H2 Det1 HDet2 HDisj HConf HEqual HStep1 HStep2; subst.
  inversion HStep1; inversion HStep2; subst. 
  exists (update_H (r0, l0, v0) (update_H (r, l, v) heapa)). exists (update_H (r, l, v) (update_H (r0, l0, v0) heapb)). repeat split.
  - inversion HDisj; subst. 
    assert (Disjoint_Dynamic (DA_Alloc r l v) (DA_Write r0 l0 v0)) by (apply H; left; reflexivity).
    inversion H0; subst. unfold update_H in *. simpl in *. 
    destruct (RegionVars.eq_dec (r, l) (r0, l0)).
    + inversion e. unfold fst, snd in *; subst.
      contradict H2. intuition.
    + clear n. 
      apply HMapP.Equal_mapsto_iff; intros. destruct k.
      destruct (RegionVars.eq_dec (n, n0) (r0, l0)); destruct (RegionVars.eq_dec (n, n0) (r, l)); split.
      * inversion e0; inversion e1. unfold fst, snd in *; do 2 subst. 
        contradict H2. intuition.
      * inversion e0; inversion e1. unfold fst, snd in *; do 2subst.
        contradict H2. intuition.
      * unfold RegionVars.eq in *. unfold fst, snd in *; subst. destruct e0; subst.
        intro. apply  HMapP.find_mapsto_iff in H1.
        rewrite H_same_key_add_twice_1 in H1. rewrite H_same_key in H1.
        apply HMapP.add_mapsto_iff. right. intuition. inversion H1; subst.
        apply HMapP.find_mapsto_iff. apply H_same_key.
      * unfold RegionVars.eq in *. unfold fst, snd in *; subst. destruct e0; subst.
        intro. apply  HMapP.find_mapsto_iff in H1. rewrite H_same_key_add_twice_2 in H1.
        rewrite H_same_key in H1.
        apply HMapP.find_mapsto_iff. inversion H1. rewrite <- H4.
        apply H_same_key. assumption.
      * unfold RegionVars.eq in *. unfold fst, snd in *; subst. destruct e0; subst.
        intro. apply  HMapP.find_mapsto_iff in H1. rewrite H_same_key_add_twice_2 in H1.
        { apply HMapP.add_mapsto_iff. left; simpl. split; auto.
          rewrite HMapP.add_o in H1. 
          destruct (HMapP.eq_dec (r, l) (r, l)) in H1; [inversion H1; subst |  simpl in n; contradict n; auto].
          reflexivity.
        }
        { contradict n1. inversion n1. intuition. }
      * unfold RegionVars.eq in *. unfold fst, snd in *; subst. destruct e0; subst.
        intro. apply  HMapP.find_mapsto_iff in H1. rewrite H_same_key_add_twice_1 in H1. 
        apply  HMapP.find_mapsto_iff in H1.  
        apply  HMapP.find_mapsto_iff. 
        apply H_diff_key_2; [ contradict H2; auto | ].
        apply HMapP.find_mapsto_iff.
        apply HMapP.add_mapsto_iff. left; simpl. split; auto.
        apply HMapP.add_mapsto_iff in H1.
        destruct H1 as [ [ ?  ?] | [? ?] ]; [assumption | contradict H2; intuition]. 
      * unfold RegionVars.eq in *. unfold fst, snd in *; subst.
        intro. apply  HMapP.find_mapsto_iff in H1.
        apply  HMapP.find_mapsto_iff.
        { eapply H_diff_key_add_comm_2. 
          - contradict n1. inversion n1. intuition.
          - contradict n2. inversion n2. intuition.
          - apply H_diff_key_2.
            + contradict n1. inversion n1. intuition.
            + unfold H.Equal in HEqual. rewrite <- HEqual.
              apply H_diff_key_1 in H1.
              * apply H_diff_key_1 in H1; [assumption | contradict n2; inversion n2; auto]. 
              * contradict n1; inversion n1; auto.
        }
      * unfold RegionVars.eq in *. unfold fst, snd in *; subst.
        intro. apply  HMapP.find_mapsto_iff in H1.
        apply  HMapP.find_mapsto_iff.
        { eapply H_diff_key_add_comm_2.
          - contradict n1. inversion n1. auto.
          - contradict n2. inversion n2. auto.
          - apply H_diff_key_2.
            + contradict n1. inversion n1. auto.
            +unfold H.Equal in HEqual. rewrite HEqual.
              apply H_diff_key_1 in H1.
              * apply H_diff_key_1 in H1; [assumption | contradict n1; inversion n1; intuition].
              * contradict n1; inversion n1; intuition.
        }  
  - inversion HDisj; subst.
    assert (Disjoint_Dynamic (DA_Alloc r l v) (DA_Write r0 l0 v0)) by (apply H; left; reflexivity).
    inversion H0; subst. unfold update_H in *. simpl in *. 
    constructor. constructor.
    apply HMapP.Equal_sym in HEqual. apply HMapP.Equal_Equiv in HEqual. inversion HEqual.
    apply HEqual in H6. apply HMapP.add_neq_in_iff; intuition.
  - inversion HDisj; subst. simpl in H. constructor. constructor.
Qed.    

Lemma Par_Step_Write_Alloc :
  forall phi1 r l v phi2 r0 l0 v0 phi1' phi2' heapa heapb heap1' heap2',
    phi1 = Phi_Elem (DA_Write r l v) ->
    phi2 = Phi_Elem (DA_Alloc r0 l0 v0) -> 
    Det_Trace phi1 ->
    Det_Trace phi2 ->
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    ~ Conflict_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    H.Equal heapa heapb ->
    (phi1, heapa) ===> (phi1', heap1') ->
    (phi2, heapb) ===> (phi2', heap2') ->
    exists heapA heapB,
      H.Equal heapA heapB /\
      (Phi_Par phi1' phi2, heap1') ===> (Phi_Par phi1' phi2', heapA) /\
      (Phi_Par phi1 phi2', heap2') ===> (Phi_Par phi1' phi2', heapB).
Proof.
  intros  phi1 r l v phi2 r0 l0 v0 phi1' phi2' heapa heapb heap1' heap2'
          H1 H2 Det1 HDet2 HDisj HConf HEqual HStep1 HStep2; subst.
  inversion HStep1; inversion HStep2; subst. 
  exists (update_H (r0, l0, v0) (update_H (r, l, v) heapa)). exists (update_H (r, l, v) (update_H (r0, l0, v0) heapb)). repeat split.
  - inversion HDisj; subst. 
    assert (Disjoint_Dynamic (DA_Write r l v) (DA_Alloc r0 l0 v0)) by (apply H; left; reflexivity).
    inversion H1; subst. unfold update_H in *. simpl in *. 
    destruct (RegionVars.eq_dec (r, l) (r0, l0)).
    + inversion e. simpl in *. subst. contradict H3. reflexivity.
    + clear n. 
      apply HMapP.Equal_mapsto_iff; intros. destruct k. 
      destruct (RegionVars.eq_dec (n, n0) (r0, l0)); destruct (RegionVars.eq_dec (n, n0) (r, l)); split.
      * inversion e0; inversion e1.  unfold fst, snd in *; subst. rewrite H6 in *. rewrite H5 in *.
        inversion H1; subst. contradict H4. intuition.
      * inversion e0; inversion e1. unfold fst, snd in *; subst. rewrite H6 in H1. rewrite H5 in H1.
        inversion H1; subst. contradict H4. intuition.
      * unfold RegionVars.eq in *. unfold fst, snd in *; subst. destruct e0; subst.
        intro. apply  HMapP.find_mapsto_iff in H2. rewrite H_same_key_add_twice_1 in H2. rewrite H_same_key in H2.
        apply HMapP.add_mapsto_iff. right; simpl. split; [ intuition | ].
        apply HMapP.find_mapsto_iff. rewrite H_same_key. assumption.
      * unfold RegionVars.eq in *. unfold fst, snd in *; subst. destruct e0; subst.
        intro. apply  HMapP.find_mapsto_iff in H2. rewrite H_same_key_add_twice_2 in H2.
        { rewrite H_same_key in H2.  apply  HMapP.find_mapsto_iff.
          inversion H2; subst. rewrite H_same_key_add_twice_1. rewrite H_same_key. assumption. }
        { contradict n1. inversion n1. intuition. }
      * unfold RegionVars.eq in *. unfold fst, snd in *; subst. destruct e0; subst.
        intro. apply  HMapP.find_mapsto_iff in H2. rewrite H_same_key_add_twice_2 in H2. 
        { apply HMapP.add_mapsto_iff. left; simpl. split; auto.
          rewrite HMapP.add_o in H2. 
          destruct (HMapP.eq_dec (r, l) (r, l)) in H2; [inversion H2; subst |  simpl in n; contradict n; auto].
          reflexivity.
        }
        { contradict n1. inversion n1. intuition. }
      * unfold RegionVars.eq in *. unfold fst, snd in *; subst. destruct e0; subst.
        intro. apply  HMapP.find_mapsto_iff in H2. rewrite H_same_key_add_twice_1 in H2. 
        apply  HMapP.find_mapsto_iff in H2.  
        apply  HMapP.find_mapsto_iff. 
        apply H_diff_key_2; [ contradict H2; auto | ].
        apply HMapP.find_mapsto_iff.
        apply HMapP.add_mapsto_iff. left; simpl. split; auto.
        apply HMapP.add_mapsto_iff in H2.
        destruct H2 as [ [ ?  ?] | [? ?] ]; [assumption | contradict H2; intuition]. 
      * unfold RegionVars.eq in *. unfold fst, snd in *; subst.
        intro. apply  HMapP.find_mapsto_iff in H2.
        apply  HMapP.find_mapsto_iff.
        { eapply H_diff_key_add_comm_2.
          - contradict n2. inversion n2. auto.
          - contradict n1. inversion n1. auto.
          - apply H_diff_key_2.
            + contradict n1. inversion n1. intuition.
            + unfold H.Equal in HEqual. rewrite <- HEqual.
              apply H_diff_key_1 in H2.
              * apply H_diff_key_1 in H2; [assumption | contradict n2; inversion n2; auto]. 
              * contradict n1; inversion n1; auto.
        }
      * unfold RegionVars.eq in *. unfold fst, snd in *; subst.
        intro. apply  HMapP.find_mapsto_iff in H2.
        apply  HMapP.find_mapsto_iff.
        { eapply H_diff_key_add_comm_2.
          - contradict n1. inversion n1. auto.
          - contradict n2. inversion n2. auto.
          - apply H_diff_key_2.
            + contradict n1. inversion n1. auto.
            +unfold H.Equal in HEqual. rewrite HEqual.
              apply H_diff_key_1 in H2.
              * apply H_diff_key_1 in H2; [assumption | contradict n1; inversion n1; intuition].
              * contradict n1; inversion n1; intuition.
        }
  - inversion HDisj; subst. 
    assert (Disjoint_Dynamic (DA_Write r l v)  (DA_Alloc r0 l0 v0)) by (apply H; left; reflexivity).
    inversion H1; subst. unfold update_H in *. simpl in *.
    constructor. constructor.
  - constructor. constructor.
    inversion HDisj; subst. 
    assert (Disjoint_Dynamic (DA_Write r l v)  (DA_Alloc r0 l0 v0)) by (apply H; left; reflexivity).
    inversion H1; subst. unfold update_H in *. simpl in *.
    apply HMapP.Equal_sym in HEqual. apply HMapP.Equal_Equiv in HEqual. inversion HEqual.
    apply HEqual in H0. apply HMapP.add_neq_in_iff; intuition.
Qed.    
    
Lemma Phi_Heap_Step_Progress :
  forall phi heap heap',
    (phi, heap) ===> (phi, heap') ->
    False.
Proof.
  induction phi; intros heap heap' HStep.
  + inversion HStep.
  + inversion HStep.
  + inversion HStep; subst.
    - eapply IHphi1; eassumption.
    - eapply IHphi2; eassumption.
  + inversion HStep; subst.
    - eapply IHphi1; eassumption.
    - eapply IHphi2; eassumption.
Qed.


Lemma Par_Step_Equal :
   forall phi1 phi2 phi1' phi2' heap0 heap1' heap2',
    Det_Trace phi1 ->
    Det_Trace phi2 ->
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    ~ Conflict_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    (phi1, heap0) ===> (phi1', heap1') ->
    (phi2, heap0) ===> (phi2', heap2') ->
    exists heapA, exists heapB,
      H.Equal heapA heapB /\
      (Phi_Par phi1' phi2, heap1') ===> (Phi_Par phi1' phi2', heapA) /\
      (Phi_Par phi1 phi2', heap2') ===> (Phi_Par phi1' phi2', heapB).
Proof.
  intros phi1 phi2 phi1' phi2' heap0 heap1' heap2' HDet1 HDet2 HDisj HConf HStep1 HStep2.
  generalize dependent phi2.
  dependent induction HStep1; intros.
  - dependent destruction HStep2. 
    + eapply Par_Step_Alloc_Alloc; eauto || econstructor.
    + eapply Par_Step_Alloc_Read; eauto  || econstructor; assumption.
    + eapply Par_Step_Alloc_Write; eauto || econstructor; assumption.
    + replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
        in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj. destruct HDisj.
      eapply Disjointness_Preserves_Update_Alloc in HStep2; eauto.
      destruct HStep2 as [? [? ?]].
      { exists x. exists (update_H (r, l, v) heap2'); repeat split.
        - assumption.
        - do 2 constructor; assumption.
        - do 2 constructor. }
    + replace (phi_as_list (Phi_Seq Phi_Nil phi0)) with (phi_as_list Phi_Nil ++ phi_as_list phi0)
        in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj. destruct HDisj.
      eapply Disjointness_Preserves_Update_Alloc in HStep2; eauto.
      destruct HStep2 as [? [? ?]].
      { exists x. exists (update_H (r, l, v) heap2'); repeat split.
        - assumption.
        - do 2 constructor; assumption.
        - do 2 constructor. }
    + { exists (update_H (r, l, v) heap2'). exists (update_H (r, l, v) heap2'); repeat split; do 2  constructor. }
    + replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
        in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj. destruct HDisj.
      eapply Disjointness_Preserves_Update_Alloc in HStep2; eauto.
      destruct HStep2 as [? [? ?]].
      { exists x. exists (update_H (r, l, v) heap2'); repeat split.
        - assumption.
        - do 2 constructor; assumption.
        - do 2 constructor.   }
    + replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
        in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj. destruct HDisj.
      eapply Disjointness_Preserves_Update_Alloc in HStep2; eauto.
      destruct HStep2 as [? [? ?]].
      { exists x. exists  (update_H (r, l, v) heap2'); repeat split.
        - assumption.
        - do 2 constructor; assumption.
        - do 2 constructor.  }            
    + { exists (update_H (r, l, v) heap2'). exists (update_H (r, l, v) heap2'); repeat split; do 2  constructor. }
  - dependent destruction HStep2. 
    + eapply Par_Step_Read_Alloc; eauto || econstructor; assumption.
    + { exists heap2'. exists heap2'; repeat split; do 2 constructor; assumption. }
    + eapply Par_Step_Read_Write; eauto || econstructor; assumption.
    + { exists heap2'. exists heap2'. repeat split.
        - do 2 constructor; assumption.
        - do 2 constructor.
          replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
            in HDisj by (simpl; reflexivity).
          apply Disjointness_app_app_and_l in HDisj. destruct HDisj as [HD1 ?].
          replace (phi_as_list (Phi_Elem (DA_Read r l v))) with (DA_Read r l v :: nil)
            in HD1 by (simpl; reflexivity).
          eapply Read_Preserved.
          eapply H.
          eapply HD1.
          eapply HStep2. }
    + { exists heap2'. exists heap2'. repeat split.
        - do 2 constructor; assumption.
        - do 2 constructor.
          replace (phi_as_list (Phi_Seq Phi_Nil phi0)) with (phi_as_list Phi_Nil ++ phi_as_list phi0)
            in HDisj by (simpl; reflexivity).
          apply Disjointness_app_app_and_l in HDisj. destruct HDisj as [? HD1].
          replace (phi_as_list (Phi_Elem (DA_Read r l v))) with (DA_Read r l v :: nil)
            in HD1 by (simpl; reflexivity).
          eapply Read_Preserved.
          eapply H.
          eapply HD1.
          eapply HStep2. }
    + exists heap2'. exists heap2'. repeat split; do 2 constructor. assumption.
    + { exists heap2'. exists heap2'. repeat split.
        - do 2 constructor; assumption.
        - do 2 constructor.
          replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
            in HDisj by (simpl; reflexivity).
          apply Disjointness_app_app_and_l in HDisj. destruct HDisj as [HD1 ?].
          replace (phi_as_list (Phi_Elem (DA_Read r l v))) with (DA_Read r l v :: nil)
            in HD1 by (simpl; reflexivity).
          eapply Read_Preserved.
          eapply H.
          eapply HD1.
          eapply HStep2. }
    + { exists heap2'. exists heap2'. repeat split.
        - do 2 constructor; assumption.
        - do 2 constructor.
          replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
            in HDisj by (simpl; reflexivity).
          apply Disjointness_app_app_and_l in HDisj. destruct HDisj as [? HD1].
          replace (phi_as_list (Phi_Elem (DA_Read r l v))) with (DA_Read r l v :: nil)
            in HD1 by (simpl; reflexivity).
          eapply Read_Preserved.
          eapply H.
          eapply HD1.
          eapply HStep2. }
    + { exists heap2'. exists heap2'. repeat split; do 2 constructor. assumption. }
  - dependent destruction HStep2. 
    + eapply Par_Step_Write_Alloc; eauto || econstructor; assumption.
    + eapply Par_Step_Write_Read; eauto || econstructor; assumption.
    + eapply Par_Step_Write_Write; eauto || econstructor; assumption.
    + eapply monotonic_heap_updates in H; eauto.
      replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
        in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj. destruct HDisj.
      eapply Disjointness_Preserves_Update_Write in HStep2; eauto.
      destruct HStep2 as [? [? ?]].   
      { exists x. exists (update_H (r, l, v) heap2'); repeat split.
        - assumption.
        - do 2 constructor. assumption.
        - constructor. constructor. assumption.
      }
    + eapply monotonic_heap_updates in H; eauto.
      replace (phi_as_list (Phi_Seq Phi_Nil phi0)) with (phi_as_list Phi_Nil ++ phi_as_list phi0)
        in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj. destruct HDisj.
      eapply Disjointness_Preserves_Update_Write in HStep2; eauto.
      destruct HStep2 as [? [? ?]].
      { exists x.  exists (update_H (r, l, v) heap2'); repeat split.
        - assumption.
        - do 2 constructor; assumption.
        - constructor. constructor. assumption. }
    + { exists (update_H (r, l, v) heap2'). exists (update_H (r, l, v) heap2'); repeat split; do 2  constructor; assumption. }
    + eapply monotonic_heap_updates in H; eauto.
      replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
        in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj. destruct HDisj.
      eapply Disjointness_Preserves_Update_Write in HStep2; eauto.
      destruct HStep2 as [? [? ?]].
      { exists x. exists (update_H (r, l, v) heap2'); repeat split.
        - assumption.
        - do 2 constructor; assumption.
        - constructor. constructor. assumption. }
    + eapply monotonic_heap_updates in H; eauto.
      replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
        in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj. destruct HDisj.
      eapply Disjointness_Preserves_Update_Write in HStep2; eauto.
      destruct HStep2 as [? [? ?]].
      { exists x. exists (update_H (r, l, v) heap2'); repeat split.
        - assumption.
        - do 2 constructor; assumption.
        - constructor. constructor. assumption.  }            
    + { exists (update_H (r, l, v) heap2'). exists (update_H (r, l, v) heap2'); repeat split; do 2  constructor; assumption. }
  - inversion HDet1; subst. 
    edestruct (IHHStep1 H1 phi1 HDet2) as [heapA [heapB [? [? ?]]]].
    + simpl in HDisj. apply Disjointness_app_app_and_r in HDisj. destruct HDisj. assumption.
    + simpl in HConf. inversion HDet1.
      apply Conflictness_app_and_r in HConf; [ destruct HConf  | | | ]; assumption.
    + assumption.
    + exists heapA. exists heapB. repeat split.
      * assumption.
      * inversion H0; subst.
        { apply Phi_Heap_Step_Progress in HStep2. contradiction. }
        { constructor. assumption. }
      * inversion H3; subst.
        { constructor. constructor. assumption. }
        { apply Phi_Heap_Step_Progress in H3. contradiction. }
  - inversion HDet1; subst.
    edestruct (IHHStep1 H2 phi0 HDet2) as [heapA [heapB [? [? ?]]]].
    + simpl in HDisj. assumption.
    + simpl in HConf. assumption.
    + assumption.
    + exists heapA. exists heapB. repeat split.
      * assumption.
      * inversion H0; subst.
        { apply Phi_Heap_Step_Progress in HStep2. contradiction. }
        { constructor. assumption. }
      * inversion H3; subst.
        { constructor. constructor. assumption. }
        { apply Phi_Heap_Step_Progress in H3. contradiction. }
  - exists heap2'. exists heap2'. repeat split.
     * constructor; assumption.
     * constructor; constructor.
  - inversion HDet1; subst.
    edestruct (IHHStep1 H1 phi1 HDet2) as [heapA [heapB [? [? ?]]]].
    + simpl in HDisj. apply Disjointness_app_app_and_r in HDisj. destruct HDisj. assumption.
    + simpl in HConf. inversion HDet1.
      apply Conflictness_app_and_r in HConf; [ destruct HConf  | | | ]; assumption.
    + assumption.
    + exists heapA. exists heapB. repeat split.
      * assumption.
      * inversion H0; subst.
        { apply Phi_Heap_Step_Progress in HStep2. contradiction. }
        { constructor. assumption. }
      * inversion H4; subst.
        { constructor. constructor. assumption. }
        { apply Phi_Heap_Step_Progress in H4. contradiction. }
  - inversion HDet1; subst.
    edestruct (IHHStep1 H2 phi1 HDet2) as [heapA [heapB [? [? ?]]]].
    + simpl in HDisj. apply Disjointness_app_app_and_r in HDisj. destruct HDisj. assumption.
    + simpl in HConf. inversion HDet1.
      apply Conflictness_app_and_r in HConf; [ destruct HConf  | | | ]; assumption.
    + assumption.
    + exists heapA. exists heapB. repeat split.
      * assumption.
      * inversion H0; subst.
        { apply Phi_Heap_Step_Progress in HStep2. contradiction. }
        { constructor. assumption. }
      * inversion H4; subst.
        { constructor. constructor. assumption. }
        { apply Phi_Heap_Step_Progress in H4. contradiction. }
  - exists heap2'. exists heap2'. repeat split.
     * constructor; assumption.
     * constructor; constructor.
Qed.

Lemma Par_Step_Equal_new :
   forall phi1 phi2 phi1' phi2' heapa heapb heap1' heap2',
    Det_Trace phi1 ->
    Det_Trace phi2 ->
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    ~ Conflict_Traces (phi_as_list phi1) (phi_as_list phi2) ->
    H.Equal heapa heapb ->
    (phi1, heapa) ===> (phi1', heap1') ->
    (phi2, heapb) ===> (phi2', heap2') ->
    exists heapA, exists heapB,
      H.Equal heapA heapB /\
      (Phi_Par phi1' phi2, heap1') ===> (Phi_Par phi1' phi2', heapA) /\
      (Phi_Par phi1 phi2', heap2') ===> (Phi_Par phi1' phi2', heapB).
Proof.
  intros phi1 phi2 phi1' phi2' heapa heapb heap1' heap2' HDet1 HDet2 HDisj HConf HEqual HStep1 HStep2.
  generalize dependent phi2.
  dependent induction HStep1; intros.
  - dependent destruction HStep2.  
    + eapply Par_Step_Alloc_Alloc; eauto || econstructor.
    + eapply Par_Step_Alloc_Read; eauto  || econstructor; assumption.
    + eapply Par_Step_Alloc_Write; eauto || econstructor; assumption.
    + apply HMapP.Equal_sym in HEqual. 
      edestruct (Aux_Aux_Step_Ext_Heap _ _ _ _ _ HStep2 HEqual)
       as [heap2'' [HEqual' HStep2']]. clear HStep2.
      replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
        in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj. destruct HDisj.
      eapply Disjointness_Preserves_Update_Alloc in HStep2'; eauto.  
      destruct HStep2' as [heapa' [? ?]]. 
      { exists heapa'. exists (update_H (r, l, v) heap2'); repeat split. 
        - unfold H.Equal in *; unfold update_H in *; simpl in *.
          intros [r' l'].
          destruct (RegionVars.eq_dec (r', l') (r, l)).
          * inversion_clear e; simpl in *; subst.
            rewrite H1. do 2 rewrite H_same_key. reflexivity.
          * unfold RegionVars.eq in *; simpl in *.
            rewrite HMapP.add_neq_o. 
            { rewrite H1. rewrite HEqual'. rewrite HMapP.add_neq_o; [reflexivity | contradict n; intuition]. }
            { simpl. contradict n. intuition. } 
        - do 2 constructor. assumption.
        - do 2 constructor. }
    + apply HMapP.Equal_sym in HEqual.
      edestruct (Aux_Aux_Step_Ext_Heap _ _ _ _ _ HStep2 HEqual)
       as [heap2'' [HEqual' HStep2']]. clear HStep2.
      replace (phi_as_list (Phi_Seq Phi_Nil phi0)) with (phi_as_list Phi_Nil ++ phi_as_list phi0)
        in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj. destruct HDisj.
      eapply Disjointness_Preserves_Update_Alloc in HStep2'; eauto.
      destruct HStep2' as [? [? ?]].
      { exists x. exists (update_H (r, l, v) heap2'); repeat split.
        - unfold H.Equal in *; unfold update_H in *; simpl in *.
          intros [r' l'].
          destruct (RegionVars.eq_dec (r', l') (r, l)).
          * inversion_clear e; simpl in *; subst.
            rewrite H1. do 2 rewrite H_same_key. reflexivity.
          * unfold RegionVars.eq in *; simpl in *.
            rewrite HMapP.add_neq_o. 
            { rewrite H1. rewrite HEqual'. rewrite HMapP.add_neq_o; [reflexivity | contradict n; intuition]. }
            { simpl. contradict n. intuition. } 
        - do 2 constructor; assumption.
        - do 2 constructor. }
    + { exists (update_H (r, l, v) heapa). exists (update_H (r, l, v) heap2'); repeat split.
        - unfold H.Equal in *; unfold update_H in *; simpl in *.
          intros [r' l']. 
          destruct (RegionVars.eq_dec (r', l') (r, l)).
          * inversion_clear e; simpl in *; subst.
            do 2 rewrite H_same_key. reflexivity.
          * unfold RegionVars.eq in *; simpl in *.
            rewrite HMapP.add_neq_o. 
            { rewrite HEqual. rewrite HMapP.add_neq_o; [reflexivity | contradict n; intuition]. }
            { simpl. contradict n. intuition. } 
        - do 2  constructor.
        - do 2 constructor. }
    + apply HMapP.Equal_sym in HEqual.
      edestruct (Aux_Aux_Step_Ext_Heap _ _ _ _ _ HStep2 HEqual)
        as [heap2'' [HEqual' HStep2']]. clear HStep2.
      replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
        in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj. destruct HDisj.
      eapply Disjointness_Preserves_Update_Alloc in HStep2'; eauto.
      destruct HStep2' as [? [? ?]].
      { exists x. exists (update_H (r, l, v) heap2'); repeat split.
        - unfold H.Equal in *; unfold update_H in *; simpl in *.
          intros [r' l'].
          destruct (RegionVars.eq_dec (r', l') (r, l)).
          * inversion_clear e; simpl in *; subst.
            rewrite H1. do 2 rewrite H_same_key. reflexivity.
          * unfold RegionVars.eq in *; simpl in *.
            rewrite HMapP.add_neq_o. 
            { rewrite H1. rewrite HEqual'. rewrite HMapP.add_neq_o; [reflexivity | contradict n; intuition]. }
            { simpl. contradict n. intuition. } 
        - do 2 constructor; assumption.
        - do 2 constructor.   }
    + apply HMapP.Equal_sym in HEqual.
      edestruct (Aux_Aux_Step_Ext_Heap _ _ _ _ _ HStep2 HEqual)
        as [heap2'' [HEqual' HStep2']]. clear HStep2.
      replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
        in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj. destruct HDisj.
      eapply Disjointness_Preserves_Update_Alloc in HStep2'; eauto.
      destruct HStep2' as [? [? ?]].
      { exists x. exists  (update_H (r, l, v) heap2'); repeat split.
        -  unfold H.Equal in *; unfold update_H in *; simpl in *.
          intros [r' l'].
          destruct (RegionVars.eq_dec (r', l') (r, l)).
          * inversion_clear e; simpl in *; subst.
            rewrite H1. do 2 rewrite H_same_key. reflexivity.
          * unfold RegionVars.eq in *; simpl in *.
            rewrite HMapP.add_neq_o. 
            { rewrite H1. rewrite HEqual'. rewrite HMapP.add_neq_o; [reflexivity | contradict n; intuition]. }
            { simpl. contradict n. intuition. } 
        - do 2 constructor; assumption.
        - do 2 constructor.  }            
    + { exists (update_H (r, l, v) heapa). exists (update_H (r, l, v) heap2'); repeat split; try (do 2  constructor). 
        unfold H.Equal in *; unfold update_H in *; simpl in *.
          intros [r' l']. 
          destruct (RegionVars.eq_dec (r', l') (r, l)).
          * inversion_clear e; simpl in *; subst.
            do 2 rewrite H_same_key. reflexivity.
          * unfold RegionVars.eq in *; simpl in *.
            rewrite HMapP.add_neq_o. 
            { rewrite HEqual. rewrite HMapP.add_neq_o; [reflexivity | contradict n; intuition]. }
            { simpl. contradict n. intuition. }
       }  
  - dependent destruction HStep2. 
    + eapply Par_Step_Read_Alloc; eauto || econstructor; assumption.
    + { exists heap1'; exists heap2'; repeat split.
        - assumption.
        - constructor. constructor. unfold H.Equal in HEqual. rewrite <- H0. apply HEqual.
        - constructor. constructor. unfold H.Equal in HEqual. rewrite <- HEqual. assumption.
      }
    + eapply Par_Step_Read_Write; eauto || econstructor; assumption.
    + { apply HMapP.Equal_sym in HEqual.
        edestruct (Aux_Aux_Step_Ext_Heap _ _ _ _ _ HStep2 HEqual)
        as [heap2'' [HEqual' HStep2']].
        exists heap2''. exists heap2'. repeat split.
        - apply HMapP.Equal_sym. assumption.
        - do 2 constructor. assumption.
        - do 2 constructor. 
          replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
            in HDisj by (simpl; reflexivity).
          apply Disjointness_app_app_and_l in HDisj. destruct HDisj as [HD1 ?].
          replace (phi_as_list (Phi_Elem (DA_Read r l v))) with (DA_Read r l v :: nil)
            in HD1 by (simpl; reflexivity).
          unfold H.Equal in HEqual'. rewrite HEqual'.
          eapply Read_Preserved.
          eapply H.
          eapply HD1.
          eapply HStep2'. }
    + { apply HMapP.Equal_sym in HEqual.
        edestruct (Aux_Aux_Step_Ext_Heap _ _ _ _ _ HStep2 HEqual)
          as [heap2'' [HEqual' HStep2']]. clear HStep2.
        exists heap2''. exists heap2'. repeat split.
        - apply HMapP.Equal_sym. assumption.
        - do 2 constructor; assumption.
        - do 2 constructor.
          replace (phi_as_list (Phi_Seq Phi_Nil phi0)) with (phi_as_list Phi_Nil ++ phi_as_list phi0)
            in HDisj by (simpl; reflexivity).
          apply Disjointness_app_app_and_l in HDisj. destruct HDisj as [? HD1].
          replace (phi_as_list (Phi_Elem (DA_Read r l v))) with (DA_Read r l v :: nil)
            in HD1 by (simpl; reflexivity).
          unfold H.Equal in HEqual'. rewrite HEqual'. eapply Read_Preserved.
          eapply H.
          eapply HD1.
          eapply HStep2'. }
    + { exists heap1'. exists heap2'. repeat split; auto.
        - do 2 constructor.
        - do 2 constructor.
          rewrite <- H. unfold H.Equal in HEqual. symmetry; apply HEqual.
      }
    + { apply HMapP.Equal_sym in HEqual.
        edestruct (Aux_Aux_Step_Ext_Heap _ _ _ _ _ HStep2 HEqual)
           as [heap2'' [HEqual' HStep2']]. clear HStep2.
        exists heap2''. exists heap2'. repeat split.
        - apply HMapP.Equal_sym. assumption.
        - do 2 constructor; assumption.
        - do 2 constructor.
          replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
            in HDisj by (simpl; reflexivity).
          apply Disjointness_app_app_and_l in HDisj. destruct HDisj as [HD1 ?].
          replace (phi_as_list (Phi_Elem (DA_Read r l v))) with (DA_Read r l v :: nil)
            in HD1 by (simpl; reflexivity).
          unfold H.Equal in HEqual'. rewrite HEqual'.  eapply Read_Preserved.
          eapply H.
          eapply HD1.
          eapply HStep2' . }
    + { apply HMapP.Equal_sym in HEqual.
        edestruct (Aux_Aux_Step_Ext_Heap _ _ _ _ _ HStep2 HEqual)
          as [heap2'' [HEqual' HStep2']]. clear HStep2.
        exists heap2''. exists heap2'. repeat split.
        - apply HMapP.Equal_sym. assumption.
        - do 2 constructor; assumption.
        - do 2 constructor.
          replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
            in HDisj by (simpl; reflexivity).
          apply Disjointness_app_app_and_l in HDisj. destruct HDisj as [? HD1].
          replace (phi_as_list (Phi_Elem (DA_Read r l v))) with (DA_Read r l v :: nil)
            in HD1 by (simpl; reflexivity).
          unfold H.Equal in HEqual'. rewrite HEqual'. eapply Read_Preserved.
          eapply H.
          eapply HD1.
          eapply HStep2'. }
    + { exists heap1'. exists heap2'. repeat split; auto.
        - do 2 constructor.
        - do 2 constructor.
          rewrite <- H. unfold H.Equal in HEqual. symmetry; apply HEqual.
      }
  - dependent destruction HStep2. 
    + eapply Par_Step_Write_Alloc; eauto || econstructor; assumption.
    + eapply Par_Step_Write_Read; eauto || econstructor; assumption.
    + eapply Par_Step_Write_Write; eauto || econstructor; assumption.
    + apply HMapP.Equal_sym in HEqual.
      edestruct (Aux_Aux_Step_Ext_Heap _ _ _ _ _ HStep2 HEqual)
        as [heap2'' [HEqual' HStep2']]. clear HStep2.
      eapply monotonic_heap_updates in H; eauto.
      replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
        in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj. destruct HDisj.
      eapply Disjointness_Preserves_Update_Write in HStep2'; eauto.
      destruct HStep2' as [? [? ?]].   
      { exists x. exists (update_H (r, l, v) heap2'); repeat split.
        -  unfold H.Equal in *; unfold update_H in *; simpl in *.
          intros [r' l'].
          destruct (RegionVars.eq_dec (r', l') (r, l)).
          * inversion_clear e; simpl in *; subst.
            rewrite H2. do 2 rewrite H_same_key. reflexivity.
          * unfold RegionVars.eq in *; simpl in *.
            rewrite HMapP.add_neq_o. 
            { rewrite H2. rewrite HEqual'. rewrite HMapP.add_neq_o; [reflexivity | contradict n; intuition]. }
            { simpl. contradict n. intuition. } 
        - do 2 constructor. assumption.
        - constructor. constructor.  apply HMapP.Equal_Equiv in HEqual'. inversion HEqual'. apply H4. assumption. 
      }
    + apply HMapP.Equal_sym in HEqual.
      edestruct (Aux_Aux_Step_Ext_Heap _ _ _ _ _ HStep2 HEqual)
         as [heap2'' [HEqual' HStep2']]. clear HStep2.
      eapply monotonic_heap_updates in H; eauto.
      replace (phi_as_list (Phi_Seq Phi_Nil phi0)) with (phi_as_list Phi_Nil ++ phi_as_list phi0)
        in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj. destruct HDisj.
      eapply Disjointness_Preserves_Update_Write in HStep2'; eauto.
      destruct HStep2' as [? [? ?]].
      { exists x.  exists (update_H (r, l, v) heap2'); repeat split.
        -  unfold H.Equal in *; unfold update_H in *; simpl in *.
          intros [r' l'].
          destruct (RegionVars.eq_dec (r', l') (r, l)).
          * inversion_clear e; simpl in *; subst.
            rewrite H2. do 2 rewrite H_same_key. reflexivity.
          * unfold RegionVars.eq in *; simpl in *.
            rewrite HMapP.add_neq_o. 
            { rewrite H2. rewrite HEqual'. rewrite HMapP.add_neq_o; [reflexivity | contradict n; intuition]. }
            { simpl. contradict n. intuition. } 
        - do 2 constructor; assumption.
        - constructor. constructor.  apply HMapP.Equal_Equiv in HEqual'. inversion HEqual'. apply H4. assumption. }
    + { exists (update_H (r, l, v) heapa). exists (update_H (r, l, v) heap2'); repeat split.
        -  unfold H.Equal in *; unfold update_H in *; simpl in *.
          intros [r' l'].
          destruct (RegionVars.eq_dec (r', l') (r, l)).
          * inversion_clear e; simpl in *; subst.
            do 2 rewrite H_same_key. reflexivity.
          * unfold RegionVars.eq in *; simpl in *.
            rewrite HMapP.add_neq_o. 
            { rewrite HEqual. rewrite HMapP.add_neq_o; [reflexivity | contradict n; intuition]. }
            { simpl. contradict n. intuition. } 
        - constructor. constructor.
        - do 2 constructor. apply HMapP.Equal_Equiv in HEqual. inversion HEqual. apply H0. assumption.  }
    + apply HMapP.Equal_sym in HEqual.
      edestruct (Aux_Aux_Step_Ext_Heap _ _ _ _ _ HStep2 HEqual)
        as [heap2'' [HEqual' HStep2']]. clear HStep2.
      eapply monotonic_heap_updates in H; eauto.
      replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
        in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj. destruct HDisj.
      eapply Disjointness_Preserves_Update_Write in HStep2'; eauto.
      destruct HStep2' as [? [? ?]].
      { exists x. exists (update_H (r, l, v) heap2'); repeat split.
        -  unfold H.Equal in *; unfold update_H in *; simpl in *.
          intros [r' l'].
          destruct (RegionVars.eq_dec (r', l') (r, l)).
          * inversion_clear e; simpl in *; subst.
             rewrite H2. do 2 rewrite H_same_key. reflexivity.
          * unfold RegionVars.eq in *; simpl in *.
            rewrite HMapP.add_neq_o. 
            { rewrite H2. rewrite HEqual'. rewrite HMapP.add_neq_o; [reflexivity | contradict n; intuition]. }
            { simpl. contradict n. intuition. } 
        - do 2 constructor; assumption.
        - constructor. constructor. apply HMapP.Equal_Equiv in HEqual'. inversion HEqual'. apply H4. assumption. }
    +  apply HMapP.Equal_sym in HEqual.
      edestruct (Aux_Aux_Step_Ext_Heap _ _ _ _ _ HStep2 HEqual)
         as [heap2'' [HEqual' HStep2']]. clear HStep2.
      eapply monotonic_heap_updates in H; eauto.
      replace (phi_as_list (Phi_Seq phi1 phi0)) with (phi_as_list phi1 ++ phi_as_list phi0)
        in HDisj by (simpl; reflexivity).
      apply Disjointness_app_app_and_l in HDisj. destruct HDisj.
      eapply Disjointness_Preserves_Update_Write in HStep2'; eauto.
      destruct HStep2' as [? [? ?]].
      { exists x. exists (update_H (r, l, v) heap2'); repeat split.
        - unfold H.Equal in *; unfold update_H in *; simpl in *.
          intros [r' l'].
          destruct (RegionVars.eq_dec (r', l') (r, l)).
          * inversion_clear e; simpl in *; subst.
             rewrite H2. do 2 rewrite H_same_key. reflexivity.
          * unfold RegionVars.eq in *; simpl in *.
            rewrite HMapP.add_neq_o. 
            { rewrite H2. rewrite HEqual'. rewrite HMapP.add_neq_o; [reflexivity | contradict n; intuition]. }
            { simpl. contradict n. intuition. } 
        - do 2 constructor; assumption.
        - constructor. constructor. apply HMapP.Equal_Equiv in HEqual'. inversion HEqual'. apply H4. assumption.  }            
    +  { exists (update_H (r, l, v) heapa). exists (update_H (r, l, v) heap2'); repeat split.
        -  unfold H.Equal in *; unfold update_H in *; simpl in *.
          intros [r' l'].
          destruct (RegionVars.eq_dec (r', l') (r, l)).
          * inversion_clear e; simpl in *; subst.
            do 2 rewrite H_same_key. reflexivity.
          * unfold RegionVars.eq in *; simpl in *.
            rewrite HMapP.add_neq_o. 
            { rewrite HEqual. rewrite HMapP.add_neq_o; [reflexivity | contradict n; intuition]. }
            { simpl. contradict n. intuition. } 
        - constructor. constructor.
        - do 2 constructor. apply HMapP.Equal_Equiv in HEqual. inversion HEqual. apply H0. assumption.  }
  - inversion HDet1; subst. clear H2.
    edestruct IHHStep1 with (phi2:=phi1)  as [heapA [heapB [? [? ?]]]]; eauto.
    + simpl in HDisj. apply Disjointness_app_app_and_r in HDisj. destruct HDisj. assumption.
    + simpl in HConf. inversion HDet1.
      apply Conflictness_app_and_r in HConf; [ destruct HConf  | | | ]; assumption.
    + exists heapA. exists heapB. repeat split.
      * assumption.
      * inversion H0; subst.
        { apply Phi_Heap_Step_Progress in HStep2. contradiction. }
        { constructor. assumption. }
      * inversion H2; subst.
        { constructor. constructor. assumption. }
        { apply Phi_Heap_Step_Progress in H2. contradiction. }
  - inversion HDet1; subst. clear H1.
    edestruct IHHStep1 with (phi2:=phi0) as [heapA [heapB [? [? ?]]]]; eauto.
    + exists heapA. exists heapB. repeat split.
      * assumption.
      * inversion H0; subst.
        { apply Phi_Heap_Step_Progress in HStep2. contradiction. }
        { constructor. assumption. }
      * inversion H1; subst.
        { constructor. constructor. assumption. }
        { apply Phi_Heap_Step_Progress in H1. contradiction. }
  -  apply HMapP.Equal_sym in HEqual.
     edestruct (Aux_Aux_Step_Ext_Heap _ _ _ _ _ HStep2 HEqual)
       as [heap2'' [HEqual' HStep2']]. clear HStep2.
     exists heap2''. exists heap2'. repeat split.
     * apply HMapP.Equal_sym. assumption.
     * constructor; assumption.
     * constructor; constructor.
  - inversion HDet1; subst. clear H2.
    edestruct IHHStep1 with (phi2:=phi1) as [heapA [heapB [? [? ?]]]]; eauto.
    + simpl in HDisj. apply Disjointness_app_app_and_r in HDisj. destruct HDisj. assumption.
    + simpl in HConf. inversion HDet1.
      apply Conflictness_app_and_r in HConf; [ destruct HConf  | | | ]; assumption.
    + exists heapA. exists heapB. repeat split.
      * assumption.
      * inversion H0; subst.
        { apply Phi_Heap_Step_Progress in HStep2. contradiction. }
        { constructor. assumption. }
      * inversion H2; subst.
        { constructor. constructor. assumption. }
        { apply Phi_Heap_Step_Progress in H2. contradiction. }
  - inversion HDet1; subst. 
    edestruct IHHStep1 with (phi2:=phi1) as [heapA [heapB [? [? ?]]]]; eauto.
    + simpl in HDisj. apply Disjointness_app_app_and_r in HDisj. destruct HDisj. assumption.
    + simpl in HConf. inversion HDet1.
      apply Conflictness_app_and_r in HConf; [ destruct HConf  | | | ]; assumption.
    + exists heapA. exists heapB. repeat split.
      * assumption.
      * inversion H0; subst.
        { apply Phi_Heap_Step_Progress in HStep2. contradiction. }
        { constructor. assumption. }
      * inversion H4; subst.
        { constructor. constructor. assumption. }
        { apply Phi_Heap_Step_Progress in H4. contradiction. }
   -  apply HMapP.Equal_sym in HEqual.
      edestruct (Aux_Aux_Step_Ext_Heap _ _ _ _ _ HStep2 HEqual)
        as [heap2'' [HEqual' HStep2']]. clear HStep2.
      exists heap2''. exists heap2'. repeat split.
     * apply HMapP.Equal_sym. assumption. 
     * constructor; assumption.
     * constructor; constructor.
Qed.



Lemma Diamond_Step :
  forall phi0 phi1 phi2 heap0 heap1 heap2,
    Det_Trace phi0 ->
    (phi0, heap0) ===> (phi1, heap1) ->
    (phi0, heap0) ===> (phi2, heap2) ->
    exists phi3, exists heap3, exists heap4, exists n13, exists n23,
      H.Equal heap3 heap4 /\                                                     
      (phi1, heap1) =a=>* (phi3, heap3, n13) /\
      (phi2, heap2) =a=>* (phi3, heap4, n23) /\
      (n13 <= 1) /\ (n23 <= 1).
Proof.
  induction phi0; intros phi1 phi2 heap0 heap1 heap2 HDet H0_1 H0_2.
  + inversion H0_1.
  + destruct d; inversion H0_1; subst; inversion H0_2; subst;
    repeat eexists; repeat econstructor.
  + inversion H0_1; subst; inversion H0_2; subst.
  - inversion HDet; subst.
      edestruct (IHphi0_1 phi1' phi1'0) as [phi3 [heap3 [heap4 [n13 [n23 [? [? [? ?]]]]]]]]; try eassumption.
      exists (Phi_Par phi3 phi0_2). exists heap3. exists heap4.  exists n13. exists n23; repeat split;
         try (solve [assumption | destruct H7; eassumption | eapply Par_Left_Pres; assumption]) .
    - inversion HDet; subst. destruct H5.
      edestruct (Par_Step_Equal phi0_1 phi0_2) as [heap3 [heap4 [? [? ?]]]]; try eassumption.
      exists (Phi_Par phi1' phi2'). exists heap3. exists heap4.
      repeat eexists; try (eapply PHT_Step; eassumption); repeat constructor. assumption.
    - inversion H0.
    - inversion HDet; subst. destruct H5.
      edestruct (Par_Step_Equal phi0_1 phi0_2 phi1' phi2') as [heap3 [heap4 [? [? ?]]]]; try eassumption.
      exists (Phi_Par phi1' phi2'). exists heap4. exists heap3. 
      repeat eexists; try (eapply PHT_Step; eassumption); repeat constructor.
      apply HMapP.Equal_sym; assumption.
    - inversion HDet; subst.
      edestruct (IHphi0_2 phi2' phi2'0) as [phi3 [heap3 [heap4 [n13 [n23 [? [? [? ?]]]]]]]]; try eassumption.
      exists (Phi_Par phi0_1 phi3). exists heap3. exists heap4. exists n13. exists n23; repeat split;
        try (solve [assumption | destruct H7; eassumption | eapply Par_Right_Pres; assumption]) .
    - inversion H0.
    - inversion H0.
    - inversion H0.
    - exists Phi_Nil. exists heap2. repeat eexists; repeat econstructor.
  + inversion H0_1; subst; inversion H0_2; subst.
    - inversion HDet; subst.
      edestruct (IHphi0_1 phi1' phi1'0) as [phi3 [heap3 [heap4 [n13 [n23 [? [? [? ?]]]]]]]]; try eassumption.
      exists (Phi_Seq phi3 phi0_2). exists heap3. exists heap4. exists n13. exists n23. repeat split;
        try (solve [assumption | destruct H6; eassumption | eapply Seq_Left_Pres; assumption]) .
    - inversion H0.
    - inversion H0.
    - inversion H1.
    - inversion HDet; subst.
      edestruct (IHphi0_2 phi2' phi2'0) as [phi3 [heap3 [heap4 [n13 [n23 [? [? [? ?]]]]]]]]; try eassumption.
      exists (Phi_Seq Phi_Nil phi3). exists heap3. exists heap4. exists n13. exists n23; repeat split;
        try (solve [assumption | destruct H6; eassumption | eapply Seq_Right_Pres; assumption]) .
    - inversion H0.
    - inversion H0.
    - inversion H0.
    - exists Phi_Nil. exists heap2. repeat eexists; repeat econstructor.
Qed.

Lemma Diamond_Step_new :
  forall phi0 phi1 phi2 heapa heapb heap1 heap2,
    Det_Trace phi0 ->
    H.Equal heapa heapb ->
    (phi0, heapa) ===> (phi1, heap1) ->
    (phi0, heapb) ===> (phi2, heap2) ->
    exists phi3, exists heap3, exists heap4, exists n13, exists n23,
      H.Equal heap3 heap4 /\                                                     
      (phi1, heap1) =a=>* (phi3, heap3, n13) /\
      (phi2, heap2) =a=>* (phi3, heap4, n23) /\
      (n13 <= 1) /\ (n23 <= 1).
Proof.
  induction phi0; intros phi1 phi2 heapa heapb heap1 heap2 HDet HEqual H0_1 H0_2.
  + inversion H0_1.
  + destruct d; inversion H0_1; subst; inversion H0_2; subst; exists Phi_Nil.
    - exists (update_H (r, n, v) heapa); exists (update_H (r, n, v) heapb).
      repeat eexists; repeat econstructor.
      unfold H.Equal in *; unfold update_H in *; simpl in *.
      intros [r' n'].
      destruct (RegionVars.eq_dec (r', n') (r, n)).
        * inversion_clear e; simpl in *; subst.
          do 2 rewrite H_same_key_1. reflexivity.
        * unfold RegionVars.eq in *; simpl in *.
          rewrite HMapP.add_neq_o by (contradict n0; intuition).
          rewrite HMapP.add_neq_o by (contradict n0; intuition).
          apply HEqual.
    - exists heap1; exists heap2; repeat eexists; repeat econstructor.
      assumption.
    - exists (update_H (r, n, v) heapa); exists (update_H (r, n, v) heapb).
      repeat eexists; repeat econstructor.
      unfold H.Equal in *; unfold update_H in *; simpl in *.
      intros [r' n'].
      destruct (RegionVars.eq_dec (r', n') (r, n)).
        * inversion_clear e; simpl in *; subst.
          do 2 rewrite H_same_key_1. reflexivity.
        * unfold RegionVars.eq in *; simpl in *.
          rewrite HMapP.add_neq_o by (contradict n0; intuition).
          rewrite HMapP.add_neq_o by (contradict n0; intuition).
          apply HEqual.
  + inversion H0_1; subst; inversion H0_2; subst.
  - inversion HDet; subst.
      edestruct (IHphi0_1 phi1' phi1'0) as [phi3 [heap3 [heap4 [n13 [n23 [? [? [? ?]]]]]]]]; try eassumption.
      exists (Phi_Par phi3 phi0_2). exists heap3. exists heap4.  exists n13. exists n23; repeat split;
         try (solve [assumption | destruct H7; eassumption | eapply Par_Left_Pres; assumption]) .
    - inversion HDet; subst. destruct H5.
      edestruct (Par_Step_Equal_new phi0_1 phi0_2) as [heap3 [heap4 [? [? ?]]]]; try eassumption.
      exists (Phi_Par phi1' phi2'). exists heap3. exists heap4.
      repeat eexists; try (eapply PHT_Step; eassumption); repeat constructor. assumption.
    - inversion H0.
    - inversion HDet; subst. destruct H5.
      assert (HEqual': H.Equal heapb heapa) by (eauto using HMapP.Equal_sym).
      edestruct (Par_Step_Equal_new phi0_1 phi0_2 phi1' phi2') as [heap3 [heap4 [? [? ?]]]]; try eassumption.
      exists (Phi_Par phi1' phi2'). exists heap4. exists heap3. 
      repeat eexists; try (eapply PHT_Step; eassumption); repeat constructor.
      apply HMapP.Equal_sym; assumption.
    - inversion HDet; subst.
      edestruct (IHphi0_2 phi2' phi2'0) as [phi3 [heap3 [heap4 [n13 [n23 [? [? [? ?]]]]]]]]; try eassumption.
      exists (Phi_Par phi0_1 phi3). exists heap3. exists heap4. exists n13. exists n23; repeat split;
        try (solve [assumption | destruct H7; eassumption | eapply Par_Right_Pres; assumption]) .
    - inversion H0.
    - inversion H0.
    - inversion H0.
    - exists Phi_Nil. exists heap1. exists heap2. repeat eexists; repeat econstructor; assumption.
  + inversion H0_1; subst; inversion H0_2; subst.
    - inversion HDet; subst.
      edestruct (IHphi0_1 phi1' phi1'0) as [phi3 [heap3 [heap4 [n13 [n23 [? [? [? ?]]]]]]]]; try eassumption.
      exists (Phi_Seq phi3 phi0_2). exists heap3. exists heap4. exists n13. exists n23. repeat split;
        try (solve [assumption | destruct H6; eassumption | eapply Seq_Left_Pres; assumption]) .
    - inversion H0.
    - inversion H0.
    - inversion H1.
    - inversion HDet; subst.
      edestruct (IHphi0_2 phi2' phi2'0) as [phi3 [heap3 [heap4 [n13 [n23 [? [? [? ?]]]]]]]]; try eassumption.
      exists (Phi_Seq Phi_Nil phi3). exists heap3. exists heap4. exists n13. exists n23; repeat split;
        try (solve [assumption | destruct H6; eassumption | eapply Seq_Right_Pres; assumption]) .
    - inversion H0.
    - inversion H0.
    - inversion H0.
    - exists Phi_Nil. exists heap1. exists heap2. repeat eexists; repeat econstructor; assumption.
Qed.

Theorem Phi_Heap_Step__Preserves_DAs :
  forall phi phi' heap heap',
    (phi, heap) ===> (phi', heap') ->
    (forall da,
       In da (phi_as_list phi') ->
       In da (phi_as_list phi)).
Proof.
  intros phi phi' heap heap' HStep.
  dependent induction HStep; intros da HIn; simpl phi_as_list in *.
  - inversion HIn.
  - inversion HIn.
  - inversion HIn.
  - apply in_or_app.
    apply in_app_or in HIn; destruct HIn.
    + left; apply IHHStep; assumption.
    + right; assumption.
  - apply IHHStep; assumption.
  - assumption.
  - apply in_or_app.
    apply in_app_or in HIn; destruct HIn.
    + left; apply IHHStep; assumption.
    + right; assumption.
  - apply in_or_app.
    apply in_app_or in HIn; destruct HIn.
    + left; assumption.
    + right; apply IHHStep; assumption.
  - assumption.
Qed.

Lemma Det_Pres_Par_Conf_1:
  forall phi1 phi1' phi2 heap heap',
    (phi1, heap) ===> (phi1', heap') ->
    Det_Trace (Phi_Par phi1 phi2) ->
    ~ Conflict_Traces (phi_as_list phi1') (phi_as_list phi2).
Proof.
  intros. inversion H0; subst. destruct H5.
  intro. inversion H5; subst. apply H1.
  econstructor; eauto using Phi_Heap_Step__Preserves_DAs.
Qed.

Lemma Det_Pres_Par_Conf_1_aux:
  forall phi1 phi1' phi2 heap heap',
    (phi1, heap) ===> (phi1', heap') ->
    Det_Trace phi1' ->
    Det_Trace (Phi_Par phi1 phi2) ->
    ~ Conflict_Traces (phi_as_list phi1') (phi_as_list phi2).
Proof.
  intros phi1 phi1' phi2 heap heap' H1 H2 H3.
  inversion_clear H3; subst. destruct H4. clear H4.
  generalize dependent phi2.  
  dependent induction H1; intros; subst; simpl in *.
  - intro. inversion H1. trivial.
  - intro. inversion H4. trivial.
  - intro. inversion H4. trivial.
  - inversion H2; inversion H; subst.  
    apply Conflictness_app_and_r in H3; auto. destruct H3.
    apply Conflictness_and_app_r; auto.
  - apply IHPhi_Heap_Step; auto; inversion H2; inversion H; assumption.
  - apply H3.
  - inversion H2; inversion H; subst.
    apply Conflictness_app_and_r in H3; auto. destruct H3.
    apply Conflictness_and_app_r; auto.
  - inversion H2; inversion H; subst.
    destruct H8.
    apply Conflictness_app_and_r in H3; auto. destruct H3.
    apply Conflictness_and_app_r; auto.
  - intro; now apply H3.
Qed.

Lemma Det_Pres_Par_Conf_2:
  forall phi1 phi1' phi2 heap heap',
    (phi1, heap) ===> (phi1', heap') ->
    Det_Trace (Phi_Par phi1 phi2) ->
    ~ Conflict_Traces (phi_as_list phi1') (phi_as_list phi2).
Proof.
  intros. inversion H0; subst. destruct H5.
  intro. inversion H5; subst. apply H1. 
  econstructor; eauto using Phi_Heap_Step__Preserves_DAs.
Qed.

Lemma Det_Pres_Par_Conf_2_aux:
  forall phi1 phi2 phi2' heap heap',
    (phi2, heap) ===> (phi2', heap') ->
    Det_Trace phi2' ->
    Det_Trace (Phi_Par phi1 phi2) ->
    ~ Conflict_Traces (phi_as_list phi1) (phi_as_list phi2').
Proof.
  intros phi1 phi2 phi2' heap heap' H1 H2 H3.
   inversion_clear H3; subst. destruct H4. clear H4.  
   generalize dependent phi1. 
   dependent induction H1; intros; inversion H0; subst; simpl in *.
   - intro. inversion H1; trivial.
   - intro. inversion H4; trivial.
   - intro. inversion H4; trivial.
   - inversion H2; inversion H0; subst.
     eapply Conflictness_app_and_l in H3; auto.  destruct H3. 
     apply Conflictness_and_app_l; auto.
   - apply IHPhi_Heap_Step; auto. inversion H2; inversion H0; assumption.
   - apply H3.
   - inversion H2; inversion H0; subst.
     destruct H8.
     apply Conflictness_app_and_l in H3; auto. destruct H3.
     apply Conflictness_and_app_l; auto. 
   - inversion H2; inversion H0; subst.
     destruct H8.
     apply Conflictness_app_and_l in H3; auto. destruct H3.
     apply Conflictness_and_app_l; auto. 
   - intro. inversion H1; trivial.
Qed.


Lemma Det_Pres_Par_Disj_1:
  forall phi1 phi1' phi2 heap heap',
    (phi1, heap) ===> (phi1', heap') ->
    Det_Trace phi1' ->
    Det_Trace (Phi_Par phi1 phi2) ->
    Disjoint_Traces (phi_as_list phi1') (phi_as_list phi2).
Proof.
  intros phi1 phi1' phi2 heap heap' H1 H2 H3.
  inversion H3; subst; simpl. destruct H6.
  inversion H0; subst. econstructor; intros. apply H6; auto.
  eapply Phi_Heap_Step__Preserves_DAs; eauto.
Qed.    
 
Lemma Det_Pres_Par_Disj_1_aux:
  forall phi1 phi1' phi2 heap heap',
    (phi1, heap) ===> (phi1', heap') ->
    Det_Trace phi1' ->
    Det_Trace (Phi_Par phi1 phi2) ->
    Disjoint_Traces (phi_as_list phi1') (phi_as_list phi2).
Proof.
  intros phi1 phi1' phi2 heap heap' H1 H2 H3.
  inversion_clear H3; subst. destruct H4. clear H3.
  generalize dependent phi2.     
  dependent induction H1; intros; simpl; try (solve [constructor]).
  inversion H4; subst;
  simpl in *; try (solve [econstructor ]).
  - econstructor; intros. apply H1; [inversion H3 | assumption].
  - econstructor; intros. inversion H3.
  - econstructor; intros. inversion H3.
  - inversion H2; inversion H; subst.
    apply Disjointness_and_app_r. simpl in H4.
    apply Disjointness_app_app_and_r in H4. destruct H4.
    split; [ apply IHPhi_Heap_Step; eauto | assumption].
  - inversion H2; inversion H. simpl in H4.
    apply IHPhi_Heap_Step; eauto.
  - econstructor; intros. inversion H1. 
  - inversion H2; inversion H; subst.
    apply Disjointness_and_app_r. simpl in H4.
    apply Disjointness_app_app_and_r in H4. destruct H4.
    split; [ apply IHPhi_Heap_Step; eauto | assumption].
  - inversion H2; inversion H; subst.
    apply Disjointness_and_app_r. simpl in H4.
    apply Disjointness_app_app_and_r in H4. destruct H4.
    split; [ assumption | apply IHPhi_Heap_Step; eauto].
  -  econstructor; intros. inversion H1.    
Qed.

Lemma Det_Pres_Par_Disj_2:
  forall phi2 phi2' phi1 heap heap',
    (phi2, heap) ===> (phi2', heap') ->
    Det_Trace phi2' ->
    Det_Trace (Phi_Par phi1 phi2) ->
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2').
Proof.
  intros phi2 phi2' phi1 heap heap' H1 H2 H3.
   inversion H3; subst; simpl. destruct H6.
  inversion H0; subst. econstructor; intros. apply H6; auto.
  eapply Phi_Heap_Step__Preserves_DAs; eauto.
Qed.   

Lemma Det_Pres_Par_Disj_2_aux:
  forall phi2 phi2' phi1 heap heap',
    (phi2, heap) ===> (phi2', heap') ->
    Det_Trace phi2' ->
    Det_Trace (Phi_Par phi1 phi2) ->
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2').
Proof.
  intros phi2 phi2' phi1 heap heap' H1 H2 H3.
  inversion_clear H3; subst. destruct H4. clear H3.
  generalize dependent phi1.     
  dependent induction H1; intros; simpl in *;
  try (solve [constructor |
              econstructor; intros; inversion H5 |
              econstructor; intros; inversion H3
             ]).
  - inversion H2; inversion H0; subst.
    apply Disjointness_and_app_l. simpl in H4.
    apply Disjointness_app_app_and_l in H4. destruct H4.
    split; [apply IHPhi_Heap_Step; eauto | assumption].
  - inversion H2; inversion H0. 
    apply IHPhi_Heap_Step; eauto.
  - inversion H2; inversion H0; subst.
    apply Disjointness_and_app_l. simpl in H4.
    apply Disjointness_app_app_and_l in H4. destruct H4.
    split; [apply IHPhi_Heap_Step; eauto | assumption].
  -  inversion H2; inversion H0; subst.
    apply Disjointness_and_app_l. simpl in H4.
    apply Disjointness_app_app_and_l in H4. destruct H4.
    split; [assumption | apply IHPhi_Heap_Step; eauto].
Qed.

Theorem Det_Pres_Aux :
   forall phi phi' heap heap',
     (phi, heap) ===> (phi', heap') ->
     Det_Trace phi ->
     Det_Trace phi'.
Proof.
  intros phi phi' heap heap' H1 H2.
  dependent induction H1; intros; try (solve [constructor]).
  - inversion H2; econstructor; [ apply IHPhi_Heap_Step; assumption | assumption].
  - inversion H2; econstructor. constructor. apply IHPhi_Heap_Step; assumption. 
  - inversion H2; subst; econstructor; [ apply IHPhi_Heap_Step; assumption | inversion H2; assumption |].
    destruct H5. split.
    + intro; inversion H5; subst.
      apply H; econstructor; eauto using Phi_Heap_Step__Preserves_DAs.
    + constructor; intros.
      inversion H0; subst.
      apply H7; eauto using Phi_Heap_Step__Preserves_DAs.
  - inversion H2; subst; econstructor; [assumption | apply IHPhi_Heap_Step; assumption |].
    destruct H5. split.
    + intro; inversion H5; subst.
      apply H; econstructor; eauto using Phi_Heap_Step__Preserves_DAs.
    + constructor; intros.
      inversion H0; subst.
      apply H7; eauto using Phi_Heap_Step__Preserves_DAs.
Qed.    

Theorem Det_Pres :
   forall phi phi' heap heap' n',
     (phi, heap) =a=>* (phi', heap', n') ->
     Det_Trace phi ->
     Det_Trace phi'.
Proof.
   intros phi phi' heap heap' n' HSteps.
   dependent induction HSteps; intro HDet.
   - assumption.
   - eapply Det_Pres_Aux; eassumption.
   - apply IHHSteps2; apply IHHSteps1; assumption.
Qed.


    
Theorem Diamond_Walk_Aux : 
  forall n n1 n2,
    n = n1 + n2 ->
    forall phi0 phi1 phi2 heap0 heap1 heap2,
    forall (H0_1: (phi0, heap0) =a=>* (phi1, heap1, n1)),
    forall (H0_2: (phi0, heap0) =a=>* (phi2, heap2, n2)),
      Det_Trace phi0 ->
      exists phi3, exists heap3, exists heap4, exists n13, exists n23,
        H.Equal heap3 heap4 /\                                                             
        (phi1, heap1) =a=>* (phi3, heap3, n13) /\
        (phi2, heap2) =a=>* (phi3, heap4, n23) /\
        (n13 <= n2) /\ (n23 <= n1).
Proof.
  induction n using Wf_nat.lt_wf_ind.
  intros n1 n2 HSum.
  intros phi0 phi1 phi2 heap0 heap1 heap2 H0_1 H0_2 HDet. 
  dependent destruction H0_1.
  - exists phi2; exists heap2; exists heap2; exists n2; exists 0.
   repeat split; try (solve [omega]).
   + assumption.  (* phi1 walks into phi1 in n2 steps *)
   + apply PHT_Refl.  (* phi2 takes 0 steps *)
  -  rename H0 into H0_1.  
    dependent destruction H0_2.
    + exists phi1. exists heap1. exists heap1. exists 0. exists 1.
      repeat split; try (solve [omega]).
      * apply PHT_Refl. (* phi1 takes 0 steps *)
      * apply PHT_Step; assumption. (* phi2 walks into phi1 in 1 step *)
    + rename H0 into H0_2.
      destruct (Diamond_Step phi0 phi1 phi2 heap0 heap1 heap2 HDet H0_1 H0_2)
        as [phi3 [heap3 [heap4 [n13 [n23 [Heq [H1_3 [H2_3 [? ?]]]]]]]]].
      exists phi3. exists heap3. exists heap4. exists n13. exists n23. (* n13 and n23 are the remaining steps *)
      repeat split;  try (solve [omega]). 
      * assumption. (* context provided by Diamond_Step *)
      * assumption. (* context provided by Diamond_Step *)
      * assumption.
    + rename phi' into phi2'. rename heap' into heap2'. 
      rename H0_2_1 into H0_2'. rename H0_2_2 into H2'_2. 
      edestruct (H (1 + n')) as [phi3 [heap3 [heap4 [n1_3 [n2'_3 [Heq [H1_3 [H2'_3 [? ?]]]]]]]]]. (* transitivity on phi2 *)
      * omega. (* phi2 took n' intermediate steps *)
      * reflexivity.
      * eapply PHT_Step; eassumption.  (* phi1 steps 1 *)
      * eassumption. (* by induction *)
      * eassumption. (* by induction *)  
      * { edestruct (H (n2'_3 + n'')) as [phi4 [heap5 [heap6 [n3_4 [n2_4 [Heq' [H3_4 [H2_4 [? ?]]]]]]]]].
          - omega.  (* phi2 took n'' intermediate steps *)
          - reflexivity.
          - eassumption. (* by induction *)
          - eassumption. (* by induction *)
          - eapply Det_Pres; eassumption.
          - apply Aux_Step_Ext_Heap with (heapB:=heap3) in H3_4; [ | apply HMapP.Equal_sym; assumption].
            destruct H3_4 as [heap5' [? ?]].
            exists phi4. exists heap5'. exists heap6. exists (1 + n1_3 + n3_4). exists n2_4.
            repeat split; try (solve [omega]).
            + eapply HMapP.Equal_trans in Heq'; eauto. apply HMapP.Equal_sym; assumption.  
            + eapply PHT_Trans. eassumption. assumption.
            + assumption. }
  - rename phi' into phi1'. rename heap' into heap1'.
    rename H0_1_1 into H0_1'. rename H0_1_2 into H1'_1.
    edestruct (H (n' + n2)) as [phi3 [heap3 [heap4 [n1'_3 [n2_3 [Heq [H1'_3 [H2_3 [? ?]]]]]]]]].
    + omega.  (* phi1 took n' intermediate steps *)
    + reflexivity.
    + eassumption.
    + eassumption.
    + assumption.
    + edestruct (H (n'' + n1'_3)) as [phi4 [heap5 [heap6 [n1_4 [n3_4 [Heq' [H1_4 [H3_4 [? ?]]]]]]]]].
      * omega. (* phi1 took the remaining n'' intermediate steps *)
      * reflexivity. 
      * eassumption.
      * eassumption.
      * eapply Det_Pres; eassumption.
      * apply Aux_Step_Ext_Heap with (heapB:=heap4) in H3_4; [ |assumption].
        destruct H3_4 as [heap6' [? ?]]. 
        exists phi4. exists heap5. exists heap6'. exists n1_4. exists (1 + n2_3 + n3_4).
        repeat split;  try (solve [omega]).
        { eapply HMapP.Equal_trans in H4; eauto. }
        { assumption. }
        { eapply PHT_Trans. eassumption. assumption. }
Qed.

Theorem Diamond_Walk_Aux_new : 
  forall n n1 n2,
    n = n1 + n2 ->
    forall phi0 phi1 phi2 heapa heapb heap1 heap2,
    H.Equal heapa heapb ->
    forall (H0_1: (phi0, heapa) =a=>* (phi1, heap1, n1)),
    forall (H0_2: (phi0, heapb) =a=>* (phi2, heap2, n2)),
      Det_Trace phi0 ->
      exists phi3, exists heap3, exists heap4, exists n13, exists n23,
        H.Equal heap3 heap4 /\
        (phi1, heap1) =a=>* (phi3, heap3, n13) /\
        (phi2, heap2) =a=>* (phi3, heap4, n23) /\
        (n13 <= n2) /\ (n23 <= n1).
Proof.
  induction n using Wf_nat.lt_wf_ind.
  intros n1 n2 HSum.
  intros phi0 phi1 phi2 heapa heapb heap1 heap2 HEqual H0_1 H0_2 HDet. 
  dependent destruction H0_1.
  - assert (HEqual' : H.Equal heapb heap1) by (eauto using HMapP.Equal_sym).
    edestruct (Aux_Step_Ext_Heap _ _ _ _ _ _ H0_2 HEqual')
     as [heap2' [HEqual'' ?]].
    exists phi2; exists heap2'; exists heap2; exists n2; exists 0.
    repeat split; try (solve [omega]).
    + eauto using HMapP.Equal_sym.  
    + assumption. (* phi1 walks into phi2 in n2 steps *)
    + apply PHT_Refl.  (* phi2 takes 0 steps *)
  - rename H0 into H0_1.  
    dependent destruction H0_2.
    + edestruct (Aux_Aux_Step_Ext_Heap _ _ _ _ _ H0_1 HEqual)
       as [heap1' [HEqual' H0_1']].
      exists phi1. exists heap1. exists heap1'. exists 0. exists 1.
      repeat split; try (solve [omega]).
      * assumption.
      * apply PHT_Refl. (* phi1 takes 0 steps *)
      * apply PHT_Step; assumption. (* phi2 walks into phi1 in 1 step *)
    + rename H0 into H0_2.
      destruct (Diamond_Step_new phi0 phi1 phi2 heapa heapb heap1 heap2 HDet HEqual H0_1 H0_2)
        as [phi3 [heap3 [heap4 [n13 [n23 [Heq [H1_3 [H2_3 [? ?]]]]]]]]].
      exists phi3. exists heap3. exists heap4. exists n13. exists n23. (* n13 and n23 are the remaining steps *)
      repeat split;  try (solve [omega]). 
      * assumption.
      * assumption. (* context provided by Diamond_Step *)
      * assumption. (* context provided by Diamond_Step *)
    + rename phi' into phi2'. rename heap' into heap2'. 
      rename H0_2_1 into H0_2'. rename H0_2_2 into H2'_2. 
      edestruct (H (1 + n')) as [phi3 [heap3 [heap4 [n1_3 [n2'_3 [Heq [H1_3 [H2'_3 [? ?]]]]]]]]]. (* transitivity on phi2 *)
      * omega. (* phi2 took n' intermediate steps *)
      * reflexivity.
      * eassumption.
      * eapply PHT_Step; eassumption.  (* phi1 steps 1 *)
      * eassumption. (* by induction *)
      * eassumption. (* by induction *)  
      * { edestruct (H (n2'_3 + n'')) as [phi4 [heap5 [heap6 [n3_4 [n2_4 [Heq' [H3_4 [H2_4 [? ?]]]]]]]]].
          - omega.  (* phi2 took n'' intermediate steps *)
          - reflexivity.
          - apply HMapP.Equal_refl.
          - eassumption. (* by induction *)
          - eassumption. (* by induction *)
          - eapply Det_Pres; eassumption.
          - apply Aux_Step_Ext_Heap with (heapB:=heap3) in H3_4; [ | apply HMapP.Equal_sym; assumption].
            destruct H3_4 as [heap5' [? ?]].
            exists phi4. exists heap5'. exists heap6. exists (1 + n1_3 + n3_4). exists n2_4.
            repeat split; try (solve [omega]).
            + eapply HMapP.Equal_trans in Heq'; eauto. apply HMapP.Equal_sym; assumption.  
            + eapply PHT_Trans. eassumption. assumption.
            + assumption. }
  - rename phi' into phi1'. rename heap' into heap1'.
    rename H0_1_1 into H0_1'. rename H0_1_2 into H1'_1.
    edestruct (H (n' + n2)) as [phi3 [heap3 [heap4 [n1'_3 [n2_3 [Heq [H1'_3 [H2_3 [? ?]]]]]]]]].
    + omega.  (* phi1 took n' intermediate steps *)
    + reflexivity.
    + eassumption.
    + eassumption.
    + eassumption.
    + assumption.
    + edestruct (H (n'' + n1'_3)) as [phi4 [heap5 [heap6 [n1_4 [n3_4 [Heq' [H1_4 [H3_4 [? ?]]]]]]]]].
      * omega. (* phi1 took the remaining n'' intermediate steps *)
      * reflexivity. 
      * apply HMapP.Equal_refl.
      * eassumption.
      * eassumption.
      * eapply Det_Pres; eassumption.
      * apply Aux_Step_Ext_Heap with (heapB:=heap4) in H3_4; [ |assumption].
        destruct H3_4 as [heap6' [? ?]]. 
        exists phi4. exists heap5. exists heap6'. exists n1_4. exists (1 + n2_3 + n3_4).
        repeat split;  try (solve [omega]).
        { eapply HMapP.Equal_trans in H4; eauto. }
        { assumption. }
        { eapply PHT_Trans. eassumption. assumption. }
Qed.

Theorem Diamond_Walk : 
  forall phi0 phi1 phi2 heap0 heap1 heap2,
    (phi0, heap0) ==>* (phi1, heap1) ->
    (phi0, heap0) ==>* (phi2, heap2) ->
    Det_Trace phi0 ->
    exists phi3, exists heap3, exists heap4,
      H.Equal heap3 heap4 /\                           
      (phi1, heap1) ==>* (phi3, heap3) /\
      (phi2, heap2) ==>* (phi3, heap4).
Proof.
  intros phi0 phi1 phi2 heap0 heap1 heap2 H0_1 H0_2 HDet.
  unfold Phi_Heap_Steps in *.
  destruct H0_1 as [n0_1 H0_1].
  destruct H0_2 as [n0_2 H0_2].
  edestruct (Diamond_Walk_Aux (n0_1 + n0_2) n0_1 n0_2) as [phi3 [heap3 [heap4 [n1_3 [n2_3 [Heq [H1_3 [H2_3 [? ?]]]]]]]]]; eauto.
  exists phi3. exists heap3. exists heap4. repeat split;[ assumption | |]; eexists; eassumption.
Qed.

Theorem Diamond_Walk_new : 
  forall phi0 phi1 phi2 heapa heapb heap1 heap2,
    H.Equal heapa heapb ->
    (phi0, heapa) ==>* (phi1, heap1) ->
    (phi0, heapb) ==>* (phi2, heap2) ->
    Det_Trace phi0 ->
    exists phi3, exists heap3, exists heap4,
      H.Equal heap3 heap4 /\                           
      (phi1, heap1) ==>* (phi3, heap3) /\
      (phi2, heap2) ==>* (phi3, heap4).
Proof.
  intros phi0 phi1 phi2 heapa heapb heap1 heap2 HEqual H0_1 H0_2 HDet.
  unfold Phi_Heap_Steps in *.
  destruct H0_1 as [n0_1 H0_1].
  destruct H0_2 as [n0_2 H0_2].
  edestruct (Diamond_Walk_Aux_new (n0_1 + n0_2) n0_1 n0_2) as [phi3 [heap3 [heap4 [n1_3 [n2_3 [Heq [H1_3 [H2_3 [? ?]]]]]]]]]; eauto.
  exists phi3. exists heap3. exists heap4. repeat split;[ assumption | |]; eexists; eassumption.
Qed.

Lemma Term_Walk_Idemp :
  forall heap phi' heap' n,
    (Phi_Nil, heap) =a=>* (phi', heap', n) ->
    phi' = Phi_Nil /\ heap = heap'.
Proof.
  intros heap phi' heap' n HStep.
  dependent induction HStep.
  + split; reflexivity.
  + inversion H.
  + eapply IHHStep2.
    - destruct IHHStep1; subst; reflexivity.
    - reflexivity.
Qed.

Theorem Diamond_Term_Walk : 
  forall phi0 heap0 heap1 heap2,
    (phi0, heap0) ==>* (Phi_Nil, heap1) ->
    (phi0, heap0) ==>* (Phi_Nil, heap2) ->
    Det_Trace phi0 ->
    H.Equal heap1 heap2.
Proof.
  intros phi0 heap0 heap1 heap2 HDet HStep1 HStep2.
  edestruct (Diamond_Walk phi0 Phi_Nil Phi_Nil heap0 heap1 heap2) as [phi3 [heap3 [heap4 [Heq [H1 H2]]]]]; try eassumption.
  destruct H1 as [n1 H1]. destruct H2 as [n2 H2].
  edestruct (Term_Walk_Idemp heap1 phi3 heap3 n1) as [? ?]; try eassumption.
  edestruct (Term_Walk_Idemp heap2 phi3 heap4 n2) as [? ?]; try eassumption.
  subst. assumption.
Qed.

Theorem Diamond_Term_Walk_new : 
  forall phi0 heapa heapb heap1 heap2,
    H.Equal heapa heapb ->
    (phi0, heapa) ==>* (Phi_Nil, heap1) ->
    (phi0, heapb) ==>* (Phi_Nil, heap2) ->
    Det_Trace phi0 ->
    H.Equal heap1 heap2.
Proof.
  intros phi0 heapa heapb heap1 heap2 HEqual HStep1 HStep2 HDet.
  edestruct (Diamond_Walk_new phi0 Phi_Nil Phi_Nil heapa heapb heap1 heap2) as [phi3 [heap3 [heap4 [Heq [H1 H2]]]]]; try eassumption.
  destruct H1 as [n1 H1]. destruct H2 as [n2 H2].
  edestruct (Term_Walk_Idemp heap1 phi3 heap3 n1) as [? ?]; try eassumption.
  edestruct (Term_Walk_Idemp heap2 phi3 heap4 n2) as [? ?]; try eassumption.
  subst. assumption.
Qed.

Lemma Ext_disjoint_sets :
  forall e1 acts a,
    Disjoint_Sets_Computed_Actions e1 (set_union acts a) ->
    Disjoint_Sets_Computed_Actions e1 acts /\ Disjoint_Sets_Computed_Actions e1 a.
Proof.
  intros e1 acts a H. 
  split; inversion H; subst.
  - econstructor; intros. apply H0; auto. unfold set_elem, set_union. apply Union_introl. assumption.
  - econstructor. intros. apply H0; auto. unfold set_elem, set_union. apply Union_intror. assumption.
Qed.

Lemma Ext_disjoint_sets_2 :
  forall e1 acts a,
    Disjoint_Sets_Computed_Actions (set_union acts a) e1 ->
    Disjoint_Sets_Computed_Actions acts e1 /\ Disjoint_Sets_Computed_Actions a e1.
Proof.
  intros e1 acts a H. 
  split; inversion H; subst.
  - econstructor; intros. apply H0; auto. unfold set_elem, set_union. apply Union_introl. assumption.
  - econstructor. intros. apply H0; auto. unfold set_elem, set_union. apply Union_intror. assumption.
Qed.

Lemma Disjoint_da_in_theta :
  forall e1 e2 p1 p2,
    Disjoint_Sets_Computed_Actions e1 e2 ->
    DA_in_Theta p1 (Some e1) ->
    DA_in_Theta p2 (Some e2) ->
    Disjoint_Dynamic p1 p2.
Proof.
  intros e1 e2 p1 p2 H1 H2 H3.
  generalize dependent p2. 
  dependent induction H2; intros.
  - generalize dependent e1. 
    dependent induction H3; intros; inversion H1; subst.  
    + assert (HD : Disjoint_Computed_Actions (CA_AllocAbs s) (CA_AllocAbs s0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H5. inversion H5. reflexivity.
    + assert (HD : Disjoint_Computed_Actions (CA_AllocAbs s) (CA_ReadAbs s0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H5; inversion H5; reflexivity.
    + assert (HD : Disjoint_Computed_Actions (CA_AllocAbs s) (CA_ReadConc s0 l0)) by (apply H2; auto).
      inversion HD; subst.
      constructor; contradict H5; inversion H5; reflexivity.
    + assert (HD : Disjoint_Computed_Actions (CA_AllocAbs s) (CA_WriteAbs s0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H5. inversion H5. reflexivity.
    + assert (HD : Disjoint_Computed_Actions (CA_AllocAbs s) (CA_WriteConc s0 l0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H5. inversion H5. reflexivity.
    + eapply IHDA_in_Theta; eauto.
      apply Ext_disjoint_sets in H1; destruct H1; assumption.
    + eapply IHDA_in_Theta; eauto.
      apply Ext_disjoint_sets in H1; destruct H1; assumption.
  - generalize dependent e1.  
    dependent induction H3; intros; inversion H1; subst.
    + assert (HD : Disjoint_Computed_Actions (CA_ReadAbs s) (CA_AllocAbs s0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H5; inversion H5; reflexivity.
    + assert (HD : Disjoint_Computed_Actions (CA_ReadAbs s) (CA_ReadAbs s0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. 
    + assert (HD : Disjoint_Computed_Actions (CA_ReadAbs s) (CA_ReadConc s0 l0)) by (apply H2; auto).
      inversion HD; subst.
      constructor.
    + assert (HD : Disjoint_Computed_Actions (CA_ReadAbs s) (CA_WriteAbs s0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H5; inversion H5; reflexivity.
    + assert (HD : Disjoint_Computed_Actions (CA_ReadAbs s) (CA_WriteConc s0 l0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H5; inversion H5; reflexivity.
    + eapply IHDA_in_Theta; eauto.
      apply Ext_disjoint_sets in H1; destruct H1; assumption.
    + eapply IHDA_in_Theta; eauto.
      apply Ext_disjoint_sets in H1; destruct H1; assumption. 
  - generalize dependent e1.  
    dependent induction H3; intros; inversion H1; subst.
    + assert (HD : Disjoint_Computed_Actions (CA_ReadConc s l) (CA_AllocAbs s0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H4; inversion H4; reflexivity.
    + assert (HD : Disjoint_Computed_Actions (CA_ReadConc s l) (CA_ReadAbs s0)) by (apply H2; auto).
      inversion HD; subst.
      constructor.
    + assert (HD : Disjoint_Computed_Actions (CA_ReadConc s l) (CA_ReadConc s0 l0)) by (apply H2; auto).
      inversion HD; subst.
      constructor.
    + assert (HD : Disjoint_Computed_Actions (CA_ReadConc s l) (CA_WriteAbs s0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H4; inversion H4; reflexivity.
    + assert (HD : Disjoint_Computed_Actions (CA_ReadConc s l) (CA_WriteConc s0 l0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H6; inversion H6; reflexivity.
    + eapply IHDA_in_Theta; eauto.
      apply Ext_disjoint_sets in H1; destruct H1; assumption.
    + eapply IHDA_in_Theta; eauto.
      apply Ext_disjoint_sets in H1; destruct H1; assumption.  
  - generalize dependent e1.  
    dependent induction H3; intros; inversion H1; subst.
    + assert (HD : Disjoint_Computed_Actions (CA_WriteAbs s) (CA_AllocAbs s0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H5; inversion H5; reflexivity.
    + assert (HD : Disjoint_Computed_Actions (CA_WriteAbs s) (CA_ReadAbs s0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H5; inversion H5; reflexivity.
    + assert (HD : Disjoint_Computed_Actions (CA_WriteAbs s) (CA_ReadConc s0 l0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H5; inversion H5; reflexivity.
    + assert (HD : Disjoint_Computed_Actions (CA_WriteAbs s) (CA_WriteAbs s0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H5; inversion H5; reflexivity.
    + assert (HD : Disjoint_Computed_Actions (CA_WriteAbs s) (CA_WriteConc s0 l0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H5; inversion H5; reflexivity.
    + eapply IHDA_in_Theta; eauto.
      apply Ext_disjoint_sets in H1; destruct H1; assumption.
    + eapply IHDA_in_Theta; eauto.
      apply Ext_disjoint_sets in H1; destruct H1; assumption.
  - generalize dependent e1.  
    dependent induction H3; intros; inversion H1; subst.
    + assert (HD : Disjoint_Computed_Actions (CA_WriteConc s l) (CA_AllocAbs s0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H4; inversion H4; reflexivity.
    +  assert (HD : Disjoint_Computed_Actions (CA_WriteConc s l) (CA_ReadAbs s0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H4; inversion H4; reflexivity. 
    + assert (HD : Disjoint_Computed_Actions (CA_WriteConc s l) (CA_ReadConc s0 l0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H6. inversion H6. reflexivity.
    + assert (HD : Disjoint_Computed_Actions (CA_WriteConc s l) (CA_WriteAbs s0)) by (apply H2; auto).
      inversion HD; subst.
    + assert (HD : Disjoint_Computed_Actions (CA_WriteConc s l) (CA_WriteConc s0 l0)) by (apply H2; auto).
      inversion HD; subst.
      constructor. contradict H6. inversion H6. reflexivity.
    + eapply IHDA_in_Theta; eauto.
      apply Ext_disjoint_sets in H1; destruct H1; assumption.
    + eapply IHDA_in_Theta; eauto.
      apply Ext_disjoint_sets in H1; destruct H1; assumption.
  -  apply Ext_disjoint_sets_2 in H1; destruct H1.
     eapply IHDA_in_Theta with (e1:=acts); eauto.
  -  apply Ext_disjoint_sets_2 in H1; destruct H1.
     eapply IHDA_in_Theta with (e1:=acts); eauto.  
Qed.
    
Lemma Disjoint_computed_disjoint_dynamic_action:
  forall e1 e2 phi1 phi2 p1 p2,
    phi1 ⊑ Some e1 ->
    phi2 ⊑ Some e2 ->
    Disjoint_Sets_Computed_Actions e1 e2 -> 
    In p1 (phi_as_list phi1) ->
    In p2 (phi_as_list phi2) -> 
    Disjoint_Dynamic p1 p2.
Proof.
  intros e1 e2 phi1 phi2 p1 p2 H1 H2 H3 H4 H5.
  generalize dependent phi2.
  dependent induction H1; intros; simpl in *.
  - contradiction.
  - destruct H4; subst.
    + dependent induction H2; simpl in H5.
      * contradiction.
      * destruct H5; [subst | contradiction ].
        eapply Disjoint_da_in_theta; eauto.
      * apply in_app_or in H5. destruct H5.
        { eapply  IHPhi_Theta_Soundness1; eauto. }
        { eapply  IHPhi_Theta_Soundness2; eauto. }
      * apply in_app_or in H5. destruct H5.
        { eapply  IHPhi_Theta_Soundness1; eauto. }
        { eapply  IHPhi_Theta_Soundness2; eauto. }
    + contradiction.
  - apply in_app_or in H4. destruct H4.
    + eapply  IHPhi_Theta_Soundness1; eauto.
    + eapply  IHPhi_Theta_Soundness2; eauto.
  - apply in_app_or in H4. destruct H4.
    + eapply  IHPhi_Theta_Soundness1; eauto.
    + eapply  IHPhi_Theta_Soundness2; eauto.
Qed.


Lemma Ext_Conflict_sets_1 :
  forall e acts a,
    Conflict_Sets_Computed_Actions e acts \/ Conflict_Sets_Computed_Actions e a ->
    Conflict_Sets_Computed_Actions e (set_union acts a).
Proof.
  intros e acts a H. destruct H.
  - inversion H; subst.
    econstructor; eauto. apply Union_introl. assumption.
  - inversion H; subst.
    econstructor; eauto. apply Union_intror. assumption. 
Qed.

Lemma Ext_Conflict_sets_2 :
  forall e acts a,
    Conflict_Sets_Computed_Actions acts e \/ Conflict_Sets_Computed_Actions a e ->
    Conflict_Sets_Computed_Actions (set_union acts a) e.
Proof.
  intros e acts a H. destruct H.
  - inversion H; subst.
    econstructor; eauto. apply Union_introl. assumption.
  - inversion H; subst.
    econstructor; eauto. apply Union_intror. assumption. 
Qed.

Lemma Conflict_da_in_theta_read :
  forall r l v e0 e,
    DA_in_Theta (DA_Write r l v) (Some e0) ->
    DA_in_Theta (DA_Read r l v) (Some e) ->
    Conflict_Sets_Computed_Actions e e0. 
Proof.
  intros.
  generalize dependent e0.
  dependent induction H0; intros.
  - dependent induction H0; intros.
    + econstructor; eauto. constructor.
    + econstructor; eauto. constructor. 
    + apply Ext_Conflict_sets_1. left. eapply IHDA_in_Theta; eauto.
    + apply Ext_Conflict_sets_1. right. eapply IHDA_in_Theta; eauto.
  - dependent induction H0; intros.
    + econstructor; eauto. constructor.
    + econstructor; eauto. constructor. 
    + apply Ext_Conflict_sets_1. left. eapply IHDA_in_Theta; eauto.
    + apply Ext_Conflict_sets_1. right. eapply IHDA_in_Theta; eauto.
  - apply Ext_Conflict_sets_2.  left. eapply IHDA_in_Theta; eauto.
  - apply Ext_Conflict_sets_2.  right. eapply IHDA_in_Theta; eauto.
Qed.

Lemma Conflict_da_in_theta_write :
  forall r l v e0 e,
    DA_in_Theta (DA_Write r l v) (Some e0) ->
    DA_in_Theta (DA_Write r l v) (Some e) ->
    Conflict_Sets_Computed_Actions e e0. 
Proof.
  intros.
  generalize dependent e0.
  dependent induction H0; intros.
  - dependent induction H0; intros.
    + econstructor; eauto. constructor.
    + econstructor; eauto. constructor. 
    + apply Ext_Conflict_sets_1. left. eapply IHDA_in_Theta; eauto.
    + apply Ext_Conflict_sets_1. right. eapply IHDA_in_Theta; eauto.
  - dependent induction H0; intros.
    + econstructor; eauto. constructor.
    + econstructor; eauto. constructor. 
    + apply Ext_Conflict_sets_1. left. eapply IHDA_in_Theta; eauto.
    + apply Ext_Conflict_sets_1. right. eapply IHDA_in_Theta; eauto.
  - apply Ext_Conflict_sets_2.  left. eapply IHDA_in_Theta; eauto.
  - apply Ext_Conflict_sets_2.  right. eapply IHDA_in_Theta; eauto.
Qed.

Lemma Conflict_computed_conflict_dynamic_action_write:
  forall phi1 phi2 e e0 r l v,
  phi1 ⊑ Some e ->
  phi2 ⊑ Some e0 ->
  In (DA_Write r l v) (phi_as_list phi1) ->
  In (DA_Write r l v) (phi_as_list phi2) ->
  Conflict_Sets_Computed_Actions e e0.
Proof.
  intros. generalize dependent phi2.
  dependent induction phi1; simpl in *.
  - contradiction.
  - intuition; subst.
    dependent induction H1; simpl in *.
    + contradiction.
    + intuition; subst. inversion H0; subst.
      eapply Conflict_da_in_theta_write; eauto.
    + apply in_app_or in H2. destruct H2; [eapply IHPhi_Theta_Soundness1 | eapply IHPhi_Theta_Soundness2] ; eauto.
    + apply in_app_or in H2. destruct H2; [eapply IHPhi_Theta_Soundness1 | eapply IHPhi_Theta_Soundness2] ; eauto.   
  - inversion H; apply in_app_or in H1. destruct H1; [eapply IHphi1_1 | eapply IHphi1_2] ; eauto.
  - inversion H; apply in_app_or in H1. destruct H1; [eapply IHphi1_1 | eapply IHphi1_2] ; eauto.
Qed.

Lemma Conflict_computed_conflict_dynamic_action_read:
  forall phi1 phi2 e e0 r l v,
  phi1 ⊑ Some e ->
  phi2 ⊑ Some e0 ->
  In (DA_Write r l v) (phi_as_list phi2) ->
  In (DA_Read r l v) (phi_as_list phi1) ->
  Conflict_Sets_Computed_Actions e e0.
Proof.
  intros. generalize dependent phi2.
  dependent induction phi1; simpl in *.
  - contradiction.
  - intuition; subst.
    dependent induction H1; simpl in *.
    + contradiction.
    + intuition; subst. inversion H0; subst.
      eapply Conflict_da_in_theta_read; eauto.
    + apply in_app_or in H2. destruct H2; [eapply IHPhi_Theta_Soundness1 | eapply IHPhi_Theta_Soundness2] ; eauto.
    + apply in_app_or in H2. destruct H2; [eapply IHPhi_Theta_Soundness1 | eapply IHPhi_Theta_Soundness2] ; eauto.   
  - inversion H; apply in_app_or in H2. destruct H2; [eapply IHphi1_1 | eapply IHphi1_2] ; eauto.
  - inversion H; apply in_app_or in H2. destruct H2; [eapply IHphi1_1 | eapply IHphi1_2] ; eauto.
Qed.

Lemma Det_trace_from_readonly :
  forall phi,
    ReadOnlyPhi phi ->
    Det_Trace phi.
Proof.
  intros phi H.
  dependent induction H.
  - constructor.
  - constructor.
  - constructor; auto.
  - constructor; auto. split. 
    + generalize dependent phi2.
      dependent induction IHReadOnlyPhi1; intros.
      * intro. inversion H1. inversion H2.
      * { dependent induction IHReadOnlyPhi2.
          - intro. inversion H1. inversion H3.
          - inversion H; inversion H0; subst.
            intro. simpl in H1. inversion H1; subst.
            inversion H2; subst; [ | inversion H5].  inversion H3; subst; [ | inversion H5].
            inversion H4.
          - simpl in *. replace (da :: nil) with (phi_as_list (Phi_Elem da))  by (simpl; reflexivity).
            inversion H0; subst.
            apply Conflictness_and_app_l. split; [apply IHIHReadOnlyPhi2_1 | apply IHIHReadOnlyPhi2_2]; assumption.
          - simpl in *. replace (da :: nil) with (phi_as_list (Phi_Elem da))  by (simpl; reflexivity).
            inversion H0; subst.
            apply Conflictness_and_app_l. split; [apply IHIHReadOnlyPhi2_1 | apply IHIHReadOnlyPhi2_2]; assumption. }
      * inversion H; subst.
        apply Conflictness_and_app_r. split; [apply IHIHReadOnlyPhi1_1 | apply IHIHReadOnlyPhi1_2]; assumption.
      * inversion H; subst.
        apply Conflictness_and_app_r. split; [apply IHIHReadOnlyPhi1_1 | apply IHIHReadOnlyPhi1_2]; assumption.
    + generalize dependent phi2.
      dependent induction IHReadOnlyPhi1; intros.
      * constructor. intros. inversion H1.
      * { dependent induction IHReadOnlyPhi2.
          - constructor. intros. inversion H2.
          - inversion H; inversion H0; subst.
            constructor. intros. simpl in *. intuition; subst.
            constructor.
          - simpl.  replace (da :: nil) with (phi_as_list (Phi_Elem da))  by (simpl; reflexivity).
            inversion H0; subst.
            apply Disjointness_and_app_l.  split; [apply IHIHReadOnlyPhi2_1 | apply IHIHReadOnlyPhi2_2]; assumption.
          - simpl.  replace (da :: nil) with (phi_as_list (Phi_Elem da))  by (simpl; reflexivity).
            inversion H0; subst.
            apply Disjointness_and_app_l.  split; [apply IHIHReadOnlyPhi2_1 | apply IHIHReadOnlyPhi2_2]; assumption. }
      * inversion H; subst.
        apply Disjointness_and_app_r. split; [apply IHIHReadOnlyPhi1_1 | apply IHIHReadOnlyPhi1_2]; assumption.
      * inversion H; subst.
        apply Disjointness_and_app_r. split; [apply IHIHReadOnlyPhi1_1 | apply IHIHReadOnlyPhi1_2]; assumption.  
Qed.

Lemma Read_only_no_conflicts:
  forall phi1 phi2,
    ReadOnlyPhi phi1 ->
    ReadOnlyPhi phi2 ->
   ~ Conflict_Traces (phi_as_list phi1) (phi_as_list phi2).
Proof.
  intros phi1 phi2 H1 H2.
  generalize dependent phi2.
  dependent induction phi1; intros.
  - intro. dependent destruction H. inversion H.
  - generalize dependent d.
    dependent induction H2; intros.
    + intro. inversion H. inversion H2.
    + intro. inversion H1; subst. simpl in H.
      inversion H; subst.
      inversion H0; subst; [ | inversion H4].
      inversion H2; subst; [ | inversion H4].
      inversion H3.
    + simpl. replace (d :: nil) with (phi_as_list (Phi_Elem d)) by (simpl; reflexivity).
      apply Conflictness_and_app_l. split; [apply IHReadOnlyPhi1 | apply IHReadOnlyPhi2]; assumption.
    + simpl. replace (d :: nil) with (phi_as_list (Phi_Elem d)) by (simpl; reflexivity).
      apply Conflictness_and_app_l. split; [apply IHReadOnlyPhi1 | apply IHReadOnlyPhi2]; assumption.
  - simpl. apply Conflictness_and_app_r.
    inversion H1; subst.
    split; [apply IHphi1_1 | apply IHphi1_2]; assumption.  
  - simpl. apply Conflictness_and_app_r.
    inversion H1; subst.
    split; [apply IHphi1_1 | apply IHphi1_2]; assumption.
Qed.

Lemma Read_only_disjointness:
  forall phi1 phi2,
    ReadOnlyPhi phi1 ->
    ReadOnlyPhi phi2 ->
    Disjoint_Traces (phi_as_list phi1) (phi_as_list phi2).
Proof.
  intros phi1 phi2 H. generalize phi2.
  dependent induction H; intros.
  - constructor. intros. inversion H0.
  - constructor. dependent induction H; intros; simpl in *.
    + inversion H0.
    + intuition; subst. constructor.
    + intuition; subst. apply in_app_or in H2. destruct H2; [apply IHReadOnlyPhi1 | apply IHReadOnlyPhi2]; intuition.
    + intuition; subst. apply in_app_or in H2. destruct H2; [apply IHReadOnlyPhi1 | apply IHReadOnlyPhi2]; intuition.
  - simpl. apply Disjointness_and_app_r. split; auto.
  - simpl. apply Disjointness_and_app_r. split; auto.
Qed.    
  
Lemma Det_par_trace_from_readonly :
  forall phi1 phi2,
    ReadOnlyPhi phi1 ->
    ReadOnlyPhi phi2 ->
    Det_Trace (Phi_Par phi1 phi2).
Proof.
  intros phi1 phi2 H1 H2.
  generalize dependent phi2.
  dependent induction H1; intros; constructor.
  - constructor.
  - dependent induction phi2.
    + constructor.
    + constructor; assumption.
    + inversion H2; constructor; [apply IHphi2_1 | apply IHphi2_2 |]; try assumption.
      split; [apply Read_only_no_conflicts | apply Read_only_disjointness]; assumption.
    + inversion H2; constructor; [apply IHphi2_1 | apply IHphi2_2 ]; assumption.
  - split; simpl.
    + intro. inversion H; subst. inversion H0.
    + econstructor; intros. inversion H.
  - constructor.
  - dependent induction H2; try (solve [constructor; auto]).
    constructor; auto.
    split; [apply Read_only_no_conflicts | apply Read_only_disjointness]; assumption.
  - split; simpl.
    + dependent induction H2.
      * intro. inversion H. inversion H1.
      * intro. simpl in H. inversion H; subst.
        { inversion H2; subst.
          - inversion H1; inversion H3.
          - inversion H1; inversion H3. }
      * simpl. replace (DA_Read r a v :: nil) with (phi_as_list (Phi_Elem (DA_Read r a v))) by (simpl; reflexivity).
        apply Conflictness_and_app_l. split; auto.
      * simpl. replace (DA_Read r a v :: nil) with (phi_as_list (Phi_Elem (DA_Read r a v))) by (simpl; reflexivity).
        apply Conflictness_and_app_l. split; auto.
    + dependent induction H2; simpl.
      * constructor; intros. inversion H0.
      * econstructor; intros.
        inversion H; subst; [| inversion H1]. inversion H0; subst; [| inversion H1]. constructor.
      * simpl. replace (DA_Read r a v :: nil) with (phi_as_list (Phi_Elem (DA_Read r a v))) by (simpl; reflexivity).
        apply Disjointness_and_app_l.  split; auto.
      * simpl. replace (DA_Read r a v :: nil) with (phi_as_list (Phi_Elem (DA_Read r a v))) by (simpl; reflexivity).
        apply Disjointness_and_app_l.  split; auto.
  - constructor; apply Det_trace_from_readonly; auto.
  - apply Det_trace_from_readonly; auto.
  - split; simpl.
    + dependent induction H2.
      * intro. inversion H. inversion H1.
      * intro. simpl in H. inversion H; subst.
        { inversion H2; subst.
          - inversion H1; inversion H3.
          - inversion H1; inversion H3. }
      * replace (phi_as_list phi1 ++ phi_as_list phi2) with (phi_as_list (Phi_Seq phi1 phi2)) by (simpl; reflexivity).
        apply Conflictness_and_app_l. split; auto.
      * replace (phi_as_list phi1 ++ phi_as_list phi2) with (phi_as_list (Phi_Seq phi1 phi2)) by (simpl; reflexivity).
        apply Conflictness_and_app_l. split; auto.
    + dependent induction H2; simpl.
      * constructor; intros. inversion H0.
      * replace (DA_Read r a v :: nil) with (phi_as_list (Phi_Elem (DA_Read r a v))) by (simpl; reflexivity). 
        assert (ReadOnlyPhi (Phi_Elem (DA_Read r a v))) by constructor.
        apply IHReadOnlyPhi1 in H. inversion H; subst.
        destruct H4; apply  Disjointness_and_app_r. split; [ auto | ].
        assert (ReadOnlyPhi (Phi_Elem (DA_Read r a v))) by constructor.
        apply IHReadOnlyPhi2 in H4. inversion H4; subst.
        destruct H9. auto.
      * replace (phi_as_list phi1 ++ phi_as_list phi2) with (phi_as_list (Phi_Seq phi1 phi2)) by (simpl; reflexivity).
        apply Disjointness_and_app_l.  split; auto.
      * replace (phi_as_list phi1 ++ phi_as_list phi2) with (phi_as_list (Phi_Seq phi1 phi2)) by (simpl; reflexivity).
        apply Disjointness_and_app_l.  split; auto.
  - apply IHReadOnlyPhi1 in H1_0. assumption.
  - apply Det_trace_from_readonly; auto.
  - split; simpl. 
    + dependent induction H2.
      * intro. inversion H. inversion H1.
      * intro. simpl in H. inversion H; subst.
        { inversion H2; subst.
          - inversion H1; inversion H3.
          - inversion H1; inversion H3. }
      * replace (phi_as_list phi1 ++ phi_as_list phi2) with (phi_as_list (Phi_Par phi1 phi2)) by (simpl; reflexivity).
        apply Conflictness_and_app_l. split; auto.
      * replace (phi_as_list phi1 ++ phi_as_list phi2) with (phi_as_list (Phi_Par phi1 phi2)) by (simpl; reflexivity).
        apply Conflictness_and_app_l. split; auto.
     + dependent induction H2; simpl.
      * constructor; intros. inversion H0.
      * replace (DA_Read r a v :: nil) with (phi_as_list (Phi_Elem (DA_Read r a v))) by (simpl; reflexivity).
        assert (ReadOnlyPhi (Phi_Elem (DA_Read r a v))) by constructor.
        apply IHReadOnlyPhi1 in H. inversion H; subst. destruct H4.
        apply Disjointness_and_app_r. split; [auto |].
        assert (ReadOnlyPhi (Phi_Elem (DA_Read r a v))) by constructor.
        apply IHReadOnlyPhi2 in H4. inversion H4; subst. destruct H9.
        assumption.        
      * replace (phi_as_list phi1 ++ phi_as_list phi2) with (phi_as_list (Phi_Par phi1 phi2)) by (simpl; reflexivity).
        apply Disjointness_and_app_l.  split; auto.
      * replace (phi_as_list phi1 ++ phi_as_list phi2) with (phi_as_list (Phi_Par phi1 phi2)) by (simpl; reflexivity).
        apply Disjointness_and_app_l.  split; auto.
Qed.
     

Lemma Det_trace_from_theta :
  forall theta1 theta2 phi1 phi2,
    phi1 ⊑ theta1 ->
    phi2 ⊑ theta2 ->
    Disjointness theta1 theta2 /\ not (Conflictness theta1 theta2) -> 
    Det_Trace phi1 ->
    Det_Trace phi2 ->
    Det_Trace (Phi_Par phi1 phi2).
Proof.
  intros theta1 theta2 phi1 phi2 H1 H2 [HDisj HConf] HDet1 HDet2.
  constructor; [assumption | assumption | split].
  - intro. dependent induction H. inversion H3; subst. apply HConf.
    + destruct theta1; destruct theta2; constructor.
      eapply Conflict_computed_conflict_dynamic_action_read; eauto. 
    + destruct theta1 ; [ | apply HConf; constructor ].
      destruct theta2 ; [ | apply HConf; constructor ].    
      apply HConf. constructor. eapply Conflict_computed_conflict_dynamic_action_write; eauto.
  - destruct theta1; [ | dependent destruction HDisj].
    destruct theta2; [ | dependent destruction HDisj]. 
    dependent destruction HDisj. constructor; intros.
    eapply Disjoint_computed_disjoint_dynamic_action with (e1:=e) (e2:=e0); eauto.
Qed.

Lemma unique_heap :
  forall (heap heap1 heap2: Heap) (acts_mu1 acts_mu2: Phi) (theta1 theta2 : Theta),
    acts_mu1 ⊑ theta1 ->
    acts_mu2 ⊑ theta2 ->
    Disjointness theta1 theta2 /\ not (Conflictness theta1 theta2) ->
    Det_Trace acts_mu1 ->
    Det_Trace acts_mu2 ->
    (Phi_Par acts_mu1 acts_mu2, heap) ==>* (Phi_Nil, heap2) ->
    (Phi_Par acts_mu1 acts_mu2, heap) ==>* (Phi_Nil, heap1) ->
    H.Equal heap1 heap2.
Proof.
  intros.
  eapply Diamond_Term_Walk; eauto.
  eapply Det_trace_from_theta; eauto.
Qed.

Lemma unique_heap_new :
  forall (heapa heapb heap1 heap2: Heap) (acts_mu1 acts_mu2: Phi) (theta1 theta2 : Theta),
    acts_mu1 ⊑ theta1 ->
    acts_mu2 ⊑ theta2 ->
    Disjointness theta1 theta2 /\ not (Conflictness theta1 theta2) ->
    Det_Trace acts_mu1 ->
    Det_Trace acts_mu2 ->
    H.Equal heapa heapb ->
    (Phi_Par acts_mu1 acts_mu2, heapa) ==>* (Phi_Nil, heap1) ->
    (Phi_Par acts_mu1 acts_mu2, heapb) ==>* (Phi_Nil, heap2) ->
    H.Equal heap1 heap2.
Proof.
  intros.
  eapply Diamond_Term_Walk_new; eauto.
  eapply Det_trace_from_theta; eauto.
Qed.


Theorem Dynamic_DetTrace :
  forall heap rgns env exp heap' val' phi',
    (heap, rgns, env, exp) ⇓ (heap', val', phi') ->
    Det_Trace phi'.
Proof.
  intros heap rgs evn exp heap' val' phi' HStep.
  dependent induction HStep;
  try (solve [repeat constructor; try (eapply IHHStep; reflexivity); try (eapply IHHStep1; reflexivity); try (eapply IHHStep2; reflexivity); try (eapply IHHStep3; reflexivity); try assumption]).
  constructor.
  * eapply Det_par_trace_from_readonly; try eassumption.
  * eapply Det_trace_from_theta; try eassumption.
    + eapply IHHStep3; reflexivity.
    + eapply IHHStep4; reflexivity.
Qed.

Lemma Equal_heap_equal:
  forall (heap1 heap2 : Heap),
    heap1 = heap2 -> H.Equal heap1 heap2.
Proof.
  intros heap1 heap2 H. subst. apply HMapP.Equal_refl.
Qed.

Theorem DynamicDeterminism_ext : 
  forall heap_a heap_b rgns env exp heap1 heap2 val1 val2 acts1 acts2,
    H.Equal heap_a heap_b ->
    (heap_a, rgns, env, exp) ⇓ (heap1, val1, acts1) ->
    (heap_b, rgns, env, exp) ⇓ (heap2, val2, acts2) ->
    H.Equal heap1 heap2 /\ val1 = val2 /\ acts1 = acts2.
Proof.
  intros heap_a heap_b rgns env exp heap1 heap2 val1 val2 acts1 acts2 Heq Dyn1. 
  generalize dependent acts2; generalize dependent val2; generalize dependent heap2. generalize dependent heap_b;
  dependent induction Dyn1; intros heap_b Heq heap2 val2 acts2 Dyn2; inversion Dyn2; subst;
  try (solve [intuition]).
  - intuition. rewrite H in H1. inversion H1; subst. reflexivity.
  - assert ( RH1 : H.Equal fheap fheap0 /\ Cls (env', rho', Mu f x ec' ee') = Cls (env'0, rho'0, Mu f0 x0 ec'0 ee'0) /\ facts = facts0 )
      by (eapply IHDyn1_1; eauto).
    destruct RH1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1. subst.
    assert ( RH2 : H.Equal aheap aheap0 /\ v = v0 /\ aacts = aacts0) by (eapply IHDyn1_2; eauto).
    destruct RH2 as [h_eq_2 [v_eq_2 a_eq_2]]; subst. 
    
    assert ( RH3 : H.Equal heap1 heap2 /\ val1 = val2 /\ bacts = bacts0).
    eapply IHDyn1_3; eauto. 
    destruct RH3 as [h_eq_3 [v_eq_3 a_eq_3]]; subst.
    auto.
  - admit.
  - admit.
  - assert (HR1 : H.Equal heap_a heap_b /\ Eff theta1 = Eff theta0 /\ acts_eff1 = acts_eff0) by (eapply IHDyn1_1; eauto).
    destruct HR1 as [h_eq_1 [v_eq_1 a_eq_1]]. inversion v_eq_1. subst.
    assert (HR2 : H.Equal heap_a heap_b /\ Eff theta2 = Eff theta3 /\ acts_eff2 = acts_eff3) by (eapply IHDyn1_2; eauto).
    destruct HR2 as [h_eq_2 [v_eq_2 a_eq_2]]. inversion v_eq_2. subst.
    assert (HR3 : H.Equal heap_mu1 heap_mu0 /\ Num v1 = Num v0 /\ acts_mu1 = acts_mu0)  by (eapply IHDyn1_3; eauto). 
    inversion HR3 as [h_eq_3 [v_eq_3 a_eq_3]]. inversion v_eq_3. 
    assert (HR4 : H.Equal heap_mu2 heap_mu3 /\ Num v2 = Num v3 /\ acts_mu2 = acts_mu3)  by (eapply IHDyn1_4; eauto). 
    inversion HR4 as [h_eq_4 [v_eq_4 a_eq_4]]. inversion v_eq_4. subst.
    intuition. eapply unique_heap_new with (heapa := heap_a) (heapb := heap_b) (theta1:=theta0) (theta2:=theta3); eauto.
    + assert (Det_Trace (Phi_Par acts_mu0 acts_mu3))
                  by (eapply Det_trace_from_theta; eauto; [ apply Dynamic_DetTrace in Dyn1_3 | apply Dynamic_DetTrace in Dyn1_4]; assumption);
      now inversion H11.
    + assert (Det_Trace (Phi_Par acts_mu0 acts_mu3))
                  by (eapply Det_trace_from_theta; eauto; [ apply Dynamic_DetTrace in Dyn1_3 | apply Dynamic_DetTrace in Dyn1_4]; assumption);
      now inversion H11.
  - 
Admitted.
    
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
      by (eapply IHDyn1_1; [ reflexivity | assumption]). inversion RH1. subst.
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
    
    do 3 f_equal.

    assert (H.Equal heap1 heap2) by
    (eapply unique_heap with (theta1:=theta0) (theta2:=theta3); eauto;
     try (solve [assert (Det_Trace (Phi_Par acts_mu0 acts_mu3))
                  by (eapply Det_trace_from_theta; eauto; [ apply Dynamic_DetTrace in Dyn1_3 | apply Dynamic_DetTrace in Dyn1_4]; assumption);
                  now inversion H5
                ])).
    
    admit.
    
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


