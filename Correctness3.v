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
Require Import Determinism.
Require Import Definitions2.
Require Import CorrectnessLemmas.

Import TypeSoundness.

Definition Correctness_Z :
  forall stty ctxt rgns ea ee,
    BackTriangle (stty, ctxt, rgns, ea, ee) ->
    forall h h' h'' env rho p p' v eff ty static,
      (h, env, rho, ea) ⇓ (h', v, p) ->
      (h, env, rho, ee) ⇓ (h'', Eff eff, p') ->
      ReadOnlyPhi p' ->
      TcHeap (h, stty) ->
      TcRho (rho, rgns) ->
      TcEnv (stty, rho, env, ctxt) -> 
      TcExp (stty, ctxt, rgns, ea, ty, static) ->    
      p ⊑ eff.
Proof.
  intros stty ctxt rgns ea ee BT.
  dependent induction BT; intros.
  - inversion H0; subst.
    apply PTS_Nil.
  - inversion H0; subst.
    apply PTS_Nil.
  - inversion H0; subst.
    apply PTS_Nil.
  - inversion H; subst.
    apply PTS_Nil.
  - inversion H1; subst.
    inversion H7; subst.
    inversion H2; subst.

    assert (clsTcVal : exists stty',  
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (fheap, stty')
               /\ TcVal (stty', Cls (env', rho', Mu f x ec' ee'), subst_rho rho (Ty2_Arrow tya effc ty effe Ty2_Effect))) 
        by (eapply ty_sound; eauto).
    destruct clsTcVal as [sttyb [Weakb [TcHeapb TcVal_cls]]]; eauto.
   
    assert (argTcVal : exists stty',
             (forall l t', ST.find l sttyb = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (aheap, stty')
               /\ TcVal (stty', v0, subst_rho rho tya))
        by (eapply ty_sound; eauto using update_env, ext_stores__env, ext_stores__exp).
      destruct argTcVal as [sttya [Weaka [TcHeapa TcVal_v']]]; eauto.

      
      inversion TcVal_cls as  [ | | | ? ? ? ? ? ? ? TcRho_rho' TcEnv_env' TcExp_abs | | ]; subst. 
      inversion TcExp_abs as [ | | | | ? ? ? ? ? ? ? ? ? TcExp_eb | | | | | | | |  | | | | | | | | | | |  ]; subst.
      rewrite <- H16 in TcVal_cls.
      do 2 rewrite subst_rho_arrow in H16. inversion H16. 
      rewrite <- H9 in TcVal_v'. 

      assert (facts ⊑ Some empty_set).
      admit.
Admitted.
