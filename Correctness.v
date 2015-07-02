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


Definition isPrime := Bool true.
Definition rho_var := Rgn2_FVar true false "r"%char.
Definition x_var := "x"%char.
Definition f := "f"%char.
Definition rho := "r"%char.

Definition incr_body := Cond (isPrime)
                             (Assign rho_var (Var x_var) (Plus (Const 1) (DeRef rho_var (Var x_var))))
                             (Assign rho_var (Var x_var) (Var x_var)).

Definition incr_eff := ∅ ⊕ ((∅ ⊕ (∅ ⊕ (ReadConc (Var x_var)))) ⊕ (WriteConc (Var x_var))).

Definition incr_abs := Lambda rho (Mu f x_var (incr_body) (incr_eff)). 

Lemma incr_incr_eff_tfp : BackTriangle2 incr_body incr_eff.
Proof.
  unfold incr_body, incr_eff.
  apply Cond_Cond_2.
  - apply Bool_Pure.
  - apply Ref_Write_Conc.
    + apply Var_Pure.
    + apply Plus_Concat.
      * apply Num_Pure.
      * apply Ref_Read_Conc.
        { apply Var_Pure. }
  - apply Ref_Write_Conc.
    + apply Var_Pure.
    + apply Var_Pure. 
Qed. 

Definition Correctness_2 (ea : Expr) (ee : Expr) :
  forall (h h' h'' : Heap) (env : Env) (rho : Rho) (p p' : Phi) (v : Val) (eff : Theta),
    (h, env, rho, ea) ⇓ (h', v, p) ->
    (h, env, rho, ee) ⇓ (h, Eff eff, p') -> 
    forall stty ctxt rgns ty static,
      TcEnv (stty, rho, env, ctxt) -> 
      TcExp (stty, ctxt, rgns, ea, ty, static) ->    
      TcHeap (h, stty) ->
      TcRho (rho, rgns) ->
      (BackTriangle2 ea ee) -> p ⊑ eff.
Proof.
  intros h h' h'' env rho p p' v eff Exprs.
  generalize dependent eff.
  generalize dependent p'.
  generalize dependent ee.
  dependent induction Exprs;
  intros edesc p' eff Specs stty ctxt rgns ty static Henv Hexp Hheap HRho Back;
  inversion Specs; subst; inversion Back; inversion Hexp; subst;
  try (solve [apply PTS_Nil | apply PhiInThetaTop]).  
  - assert (facts ⊑ Some empty_set).
    eapply IHExprs1 with (ee:=∅); eauto; constructor.
    
    assert (aacts ⊑ Some empty_set).
    eapply IHExprs2 with (p':=Phi_Nil); eauto.
    + constructor.
    + admit.
    + apply EmptyIsNil in H; subst. apply EmptyIsNil in H1; subst.
      rewrite Phi_Seq_Nil_R. rewrite Phi_Seq_Nil_L.

      assert (clsTcVal : exists stty',  
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (fheap, stty')
               /\ TcVal (stty', Cls (env', rho', Mu f0 x ec' ee'), subst_rho rho (Ty2_Arrow tya effc ty effe Ty2_Effect))) 
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
      rewrite <- H9 in TcVal_cls.
      do 2 rewrite subst_rho_arrow in H9. inversion H9. 
      rewrite <- H1 in TcVal_v'.
      
      eapply IHExprs3 with (stty := sttya) (p':=Phi_Nil); eauto.
      * admit.
      * apply update_env; simpl.
        eapply ext_stores__env; eauto.
        { apply update_env; eauto. }
        { eassumption. }
      * eapply ext_stores__exp; eauto. 
  - assert (facts ⊑ Some empty_set) by (eapply IHExprs1  with (ee:=∅); eauto; constructor).
    assert (aacts ⊑ Some empty_set).
    eapply IHExprs2 with (p':=Phi_Nil); eauto.
    + constructor.
    + admit.
    + apply EmptyIsNil in H; subst. apply EmptyIsNil in H1; subst.
      rewrite Phi_Seq_Nil_R. rewrite Phi_Seq_Nil_L.

      assert (clsTcVal : exists stty',  
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (fheap, stty')
               /\ TcVal (stty', Cls (env', rho', Mu f0 x ec' ee'), subst_rho rho (Ty2_Arrow tya effc ty effe Ty2_Effect))) 
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
      rewrite <- H8 in TcVal_cls.
      do 2 rewrite subst_rho_arrow in H8. inversion H8. 
      rewrite <- H1 in TcVal_v'.
      
      eapply IHExprs3 with (stty := sttya) (p':=Phi_Nil); eauto.
      * admit.
      * apply update_env; simpl.
        eapply ext_stores__env; eauto.
        { apply update_env; eauto. }
        { eassumption. }
      * eapply ext_stores__exp; eauto. 
  - assert (facts ⊑ Some empty_set) by (eapply IHExprs1  with (ee:=∅); eauto; constructor).
    assert (aacts ⊑ Some empty_set).
    eapply IHExprs2 with (p':=Phi_Nil); eauto.
    + constructor.
    + admit.
    + apply EmptyIsNil in H; subst. apply EmptyIsNil in H0; subst.
      rewrite Phi_Seq_Nil_R. rewrite Phi_Seq_Nil_L.

      assert (clsTcVal : exists stty',  
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (fheap, stty')
               /\ TcVal (stty', Cls (env', rho', Mu f0 x ec' ee'), subst_rho rho (Ty2_Arrow tya effc ty effe Ty2_Effect))) 
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
      rewrite <- H11 in TcVal_cls.
      do 2 rewrite subst_rho_arrow in H11. inversion H11. 
      rewrite <- H0 in TcVal_v'.
      
      eapply IHExprs3 with (stty := sttya) (p':=Phi_Nil); eauto.
      * admit.
      * apply update_env; simpl.
        eapply ext_stores__env; eauto.
        { apply update_env; eauto. }
        { eassumption. }
      * eapply ext_stores__exp; eauto. 
  - assert (facts ⊑ Some empty_set) by (eapply IHExprs1  with (ee:=∅); eauto; constructor).
    assert (aacts ⊑ Some empty_set).
    eapply IHExprs2 with (p':=Phi_Nil); eauto.
    + constructor.
    + admit.
    + apply EmptyIsNil in H; subst. apply EmptyIsNil in H0; subst.
      rewrite Phi_Seq_Nil_R. rewrite Phi_Seq_Nil_L.

      assert (clsTcVal : exists stty',  
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (fheap, stty')
               /\ TcVal (stty', Cls (env', rho', Mu f0 x ec' ee'), subst_rho rho (Ty2_Arrow tya effc ty effe Ty2_Effect))) 
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
      rewrite <- H10 in TcVal_cls.
      do 2 rewrite subst_rho_arrow in H10. inversion H10. 
      rewrite <- H0 in TcVal_v'.
      
      eapply IHExprs3 with (stty := sttya) (p':=Phi_Nil); eauto.
      * admit.
      * apply update_env; simpl.
        eapply ext_stores__env; eauto.
        { apply update_env; eauto. }
        { eassumption. }
      * eapply ext_stores__exp; eauto. 
  - assert (facts ⊑ Some empty_set) by (eapply IHExprs1  with (ee:=∅); eauto; constructor).
    assert (aacts ⊑ Some empty_set).
    eapply IHExprs2 with (p':=Phi_Nil); eauto.
    + constructor.
    + admit.
    + apply EmptyIsNil in H; subst. apply EmptyIsNil in H0; subst.
      rewrite Phi_Seq_Nil_R. rewrite Phi_Seq_Nil_L.

      assert (clsTcVal : exists stty',  
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (fheap, stty')
               /\ TcVal (stty', Cls (env', rho', Mu f0 x ec' ee'), subst_rho rho (Ty2_Arrow tya effc ty effe Ty2_Effect))) 
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
      rewrite <- H11 in TcVal_cls.
      do 2 rewrite subst_rho_arrow in H11. inversion H11. 
      rewrite <- H0 in TcVal_v'.
      
      eapply IHExprs3 with (stty := sttya) (p':=Phi_Nil); eauto.
      * admit.
      * apply update_env; simpl.
        eapply ext_stores__env; eauto.
        { apply update_env; eauto. }
        { eassumption. }
      * eapply ext_stores__exp; eauto. 
  - assert (facts ⊑ Some empty_set) by (eapply IHExprs1  with (ee:=∅); eauto; constructor).
    assert (aacts ⊑ Some empty_set).
    eapply IHExprs2 with (p':=Phi_Nil); eauto.
    + constructor.
    + admit.
    + apply EmptyIsNil in H; subst. apply EmptyIsNil in H0; subst.
      rewrite Phi_Seq_Nil_R. rewrite Phi_Seq_Nil_L.

      assert (clsTcVal : exists stty',  
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (fheap, stty')
               /\ TcVal (stty', Cls (env', rho', Mu f0 x ec' ee'), subst_rho rho (Ty2_Arrow tya effc ty effe Ty2_Effect))) 
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
      rewrite <- H10 in TcVal_cls.
      do 2 rewrite subst_rho_arrow in H10. inversion H10. 
      rewrite <- H0 in TcVal_v'.
      
      eapply IHExprs3 with (stty := sttya) (p':=Phi_Nil); eauto.
      * admit.
      * apply update_env; simpl.
        eapply ext_stores__env; eauto.
        { apply update_env; eauto. }
        { eassumption. }
      * eapply ext_stores__exp; eauto. 
  - assert (facts ⊑ Some empty_set) by (eapply IHExprs1  with (ee:=∅); eauto; constructor).
    assert (aacts ⊑ Some empty_set).
    eapply IHExprs2 with (p':=Phi_Nil); eauto.
    + constructor.
    + admit.
    + apply EmptyIsNil in H; subst. apply EmptyIsNil in H0; subst.
      rewrite Phi_Seq_Nil_R. rewrite Phi_Seq_Nil_L.

      assert (clsTcVal : exists stty',  
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (fheap, stty')
               /\ TcVal (stty', Cls (env', rho', Mu f0 x ec' ee'), subst_rho rho (Ty2_Arrow tya effc ty effe Ty2_Effect))) 
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
      rewrite <- H11 in TcVal_cls.
      do 2 rewrite subst_rho_arrow in H11. inversion H11. 
      rewrite <- H0 in TcVal_v'.
      
      eapply IHExprs3 with (stty := sttya) (p':=Phi_Nil); eauto.
      * admit.
      * apply update_env; simpl.
        eapply ext_stores__env; eauto.
        { apply update_env; eauto. }
        { eassumption. }
      * eapply ext_stores__exp; eauto. 
  - assert (facts ⊑ Some empty_set) by (eapply IHExprs1  with (ee:=∅); eauto; constructor).
    assert (aacts ⊑ Some empty_set).
    eapply IHExprs2 with (p':=Phi_Nil); eauto.
    + constructor.
    + admit.
    + apply EmptyIsNil in H; subst. apply EmptyIsNil in H0; subst.
      rewrite Phi_Seq_Nil_R. rewrite Phi_Seq_Nil_L.

      assert (clsTcVal : exists stty',  
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (fheap, stty')
               /\ TcVal (stty', Cls (env', rho', Mu f0 x ec' ee'), subst_rho rho (Ty2_Arrow tya effc ty effe Ty2_Effect))) 
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
      rewrite <- H10 in TcVal_cls.
      do 2 rewrite subst_rho_arrow in H10. inversion H10. 
      rewrite <- H0 in TcVal_v'.
      
      eapply IHExprs3 with (stty := sttya) (p':=Phi_Nil); eauto.
      * admit.
      * apply update_env; simpl.
        eapply ext_stores__env; eauto.
        { apply update_env; eauto. }
        { eassumption. }
      * eapply ext_stores__exp; eauto. 
  - assert (facts ⊑ Some empty_set) by (eapply IHExprs1  with (ee:=∅); eauto; constructor).
    assert (aacts ⊑ Some empty_set).
    eapply IHExprs2 with (p':=Phi_Nil); eauto.
    + constructor.
    + admit.
    + apply EmptyIsNil in H; subst. apply EmptyIsNil in H0; subst.
      rewrite Phi_Seq_Nil_R. rewrite Phi_Seq_Nil_L.

      assert (clsTcVal : exists stty',  
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (fheap, stty')
               /\ TcVal (stty', Cls (env', rho', Mu f0 x ec' ee'), subst_rho rho (Ty2_Arrow tya effc ty effe Ty2_Effect))) 
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
      rewrite <- H10 in TcVal_cls.
      do 2 rewrite subst_rho_arrow in H10. inversion H10. 
      rewrite <- H0 in TcVal_v'.
      
      eapply IHExprs3 with (stty := sttya) (p':=Phi_Nil); eauto.
      * admit.
      * apply update_env; simpl.
        eapply ext_stores__env; eauto.
        { apply update_env; eauto. }
        { eassumption. }
      * eapply ext_stores__exp; eauto. 
  - assert (facts ⊑ Some empty_set) by (eapply IHExprs1  with (ee:=∅); eauto; constructor).
    assert (aacts ⊑ Some empty_set).
    eapply IHExprs2 with (p':=Phi_Nil); eauto.
    + constructor.
    + admit.
    + apply EmptyIsNil in H; subst. apply EmptyIsNil in H0; subst.
      rewrite Phi_Seq_Nil_R. rewrite Phi_Seq_Nil_L.

      assert (clsTcVal : exists stty',  
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (fheap, stty')
               /\ TcVal (stty', Cls (env', rho', Mu f0 x ec' ee'), subst_rho rho (Ty2_Arrow tya effc ty effe Ty2_Effect))) 
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
      rewrite <- H9 in TcVal_cls.
      do 2 rewrite subst_rho_arrow in H9. inversion H9. 
      rewrite <- H0 in TcVal_v'.
      
      eapply IHExprs3 with (stty := sttya) (p':=Phi_Nil); eauto.
      * admit.
      * apply update_env; simpl.
        eapply ext_stores__env; eauto.
        { apply update_env; eauto. }
        { eassumption. }
      * eapply ext_stores__exp; eauto. 
  - assert (facts ⊑ Some empty_set) by (eapply IHExprs1  with (ee:=∅); eauto; constructor).
    assert (aacts ⊑ Some empty_set).
    eapply IHExprs2 with (p':=Phi_Nil); eauto.
    + constructor.
    + admit.
    + apply EmptyIsNil in H; subst. apply EmptyIsNil in H0; subst.
      rewrite Phi_Seq_Nil_R. rewrite Phi_Seq_Nil_L.

      assert (clsTcVal : exists stty',  
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (fheap, stty')
               /\ TcVal (stty', Cls (env', rho', Mu f0 x ec' ee'), subst_rho rho (Ty2_Arrow tya effc ty effe Ty2_Effect))) 
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
      rewrite <- H10 in TcVal_cls.
      do 2 rewrite subst_rho_arrow in H10. inversion H10. 
      rewrite <- H0 in TcVal_v'.
      
      eapply IHExprs3 with (stty := sttya) (p':=Phi_Nil); eauto.
      * admit.
      * apply update_env; simpl.
        eapply ext_stores__env; eauto.
        { apply update_env; eauto. }
        { eassumption. }
      * eapply ext_stores__exp; eauto. 
  - assert (facts ⊑ Some empty_set) by (eapply IHExprs1  with (ee:=∅); eauto; constructor).
    assert (aacts ⊑ Some empty_set).
    eapply IHExprs2 with (p':=Phi_Nil); eauto.
    + constructor.
    + admit.
    + apply EmptyIsNil in H; subst. apply EmptyIsNil in H0; subst.
      rewrite Phi_Seq_Nil_R. rewrite Phi_Seq_Nil_L.

      assert (clsTcVal : exists stty',  
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (fheap, stty')
               /\ TcVal (stty', Cls (env', rho', Mu f0 x ec' ee'), subst_rho rho (Ty2_Arrow tya effc ty effe Ty2_Effect))) 
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
      rewrite <- H9 in TcVal_cls.
      do 2 rewrite subst_rho_arrow in H9. inversion H9. 
      rewrite <- H0 in TcVal_v'.
      
      eapply IHExprs3 with (stty := sttya) (p':=Phi_Nil); eauto.
      * admit.
      * apply update_env; simpl.
        eapply ext_stores__env; eauto.
        { apply update_env; eauto. }
        { eassumption. }
      * eapply ext_stores__exp; eauto. 
  - assert (facts ⊑ Some empty_set) by (eapply IHExprs1  with (ee:=∅); eauto; constructor).
    assert (aacts ⊑ Some empty_set).
    eapply IHExprs2 with (p':=Phi_Nil); eauto.
    + constructor.
    + admit.
    + apply EmptyIsNil in H; subst. apply EmptyIsNil in H0; subst.
      rewrite Phi_Seq_Nil_R. rewrite Phi_Seq_Nil_L.

      assert (clsTcVal : exists stty',  
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (fheap, stty')
               /\ TcVal (stty', Cls (env', rho', Mu f0 x ec' ee'), subst_rho rho (Ty2_Arrow tya effc ty effe Ty2_Effect))) 
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
      rewrite <- H11 in TcVal_cls.
      do 2 rewrite subst_rho_arrow in H11. inversion H11. 
      rewrite <- H0 in TcVal_v'.
      
      eapply IHExprs3 with (stty := sttya) (p':=Phi_Nil); eauto.
      * admit.
      * apply update_env; simpl.
        eapply ext_stores__env; eauto.
        { apply update_env; eauto. }
        { eassumption. }
      * eapply ext_stores__exp; eauto. 
  - assert (facts ⊑ Some empty_set) by (eapply IHExprs1  with (ee:=∅); eauto; constructor).
    assert (aacts ⊑ Some empty_set).
    eapply IHExprs2 with (p':=Phi_Nil); eauto.
    + constructor.
    + admit.
    + apply EmptyIsNil in H; subst. apply EmptyIsNil in H0; subst.
      rewrite Phi_Seq_Nil_R. rewrite Phi_Seq_Nil_L.

      assert (clsTcVal : exists stty',  
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (fheap, stty')
               /\ TcVal (stty', Cls (env', rho', Mu f0 x ec' ee'), subst_rho rho (Ty2_Arrow tya effc ty effe Ty2_Effect))) 
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
      rewrite <- H10 in TcVal_cls.
      do 2 rewrite subst_rho_arrow in H10. inversion H10. 
      rewrite <- H0 in TcVal_v'.
      
      eapply IHExprs3 with (stty := sttya) (p':=Phi_Nil); eauto.
      * admit.
      * apply update_env; simpl.
        eapply ext_stores__env; eauto.
        { apply update_env; eauto. }
        { eassumption. }
      * eapply ext_stores__exp; eauto.
  - assert (facts ⊑ Some empty_set) by (eapply IHExprs1  with (ee:=∅); eauto; constructor).
    assert (aacts ⊑ Some empty_set).
    eapply IHExprs2 with (p':=Phi_Nil); eauto.
    + constructor.
    + admit.
    + apply EmptyIsNil in H; subst. apply EmptyIsNil in H1; subst.
      rewrite Phi_Seq_Nil_R. rewrite Phi_Seq_Nil_L.

      assert (clsTcVal : exists stty',  
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (fheap, stty')
               /\ TcVal (stty', Cls (env', rho', Mu f0 x ec' ee'), subst_rho rho (Ty2_Arrow tya effc ty effe Ty2_Effect))) 
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
      rewrite <- H9 in TcVal_cls.
      do 2 rewrite subst_rho_arrow in H9. inversion H9. 
      rewrite <- H1 in TcVal_v'.
      
      eapply IHExprs3 with (stty := sttya) (p':=Phi_Nil); eauto.
      * admit.
      * apply update_env; simpl.
        eapply ext_stores__env; eauto.
        { apply update_env; eauto. }
        { eassumption. }
      * eapply ext_stores__exp; eauto.       
  - assert (facts ⊑ Some empty_set) by (eapply IHExprs1  with (ee:=∅); eauto; constructor).
    assert (aacts ⊑ Some empty_set).
    eapply IHExprs2 with (p':=Phi_Nil); eauto.
    + constructor.
    + admit.
    + apply EmptyIsNil in H; subst. apply EmptyIsNil in H1; subst.
      rewrite Phi_Seq_Nil_R. rewrite Phi_Seq_Nil_L.

      assert (clsTcVal : exists stty',  
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (fheap, stty')
               /\ TcVal (stty', Cls (env', rho', Mu f0 x ec' ee'), subst_rho rho (Ty2_Arrow tya effc ty effe Ty2_Effect))) 
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
      rewrite <- H8 in TcVal_cls.
      do 2 rewrite subst_rho_arrow in H8. inversion H8. 
      rewrite <- H1 in TcVal_v'.
      
      eapply IHExprs3 with (stty := sttya) (p':=Phi_Nil); eauto.
      * admit.
      * apply update_env; simpl.
        eapply ext_stores__env; eauto.
        { apply update_env; eauto. }
        { eassumption. }
      * eapply ext_stores__exp; eauto. 
  -  assert (facts ⊑ Some empty_set) by (eapply IHExprs1  with (ee:=∅); eauto; constructor).
    assert (aacts ⊑ Some empty_set).
    eapply IHExprs2 with (p':=Phi_Nil); eauto.
    + constructor.
    + admit.
    + apply EmptyIsNil in H; subst. apply EmptyIsNil in H1; subst.
      rewrite Phi_Seq_Nil_R. rewrite Phi_Seq_Nil_L.

      assert (clsTcVal : exists stty',  
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (fheap, stty')
               /\ TcVal (stty', Cls (env', rho', Mu f0 x ec' ee'), subst_rho rho (Ty2_Arrow tya effc ty effe Ty2_Effect))) 
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
      rewrite <- H9 in TcVal_cls.
      do 2 rewrite subst_rho_arrow in H9. inversion H9. 
      rewrite <- H1 in TcVal_v'.
      
      eapply IHExprs3 with (stty := sttya) (p':=Phi_Nil); eauto.
      * admit.
      * apply update_env; simpl.
        eapply ext_stores__env; eauto.
        { apply update_env; eauto. }
        { eassumption. }
      * eapply ext_stores__exp; eauto. 
  -  assert (facts ⊑ Some empty_set) by (eapply IHExprs1  with (ee:=∅); eauto; constructor).
    assert (aacts ⊑ Some empty_set).
    eapply IHExprs2 with (p':=Phi_Nil); eauto.
    + constructor.
    + admit.
    + apply EmptyIsNil in H; subst. apply EmptyIsNil in H1; subst.
      rewrite Phi_Seq_Nil_R. rewrite Phi_Seq_Nil_L.

      assert (clsTcVal : exists stty',  
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (fheap, stty')
               /\ TcVal (stty', Cls (env', rho', Mu f0 x ec' ee'), subst_rho rho (Ty2_Arrow tya effc ty effe Ty2_Effect))) 
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
      rewrite <- H8 in TcVal_cls.
      do 2 rewrite subst_rho_arrow in H8. inversion H8. 
      rewrite <- H1 in TcVal_v'.
      
      eapply IHExprs3 with (stty := sttya) (p':=Phi_Nil); eauto.
      * admit.
      * apply update_env; simpl.
        eapply ext_stores__env; eauto.
        { apply update_env; eauto. }
        { eassumption. }
      * eapply ext_stores__exp; eauto.
  -  assert (facts ⊑ Some empty_set) by (eapply IHExprs1  with (ee:=∅); eauto; constructor).
    assert (aacts ⊑ Some empty_set).
    eapply IHExprs2 with (p':=Phi_Nil); eauto.
    + constructor.
    + admit.
    + apply EmptyIsNil in H; subst. apply EmptyIsNil in H1; subst.
      rewrite Phi_Seq_Nil_R. rewrite Phi_Seq_Nil_L.

      assert (clsTcVal : exists stty',  
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (fheap, stty')
               /\ TcVal (stty', Cls (env', rho', Mu f0 x ec' ee'), subst_rho rho (Ty2_Arrow tya effc ty effe Ty2_Effect))) 
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
      rewrite <- H9 in TcVal_cls.
      do 2 rewrite subst_rho_arrow in H9. inversion H9. 
      rewrite <- H1 in TcVal_v'.
      
      eapply IHExprs3 with (stty := sttya) (p':=Phi_Nil); eauto.
      * admit.
      * apply update_env; simpl.
        eapply ext_stores__env; eauto.
        { apply update_env; eauto. }
        { eassumption. }
      * eapply ext_stores__exp; eauto.       
  -  assert (facts ⊑ Some empty_set) by (eapply IHExprs1  with (ee:=∅); eauto; constructor).
    assert (aacts ⊑ Some empty_set).
    eapply IHExprs2 with (p':=Phi_Nil); eauto.
    + constructor.
    + admit.
    + apply EmptyIsNil in H; subst. apply EmptyIsNil in H1; subst.
      rewrite Phi_Seq_Nil_R. rewrite Phi_Seq_Nil_L.

      assert (clsTcVal : exists stty',  
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (fheap, stty')
               /\ TcVal (stty', Cls (env', rho', Mu f0 x ec' ee'), subst_rho rho (Ty2_Arrow tya effc ty effe Ty2_Effect))) 
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
      rewrite <- H8 in TcVal_cls.
      do 2 rewrite subst_rho_arrow in H8. inversion H8. 
      rewrite <- H1 in TcVal_v'.
      
      eapply IHExprs3 with (stty := sttya) (p':=Phi_Nil); eauto.
      * admit.
      * apply update_env; simpl.
        eapply ext_stores__env; eauto.
        { apply update_env; eauto. }
        { eassumption. }
      * eapply ext_stores__exp; eauto. 
  -  assert (facts ⊑ Some empty_set) by (eapply IHExprs1  with (ee:=∅); eauto; constructor).
    assert (aacts ⊑ Some empty_set).
    eapply IHExprs2 with (p':=Phi_Nil); eauto.
    + constructor.
    + admit.
    + apply EmptyIsNil in H; subst. apply EmptyIsNil in H0; subst.
      rewrite Phi_Seq_Nil_R. rewrite Phi_Seq_Nil_L.

      assert (clsTcVal : exists stty',  
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (fheap, stty')
               /\ TcVal (stty', Cls (env', rho', Mu f0 x ec' ee'), subst_rho rho (Ty2_Arrow tya effc ty effe Ty2_Effect))) 
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
      rewrite <- H9 in TcVal_cls.
      do 2 rewrite subst_rho_arrow in H9. inversion H9. 
      rewrite <- H0 in TcVal_v'.
      
      eapply IHExprs3 with (stty := sttya) (p':=Phi_Nil); eauto.
      * admit.
      * apply update_env; simpl.
        eapply ext_stores__env; eauto.
        { apply update_env; eauto. }
        { eassumption. }
      * eapply ext_stores__exp; eauto.
  -  assert (facts ⊑ Some empty_set) by (eapply IHExprs1  with (ee:=∅); eauto; constructor).
    assert (aacts ⊑ Some empty_set).
    eapply IHExprs2 with (p':=Phi_Nil); eauto.
    + constructor.
    + admit.
    + apply EmptyIsNil in H; subst. apply EmptyIsNil in H0; subst.
      rewrite Phi_Seq_Nil_R. rewrite Phi_Seq_Nil_L.

      assert (clsTcVal : exists stty',  
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (fheap, stty')
               /\ TcVal (stty', Cls (env', rho', Mu f0 x ec' ee'), subst_rho rho (Ty2_Arrow tya effc ty effe Ty2_Effect))) 
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
      rewrite <- H8 in TcVal_cls.
      do 2 rewrite subst_rho_arrow in H8. inversion H8. 
      rewrite <- H0 in TcVal_v'.
      
      eapply IHExprs3 with (stty := sttya) (p':=Phi_Nil); eauto.
      * admit.
      * apply update_env; simpl.
        eapply ext_stores__env; eauto.
        { apply update_env; eauto. }
        { eassumption. }
      * eapply ext_stores__exp; eauto.
  -  assert (facts ⊑ Some empty_set) by (eapply IHExprs1  with (ee:=∅); eauto; constructor).
    assert (aacts ⊑ Some empty_set).
    eapply IHExprs2 with (p':=Phi_Nil); eauto.
    + constructor.
    + admit.
    + apply EmptyIsNil in H; subst. apply EmptyIsNil in H0; subst.
      rewrite Phi_Seq_Nil_R. rewrite Phi_Seq_Nil_L.

      assert (clsTcVal : exists stty',  
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (fheap, stty')
               /\ TcVal (stty', Cls (env', rho', Mu f0 x ec' ee'), subst_rho rho (Ty2_Arrow tya effc ty effe Ty2_Effect))) 
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
      rewrite <- H9 in TcVal_cls.
      do 2 rewrite subst_rho_arrow in H9. inversion H9. 
      rewrite <- H0 in TcVal_v'.
      
      eapply IHExprs3 with (stty := sttya) (p':=Phi_Nil); eauto.
      * admit.
      * apply update_env; simpl.
        eapply ext_stores__env; eauto.
        { apply update_env; eauto. }
        { eassumption. }
      * eapply ext_stores__exp; eauto.
  -  assert (facts ⊑ Some empty_set) by (eapply IHExprs1  with (ee:=∅); eauto; constructor).
    assert (aacts ⊑ Some empty_set).
    eapply IHExprs2 with (p':=Phi_Nil); eauto.
    + constructor.
    + admit.
    + apply EmptyIsNil in H; subst. apply EmptyIsNil in H0; subst.
      rewrite Phi_Seq_Nil_R. rewrite Phi_Seq_Nil_L.

      assert (clsTcVal : exists stty',  
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (fheap, stty')
               /\ TcVal (stty', Cls (env', rho', Mu f0 x ec' ee'), subst_rho rho (Ty2_Arrow tya effc ty effe Ty2_Effect))) 
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
      rewrite <- H8 in TcVal_cls.
      do 2 rewrite subst_rho_arrow in H8. inversion H8. 
      rewrite <- H0 in TcVal_v'.
      
      eapply IHExprs3 with (stty := sttya) (p':=Phi_Nil); eauto.
      * admit.
      * apply update_env; simpl.
        eapply ext_stores__env; eauto.
        { apply update_env; eauto. }
        { eassumption. }
      * eapply ext_stores__exp; eauto.
  - apply PTS_Seq.      
    + apply EnsembleUnionComp. 
      * assert (facts ⊑ Some empty_set).
        eapply IHExprs1 with (ee:=∅) (p':=Phi_Nil); eauto. constructor. constructor.
        apply EmptyInAnyTheta. assumption.
      * assert (aacts ⊑ Some empty_set).  
        eapply IHExprs2 with (ee:=∅) (p':=Phi_Nil); eauto;
        assert (ReadOnlyPhi facts) by admit;
        assert (h=fheap) by (eapply ReadOnlyTracePreservesHeap_1; eauto). constructor.
        { rewrite <- H0. assumption. }
        apply EmptyInAnyTheta. assumption.
    +  assert (clsTcVal : exists stty',  
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (fheap, stty')
               /\ TcVal (stty', Cls (env', rho', Mu f0 x ec' ee'), subst_rho rho (Ty2_Arrow tya effc ty effe Ty2_Effect))) 
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
      rewrite <- H10 in TcVal_cls.
      do 2 rewrite subst_rho_arrow in H10. inversion H10. 
      rewrite <- H0 in TcVal_v'.    

      eapply IHExprs3 with (stty := sttya) (p':=phib); eauto.
      * admit.
      * apply update_env; simpl.
        eapply ext_stores__env; eauto.
        { apply update_env; eauto. }
        { eassumption. }
      * eapply ext_stores__exp; eauto.
  -  apply PTS_Seq.      
    + apply EnsembleUnionComp. 
      * assert (facts ⊑ Some empty_set).
        eapply IHExprs1 with (ee:=∅) (p':=Phi_Nil); eauto. constructor. 
        apply EmptyInAnyTheta. assumption.
      * assert (aacts ⊑ Some empty_set).  
        eapply IHExprs2 with (ee:=∅) (p':=Phi_Nil); eauto;
        assert (ReadOnlyPhi facts) by admit;
        assert (h=fheap) by (eapply ReadOnlyTracePreservesHeap_1; eauto). constructor.
        { rewrite <- H0. assumption. }
        apply EmptyInAnyTheta. assumption.
    +  assert (clsTcVal : exists stty',  
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (fheap, stty')
               /\ TcVal (stty', Cls (env', rho', Mu f0 x ec' ee'), subst_rho rho (Ty2_Arrow tya effc ty effe Ty2_Effect))) 
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
      rewrite <- H9 in TcVal_cls.
      do 2 rewrite subst_rho_arrow in H9. inversion H9. 
      rewrite <- H0 in TcVal_v'.    

      eapply IHExprs3 with (stty := sttya) (p':=phib); eauto.
      * admit.
      * apply update_env; simpl.
        eapply ext_stores__env; eauto.
        { apply update_env; eauto. }
        { eassumption. }
      * eapply ext_stores__exp; eauto.
     

    
  - apply PTS_Seq.      
    + apply EnsembleUnionComp. 
      * assert (facts ⊑ effa).
        eapply IHExprs1 with (ee:=a) (p':=phia); eauto.  assumption.
      * inversion H6; subst.
        assert (aacts ⊑ effa2).  
        eapply IHExprs2 with (ee:=effa0) (p':=phia0); eauto;
        assert (ReadOnlyPhi facts) by admit;
        assert (h=fheap) by (eapply ReadOnlyTracePreservesHeap_1; eauto); now rewrite <- H0.
        apply Theta_introl. assumption.
    + inversion H6; subst. 
      apply Theta_intror. apply Theta_intror.

      assert (clsTcVal : exists stty',  
             (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t')
               /\ TcHeap (fheap, stty')
               /\ TcVal (stty', Cls (env', rho', Mu f0 x ec' ee'), subst_rho rho (Ty2_Arrow tya effc ty effe Ty2_Effect))) 
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
      rewrite <- H10 in TcVal_cls.
      do 2 rewrite subst_rho_arrow in H10. inversion H10. 
      rewrite <- H0 in TcVal_v'. 
      
      eapply IHExprs3 with (stty := sttya) (p' := phib0); eauto.
      * admit.
      * apply update_env; simpl.
        eapply ext_stores__env; eauto.
        { apply update_env; eauto. }
        { eassumption. }
      * eapply ext_stores__exp; eauto.
  - admit.
  - admit.
  - assert (facts ⊑ Some empty_set) by (eapply IHExprs1 with (ee:=∅); eauto; constructor);
    apply EmptyIsNil in H0; subst;
    apply PTS_Seq; [apply PTS_Nil |]; 
    inversion  Exprs1; subst;
    inversion H7; subst;
    eapply IHExprs2 with (ea:=eb) (p':= Phi_Nil) (static:=effr0); eauto using extended_rho, update_rho.
    admit. 
  - assert (facts ⊑ Some empty_set) by (eapply IHExprs1 with (ee:=∅); eauto; constructor);
    apply EmptyIsNil in H0; subst;
    apply PTS_Seq; [apply PTS_Nil |]; 
    inversion  Exprs1; subst;
    inversion H7; subst;
    eapply IHExprs2 with (ea:=eb) (p':= Phi_Nil) (static:=effr0); eauto using extended_rho, update_rho.
    inversion H7; subst. 
    admit.
  - admit.
  - admit.
  - admit.
  - admit.  
  - admit.
  - admit. 
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - assert (cacts ⊑ Some empty_set) by (eapply IHExprs1; eauto; constructor).
    apply EmptyIsNil in H; subst.
    apply PTS_Seq; [apply PTS_Nil |].
    eapply IHExprs2; eauto. econstructor. assumption.
    assert (h=cheap) by (eapply EmptyTracePreservesHeap_1; eauto; now apply EmptyIsNil); subst.
    assumption.
  - assert (cacts ⊑ Some empty_set) by (eapply IHExprs1; eauto; constructor).
    apply EmptyIsNil in H; subst.
    apply PTS_Seq; [apply PTS_Nil |].
    assert (h=cheap) by (eapply EmptyTracePreservesHeap_1; eauto; now apply EmptyIsNil); subst. 
    eapply IHExprs2 with (ee:= Mu_App ef0 ea) (p':=Phi_Seq (Phi_Seq facts aacts) bacts); eauto.
  - assert (cacts ⊑ Some empty_set) by (eapply IHExprs1; eauto; constructor).
    apply EmptyIsNil in H; subst.
    apply PTS_Seq; [apply PTS_Nil |].
    assert (h=cheap) by (eapply EmptyTracePreservesHeap_1; eauto; now apply EmptyIsNil); subst. 
    eapply IHExprs2 with (ee:= Rgn_App er w) (p':=  Phi_Seq facts bacts); eauto.
  - assert (cacts ⊑ Some empty_set) by (eapply IHExprs1; eauto; constructor).
    apply EmptyIsNil in H; subst.
    apply PTS_Seq; [apply PTS_Nil |].
    assert (h=cheap) by (eapply EmptyTracePreservesHeap_1; eauto; now apply EmptyIsNil); subst.
    eapply IHExprs2 with (ee:= Eff_App ef0 ea) (p':= Phi_Seq (Phi_Seq facts aacts) bacts); eauto.
  - assert (cacts ⊑ Some empty_set) by (eapply IHExprs1; eauto; constructor).
    apply EmptyIsNil in H; subst.
    apply PTS_Seq; [apply PTS_Nil |]. inversion Exprs1; subst.  inversion H1; subst.
    eapply IHExprs2 with (ee:= et0) (p':= tacts0); eauto.
    + inversion Exprs1; subst.  inversion H1; subst.
      eapply IHExprs2 with (ee:=et0); eauto.
  - assert (cacts ⊑ Some empty_set) by (eapply IHExprs1; eauto; constructor).
    apply EmptyIsNil in H; subst.
    apply PTS_Seq; [apply PTS_Nil |].
    inversion Exprs1; subst; inversion H1; subst.
    eapply IHExprs2 with (ee:= Cond (Bool true) et0 ef0); eauto.
    + eapply IHExprs2 with (ee:=Cond (Var x) et0 ef0) (p':=Phi_Seq Phi_Nil tacts0) ; eauto.
    + eapply IHExprs2 with (ee:=Cond (Mu_App ef1 ea) et0 ef0) (p':=Phi_Seq (Phi_Seq (Phi_Seq facts aacts) bacts) tacts0) ; eauto.
    + eapply IHExprs2 with (ee:=Cond (Rgn_App er w) et0 ef0) (p':=Phi_Seq (Phi_Seq facts bacts) tacts0) ; eauto.
    + eapply IHExprs2 with (ee:=Cond (Eff_App ef1 ea) et0 ef0) (p':=Phi_Seq (Phi_Seq (Phi_Seq facts aacts) bacts) tacts0) ; eauto.
    + eapply IHExprs2 with (ee:=Cond (Cond e et1 ef1) et0 ef0) (p':=Phi_Seq (Phi_Seq cacts tacts1) tacts0) ; eauto.
    + eapply IHExprs2 with (ee:=Cond (Cond e et1 ef1) et0 ef0) (p':=Phi_Seq (Phi_Seq cacts facts) tacts0) ; eauto.
    + eapply IHExprs2 with (ee:=Cond (DeRef w ea) et0 ef0) (p':= Phi_Seq (Phi_Seq aacts (Phi_Elem (DA_Read r l))) tacts0) ; eauto.
    + eapply IHExprs2 with (ee:=Cond (Eq a b) et0 ef0) (p':= Phi_Seq (Phi_Seq lacts racts) tacts0) ; eauto.
    + eapply IHExprs2 with (ee:=Cond (Bool true) et0 ef0) (p':= Phi_Seq Phi_Nil tacts0) ; eauto.   
    + eapply IHExprs2 with (ee:=Cond (Var x0) et0 ef0) (p':= Phi_Seq Phi_Nil tacts0); eauto.
    + eapply IHExprs2 with (ee:=Cond (Mu_App ef1 ea) et0 ef0) (p':= Phi_Seq (Phi_Seq (Phi_Seq facts aacts) bacts) tacts0); eauto.
    + eapply IHExprs2 with (ee:=Cond (Rgn_App er w) et0 ef0) (p':= Phi_Seq (Phi_Seq facts bacts) tacts0); eauto.
    + eapply IHExprs2 with (ee:=Cond (Eff_App ef1 ea) et0 ef0) (p':= Phi_Seq (Phi_Seq (Phi_Seq facts aacts) bacts) tacts0); eauto.
    + eapply IHExprs2 with (ee:=Cond (Cond e et1 ef1) et0 ef0) (p':=  Phi_Seq (Phi_Seq cacts tacts1) tacts0); eauto.
    + eapply IHExprs2 with (ee:=Cond (Cond e et1 ef1) et0 ef0) (p':=  Phi_Seq (Phi_Seq cacts facts) tacts0); eauto.
    + eapply IHExprs2 with (ee:=Cond (DeRef w ea) et0 ef0) (p':= Phi_Seq (Phi_Seq aacts (Phi_Elem (DA_Read r l))) tacts0); eauto.
    + eapply IHExprs2 with (ee:=Cond (Eq a b) et0 ef0) (p':= Phi_Seq (Phi_Seq lacts racts) tacts0); eauto. 
  - assert ( Hbit : (cheap, Bit true, cacts) = (cheap0, Bit false, cacts0) )
      by (eapply DynamicDeterminism; eauto); discriminate Hbit.
  - assert (cacts ⊑ Some empty_set) by (eapply IHExprs1; eauto; constructor).
    apply EmptyIsNil in H; subst.
    apply PTS_Seq; [apply PTS_Nil |]. inversion Exprs1; subst.  inversion H1; subst.
    eapply IHExprs2 with (ee:= Cond (Bool false) et0 ef0) (p':= Phi_Seq Phi_Nil facts); eauto.
    +  eapply IHExprs2 with (ee:=Cond (Var x) et0 ef0) (p':=Phi_Seq Phi_Nil facts) ; eauto.
    +  eapply IHExprs2 with (ee:=Cond (Mu_App ef1 ea) et0 ef0) (p':= Phi_Seq (Phi_Seq (Phi_Seq facts0 aacts) bacts) facts) ; eauto.
    +  eapply IHExprs2 with (ee:= Cond (Rgn_App er w) et0 ef0 ) (p':=Phi_Seq (Phi_Seq facts0 bacts) facts) ; eauto.
    +  eapply IHExprs2 with (ee:= Cond (Eff_App ef1 ea) et0 ef0) (p':= Phi_Seq (Phi_Seq (Phi_Seq facts0 aacts) bacts) facts) ; eauto.
    +   eapply IHExprs2 with (ee:=Cond (Cond e et1 ef1) et0 ef0) (p':=  Phi_Seq (Phi_Seq cacts tacts0) facts); eauto.
    +   eapply IHExprs2 with (ee:=Cond (Cond e et1 ef1) et0 ef0) (p':= Phi_Seq (Phi_Seq cacts facts0) facts); eauto.
    + eapply IHExprs2 with (ee:=Cond (DeRef w ea) et0 ef0) (p':= Phi_Seq (Phi_Seq aacts (Phi_Elem (DA_Read r l))) facts) ; eauto.
    +  eapply IHExprs2 with (ee:=Cond (Eq a b) et0 ef0) (p':= Phi_Seq (Phi_Seq lacts racts) facts); eauto.
    + eapply IHExprs2 with (ee:=Cond e0 et0 ef0) (p':= Phi_Seq cacts0 facts); eauto.  
  - assert (cacts ⊑ Some empty_set) by (eapply IHExprs1; eauto; constructor).
    apply EmptyIsNil in H; subst.
    apply PTS_Seq; [apply PTS_Nil |]. inversion Exprs1; subst.  
    eapply IHExprs2 with (ee:=DeRef w ea); eauto.
    + inversion Exprs1; subst.
      eapply IHExprs2 with (ee:=DeRef w ea); eauto.
  - assert (cacts ⊑ Some empty_set) by (eapply IHExprs1; eauto; constructor).
    apply EmptyIsNil in H; subst.
    apply PTS_Seq; [apply PTS_Nil |]. inversion Exprs1; subst.  
    eapply IHExprs2 with (ee:=AllocAbs w); eauto.
    + inversion Exprs1; subst.
      eapply IHExprs2 with (ee:=AllocAbs w); eauto.
  - assert (cacts ⊑ Some empty_set) by (eapply IHExprs1; eauto; constructor).
    apply EmptyIsNil in H; subst.
    apply PTS_Seq; [apply PTS_Nil |]. inversion Exprs1; subst.  
    eapply IHExprs2 with (ee:=ReadAbs w); eauto.
    + inversion Exprs1; subst.
      eapply IHExprs2 with (ee:=ReadAbs w); eauto.
  - assert (cacts ⊑ Some empty_set) by (eapply IHExprs1; eauto; constructor).
    apply EmptyIsNil in H; subst.
    apply PTS_Seq; [apply PTS_Nil |]. inversion Exprs1; subst.  
    eapply IHExprs2 with (ee:=WriteAbs w); eauto.
    + inversion Exprs1; subst.
      eapply IHExprs2 with (ee:=WriteAbs w); eauto.
  - assert (cacts ⊑ Some empty_set) by (eapply IHExprs1; eauto; constructor).
    apply EmptyIsNil in H; subst.
    apply PTS_Seq; [apply PTS_Nil |]. inversion Exprs1; subst.  
    eapply IHExprs2 with (ee:=ReadConc ea); eauto.
    + inversion Exprs1; subst.
      eapply IHExprs2 with (ee:=ReadConc ea); eauto.
  - assert (cacts ⊑ Some empty_set) by (eapply IHExprs1; eauto; constructor).
    apply EmptyIsNil in H; subst.
    apply PTS_Seq; [apply PTS_Nil |]. inversion Exprs1; subst.  
    eapply IHExprs2 with (ee:=WriteConc ea); eauto.
    + inversion Exprs1; subst.
      eapply IHExprs2 with (ee:=WriteConc ea); eauto.   
  - assert (cacts ⊑ Some empty_set) by (eapply IHExprs1; eauto; constructor).
    apply EmptyIsNil in H; subst.
    apply PTS_Seq; [apply PTS_Nil |]. inversion Exprs1; subst.
    eapply IHExprs2 with (ee:=(a ⊕ b)); eauto.
    + eapply IHExprs2 with (ee:=(a ⊕ b)); eauto.
  -  assert (cacts ⊑ Some empty_set) by (eapply IHExprs1; eauto; constructor).
    apply EmptyIsNil in H; subst.
    apply PTS_Seq; [apply PTS_Nil |]. inversion Exprs1; subst.
    eapply IHExprs2 with (ee:=∅); eauto.
     +  eapply IHExprs2 with (ee:=∅); eauto.
  - assert (cacts ⊑ Some empty_set) by (eapply IHExprs1; eauto; constructor).
    apply EmptyIsNil in H; subst.
    apply PTS_Seq; [apply PTS_Nil |]. inversion Exprs1; subst.
    eapply IHExprs2 with (ee:=(Var x)); eauto.
    + eapply IHExprs2 with (ee:=(Var x)); eauto.
  - assert (cacts ⊑ Some empty_set) by (eapply IHExprs1; eauto; constructor).
    apply EmptyIsNil in H; subst.
    apply PTS_Seq; [apply PTS_Nil |]. inversion Exprs1; subst.
    eapply IHExprs2 with (ee:=Mu_App ef0 ea); eauto.
    + eapply IHExprs2 with (ee:=Mu_App ef0 ea); eauto.
  - assert (cacts ⊑ Some empty_set) by (eapply IHExprs1; eauto; constructor).
    apply EmptyIsNil in H; subst.
    apply PTS_Seq; [apply PTS_Nil |]. inversion Exprs1; subst.
    eapply IHExprs2 with (ee:=Rgn_App er w); eauto.
    + eapply IHExprs2 with (ee:=Rgn_App er w); eauto.
  - assert (cacts ⊑ Some empty_set) by (eapply IHExprs1; eauto; constructor).
    apply EmptyIsNil in H; subst.
    apply PTS_Seq; [apply PTS_Nil |]. inversion Exprs1; subst.
    eapply IHExprs2 with (ee:=Eff_App ef0 ea); eauto.
    + eapply IHExprs2 with (ee:=Eff_App ef0 ea); eauto. 
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  (* 
  - assert (cacts ⊑ Some empty_set) by (eapply IHExprs1; eauto; constructor).
    apply EmptyUnionIsIdentity.
    assert ( Hbit : (cheap, Bit true, cacts) = (cheap0, Bit true, cacts0) )
      by (eapply DynamicDeterminism; eauto); inversion Hbit; subst.
    apply EmptyIsNil in H; subst.
    apply PTS_Seq; [apply PTS_Nil |].
    assert (H_empty : Union_Theta (Some empty_set) eff = eff) by admit; rewrite H_empty. clear H_empty. 
    assert (h=cheap0) by (eapply EmptyTracePreservesHeap_1; eauto; now apply EmptyIsNil); subst.
    eapply IHExprs2 with (ee:=et0); eauto.
  -  assert (cacts ⊑  Some empty_set) by (eapply IHExprs1; eauto; constructor). 
    apply EmptyUnionIsIdentity.
    assert ( Hbit : (cheap, Bit true, cacts) = (cheap0, Bit false, cacts0) )
      by (eapply DynamicDeterminism; eauto); discriminate Hbit.
  - assert (cacts ⊑ Some empty_set) by (eapply IHExprs1; eauto; constructor). 
    apply EmptyUnionIsIdentity.
    assert ( Hbit : (cheap, Bit false, cacts) = (cheap0, Bit true, cacts0) )
      by (eapply DynamicDeterminism; eauto); inversion Hbit; subst.
  - assert (cacts ⊑  Some empty_set) by (eapply IHExprs1; eauto; constructor).
    assert ( Hbit : (cheap, Bit false, cacts) =  (cheap0, Bit false, cacts0) )
      by (eapply DynamicDeterminism; eauto); inversion Hbit; subst.
    assert (h=cheap0) by (eapply EmptyTracePreservesHeap_1; eauto; now apply EmptyIsNil); subst.
     apply EmptyIsNil in H; subst; rewrite Phi_Seq_Nil_L.
    eapply IHExprs2 with (ee:= ef0); eauto. *)     
  - apply EnsembleUnionComp.  
    + eapply IHExprs; eauto.
    + inversion H8; subst. apply PTS_Elem. apply DAT_Alloc_Abs.
      simpl in H; inversion H; subst. inversion H4; subst.
      apply In_singleton.
  - apply EnsembleUnionComp.
    + eapply IHExprs; eauto.
    + apply PTS_Elem; inversion H8; subst.
      inversion H4; rewrite <- H5.
      inversion H.
      apply DAT_Read_Abs; apply In_singleton.
  -  apply EnsembleUnionComp.
     + eapply IHExprs; eauto.
     + apply PTS_Elem; inversion H8; subst.
       assert ( Hnil : (h, Loc (Rgn2_Const true false r0) l0, Phi_Nil) = (h', Loc (Rgn2_Const true false s) l, aacts))
         by (eapply DynamicDeterminism; eauto); inversion Hnil; subst.
       inversion H; subst.
       apply DAT_Read_Conc; apply In_singleton.
  -  apply PTS_Seq.
     +  apply EnsembleUnionComp.
        * eapply IHExprs1; eauto.
        * inversion H7; subst.
          assert (vacts ⊑ effa0). 
          eapply IHExprs2; eauto;  assert (ReadOnlyPhi aacts) by admit.
          { assert (h=heap') by (eapply ReadOnlyTracePreservesHeap_1; eauto; constructor).
            rewrite <- H1; eassumption. }
          { assert (h=heap') by (eapply ReadOnlyTracePreservesHeap_1; eauto).
            rewrite <- H1; eassumption. }
          apply Theta_introl. assumption. 
     + inversion H7; subst.
       assert (Phi_Elem (DA_Write r l) ⊑ effb0).
       apply PTS_Elem; inversion H12; subst.
       inversion H1; subst.
       inversion H; subst.
       apply DAT_Write_Abs; apply In_singleton.
       apply Theta_intror. apply Theta_intror. assumption.
  - apply PTS_Seq.
     + apply EnsembleUnionComp.
       * eapply IHExprs1; eauto.
       * inversion H7; subst.
         assert (vacts ⊑ effa0). 
         eapply IHExprs2; eauto;  assert (ReadOnlyPhi aacts) by admit.
         { assert (h=heap') by (eapply ReadOnlyTracePreservesHeap_1; eauto; constructor).
           rewrite <- H1; eassumption. }
         { assert (h=heap') by (eapply ReadOnlyTracePreservesHeap_1; eauto).
           rewrite <- H1; eassumption. }
         apply Theta_introl. assumption.
     + inversion H7; subst.
       assert (Phi_Elem (DA_Write r l) ⊑ effb0).
       apply PTS_Elem; inversion H12; subst.
       assert ( HD : (heap', Loc (Rgn2_Const true false s) l, aacts) =  (h, Loc (Rgn2_Const true false r0) l0, Phi_Nil))
         by (eapply DynamicDeterminism; eauto). inversion HD; subst.
       inversion H; subst.
       apply DAT_Write_Conc; apply In_singleton.
       apply Theta_intror. apply Theta_intror. assumption.
  - apply EnsembleUnionComp.
    eapply IHExprs1; eauto. eapply IHExprs2 with (p':=phib); eauto;
    assert (ReadOnlyPhi lacts) by admit;
    assert (h=lheap) by (eapply  ReadOnlyTracePreservesHeap_1; eauto); subst; auto.
  - apply EnsembleUnionComp.
    eapply IHExprs1; eauto. eapply IHExprs2 with (p':=phib); eauto;
    assert (ReadOnlyPhi lacts) by admit;
    assert (h=lheap) by (eapply  ReadOnlyTracePreservesHeap_1; eauto); subst; auto.
  - apply EnsembleUnionComp.
    eapply IHExprs1; eauto. eapply IHExprs2 with (p':=phib); eauto;
    assert (ReadOnlyPhi lacts) by admit;
    assert (h=lheap) by (eapply  ReadOnlyTracePreservesHeap_1; eauto); subst; auto.  
Qed.


