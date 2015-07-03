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
Import EffectSoundness.

Definition Correctness_1 (ea : Expr) (ee : Expr) :
  forall (h h' h'' : Heap) (env : Env) (rho : Rho) (p p' : Phi) (v : Val) (eff : Theta),
    (h, env, rho, ea) ⇓ (h', v, p) -> 
    ReadOnlyPhi p' ->
    (h, env, rho, ee) ⇓ (h'', Eff eff, p') -> 
    forall stty ctxt rgns ty static,
      TcEnv (stty, rho, env, ctxt) -> 
      TcExp (stty, ctxt, rgns, ea, ty, static) ->    
      TcHeap (h, stty) ->
      TcRho (rho, rgns) ->
      BackTriangle (stty, ctxt, rgns, ea, ee) -> p ⊑ eff.
Proof.
  intros h h' h'' env rho p p' v eff Exprs.
  generalize dependent eff.
  generalize dependent p'.
  generalize dependent ee.
  dependent induction Exprs;
  intros edesc p' eff HReadOnly Specs stty ctxt rgns ty static Henv Hexp Hheap HRho Back;
  inversion Specs; subst; inversion Back; inversion Hexp; subst; try (solve [apply PTS_Nil | apply PhiInThetaTop]).
  - inversion HReadOnly; subst.
    assert (facts ⊑ effa) by (eapply IHExprs1 with (p':=phia); eauto).
    apply PTS_Seq. 
    + apply PTS_Seq.
      * apply Theta_introl. assumption.
      * inversion H7; subst.
        assert (aacts ⊑ effa2)
          by (eapply IHExprs2 with (p':=phia0); eauto;
              inversion HReadOnly; inversion H13; auto;
              assert (h'' = fheap) by (eapply ReadOnlyTracePreservesHeap_2; eauto); subst; assumption).
        apply Theta_intror. apply Theta_introl. assumption.
    + assert (clsTcVal : exists stty',  
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
      rewrite <- H14 in TcVal_cls.
      do 2 rewrite subst_rho_arrow in H14. inversion H14. 
      rewrite <- H4 in TcVal_v'.
      inversion H7; subst.
      eapply IHExprs3 with (stty := sttya) (ee:=ee') (p' := phib0); eauto;
      inversion H3; subst; auto.
      * admit.
      * apply update_env; simpl.
        eapply ext_stores__env; eauto.
        { apply update_env; eauto. }
        { eassumption. }
      * eapply ext_stores__exp; eauto.
      * eapply ext_stores__bt; eauto.
  - admit.
Admitted.        

