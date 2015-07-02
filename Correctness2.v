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
Admitted.        
