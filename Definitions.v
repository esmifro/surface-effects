Require Import Coq.Program.Equality.
Require Import Coq.Sets.Ensembles.
Require Import Coq.FSets.FSetAVL.
Require Import Coq.FSets.FSetWeakList.
Require Import Coq.MSets.MSetWeakList.
Require Import Coq.FSets.FSetFacts.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.Natural.Peano.NPeano. 
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Mult.
Require Import Coq.Arith.Plus.
Require Import Coq.Arith.Minus. 
Require Import Coq.Init.Peano.
Require Import Ascii.
Require Import Keys.
Require Import Tactics.

Definition empty_set `{T: Type} := Empty_set T.
Definition singleton_set `{T: Type} (e: T) := Singleton T e.
Definition set_union `{T: Type} (s1 s2: Ensemble T) := Union T s1 s2.
Definition set_elem `{T: Type} (s: Ensemble T) (e: T) := Ensembles.In T s e.
Definition not_set_elem `{T: Type} (s: Ensemble T) (e: T) := Ensembles.Complement T s e.
Definition included `{T: Type} (s1 s2: Ensemble T) := Ensembles.Included T s1 s2.
Definition set_minus `{T: Type} (s: Ensemble T) (e: T)  := Ensembles.Subtract T s e.

(* Static Labels *)
Definition Region :=  nat.

(* Program Variables *)
Definition Name := ascii.
  
Inductive Expr :=
  | Const     : nat -> Expr
  | Bool      : bool -> Expr
  | Var       : Name -> Expr
  | Mu        : Name -> Name -> Expr -> Expr -> Expr
  | Lambda    : Name -> Expr -> Expr                                               
  | Mu_App    : Expr -> Expr -> Expr 
  | Rgn_App   : Expr -> Rgn -> Expr                                     
  | Eff_App   : Expr -> Expr -> Expr
  | Pair_Par  : Expr -> Expr -> Expr -> Expr -> Expr                              
  | Cond      : Expr -> Expr -> Expr -> Expr 
  | Ref       : Rgn -> Expr -> Expr                  
  | DeRef     : Rgn -> Expr -> Expr                     
  | Assign    : Rgn -> Expr -> Expr -> Expr
  | Plus      : Expr -> Expr -> Expr
  | Minus     : Expr -> Expr -> Expr
  | Times     : Expr -> Expr -> Expr
  | Eq        : Expr -> Expr -> Expr
  | AllocAbs  : Rgn -> Expr                         
  | ReadAbs   : Rgn -> Expr
  | WriteAbs  : Rgn -> Expr                               
  | ReadConc  : Region -> Expr -> Expr               
  | WriteConc : Region -> Expr -> Expr
  | Concat    : Expr -> Expr -> Expr
  | Top       : Expr
  | Empty     : Expr
with Rgn := (* w *)
  | Rgn_Const : Region -> Rgn (* s *)
  | Rgn_Var   : Name -> Rgn (* r *). 

Notation "'(|' a ',' b '|)" := (Pair_Par a b) (at level 60).

(* Dynamic Actions; for operational semantics *)
Inductive DynamicAction : Set :=
| DA_Alloc : Region -> nat -> DynamicAction
| DA_Read  : Region -> nat -> DynamicAction
| DA_Write : Region -> nat -> DynamicAction. 

Definition Trace := list DynamicAction. 
Inductive Phi :=
 | Phi_Nil : Phi
 | Phi_Elem : DynamicAction -> Phi                                
 | Phi_Par : Phi -> Phi -> Phi                 
 | Phi_Seq : Phi -> Phi -> Phi.

Definition Empty_Dynamic_Action := Empty_set DynamicAction.
Definition Singleton_Dynamic_Action (e : DynamicAction) :=  Singleton DynamicAction e.
Definition Union_Dynamic_Action (a b : Ensemble DynamicAction) :=  Union DynamicAction a b.

(* Static Actions; for type-and-effect system *)
Inductive StaticAction : Set :=
| SA_Alloc : Rgn -> StaticAction
| SA_Read  : Rgn -> StaticAction
| SA_Write : Rgn -> StaticAction.
Definition Epsilon := Ensemble StaticAction.

Definition Empty_Static_Action := Empty_set StaticAction.
Definition Singleton_Static_Action (e : StaticAction) :=  Singleton StaticAction e.
Definition Union_Static_Action (a b : Ensemble StaticAction) :=  Union StaticAction a b.

(* Computed Actions; for effect specification *)
Inductive ComputedAction : Set :=
| CA_ReadConc  : Region -> nat -> ComputedAction
| CA_WriteConc : Region -> nat -> ComputedAction 
| CA_AllocAbs : Region -> ComputedAction
| CA_ReadAbs  : Region -> ComputedAction
| CA_WriteAbs : Region -> ComputedAction. 
 
 
                   
Definition Theta := option (Ensemble ComputedAction).
Definition Theta_Top : Theta := None.
Definition Theta_Empty : Theta := Some empty_set.

Definition Union_Theta (theta1 theta2 : Theta) := 
  match theta1,theta2 with
    | None, _ => None
    | _, None => None
    | Some acts1, Some acts2 => Some (set_union acts1 acts2)                                    
  end.


Inductive DA_in_Phi : DynamicAction -> Phi -> Prop :=
| DAP_Trace : forall da, DA_in_Phi da (Phi_Elem da)
| DAP_Par   : forall da phi1 phi2, DA_in_Phi da phi1 \/ DA_in_Phi da phi2 -> DA_in_Phi da (Phi_Par phi1 phi2)
| DAP_Seq   : forall da phi1 phi2, DA_in_Phi da phi1 \/ DA_in_Phi da phi2 -> DA_in_Phi da (Phi_Seq phi1 phi2).
  
Inductive DA_in_Theta : DynamicAction -> Theta -> Prop :=
| DAT_Top :
    forall da, DA_in_Theta da None
| DAT_Alloc_Abs :
    forall s l acts,
      set_elem acts (CA_AllocAbs s) ->
      DA_in_Theta (DA_Alloc s l) (Some acts)
| DAT_Read_Abs :
    forall s l acts,
      set_elem acts (CA_ReadAbs s) ->
      DA_in_Theta (DA_Read s l) (Some acts)
| DAT_Read_Conc :
    forall s l acts,
      set_elem acts (CA_ReadConc s l) ->
      DA_in_Theta (DA_Read s l) (Some acts)
| DAT_Write_Abs :
    forall s l acts,
      set_elem acts (CA_WriteAbs s) ->
      DA_in_Theta (DA_Write s l) (Some acts)
| DAT_Write_Conc :
    forall s l acts,
      set_elem acts (CA_WriteConc s l) ->
      DA_in_Theta (DA_Write s l) (Some acts).


Inductive Disjoint_Dynamic : DynamicAction -> DynamicAction -> Prop :=
 | DD_Read_Read   : forall r1 l1 r2 l2, Disjoint_Dynamic (DA_Read r1 l1) (DA_Read r2 l2)
 | DD_Write_Write : forall r1 l1 r2 l2, r1 <> r2 -> l1 <> l2 -> Disjoint_Dynamic (DA_Write r1 l1) (DA_Write r2 l2)
 | DD_Read_Write  : forall r1 l1 r2 l2, r1 <> r2 -> l1 <> l2 -> Disjoint_Dynamic (DA_Read r1 l1) (DA_Write r2 l2)
 | DD_Write_Read  : forall r1 l1 r2 l2, r1 <> r2 -> l1 <> l2 -> Disjoint_Dynamic (DA_Write r1 l1) (DA_Read r2 l2).                                                                                

Inductive Disjoint_Static : StaticAction -> StaticAction -> Prop :=
 | DS_Read_Read   : forall r1 r2, Disjoint_Static (SA_Read r1) (SA_Read r2)
 | DS_Write_Write : forall r1 r2, r1 <> r2 -> Disjoint_Static (SA_Write r1) (SA_Write r2)
 | DS_Read_Write  : forall r1 r2, r1 <> r2 -> Disjoint_Static (SA_Read r1) (SA_Write r2)
 | DS_Write_Read  : forall r1 r2, r1 <> r2 -> Disjoint_Static (SA_Write r1) (SA_Read r2).


Inductive Disjoint_Computed_Actions : ComputedAction -> ComputedAction -> Prop :=
 | D_CA_ReadConc_ReadConc   : forall r1 l1 r2 l2, Disjoint_Computed_Actions (CA_ReadConc r1 l1) (CA_ReadConc r2 l2)
 | D_CA_ReadAbs_ReadConc    : forall r1 r2 l2, Disjoint_Computed_Actions (CA_ReadAbs r1) (CA_ReadConc r2 l2)
 | D_CA_WriteConc_WriteConc : forall r1 l1 r2 l2, r1 <> r2 -> l1 <> l2 -> Disjoint_Computed_Actions (CA_WriteConc l1 r1) (CA_WriteConc r2 l2)
 | D_CA_WriteAbs_WriteConc  : forall r1 r2 l2, r1 <> r2 -> Disjoint_Computed_Actions (CA_WriteAbs r1) (CA_WriteConc r2 l2)
 | D_CA_WriteAbs_WriteAbs   : forall r1 r2, r1 <> r2 -> Disjoint_Computed_Actions (CA_WriteAbs r1) (CA_WriteAbs r2)
 | D_CA_WriteConc_ReadConc  : forall r1 l1 r2 l2, r1 <> r2 -> l1 <> l2 -> Disjoint_Computed_Actions (CA_WriteConc l1 r1) (CA_ReadConc r2 l2)
 | D_CA_WriteConc_ReadAbs   : forall r1 l1 r2, r1 <> r2 -> Disjoint_Computed_Actions (CA_WriteConc r1 l1) (CA_ReadAbs r2)
 | D_CA_WriteAbs_ReadConc  : forall r1 l1 r2 l2, r1 <> r2 -> l1 <> l2 -> Disjoint_Computed_Actions (CA_WriteConc l1 r1) (CA_ReadConc r2 l2)
 | D_CA_WriteAbs_ReadAbs   : forall r1 r2, r1 <> r2 -> Disjoint_Computed_Actions (CA_WriteAbs r1) (CA_ReadAbs r2).

Axiom Disjoint_Computed_Actions_Refl :
  forall ca1 ca2, Disjoint_Computed_Actions ca1 ca2 -> Disjoint_Computed_Actions ca2 ca1.

Inductive Disjoint_Sets_Computed_Actions : Ensemble (ComputedAction) -> Ensemble (ComputedAction) -> Prop :=
 | D_Set_CA  : forall d1 d2 theta1 theta2,
                    set_elem theta1 d1 -> set_elem theta2 d2 -> Disjoint_Computed_Actions d1 d2 -> Disjoint_Sets_Computed_Actions theta1 theta2. 

Inductive Disjointness : Theta -> Theta -> Prop :=
 | D_Empty : forall theta , Disjointness (Some theta) Theta_Empty                                   
 | D_Theta  : forall theta1 theta2, Disjoint_Sets_Computed_Actions theta1 theta2 -> Disjointness (Some theta1) (Some theta2).

Axiom Disjointness_Refl : forall theta1 theta2, Disjointness theta1 theta2 -> Disjointness theta2 theta1.

Inductive Conflict_Computed_Actions : ComputedAction -> ComputedAction -> Prop :=
 | C_Write : forall r l (d : ComputedAction),
                  d = CA_ReadConc r l \/ d = CA_WriteConc r l ->
                  d = CA_ReadAbs r \/ d = CA_WriteConc r l ->
                  d = CA_ReadConc r l \/ d = CA_WriteAbs r ->
                  d = CA_ReadAbs r \/ d = CA_WriteAbs r -> Conflict_Computed_Actions d (CA_WriteConc r l).  

Axiom Conflict_Computed_Actions_Refl :
  forall ca1 ca2, Conflict_Computed_Actions ca1 ca2 -> Conflict_Computed_Actions ca2 ca1.

Inductive Conflict_Sets_Computed_Actions : Ensemble (ComputedAction) -> Ensemble (ComputedAction) -> Prop :=
 | C_Set_CA  : forall d1 d2 theta1 theta2,
                    set_elem theta1 d1 -> set_elem theta2 d2 -> Conflict_Computed_Actions d1 d2 -> Conflict_Sets_Computed_Actions theta1 theta2. 

Inductive Conflictness : Theta -> Theta -> Prop :=
 | C_Top    : forall theta, Conflictness theta Theta_Top
 | C_Theta  : forall theta1 theta2,
                 Conflict_Sets_Computed_Actions theta1 theta2  -> Conflictness (Some theta1) (Some theta2).                                                                                                               

Reserved Notation "phi '⊑' theta" (at level 50, left associativity).
Inductive Phi_Theta_Soundness : Phi -> Theta -> Prop :=
| PTS_Nil :
    forall theta, (Phi_Nil) ⊑ theta
| PTS_Elem : forall da theta,
      DA_in_Theta da theta ->
      (Phi_Elem da) ⊑ theta
| PTS_Seq : forall phi1 phi2 theta,
      phi1 ⊑ theta ->
      phi2 ⊑ theta ->
      Phi_Seq phi1 phi2 ⊑ theta
| PTS_Par : forall phi1 phi2 theta,
      phi1 ⊑ theta ->
      phi2 ⊑ theta ->
      Phi_Par phi1 phi2 ⊑ theta
where "phi '⊑' theta" := (Phi_Theta_Soundness phi theta) : type_scope.

Axiom Phi_Seq_Nil_L : forall phi, Phi_Seq Phi_Nil phi = phi.
Axiom Phi_Seq_Nil_R : forall phi, Phi_Seq phi Phi_Nil = phi.
Axiom Phi_Par_Nil_R : forall phi, Phi_Par Phi_Nil phi = phi.
Axiom Phi_Par_Nil_L : forall phi, Phi_Par Phi_Nil phi = phi.

Lemma EnsembleUnionSym :
  forall (phi : Phi) (theta theta' : Theta),
    phi ⊑ theta -> phi ⊑ (Union_Theta theta theta') /\ phi ⊑ (Union_Theta theta' theta).
Proof.
  intros phi theta theta' H.
  generalize dependent theta'.
  induction H; intros theta'.
  - split; [apply PTS_Nil | apply PTS_Nil]. 
  - destruct theta as [acts|]; destruct theta' as [acts'|]; intuition; simpl;
    try (apply PTS_Elem; inversion H; subst; apply DAT_Top).
    + apply PTS_Elem; inversion H; subst;
      [apply DAT_Alloc_Abs | 
       apply DAT_Read_Abs | apply DAT_Read_Conc |
       apply DAT_Write_Abs | apply DAT_Write_Conc ];
      apply Union_introl; assumption.
    + apply PTS_Elem; inversion H; subst;
      [apply DAT_Alloc_Abs | 
       apply DAT_Read_Abs | apply DAT_Read_Conc |
       apply DAT_Write_Abs | apply DAT_Write_Conc ];
      apply Union_intror; assumption.  
  - destruct theta as [acts|]; destruct theta' as [acts'|]; intuition;
    (apply PTS_Seq; [apply IHPhi_Theta_Soundness1 | apply IHPhi_Theta_Soundness2]).
  - split; destruct theta as [acts|]; destruct theta' as [acts'|]; intuition;
    (apply PTS_Par; [apply IHPhi_Theta_Soundness1 | apply IHPhi_Theta_Soundness2]).
Qed.


Lemma EnsembleUnionComp :
  forall (phi1 phi2 : Phi) (theta1 theta2 : Theta),
    phi1 ⊑ theta1 -> phi2 ⊑ theta2 -> Phi_Seq phi1  phi2 ⊑ (Union_Theta theta1 theta2).
Proof. 
  intros phi1 phi2 theta1 theta2 H1 H2.
  econstructor.
  - apply EnsembleUnionSym with (theta' := theta2) in H1. intuition. 
  - apply EnsembleUnionSym with (theta' := theta1) in H2. intuition.
Qed.


Module E := FMapAVL.Make (AsciiVars).
Module H := FMapAVL.Make (RegionVars).
Module R := FMapAVL.Make (AsciiVars).

Module Raw := E.Raw.
 
Inductive Val :=
  | Loc  : Rgn -> nat -> Val
  | Num  : nat -> Val
  | Bit  : bool -> Val
  | Cls  : (Raw.t Val * R.t Region * Expr) -> Val                    
  | Eff  : Theta -> Val             
  | Unit : Val
  | Pair : nat * nat -> Val.
 
Definition Env := Raw.t Val.
Definition Rho := R.t nat.
Definition Heap  := H.t Val.  
Definition V_Key := Raw.key.
Definition R_Key := R.key.
Definition H_Key := H.key.

Definition find_E (k: V_Key) (m: Env) : option Val := Raw.find (elt := Val) k m. 
Definition update_E (p: Name * Val) (m : Env) := Raw.add (fst p) (snd p) m.

Definition find_R (k: Rgn) (m: Rho) : option Region :=
  match k with
    | Rgn_Const r => Some r
    | Rgn_Var rho => R.find (elt := Region) rho m
  end.
Definition update_R (p: Name * Region) (m : Rho) := R.add (fst p) (snd p) m.

Definition find_H (k: H_Key) (m: Heap) : option Val := H.find k m.
Definition update_H (p: H_Key * Val) (m: Heap) := H.add (fst p) (snd p) m.

Definition Functional_Map_Union (heap1 heap2 : Heap) : Heap :=
  let f := fun (k : nat * nat) (v : Val) (m : Heap) => H.add k v m
  in H.fold f heap1 heap2.

Inductive merge : Heap -> Heap -> Heap -> Prop :=
| mergeL : forall heap1 heap2, merge heap1 heap2 (Functional_Map_Union heap1 heap2)
| mergeR : forall heap1 heap2, merge heap1 heap2 (Functional_Map_Union heap2 heap1).

Reserved Notation "e '⇓' n" (at level 50, left associativity).
Inductive BigStep   : (Heap * Env * Rho * Expr) -> (Heap * Val * Phi) -> Prop:=
  | BS_Nat_Cnt    : forall n env rho heap,
                        (heap, env, rho, Const n) ⇓ (heap, Num n, Phi_Nil)
  | BS_Boolean    : forall b env rho heap,
                        (heap, env, rho, Bool b) ⇓ (heap, Bit b, Phi_Nil)                                     
  | BS_Val_Var    : forall x v env rho heap,
                        find_E x env = Some v -> (heap, env, rho, Var x) ⇓ (heap, v, Phi_Nil)                          
  | BS_Mu_Abs     : forall f x ec ee env rho heap,
                      (heap, env, rho, Mu f x ec ee) ⇓ (heap, Cls (env, rho, Mu f x ec ee), Phi_Nil)
  | BS_Lambda_Abs : forall x er env rho heap,
                        (heap, env, rho, Lambda x er) ⇓ (heap, Cls (env, rho, Lambda x er), Phi_Nil)
  | BS_Mu_App     : forall f x ef ea ec' ee' v v'
                           (env env': Env) (rho rho' : Rho) (heap fheap aheap bheap : Heap) (facts aacts bacts : Phi), 
                        (heap, env, rho, ef) ⇓ (fheap, Cls (env', rho', Mu f x ec' ee'), facts) ->
                        (fheap, env, rho, ea) ⇓ (aheap, v', aacts) ->
                        (aheap, update_E (x, v') env', rho', ec') ⇓ (bheap, v, bacts) ->
                        (heap, env, rho, Mu_App ef ea) ⇓ (bheap, v, Phi_Seq (Phi_Seq facts aacts) bacts)
  | BS_Rgn_App    : forall x er eb w v v'
                           (env env': Env) (rho rho' : Rho) (heap fheap aheap bheap : Heap) (facts aacts bacts : Phi), 
                        (heap, env, rho, er) ⇓ (fheap, Cls (env', rho', Lambda x eb), facts) ->
                        find_R w rho = Some v' ->
                        (fheap, env', update_R (x, v') rho' , eb) ⇓ (bheap, v, bacts) ->
                        (heap, env, rho, Rgn_App er w) ⇓ (bheap, v, Phi_Seq facts bacts)          
  | BS_Eff_App    : forall f x ef ea ec' ee' v v' (env env': Env) (rho rho' : Rho) heap (facts aacts bacts : Phi), 
                        (heap, env, rho, ef) ⇓ (heap, Cls (env', rho', Mu f x ec' ee'), facts) ->
                        (heap, env, rho, ea) ⇓ (heap, v', aacts) ->
                        (heap, update_E (x, v') env', rho', ee') ⇓ (heap, v, bacts) ->
                        (heap, env, rho, Eff_App ef ea) ⇓ (heap, v, Phi_Seq (Phi_Seq facts aacts) bacts)
  | BS_Pair_Par   : forall env rho ea1 ef1 ea2 ef2 v1 v2 theta1 theta2
                           (heap heap_mu1 heap_mu2 heap' : Heap) (acts_mu1 acts_mu2 acts_eff1 acts_eff2 : Phi),
                        (heap, env, rho, Eff_App ef1 ea1) ⇓ (heap, Eff theta1, acts_eff1) ->
                        (heap, env, rho, Eff_App ef2 ea2) ⇓ (heap, Eff theta2, acts_eff2) ->
                        Disjointness theta1 theta1 /\ not (Conflictness theta1 theta2) ->
                        (heap, env, rho, Mu_App ef1 ea1) ⇓ (heap_mu1, Num v1, acts_mu1) ->
                        (heap, env, rho, Mu_App ef2 ea2) ⇓ (heap_mu2, Num v2, acts_mu2) ->
                        merge heap_mu1 heap_mu2 heap' ->
                        (heap, env, rho, Pair_Par ef1 ea1 ef2 ea2) 
                           ⇓ (heap', Pair (v1, v2), Phi_Seq (Phi_Par acts_eff1 acts_eff2) (Phi_Par acts_mu1 acts_mu2))
  | BS_Cond_True  : forall e et ef env rho v (heap cheap theap : Heap) (cacts tacts : Phi),
                        (heap, env, rho, e) ⇓ (cheap, (Bit true), cacts) -> 
                        (cheap, env, rho, et) ⇓ (theap, v, tacts) -> 
                        (heap, env, rho, Cond e et ef) ⇓ (theap, v, Phi_Seq cacts tacts)
  | BS_Cond_False : forall e et ef env rho v (heap cheap fheap : Heap) (cacts facts : Phi),
                        (heap, env, rho, e) ⇓ (cheap, (Bit false), cacts) -> 
                        (cheap, env, rho, ef) ⇓ (fheap, v, facts) -> 
                        (heap, env, rho, Cond e et ef) ⇓ (fheap, v, Phi_Seq cacts facts) 
  | BS_New_Ref     : forall e w r l v env rho  (heap heap' : Heap) vacts,
                        (heap, env, rho, e) ⇓ (heap', v, vacts) ->
                        find_R w rho = Some r ->
                        find_H (r, l) heap' = None -> 
                        (heap, env, rho, Ref w e) ⇓ (update_H ((r, l), v) heap', Loc (Rgn_Const r) l, Phi_Seq vacts (Phi_Elem (DA_Alloc r l)))   
  | BS_Get_Ref     : forall ea w r l v env rho (heap heap' : Heap) aacts,
                        (heap, env, rho, ea) ⇓ (heap', Loc w l, aacts) ->
                        find_R w rho = Some r ->
                        find_H (r, l) heap' = Some v ->                       
                        (heap, env, rho, DeRef w ea) ⇓ (heap', v, Phi_Seq aacts (Phi_Elem (DA_Read r l)))
  | BS_Set_Ref     : forall ea ev w r l v env rho (heap heap' heap'' : Heap) (aacts vacts : Phi),
                        (heap, env, rho, ea) ⇓ (heap', Loc w l, aacts) ->
                        (heap', env, rho, ev) ⇓ (heap'', v, vacts) ->
                        find_R w rho = Some r ->
                        (heap, env, rho, Assign w ea ev) ⇓ (update_H ((r, l), v) heap'', Unit, Phi_Seq (Phi_Seq aacts vacts) (Phi_Elem (DA_Write r l)))
  | BS_Nat_Plus    : forall a b va vb env rho (heap lheap rheap : Heap) (lacts racts : Phi),
                        (heap, env, rho, a) ⇓ (lheap, Num va, lacts) ->
                        (lheap, env, rho, b) ⇓ (rheap, Num vb, racts) ->  
                        (heap, env, rho, Plus a b) ⇓ (rheap, Num (va + vb), Phi_Seq lacts racts)
  | BS_Nat_Minus   : forall a b va vb env rho (heap lheap rheap : Heap) (lacts racts : Phi),
                        (heap, env, rho, a) ⇓ (lheap, Num va, lacts) ->
                        (lheap, env, rho, b) ⇓ (rheap, Num vb, racts) ->  
                        (heap, env, rho, Minus a b) ⇓ (rheap, Num (va - vb), Phi_Seq lacts racts)
  | BS_Nat_Times   : forall a b va vb env rho (heap lheap rheap : Heap) (lacts racts : Phi),
                        (heap, env, rho, a) ⇓ (lheap, Num va, lacts) ->
                        (lheap, env, rho, b) ⇓ (rheap, Num vb, racts) -> 
                        (heap, env, rho, Times a b) ⇓ (rheap, Num (va * vb), Phi_Seq lacts racts)
  | BS_Bool_Eq     : forall a b va vb env rho (heap lheap rheap : Heap) (lacts racts : Phi),
                        (heap, env, rho, a) ⇓ (lheap, Num va, lacts) ->
                        (lheap, env, rho, b) ⇓ (rheap, Num vb, racts) ->   
                        (heap, env, rho, Eq a b) ⇓ (rheap, Bit (beq_nat va vb), Phi_Seq lacts racts)
  | BS_Alloc_Abs   : forall w r env rho heap,
                        find_R w rho = Some r ->
                        (heap, env, rho, AllocAbs w) ⇓ (heap, Eff (Some (singleton_set (CA_AllocAbs r))), Phi_Nil)
  | BS_Read_Abs    : forall w r env rho heap,
                        find_R w rho = Some r ->  
                        (heap, env, rho, ReadAbs w) ⇓ (heap, Eff (Some (singleton_set (CA_ReadAbs r))), Phi_Nil)        
  | BS_Write_Abs   : forall w r env rho heap,
                        find_R w rho = Some r ->   
                        (heap, env, rho, WriteAbs w) ⇓ (heap, Eff (Some (singleton_set (CA_WriteAbs r))), Phi_Nil)
  | BS_Read_Conc   : forall ea r l env rho (heap heap' : Heap) aacts,
                        (heap, env, rho, ea) ⇓ (heap', Loc (Rgn_Const r) l, aacts) ->
                        aacts = Phi_Nil->
                        (heap, env, rho, ReadConc r ea) ⇓ (heap', Eff (Some (singleton_set (CA_ReadConc r l))), Phi_Nil) 
  | BS_Write_Conc  : forall ea r l env rho (heap heap' : Heap) aacts,
                        (heap, env, rho, ea) ⇓ (heap', Loc (Rgn_Const r) l, aacts) ->
                        aacts = Phi_Nil ->
                        (heap, env, rho, WriteConc r ea) ⇓ (heap', Eff (Some (singleton_set (CA_WriteConc r l))), Phi_Nil)
  | BS_Eff_Concat  : forall a b env rho heap (effa effb : Theta),
                        (heap, env, rho, a) ⇓ (heap, Eff effa, Phi_Nil) ->
                        (heap, env, rho, b) ⇓ (heap, Eff effb, Phi_Nil) ->
                        (heap, env, rho, Concat a b) ⇓ (heap, Eff (Union_Theta effa effb), Phi_Nil)
  | BS_Eff_Top     : forall env rho heap,
                        (heap, env, rho, Top) ⇓ (heap, Eff None, Phi_Nil)
  | BS_Eff_Empty   : forall  env rho heap,
                        (heap, env, rho, Empty) ⇓ (heap, Eff (Some empty_set), Phi_Nil) 
where "e '⇓' n" := (BigStep e n) : type_scope.

Lemma bs_det : forall heap env rho exp heap1 val1 phi1 heap2 val2 phi2,
                 BigStep (heap, env, rho, exp) (heap1, val1, phi1) ->
                 BigStep (heap, env, rho, exp) (heap2, val2, phi2) ->
                 H.Equal heap1 heap2 /\ val1 = val2 /\ phi1 = phi2.
Admitted.

Tactic Notation "dynamic_cases" tactic (first) ident(c) :=
  first;
  [ Case_aux c "cnt n"
  | Case_aux c "bool b"           
  | Case_aux c "var x"
  | Case_aux c "mu_abs"
  | Case_aux c "rgn_abs"              
  | Case_aux c "mu_app"
  | Case_aux c "rgn_app"             
  | Case_aux c "eff_app"
  | Case_aux c "par_pair"             
  | Case_aux c "cond_true" 
  | Case_aux c "cond_false"
  | Case_aux c "new_ref e"
  | Case_aux c "get_ref e"
  | Case_aux c "set_ref e1 e2"
  | Case_aux c "nat_plus x y"
  | Case_aux c "nat_minus x y"
  | Case_aux c "nat_times x y"
  | Case_aux c "bool_eq x y"
  | Case_aux c "alloc_abs"
  | Case_aux c "read_abs"             
  | Case_aux c "write_abs"             
  | Case_aux c "read_conc"
  | Case_aux c "write_conc"
  | Case_aux c "eff_concat"
  | Case_aux c "eff_top"
  | Case_aux c "eff_empty" ].

Inductive type_v1 :=
  | Natural  : type_v1
  | Boolean  : type_v1           
  | Arrow    : type_v1 -> (Epsilon * type_v1) -> (Epsilon * type_v1) -> type_v1
  | UnitTy   : type_v1
  | RefTy    : Rgn -> type_v1 -> type_v1
  | Effect   : type_v1
  | RgnPoly  : Name -> (Epsilon * type_v1) -> type_v1
  | RegionTy : type_v1.
Definition tau := type_v1.

Module ST := FMapAVL.Make (RegionVars).
Definition Sigma : Type := ST.t tau.
Definition Gamma : Type := E.t tau.
Definition Omega : Type := Ensemble Name.

Definition find_T (k: V_Key) (m: Gamma) : option tau := E.find k m.
Definition update_T (p: V_Key * tau) m := E.add (fst p) (snd p) m.             

Definition find_ST (k: ST.key) (m: Sigma) : option tau := ST.find k m.
Definition update_ST (p: ST.key * tau) m := ST.add (fst p) (snd p) m.

Notation "'∀' var '.' ty '!' eff " := (RgnPoly var (eff, ty))  (at level 60).
Definition eq_name (n n' : Name) := beq_nat (nat_of_ascii n) (nat_of_ascii n').

Inductive rgn2 : bool * bool * bool -> Set :=
  | Rgn2_Const : forall fv bv, Region -> rgn2 (true, fv, bv)
  | Rgn2_FVar : forall c bv, Name -> rgn2 (c, true, bv)
  | Rgn2_BVar : forall c fv, nat -> rgn2 (c, fv, true).
Definition rgn2_in_exp := rgn2 (true, true, false).
Definition rgn2_in_typ := rgn2 (true, true, true).

Inductive StaticAction2 : Set :=
| SA2_Alloc : rgn2_in_typ -> StaticAction2
| SA2_Read  : rgn2_in_typ -> StaticAction2
| SA2_Write : rgn2_in_typ -> StaticAction2.



(*Module Epsilon2Decidable.
Definition t := StaticAction2.
Definition eq (sa: StaticAction2) (sa': StaticAction2) := sa = sa'.
Lemma eq_refl : forall x : t, eq x x. unfold eq. auto. Qed.
Lemma eq_sym : forall x y : t, eq x y -> eq y x. unfold eq. auto. Qed.
Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z. unfold eq. intros. subst. reflexivity. Qed.
Lemma eq_dec: forall sa sa' : t, { eq sa sa' } + { ~ eq sa sa' }.
Proof.
assert (forall c fv bv (r: rgn2 (c, fv, bv)) (r': rgn2 (c, fv, bv)), { r = r' } + { ~ r = r' }).
{
dependent induction r; dependent induction r'; try (solve [right; intro; unfold eq in H; inversion H]).
+ destruct (Nat.eq_dec r r0). left. auto. right. intro. inversion H. contradiction.
+ destruct (AsciiVars.eq_dec n n0). unfold AsciiVars.eq in e. destruct e. left. auto. right. intro. inversion H. contradiction.
+ destruct (Nat.eq_dec n n0). left. auto. right. intro. inversion H. contradiction.
}
unfold eq.
dependent induction sa; dependent induction sa'; try (solve [right; intro; inversion H0]).
+ destruct (H true true true r r0). left. subst. auto. right. intro. inversion H0. contradiction.
+ destruct (H true true true r r0). left. subst. auto. right. intro. inversion H0. contradiction.
+ destruct (H true true true r r0). left. subst. auto. right. intro. inversion H0. contradiction.
Qed.
End Epsilon2Decidable.

Module Epsilon3 := MSetWeakList.Make (Epsilon2Decidable).*)
Definition Epsilon2 := Ensemble StaticAction2. (* FSetWeakList.Make (Epsilon2Decidable). *)


(* substitute for type *)
Inductive type2 :=
  | Ty2_Natural : type2
  | Ty2_Ref     : rgn2_in_typ -> type2 -> type2
  | Ty2_Arrow   : type2 -> Epsilon2 -> type2 -> Epsilon2 -> type2 -> type2
  | Ty2_ForallRgn : Epsilon2 -> type2 -> type2.

Definition free_rgn_vars_in_rgn2 (rgn: rgn2_in_typ) : Ensemble Name :=
  match rgn with
  | Rgn2_Const _ _ _ => empty_set
  | Rgn2_FVar _ _ n => singleton_set n
  | Rgn2_BVar _ _ _ => empty_set
  end.
Definition free_rgn_vars_in_sa2 (sa: StaticAction2) : Ensemble Name :=
  match sa with
  | SA2_Alloc rgn => free_rgn_vars_in_rgn2 rgn
  | SA2_Read rgn => free_rgn_vars_in_rgn2 rgn
  | SA2_Write rgn => free_rgn_vars_in_rgn2 rgn
  end.

Definition free_rgn_vars_in_eps2 (eps: Epsilon2) : Ensemble Name := 
  fun n => exists sa, eps sa -> (free_rgn_vars_in_sa2 sa) n.

(* substitute for fv *)
Fixpoint free_rgn_vars (t: type2) : Ensemble Name :=
  match t with
  | Ty2_Natural    => empty_set
  | Ty2_Ref rgn ty => set_union (free_rgn_vars_in_rgn2 rgn) (free_rgn_vars ty)
  | Ty2_Arrow aty ceff crty eeff erty =>
                      set_union (free_rgn_vars aty)
                                (set_union (set_union (free_rgn_vars_in_eps2 ceff)
                                                      (free_rgn_vars crty))
                                           (set_union (free_rgn_vars_in_eps2 eeff)
                                                      (free_rgn_vars erty)))
  | Ty2_ForallRgn eff rty => set_union (free_rgn_vars_in_eps2 eff)
                                       (free_rgn_vars rty)
  end.

Definition mk_rgn_type (u: rgn2_in_exp) : rgn2_in_typ
 := match u with
      | Rgn2_Const fv bv n => Rgn2_Const true true n
      | Rgn2_FVar c bv n => Rgn2_FVar true true n
      | Rgn2_BVar c fv n => Rgn2_BVar true true n                              
    end.

Definition open_subst_rgn_exp_in_rgn2 (k : nat) (u: rgn2_in_exp) (t: rgn2_in_typ) : rgn2_in_typ
 := match t with
    | Rgn2_Const _ _ _ => t
    | Rgn2_FVar _ _ _ => t
    | Rgn2_BVar _ _ n => if (beq_nat n k) then mk_rgn_type u else t
    end.

Definition open_subst_rgn_exp_in_sa2 (k : nat) (u: rgn2_in_exp) (sa: StaticAction2) : StaticAction2 :=
  match sa with
  | SA2_Alloc rgn => SA2_Alloc (open_subst_rgn_exp_in_rgn2 k u rgn)
  | SA2_Read rgn  => SA2_Read (open_subst_rgn_exp_in_rgn2 k u rgn)
  | SA2_Write rgn => SA2_Write (open_subst_rgn_exp_in_rgn2 k u rgn)
  end.

Definition open_subst_rgn_exp_in_eps2 (k : nat) (u: rgn2_in_exp) (eps: Epsilon2) : Epsilon2 := 
  fun sa => exists (eps' : Epsilon2), eps sa -> eps' (open_subst_rgn_exp_in_sa2 k u sa) . 

(* substitute for open_subst *)
Fixpoint open_subst_rgn_exp (k: nat) (u: rgn2_in_exp) (t: type2) {struct t} : type2 :=
  match t with
  | Ty2_Natural    => t
  | Ty2_Ref rgn ty => Ty2_Ref (open_subst_rgn_exp_in_rgn2 k u rgn) (open_subst_rgn_exp k u ty)
  | Ty2_Arrow aty ceff crty eeff erty =>
                      Ty2_Arrow (open_subst_rgn_exp k u aty)
                                (open_subst_rgn_exp_in_eps2 k u ceff) (open_subst_rgn_exp k u crty)
                                (open_subst_rgn_exp_in_eps2 k u eeff) (open_subst_rgn_exp k u erty)
  | Ty2_ForallRgn eff rty =>
                      Ty2_ForallRgn (open_subst_rgn_exp_in_eps2 k u eff) (open_subst_rgn_exp k u rty)
  end.

Definition open_subst_rgn (u: rgn2_in_exp)  (t: type2) : type2 := open_subst_rgn_exp 0 u t.
Definition open_rgn (t : type2) (x : Name) : type2
  := let rgn_fvar := Rgn2_FVar true false x in open_subst_rgn_exp 0 (rgn_fvar) t.

Definition close_subst_rgn_exp_in_rgn2 (k : nat) (x: Name) (t: rgn2_in_typ) : rgn2_in_typ
 := match t with
    | Rgn2_Const _ _ _ => t
    | Rgn2_FVar _ _ n  => if AsciiVars.eq_dec n x then (Rgn2_BVar true true k) else t  
    | Rgn2_BVar _ _ _  => t
    end.

Definition close_subst_rgn_exp_in_sa2 (k : nat) (x: Name) (sa: StaticAction2) : StaticAction2 :=
  match sa with
  | SA2_Alloc rgn => SA2_Alloc (close_subst_rgn_exp_in_rgn2 k x rgn)
  | SA2_Read rgn  => SA2_Read (close_subst_rgn_exp_in_rgn2 k x rgn)
  | SA2_Write rgn => SA2_Write (close_subst_rgn_exp_in_rgn2 k x rgn)
  end.

Definition close_subst_rgn_exp_in_eps2 (k : nat) (x: Name) (eps: Epsilon2) : Epsilon2 := 
  fun sa => exists (eps' : Epsilon2), eps sa -> eps' (close_subst_rgn_exp_in_sa2 k x sa) .

(* substitute for close_subst *)
Fixpoint close_subst_rgn_exp (k: nat) (x: Name) (t: type2) {struct t} : type2 :=
  match t with
  | Ty2_Natural    => t
  | Ty2_Ref rgn ty => Ty2_Ref (close_subst_rgn_exp_in_rgn2 k x rgn) (close_subst_rgn_exp k x ty)
  | Ty2_Arrow aty ceff crty eeff erty =>
                      Ty2_Arrow (close_subst_rgn_exp k x aty)
                                (close_subst_rgn_exp_in_eps2 k x ceff) (close_subst_rgn_exp k x crty)
                                (close_subst_rgn_exp_in_eps2 k x eeff) (close_subst_rgn_exp k x erty)
  | Ty2_ForallRgn eff rty =>
                      Ty2_ForallRgn (close_subst_rgn_exp_in_eps2 k x eff) (close_subst_rgn_exp k x rty)
  end.

Definition close_rgn (x : Name) (t : type2) := close_subst_rgn_exp 0 x t.


Inductive type: Set :=
  | Fvar    : Name -> type
  | Bvar    : nat -> type
  | Arrow_t : type -> type -> type
  | Forall  : type -> type.

Fixpoint fv (t: type) : Ensemble Name :=
  match t with
  | Fvar x        => singleton_set x 
  | Bvar n        => empty_set
  | Arrow_t t1 t2 => set_union (fv t1) (fv t2)
  | Forall t2     => fv t2
  end.

Fixpoint open_subst (k: nat) (u: type) (t: type) {struct t} : type :=
  match t with
  | Fvar n        => t
  | Bvar n        => if (beq_nat n k) then u else t
  | Arrow_t a1 a2 => Arrow_t (open_subst k u a1) (open_subst k u a2)
  | Forall a2     => Forall (open_subst (S k) u a2)
  end.

Definition open (u: type)  (t: type) : type := open_subst 0 u t.
Definition open_var (t : type) (x : Name) : type := open_subst 0 (Fvar x) t.

Fixpoint close_subst (k: nat)  (x: Name)  (t: type) {struct t} : type :=
  match t with
  | Fvar n        => if AsciiVars.eq_dec n x then (Bvar k) else t                  
  | Bvar n        => t
  | Arrow_t t1 t2 => Arrow_t (close_subst k x t1) (close_subst k x t2)
  | Forall t2     => Forall (close_subst (S k) x t2)
  end.

Definition close_var (x : Name) (t : type) := close_subst 0 x t.

(*Reserved Notation "'[' z ':=' u ']' t" (at level 20).*)
Fixpoint subst (z : Name) (u : type) (t : type) {struct t} : type :=
  match t with
  | Bvar i        => t
  | Fvar x        => if AsciiVars.eq_dec x z then u else t
  | Arrow_t t1 t2 => Arrow_t (subst z u t1) (subst z u t2)
  | Forall t1     => Forall (subst z u t1) 
end.
(*where "'[' z ':=' u ']' t" := (subst z u t).*)



Reserved Notation "'[' x ':=' w ']' t" (at level 20).
Fixpoint subst_v1 (t:tau) (x:Name) (w:Rgn) : tau := t
where "'[' x ':=' w ']' t" := (subst_v1 t x w).

Definition subst_rho rho tau :=
  R.fold (fun x r ty => subst_v1 ty x (Rgn_Const r))
         rho tau.

Notation "'∅'" := (Empty)  (at level 60).
Notation "'⊤'" := (Top) (at level 60).
Notation "a '⊕' b" := (Concat a b) (at level 60).

Reserved Notation "ec '◀' ee" (at level 50, left associativity).
Inductive BackTriangle : Expr -> Expr -> Prop :=
 | Num_Pure  : forall n : nat,
                (Const n) ◀ ∅
 | Bool_Pure : forall b : bool,
                 (Bool b) ◀ ∅
 | Var_Pure  : forall x : ascii,
                 (Var x) ◀ ∅
 | Abs_Pure  : forall (f x: ascii) (ec ee: Expr),
                 (Mu f x ec ee) ◀ ∅
 | App_Conc  : forall (ef ea efff effa : Expr), 
                 (ef ◀ ∅) -> (ea ◀ ∅) -> (Mu_App ef ea) ◀ (Eff_App ef ea)
 | Cond_Cond : forall (e et ef efft efff : Expr),                   
                 (e ◀ ∅ ) -> (et ◀ efft) -> (ef ◀ efff) -> (Cond e et ef) ◀ (Cond e efft efff)                       
 | Ref_Alloc_Abs : forall (e eff : Expr) (w : Rgn),
                     (e ◀ eff) -> (Ref w e) ◀ (eff ⊕ AllocAbs w)
 | Ref_Read_Abs  : forall (e eff : Expr) (w : Rgn),
                     (e ◀ eff) -> (DeRef w e) ◀ (eff ⊕ (ReadAbs w))
 | Ref_Read_Conc : forall (e eff : Expr) (r : Region),
                     (e ◀ ∅) -> (DeRef (Rgn_Const r) e) ◀ (ReadConc r e)
 | Ref_Write_Abs  : forall (e1 e2 eff2 : Expr) (w : Rgn),
                      (e1 ◀ ∅) -> (e2 ◀ eff2) -> (Assign w e1 e2) ◀ (eff2 ⊕ (WriteAbs w))
 | Ref_Write_Conc : forall (e1 e2 eff2 : Expr) (r : Region),
                      (e1 ◀ ∅) -> (e2 ◀ eff2) -> (Assign (Rgn_Const r) e1 e2) ◀ (eff2 ⊕ (WriteConc r e1))
 | Top_Approx: forall e : Expr, e ◀ Top
where "ec '◀' ee" := (BackTriangle ec ee) : type_scope.

Inductive TcRho : (Rho * Omega) -> Prop :=
  | TC_Rho : forall rho rgns,
               (forall r w,
                  (R.find r rho = Some w ->
                   set_elem rgns r)) ->
               (forall r,
                  set_elem rgns r ->
                  (exists w,
                     R.find r rho = Some w)) ->
               TcRho (rho, rgns).

Inductive TcRgn : (Omega * Rgn) -> Prop :=
  | TC_Rgn_Const : forall rgns s,
                      TcRgn (rgns, Rgn_Const s)
  | TC_Rgn_Var   : forall rgns r,
                      set_elem rgns r ->
                      TcRgn (rgns, Rgn_Var r).      

Inductive TcExp : (Sigma * Gamma * Omega * Expr * tau * Epsilon) -> Prop :=
  | TC_Nat_Cnt     : forall stty ctxt rgns n,
                        TcExp (stty, ctxt, rgns, Const n, Natural, Empty_Static_Action)
  | TC_Boolean     : forall stty ctxt rgns b,
                        TcExp (stty, ctxt, rgns, Bool b, Boolean, Empty_Static_Action)                     
  | TC_Val_Var     : forall stty ctxt rgns x ty,
                        find_T x ctxt = Some ty ->
                        TcExp (stty, ctxt, rgns, Var x, ty, Empty_Static_Action)                           
  | TC_Mu_Abs      : forall stty ctxt rgns f x ec ee tyx effc tyc effe,
                        ec ◀ ee ->  
                        TcExp (stty, update_T (x, tyx) ctxt, rgns, ec, tyc, effc) ->
                        TcExp (stty, update_T (x, tyx) ctxt, rgns, ee, Effect, effe) ->
                        TcExp (stty, ctxt, rgns, Mu f x ec ee, Arrow tyx (effc, tyc) (effe, Effect), Empty_Static_Action)
  | TC_Rgn_Abs     : forall stty ctxt rgns x er effr tyr,
                        not_set_elem rgns x ->
                        TcExp (stty, ctxt, set_union rgns (singleton_set x), er, tyr, effr) ->
                        TcExp (stty, ctxt, rgns, Lambda x er, RgnPoly x (effr, tyr), Empty_Static_Action)                              
  | TC_Mu_App      : forall stty ctxt rgns ef ea tya effc tyc effe efff effa,
                        TcExp (stty, ctxt, rgns, ef, Arrow tya (effc, tyc) (effe, Effect), efff) ->
                        TcExp (stty, ctxt, rgns, ea, tya, effa) ->
                        TcExp (stty, ctxt, rgns, Mu_App ef ea, tyc, Union_Static_Action (Union_Static_Action efff effa) effc)
  | TC_Rgn_App      : forall stty ctxt rgns er x w  tyr effr efff,
                        TcExp (stty, ctxt, rgns, er, RgnPoly x (effr, tyr), efff) ->
                        TcRgn (rgns, w) ->
                        TcExp (stty, ctxt, rgns, Rgn_App er w, [x := w]tyr, Union_Static_Action efff effr)
  | TC_Eff_App     : forall stty ctxt rgns ef ea tya effc tyc effe efff effa,
                        TcExp (stty, ctxt, rgns, ef, Arrow tya (effc, tyc) (effe, Effect), efff) ->
                        TcExp (stty, ctxt, rgns, ea, tya, effa) ->
                        TcExp (stty, ctxt, rgns, Eff_App ef ea, Effect, Union_Static_Action (Union_Static_Action efff effa) effe)                 
  | TC_New_Ref     : forall stty ctxt rgns e t veff w s,      
                        TcExp (stty, ctxt, rgns, e, t, veff) ->
                        w = Rgn_Const s -> 
                        TcExp (stty, ctxt, rgns, Ref w e, RefTy w t, Union_Static_Action veff (Singleton_Static_Action (SA_Alloc w)))
  | TC_Get_Ref     : forall stty ctxt rgns e t aeff w,   
                        TcExp (stty, ctxt, rgns, e, RefTy w t, aeff) ->
                        TcRgn (rgns, w) ->
                        TcExp (stty, ctxt, rgns, DeRef w e, t, Union_Static_Action aeff (Singleton_Static_Action (SA_Read w)))                     
  | TC_Set_Ref     : forall stty ctxt rgns ea ev t aeff veff w,
                        TcExp (stty, ctxt, rgns, ea, RefTy w t, aeff) ->
                        TcExp (stty, ctxt, rgns, ev, t, veff) ->
                        TcRgn (rgns, w) ->
                        TcExp (stty, ctxt, rgns, Assign w ea ev, UnitTy,
                               Union_Static_Action (Union_Static_Action aeff veff) (Singleton_Static_Action (SA_Write w)))                              
  | TC_Conditional : forall stty ctxt rgns b e1 e2 te eff eff1 eff2,      
                        TcExp (stty, ctxt, rgns, b, Boolean, eff) ->         
                        TcExp (stty, ctxt, rgns, e1, te, eff1) -> 
                        TcExp (stty, ctxt, rgns, e2, te, eff2) -> 
                        TcExp (stty, ctxt, rgns, Cond b e1 e2, te, Union_Static_Action eff (Union_Static_Action eff1 eff2))                          
  | TC_Nat_Plus    : forall stty ctxt rgns e1 e2 eff1 eff2,   
                        TcExp (stty, ctxt, rgns,  e1, Natural, eff1) ->
                        TcExp (stty, ctxt, rgns, e2, Natural, eff2) -> 
                        TcExp (stty, ctxt, rgns, Plus e1 e2, Natural, Union_Static_Action eff1 eff2)
  | TC_Nat_Minus  : forall stty ctxt rgns e1 e2 eff1 eff2,   
                        TcExp (stty, ctxt, rgns, e1, Natural, eff1) ->
                        TcExp (stty, ctxt, rgns, e2, Natural, eff2) -> 
                        TcExp (stty, ctxt, rgns, Minus e1 e2, Natural, Union_Static_Action eff1 eff2)
  | TC_Nat_Times  : forall stty ctxt rgns e1 e2 eff1 eff2,   
                        TcExp (stty, ctxt, rgns, e1, Natural, eff1) ->
                        TcExp (stty, ctxt, rgns, e2, Natural, eff2) -> 
                        TcExp (stty, ctxt, rgns, Times e1 e2, Natural, Union_Static_Action eff1 eff2)
  | TC_Bool_Eq     : forall stty ctxt rgns e1 e2 eff1 eff2,   
                        TcExp (stty, ctxt, rgns, e1, Natural, eff1) ->
                        TcExp (stty, ctxt, rgns, e2, Natural, eff2) -> 
                        TcExp (stty, ctxt, rgns, Eq e1 e2, Boolean, Union_Static_Action eff1 eff2)
  | TC_Alloc_Abs  : forall stty ctxt rgns r,
                        TcExp (stty, ctxt, rgns, AllocAbs r, Effect, Empty_Static_Action)
  | TC_Read_Abs   : forall stty ctxt rgns r,
                        TcExp (stty, ctxt, rgns, ReadAbs r, Effect, Empty_Static_Action)
  | TC_Read_Conc  : forall stty ctxt rgns e r t aeff,
                        TcExp (stty, ctxt, rgns, e, RefTy (Rgn_Const r) t, aeff) ->
                        TcExp (stty, ctxt, rgns, ReadConc r e, Effect, aeff)
  | TC_Write_Abs  : forall stty ctxt rgns r,
                       TcExp (stty, ctxt, rgns, WriteAbs r, Effect, Empty_Static_Action)
  | TC_Write_Conc : forall stty ctxt rgns e r t aeff,
                       TcExp (stty, ctxt, rgns, e, RefTy (Rgn_Const r) t, aeff) ->
                       TcExp (stty, ctxt, rgns, WriteConc r e, Effect, aeff)
  | TC_Eff_Concat : forall stty ctxt rgns a b eff1 eff2,   
                       TcExp (stty, ctxt, rgns, a, Effect, eff1) ->
                       TcExp (stty, ctxt, rgns, b, Effect, eff2) -> 
                       TcExp (stty, ctxt, rgns, Concat a b, Effect, Empty_Static_Action)                   
  | TC_Eff_Top    : forall stty ctxt rgns,
                       TcExp (stty, ctxt, rgns, Top, Effect, Empty_Static_Action)
  | TC_Eff_Empty  : forall stty ctxt rgns,
                       TcExp (stty, ctxt, rgns, Empty, Effect, Empty_Static_Action).




Inductive TcVal : (Sigma * Val * tau) -> Prop :=
  | TC_Num     : forall stty  n,
                   TcVal (stty, Num n, Natural)
  | TC_Bit     : forall stty b,
                   TcVal (stty, Bit b, Boolean)
  | TC_Loc     : forall stty s l ty,
                   ST.find (s, l) stty = Some ty ->
                   TcVal (stty, Loc (Rgn_Const s) l, RefTy (Rgn_Const s) ty)
  | TC_Cls     : forall stty env rho e rgns ctxt t,
                   TcRho (rho, rgns) ->
                   TcEnv (stty, rho, env, ctxt) ->
                   TcExp (stty, ctxt, rgns, e, t, Empty_Static_Action) ->
                   TcVal (stty, Cls (env, rho, e), subst_rho rho t) 
  | TC_Unit     : forall stty, TcVal (stty, Unit, UnitTy)
  | TC_Eff      : forall stty e, TcVal (stty, Eff e, Effect)
                   
                        
with TcEnv : (Sigma * Rho * Env * Gamma) -> Prop :=
  | TC_Env : forall stty rho env ctxt, 
               E.Raw.bst env ->
               (forall x v, 
                  (find_E x env = Some v -> 
                   exists t, find_T x ctxt = Some t)) ->
               (forall x t,
                  (find_T x ctxt = Some t ->
                   exists v, find_E x env = Some v)) ->
               (forall x v t,
                  find_E x env = Some v -> 
                  find_T x ctxt = Some t ->
                  TcVal (stty, v, subst_rho rho t)) ->
               TcEnv (stty, rho, env, ctxt).
                    

Definition find_type_ext_stores_def  := 
   forall stty stty' l (t' : tau),
      ST.find l stty = Some t' ->
      ST.find l stty' = Some t' -> 
      ST.find l stty =  ST.find l stty'.

Lemma find_type_ext_stores: find_type_ext_stores_def.  
Proof.
  intros stty stty' l t' H1 H2.
  rewrite <- H1 in H2.
  symmetry in H2.
  assumption.
Qed.

Scheme tc_val__xind := Induction for TcVal Sort Prop
  with tc_env__xind := Induction for TcEnv Sort Prop.
Combined Scheme tc_val__tc_env__xind from tc_val__xind, tc_env__xind.

Lemma ext_stores__exp:
   forall stty stty',
     (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t') -> 
     (forall ctxt rgns e t eff, TcExp (stty, ctxt, rgns, e, t, eff) -> TcExp (stty', ctxt, rgns, e, t, eff)).
Proof.
 intros stty stty' H ctxt  rho e t eff HTc.
 dependent induction HTc;  
 try (econstructor); eauto.
Qed.
        
Definition get_store_typing_val {A B:Type} (p : Sigma * A * B) : Sigma   
  := fst (fst p).

Definition get_store_typing_env {A B C:Type} (p : Sigma * A * B * C) : Sigma   
  := fst (fst (fst p)).

Definition mk_TcVal_ext_store_ty (p : Sigma * Val * tau) (stty' : Sigma)
  := TcVal (stty', snd (fst p), snd p).

Definition mk_TcEnv_ext_store_ty (p : Sigma * Rho * Env * Gamma) (stty' : Sigma)
  := TcEnv (stty', snd (fst (fst p)), snd (fst p), snd p).

Lemma ext_stores__val_env__aux:
   forall stty stty',
     (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t') -> 
     (forall p,
        TcVal p -> get_store_typing_val p = stty -> mk_TcVal_ext_store_ty p stty') /\
     (forall p,
        TcEnv p -> get_store_typing_env p = stty -> mk_TcEnv_ext_store_ty p stty').  
Proof.
  intros stty stty' HWeak. 
  apply tc_val__tc_env__xind; intro stty''; intros; 
  try constructor; try assumption ;  
  unfold mk_TcVal_ext_store_ty, mk_TcEnv_ext_store_ty, get_store_typing_val, get_store_typing_env in *; simpl in *; 
  try assumption.
  - subst. now apply HWeak.
  - eapply ext_stores__exp in t2.  
    + intuition; econstructor; eauto. 
    + subst; exact HWeak.
  - intuition.  eapply H; eassumption. 
    (*eapply TC_Subst;eauto.
  - intros x v t0 H1 H2. eapply H; eassumption. *)
Qed.

Lemma ext_stores__val:
   forall stty stty',
     (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t') -> 
     (forall v t, TcVal (stty, v, t) -> TcVal (stty', v, t)).
Proof.
  intros stty stty' HWeak v t H. pose HWeak.  
  apply ext_stores__val_env__aux in e. destruct e as [HTc  HEnv].  
  inversion H; subst; try econstructor; eauto.
  - eapply ext_stores__exp in H5. 
    + eapply HEnv in H4. cbv in H4. exact H4. cbv. reflexivity. 
    + exact HWeak.
  - eapply ext_stores__exp in H5. eassumption. exact HWeak.
  (*- apply HTc in H4; [unfold mk_TcVal_ext_store_ty in H4; simpl in H4; assumption | reflexivity]. *)
Qed.

Lemma ext_stores__env:
   forall stty stty',
     (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t') -> 
     (forall rho env ctxt, TcEnv (stty, rho, env, ctxt) -> TcEnv (stty', rho, env, ctxt)).
Proof.
  intros stty stty' HWeak rho env ctxt H. pose HWeak.  
  apply ext_stores__val_env__aux in e. destruct e as [HTc  HEnv]. 
  unfold mk_TcEnv_ext_store_ty in HEnv. apply HEnv in H. 
  - now simpl in H.
  - now cbv.
Qed.
 
Lemma EmptyIsNil:
  forall phi, phi ⊑ Theta_Empty -> phi = Phi_Nil.
Proof.
  induction phi; intros.
  reflexivity.
  inversion H; subst; inversion H1; subst; contradiction.
  - assert ( H1 : phi1 = Phi_Nil ) by (apply IHphi1; inversion H; assumption); rewrite H1.
    assert ( H2 : phi2 = Phi_Nil ) by (apply IHphi2; inversion H; assumption); rewrite H2.
    rewrite Phi_Par_Nil_R. reflexivity.
  - assert ( H1 : phi1 = Phi_Nil ) by (apply IHphi1; inversion H; assumption); rewrite H1.
    assert ( H2 : phi2 = Phi_Nil ) by (apply IHphi2; inversion H; assumption); rewrite H2.
    rewrite Phi_Seq_Nil_R. reflexivity.  
Qed.

Lemma PhiInThetaTop:
  forall phi, phi ⊑ Theta_Top.
Proof.  
  induction phi; intros; econstructor; try assumption; apply DAT_Top.
Qed.

Lemma EmptyTracePreservesHeap_1 : 
  forall h r env e same_h v' acts, (h, r, env, e) ⇓ (same_h, v', acts) -> acts = Phi_Nil -> h = same_h.
Proof.
  intros h r env e same_h v' acts H Hnil.  (*destruct H as [H Hnil]. *)
  dependent induction H; auto; inversion Hnil.
  - eapply IHBigStep; [reflexivity | auto].
  - eapply IHBigStep; [reflexivity | auto]. 
Qed.

Lemma EmptyTracePreservesHeap_2 : 
  forall h r env e same_h v acts,
    (h, r, env, e) ⇓ (h, v, acts) -> h = same_h -> (same_h, r, env, e) ⇓ (same_h, v, acts).
Proof.
  intros h r env e same_h v' acts Dyn H. now subst.
Qed.

Lemma EmptyTracePreservesHeap_3 : 
  forall h r env e same_h v acts,
    (same_h, r, env, e) ⇓ (same_h, v, acts) -> (h, r, env, e) ⇓ (same_h, v, acts) -> acts = Phi_Nil -> (h, r, env, e) ⇓ (h, v, acts).
Proof.
  intros h r env e same_h v' acts H Dyn1 Hnil.
  apply EmptyTracePreservesHeap_1 in Dyn1. now subst. exact Hnil.
Qed. 