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
Require Export Nameless2.
Require Export TypeLemmas.


Inductive Expr :=
  | Const     : nat -> Expr
  | Bool      : bool -> Expr
  | Var       : Name -> Expr
  | Mu        : Name -> Name -> Expr -> Expr -> Expr
  | Lambda    : Name -> Expr -> Expr                                               
  | Mu_App    : Expr -> Expr -> Expr 
  | Rgn_App   : Expr -> rgn2_in_exp -> Expr                                     
  | Eff_App   : Expr -> Expr -> Expr
  | Pair_Par  : Expr -> Expr -> Expr -> Expr -> Expr                              
  | Cond      : Expr -> Expr -> Expr -> Expr 
  | Ref       : rgn2_in_exp -> Expr -> Expr                  
  | DeRef     : rgn2_in_exp -> Expr -> Expr                     
  | Assign    : rgn2_in_exp -> Expr -> Expr -> Expr
  | Plus      : Expr -> Expr -> Expr
  | Minus     : Expr -> Expr -> Expr
  | Times     : Expr -> Expr -> Expr
  | Eq        : Expr -> Expr -> Expr
  | AllocAbs  : rgn2_in_exp -> Expr                         
  | ReadAbs   : rgn2_in_exp -> Expr
  | WriteAbs  : rgn2_in_exp -> Expr                               
  | ReadConc  : Expr -> Expr               
  | WriteConc : Expr -> Expr
  | Concat    : Expr -> Expr -> Expr
  | Top       : Expr
  | Empty     : Expr. 
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

Inductive ReadOnlyPhi : Phi -> Prop :=
 | Phi_RO_Nil  : ReadOnlyPhi (Phi_Nil)
 | Phi_RO_Elem : forall r a, ReadOnlyPhi (Phi_Elem (DA_Read r a))
 | Phi_RO_Seq  : forall phi1 phi2, ReadOnlyPhi phi1 -> ReadOnlyPhi phi2 -> ReadOnlyPhi (Phi_Seq phi1 phi2)
 | Phi_RO_Par  : forall phi1 phi2, ReadOnlyPhi phi1 -> ReadOnlyPhi phi2 -> ReadOnlyPhi (Phi_Par phi1 phi2).                                                                                       

Definition Empty_Dynamic_Action := Empty_set DynamicAction.
Definition Singleton_Dynamic_Action (e : DynamicAction) :=  Singleton DynamicAction e.
Definition Union_Dynamic_Action (a b : Ensemble DynamicAction) :=  Union DynamicAction a b.

(* Static Actions; for type-and-effect system *)
Definition StaticAction := StaticAction2.
Definition Epsilon := Epsilon2.
Definition SA_Alloc:= SA2_Alloc.
Definition SA_Read:= SA2_Read.
Definition SA_Write:= SA2_Write.

Definition Empty_Static_Action := Empty_set StaticAction.
Definition Singleton_Static_Action (e : StaticAction) :=  Singleton StaticAction e.
Definition Union_Static_Action (a b : Ensemble StaticAction) :=  Union StaticAction a b.

Inductive ReadOnlyStatic : Epsilon -> Prop :=
 | Static_RO_Empty     : ReadOnlyStatic (Empty_Static_Action)
 | Static_RO_Singleton : forall r, ReadOnlyStatic (Singleton_Static_Action (SA_Read r))
 | Static_RO_Union     : forall eps1 eps2, ReadOnlyStatic eps1 -> ReadOnlyStatic eps2 -> ReadOnlyStatic (Union_Static_Action eps1 eps2).                                  

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
      DA_in_Theta (DA_Write s l) (Some acts)
| DAT_intror :
    forall da a acts, DA_in_Theta da (Some acts) ->
                      DA_in_Theta da (Some (set_union acts a))
| DAT_introl :
    forall da a acts, DA_in_Theta da (Some acts) ->
                      DA_in_Theta da (Some (set_union a acts)).


Inductive Disjoint_Dynamic : DynamicAction -> DynamicAction -> Prop :=
 | DD_Read_Read   : forall r1 l1 r2 l2, Disjoint_Dynamic (DA_Read r1 l1) (DA_Read r2 l2)
 | DD_Write_Write : forall r1 l1 r2 l2, r1 <> r2 -> l1 <> l2 -> Disjoint_Dynamic (DA_Write r1 l1) (DA_Write r2 l2)
 | DD_Read_Write  : forall r1 l1 r2 l2, r1 <> r2 -> l1 <> l2 -> Disjoint_Dynamic (DA_Read r1 l1) (DA_Write r2 l2)
 | DD_Write_Read  : forall r1 l1 r2 l2, r1 <> r2 -> l1 <> l2 -> Disjoint_Dynamic (DA_Write r1 l1) (DA_Read r2 l2).                                                                                

Inductive Disjoint_Static : StaticAction2 -> StaticAction2 -> Prop :=
 | DS_Read_Read   : forall r1 r2, Disjoint_Static (SA2_Read r1) (SA2_Read r2)
 | DS_Write_Write : forall r1 r2, r1 <> r2 -> Disjoint_Static (SA2_Write r1) (SA2_Write r2)
 | DS_Read_Write  : forall r1 r2, r1 <> r2 -> Disjoint_Static (SA2_Read r1) (SA2_Write r2)
 | DS_Write_Read  : forall r1 r2, r1 <> r2 -> Disjoint_Static (SA2_Write r1) (SA2_Read r2).


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




Module E := FMapAVL.Make (AsciiVars).
Module H := FMapAVL.Make (RegionVars).


Module Raw := E.Raw.
 
Inductive Val :=
  | Loc  : rgn2_in_exp -> nat -> Val
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
Definition update_rec_E (f : ascii * Val) (x: ascii * Val) m :=
  let m' := Raw.add (fst f) (snd f) m
  in Raw.add (fst x) (snd x) m'.

Definition find_R (k: rgn2_in_exp) (m: Rho) : option Region :=
 match k with 
  | Rgn2_Const fv bv n => Some n
  | Rgn2_FVar c bv n => R.find (elt := Region) n m
  | Rgn2_BVar c fv n => None                               
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
  | BS_Mu_Abs     : forall f x ec ee env rho (heap fheap : Heap),
                        (heap, env, rho, Mu f x ec ee) ⇓ (heap, Cls (env, rho, Mu f x ec ee), Phi_Nil)
  | BS_Lambda_Abs : forall x eb env rho heap,
                        (heap, env, rho, Lambda x eb) ⇓ (heap, Cls (env, rho, Lambda x eb), Phi_Nil)
  | BS_Mu_App     : forall f x ef ea ec' ee' v v'
                           (env env': Env) (rho rho' : Rho) (heap fheap aheap bheap : Heap) (facts aacts bacts : Phi),
                        (heap, env, rho, ef) ⇓ (fheap, Cls (env', rho', Mu f x ec' ee'), facts) ->
                        (fheap, env, rho, ea) ⇓ (aheap, v, aacts) ->
                        (aheap, update_rec_E (f, Cls (env', rho', Mu f x ec' ee')) (x, v) env', rho', ec') ⇓ (bheap, v', bacts) ->
                        (heap, env, rho,  Mu_App ef ea) ⇓ (bheap, v', Phi_Seq (Phi_Seq facts aacts) bacts) 
  | BS_Rgn_App    : forall x er eb w v v'
                           (env env': Env) (rho rho' : Rho) (heap fheap aheap bheap : Heap) (facts aacts bacts : Phi), 
                        (heap, env, rho, er) ⇓ (fheap, Cls (env', rho', Lambda x eb), facts) ->
                        find_R w rho = Some v' ->
                        (fheap, env', update_R (x, v') rho' , eb) ⇓ (bheap, v, bacts) ->
                        (heap, env, rho, Rgn_App er w) ⇓ (bheap, v, Phi_Seq facts bacts)          
  | BS_Eff_App    : forall f x ef ea ec' ee' v v' (env env': Env) (rho rho' : Rho) heap (facts aacts bacts : Phi), 
                        (heap, env, rho, ef) ⇓ (heap, Cls (env', rho', Mu f x ec' ee'), facts) ->
                        (heap, env, rho, ea) ⇓ (heap, v', aacts) ->
                        (*(heap, update_E (x, v') env', rho', ee') ⇓ (heap, v, bacts) ->*)
                        (heap, update_rec_E (f, Cls (env', rho', Mu f x ec' ee')) (x, v') env', rho', ee') ⇓ (heap, v, bacts) ->
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
                        (heap, env, rho, Ref w e) ⇓ (update_H ((r, l), v) heap',
                                                     Loc (Rgn2_Const true false r) l,
                                                     Phi_Seq vacts (Phi_Elem (DA_Alloc r l)))   
  | BS_Get_Ref     : forall ea w r l v env rho (heap heap' : Heap) aacts,
                        (heap, env, rho, ea) ⇓ (heap', Loc w l, aacts) ->
                        find_R w rho = Some r ->
                        find_H (r, l) heap' = Some v ->                       
                        (heap, env, rho, DeRef w ea) ⇓ (heap', v, Phi_Seq aacts (Phi_Elem (DA_Read r l)))
  | BS_Set_Ref     : forall ea ev w r l v env rho (heap heap' heap'' : Heap) (aacts vacts : Phi),
                        (heap, env, rho, ea) ⇓ (heap', Loc w l, aacts) ->
                        (heap', env, rho, ev) ⇓ (heap'', v, vacts) ->
                        find_R w rho = Some r ->
                        (heap, env, rho, Assign w ea ev) ⇓ (update_H ((r, l), v) heap'', Unit,
                                                            Phi_Seq (Phi_Seq aacts vacts) (Phi_Elem (DA_Write r l)))
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
                        (heap, env, rho, ea) ⇓ (heap', Loc (Rgn2_Const true false r) l, aacts) ->
                        aacts = Phi_Nil->
                        (heap, env, rho, ReadConc ea) ⇓ (heap', Eff (Some (singleton_set (CA_ReadConc r l))), Phi_Nil) 
  | BS_Write_Conc  : forall ea r l env rho (heap heap' : Heap) aacts,
                        (heap, env, rho, ea) ⇓ (heap', Loc (Rgn2_Const true false r) l, aacts) ->
                        aacts = Phi_Nil ->
                        (heap, env, rho, WriteConc ea) ⇓ (heap', Eff (Some (singleton_set (CA_WriteConc r l))), Phi_Nil)
  | BS_Eff_Concat  : forall a b env rho heap (effa effb : Theta) phia phib,
                        (heap, env, rho, a) ⇓ (heap, Eff effa, phia) ->
                        (heap, env, rho, b) ⇓ (heap, Eff effb, phib) ->
                        (heap, env, rho, Concat a b) ⇓ (heap, Eff (Union_Theta effa effb), Phi_Seq phia phib)
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
  | Case_aux c "eff_empty"
  (*| Case_aux c "mu_rec"*) ].

Definition tau := type2.

Module ST := FMapAVL.Make (RegionVars).
Definition Sigma : Type := ST.t tau.
Definition Gamma : Type := E.t tau.
Definition Omega : Type := Ensemble Name.

Definition find_T (k: V_Key) (m: Gamma) : option tau := E.find k m.
Definition update_T (p: V_Key * tau) m := E.add (fst p) (snd p) m.
Definition update_rec_T (f: ascii * tau) (x: ascii * tau) m :=
  let m' := E.add (fst f) (snd f) m
  in E.add (fst x) (snd x) m'.

Definition find_ST (k: ST.key) (m: Sigma) : option tau := ST.find k m.
Definition update_ST (p: ST.key * tau) m := ST.add (fst p) (snd p) m.

Notation "'∅'" := (Empty)  (at level 60).
Notation "'⊤'" := (Top) (at level 60).
Notation "a '⊕' b" := (Concat a b) (at level 60).


Inductive TcRgn : (Omega * rgn2_in_exp) -> Prop :=
  | TC_Rgn_Const : forall rgns s,
                      TcRgn (rgns, Rgn2_Const true false s)
  | TC_Rgn_Var   : forall rgns r,
                      set_elem rgns r ->
                      TcRgn (rgns, Rgn2_FVar true false r).      


Reserved Notation "ec '◀' ee" (at level 50, left associativity).
Inductive BackTriangle2 : Expr -> Expr -> Prop :=
 | Num_Pure      : forall n eff,
                     (Const n) ◀ eff
 | Bool_Pure     : forall b eff,
                     (Bool b) ◀ eff
 | Var_Pure      : forall x eff,
                     (Var x) ◀ eff
 | Abs_Pure      : forall (f x: ascii) (ec ee: Expr),                     
                     (Mu f x ec ee) ◀ ∅
 | Abs_Rgn_Pure  : forall x eb,
                     Lambda x eb ◀ (∅)
 | App_F_Free    : forall (f x : ascii) (ec ee ea: Expr), 
                     ((Mu f x ec ee) ◀ ∅) -> 
                     (ea ◀ ∅) ->
                     (Mu_App (Mu f x ec ee) ea) ◀ ee ->
                     (Mu_App (Var f) ea) ◀ ee
 | App_Inner_Eff : forall (f x : ascii) (ec ee ea: Expr), 
                     ((Mu f x ec ee) ◀ ∅) ->
                     (ea ◀ ∅) ->
                     (Mu_App (Mu f x ec ee) ea) ◀ ee                                           
 | App_Capp_Eapp : forall (ef ea efff effa : Expr), 
                     (ef ◀ efff) ->
                     (ea ◀ effa) ->
                     (Mu_App ef ea) ◀ (efff ⊕ (effa ⊕ (Eff_App ef ea)))
 | Rgn_App_Eff   : forall eb x w eff,
                     eb ◀ eff ->
                     (Rgn_App (Lambda x eb) w) ◀ eff
 | Cond_Cond     : forall (e et ef efft efff : Expr),                   
                     (e ◀ ∅ ) ->
                     (et ◀ efft) ->
                     (ef ◀ efff) ->
                     (Cond e et ef) ◀ (Cond e efft efff)                                        
 | Ref_Alloc_Abs : forall (e eff : Expr) (w : rgn2_in_exp),
                     (e ◀ eff) ->
                     (Ref w e) ◀ (eff ⊕ AllocAbs w)
 | Ref_Read_Abs  : forall (e eff : Expr) (w : rgn2_in_exp),
                     (e ◀ eff) ->
                     (DeRef w e) ◀ (eff ⊕ (ReadAbs w))
 | Ref_Read_Conc : forall (e eff : Expr) (w : rgn2_in_exp),
                     (e ◀ eff) ->
                     (DeRef w e) ◀ (eff ⊕ (ReadConc e))
 | Ref_Write_Abs  : forall (e1 e2 eff1 eff2 : Expr) (w : rgn2_in_exp),
                      (e1 ◀ eff1) ->
                      (e2 ◀ eff2) ->
                      (Assign w e1 e2) ◀ (eff1 ⊕ (eff2 ⊕ (WriteAbs w)))
 | Ref_Write_Conc : forall (e1 e2 eff1 eff2 : Expr) (w : rgn2_in_exp),
                      (e1 ◀ eff1) ->
                      (e2 ◀ eff2) ->
                      (Assign w e1 e2) ◀ (eff1 ⊕ (eff2 ⊕ (WriteConc e1)))                                                  
 | Top_Approx     : forall e : Expr,
                      e ◀ Top
 | Times_Concat   : forall e1 e2 eff1 eff2,
                     (e1 ◀ eff1) ->
                     (e2 ◀ eff2) ->
                     (Times e1 e2) ◀ (eff1 ⊕ eff2)
 | Plus_Concat   : forall e1 e2 eff1 eff2,
                     (e1 ◀ eff1) ->
                     (e2 ◀ eff2) ->
                     (Plus e1 e2) ◀ (eff1 ⊕ eff2)
 | Eq_Concat      : forall e1 e2 eff1 eff2,
                     (e1 ◀ eff1) ->
                     (e2 ◀ eff2) ->
                     (Eq e1 e2) ◀ (eff1 ⊕ eff2)
  | Cond_Cond_2   : forall (e et ef eff : Expr),                   
                     (e ◀ ∅ ) ->
                     (et ◀ eff) ->
                     (ef ◀ eff) ->
                     (Cond e et ef) ◀ eff                               
where "ec '◀' ee" := (BackTriangle2 ec ee) : type_scope.

Reserved Notation "stty ';;' ctxt ';;' rgns '|-' ec '<<' ee" (at level 50, left associativity).
Inductive TcExp : (Sigma * Gamma * Omega * Expr * tau * Epsilon) -> Prop :=
  | TC_Nat_Cnt     : forall stty ctxt rgns n,
                        TcExp (stty, ctxt, rgns, Const n, Ty2_Natural, Empty_Static_Action)
  | TC_Boolean     : forall stty ctxt rgns b,
                        TcExp (stty, ctxt, rgns, Bool b, Ty2_Boolean, Empty_Static_Action)
  | TC_Val_Var     : forall stty ctxt rgns x ty,
                        find_T x ctxt = Some ty ->
                        TcExp (stty, ctxt, rgns, Var x, ty, Empty_Static_Action)                           
  | TC_Mu_Abs      : forall stty ctxt rgns f x ec ee tyx effc tyc effe,
                        BackTriangle (stty, update_rec_T (f, Ty2_Arrow tyx effc tyc effe Ty2_Effect) (x, tyx) ctxt, rgns, ec, ee) ->
                        (BackTriangle2 ec ee) ->
                        TcExp (stty, update_rec_T (f, Ty2_Arrow tyx effc tyc effe Ty2_Effect) (x, tyx) ctxt, rgns, ec, tyc, effc) ->
                        TcExp (stty, update_rec_T (f, Ty2_Arrow tyx effc tyc effe Ty2_Effect) (x, tyx) ctxt, rgns, ee, Ty2_Effect, effe) ->
                        TcExp (stty, ctxt, rgns, Mu f x ec ee, Ty2_Arrow tyx effc tyc effe Ty2_Effect, Empty_Static_Action)
  | TC_Rgn_Abs     : forall stty ctxt rgns x er effr tyr,
                        not_set_elem rgns x ->
                        lc_type tyr ->
                        lc_type_eps effr ->
                        TcExp (stty, ctxt, set_union rgns (singleton_set x), er, tyr, effr) ->
                        TcExp (stty, ctxt, rgns, Lambda x er, Ty2_ForallRgn (close_var_eff x effr) (close_var x tyr),
                               Empty_Static_Action)
  | TC_Mu_App      : forall stty ctxt rgns ef ea tya effc tyc effe efff effa,
                        TcExp (stty, ctxt, rgns, ef, Ty2_Arrow tya effc tyc effe Ty2_Effect, efff) ->
                        TcExp (stty, ctxt, rgns, ea, tya, effa) ->
                        ReadOnlyStatic efff ->
                        TcExp (stty, ctxt, rgns, Mu_App ef ea, tyc, Union_Static_Action (Union_Static_Action efff effa) effc)
  | TC_Rgn_App      : forall stty ctxt rgns er w tyr effr efff,
                        TcExp (stty, ctxt, rgns, er, Ty2_ForallRgn effr tyr, efff) ->
                        TcRgn (rgns, w) ->
                        TcExp (stty, ctxt, rgns, Rgn_App er w, open (mk_rgn_type w) tyr,
                               Union_Static_Action efff (open_rgn_eff (mk_rgn_type w) effr))
  | TC_Eff_App     : forall stty ctxt rgns ef ea tya effc tyc effe efff effa,
                        TcExp (stty, ctxt, rgns, ef, Ty2_Arrow tya effc tyc effe Ty2_Effect, efff) ->
                        TcExp (stty, ctxt, rgns, ea, tya, effa) ->
                        TcExp (stty, ctxt, rgns, Eff_App ef ea, Ty2_Effect, Union_Static_Action (Union_Static_Action efff effa) effe)
  | TC_New_Ref     : forall stty ctxt rgns e t veff w s,      
                        TcExp (stty, ctxt, rgns, e, t, veff) -> 
                        w = Rgn2_Const true false s ->
                        TcExp (stty, ctxt, rgns, Ref w e, Ty2_Ref (mk_rgn_type w) t,
                               Union_Static_Action veff (Singleton_Static_Action (SA_Alloc(mk_rgn_type w))))
  | TC_Get_Ref     : forall stty ctxt rgns e t aeff w s,
                        w = Rgn2_Const true false s ->
                        TcExp (stty, ctxt, rgns, e, Ty2_Ref (mk_rgn_type w) t, aeff) ->
                        TcRgn (rgns, w) ->
                        TcExp (stty, ctxt, rgns, DeRef w e, t, Union_Static_Action aeff (Singleton_Static_Action (SA_Read  (mk_rgn_type w))))
  | TC_Set_Ref     : forall stty ctxt rgns ea ev t aeff veff w s,
                        w = Rgn2_Const true false s -> 
                        TcExp (stty, ctxt, rgns, ea, Ty2_Ref (mk_rgn_type w) t, aeff) ->
                        TcExp (stty, ctxt, rgns, ev, t, veff) ->
                        TcRgn (rgns, w) ->
                        TcExp (stty, ctxt, rgns, Assign w ea ev, Ty2_Unit,
                               Union_Static_Action (Union_Static_Action aeff veff) (Singleton_Static_Action (SA_Write  (mk_rgn_type w))))
  | TC_Conditional : forall stty ctxt rgns b e1 e2 te eff eff1 eff2,      
                        TcExp (stty, ctxt, rgns, b, Ty2_Boolean, eff) ->         
                        TcExp (stty, ctxt, rgns, e1, te, eff1) -> 
                        TcExp (stty, ctxt, rgns, e2, te, eff2) -> 
                        TcExp (stty, ctxt, rgns, Cond b e1 e2, te, Union_Static_Action eff (Union_Static_Action eff1 eff2))
  | TC_Nat_Plus    : forall stty ctxt rgns e1 e2 eff1 eff2,   
                        TcExp (stty, ctxt, rgns,  e1, Ty2_Natural, eff1) ->
                        TcExp (stty, ctxt, rgns, e2, Ty2_Natural, eff2) -> 
                        TcExp (stty, ctxt, rgns, Plus e1 e2, Ty2_Natural, Union_Static_Action eff1 eff2)
  | TC_Nat_Minus  : forall stty ctxt rgns e1 e2 eff1 eff2,   
                        TcExp (stty, ctxt, rgns, e1, Ty2_Natural, eff1) ->
                        TcExp (stty, ctxt, rgns, e2, Ty2_Natural, eff2) -> 
                        TcExp (stty, ctxt, rgns, Minus e1 e2, Ty2_Natural, Union_Static_Action eff1 eff2)
  | TC_Nat_Times  : forall stty ctxt rgns e1 e2 eff1 eff2,   
                        TcExp (stty, ctxt, rgns, e1, Ty2_Natural, eff1) ->
                        TcExp (stty, ctxt, rgns, e2, Ty2_Natural, eff2) -> 
                        TcExp (stty, ctxt, rgns, Times e1 e2, Ty2_Natural, Union_Static_Action eff1 eff2)
  | TC_Bool_Eq     : forall stty ctxt rgns e1 e2 eff1 eff2,   
                        TcExp (stty, ctxt, rgns, e1, Ty2_Natural, eff1) ->
                        TcExp (stty, ctxt, rgns, e2, Ty2_Natural, eff2) -> 
                        TcExp (stty, ctxt, rgns, Eq e1 e2, Ty2_Boolean, Union_Static_Action eff1 eff2)
  | TC_Alloc_Abs  : forall stty ctxt rgns r,
                        TcExp (stty, ctxt, rgns, AllocAbs r, Ty2_Effect, Empty_Static_Action)
  | TC_Read_Abs   : forall stty ctxt rgns r,
                        TcExp (stty, ctxt, rgns, ReadAbs r, Ty2_Effect, Empty_Static_Action)
  | TC_Read_Conc  : forall stty ctxt rgns e r t aeff,
                        TcExp (stty, ctxt, rgns, e, Ty2_Ref (Rgn2_Const true true r) t, aeff) ->
                        TcExp (stty, ctxt, rgns, ReadConc e, Ty2_Effect, aeff)
  | TC_Write_Abs  : forall stty ctxt rgns r,
                       TcExp (stty, ctxt, rgns, WriteAbs r, Ty2_Effect, Empty_Static_Action)
  | TC_Write_Conc : forall stty ctxt rgns e r t aeff,
                       TcExp (stty, ctxt, rgns, e,  Ty2_Ref (Rgn2_Const true true r) t, aeff) ->
                       TcExp (stty, ctxt, rgns, WriteConc e, Ty2_Effect, aeff)
  | TC_Eff_Concat : forall stty ctxt rgns a b eff1 eff2,   
                       TcExp (stty, ctxt, rgns, a, Ty2_Effect, eff1) ->
                       TcExp (stty, ctxt, rgns, b, Ty2_Effect, eff2) -> 
                       TcExp (stty, ctxt, rgns, Concat a b, Ty2_Effect, Union_Static_Action eff1 eff2)                   
  | TC_Eff_Top    : forall stty ctxt rgns,
                       TcExp (stty, ctxt, rgns, Top, Ty2_Effect, Empty_Static_Action)
  | TC_Eff_Empty  : forall stty ctxt rgns,
                      TcExp (stty, ctxt, rgns, Empty, Ty2_Effect, Empty_Static_Action)
                            
with BackTriangle : Sigma * Gamma * Omega * Expr * Expr -> Prop :=
  | TC_Num_Pure     : forall stty ctxt rgns (n : nat),
                          TcExp (stty, ctxt, rgns, Const n, Ty2_Natural, Empty_Static_Action) ->   
                          BackTriangle (stty, ctxt, rgns, (Const n), ∅)
  | TC_Bool_Pure    : forall stty ctxt rgns (b : bool),
                          TcExp (stty, ctxt, rgns, Bool b, Ty2_Boolean, Empty_Static_Action) ->
                          BackTriangle (stty, ctxt, rgns, Bool b, ∅)
  | TC_Var_Pure     : forall stty ctxt rgns ty (x : ascii),
                          TcExp (stty, ctxt, rgns, Var x, ty, Empty_Static_Action) ->
                          BackTriangle (stty, ctxt, rgns, Var x, ∅)
  | TC_Abs_Pure     : forall stty ctxt rgns (f x: ascii) (ec ee: Expr),
                          BackTriangle (stty, ctxt, rgns, Mu f x ec ee, ∅)
  | TC_App_Conc     : forall  stty ctxt rgns (ef ea efff effa : Expr) ty_ef ty_ea  static_ef static_ea,
                          TcExp (stty, ctxt, rgns, ef, ty_ef, static_ef) ->
                          TcExp (stty, ctxt, rgns, ea, ty_ea, static_ea) ->
                          BackTriangle (stty, ctxt, rgns, ef, efff) ->
                          BackTriangle (stty, ctxt, rgns, ea, effa) ->
                          ReadOnlyStatic static_ef ->
                          BackTriangle (stty, ctxt, rgns, Mu_App ef ea, efff ⊕ (effa ⊕ (Eff_App ef ea)))                           
  | TC_Cond_Cond    : forall stty ctxt rgns (e et ef effe efft efff : Expr) ty_e ty_et ty_ef static_e static_et static_ef,
                          TcExp (stty, ctxt, rgns, e, ty_e, static_e) ->
                          TcExp (stty, ctxt, rgns, et, ty_et, static_et) ->
                          TcExp (stty, ctxt, rgns, ef, ty_ef, static_ef) ->
                          ReadOnlyStatic static_e ->
                          BackTriangle (stty, ctxt, rgns, e, ∅) ->
                          BackTriangle (stty, ctxt, rgns, et, efft) ->
                          BackTriangle (stty, ctxt, rgns, ef, efff) ->
                          BackTriangle (stty, ctxt, rgns, Cond e et ef, Cond e efft efff)
  | TC_Ref_Alloc_Abs : forall stty ctxt rgns (e eff : Expr) (w : rgn2_in_exp) ty_e static_e,
                          TcExp (stty, ctxt, rgns, e, ty_e, static_e) ->
                          BackTriangle (stty, ctxt, rgns, e, eff) ->
                          BackTriangle (stty, ctxt, rgns, Ref w e, eff ⊕ AllocAbs w)
  | TC_Ref_Read_Abs  : forall stty ctxt rgns (e eff : Expr) (w : rgn2_in_exp) ty_e static_e,
                          TcExp (stty, ctxt, rgns, e, ty_e, static_e) ->
                          BackTriangle (stty, ctxt, rgns, e, eff) ->
                          BackTriangle (stty, ctxt, rgns, DeRef w e, eff ⊕ (ReadAbs w))
  | TC_Ref_Read_Conc : forall stty ctxt rgns (e eff : Expr) (r : Region) ty_e static_e,
                          TcExp (stty, ctxt, rgns, e, ty_e, static_e) ->
                          BackTriangle (stty, ctxt, rgns, e, ∅) ->
                          BackTriangle (stty, ctxt, rgns, DeRef (Rgn2_Const true false r) e, ReadConc e)
  | TC_Ref_Write_Abs : forall stty ctxt rgns (e1 e2 eff2 : Expr) (w : rgn2_in_exp)  ty_e1 static_e1  ty_e2 static_e2,
                          TcExp (stty, ctxt, rgns, e1, ty_e1, static_e1) ->
                          TcExp (stty, ctxt, rgns, e2, ty_e2, static_e2) ->
                          BackTriangle (stty, ctxt, rgns, e1, ∅) ->
                          BackTriangle (stty, ctxt, rgns, e2, eff2) ->
                          BackTriangle (stty, ctxt, rgns, Assign w e1 e2, eff2 ⊕ (WriteAbs w))            
  | TC_Ref_Write_Conc: forall stty ctxt rgns (e1 e2 eff2 : Expr) (r : Region)  ty_e1 static_e1  ty_e2 static_e2,
                          TcExp (stty, ctxt, rgns, e1, ty_e1, static_e1) ->
                          TcExp (stty, ctxt, rgns, e2, ty_e2, static_e2) ->
                          BackTriangle (stty, ctxt, rgns, e1, ∅) ->
                          BackTriangle (stty, ctxt, rgns, e2, eff2) ->
                          BackTriangle (stty, ctxt, rgns, Assign (Rgn2_Const true false r) e1 e2, eff2 ⊕ (WriteConc e1))
  | TC_Top_Approx    : forall stty ctxt rgns (e : Expr) ty_e static_e,
                          TcExp (stty, ctxt, rgns, e, ty_e, static_e) ->
                          BackTriangle (stty, ctxt, rgns, e, Top)
where "stty ';;' ctxt ';;' rgns '|-' ec '<<' ee" := (BackTriangle (stty, ctxt, rgns, ec, ee)) : type_scope.

Scheme tc_exp__xind := Induction for TcExp Sort Prop
  with bt__xind := Induction for BackTriangle Sort Prop.
Combined Scheme tc_exp__bt__xind from tc_exp__xind, bt__xind.

Inductive TcVal : (Sigma * Val * tau) -> Prop :=
  | TC_Num     : forall stty n,
                   TcVal (stty, Num n, Ty2_Natural)
  | TC_Bit     : forall stty b,
                   TcVal (stty, Bit b, Ty2_Boolean)
  | TC_Loc     : forall stty s l ty,
                   ST.find (s, l) stty = Some ty ->
                   TcVal (stty, Loc (Rgn2_Const true false s) l, Ty2_Ref (Rgn2_Const true true s) ty)
  | TC_Cls     : forall stty env rho e rgns ctxt t,
                   TcRho (rho, rgns) ->
                   TcEnv (stty, rho, env, ctxt) ->
                   TcExp (stty, ctxt, rgns, e, t, Empty_Static_Action) ->
                   TcVal (stty, Cls (env, rho, e), subst_rho rho t) 
  | TC_Unit     : forall stty, TcVal (stty, Unit, Ty2_Unit)
  | TC_Eff      : forall stty e, TcVal (stty, Eff e, Ty2_Effect)
       
                        
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
               TcEnv (stty, rho, env, ctxt)
                     
with TcRho : (Rho * Omega) -> Prop :=
  | TC_Rho : forall rho rgns,
               (forall r,
                  (R.find r rho <> None -> set_elem rgns r)) ->
               (forall r,
                  set_elem rgns r ->
                  R.find r rho <> None) ->
                (forall stty r v t,
                  R.find r rho <> None -> 
                  set_elem rgns r ->
                  TcVal (stty, v, subst_rho rho t)) ->
                (forall t x,
                   not_set_elem rgns x -> x # t) ->
                (forall stty v r u t,
                   not_set_elem rgns r ->
                   TcVal (stty, v, subst_rho rho (subst_in_type r u t))) ->
               TcRho (rho, rgns).





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
                       with tc_env__xind := Induction for TcEnv Sort Prop
                       with tc_rho__xind := Induction for TcRho Sort Prop.
Combined Scheme tc_val__tc_env__xind from tc_val__xind, tc_env__xind, tc_rho__xind.

Lemma ext_stores__exp__bt__aux:
  (forall p, TcExp p ->
             match p with (stty, ctxt, rgns, e, t, eff) => 
               forall stty',
                 (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t') ->
                 TcExp (stty', ctxt, rgns, e, t, eff)
             end)
    /\
  (forall p, BackTriangle p ->
             match p with (stty, ctxt, rgns, ec, ee) => 
               forall stty',
                 (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t') ->
                 BackTriangle (stty', ctxt, rgns, ec, ee)
             end).
Proof.
  apply tc_exp__bt__xind;
 try (econstructor); eauto.
Qed.

Lemma ext_stores__exp:
   forall stty stty',
     (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t') -> 
     (forall ctxt rgns e t eff, TcExp (stty, ctxt, rgns, e, t, eff) -> TcExp (stty', ctxt, rgns, e, t, eff)).
Proof.
  intros.
  apply (match ext_stores__exp__bt__aux with conj F _ => F (stty, ctxt, rgns, e, t, eff) end); auto.
Qed.

Lemma ext_stores__bt:
   forall stty stty',
     (forall l t', ST.find l stty = Some t' -> ST.find l stty' = Some t') -> 
     (forall ctxt rgns ec ee, BackTriangle (stty, ctxt, rgns, ec, ee) -> BackTriangle (stty', ctxt, rgns, ec, ee)).
Proof.
  intros.
  apply (match ext_stores__exp__bt__aux with conj _ F => F (stty, ctxt, rgns, ec, ee) end); auto.
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
        TcEnv p -> get_store_typing_env p = stty -> mk_TcEnv_ext_store_ty p stty') /\
     (forall p,
        TcRho p -> TcRho p) .  
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

