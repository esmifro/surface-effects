Require Import Coq.Program.Equality.
Require Import Coq.Sets.Ensembles.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Lists.List.
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

(* Static Labels *)
Definition Region :=  nat.

(* Dynamic Actions; for operational semantics *)
Inductive DynamicAction : Set :=
| DA_Alloc : Region -> nat -> DynamicAction
| DA_Read  : Region -> nat -> DynamicAction
| DA_Write : Region -> nat -> DynamicAction.
Definition Phi := list DynamicAction.

Definition Empty_Dynamic_Action := Empty_set DynamicAction.
Definition Singleton_Dynamic_Action (e : DynamicAction) :=  Singleton DynamicAction e.
Definition Union_Dynamic_Action (a b : Ensemble DynamicAction) :=  Union DynamicAction a b.

(* Static Actions; for type-and-effect system *)
Inductive StaticAction : Set :=
| SA_Alloc : Region -> StaticAction
| SA_Read  : Region -> StaticAction
| SA_Write : Region -> StaticAction.
Definition Epsilon := Ensemble StaticAction.

Definition Empty_Static_Action := Empty_set StaticAction.
Definition Singleton_Static_Action (e : StaticAction) :=  Singleton StaticAction e.
Definition Union_Static_Action (a b : Ensemble StaticAction) :=  Union StaticAction a b.
                   
Definition Theta := option (Ensemble (DynamicAction + StaticAction)).
Definition Theta_Top : Theta := None.
Definition Theta_Empty : Theta := Some empty_set.

Definition Union_Theta (theta1 theta2 : Theta) := 
  match theta1,theta2 with
    | None, _ => None
    | _, None => None
    | Some acts1, Some acts2 => Some (set_union acts1 acts2)
  end.

Inductive DA_in_Theta : DynamicAction -> Theta -> Prop :=
| DAT_Top :
    forall da, DA_in_Theta da None
| DAT_Alloc_Abs :
    forall r l acts,
      set_elem acts (inr (SA_Alloc r)) ->
      DA_in_Theta (DA_Alloc r l) (Some acts)
| DAT_Read_Abs :
    forall r l acts,
      set_elem acts (inr (SA_Read r)) ->
      DA_in_Theta (DA_Read r l) (Some acts)
| DAT_Read_Conc :
    forall r l acts,
      set_elem acts (inl (DA_Read r l)) ->
      DA_in_Theta (DA_Read r l) (Some acts)
| DAT_Write_Abs :
    forall r l acts,
      set_elem acts (inr (SA_Write r)) ->
      DA_in_Theta (DA_Write r l) (Some acts)
| DAT_Write_Conc :
    forall r l acts,
      set_elem acts (inl (DA_Write r l)) ->
      DA_in_Theta (DA_Write r l) (Some acts).

Reserved Notation "phi '⊑' theta" (at level 50, left associativity).
Inductive Phi_Theta_Soundness : Phi -> Theta -> Prop :=
| PTS_nil :
    forall theta, nil ⊑ theta
| PTS_cons :
    forall da phi theta,
      DA_in_Theta da theta ->
      phi ⊑ theta -> (da::phi) ⊑ theta
where "phi '⊑' theta" := (Phi_Theta_Soundness phi theta) : type_scope.

Module E := FMapAVL.Make (AsciiVars).
Module H := FMapAVL.Make (RegionVars).
Module R := FMapAVL.Make (AsciiVars).

Module Raw := E.Raw.

(* Program Variables *)
Definition Name := ascii.
  
Inductive Expr :=
  | Const     : nat -> Expr
  | Bool      : bool -> Expr
  | Var       : Name -> Expr
  | Mu        : Name -> Name -> Expr -> Expr -> Expr
  | Lambda    : Name -> Expr                                               
  | Mu_App    : Expr -> Expr -> Expr
  | Rgn_App   : Expr -> Expr -> Expr                                     
  | Eff_App   : Expr -> Expr -> Expr                         
  | Cond      : Expr -> Expr -> Expr -> Expr 
  | Ref       : Region -> Expr -> Expr                  
  | DeRef     : Rgn -> Expr -> Expr                     
  | Assign    : Rgn -> Expr -> Expr -> Expr
  | Plus      : Expr -> Expr -> Expr
  | Minus     : Expr -> Expr -> Expr
  | Times     : Expr -> Expr -> Expr
  | Eq        : Expr -> Expr -> Expr
  | Let_Var   : Name -> Expr -> Expr -> Expr
  | AllocAbs  : Region -> Expr                         
  | ReadAbs   : Rgn -> Expr
  | WriteAbs  : Rgn -> Expr                               
  | ReadConc  : Region -> Expr -> Expr               
  | WriteConc : Region -> Expr -> Expr
  | Concat    : Expr -> Expr -> Expr
  | Top       : Expr
  | Empty     : Expr
with Rgn :=
  | Rgn_Const : Region -> Rgn
  | Rgn_Var   : ascii -> Rgn .

 
Inductive Val :=
  | Loc  : Rgn -> nat -> Val
  | Num  : nat -> Val
  | Bit  : bool -> Val
  | Cls  : (Raw.t Val * R.t Region * Expr) -> Val                    
  | Eff  : Theta -> Val             
  | Unit : Val.
 
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

Reserved Notation "e '⇓' n" (at level 50, left associativity).
Inductive BigStep   : (Heap * Env * Rho * Expr) -> (Heap * Val * Phi) -> Prop:=
  | BS_Nat_Cnt    : forall n env rho heap,
                        (heap, env, rho, Const n) ⇓ (heap, Num n, nil)
  | BS_Boolean    : forall b env rho heap,
                        (heap, env, rho, Bool b) ⇓ (heap, Bit b, nil)                                     
  | BS_Val_Var    : forall x v env rho heap,
                        find_E x env = Some v -> (heap, env, rho, Var x) ⇓ (heap, v, nil)                          
  | BS_Mu_Abs     : forall f x ec ee env rho heap,
                        (heap, env, rho, Mu f x ec ee) ⇓ (heap, Cls (env, rho, Mu f x ec ee), nil)            
  | BS_Mu_App     : forall f x ef ea ec' ee' v v'
                           (env env': Env) (rho rho' : Rho) (heap fheap aheap bheap : Heap) (facts aacts bacts : Phi), 
                        (heap, env, rho, ef) ⇓ (fheap, Cls (env', rho', Mu f x ec' ee'), facts) ->
                        (fheap, env, rho, ea) ⇓ (aheap, v', aacts) ->
                        (aheap, update_E (x, v') env', rho, ec') ⇓ (bheap, v, bacts) ->
                        (heap, env, rho, Mu_App ef ea) ⇓ (bheap, v, facts ++ aacts ++ bacts)
  | BS_Eff_App    : forall f x ef ea ec' ee' v v' (env env': Env) (rho rho' : Rho) heap (facts aacts bacts : Phi), 
                        (heap, env, rho, ef) ⇓ (heap, Cls (env', rho', Mu f x ec' ee'), facts) ->
                        (heap, env, rho, ea) ⇓ (heap, v', aacts) ->
                        (heap, update_E (x, v') env', rho, ee') ⇓ (heap, v, bacts) ->
                        (heap, env, rho, Eff_App ef ea) ⇓ (heap, v, facts ++ aacts ++ bacts)                                                       
  | BS_Cond_True  : forall e et ef env rho v (heap cheap theap : Heap) (cacts tacts : Phi),
                        (heap, env, rho, e) ⇓ (cheap, (Bit true), cacts) -> 
                        (cheap, env, rho, et) ⇓ (theap, v, tacts) -> 
                        (heap, env, rho, Cond e et ef) ⇓ (theap, v, cacts ++ tacts)
  | BS_Cond_False : forall e et ef env rho v (heap cheap fheap : Heap) (cacts facts : Phi),
                        (heap, env, rho, e) ⇓ (cheap, (Bit false), cacts) -> 
                        (cheap, env, rho, ef) ⇓ (fheap, v, facts) -> 
                        (heap, env, rho, Cond e et ef) ⇓ (fheap, v, cacts ++ facts) 
  | BS_New_Ref     : forall e r l v env rho  (heap heap' : Heap) vacts,
                        (heap, env, rho, e) ⇓ (heap', v, vacts) ->
                        find_H (r, l) heap' = None -> 
                        (heap, env, rho, Ref r e) ⇓ (update_H ((r, l), v) heap',  Loc (Rgn_Const r) l, vacts ++ (DA_Alloc r l)::nil)   
  | BS_Get_Ref     : forall ea w r l v env rho (heap heap' : Heap) aacts,
                        (heap, env, rho, ea) ⇓ (heap', Loc w l, aacts) ->
                        find_R w rho = Some r ->
                        find_H (r, l) heap' = Some v ->                       
                        (heap, env, rho, DeRef w ea) ⇓ (heap', v, aacts ++ (DA_Read r l)::nil)
  | BS_Set_Ref     : forall ea ev w r l v env rho (heap heap' heap'' : Heap) (aacts vacts : Phi),
                        (heap, env, rho, ea) ⇓ (heap', Loc w l, aacts) ->
                        (heap', env, rho, ev) ⇓ (heap'', v, vacts) ->
                        find_R w rho = Some r ->
                        (heap, env, rho, Assign w ea ev) ⇓ (update_H ((r, l), v) heap'', Unit, aacts ++ vacts ++ (DA_Write r l)::nil)
  | BS_Let_Val_In  : forall x e e' v env rho (heap heap': Heap) eacts,
                        (heap, env, rho, e) ⇓ (heap', v, eacts) ->
                        (heap, env, rho, Let_Var x e e') ⇓ (heap', v, eacts)
  | BS_Nat_Plus    : forall a b va vb env rho (heap lheap rheap : Heap) (lacts racts : Phi),
                        (heap, env, rho, a) ⇓ (lheap, Num va, lacts) ->
                        (lheap, env, rho, b) ⇓ (rheap, Num vb, racts) ->  
                        (heap, env, rho, Plus a b) ⇓ (rheap, Num (va + vb), lacts ++ racts)
  | BS_Nat_Minus   : forall a b va vb env rho (heap lheap rheap : Heap) (lacts racts : Phi),
                        (heap, env, rho, a) ⇓ (lheap, Num va, lacts) ->
                        (lheap, env, rho, b) ⇓ (rheap, Num vb, racts) ->  
                        (heap, env, rho, Minus a b) ⇓ (rheap, Num (va - vb), lacts ++ racts)
  | BS_Nat_Times   : forall a b va vb env rho (heap lheap rheap : Heap) (lacts racts : Phi),
                        (heap, env, rho, a) ⇓ (lheap, Num va, lacts) ->
                        (lheap, env, rho, b) ⇓ (rheap, Num vb, racts) -> 
                        (heap, env, rho, Times a b) ⇓ (rheap, Num (va * vb), lacts ++ racts)
  | BS_Bool_Eq     : forall a b va vb env rho (heap lheap rheap : Heap) (lacts racts : Phi),
                        (heap, env, rho, a) ⇓ (lheap, Num va, lacts) ->
                        (lheap, env, rho, b) ⇓ (rheap, Num vb, racts) ->   
                        (heap, env, rho, Eq a b) ⇓ (rheap, Bit (beq_nat va vb), lacts ++ racts)
  | BS_Alloc_Abs   : forall r env rho heap,
                        (heap, env, rho, AllocAbs r) ⇓ (heap, Eff (Some (singleton_set (inr (SA_Alloc r)))), nil)
  | BS_Read_Abs    : forall w r env rho heap,
                        find_R w rho = Some r ->  
                        (heap, env, rho, ReadAbs w) ⇓ (heap, Eff (Some (singleton_set (inr (SA_Read r)))), nil)        
  | BS_Write_Abs   : forall w r env rho heap,
                        find_R w rho = Some r ->   
                        (heap, env, rho, WriteAbs w) ⇓ (heap, Eff (Some (singleton_set (inr (SA_Write r)))), nil)
  | BS_Read_Conc   : forall ea r l env rho (heap heap' : Heap) aacts,
                        (heap, env, rho, ea) ⇓ (heap', Loc (Rgn_Const r) l, aacts) ->
                        aacts = nil ->
                        (heap, env, rho, ReadConc r ea) ⇓ (heap', Eff (Some (singleton_set (inl (DA_Read r l)))), nil) 
  | BS_Write_Conc  : forall ea r l env rho (heap heap' : Heap) aacts,
                        (heap, env, rho, ea) ⇓ (heap', Loc (Rgn_Const r) l, aacts) ->
                        aacts = nil ->
                        (heap, env, rho, WriteConc r ea) ⇓ (heap', Eff (Some (singleton_set (inl (DA_Write r l)))), nil)
  | BS_Eff_Concat  : forall a b env rho heap (effa effb : Theta),
                        (heap, env, rho, a) ⇓ (heap, Eff effa, nil) ->
                        (heap, env, rho, b) ⇓ (heap, Eff effb, nil) ->
                        (heap, env, rho, Concat a b) ⇓ (heap, Eff (Union_Theta effa effb), nil)
  | BS_Eff_Top     : forall env rho heap,
                        (heap, env, rho, Top) ⇓ (heap, Eff None, nil)
  | BS_Eff_Empty   : forall  env rho heap,
                        (heap, env, rho, Empty) ⇓ (heap, Eff (Some empty_set), nil) 
where "e '⇓' n" := (BigStep e n) : type_scope.

Tactic Notation "dynamic_cases" tactic (first) ident(c) :=
  first;
  [ Case_aux c "cnt n"
  | Case_aux c "bool b"           
  | Case_aux c "var x"
  | Case_aux c "mu_abs" 
  | Case_aux c "mu_app"
  | Case_aux c "eff_app"
  | Case_aux c "cond_true" 
  | Case_aux c "cond_false"
  | Case_aux c "new_ref e"
  | Case_aux c "get_ref e"
  | Case_aux c "set_ref e1 e2"           
  | Case_aux c "let_var_in"             
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

Inductive type :=
  | Natural : type
  | Boolean : type           
  | Arrow   : type -> (Epsilon * type) -> (Epsilon * type) -> type
  | UnitTy  : type
  | RefTy   : Region -> type -> type
  | Effect  : type.
Definition tau := type.

Module ST := FMapAVL.Make (RegionVars).
Definition Sigma : Type := ST.t tau.
Definition Gamma : Type := E.t tau. 

Definition find_T (k: V_Key) (m: Gamma) : option tau := E.find k m.
Definition update_T (p: V_Key * tau) m := E.add (fst p) (snd p) m.             

Definition find_ST (k: ST.key) (m: Sigma) : option tau := ST.find k m.
Definition update_ST (p: ST.key * tau) m := ST.add (fst p) (snd p) m.


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
 | Ref_Alloc_Abs : forall (e eff : Expr) (r : Region),
                     (e ◀ eff) -> (Ref r e) ◀ (eff ⊕ (AllocAbs r))
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


Inductive TcExp : (Sigma * Gamma * Rho * Expr * tau * Epsilon) -> Prop :=
  | TC_Nat_Cnt     : forall stty ctxt rho n,
                        TcExp (stty, ctxt, rho, Const n, Natural, Empty_Static_Action)
  | TC_Boolean     : forall stty ctxt rho b,
                        TcExp (stty, ctxt, rho, Bool b, Boolean, Empty_Static_Action)                     
  | TC_Val_Var     : forall stty ctxt rho x ty,
                        find_T x ctxt = Some ty ->
                        TcExp (stty, ctxt, rho, Var x, ty, Empty_Static_Action)
  | TC_Mu_Abs      : forall stty ctxt rho f x ec ee tyx effc tyc effe,
                        ec ◀ ee ->  
                        TcExp (stty, update_T (x, tyx) ctxt, rho, ec, tyc, effc) ->
                        TcExp (stty, update_T (x, tyx) ctxt, rho, ee, Effect, effe) ->
                        TcExp (stty, ctxt, rho, Mu f x ec ee, Arrow tyx (effc, tyc) (effe, Effect), Empty_Static_Action)
  | TC_Mu_App      : forall stty ctxt rho ef ea tya effc tyc effe efff effa,
                        TcExp (stty, ctxt, rho, ef, Arrow tya (effc, tyc) (effe, Effect), efff) ->
                        TcExp (stty, ctxt, rho, ea, tya, effa) ->
                        TcExp (stty, ctxt, rho, Mu_App ef ea, tyc, Union_Static_Action (Union_Static_Action efff effa) effc)
  | TC_Eff_App     : forall stty ctxt rho ef ea tya effc tyc effe efff effa,
                        TcExp (stty, ctxt, rho, ef, Arrow tya (effc, tyc) (effe, Effect), efff) ->
                        TcExp (stty, ctxt, rho, ea, tya, effa) ->
                        TcExp (stty, ctxt, rho, Eff_App ef ea, Effect, Union_Static_Action (Union_Static_Action efff effa) effe)                 
  | TC_New_Ref     : forall stty ctxt rho e r t veff,      
                        TcExp (stty, ctxt, rho, e, t, veff) ->
                        TcExp (stty, ctxt, rho, Ref r e, RefTy r t, Union_Static_Action veff (Singleton_Static_Action (SA_Alloc r)))
  | TC_Get_Ref     : forall stty ctxt rho e t aeff w r,   
                        TcExp (stty, ctxt, rho, e, RefTy r t, aeff) ->
                        find_R w rho = Some r ->
                        TcExp (stty, ctxt, rho, DeRef w e, t, Union_Static_Action aeff (Singleton_Static_Action (SA_Read r)))                     
  | TC_Set_Ref     : forall stty ctxt rho ea ev t aeff veff w r,   
                        TcExp (stty, ctxt, rho, ea, RefTy r t, aeff) ->
                        TcExp (stty, ctxt, rho, ev, t, veff) ->
                        find_R w rho = Some r ->
                        TcExp (stty, ctxt, rho, Assign w ea ev, UnitTy,
                                        Union_Static_Action (Union_Static_Action aeff veff) (Singleton_Static_Action (SA_Write r)))
  | TC_Conditional : forall stty ctxt rho b e1 e2 te eff eff1 eff2,      
                        TcExp (stty, ctxt, rho, b, Boolean, eff) ->         
                        TcExp (stty, ctxt, rho, e1, te, eff1) -> 
                        TcExp (stty, ctxt, rho, e2, te, eff2) -> 
                        TcExp (stty, ctxt, rho, Cond b e1 e2, te, Union_Static_Action eff (Union_Static_Action eff1 eff2))
  | TC_Let_Var     : forall stty ctxt rho x e t eff,   
                        TcExp (stty, ctxt, rho, e, t, eff) ->
                        TcExp (stty, ctxt, rho, Let_Var x e (Var x), t, eff)
  | TC_Nat_Plus    : forall stty ctxt rho e1 e2 eff1 eff2,   
                        TcExp (stty, ctxt, rho,  e1, Natural, eff1) ->
                        TcExp (stty, ctxt, rho, e2, Natural, eff2) -> 
                        TcExp (stty, ctxt, rho, Plus e1 e2, Natural, Union_Static_Action eff1 eff2)
  | TC_Nat_Minus  : forall stty ctxt rho e1 e2 eff1 eff2,   
                        TcExp (stty, ctxt, rho, e1, Natural, eff1) ->
                        TcExp (stty, ctxt, rho, e2, Natural, eff2) -> 
                        TcExp (stty, ctxt, rho, Minus e1 e2, Natural, Union_Static_Action eff1 eff2)
  | TC_Nat_Times  : forall stty ctxt rho e1 e2 eff1 eff2,   
                        TcExp (stty, ctxt, rho, e1, Natural, eff1) ->
                        TcExp (stty, ctxt, rho, e2, Natural, eff2) -> 
                        TcExp (stty, ctxt, rho, Times e1 e2, Natural, Union_Static_Action eff1 eff2)
  | TC_Bool_Eq     : forall stty ctxt rho e1 e2 eff1 eff2,   
                        TcExp (stty, ctxt, rho, e1, Natural, eff1) ->
                        TcExp (stty, ctxt, rho, e2, Natural, eff2) -> 
                        TcExp (stty, ctxt, rho, Eq e1 e2, Boolean, Union_Static_Action eff1 eff2)
  | TC_Alloc_Abs  : forall stty ctxt rho r,
                        TcExp (stty, ctxt, rho, AllocAbs r, Effect, Empty_Static_Action)
  | TC_Read_Abs   : forall stty ctxt rho r,
                        TcExp (stty, ctxt, rho, ReadAbs r, Effect, Empty_Static_Action)
  | TC_Read_Conc  : forall stty ctxt rho e r t aeff,
                        TcExp (stty, ctxt, rho, e, RefTy r t, aeff) ->
                        TcExp (stty, ctxt, rho, ReadConc r e, Effect, aeff)
  | TC_Write_Abs  : forall stty ctxt rho r,
                       TcExp (stty, ctxt, rho, WriteAbs r, Effect, Empty_Static_Action)
  | TC_Write_Conc : forall stty ctxt rho e r t aeff,
                       TcExp (stty, ctxt, rho, e, RefTy r t, aeff) ->
                       TcExp (stty, ctxt, rho, WriteConc r e, Effect, aeff)
  | TC_Eff_Concat : forall stty ctxt rho a b eff1 eff2,   
                       TcExp (stty, ctxt, rho, a, Effect, eff1) ->
                       TcExp (stty, ctxt, rho, b, Effect, eff2) -> 
                       TcExp (stty, ctxt, rho, Concat a b, Effect, Empty_Static_Action)                   
  | TC_Eff_Top    : forall stty ctxt rho,
                       TcExp (stty, ctxt, rho, Top, Effect, Empty_Static_Action)
  | TC_Eff_Empty  : forall stty ctxt rho,
                       TcExp (stty, ctxt, rho, Empty, Effect, Empty_Static_Action).

Inductive TcVal : (Sigma * Rho * Val * tau) -> Prop :=
  | TC_Num   : forall stty rho n,
                 TcVal (stty, rho, Num n, Natural)
  | TC_Bit   : forall stty rho b,
                 TcVal (stty, rho, Bit b, Boolean)
  | TC_Loc   : forall stty rho w r l ty,
                  find_R w rho = Some r ->
                  ST.find (r, l) stty = Some ty ->
                  TcVal (stty, rho, Loc w l, RefTy r ty)
  | TC_Cls   : forall stty rho env f x ec ee ctxt t,
                 TcEnv (stty, env, rho, ctxt) ->
                 TcExp (stty, ctxt, rho, Mu f x ec ee, t, Empty_Static_Action) ->
                 TcVal (stty, rho, Cls (env, rho, Mu f x ec ee), t)
  | TC_Unit : forall stty rho, TcVal (stty, rho, Unit, UnitTy)
  | TC_Eff  : forall stty rho e, TcVal (stty, rho, Eff e, Effect)
                        
with TcEnv : (Sigma * Env * Rho * Gamma) -> Prop :=
  | TC_Env : forall stty env rho ctxt, 
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
                  TcVal (stty, rho, v, t)) ->
               TcEnv (stty, env, rho, ctxt).
                    

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
     (forall ctxt rho e t eff, TcExp (stty, ctxt, rho, e, t, eff) -> TcExp (stty', ctxt, rho, e, t, eff)).
Proof.
 intros stty stty' H ctxt  rho e t eff HTc.
 dependent induction HTc;  
 try (econstructor);
 try (econstructor; eapply IHHTc);
 try (econstructor; [eapply IHHTc1 | eapply IHHTc2]); eauto.
Qed.

Definition get_store_typing {A B C:Type} (p : Sigma * A * B * C) : Sigma   
  := fst (fst (fst p)).

Definition mk_TcVal_ext_store_ty (p : Sigma * Rho * Val * tau) (stty' : Sigma)
  := TcVal (stty', snd (fst (fst p)), snd (fst p), snd p).

Definition mk_TcEnv_ext_store_ty (p : Sigma * Env * Rho * Gamma) (stty' : Sigma)
  := TcEnv (stty',  snd (fst (fst p)), snd (fst p), snd p).

Lemma ext_stores__val_env__aux:
   forall stty stty',
     (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t') -> 
     (forall p,
        TcVal p -> get_store_typing p = stty -> mk_TcVal_ext_store_ty p stty') /\
     (forall p,
        TcEnv p -> get_store_typing p = stty -> mk_TcEnv_ext_store_ty p stty').  
Proof.
  intros stty stty' HWeak. 
  apply tc_val__tc_env__xind; intro stty''; intros; 
  try constructor; try assumption ;  
  unfold mk_TcVal_ext_store_ty, mk_TcEnv_ext_store_ty, get_store_typing in *; simpl in *; 
  try assumption.
  - subst. now apply HWeak.
  - eapply ext_stores__exp in t1.  
    + intuition; econstructor; eauto. 
    + subst; exact HWeak.
  - intuition. eapply H; eauto.
Qed.

Lemma ext_stores__val:
   forall stty stty',
     (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t') -> 
     (forall rho v t, TcVal (stty, rho, v, t) -> TcVal (stty', rho, v, t)).
Proof.
  intros stty stty' HWeak rho v t H. pose HWeak.  
  apply ext_stores__val_env__aux in e. destruct e as [HTc  HEnv].  
  inversion H; subst; try constructor; eauto.
  - eapply ext_stores__exp in H5. 
    + eapply HEnv in H2; [econstructor; eauto | cbv; auto].
    + exact HWeak.
Qed.

Lemma ext_stores__env:
   forall stty stty',
     (forall l t', find_ST l stty = Some t' -> find_ST l stty' = Some t') -> 
     (forall env ctxt rho, TcEnv (stty, env, rho, ctxt) -> TcEnv (stty', env, rho, ctxt)).
Proof.
  intros stty stty' HWeak env ctxt rho H. pose HWeak.  
  apply ext_stores__val_env__aux in e. destruct e as [HTc  HEnv]. 
  unfold mk_TcEnv_ext_store_ty in HEnv. apply HEnv in H. 
  - now simpl in H.
  - now cbv.
Qed.
 
Lemma EmptyIsNil:
  forall phi, phi ⊑ Theta_Empty -> phi = nil.
Proof.
  intros phi H.
  destruct phi as [ | da phi].
  reflexivity.
  inversion H as [ | ? ? ? da_in_Theta_Empty ]; subst.
  inversion da_in_Theta_Empty; subst; contradiction.
Qed.

Lemma EmptyInNil:
  forall theta, nil ⊑ theta.
Proof.
  constructor.
Qed.

Lemma PhiInThetaTop:
  forall phi, phi ⊑ Theta_Top.
Proof.
  induction phi.
  - constructor.
  - repeat constructor. auto.
Qed.

Lemma EnsembleUnionSym :
  forall (phi : Phi) (theta theta' : Theta),
    phi ⊑ theta -> phi ⊑ (Union_Theta theta theta') /\ phi ⊑ (Union_Theta theta' theta).
Proof.
  intros phi theta theta' H. generalize dependent theta'.
  induction H.
  - intros theta'. split; constructor.
  - intros theta'.
    destruct theta as [acts|]; destruct theta' as [acts'|];
    try (split; apply PhiInThetaTop).
    split; constructor; try (apply IHPhi_Theta_Soundness).
    + inversion H; subst;
      [apply DAT_Alloc_Abs |
       apply DAT_Read_Abs | apply DAT_Read_Conc |
       apply DAT_Write_Abs | apply DAT_Write_Conc ];
      apply Union_introl; assumption.
    + inversion H; subst;
      [apply DAT_Alloc_Abs |
       apply DAT_Read_Abs | apply DAT_Read_Conc |
       apply DAT_Write_Abs | apply DAT_Write_Conc ];
      apply Union_intror; assumption.
Qed.

Lemma EnsembleUnionComp :
  forall (phi1 phi2 : Phi) (theta1 theta2 : Theta),
    phi1 ⊑ theta1 -> phi2 ⊑ theta2 -> (phi1 ++ phi2) ⊑ (Union_Theta theta1 theta2).
Proof.
  induction phi1 as [| da phi1].
  - intros phi2 theta1 theta2 H1 H2; simpl.
    apply EnsembleUnionSym with (theta' := theta1) in H2; intuition.
  - intros phi2 theta1 theta2 H1 H2; simpl.
    inversion H1; subst.
    constructor; try (apply IHphi1; auto).
    destruct theta1 as [acts1|]; destruct theta2 as [acts2|]; simpl; try constructor.
    inversion H3; subst;
    [apply DAT_Alloc_Abs |
     apply DAT_Read_Abs | apply DAT_Read_Conc |
     apply DAT_Write_Abs | apply DAT_Write_Conc ];
    apply Union_introl; assumption.
Qed.


Lemma EmptyTracePreservesHeap_1 : 
  forall h r env e same_h v' acts, (h, r, env, e) ⇓ (same_h, v', acts) -> acts = nil -> h = same_h.
Proof.
  intros h r env e same_h v' acts H Hnil. (*destruct H as [H Hnil]. *)
  dependent induction H; auto;
  try (apply List.app_eq_nil in Hnil; destruct Hnil as [Hnil'' Hnil']; subst);
  try (apply List.app_eq_nil in Hnil'; destruct Hnil'; subst);
  try (apply List.app_eq_nil in Hnil; subst).  
  - assert (h=fheap) by (eapply IHBigStep1; eauto).
    intuition; subst.
    assert (aheap=same_h) by (eapply IHBigStep3; eauto).
    subst; reflexivity.
  - intuition; subst. eapply IHBigStep1; eauto.
  - intuition; subst. eapply IHBigStep1; eauto.
  - symmetry in Hnil'. contradict Hnil'.  apply List.nil_cons.
  - symmetry in Hnil'. contradict Hnil'.  apply List.nil_cons.
  - intuition; subst. symmetry in H3. contradict H3.  apply List.nil_cons.
  - assert (h=lheap) by (eapply IHBigStep1; eauto).
    assert (lheap=same_h) by (eapply IHBigStep2; eauto).
    subst; reflexivity.
  - assert (h=lheap) by (eapply IHBigStep1; eauto).
    assert (lheap=same_h) by (eapply IHBigStep2; eauto).
    subst; reflexivity. 
  - assert (h=lheap) by (eapply IHBigStep1; eauto).
    assert (lheap=same_h) by (eapply IHBigStep2; eauto).
    subst; reflexivity.
  - assert (h=lheap) by (eapply IHBigStep1; eauto).
    assert (lheap=same_h) by (eapply IHBigStep2; eauto).
    subst; reflexivity.
  - eapply IHBigStep; eauto. 
  - eapply IHBigStep; eauto.
Qed.

Lemma EmptyTracePreservesHeap_2 : 
  forall h r env e same_h v acts,
    (h, r, env, e) ⇓ (h, v, acts) -> h = same_h -> (same_h, r, env, e) ⇓ (same_h, v, acts).
Proof.
  intros h r env e same_h v' acts Dyn H. now subst.
Qed.

Lemma EmptyTracePreservesHeap_3 : 
  forall h r env e same_h v acts,
    (same_h, r, env, e) ⇓ (same_h, v, acts) -> (h, r, env, e) ⇓ (same_h, v, acts) -> acts = nil -> (h, r, env, e) ⇓ (h, v, acts).
Proof.
  intros h r env e same_h v' acts H Dyn1 Hnil.
  apply EmptyTracePreservesHeap_1 in Dyn1. now subst. exact Hnil.
Qed.
