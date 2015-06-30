Require Import Definitions2.
Require Import Ascii.

Definition Fact_Body : Expr
  := Cond (Eq (Var "x"%char) (Const 0))
          (Const 1)
          (Times (Var "x"%char) (Mu_App (Var "f"%char) (Minus (Var "x"%char) (Const 1)))).

Definition Fact_Eff : Expr
  := Cond (Eq (Var "x"%char) (Const 0))
          Empty
          (Empty ⊕ (Eff_App (Var "f"%char) (Minus (Var "x"%char) (Const 1)))).

(*
Definition Fact_Eff : Expr
  := Empty.
*)

Definition Mu_Fact : Expr
  := Mu "f"%char "x"%char Fact_Body Fact_Eff.

Lemma Mu_Fact__well_typed :
  forall stty ctxt rgns,
    TcExp (stty, ctxt, rgns, Mu_Fact, Ty2_Arrow Ty2_Natural Empty_Static_Action Ty2_Natural Empty_Static_Action Ty2_Effect, Empty_Static_Action).
Proof.
  intros.
  unfold Mu_Fact, Fact_Body, Fact_Eff.
  repeat econstructor.
Admitted.


(*


Gamma; Assms |- exp : ty ! eff

A(f, x, ee) ~=~ capp f x << ee
B(f, ee) ~=~ forall z, capp f z << ee

f \notin Gamma
x \notin Gamma
Gamma, f : ty_a -> (ty_r ! effc | eff ! effe), x : ty_a ; Assms, A(f, x, ee) |- ec : ty_r ! effc
Gamma, f : ty_a -> (ty_r ! effc | eff ! effe), x : ty_a ; Assms, A(f, x, ee) |- ee : eff ! effe
Gamma, f : ty_a -> (ty_r ! effc | eff ! effe), x : ty_a ; Assms, A(f, x, ee) |- ec << ee
----------------------------------------------------------------------------------------------------
Gamma; Assms |- mu f x (ec, ee) : ty_a -> (ty_r ! effc | eff ! effe) ! \empty

f \notin Gamma
x \notin Gamma
x \notin FV(ee)
Gamma, f : ty_a -> (ty_r ! effc | eff ! effe), x : ty_a ; Assms, B(f, ee) |- ec : ty_r ! effc
Gamma, f : ty_a -> (ty_r ! effc | eff ! effe), x : ty_a ; Assms, B(f, ee) |- ee : eff ! effe
Gamma, f : ty_a -> (ty_r ! effc | eff ! effe), x : ty_a ; Assms, B(f, ee) |- ec << ee
----------------------------------------------------------------------------------------------------
Gamma; Assms |- mu f x (ec, ee) : ty_a -> (ty_r ! effc | eff ! effe) ! \empty


Gamma; Assms |- e1 : int ! eff1
Gamma; Assms|eff1 |- e2 : int ! eff2
-------------------------------------------------
Gamma; Assms |- e1 + e2 : int ! eff1 \union eff2



Assms|eff = if RO(eff) then Assms else \empty

RO(eff) ==> Assms|eff == Assms




Gamma; Assms |- ec << ee

A(f, x, ee) \in Assms
------------------------------
Gamma; Assms |- capp f x << ee

B(f, ee) \in Assms
-------------------------------
Gamma; Assms |- capp f ea << ee


x \notin FV(ee)

(forall z : capp f z << ee) |- ec << ee
------------------------------------------
??? |- mu f x (ec, ee) : 


=====


x \in FV(ee)

capp f x << ee |- ec << ee
------------------------------------------
??? |- mu f x (ec, ee) : 


*)
