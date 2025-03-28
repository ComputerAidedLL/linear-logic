(* Encode linear logic connectives and rules. (Combines Pfenning, Power/Webster, and Gwenn-Bosser's approaches.)
Defines the notation for them and for manipulating the environment 
(multiset of linear props). *)

From Stdlib Require Export Multiset.
From Stdlib Require Import PeanoNat.
Set Implicit Arguments.

Definition Var : Type := nat.

(* ILL connectives -- combination of those given by Pfenning + AGB's encoding *)
Inductive LinProp : Type :=
  (* Atomic *)
  | LProp : Var -> LinProp
  (* Multiplicative *)
  | Implies : LinProp -> LinProp -> LinProp (* -o *)
  | Times : LinProp -> LinProp -> LinProp (* (X) *)
  | One : LinProp                         (* Multiplicative identity TODO *)
  (* Additive *)
  | With : LinProp -> LinProp -> LinProp (* & *)
  | Plus : LinProp -> LinProp -> LinProp (* (+) *)
  | Top : LinProp                        (* aka True? *)
  | Zero : LinProp                       (* Additive identity TODO *)
  (* Exponentials *)
  | Bang : LinProp -> LinProp.

Notation "A -o B" := (Implies A B) (at level 98, left associativity).
Notation "A ** B" := (Times A B) (at level 98, left associativity).
Notation "A && B" := (With A B) (at level 40, left associativity).
Notation "A ++ B" := (Plus A B) (at level 60, right associativity). (* watch out *)
Notation "! A" := (Bang A) (at level 98, left associativity).

Definition env : Type := multiset LinProp.

(* Equality of LinProps (needed for multisets) *)
Fixpoint eqLPC (f1 f2 : LinProp) : bool := 
  match f1, f2 with
    | One, One => true
    | Zero, Zero => true
    | Top, Top => true
    | LProp v1, LProp v2 => Nat.eqb v1 v2
    | Bang f1_1, Bang f2_1 => eqLPC f1_1 f2_1
    | Implies f1_1 f1_2, Implies f2_1 f2_2 =>
      andb (eqLPC f1_1 f2_1) (eqLPC f1_2 f2_2)
    | Times f1_1 f1_2, Times f2_1 f2_2 =>
      andb (eqLPC f1_1 f2_1) (eqLPC f1_2 f2_2)
    | With f1_1 f1_2, With f2_1 f2_2 =>
      andb (eqLPC f1_1 f2_1) (eqLPC f1_2 f2_2)
    | Plus f1_1 f1_2, Plus f2_1 f2_2 =>
      andb (eqLPC f1_1 f2_1) (eqLPC f1_2 f2_2)
    | _, _ => false
  end.

Definition eqLinProp (f1 f2 : LinProp) :=
  eqLPC f1 f2 = true. (* lift computational into propositional *)

Lemma eq_neq_LinProp : forall (f1 f2 : LinProp),
                         {eqLinProp f1 f2} + {~ eqLinProp f1 f2}.
Proof.
  Set Printing All.
  intros.
  (* SearchAbout sumbool. *)
  (* Print eq_nat_decide. *)
  (* Print sumbool.  *)
  destruct f1; destruct f2; try reflexivity; try auto.
  (* TODO: might need to use the "remember as" trick. anyway this is decidable *)
Admitted.

(* Things about multisets of linear props, which is how the environment is represented *)
Definition singleton := SingletonBag eqLinProp eq_neq_LinProp.

Definition inSet {A : Type} (m : multiset A) (x : A) : Prop :=
  multiplicity m x > 0.

Definition setMinus (m : multiset LinProp) (e : LinProp) : multiset LinProp :=
  Bag (fun (x : LinProp) => if eq_neq_LinProp e x
                            then multiplicity m x - 1
                            else multiplicity m x).

Notation "{{ Z }}" := (singleton Z) (at level 5, Z at level 99, right associativity).
Notation "S == T" := (meq S T) (at level 1, left associativity).
Notation "g1 'U' g2" := (munion g1 g2) (at level 100, right associativity).
Notation "Z :: g" := (munion (singleton Z) g) (at level 60, right associativity).
Notation "x ∈ S" := (inSet S x) (at level 60, right associativity).
Notation "S \ x" := (setMinus S x) (at level 60, right associativity).

Reserved Notation "A '|-' B" (at level 3).

(* Here, (->) (Coq implication) denotes (--------) (logic "lines") *)
(* convention: env name lowercase, prop name uppercase *)
(* gamma = classical resources; delta = linear resources (after Pfenning)
     can I encode this at the type level? TODO. right now there might be problems with (!) because it doesn't distinguish *)

Inductive LinProof : env -> LinProp -> Prop :=
  | Id : forall (g : env) (A : LinProp),
           (g == {{A}}) ->
           g |- A

  (* Multiplicative connectives *)
  | Impl_R : forall (g : env) (A B : LinProp),
              (A :: g) |- B ->
              g |- (A -o B)

  (* basically, if you can prove the assump A, then you can have the conclusion B *)
  | Impl_L : forall (g d1 d2 : env) (A B C : LinProp),
               (A -o B) ∈ g ->
               (g \ (A -o B)) == (d1 U d2) ->
               d1 |- A ->
               (B :: d2) |- C ->
               g |- C

  | Times_R : forall (g d1 d2 : env) (A B : LinProp),
                g == (d1 U d2) ->
                d1 |- A ->
                d2 |- B ->
                g |- (A ** B)

  | Times_L : forall (g : env) (A B C : LinProp),
                (A ** B) ∈ g ->
                (A :: B :: (g \ (A ** B))) |- C ->
                g |- C

  | One_R : forall (g : env),
              g == (EmptyBag LinProp) ->
              g |- One

  | One_L : forall (g : env) (C : LinProp),
              One ∈ g ->
              (g \ One) |- C ->
              g |- C

  (* Additive connectives *)
  (* With = internal choice *)
  | With_R : forall (g : env) (A B : LinProp),
               g |- A ->
               g |- B ->
               g |- (A && B)

  | With_L1 : forall (g : env) (A B C : LinProp),
                (A && B) ∈ g ->
                (A :: (g \ (A && B))) |- C ->
                g |- C

  | With_L2 : forall (g : env) (A B C : LinProp),
                (A && B) ∈ g ->
                (B :: (g \ (A && B))) |- C ->
                g |- C

  | Top_R : forall (g : env),
              g |- Top

  (* (* Plus = external choice *) *)
  | Plus_R1 : forall (g : env) (A B : LinProp),
                g |- A ->
                g |- (A ++ B)

  | Plus_R2 : forall (g : env) (A B : LinProp),
                g |- B ->
                g |- (A ++ B)

  | Plus_L : forall (g : env) (A B C : LinProp),
               (A ++ B) ∈ g ->
               (A :: (g \ (A ++ B))) |- C ->
               (B :: (g \ (A ++ B))) |- C ->
               g |- C

  | Zero_L : forall (g : env) (C : LinProp),
               Zero ∈ g ->
               g |- C

  (* Quantifiers: included in Coq *)

  (* Exponentials *)
  (* TODO: implication is included in Coq *)

  (* Bang_R is a rule from Pfenning (Bang_L superseded by Bang_Replace) *)
  (* NOTE: the linear context has to be empty here; everything in g needs to be classical *)
  | Bang_R : forall (g : env) (A : LinProp),
               g |- A ->
               g |- !A

  | Bang_Replace : forall (g : env) (A C : LinProp),
                     (!A) ∈ g ->
                     (A :: (g \ (!A))) |- C ->
                     g |- C

  | Bang_Replicate : forall (g : env) (A C : LinProp),
                     (!A) ∈ g ->
                     ((!A) :: g) |- C ->
                     g |- C 

  | Bang_Remove : forall (g : env) (A C : LinProp),
                    (!A) ∈ g ->
                    (g \ (!A)) |- C ->
                    g |- C 

  where "x |- y" := (LinProof x y).

(* Various other ILL axioms here *)

(* Linear cut: 
gamma is eliminated from pfenning's version *)
(* Need to synthesize an A *)
Axiom cut : forall (g d1 d2 : env) (A C : LinProp),
              g == (d1 U d2) ->
              d1 |- A ->
              (A :: d2) |- C ->
              g |- C.

(* Factory cut -- note g' and d, not d1 and d2 *)
Axiom cut_fact : forall (g g' d : env) (A C : LinProp),
                   g == (g' U d) ->
                   g' |- A ->
                   ((A :: g') U d) |- C ->
                   g |- C.
