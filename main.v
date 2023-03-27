From Coq Require Import Sets.Ensembles.
From Coq Require Import Relations_1.
From Coq Require Import Bool.
Section Groups.
Variable U : Type.

(*Binary operation.*)
Definition binop :=U->U->U.

Definition Group (G : Ensemble U) (star : binop) : Prop:=
(
    (forall (a b c: U), In U G a /\ In U G b /\ In U G c->
    In U G (star a b)) (*Being closed under operator*)
    /\
    (forall (a b c: U), In U G a /\ In U G b /\ In U G c->
    star a (star b c) = star (star a b) c) (*Associativity*)
    /\
    exists e: U, In U G e /\ (forall d: U, In U G d -> star e d = d /\ star d e = d) (*Existence of identity*)
    /\
    forall d: U, In U G d -> (exists d': U, In U G d' /\ star d d'= e /\ star d' d = e) (*Invertibality*)
).
(*More Variables:*)
Variable G : Ensemble U.
Variable star : binop.


Notation "x ** y" := (star x y) (at level 40, left associativity).

(*Associativiy:*)
Lemma assoc:
Group G star -> (forall (a b c: U), In U G a /\ In U G b /\ In U G c-> a ** (b ** c) = star (star a b) c).
Proof.
    intros H a b c H1. apply H. apply H1.
    Qed.

(*Identity element:*)
Variable e : U.
Definition Group_iden G star e : Prop :=
    Group G star /\ In U G e -> forall d : U, In U G d -> d**e=d /\ e**d=d.

Lemma iden_l : 
Group G star -> In U G e -> Group_iden G star e ->
    forall d :U, In U G d -> e**d = d.
    Proof.
        intros H H0 H1 d H2. apply H1. +split. ++apply H.
        ++apply H0. +apply H2.
    Qed.
Lemma iden_r : 
Group G star -> In U G e -> Group_iden G star e ->
    forall d :U, In U G d -> d**e = d.
    Proof.
        intros H H0 H1 d H2. apply H1. +split. ++apply H.
        ++apply H0. +apply H2.
    Qed.

(*Inverse element:*)
Definition inv_prop (a a' : U) : Prop :=
    Group G star -> Group_iden G star e -> In U G a -> In U G a' -> a ** a' = e /\ a'**a = e.

Lemma inv_l:
    Group G star -> Group_iden G star e -> 
    forall a a':U, In U G a -> In U G a' -> inv_prop a a' -> a' ** a = e.
    Proof.
        intros H H1 a a' H2 H3 H4. apply H4.
        +apply H. +apply H1. +apply H2. +apply H3.
    Qed. 
Lemma inv_r:
    Group G star -> Group_iden G star e -> 
    forall a a':U, In U G a -> In U G a' -> inv_prop a a' -> a ** a' = e.
    Proof.
        intros H H1 a a' H2 H3 H4. apply H4.
        +apply H. +apply H1. +apply H2. +apply H3.
    Qed.
    

(*Multiplying an element on two sides of an equality:*)
Lemma eq_mul_l : 
Group G star -> forall (a b c:U), b = c -> star a b = star a c.
Proof. 
    intros H a b c H1. rewrite -> H1. reflexivity.
    Qed.

Lemma eq_mul_r : 
Group G star -> forall (a b c:U), b = c -> b ** a = c **a.
Proof. 
    intros H a b c H1. rewrite -> H1. reflexivity.
    Qed.


(*(*Cancellation laws:*)
Lemma cancel_l : 
Group G star -> forall (a b c:U),
In U G a /\ In U G b /\ In U G c ->
star a b = star a c -> b = c.
Proof.
    intros H a b c H1 H2. unfold Group in H. destruct H.
    destruct H0. destruct H3. destruct H3. destruct H4.
    assert (H12: exists a', In U G a' -> a ** a' = e /\ a' ** a = e).
    +destruct H1. apply H5 in H1. destruct H1. 
    exists x0. intros H54. split. ++apply H1.
    rewrite -> eq_mul_l with (a:=a'). *)




End Groups.










Definition add (a b:bool):=a || b.
Definition adib : binop bool := add. 
Theorem disj_group: forall (G : Ensemble bool) , (forall (n:bool), In bool G n)
->Group bool G adib.
Proof.
    intros G H. unfold Group. split.
    +intros a b c H0. apply H. +split.
    ++intros a b c H0. unfold adib. unfold add. apply orb_assoc. 
    ++exists false. split. +++apply H. +++split.
    ++++intros d H1. split. +++++unfold adib. unfold add. simpl. reflexivity.
    +++++unfold adib. unfold add. rewrite -> orb_commutative.  

Qed.



