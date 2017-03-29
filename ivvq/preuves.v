Require Import List. Import ListNotations.
Set Implicit Arguments.

(** * Preuve assistée en Coq *)

(** Premier exemple de théorème *)
Parameters (p q : Prop).
Theorem th0 : p -> (p -> q) -> q.
Proof.
  exact (fun x (f : p -> q) => f x).
Qed.

Theorem th : p -> (p -> q) -> q.
Proof. auto. Qed.

Print th.
(* th = fun (H : p) (H0 : p -> q) => H0 H
 : p -> (p -> q) -> q *)

(** Exemple d'utilisation de "reflexivity" *)
Lemma facile : 1 + 1 = 2.
reflexivity.
Qed.

(** Exemple d'utilisation de "rewrite" *)
Lemma exemple (pred : nat -> nat) (E : forall n : nat, 0 < n -> S (pred n) = n) (n : nat) :
  S (pred (2 * (n + 1))) = 2 * n + 2.
rewrite E.
Show 1.
Show 2.
Abort.

(** Exemple d'utilisation de "apply" *)
Lemma exemple (le_S : forall n m, n <= m -> n <= S m) (n : nat) :
  n <= S (S n).
apply le_S.
Show 1.
Abort.

(** Exemple d'utilisation de "induction" *)
Theorem add_comm : forall n m : nat, n + m = m + n.
induction n.
Show 1.
Show 2.
Abort.

(** Exemple d'utilisation de "destruct" *)
Theorem addn1_neq0 : forall n : nat, n + 1 <> 0.
destruct n.
Show 1.
Show 2.
Abort.

(** Exemple d'utilisation de "simpl" *)
Lemma example (n : nat) : 1 + n = n + 1.
simpl.
Abort.

(** ** Exemples et exercices autour des listes *)
Print rev.
Print "++".

Lemma app_nil :
  forall T (l : list T), l = l ++ [].
Proof.
induction l.
  simpl.
  reflexivity.
simpl.
rewrite <- IHl. (* utilise l'hypothèse d'induction *)
reflexivity.
Qed.

Lemma app_assoc :
  forall T (l1 l2 l3 : list T),
  l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof.
induction l1; simpl; intros; auto.
rewrite IHl1.
reflexivity.
Qed.

Lemma rev_app_distr :
  forall T (l1 l2 : list T),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
induction l1; simpl; intros.
  apply app_nil.
rewrite IHl1.
rewrite app_assoc.
reflexivity.
Qed.

Theorem rev_involutive :
  forall T (l : list T),
  rev (rev l) = l.
Proof.
Admitted.
