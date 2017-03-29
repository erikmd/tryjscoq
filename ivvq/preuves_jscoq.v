(* Le préfixe "From Coq" serait inutile avec CoqIDE *)
From Coq Require Import Init.Prelude Unicode.Utf8.
From Coq Require Import List. Import ListNotations.
Set Implicit Arguments.

(** * Preuve assistée par Coq *)

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

(** * Exercices : preuve de programmes fonctionnels sur les entiers/listes *)

Lemma plus_n_0 : forall n : nat, n + 0 = n.
Proof.
Admitted.

Lemma plus_n_Sm : forall n m, n + S m = S (n + m).
Proof.
Admitted.

Theorem plus_comm : forall a b, a + b = b + a.
Proof.
Admitted.

(* Lemma app_len :
   (* la longueur de la concaténation de deux listes
      est la somme des longueurs des listes *)
 *)

Theorem rev_len :
  forall T (l : list T), length (rev l) = length l.
Proof.
Admitted.

(* Exercices pour les plus rapides :
 - Prouver quelle est la longueur des listes renvoyées par la fonction hanoi.
 - Plus difficile : spécifier & prouver que le tri par insertion est correct.
 *)
