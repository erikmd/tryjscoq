(* Le préfixe "From Coq" serait inutile avec CoqIDE *)
From Coq Require Import Init.Prelude Unicode.Utf8.
From Coq Require Import List. Import ListNotations.
Set Implicit Arguments.

Module Type Monoide.
  Parameter T : Type.           (* une sorte *)
  Parameter un : T.             (* une constante *)
  Parameter prod : T -> T -> T. (* une opération *)

  Axiom assoc : forall x y z:T, prod x (prod y z) = prod (prod x y) z.
  Axiom neutre_g : forall x, prod un x = x.
  Axiom neutre_d : forall x, prod x un = x.
End Monoide.

Module MonoList <: Monoide. (* vérification sans masquage *)
  Definition T := list nat.
  Definition un : T := [].
  Definition prod (x y : T) := x ++ y.
  Lemma assoc : forall x y z:T, prod x (prod y z) = prod (prod x y) z.
  Proof. apply app_assoc. Qed.
  Lemma neutre_g : forall x, prod un x = x.
  Proof. reflexivity. Qed.
  Lemma neutre_d : forall x, prod x un = x.
  Proof. induction x; auto. simpl. rewrite IHx. reflexivity. Qed.
End MonoList.

Module Use (M : Monoide).
  Theorem unicite : forall u : M.T, (forall x, M.prod x u = x) -> u = M.un.
  Proof.
  intros u Hu.
  rewrite <-(Hu M.un).
  rewrite M.neutre_g.
  reflexivity.
  Qed.
End Use.

Module Inst := Use(MonoList).
Check Inst.unicite.
(* : forall u : MonoList.T, (forall x : MonoList.T, MonoList.prod x u = x) -> u = MonoList.un *)

Print MonoList.un.
(* MonoList.un = [] : MonoList.T *)
Print MonoList.T.
(* MonoList.T = list nat : Set *)

Module Type Pile.
  Parameter Elem: Type.
  Parameter P: Type.

  Parameter vide: P.
  Parameter push: Elem -> P -> P.
  Parameter estVide: P -> bool.
  Parameter pop: P -> P.
  Parameter top: P -> option Elem.

  Axiom estVide_vide: estVide vide = true.
  Axiom estVide_push: forall p e, estVide (push e p) = false.
  Axiom top_vide: top vide = None.
  Axiom top_push: forall p e, top (push e p) = Some e.
  Axiom pop_vide: pop vide = vide.
  Axiom pop_push: forall p e, pop (push e p) = p.
End Pile.

Module Pile_Liste <: Pile.
  Definition Elem := nat.
  Definition P := list nat.
  Definition vide : P := [].
  Definition push (e: Elem) (p: P) := e :: p.
  Definition estVide (p: P) :=
    match p with [] => true | _ => false end.
  Definition top (p: P) :=
    match p with [] => None | x :: _ => Some x end.
  Definition pop (p: P) :=
    match p with [] => [] | _ :: l => l end.

  Lemma estVide_vide: estVide vide = true.
  Proof.
  Admitted.

  Lemma estVide_push: forall p e, estVide (push e p) = false.
  Proof.
  Admitted.

  Lemma top_vide: top vide = None.
  Proof.
  Admitted.

  Lemma top_push: forall p e, top (push e p) = Some e.
  Proof.
  Admitted.

  Lemma pop_vide: pop vide = vide.
  Proof.
  Admitted.

  Lemma pop_push: forall p e, pop (push e p) = p.
  Proof.
  Admitted.
End Pile_Liste.


Module Pile_QListe <: Pile.
  Definition Elem := nat.
  Definition P := list nat.
  Definition vide : P := [].
  Definition push (e: Elem) (p: P) := p ++ [e].
  Definition estVide (p: P) :=
    match p with [] => true | _ => false end.
  Fixpoint top (p: P) :=
    match p with
    | [] => None
    | [e] => Some e
    | x :: l => top l
    end.
  Fixpoint pop (p: P) :=
    match p with
    | [] => []
    | [e] => []
    | x :: l => x :: pop l
    end.

  Lemma estVide_vide: estVide vide = true.
  Proof.
  Admitted.

  Lemma estVide_push: forall p e, estVide (push e p) = false.
  Proof.
  Admitted.

  Lemma top_vide: top vide = None.
  Proof.
  Admitted.

  Lemma top_push: forall p e, top (push e p) = Some e.
  Proof.
  Admitted.

  Lemma pop_vide: pop vide = vide.
  Proof.
  Admitted.

  Lemma pop_push: forall p e, pop (push e p) = p.
  Proof.
  Admitted.

End Pile_QListe.
