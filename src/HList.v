Require Import List.
Require Import Coq.Program.Equality.

Set Implicit Arguments.

Import ListNotations.
Local Open Scope list.

Generalizable Variables ty.

Section HList.
  Context (A:Type).
  Context (B:A -> Type).

  Implicit Types (ty: list A).

  Inductive hlist : list A -> Type :=
  | Nil : hlist []
  | Cons : forall T (x:B T) ty (l:hlist ty), hlist (T::ty).

  Inductive member (T:A) : list A -> Type :=
  | HFirst : forall ty, member T (T::ty)
  | HNext : forall T' ty, member T ty -> member T (T'::ty).
  Arguments HFirst {T ty}.
  Arguments HNext {T T' ty}.

  Fixpoint hget T `(ls: hlist ty) : member T ty -> B T.
    destruct ls as [ | ? x ? ls'].
    - intro mem.
      refine (match mem in member _ ls' return
                    (match ls' with
                     | nil => B T
                     | _ :: _ => unit
                     end) with
              | HFirst => tt
              | HNext _ => tt
              end).
    - intro mem.
      refine (match mem in member _ ls' return (match ls' with
                                                | nil => Empty_set
                                                | x' :: ls'' =>
                                                  B x' -> (member T ls'' -> B T) -> B T
                                                end) with
              | HFirst => fun x _ => x
              | HNext mem' => fun _ get' => get' mem'
              end x (hget _ _ ls')).
  Defined.

  Theorem hget_cons T `(ls: hlist ty) (m: member T ty) T' (x: B T') :
    hget (Cons x ls) (HNext m) = hget ls m.
  Proof.
    reflexivity.
  Qed.

  Fixpoint member_shift T `(m: member T ty) ty' : member T (ty ++ ty').
    destruct m; simpl.
    - exact HFirst.
    - exact (HNext (member_shift _ _ m ty')).
  Defined.

  Fixpoint happ `(ls1: hlist ty1) `(ls2: hlist ty2) :
    hlist (ty1 ++ ty2).
    destruct ls1; simpl.
    - exact ls2.
    - exact (Cons x (happ _ ls1 _ ls2)).
  Defined.

  Theorem happ_hget `(ls1: hlist ty1) `(ls2: hlist ty2) T (m: member T _) :
    hget (happ ls1 ls2) (member_shift m _) = hget ls1 m.
  Proof.
    generalize dependent m.
    generalize dependent T.
    generalize dependent ls2.
    induction ls1; intros.
    - exfalso; inversion m.
    - dependent destruction m; simpl; auto.
  Qed.

End HList.
