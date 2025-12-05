Require Import Arith Lia.
Require Import List.
Import ListNotations.

(** * Ordenação por Inserção *)

(* 1. Definições das Funções *)
Fixpoint insert (x:nat) (l: list nat) :=
  match l with
  | [] => [x]
  | h::tl => if (x <=? h)
             then x::l
             else h::(insert x tl)
  end.

Fixpoint insertion_sort (l: list nat) :=
  match l with
  | []  => []
  | h::tl => insert h (insertion_sort tl)
  end.

Require Import Sorted.
Require Import Permutation.

(* 2. Lemmas Auxiliares *)

Lemma insert_perm: forall x l, Permutation (insert x l) (x::l).
Proof.
  intros x l. induction l as [| h tl IHtl].
  - simpl. apply Permutation_refl.
  - simpl. destruct (x <=? h).
    + apply Permutation_refl.
    + apply Permutation_trans with (l' := h :: x :: tl).
      * apply perm_skip. exact IHtl.
      * apply perm_swap.
Qed.

Lemma insert_hd_rel: forall x a l, a <= x -> HdRel le a l -> HdRel le a (insert x l).
Proof.
  intros x a l H_ax H_rel.
  destruct l as [| h tl].
  - simpl. constructor. assumption.
  - simpl. destruct (x <=? h).
    + constructor. assumption.
    + constructor. 
      inversion H_rel. 
      assumption.
Qed.

Lemma insert_sorted: forall x l, Sorted le l -> Sorted le (insert x l).
Proof.
  intros x l H. induction H.
  - simpl. constructor. apply Sorted_nil. constructor.
  - simpl. destruct (x <=? a) eqn:Tes.
    + constructor.
      * constructor; assumption.
      * constructor. apply Nat.leb_le. assumption.
    + constructor.
      * apply IHSorted.
      * apply insert_hd_rel.
        -- apply Nat.leb_gt in Tes. lia.
        -- assumption.
Qed.



(* 3. Teorema Principal *)

Theorem insertion_sort_correct: forall lista, Sorted le (insertion_sort lista) /\ Permutation (insertion_sort lista) lista.
Proof.
  induction lista as [| a resto HipoteseInd].
  
  - (* Caso Base *)
    split. apply Sorted_nil. apply Permutation_refl.
  
  - (* Passo Indutivo *)
    destruct HipoteseInd as [H_ordenada H_permutacao].
    split.
    
    + (* Parte 1: Ordenação *)
      apply insert_sorted. 
      exact H_ordenada.
      
    + (* Parte 2: Permutação *)
      apply Permutation_trans with (l' := a :: insertion_sort resto).
      * apply insert_perm.
      * apply perm_skip. 
        exact H_permutacao.
Qed.