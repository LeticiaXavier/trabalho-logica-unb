Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Import ListNotations.

(* Definição da função insert *)
Fixpoint insert (x:nat) (l: list nat) :=
  match l with
  | [] => [x]
  | h::tl => if (x <=? h)
             then x::l
             else h::(insert x tl)
  end.

(* Definição da função insertion_sort *)
Fixpoint insertion_sort (l: list nat) :=
  match l with
  | [] => []
  | h::tl => insert h (insertion_sort tl)
  end.

(* ================================================================= *)
(* PARTE DA PESSOA 1: Lemmas Auxiliares                              *)
(* ================================================================= *)

(* Tarefa 1: Provar que inserir um elemento numa lista resulta numa 
   permutação da lista original mais aquele elemento. *)
Lemma insert_perm: forall x l, Permutation (insert x l) (x::l).
Proof.
  intros x l. induction l as [| h tl IHtl].
  - (* Caso Base: Lista vazia *)
    simpl. apply Permutation_refl.
  - (* Passo Indutivo *)
    simpl. destruct (x <=? h).
    + (* Caso x <= h *)
      apply Permutation_refl.
    + (* Caso x > h *)
      apply Permutation_trans with (l' := h :: x :: tl).
      * apply perm_skip. exact IHtl.
      * apply perm_swap.
Qed.

(* Tarefa 2: Provar que se a lista 'l' já é ordenada, inserir 'x'
   nela mantém a propriedade de estar ordenada. *)
Lemma insert_sorted: forall x l, Sorted le l -> Sorted le (insert x l).
Proof.
  intros x l H. induction H.
  - (* Caso Base: Lista vazia *)
    simpl. constructor. apply Sorted_nil. constructor.
  
  - (* Passo Indutivo *)
    simpl. destruct (x <=? a) eqn:Tes.
    + (* Caso x <= a: O x fica na frente. *)
      constructor.
      * constructor; assumption.
      * constructor. apply Nat.leb_le. assumption.
      
    + (* Caso x > a: O x vai para o meio/fim. *)
      constructor.
      * apply IHSorted. 
      * (* A parte aritmética chata. Admitimos para focar na lógica. *)
        admit. 
Admitted.



(* ================================================================= *)
(* PARTE DA PESSOA 2: Teorema Principal                 *)
(* ================================================================= *)

(* Tarefa Principal: Mostrar que o insertion_sort retorna uma lista
   que é AO MESMO TEMPO (/\) ordenada e uma permutação da original.
   [cite_start]Objetivo definido no enunciado [cite: 23-25].
*)
Theorem insertion_sort_correct: forall l,
  Sorted le (insertion_sort l) /\ Permutation (insertion_sort l) l.
Proof.
  induction l.
  - (* Caso Base: Lista vazia *)
    split.
    + apply Sorted_nil. (* Lista vazia é ordenada *)
    + apply Permutation_refl. (* Lista vazia é permutação de si mesma *)
  
  - (* Passo Indutivo: h :: tl *)
    destruct IHl as [H_sorted H_perm]. (* Quebra a hipótese em duas partes *)
    split.
    
    + (* Sub-objetivo 1: Provar que o resultado é Ordenado *)
      (* AQUI VOCÊ USA O TRABALHO DA PESSOA 1 *)
      apply insert_sorted. 
      assumption. (* Usa a hipótese H_sorted *)
      
    + (* Sub-objetivo 2: Provar que é Permutação *)
      (* AQUI VOCÊ USA O TRABALHO DA PESSOA 1 TAMBÉM *)
      (* Dica: A prova vai exigir transitividade da permutação.
         Você sabe que (insert h (insertion_sort tl)) é permutação de 
         (h :: insertion_sort tl) pelo lemma insert_perm. *)
      
      (* Tente terminar essa parte... *)
Admitted.






(* ================================================================= *)
(* ÁREA DE TESTES (Pode apagar depois se quiser)                    *)
(* ================================================================= *)

(* Teste 1: Inserir 3 numa lista que já tem 1, 2, 4, 5 *)
(* Esperado: [1; 2; 3; 4; 5] *)
Compute (insert 3 [1; 2; 4; 5]).

(* Teste 2: Inserir numa lista vazia *)
(* Esperado: [5] *)
Compute (insert 5 []).

(* Teste 3: Inserir um número menor que todos (no começo) *)
(* Esperado: [0; 2; 4] *)
Compute (insert 0 [2; 4]).

(* Teste 4: Inserir um número maior que todos (no fim) *)
(* Esperado: [1; 2; 9] *)
Compute (insert 9 [1; 2]).

(* Teste Unitário: O Coq só aceita isso se o resultado for EXATAMENTE igual *)
Example teste_ordenacao: insert 3 [1; 4; 5] = [1; 3; 4; 5].
Proof.
  simpl.       (* Roda a função *)
  reflexivity. (* Verifica se esquerda == direita *)
Qed.






