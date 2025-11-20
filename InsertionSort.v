(* ================================================================= *)
(* CONFIGURAÇÃO INICIAL (AMBOS DEVEM TER)               *)
(* ================================================================= *)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Import ListNotations.

[cite_start](* Definição da função insert (Copiado do PDF [cite: 9-15]) *)
Fixpoint insert (x:nat) (l: list nat) :=
  match l with
  | [] => [x]
  | h::tl => if (x <=? h)
             then x::l
             else h::(insert x tl)
  end.

[cite_start](* Definição da função insertion_sort (Copiado do PDF [cite: 17-21]) *)
Fixpoint insertion_sort (l: list nat) :=
  match l with
  | [] => []
  | h::tl => insert h (insertion_sort tl)
  end.

(* ================================================================= *)
(* PARTE DA PESSOA 1: Lemmas Auxiliares                 *)
(* ================================================================= *)

(* Tarefa 1: Provar que inserir um elemento numa lista resulta numa 
   permutação da lista original mais aquele elemento.
*)
Lemma insert_perm: forall x l, Permutation (insert x l) (x::l).
Proof.
  (* DICA: Faça indução em l. *)
  (* Quando terminar, troque 'Admitted' por 'Qed'. *)
Admitted. 

(* Tarefa 2: Provar que se a lista 'l' já é ordenada, inserir 'x'
   nela mantém a propriedade de estar ordenada.
   [cite_start]Isso é sugerido explicitamente no enunciado[cite: 16].
*)
Lemma insert_sorted: forall x l, Sorted le l -> Sorted le (insert x l).
Proof.
  (* DICA: Faça indução em l. Vai precisar analisar os casos
     x <= h e x > h usando destruct. *)
  (* Quando terminar, troque 'Admitted' por 'Qed'. *)
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