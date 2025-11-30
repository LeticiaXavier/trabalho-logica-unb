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