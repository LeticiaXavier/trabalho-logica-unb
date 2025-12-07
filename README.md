# 🛡️ Formalização do Insertion Sort em Coq/Rocq

Este repositório contém o projeto final da disciplina de **Lógica Computacional 1** (UnB - 2025/2), focado na verificação formal da correção do algoritmo de ordenação *Insertion Sort* utilizando o assistente de provas **Coq (Rocq)**.

## 🎯 Objetivo
Demonstrar matematicamente que o algoritmo `insertion_sort` satisfaz as seguintes propriedades:
1.  **Ordenação:** A lista resultante está devidamente ordenada segundo a relação `le` ($\le$).
2.  **Permutação:** A lista resultante é uma permutação exata da lista de entrada, garantindo a integridade dos dados.

## 🗂️ Estrutura do Projeto

* **`InsertionSort.v`**: Arquivo principal contendo a formalização completa:
    * Definições das funções recursivas `insert` e `insertion_sort`.
    * Lemmas auxiliares para preservação de elementos e manutenção da ordem.
    * Teorema de correção total: `insertion_sort_correct`.
* **`relatorio.pdf`**: Documentação detalhada contendo a estruturação das provas em linguagem natural e explicações sobre o desenvolvimento.
* **`_CoqProject`**: Arquivo de configuração para o mapeamento lógico das bibliotecas do Rocq.

## 🛠️ Tecnologias e Táticas

* **Ferramenta:** Coq (Rocq).
* **Bibliotecas utilizadas:** `Arith`, `List`, `Sorted`, `Permutation` e `Lia`.
* **Destaques Técnicos:**
    * Aplicação de **Indução Estrutural** na prova de propriedades de listas.
    * Uso da tática **`Lia` (Linear Integer Arithmetic)** para automatizar a verificação de desigualdades aritméticas nos lemmas de ordenação.
    * Estratégia de **Divisão e Conquista** para simplificar as provas principais através de resultados auxiliares.

## 🚀 Como Executar

### Pré-requisitos
* **Coq Platform** ou **Rocq** instalado no sistema.

### Compilação e Verificação
Para compilar o projeto e verificar a validade das provas via terminal, utilize o compilador `coqc`:

```bash
coqc InsertionSort.v

[Letícia Xavier de Almeida Silva]
[Rafael Silva Lima]
