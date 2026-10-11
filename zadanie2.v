(*********************************************)
(**       Zadanie k prednáške 2             **)
(*Import potrebných knižníc*)
From Corelib Require Import Init.Nat.
From Stdlib Require Import Bool.Bool Arith.PeanoNat Lists.List.
Import ListNotations.
Local Open Scope nat_scope.

(*
==================================================
Doplnok k prednáške:
==================================================
Základná tabuľka operátorov v Rocq
==================================================

1 Porovnávacie operátory pre nat (vracajú bool)
--------------------------------------------------
  n =? m    : test rovnosti (true ak n = m, inak false)
  n <=? m   : menšie alebo rovné
  n <? m    : menšie

Príklady:
  Compute (3 <=? 5).  (* true *)
  Compute (5 =? 3).   (* false *)
  Compute (4 <? 4).   (* false *)

--------------------------------------------------
2 Logické operátory pre bool
--------------------------------------------------
  negb b        : -
  andb b1 b2    : b1 && b2
  orb b1 b2     : b1 || b2
  xorb b1 b2    : -

Príklady:
  Compute (andb true false).   (* false *)
  Compute (orb true false).    (* true *)
  Compute (negb true).         (* false *)
  Compute (xorb true false).   (* true *)

--------------------------------------------------
3 Logické operátory pre Prop (dôkazy)
--------------------------------------------------
  P /\ Q        : P AND Q
  P \/ Q        : P OR Q
  ~ P           : NOT P
  P -> Q        : implikácia
  P <-> Q       : ekvivalencia

Poznámka: Prop je sort logických tvrdení; dôkaz tvrdenia P má typ P.
          bool je typ s hodnotami true a false.

==================================================
*)


(*
==================================================
Rozdiel medzi bool a Prop pri porovnaniach
==================================================

V Rocq existujú dve “verzie” porovnania pre nat:

bool – programovo vyhodnocovateľná hodnota
  - Napr. n =? m alebo n <=? m vracia true/false (typu bool)
  - Používa sa pri výpočtoch, Compute, if vetveniach
  - Príklad: Compute (3 <=? 5).  (* true *)

Prop – logické tvrdenie
  - Napr. n = m alebo n <= m typu Prop
  - Používa sa pri dôkazoch, rewrite, indukcii
  - Príklad: forall n m : nat, n <= m -> ...

Otáznik (?):
  - n =? m, n <=? m, n <? m vracajú bool
  - Zápisy n = m, n <= m a n < m sú logické tvrdenia typu Prop.
    Na ich preukázanie potrebujeme dôkaz; nejde o booleovské testy.
  - Bool verziu môžeme kombinovať 
    s andb, orb alebo if (vo výpočtoch)
  - Prop verziu používame v dôkazoch
==================================================
*)

(* Súvis medzi booleovským testom a logickým tvrdením: *)
Check Nat.eqb_eq.  (* forall n m, (n =? m) = true <-> n = m *)
Check Nat.leb_le.  (* forall n m, (n <=? m) = true <-> n <= m *)

(*********************************************)
(**           Dôkazy                        **)

(* Pokyny:
   - Aritmetické úlohy riešte pomocou simpl a tam, kde definícia
     nestačí, indukciou. Pri booleovských úlohách použite podľa potreby
     destruct. Pomocné tvrdenia môžete zaviesť pomocou assert alebo Lemma.
   - Môžete používať výsledky predchádzajúcich úloh a lemy z prednášky.
     Z knižnice môžete použiť plus_n_O, Nat.add_0_r, Nat.add_comm,
     Nat.add_assoc a Bool.negb_involutive ako pomocné lemy.
     Nepoužite však priamo knižničnú vetu, ktorá už vyjadruje celý
     výsledok aktuálnej úlohy: napr. Nat.add_comm v úlohe 3.5.
   - Admitted označuje nedokončený dôkaz a prijme tvrdenie bez dôkazu,
     aby bolo možné pokračovať ďalšími úlohami. Samotná kompilácia
     zadania preto nepotvrdzuje správnosť chýbajúcich dôkazov.
     V hotovom riešení nahraďte Admitted dôkazom ukončeným Qed.
     Pri definícii funkcie v úlohe 3.22 doplňte telo a ukončite ju Defined.
     Defined zachová telo dostupné na vyhodnocovanie, takže príklad
     použitia funkcie možno dokázať výpočtom pomocou reflexivity. *)

(* 
  Úloha 3.1: Dokážte, že n - n = 0
*)
Theorem minus_n_n : forall n,
  minus n n = 0.
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.2: Dokážte: n * 0 = 0 *)
Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.3: Dokážte: n * 1 = n *)
Theorem mult_n_1 : forall n, n * 1 = n.
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.4: Dokážte, že 1 + (n + m) = n + (1 + m) *)
Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.5: Dokážte komutatívnosť sčítania *)
Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.6: Dokážte asociativnosť sčítania *)
Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Definícia: Funkcia double zdvojnásobí argument *)
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(* Úloha 3.7: Dokážte, že double n = n + n *)
Lemma double_plus : forall n, double n = n + n .
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.8
Jedným nepraktickým aspektom definície even 
zo štandardnej knižnice je 
rekurzívne volanie na n - 2. 
To sťažuje dôkazy indukciou, 
pretože môžeme potrebovať 
indukčný predpoklad pre n - 2. 
Nasledujúca lema poskytuje 
alternatívnu charakterizáciu even (S n).
*)
Print even.

Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.9: Zamiešanie sčítania *)
Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.10: Komutativnosť násobenia *)
Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.11: 
Ak má hypotéza tvar H: P → a = b, 
potom taktika rewrite H prepíše a na b 
v cieli a pridá P ako nový podcieľ. 

Použite to v indukčnom kroku tejto úlohy. *)
Check leb.
Print leb.

Theorem plus_leb_compat_l : forall n m p : nat,
  (n <=? m) = true -> ((p + n) <=? (p + m)) = true.
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.12: Reflexivita leb *)
Theorem leb_refl : forall n:nat,
  (n <=? n) = true.
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.13: 0 sa nerovná 1 + n *)
Theorem zero_neqb_S : forall n:nat,
  (0 =? S n) = false.
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.14: b && false = false *)
Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.15: 1+n sa nerovná 0 *)
Theorem S_neqb_0 : forall n:nat,
  (S n =? 0) = false.
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.16: 1 * n = n *)
Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.17: Logická kombinácia orb/andb/negb *)
Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.18: Distribútivita násobenia 
cez sčítanie sprava *)
Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.19: Asociativnosť násobenia *)
Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.20: add_shuffle3' s replace
   Taktika replace a with b nahradí a výrazom b v cieli.
   Vytvorí upravený cieľ a podcieľ dokazujúci b = a.
   Zápis replace a with b by (taktiky) rovnosť dokáže ihneď.
   Pomocou tejto taktiky dokážte nasledujúcu vetu;
   môžete použiť add_assoc a add_comm z predchádzajúcich úloh. *)
Theorem add_shuffle3' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* Doplnte dôkaz *) Admitted.

(*********************************************)
(**         Funkcie vyššieho rádu            **)

(* V týchto úlohách používame filter, map a fold_right zo štandardnej
   knižnice. Ich správanie zodpovedá funkciám z prednášky.
   Pozor na poradie argumentov:
     fold_right f b l zodpovedá zápisu fold f l b z prednášky. *)
Check @filter.
Check @map.
Check @fold_right.

(* Úloha 3.21: Najprv určte výsledky ručne, potom ich overte Compute.
   Pri fold_right rozviňte vnorené volania funkcie. *)
Compute filter even [1;2;3;4;5;6].
Compute map (fun n => n + 1) [1;2;3].
Compute fold_right (fun l acc => l ++ acc) [] [[1];[2;3];[4]].

(* Úloha 3.22: Pomocou fold_right definujte funkciu, ktorá sčíta
   dĺžky všetkých vnútorných zoznamov. Nevytvárajte vlastnú rekurziu.
   Pri doplnení tela môžete použiť exact (fold_right ...). *)
Definition sum_lengths (l : list (list nat)) : nat.
Proof.
  (* Doplňte telo definície a ukončite ho Defined. *) Admitted.

Example sum_lengths_example :
  sum_lengths [[1];[];[2;3;2];[4]] = 5.
Proof.
  (* Doplňte dôkaz výpočtom. *) Admitted.

(* Úloha 3.23: Dokážte indukciou nad l, že map zachováva dĺžku.
   Nepoužívajte hotovú knižničnú vetu map_length. *)
Theorem map_length_exercise : forall (X Y : Type)
  (f : X -> Y) (l : list X),
  length (map f l) = length l.
Proof.
  (* Doplňte dôkaz. *) Admitted.

(* Úloha 3.24: Dokážte indukciou nad l, že filter s testom,
   ktorý vždy vracia true, zachová celý zoznam. *)
Theorem filter_true_exercise : forall (X : Type) (l : list X),
  filter (fun _ => true) l = l.
Proof.
  (* Doplňte dôkaz. *) Admitted.
