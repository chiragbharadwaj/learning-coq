(******************************************************************************
 * 1. DATA AND FUNCTIONS                                                      *
 ******************************************************************************)

(* Defines a boolean type inductively. *)
Inductive bool' : Type :=
  | T
  | F.

(* [negb b] returns the logical negation of [b].
 *   - b: a boolean value
 *)
Definition negb (b: bool') : bool' :=
  match b with
  | F => T
  | T => F
  end.

(* [andb b1 b2] returns the logical conjunction of [b1] and [b2].
 *   - b1: a boolean value
 *   - b2: a boolean value
 *)
Definition andb (b1: bool') (b2:bool') : bool' :=
  match b1 with
  | F => F
  | T => b2
  end.

(* [orb b1 b2] returns the logical disjunction of [b1] and [b2].
 *   - b1: a boolean value
 *   - b2: a boolean value
 *)
Definition orb (b1: bool') (b2: bool') : bool' :=
  match b1 with
  | F => b2
  | T => T
  end.

(* Defining shorthand notation for the logical functions over booleans. *)
Notation "b1 && b2" := (andb b1 b2).
Notation "b1 || b2" := (orb b1 b2).

(* + *)
(* [nandb b1 b2] returns the logical un-conjunction of [b1] and [b2].
 *   - b1: a boolean value
 *   - b2: a boolean value
 *)
Definition nandb (b1: bool') (b2: bool') : bool' :=
  negb (b1 && b2).

(* Test: ~[False /\ False] = False. *)
Example testNandb1: (nandb F F) = T.
Proof. simpl. reflexivity. Qed.

(* Test: ~[False /\ True] = False. *)
Example testNandb2: (nandb F T) = T.
Proof. simpl. reflexivity. Qed.

(* Test: ~[True /\ False] = False. *)
Example testNandb3: (nandb T F) = T.
Proof. simpl. reflexivity. Qed.

(* Test: ~[True /\ True] = False. *)
Example testNandb4: (nandb T T) = F.
Proof. simpl. reflexivity. Qed.

(* + *)
(* [andb3 b1 b2 b3] returns the logical conjunction of [b1], [b2], and [b3].
 *   - b1: a boolean value
 *   - b2: a boolean value
 *   - b3: a boolean value
 *)
Definition andb3 (b1: bool') (b2: bool') (b3: bool') : bool' :=
  b1 && b2 && b3.

(* Test: False /\ False /\ False = False. *)
Example testAndb31: (andb3 F F F) = F.
Proof. simpl. reflexivity. Qed.

(* Test: False /\ False /\ True = False. *)
Example testAndb32: (andb3 F F T) = F.
Proof. simpl. reflexivity. Qed.

(* Test: False /\ True /\ False = False. *)
Example testAndb33: (andb3 F T F) = F.
Proof. simpl. reflexivity. Qed.

(* Test: False /\ True /\ True = False. *)
Example testAndb34: (andb3 F T T) = F.
Proof. simpl. reflexivity. Qed.

(* Test: True /\ False /\ False = False. *)
Example testAndb35: (andb3 T F F) = F.
Proof. simpl. reflexivity. Qed.

(* Test: True /\ False /\ True = False. *)
Example testAndb36: (andb3 T F T) = F.
Proof. simpl. reflexivity. Qed.

(* Test: True /\ True /\ False = False. *)
Example testAndb37: (andb3 T T F) = F.
Proof. simpl. reflexivity. Qed.

(* Test: True /\ True /\ True = True. *)
Example testAndb38: (andb3 T T T) = T.
Proof. simpl. reflexivity. Qed.

(* Defines a natural number type inductively. *)
Inductive nat' : Type :=
  | Zero
  | Succ : nat' -> nat'.

(* [pred n] returns the predecessor of [n].
 *   - n: a natural number
 *)
Definition pred (n: nat') : nat' :=
  match n with
  | Zero    => Zero
  | Succ n' => n'
  end.

(* [plusn n1 n2] returns the natural number [n1] + [n2].
 *   - n1: a natural number
 *   - n2: a natural number
 *)
Fixpoint plusn (n1: nat') (n2: nat') : nat' :=
  match n1 with
  | Zero     => n2
  | Succ n1' => Succ (plusn n1' n2)
  end.

(* [minusn n1 n2] returns the natural number [n1] - [n2] or Zero if [n1] < [n2].
 *   - n1: a natural number
 *   - n2: a natural number
 *)
Fixpoint minusn (n1: nat') (n2: nat') : nat' :=
  match (n1,n2) with
  | (Zero, _) => Zero
  | (_, Zero) => n1
  | (Succ n1', Succ n2') => minusn n1' n2'
  end.

(* [multn n1 n2] returns the natural number [n1] * [n2].
 *   - n1: a natural number
 *   - n2: a natural number
 *)
Fixpoint multn (n1: nat') (n2: nat') : nat' :=
  match n1 with
  | Zero     => Zero
  | Succ n1' => plusn n2 (multn n1' n2)
  end.

(* + *)
(* [factorialn n] returns the natural number [n]!.
 *   - n: a natural number
 *)
Fixpoint factorialn (n: nat') : nat' :=
  match n with
  | Zero    => Succ Zero
  | Succ n' => multn n (factorialn n')
  end.

(* Test: factorialn 3 = 6. *)
Example testFactorialn1: (factorialn (Succ (Succ (Succ Zero)))) = Succ (Succ (Succ (Succ (Succ (Succ Zero))))).
Proof. simpl. reflexivity. Qed.

(* Test: factorialn 5 = 10 * 12. *)
Example testFactorialn2: (factorialn (Succ (Succ (Succ (Succ (Succ Zero)))))) =
  multn (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero))))))))))
        (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Succ Zero)))))))))))).
Proof. simpl. reflexivity. Qed.

(* [eqn n1 n2] returns the boolean [n1] == [n2].
 *   - n1: a natural number
 *   - n2: a natural number
 *)
Fixpoint eqn (n1: nat') (n2: nat') : bool' :=
  match n1 with
  | Zero =>
      match n2 with
      | Zero => T
      | _ => F
      end
  | Succ n1' =>
      match n2 with
      | Zero => F
      | Succ n2' => eqn n1' n2'
      end
  end.

(* [leqn n1 n2] returns the boolean [n1] <= [n2].
 *   - n1: a natural number
 *   - n2: a natural number
 *)
Fixpoint leqn (n1: nat') (n2: nat') : bool' :=
  match n1 with
  | Zero => T
  | Succ n1' =>
      match n2 with
      | Zero => F
      | Succ n2' => leqn n1' n2'
      end
  end.

(* Defining shorthand notation for boolean comparisons over natural numbers. *)
Notation "n1 = n2"  := (eqn n1 n2).
Notation "n1 <= n2" := (leqn n1 n2).

(* + *)
(* [ltn n1 n2] returns the boolean [n1] < [n2].
 *   - n1: a natural number
 *   - n2: a natural number
 *)
Definition ltn (n1: nat') (n2: nat') : bool' :=
  (n1 <= n2) && (negb (n1 = n2)).

(* Test: [2 < 2] = False. *)
Example testLtn1: (ltn (Succ (Succ Zero)) (Succ (Succ Zero))) = F.
Proof. simpl. reflexivity. Qed.

(* Test: [2 < 4] = True. *)
Example testLtn2: (ltn (Succ (Succ Zero)) (Succ (Succ (Succ (Succ Zero))))) = T.
Proof. simpl. reflexivity. Qed.

(* Test: [4 < 2] = False. *)
Example testLtn3: (ltn (Succ (Succ (Succ (Succ Zero)))) (Succ (Succ Zero))) = F.
Proof. simpl. reflexivity. Qed.

(******************************************************************************
 * 2. PROOF BY SIMPLIFICATION                                                 *
 ******************************************************************************)

(* Empty. *)

(******************************************************************************
 * 3. PROOF BY REWRITING                                                      *
 ******************************************************************************)

(* + *)
(* Theorem: If n1 = n2 and n2 = n3, then n1 + n2 = n2 + n3. *)
Theorem plusId: forall n1 n2 n3 : nat,
  n1 = n2 ->
  n2 = n3 ->
  n1 + n2 = n2 + n3.
Proof.
  intros n1 n2 n3.
  intros H1 H2.
  rewrite -> H1.
  rewrite <- H2.
  reflexivity. Qed.

(* Theorem: Succ and +1 are the same thing. *)
Theorem plus1L: forall n : nat,
  1 + n = S n.
Proof.
  intros n.
  simpl.
  reflexivity. Qed.

(* ++ *)
(* Theorem: If n2 = 1 + n1, then n2 * (1 + n1) = n2 ^ 2. *)
Theorem multSuccL: forall n1 n2 : nat,
  n2 = S n1 ->
  n2 * (1 + n1) = n2 * n2.
Proof.
  intros n1 n2.
  intros H.
  rewrite -> plus1L.
  rewrite <- H.
  reflexivity. Qed.

(******************************************************************************
 * 4. PROOF BY CASE ANALYSIS                                                  *
 ******************************************************************************)

(* TBD. *)