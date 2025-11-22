Module TupleM.
Inductive bit: Type := | b0 | b1.
Inductive nybble: Type := | bits (b0  b1 b2 b3: bit).
Check (bits b0 b1 b0 b1) : nybble.

Definition all_zeros (nb: nybble) : bool :=
  match nb with
  | (bits b0 b0 b0 b0) => true
  | _ => false
end.
Compute (all_zeros (bits b0 b0 b0 b0)).

End TupleM.

Module NatM.
Inductive nat : Type := zero | succ (n: nat).

Definition pred (n: nat) : nat :=
  match n with
  | zero => zero
  | succ np => np
  end.

Definition minus_two (n: nat) : nat :=
  match n with
  | zero => zero
  | succ zero => zero
  | succ (succ np) => np
  end.

Compute (minus_two (succ (succ (succ zero)))).

(* Recursion on definitions *)
Fixpoint even (n: nat) : bool :=
  match n with
  | zero => true
  | succ zero => false
  | succ (succ np) => false
  end.
Definition odd (n: nat) : bool := negb (even n).

Example odd1:  (even (succ zero)) = false.
Proof. simpl. reflexivity. Qed.

Fixpoint plus (n1: nat) (n2: nat) : nat  :=
  match (n1: nat) with
  | zero => n2
  | succ (np) => succ (plus np n2)
  end.

Example three_plus_two : plus (succ (succ (succ zero))) (succ (succ zero)) = succ (succ (succ (succ (succ zero)))).
Proof. simpl. reflexivity. Qed.

Fixpoint mult (n1 n2  : nat )  : nat :=
  match n1 with
  | zero => zero
  | succ np => plus (mult np n2) n2
  end.

Definition one:= succ zero.
Definition two:= succ one.
Definition three := succ two.
Definition four:= succ three.
Definition five:= succ four.
Definition six:= succ five.
Definition nine := succ (succ (succ (succ (succ (succ (succ (succ (succ zero )))))))).

Example three_times_three: mult three three = nine.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n1 n2: nat) : nat :=
  match n1, n2 with
  | zero, _ => zero
  | succ _, zero => n1
  | succ n1p, succ n2p => minus n1p n2p
  end.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | zero => succ zero
  | succ np =>  mult base (exp base np)
  end.
Example two_power_two : exp two two = four.
Proof. simpl. reflexivity. Qed.

Fixpoint factorial (n: nat) : nat :=
  match n with
  | zero => one
  | succ np => mult n (factorial np)
  end.

Example one_fact: factorial one = one.
Proof. simpl. reflexivity. Qed.

Example two_fact: factorial two= two.
Proof. simpl. reflexivity. Qed.

Example three_fact: factorial three = six.
Proof. simpl. reflexivity. Qed.

Theorem plus_zero_n : forall (n : nat) , plus zero n = n.
Proof.
  intros n.  simpl. reflexivity. Qed.

Theorem plus_one_n : forall (n: nat) , plus one n = succ n.
Proof. intros n. reflexivity. Qed.

Theorem mult_one_n : forall (n: nat) , mult one n = n.
Proof. intros n. reflexivity. 
Qed. 


End NatM.



