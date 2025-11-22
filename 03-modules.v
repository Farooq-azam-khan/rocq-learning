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

End NatM.



