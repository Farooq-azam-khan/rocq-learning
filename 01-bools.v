Inductive bool : Type := | true | false .

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

 Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.


Example test_orb1: (orb true false) = true.
Proof.
  simpl. reflexivity.
Qed.

Example test_orb2: (orb false false) = false.
Proof.
  simpl. reflexivity.
Qed.

Example test_orb3: (orb false true) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_orb4: (orb true true) = true.
Proof. 
  simpl. 
  reflexivity. 
Qed.

(* E1. *)
Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => negb b2
  | false => true
 end. 

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

(* E2. *)
Definition and3 (b1: bool) (b2: bool) (b3: bool) : bool := 
  match b1 with
  | true => match b2 with
            | true => b3
            | _ => b2
            end
  | _ => b1 end.


Example test_and3_1: (and3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_and3_2: (and3 true true false) = false.
Proof. simpl. reflexivity. Qed.
Example test_and3_3: (and3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_and3_4: (and3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_and3_5: (and3 false false true) = false.
Proof. simpl. reflexivity. Qed.


