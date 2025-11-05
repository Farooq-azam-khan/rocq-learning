Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Inductive list (A:Type) : Type :=
  | nil : list A
  | cons : A -> list A -> list A.

Structure monoid := { 
   dom : Type ; 
   op : dom -> dom -> dom where "x * y" := (op x y); 
   id : dom where "1" := id; 
   assoc : forall x y z, x * (y * z) = (x * y) * z ; 
   left_neutral : forall x, 1 * x = x ;
   right_neutral : forall x, x * 1 = x 
 }.


Inductive day  : Type  := 
  | mon | tue| wed| thu| fri | sat | sun . 

Definition next_working_day (d: day) : day := 
  match d with 
  | mon => tue 
  |tue => wed  
  | wed => thu 
  | thu => fri 
  | fri => mon 
  | sat => mon | sun => mon 
  end.

Compute (next_working_day fri).
Compute (next_working_day (next_working_day fri)).
Compute (next_working_day (next_working_day fri)) = tue. 
