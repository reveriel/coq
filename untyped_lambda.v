
(* material : Lecture Notes on the Lambda Calculus by Peter Selinger *)


Fail Definition Ident := fun x => x.
(* Cannot infer the type of x. *)
(* You can't do Ident Ident .So coq can't implements untyped lambda *)

Definition Ident := fun x:Set => x.

Fail Compute Ident Ident.
(* Type error *)


(* But!!! We cant define a new Type *)

(* First, variable *)
(* Inductive var : Type := *)
(*   | Var : nat -> var. *)

(* Inductive term : Type := *)
(* | var : term *)                  (* how to express this: var is term *)
(* | App : term -> term -> term *)
(* | Lambda : var -> term -> term. *)

Inductive var : Type :=
  | X : nat -> var.

Check X 0.

Inductive term : Type :=
  | Var : var -> term
  | Lambda  : var -> term -> term
  | App : term -> term -> term.

Check Var (X 0).
Check Lambda (X 0) (Var (X 0)). (* \x.x *)
Check App (Lambda (X 0) (Var (X 0))) (Var (X 0)). (* \x.x x *)

(** compute free vaiable *)
(* compute list minus list *)

Definition var_eq (x y : var) : bool :=
  match x with
  | X nx => match y with
            |X ny =>  Nat.eqb nx ny
            end
  end.

Require Export List.
Check filter.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* I don't know how to import these notation ... *)

Fixpoint remove_one(l : list var) (x : var) :=
  filter (fun xi => negb (var_eq xi x)) l.

Example remove_one_test : remove_one [X 1; X 2; X 0] (X 0) = [X 1; X 2].
Proof. simpl. reflexivity. Qed.

Fixpoint minus (l1 l2 : list var) : list var :=
  match l2 with
  | [] => l1
  | h :: tail =>  minus (remove_one l1 h) tail
  end.

Example minus_test : minus [X 1; X 2; X 3] [X 1; X 3] = [X 2].
Proof. reflexivity. Qed.

Fixpoint FV (t : term) : list var :=
  match t with
  | Var xi => xi :: nil
  | Lambda x  t' => remove_one (FV t') x
  | App m n => FV m ++ FV n
  end.

Example FV_test1 : FV (Lambda (X 0) (Var (X 0))) = []. (* \x.x *)
Proof. reflexivity. Qed.

(* \x.x x *)
Example FV_test2 : FV (App (Lambda (X 0) (Var (X 0))) (Var (X 0))) = [X 0].
Proof. reflexivity. Qed.

(* rename y as x in m, or m[y/x] *)

Fixpoint renaming (m : term) (y x : var) : term :=
  match m with
  | Var xi => if var_eq xi x then Var y
              else Var xi
  | Lambda xi m' =>  Var x
  | App m1 m2 =>  Var x
  end. (* TODO *)





















