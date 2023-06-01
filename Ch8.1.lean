inductive Vect (α : Type u) : Nat → Type u where 
  | nil : Vect α 0 
  | cons : α → Vect α n → Vect α (n + 1)
deriving Repr

/- example : Vect String 3 := Vect.nil -/


def Vect.replicate (n : Nat) (x : α) : Vect α n := 
  match n with 
  | 0 => Vect.nil
  | k + 1 => Vect.cons x (Vect.replicate k x)



def Vect.zip :(lh: Vect α n) → (rh: Vect β n) → Vect (α × β) n 
  | .nil, .nil => .nil 
  | .cons x xs, .cons y ys => .cons (x, y) (zip xs ys)


def v1 : Vect Nat 4 := Vect.cons 0 (Vect.cons 1 (Vect.cons 2 (Vect.cons 3 Vect.nil)))

def v2 : Vect String 4 := Vect.cons "zero" (Vect.cons "one" (Vect.cons "two" (Vect.cons "three" Vect.nil)))


#eval Vect.zip v1 v2



  

