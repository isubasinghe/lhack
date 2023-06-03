
def NonTail.sum : List Nat → Nat 
  | [] => 0 
  | x :: xs => x + sum xs 


def Tail.sumHelper (soFar : Nat) : List Nat → Nat 
  | [] => soFar 
  | x :: xs => sumHelper (x + soFar) xs

def Tail.sum (xs : List Nat) : Nat := 
  Tail.sumHelper 0 xs


def NonTail.reverse : List α → List α 
  | [] => []
  | x :: xs => reverse xs ++ [x]

def Tail.reverseHelper (soFar : List α) : List α → List α
  | [] => soFar
  | x :: xs => reverseHelper (x :: soFar) xs

def Tail.reverse (xs : List α) : List α :=
  Tail.reverseHelper [] xs


def NonTail.length : List α → Nat 
  | [] => 0 
  | _ :: xs => NonTail.length xs + 1

def Tail.lengthHelper (soFar : Nat) : List α → Nat 
  | [] => 0
  | _ :: xs => lengthHelper (soFar + 1) xs

def NonTail.factorial : Nat → Nat 
  | 0 => 1 
  | n + 1 => factorial n * (n + 1)



partial def Tail.factorialHelper (soFar : Nat) : Nat → Nat 
  | 0 => 1 
  | 1 => soFar 
  | n => factorialHelper (n*soFar) (n-1)

partial def Tail.factorial (x: Nat) : Nat := 
  Tail.factorialHelper 1 x



theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
    induction xs with 
    | nil => 
      intro n 
      rfl
      
    | cons y ys ih => 
      intro n
      simp [NonTail.sum, Tail.sumHelper] 
      rw [<-Nat.add_assoc] 
      rw [Nat.add_comm y n] 
      exact ih (n + y)

theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by 
  funext xs
  simp [Tail.sum]
  rw [<-Nat.zero_add (NonTail.sum xs)]
  exact non_tail_sum_eq_helper_accum xs 0


theorem non_tail_reverse_eq_helper_reverse (xs : List Nat) : 
  (ls : List Nat) -> (NonTail.reverse xs) ++ ls  = (Tail.reverse xs) ++ ls := by 
  induction xs with 
  | nil => 
    intro n 
    rfl
    
  | cons y ys ih => 
    intro n 
    simp [NonTail.reverse, Tail.reverse, Tail.reverseHelper]
    rw [ih]
    simp [Tail.reverse]
    induction ys with 
    | nil => 
      simp [Tail.reverseHelper]
    | cons b bs bh => 
     simp [Tail.reverseHelper]
     





    
    



     
    



/- theorem non_tail_reverse_eq_tail_reverse : @NonTail.reverse = @Tail.reverse := by
  funext α xs
  simp [Tail.reverse] -/

