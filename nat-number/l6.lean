theorem zero_add (a : Nat): 0 + a = a := by 
  simp

theorem add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by 
  induction c with 
  | zero => simp
  | succ x hx => 
    rw [Nat.add_succ]
    rw [Nat.add_succ]
    rw [Nat.add_succ]
    rw [hx]

theorem succ_add (a b : Nat) : (Nat.succ a) + b = Nat.succ (a + b) := by  
  induction b with 
  | zero => simp 
  | succ x hx => 
  rw [Nat.add_succ]
  rw [Nat.add_succ]
  rw [hx]

theorem add_comm (a b : Nat): a + b = b + a := by 
  induction b with 
  | zero => simp
  | succ x hx => 
  rw [Nat.add_succ]
  rw [succ_add]
  rw [hx]

theorem succ_eq_add_one (n : Nat) : Nat.succ n = n + 1 := by 
  induction n with 
  | zero => simp
  | succ x _ => 
    rw [Nat.add_succ]


theorem add_right_comm (a b c : Nat) : a + b + c = a + c + b := by 
  induction b with 
  | zero => 
    rw [add_assoc]
    simp
  | succ x hx => 
    rw [Nat.add_succ] 
    rw [add_assoc]
    rw [<-Nat.add_succ]
    rw [<-add_comm]
    rw [Nat.add_succ]
    rw [Nat.add_succ]
    rw [Nat.add_succ]
    rw [Nat.add_succ]
    simp
    rw [<-Nat.add_assoc] 
    rw [<-Nat.add_assoc]
    rw [add_comm]
    rw [<-Nat.add_assoc]
    rw [add_comm]
    rw [<-Nat.add_assoc]
    rw [hx]



    

