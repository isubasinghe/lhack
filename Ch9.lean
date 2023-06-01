def Nat.plusR :  Nat → Nat → Nat 
  | n, 0 => n 
  | n, k + 1 => plusR n k + 1

/- theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by 
  induction k with 
  | zero => rfl 
  | succ n ih =>
    unfold Nat.plusR
    rw [<-ih] -/


theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by 
  induction k with 
  | zero => rfl 
  | succ n ih => 
    simp [Nat.plusR]
    assumption

inductive BinTree (α: Type) where 
  | leaf : BinTree α 
  | branch : BinTree α → α → BinTree α → BinTree α 


def BinTree.mirror : BinTree α → BinTree α 
  | BinTree.leaf => .leaf 
  | BinTree.branch lhs a rhs => .branch rhs a lhs

def BinTree.count : BinTree α → Nat 
  | .leaf => 0 
  | .branch l _ r => 
    1 + l.count + r.count

def eqBinTree [BEq α] : BinTree α → BinTree α → Bool 
  | BinTree.leaf, BinTree.leaf => true 
  | BinTree.branch l x r, BinTree.branch l2 x2 r2 => 
    x == x2 && eqBinTree l l2 && eqBinTree r r2 
  | _, _ => false

instance [BEq α] : BEq (BinTree α) where 
  beq := eqBinTree

def hashBinTree [Hashable α] : BinTree α -> UInt64 
  | BinTree.leaf => 0 
  | BinTree.branch left x right => 
    mixHash 1 (mixHash (hashBinTree left) (mixHash (hash x) (hashBinTree right)))

instance [Hashable α] : Hashable (BinTree α) where 
  hash := hashBinTree



/- theorem BinTree.mirror_count (t : BinTree α) : t.mirror.count = t.count := by 
  induction t with 
  | leaf => rfl 
  | branch l x r ihl ihr => 
    simp [BinTree.mirror, BinTree.count]
    rw [ihl, ihr]  -/

theorem BinTree.mirror_count (t : BinTree α) : t.mirror.count = t.count := by
  induction t with
  | leaf => simp [BinTree.mirror]
  | branch l _ r ihl ihr =>
    simp_arith [BinTree.mirror, BinTree.count, ihl, ihr]


