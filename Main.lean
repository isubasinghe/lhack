/- import Lhack -/
/-
#check Nat → Nat

#eval Nat.succ 2

#check Nat

#check Nat × Nat

#check (Nat × Nat) → Nat

#check Type

#check List 

#check Prod

def α : Type := Nat
def β : Type := Bool

#check α

universe γ 

def F (α: Type γ) : Type γ := Prod α α 

#check F

def F'.{u} (α: Type u): Type u := Prod α α 

#check fun (x: Nat) => x + 5 

def f (n: Nat): String := toString n

def greater(x y: Nat) := 
  if x > y then x 
  else y


def doTwice (f: (Nat → Nat → Nat)) (x: Nat) : Nat := 
  f x 3 


def compose (α β γ : Type) (g: β -> γ) (f: α -> β) (x: α) : γ := g (f x)


#check and

universe u v

def ff (α : Type u) (β : α → Type v) (a: α) (b: β a) : (a: α) × β a := Sigma.mk a b

def fff (α : Type u) (β : α → Type v) (a: α) (b: β a) : Σ a: α, β a := Sigma.mk a b

def h1 (x: Nat) := 
  (ff (Type) (fun x => x) (Nat) (x+3)).2

#eval h1 4


#check id

#check @id



variable {p: Prop}
variable {q: Prop}

/- theorem t1: p → q → p := 
  fun hp : p => 
  fun hq : q => 
  show p from hp -/

theorem t1 (hp: p) (hq: q) : p := hp
axiom hp : p 


#print t1

theorem t2 : q -> p := t1 hp

axiom unsound : False

axiom sound : True

theorem ex: 1 = 0 := False.elim unsound

section 
  variable {p q: Prop}
  example (hp: p) (hq: q) : p ∧ q := And.intro hp hq
  #check fun (hp: p) (hq: q) => And.intro hp hq
  example (h: p ∧ q) : p := And.left h
  example (h: p ∧ q) : q := And.right h
end

structure Point where 
  x: Float 
  y: Float 
deriving Repr

def origin : Point := {x := 0.0, y:= 0.0}

def addPoints (p1 p2 : Point) : Point := 
  {x := p1.x + p2.x, y := p1.y + p2.y }
 

def zeroX (p: Point) : Point := 
  { p with x := 0.0 } -/


partial def dump (stream: IO.FS.Stream) : IO Unit := do  
  let buf <- stream.read (20 * 1024)
  if buf.isEmpty then 
    pure ()
  else 
    let stdout <- IO.getStdout 
    stdout.write buf
    dump stream


def fileStream (filename: System.FilePath) : IO (Option IO.FS.Stream) := do 
  let fileExists <- filename.pathExists 
  if not fileExists then 
    let stderr <- IO.getStderr 
    stderr.putStrLn s!"File not found {filename}"
    pure none 
  else 
    let handle <- IO.FS.Handle.mk filename IO.FS.Mode.read 
    pure (some (IO.FS.Stream.ofHandle handle))

def process (exitCode: UInt32) (args: List String) : IO UInt32 := do 
  match args with 
  | [] => pure exitCode 
  | "-" :: args => 
    let stdin <- IO.getStdin 
    dump stdin 
    process exitCode args 
  | filename :: args => 
    let stream <- fileStream ⟨ filename  ⟩ 
    match stream with 
    | none => 
      process 1 args 
    | some stream => 
      dump stream 
      process exitCode args

def main (args: List String) : IO UInt32 := 
  match args with 
  | [] => process 0 ["-"]
  | _ => process 0 args


/- def onePlusOne : 1 + 1  = 2 := rfl -/

theorem onePlusOneIsTwo : 1 + 1 = 2 := by 
  simp

theorem addAndAppend : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := by 
  simp

theorem andImpliesOr : A ∧ B → A ∨ B := 
  fun andEvidence => 
    match andEvidence with 
    | And.intro a b => Or.inl a

def woodlandCritters : List String := 
  ["hedghog", "deer", "snail"]

def third (xs: List α) (ok: xs.length > 2) : α := xs[2]

#eval third woodlandCritters (by simp)

def fifteenMinus8Is7 : 15 - 8 = 7 := by simp

class Plus (α : Type) where 
  plus : α → α → α 


instance : Plus Nat where 
  plus := Nat.add

open Plus(plus)
#eval plus 4 5

inductive LT4 where
  | zero 
  | one 
  | two 
  | three 
  deriving Repr 


instance : OfNat LT4 0 where 
  ofNat := LT4.zero 


instance : OfNat LT4 1 where 
  ofNat := LT4.one 

instance : OfNat LT4 2 where 
  ofNat := LT4.two 

instance : OfNat LT4 3 where 
  ofNat := LT4.three


#eval (3 : LT4)
#check @IO.println

def List.sum [Add α] [OfNat α 0] : List α -> α 
  | [] => 0 
  | x ::xs => x + xs.sum

structure PPoint (α : Type) where 
  x : α 
  y : α 
deriving Repr

instance [Add α] : Add (PPoint α) where 
  add p1 p2 := {x := p1.x + p2.x, y := p1.y + p2.y }



def northernTrees : Array String := 
  #["sloe", "birch", "elm", "oak"]

structure NonEmptyList (α : Type) : Type where 
  head: α 
  tail: List α 


def idahoSpiders : NonEmptyList String := {
  head := "Banded Garden Spider", 
  tail := [
    "Long-legged Sac Spider", 
    "Wolf Spider", 
    "Hobo Spider", 
    "Cat-faced Spider"
  ]
}


#check 2 < 4

/- #eval if (fun (x: Nat) => 1 + x) = (Nat.succ .) then "yes" else "no" -/


inductive BinTree (α: Type) where 
  | leaf : BinTree α 
  | branch : BinTree α → α → BinTree α → BinTree α 

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

deriving instance BEq, Hashable, Repr for NonEmptyList

instance : Append (NonEmptyList α) where 
  append xs ys := {head := xs.head, tail := xs.tail ++ ys.head :: ys.tail}


#eval idahoSpiders ++ idahoSpiders



instance : HAppend (NonEmptyList α) (List α) (NonEmptyList α) where 
  hAppend xs ys := { head := xs.head, tail := xs.tail ++ ys}


#eval idahoSpiders ++ ["Trapdoor Spider"]



instance : Functor NonEmptyList where 
  map f xs := {head := f xs.head, tail := f <$> xs.tail }

def concat [Append α] (xs : NonEmptyList α) : α :=
  let rec catList (start : α) : List α → α
    | [] => start
    | (z :: zs) => catList (start ++ z) zs
  catList xs.head xs.tail



#eval concat idahoSpiders


class Coe' (α : Type) (β: Type) where 
  coe : α → β 


/- instance: Coe Pos Nat where 
  coe x := x.toNat  -/

  instance : Coe (NonEmptyList α) (List α) where
  coe
    | { head := x, tail := xs } => x :: xs


instance : CoeDep (List α) (x :: xs) (NonEmptyList α) where
  coe := { head := x, tail := xs }


structure Monoid where 
  Carrier: Type 
  neutral : Carrier 
  op: Carrier → Carrier → Carrier 


def natMulMoinoid : Monoid := 
  { Carrier := Nat, neutral := 1, op := (.*.)}

def foldMap (M : Monoid) (f : α → M.Carrier) (xs : List α) : M.Carrier :=
  let rec go (soFar : M.Carrier) : List α → M.Carrier
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs


def first (xs : List α) : Option α := 
  xs[0]?

def firstThird (xs : List α) : Option (α × α) := 
  match xs[0]? with 
  | none => none 
  | some first => 
    match xs[2]? with 
    | none => none 
    | some third => 
      some (first, third)
/- Fairly unwieldy already -/ 

def andThen (opt : Option α) (next : α → Option β) : Option β := 
  match opt with 
  | none => none 
  | some x => next x

def firstThird' (xs: List α) : Option (α × α) := 
  andThen xs[0]? fun first => 
  andThen xs[2]? fun third => 
  some (first, third)


inductive Except' (ε : Type) (α : Type) where 
  | error' : ε → Except' ε α 
  | ok' : α → Except' ε α 

def get(xs : List α) (i : Nat) : Except String α := 
  match xs[i]? with 
  | none => Except.error ""
  | some x => Except.ok x


class Monad' (m : Type → Type) where 
  pure' : α → m α 
  bind' : m α → (α → m β) → m β 


structure WithLog (logged : Type) (α : Type) where 
  log : List logged 
  val : α 


def save (data : α) : WithLog α Unit := 
  { log := [data], val := () }





instance : Monad (WithLog logged) where
  pure x := {log := [], val := x}
  bind result next :=
    let {log := thisOut, val := thisRes} := result
    let {log := nextOut, val := nextRes} := next thisRes
    {log := thisOut ++ nextOut, val := nextRes}


