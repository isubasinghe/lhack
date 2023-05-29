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
  tail := []
}



