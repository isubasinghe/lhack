import Lean 

structure Adder where 
  howMuch : Nat
deriving Repr

def add5 : Adder := ⟨5⟩ 

#eval add5

instance : CoeFun Adder (fun _ => Nat → Nat) where 
  coe a := (. + a.howMuch)

#eval add5 3

inductive JSON where 
  | true : JSON 
  | false : JSON 
  | null : JSON 
  | string : String → JSON 
  | number : Float → JSON 
  | object : List (String × JSON) → JSON 
  | array : List JSON → JSON 
deriving Repr


structure Serializer where 
  Contents : Type 
  serialize : Contents → JSON 


def Str : Serializer := 
  { Contents := String, 
    serialize := JSON.string 
  }

instance : CoeFun Serializer (fun s => s.Contents → JSON) where 
  coe s := s.serialize

def buildResponse (title : String) (R : Serializer) (record : R.Contents) : JSON :=
  JSON.object [
    ("title", JSON.string title),
    ("status", JSON.number 200),
    ("record", R record)
  ]


#eval buildResponse "Functional Programming in Lean" Str "Programming is fun!"

def dropDecimals (numString : String) : String :=
  if numString.contains '.' then
    let noTrailingZeros := numString.dropRightWhile (· == '0')
    noTrailingZeros.dropRightWhile (· == '.')
  else numString

def String.separate (sep : String) (strings : List String) : String :=
  match strings with
  | [] => ""
  | x :: xs => String.join (x :: xs.map (sep ++ ·))



partial def JSON.asString (val : JSON) : String :=
  match val with
  | true => "true"
  | false => "false"
  | null => "null"
  | string s => "\"" ++ Lean.Json.escape s ++ "\""
  | number n => dropDecimals n.toString
  | object members =>
    let memberToString mem :=
      "\"" ++ Lean.Json.escape mem.fst ++ "\": " ++ asString mem.snd
    "{" ++ ", ".separate (members.map memberToString) ++ "}"
  | array elements =>
    "[" ++ ", ".separate (elements.map asString) ++ "]"


