inductive NatOrBool where 
  | nat 
  | bool

abbrev NatOrBool.asType (code: NatOrBool) : Type := 
  match code with 
  | .nat => Nat 
  | .bool => Bool 


def decode (t: NatOrBool) (input: String) : Option t.asType := 
  match t with 
  | .nat => input.toNat? 
  | .bool => 
    match input with 
    | "true" => some true 
    | "false" => some false 
    | _ => none


inductive NestedPairs where 
  | nat : NestedPairs 
  | pair : NestedPairs → NestedPairs → NestedPairs 


def NestedPairs.asType : NestedPairs → Type 
  | .nat => Nat 
  | .pair t1 t2 => asType t1 × asType t2


/- def NestedPairs.beq (t : NestedPairs) (x y : t.asType) : Bool :=
  match t with
  | .nat => x == y
  | .pair t1 t2 => beq t1 x.fst y.fst && beq t2 x.snd y.snd

instance {t : NestedPairs} : BEq t.asType where
  beq x y := x == y -/




