structure MythicalCreature where 
  large: Bool 
deriving Repr 

#check MythicalCreature.mk

#check MythicalCreature.large

structure Monster extends MythicalCreature where 
  vulnerability : String 
deriving Repr 


def troll : Monster where
  vulnerability := "sunlight"
  large := true

#check Monster.mk


structure Helper extends MythicalCreature where 
  assistance: String 
  payment : String 
deriving Repr 

def nisse : Helper where 
  large := false 
  assistance := "household tasks"
  payment := "porridge"

structure MonstrousAssistant extends Monster, Helper where 
deriving Repr 


def domesticatedTroll : MonstrousAssistant where 
  large := false 
  assistance := "heavy labour"
  payment := "toy goats"
  vulnerability := "sunlight"

inductive Size where 
  | small 
  | medium 
  | large 
deriving BEq

structure SizedCreature extends MythicalCreature where 
  size : Size 
  large := size == Size.large

def nonsenseCreature : SizedCreature where 
  large := false 
  size := .large


abbrev SizesMatch (sc : SizedCreature) : Prop := 
  sc.large == (sc.size == Size.large)

def huldre : SizedCreature where 
  size := .medium
  large := false 

example : SizesMatch huldre := by simp

