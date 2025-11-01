import AP.Util

universe u
variable {World Ent : Type u}

def KnowledgeFn (World Ent : Type u) (n : ℕ) : Type u :=
  match n with
  | 0 => PUnit
  | n + 1 => Ent → World → KnowledgeFn World Ent n → Prop

structure Knowledge (World Ent : Type u) : Type u where
  depth : ℕ
  fn : KnowledgeFn World Ent depth

structure WorldWithKnowledge (World Ent : Type u) : Type u where
  world : World
  knowledge : Knowledge World Ent

#check 0 #exit

def Knowledge.WF (k : Knowledge World Ent) (w : World) : Prop :=
  match k with
  | ⟨0, _⟩ => true
  | ⟨n + 1, f⟩ => ∀ e w' k', f e w' k' → sorry

def WorldWithKnowledge.WF (wk : WorldWithKnowledge World Ent) : Prop :=
  wk.knowledge.WF wk.world

def Knowing (W E K : Type*) :=
  E → W → K → Prop

structure WorldStruct (W E K : Type*) where
  world : W
  knowOld : K
  knowNew : Knowing W E K
  h : ∀ e, knowNew e world knowOld

def WorldRec.{u} (W E : Type u) (n : ℕ) : Type u × Type u :=
  match n with
  | 0 => (W, PUnit)
  | n + 1 =>
    let (w, k) := WorldRec W E n
    let k' := Knowing w E k
    (WorldStruct w E k, k')

structure World.{u} (W E : Type u) where
  depth : ℕ
  world : WorldRec W E (depth + 1) |>.1

-----

structure W where
  x : ℕ

abbrev E := Fin 2

def w : W where
  x := 5

def world : World W E where
  depth := 1
  world :=
    { world :=
      { world := w
      , knowOld := ()
      , knowNew _e _w _k := True
      , h := by simp
      }
    , knowOld _e _w _k := True
    , knowNew _e _w _k := True
    , h := by simp
    }