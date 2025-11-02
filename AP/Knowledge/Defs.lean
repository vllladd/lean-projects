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

def KnowledgeFnWf (w : World) (n : ℕ) (f : KnowledgeFn World Ent n) : Prop :=
  match n, f with
  | 0, _ => True
  | n + 1, p => ∀ e, ∃ (f' : KnowledgeFn World Ent n), KnowledgeFnWf w n f' ∧ p e w f'

def Knowledge.WF (k : Knowledge World Ent) (w : World) : Prop :=
  KnowledgeFnWf w k.depth k.fn

def Knowledge.SatisfiesAnyW (k : Knowledge World Ent) (e : Ent) (w : World) : Prop :=
  match k.depth, k.fn with
  | 0, _ => True
  | _ + 1, p => ∃ f', p e w f'

def Knowledge.SatisfiesAllW (k : Knowledge World Ent) (e : Ent) (w : World) : Prop :=
  match k.depth, k.fn with
  | 0, _ => True
  | _ + 1, p => ∀ f', p e w f'

def WorldWithKnowledge.WF (wk : WorldWithKnowledge World Ent) : Prop :=
  wk.knowledge.WF wk.world

def Knowledge.KnowsW (k : Knowledge World Ent) (e : Ent) (p : World → Prop) (w : World) : Prop :=
  p w ∧ ∀ w', k.SatisfiesAnyW e w' → p w'

def WorldWithKnowledge.KnowsW (wk : WorldWithKnowledge World Ent) (e : Ent)
(p : World → Prop) : Prop :=
  wk.knowledge.KnowsW e p wk.world

#check 0 #exit

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