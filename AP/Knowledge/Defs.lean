import AP.Util

namespace Knowledge

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