module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.PeriodIntegrals.UnimodGenus

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.AdUnimod
open MeasureTheory

noncomputable section

namespace PI

def AdUnimod : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (μf : Measure I.Gf), μf.IsHaarMeasure → μf.IsMulRightInvariant

end PI

end
end

noncomputable section

namespace PI.WAU

open Formalism.MainNotions.S MeasureTheory

def Ksub (I : AutInst) : Subgroup I.Gf :=
  (Formalism.UG.stabGL I.Lf).comap (Formalism.UG.UPts I.cm.sig I.J (Af I.F)).subtype

def KgSubgroup : Prop :=
  ∀ (I : AutInst) (g : ℕ), 1 ≤ g → ∃ H : Subgroup I.Gf, (H : Set I.Gf) = I.Kg g

def KCompact : Prop := ∀ I : AutInst, IsCompact I.Kset

def KCountable : Prop :=
  ∀ I : AutInst, ∃ s : Set I.Gf, s.Countable ∧ ∀ x : I.Gf, ∃ y ∈ s, y⁻¹ * x ∈ I.Kset

def IndexEq : Prop :=
  ∀ (I : AutInst) (x : I.Gf),
    ((Ksub I).map (MulAut.conj x).toMonoidHom).relIndex (Ksub I) =
      ((Ksub I).map (MulAut.conj x⁻¹).toMonoidHom).relIndex (Ksub I)

end PI.WAU
