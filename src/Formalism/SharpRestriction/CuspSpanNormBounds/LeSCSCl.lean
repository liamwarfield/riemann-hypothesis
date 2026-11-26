module

public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalFunctionIntegrableOfLocal
public import Formalism.LatticeRigidity.HeightMinimum.PackingCountGeometricMean
public import Formalism.LatticeRigidity.HeightMinimum.SqrtAbsNormLeProd

@[expose] public section

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.LeSCSCl
noncomputable section

namespace Formalism.MainNotions.S

open Formalism.MainNotions

variable {eps : ℝ}

def sC' (Fm : FamP eps) : ℝ := Fm.CkLow

def sCl (Fm : FamP eps) : ℝ :=
  min Fm.CfL (min Fm.Cw (min Fm.CDel (min Fm.CCount (min Fm.Ch0r Fm.Cgap))))

def scT : ℝ := 1 / 2

def OwnEv (Fm : FamP eps) (P : ℝ → ℝ → ∀ x, Fm.Ix x → Prop) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, P (sC' Fm) (sCl Fm) x i

theorem OwnEv.mono {Fm : FamP eps} {P Q : ℝ → ℝ → ∀ x, Fm.Ix x → Prop}
    (h : ∀ C' Cl x i, P C' Cl x i → Q C' Cl x i) (hP : OwnEv Fm P) : OwnEv Fm Q := by
  obtain ⟨x0, hx⟩ := hP
  exact ⟨x0, fun x hx' i => h _ _ _ _ (hx x hx' i)⟩

theorem OwnEv.and {Fm : FamP eps} {P Q : ℝ → ℝ → ∀ x, Fm.Ix x → Prop}
    (hP : OwnEv Fm P) (hQ : OwnEv Fm Q) : OwnEv Fm (fun C' Cl x i => P C' Cl x i ∧ Q C' Cl x i) := by
  obtain ⟨a, ha⟩ := hP
  obtain ⟨b, hb⟩ := hQ
  exact ⟨max a b, fun x hx i => ⟨ha x (le_of_max_le_left hx) i, hb x (le_of_max_le_right hx) i⟩⟩

theorem le_sC'_sCl {Fm : FamP eps} {K : TransportedAlt} {CH : ℝ} (h : Fm.Large K CH) :
    K.last (Fm.cOut ++ Fm.cMid CH) ≤ sC' Fm ∧ K.last (Fm.cOut ++ Fm.cMid CH) ≤ sCl Fm := by
  have H := h.2.2.2
  refine ⟨H _ (by simp [sC', FamP.cLast]), ?_⟩
  simp only [sCl, le_min_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact H _ (by simp [FamP.cLast])

end Formalism.MainNotions.S
end
end

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.BesselBoundFamilyOfDoubleCoset
open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₄

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

def DDsp {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mx k r → (H →L[ℂ] H)) (w0 : H) : Submodule ℂ H :=
  Submodule.span ℂ ((fun g => σ g w0) '' UH (Hpk k r))

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

end Family

end Formalism.MainNotions.BridgeLemma₄
end
end

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.BridgeUnipRad
noncomputable section

namespace Formalism.MainNotions.BridgeUnipRad

open MeasureTheory NumberField Matrix
open Formalism.MainNotions.S

section CM

variable (I : AutInst)

theorem emb_star (v : InfinitePlace I.F) (x : I.E) : I.φ v (star x) = starRingEnd ℂ (I.φ v x) := by
  obtain ⟨hcm, -, -, -⟩ := I.cm
  unfold Formalism.HermitianLatticesTheory.IsCMUnram at hcm
  exact hcm.2.1 (I.φ v) x

end CM

section Form

variable {n : ℕ}

theorem hform_eq (J : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    Formalism.UG.hform (starRingEnd ℂ) J x y = star x ⬝ᵥ (J *ᵥ y) := by
  rw [Formalism.UG.hform.eq_1]
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

end Form

section Span

variable (I : AutInst)

end Span

section Rad

variable {n : ℕ}

variable {J' : Matrix (Fin n) (Fin n) ℂ} {U : Submodule ℂ (Fin n → ℂ)}

end Rad

section Sub

variable {n : ℕ} (ε : Fin n → Bool) {P J' : Matrix (Fin n) (Fin n) ℂ}

end Sub

end Formalism.MainNotions.BridgeUnipRad

end
end
