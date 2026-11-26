module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Definitions.Foundations.LatticeIntegralCoordinates
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DatumCurveIntegralUnitDiscModel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.CanonicalExponents
noncomputable section

namespace GlobalTheory.AllWt.Model

open NumberField IsDedekindDomain MeasureTheory Module

section Gram

variable {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {V : Type} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [StarRing K]


end Gram

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

variable {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem modelWt_eq_sub {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (G : WTZ E) (hG : Even G.2) :
    ∃ a n a' n', Dom a n ∧ Dom a' n' ∧ ∀ k, laU U a' n' k = modelWt U G k + laU U a n k := by
  obtain ⟨B, hB⟩ : ∃ B : ℕ, ∀ (τ : E →+* ℂ) (i : Fin r), (G.1 (τ, i)).natAbs ≤ B :=
    ⟨Finset.univ.sup fun x : (E →+* ℂ) × Fin r => (G.1 (x.1, x.2)).natAbs, fun τ i =>
      Finset.le_sup (f := fun x : (E →+* ℂ) × Fin r => (G.1 (x.1, x.2)).natAbs) (Finset.mem_univ (τ, i))⟩
  have hB' : ∀ τ i, i < r → -(B : ℤ) ≤ G.1 (τ, i) ∧ G.1 (τ, i) ≤ B := fun τ i hi => by
    have := hB τ ⟨i, hi⟩
    simp only at this
    omega
  obtain ⟨s, hs⟩ := hG
  have hpos : ∀ τ i, i < r → 0 ≤ G.1 (τ, i) + ((2 * B * (r - i) : ℕ) : ℤ) := fun τ i hi => by
    have h1 := (hB' τ i hi).1
    have h2 : 2 * B * 1 ≤ 2 * B * (r - i) := Nat.mul_le_mul_left _ (by omega)
    omega
  refine ⟨fun x => 2 * B * (r - x.2), 2 * s.natAbs,
    fun x => if x.2 < r then (G.1 x + ((2 * B * (r - x.2) : ℕ) : ℤ)).toNat else 0, 2 * (s + s.natAbs).toNat,
    ⟨fun τ i j hij => Nat.mul_le_mul_left _ (by omega), even_two_mul _⟩,
    ⟨fun τ i j hij => ?_, even_two_mul _⟩, fun k => ?_⟩
  · simp only
    split_ifs with h1 h2 h2
    · rcases hij.eq_or_lt with rfl | hlt
      · exact le_rfl
      · have e1 := hB' τ i h2
        have e2 := hB' τ j h1
        have e3 : 2 * B * (r - j) + 2 * B * 1 ≤ 2 * B * (r - i) := by
          rw [← mul_add]; exact Nat.mul_le_mul_left _ (by omega)
        omega
    · omega
    · exact Nat.zero_le _
    · exact le_rfl
  · funext τ j
    have hj := j.2
    have hp := (U.X k).p0_le
    simp only [laU, modelWt, Pi.add_apply]
    split_ifs with h1 h2 h2
    · rw [Int.toNat_of_nonneg (hpos _ _ h2)]; omega
    · omega
    · rw [Int.toNat_of_nonneg (hpos _ _ h2)]; omega
    · omega

theorem chi_modelWt {σ : c.F →+* ℂ} (U : Unf Xo c σ r)
    (h : ∀ a n, Dom a n → ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (laU U a n k) γ = 1)
    (G : WTZ E) (hG : Even G.2) (k : U.Comp) : ∀ γ ∈ (U.X k).Γ, (U.X k).χ (modelWt U G k) γ = 1 := by
  intro γ hγ
  obtain ⟨a, n, a', n', h1, h2, h3⟩ := modelWt_eq_sub U G hG
  have := h a' n' h2 k γ hγ
  rwa [h3, (U.X k).χ_add _ _ γ hγ, h a n h1 k γ hγ, mul_one] at this

end GlobalTheory.AllWt.Model
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyLiftObj
noncomputable section
namespace GlobalTheory.Glob.IntegralWittCoefficients.Model
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric

def stdLat (E : Type) [Field E] [NumberField E] (N : ℕ) : Submodule (𝓞 E) (Fin N → E) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)

theorem mem_range_iff {E : Type} [Field E] [NumberField E] (x : E) :
    x ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ x :=
  ⟨by rintro ⟨a, rfl⟩; exact a.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

theorem mem_stdLat {E : Type} [Field E] [NumberField E] {N : ℕ} (x : Fin N → E) :
    x ∈ stdLat E N ↔ ∀ k, IsIntegral ℤ (x k) := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_one]
  exact forall_congr' fun k => mem_range_iff (x k)

theorem isSDLat_std (E : Type) [Field E] [NumberField E] [StarRing E] (N : ℕ) : IsSDLat E N (stdLat E N) := by
  have hs : ∀ k : Fin N, (Pi.single k 1 : Fin N → E) ∈ stdLat E N := fun k => by
    rw [mem_stdLat]
    intro j
    rw [Pi.single_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  refine ⟨Submodule.fg_pi fun _ => ?_, ?_, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩
  · rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  · rw [eq_top_iff, ← (Pi.basisFun E (Fin N)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨k, rfl⟩
    simpa using hs k
  · rw [mem_range_iff]
    rw [mem_stdLat] at hx hy
    exact IsIntegral.sum _ fun i _ => ((hx i).map (starRingEnd E).toIntAlgHom).mul (hy i)
  · rw [mem_stdLat]
    intro k
    have := h _ (hs k)
    rw [mem_range_iff] at this
    simpa [stdH, Pi.single_apply, apply_ite] using this

end GlobalTheory.Glob.IntegralWittCoefficients.Model
end
end
