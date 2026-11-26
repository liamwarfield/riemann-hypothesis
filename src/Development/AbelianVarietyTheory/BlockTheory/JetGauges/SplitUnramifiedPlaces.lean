module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.BlockTheory.JetGauges.SplitUnramifiedPlaces
noncomputable section

open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces

section Ring

variable (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE]

abbrev Op : Type := ℤ_[p] ⊗[ℤ] OE

def bar [StarRing OE] : Op p OE ≃ₐ[ℤ_[p]] Op p OE :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : ℤ_[p] ≃ₐ[ℤ_[p]] ℤ_[p])
    (AlgEquiv.ofRingEquiv (f := (starRingAut : RingAut OE)) (fun n => by simp))

variable {p OE}

def extend {O : Type} [CommRing O] [Algebra ℤ_[p] O] (σ : OE →+* O) : Op p OE →ₐ[ℤ_[p]] O :=
  Algebra.TensorProduct.lift (Algebra.ofId ℤ_[p] O) σ.toIntAlgHom (fun _ _ => Commute.all _ _)

end Ring

@[ext] structure Place (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE] where

  e : Op p OE
  idem : IsIdempotentElem e
  ne_zero : e ≠ 0
  primitive : ∀ f : Op p OE, IsIdempotentElem f → f * e = f → f = 0 ∨ f = e

namespace Place

variable {p : ℕ} [Fact p.Prime] {OE : Type} [CommRing OE]

abbrev Ow (w : Place p OE) : Type := Op p OE ⧸ Ideal.span {1 - w.e}

def toOw (w : Place p OE) : OE →+* w.Ow :=
  (Ideal.Quotient.mk _).comp
    (Algebra.TensorProduct.includeRight : OE →ₐ[ℤ] Op p OE).toRingHom

end Place

section Gauss

variable {p : ℕ} [Fact p.Prime]

end Gauss

end GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.JetGauges.BalancedHermitianSpace
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace

open NumberField NumberField.IsCMField TensorProduct

abbrev Bil (Y : Type) [AddCommGroup Y] : Type := Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ

section Forms

variable {Y : Type} [AddCommGroup Y]

def quad (β : Bil Y) (x : Y) : ℝ := β x x / 2

def IsIntegralFn (S : Submodule ℝ (Bil Y)) (l : S →ₗ[ℝ] ℝ) : Prop :=
  ∀ β : S, (∀ a c, ∃ z : ℤ, (β : Bil Y) a c = z) → ∃ z : ℤ, l β = z

def IsPositiveFn (S : Submodule ℝ (Bil Y)) (l : S →ₗ[ℝ] ℝ) : Prop :=
  ∀ β : S, (∀ a, 0 ≤ (β : Bil Y) a a) → β ≠ 0 → 0 < l β

def leastExponent (S : Submodule ℝ (Bil Y)) (b : S) : ℝ :=
  sInf {x | ∃ l : S →ₗ[ℝ] ℝ, IsIntegralFn S l ∧ IsPositiveFn S l ∧ x = l b}

def evalSum (S : Submodule ℝ (Bil Y)) {k : ℕ} (x x' : Fin k → Y) : S →ₗ[ℝ] ℝ where
  toFun β := ∑ i, (β : Bil Y) (x i) (x' i)
  map_add' β γ := by simp [Finset.sum_add_distrib]
  map_smul' r β := by simp [Finset.mul_sum]

end Forms

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

def HasTraceOne : Prop := ∃ w : 𝓞 E, w + ringOfIntegersComplexConj E w = 1

variable {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]

def IsBalanced (β : Bil Y) : Prop :=
  (∀ x y, β x y = β y x) ∧
    ∀ (a : 𝓞 E) (x y : Y), β (a • x) y = β x (ringOfIntegersComplexConj E a • y)

def IsBalancedSpace (S : Submodule ℝ (Bil Y)) : Prop := ∀ β, β ∈ S ↔ IsBalanced E β



omit [NumberField E] [IsCMField E] [Module (𝓞 E) Y] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.isIntegralFn_evalSum (S : Submodule ℝ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.Bil Y))
    {k : ℕ} (x x' : Fin k → Y) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.IsIntegralFn S (_root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.evalSum S x x') := by
  intro β hβ
  choose f hf using hβ
  refine ⟨∑ i, f (x i) (x' i), ?_⟩
  show ∑ i, (β : _root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.Bil Y) (x i) (x' i) = _
  push_cast
  exact Finset.sum_congr rfl fun i _ => hf _ _

end GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.JetGauges.NodalSeriesPeriods
open PowerSeries

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods

abbrev Qbar : Type := ↥(algebraicClosure ℚ ℂ)

abbrev Place (p : ℕ) [Fact p.Prime] : Type := Qbar →+* ℂ_[p]

abbrev incl (p : ℕ) [Fact p.Prime] : 𝓞_ℂ_[p] →+* ℂ_[p] := algebraMap 𝓞_ℂ_[p] ℂ_[p]

def IsModel {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve ℂ_[p]) (W : WeierstrassCurve 𝓞_ℂ_[p])
    (C : WeierstrassCurve.VariableChange ℂ_[p]) : Prop :=
  C • E = W.map (incl p) ∧ IsUnit W.Δ

section Expansion

variable {A : Type} [CommRing A] (W : WeierstrassCurve A)

def step (v : A⟦X⟧) : A⟦X⟧ :=
  1 + C W.a₁ * X * v + C W.a₂ * X ^ 2 * v + C W.a₃ * X ^ 3 * v ^ 2 + C W.a₄ * X ^ 4 * v ^ 2
    + C W.a₆ * X ^ 6 * v ^ 3

def vSer : A⟦X⟧ := mk fun n => coeff n ((step W)^[n + 1] 0)

def wSer : A⟦X⟧ := X ^ 3 * vSer W

private lemma nodal_map_sub_eq_X_mul_sub_mul (u v : A⟦X⟧) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W u - _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W v =
      X * (u - v) * (C W.a₁ + C W.a₂ * X + C W.a₃ * X ^ 2 * (u + v) + C W.a₄ * X ^ 3 * (u + v)
        + C W.a₆ * X ^ 5 * (u ^ 2 + u * v + v ^ 2)) := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step
  ring

private lemma X_pow_succ_dvd_sub_of_X_pow_dvd {k : ℕ} {u v : A⟦X⟧} (h : X ^ k ∣ u - v) :
    X ^ (k + 1) ∣
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W u - _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W v := by
  rw [nodal_map_sub_eq_X_mul_sub_mul, pow_succ']
  exact Dvd.dvd.mul_right (mul_dvd_mul_left X h) _

private lemma X_pow_dvd_iterate_sub_iterate (n m : ℕ) :
    X ^ n ∣ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[n + m] 0
      - (_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[n] 0 := by
  induction n with
  | zero => rw [pow_zero]; exact one_dvd _
  | succ n ih =>
    have e1 : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[n + 1 + m] 0 =
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W
          ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[n + m] 0) := by
      rw [show n + 1 + m = n + m + 1 by omega]
      exact Function.iterate_succ_apply' _ _ _
    have e2 : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[n + 1] 0 =
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W
          ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[n] 0) :=
      Function.iterate_succ_apply' _ _ _
    rw [e1, e2]
    exact X_pow_succ_dvd_sub_of_X_pow_dvd W ih

private lemma vSer_isFixedPt :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.vSer W =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W (_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.vSer W) := by
  ext k
  have h : X ^ k ∣ _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.vSer W
      - (_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[k] 0 := by
    rw [X_pow_dvd_iff]
    intro m hm
    have h2 := X_pow_dvd_iterate_sub_iterate W (m + 1) (k - (m + 1))
    rw [show m + 1 + (k - (m + 1)) = k by omega, X_pow_dvd_iff] at h2
    have h3 := h2 m (Nat.lt_succ_self m)
    rw [map_sub, sub_eq_zero] at h3
    rw [map_sub, sub_eq_zero, _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.vSer, coeff_mk]
    exact h3.symm
  have h2 := X_pow_succ_dvd_sub_of_X_pow_dvd W h
  have e : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[k + 1] 0 =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W
        ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[k] 0) :=
    Function.iterate_succ_apply' _ _ _
  rw [← e, X_pow_dvd_iff] at h2
  have h3 := h2 k (Nat.lt_succ_self k)
  rw [map_sub, sub_eq_zero] at h3
  rw [h3, _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.vSer, coeff_mk]

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer_eq :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer W = X ^ 3 + C W.a₁ * X * _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer W
      + C W.a₂ * X ^ 2 * _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer W
      + C W.a₃ * _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer W ^ 2
      + C W.a₄ * X * _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer W ^ 2
      + C W.a₆ * _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer W ^ 3 := by
  have hv := vSer_isFixedPt W
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer]
  conv_lhs => rw [hv, _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step]
  ring

end Expansion

end GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods
end
end
