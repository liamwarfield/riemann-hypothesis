module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSchurGA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HeisenbergHaarFactsHold

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StSchurW
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def StBeHerm : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ u ∈ Vfl X, ∀ u' ∈ Vfl X, ∀ η ξ : Wp, ⟪ξ, beOp D X u u' η⟫_ℂ = ⟪beOp D X u' u ξ, η⟫_ℂ

def StBePos : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    aM k r ≤ X.a → ∀ u ∈ Vfl X, ∀ ξ : Wp, 0 ≤ (⟪ξ, beOp D X u u ξ⟫_ℂ).re

def StSchurW : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp), IsDiag D → ∀ v w v' w' : Wp,
    ∫ h : Mt k r, ⟪w, D.π (Matrix.of h) v⟫_ℂ * star ⟪w', D.π (Matrix.of h) v'⟫_ℂ ∂D.μW =
      ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (Module.finrank ℂ Wp : ℂ)

def StSInt : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp), IsDiag D → ∀ b : ℝ, AB k r ≤ b →
    Integrable (fun p : Mt k r × Mt k r => gN (Matrix.of p.2 * Matrix.of p.1) ^ (-b)) (D.μW.prod D.μN)

end ReciprocityTheory.ChartRestriction.DS.Mult1
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSchurG
namespace ReciprocityTheory.ChartRestriction.DS.Mult1

theorem stSchurG : StSchurG := by
  intro k r Wp _ _ _ D X _ hX
  letI := X.hN
  letI := X.hI
  letI := X.hC

  haveI : Nontrivial X.Hs := ⟨⟨X.w, 0, fun h => by
    have hw := X.w_norm
    rw [h, norm_zero] at hw
    exact zero_ne_one hw⟩⟩
  obtain ⟨d, hd, h⟩ := schur_GV D.haarG X.rep X.irr (fun v w => hX v w)
  exact ⟨d, hd, fun v w v' w' => h v w v' w'⟩

end ReciprocityTheory.ChartRestriction.DS.Mult1
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.InHolds
namespace ReciprocityTheory.ChartRestriction.DS.Mult1

theorem multiplicity_one_hypotheses_hold : UnitaryGroupStructuralFacts :=
  ⟨ReciprocityTheory.ChartRestriction.DS.Xi.heisenbergHaarFacts_hold,
    Formalism.FourierDecayAlt.P.setting_with_prescribed_data_exists,
    Formalism.FourierDecayAlt.P.b2_rank_one_coord,
    Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization,
    Formalism.FourierDecayAlt.P.unipotent_weyl_properties,
    Formalism.FourierDecayAlt.P.conjugation_preserves_haar,
    Formalism.FourierDecayAlt.P.lemma_b_from_xi,
    Formalism.FourierDecayAlt.P.orbital_integral_ae_convergence_continuity,
    Formalism.FourierDecayAlt.P.phase_function_bound,
    Formalism.FourierDecayAlt.P.regularized_beta_bound_continuity_sesquilinear,
    Formalism.FourierDecayAlt.P.regularised_average_identity,
    Formalism.FourierDecayAlt.P.unfolding_identity_of_integration_formula,
    Formalism.FourierDecayAlt.P.ae_equality_from_test_functions,
    Formalism.FourierDecayAlt.P.dilation_jacobian_every_setting,
    Formalism.FourierDecayAlt.P.normalisation_unique_every_setting,
    Formalism.QuantumDeterminants.uWNormal,
    Formalism.QuantumDeterminants.ellAdd,
    Formalism.QuantumDeterminants.nSubgroup⟩

end ReciprocityTheory.ChartRestriction.DS.Mult1
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDiagExists
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem isHaarOn_smul_of {k r : ℕ} {U : Set (Mat k r)} {μ : Measure (Mt k r)} (hμ : IsHaarOn U μ)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ∞) : IsHaarOn U (c • μ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [smul_apply, hμ.conc, smul_zero]
  · intro a ha
    have hcont : Continuous (lmulM (k := k) (r := r) a) :=
      continuous_const.matrix_mul continuous_id
    rw [Measure.map_smul c hcont.measurable.aemeasurable, hμ.left a ha]
  · intro a ha
    have hcont : Continuous (rmulF a) := continuous_id.matrix_mul continuous_const
    rw [Measure.map_smul c hcont.measurable.aemeasurable, hμ.right a ha]
  · intro K hK
    rw [smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hct) (hμ.finite_compact K hK)
  · intro h0
    apply hμ.ne_zero
    ext s _
    have h1 := congrArg (fun ν : Measure (Mt k r) => ν s) h0
    simp only [smul_apply, smul_eq_mul, FunLike.coe_zero, Pi.zero_apply, mul_eq_zero] at h1
    simpa [hc0] using h1

theorem stDiagExists (h : UnitaryGroupStructuralFacts) : StDiagExists := by
  unfold StDiagExists
  intro k r Wp _ _ _ z π hk hz hT hrep hun hcont hirr
  unfold UnitaryGroupStructuralFacts at h
  obtain ⟨hB2, hBS, -⟩ := h
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.InductiveHeisenbergInputs at hB2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hCW, -⟩ := hB2
  obtain ⟨D, hDz, hDz', hDπ, hDπ', -⟩ :=
    hBS k r Wp Wp z z π π hk hz hz hT hT hrep hrep hun hun hcont hcont
  have hcomp : IsCompact (UWset k r z) := hCW k r z hz hT
  have hW : IsHaarOn (UWset k r z) D.μW := by
    have h0 := D.haarW
    rw [hDz] at h0
    exact h0
  have hm0 : D.μW Set.univ ≠ 0 := by
    intro h0
    exact hW.ne_zero (Measure.measure_univ_eq_zero.mp h0)
  have hmt : D.μW Set.univ ≠ ∞ := by
    have h1 : D.μW Set.univ ≤ D.μW (UWset k r z) + D.μW (UWset k r z)ᶜ :=
      measure_univ_le_add_compl _
    rw [hW.conc, add_zero] at h1
    exact ne_top_of_le_ne_top (hW.finite_compact _ hcomp).ne h1
  have hc0 : (D.μW Set.univ)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hmt
  have hct : (D.μW Set.univ)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hm0
  have hH : IsHaarOn (UWset k r D.z) ((D.μW Set.univ)⁻¹ • D.μW) :=
    isHaarOn_smul_of D.haarW hc0 hct
  have hH' : IsHaarOn (UWset k r D.z') ((D.μW Set.univ)⁻¹ • D.μW) := by
    rw [hDz', ← hDz]
    exact hH
  let D' : RealPlaceData k r Wp Wp :=
    { D with
      μW := (D.μW Set.univ)⁻¹ • D.μW
      μW' := (D.μW Set.univ)⁻¹ • D.μW
      haarW := hH
      haarW' := hH' }
  refine ⟨D', hDz, hDπ, ?_⟩
  refine ⟨hDz'.trans hDz.symm, hDπ'.trans hDπ.symm, rfl, ?_, ?_⟩
  · show ((D.μW Set.univ)⁻¹ • D.μW) Set.univ = 1
    rw [smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hm0 hmt]
  · show Formalism.MainNotions.S.IsIrredOn (UWset k r D.z) D.π
    rw [hDz, hDπ]
    exact hirr

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDicho
noncomputable section

open MeasureTheory ComplexConjugate
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open ConjugateHilbertSpace

theorem schurDichotomy : SchurDichotomy := by
  intro G _ _ _ _ _ μ _ _ _ H _ _ _ _ θ ρ hθc hθm hθθ hmap hρ1 hρm hiso hcont hsq hirr
  classical
  have hθ1 : θ 1 = 1 := by
    have h := hθm 1 1
    rw [one_mul] at h
    exact mul_left_cancel (a := θ 1) (by rw [mul_one]; exact h.symm)
  have hθinv : ∀ a, θ a⁻¹ = (θ a)⁻¹ := by
    intro a
    apply eq_inv_of_mul_eq_one_left
    rw [← hθm, mul_inv_cancel, hθ1]
  have hθmp : MeasurePreserving θ μ μ := ⟨hθc.measurable, hmap⟩
  have hR : Formalism.MainNotions.BridgeCSchur.SqRep μ ρ := ⟨hρ1, hρm, hiso, hcont, hsq⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : G → (Cj H →L[ℂ] Cj H),
      ∀ g v, τ g v = toCj (ρ (θ g)⁻¹ (ofCj v)) :=
    ⟨fun g => opCj (ρ (θ g)⁻¹), fun g v => opCj_apply _ _⟩
  have hcoef : ∀ g (v w : Cj H), ⟪w, τ g v⟫_ℂ = ⟪ofCj v, ρ (θ g) (ofCj w)⟫_ℂ := by
    intro g v w
    rw [inner_def, hτ]
    have h := hR.inner_left (θ g)⁻¹ (ofCj v) (ofCj w)
    rw [inv_inv] at h
    exact h
  have hT : Formalism.MainNotions.BridgeCSchur.SqRep μ τ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · ext v
      simp only [hτ, hθ1, inv_one, hρ1]
      rfl
    · intro a b
      ext v
      simp only [ContinuousLinearMap.comp_apply, hτ]
      rw [hθm, mul_inv_rev, hρm]
      rfl
    · intro g v
      rw [hτ]
      exact hiso _ _
    · intro v
      have e : (fun g => τ g v) = fun g => toCj (ρ (θ g)⁻¹ (ofCj v)) := funext fun g => hτ g v
      rw [e]
      exact (hcont (ofCj v)).comp hθc.inv
    · intro v w
      have e : (fun g => ⟪w, τ g v⟫_ℂ) = fun g => ⟪ofCj v, ρ (θ g) (ofCj w)⟫_ℂ :=
        funext fun g => hcoef g v w
      rw [e]
      exact (hsq (ofCj w) (ofCj v)).comp_measurePreserving hθmp
  have hirrT : ∀ S : Submodule ℂ (Cj H), IsClosed (S : Set (Cj H)) →
      (∀ g, ∀ v ∈ S, τ g v ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro S hS hSi
    let S' : Submodule ℂ H :=
      { carrier := {x | toCj x ∈ S}
        add_mem' := fun ha hb => S.add_mem ha hb
        zero_mem' := S.zero_mem
        smul_mem' := fun c x hx => by
          have h2 := S.smul_mem (conj c) (show toCj x ∈ S from hx)
          rw [smul_def, Complex.conj_conj] at h2
          show toCj (c • x) ∈ S
          exact h2 }
    have hS'c : IsClosed (S' : Set H) := hS.preimage (eCj (H := H)).symm.continuous
    have hS'i : ∀ h, ∀ x ∈ S', ρ h x ∈ S' := by
      intro h x hx
      have h2 := hSi (θ h⁻¹) (toCj x) hx
      rw [hτ, hθθ, inv_inv] at h2
      exact h2
    rcases hirr S' hS'c hS'i with h | h
    · left
      rw [eq_bot_iff]
      intro v hv
      have h3 : ofCj v ∈ S' := hv
      rw [h, Submodule.mem_bot] at h3
      exact h3
    · right
      rw [eq_top_iff]
      intro v _
      have h3 : ofCj v ∈ S' := by rw [h]; trivial
      exact h3
  by_cases hne : ∃ U : Cj H ≃ₗᵢ[ℂ] H, ∀ g v, U (τ g v) = ρ g (U v)
  · right
    obtain ⟨U, hU⟩ := hne
    refine ⟨((eCj (H := H)).symm.trans U : H ≃ₗᵢ⋆[ℂ] H), ?_, ?_⟩
    · intro g x y
      calc ⟪y, ρ (θ g) x⟫_ℂ = ⟪toCj x, τ g (toCj y)⟫_ℂ := (hcoef g (toCj y) (toCj x)).symm
        _ = ⟪U (toCj x), U (τ g (toCj y))⟫_ℂ := (U.inner_map_map _ _).symm
        _ = ⟪U (toCj x), ρ g (U (toCj y))⟫_ℂ := by rw [hU]
    · intro h v
      have h2 := hU (θ h)⁻¹ (toCj v)
      rw [hτ, hθinv, hθθ, inv_inv] at h2
      exact h2
  · left
    intro x y x' y'
    have h0 := Formalism.MainNotions.BridgeCSchur.schur_orth_ineq hT hR hirrT hirr hne (toCj y) (toCj x) x' y'
    have e : (fun g => ⟪y, ρ (θ g) x⟫_ℂ * star ⟪y', ρ g x'⟫_ℂ) =
        fun g => ⟪toCj x, τ g (toCj y)⟫_ℂ * star ⟪y', ρ g x'⟫_ℂ :=
      funext fun g => congrArg (· * star ⟪y', ρ g x'⟫_ℂ) (hcoef g (toCj y) (toCj x)).symm
    exact (congrArg (fun f => ∫ g, f g ∂μ) e).trans h0

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JPairsA
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.ConjugateNormInequalities

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section frob

attribute [local instance] Matrix.frobeniusNormedAddCommGroup

theorem gN_eq_frob {k r : ℕ} (g : Mat k r) : gN g = ‖g‖ := by
  rw [frobenius_norm_def, gN, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_norm_sq, Real.rpow_two]

theorem gN_mul_le {k r : ℕ} (A B : Mat k r) : gN (A * B) ≤ gN A * gN B := by
  rw [gN_eq_frob, gN_eq_frob, gN_eq_frob]
  exact frobenius_norm_mul A B

theorem gN_conjTranspose {k r : ℕ} (A : Mat k r) : gN Aᴴ = gN A := by
  rw [gN_eq_frob, gN_eq_frob, frobenius_norm_conjTranspose]

end frob

theorem gN_nonneg {k r : ℕ} (A : Mat k r) : 0 ≤ gN A := Real.sqrt_nonneg _

section hpk
variable (k r : ℕ)

theorem Hpk_out {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = 2 * r + k - i.val then 1 else 0 := by
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
  simp only [Hpk, Fin.mk.injEq] at h ⊢
  split_ifs <;> first | rfl | (exfalso; omega)

theorem Hpk_mid {i : Fin (2 * r + k + 1)} (h : ¬(i.val < r ∨ r + k < i.val)) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = i.val then (if i.val = r + k then -1 else 1) else 0 := by
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
  simp only [Hpk, Fin.mk.injEq] at h ⊢
  split_ifs <;> first | rfl | (exfalso; omega)

theorem Hpk_mulVec (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = if i.val < r ∨ r + k < i.val then v ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -v i else v i := by
  simp only [mulVec, dotProduct]
  by_cases h1 : i.val < r ∨ r + k < i.val
  · rw [if_pos h1]
    simp only [Hpk_out k r h1]
    rw [Finset.sum_eq_single ⟨2 * r + k - i.val, by omega⟩]
    · simp
    · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h))]; simp
    · simp
  · rw [if_neg h1]
    simp only [Hpk_mid k r h1]
    rw [Finset.sum_eq_single i]
    · split_ifs <;> first | (exfalso; omega) | simp
    · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h))]; simp
    · simp

theorem Hpk_mulVec_mulVec (v : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ v) = v := by
  ext i
  rw [Hpk_mulVec]
  by_cases h1 : i.val < r ∨ r + k < i.val
  · rw [if_pos h1, Hpk_mulVec]
    have e1 : ((⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1)).val) = 2 * r + k - i.val := rfl
    rw [if_pos (by rw [e1]; omega)]
    congr 1; ext; simp; omega
  · rw [if_neg h1, Hpk_mulVec, if_neg h1]
    split_ifs <;> simp

theorem mat_eq_of_mulVec' {A B : Mat k r} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext i j
  simpa [Matrix.mulVec_single_one] using congrFun (h (Pi.single j 1)) i

theorem Hpk_sq : Hpk k r * Hpk k r = 1 :=
  mat_eq_of_mulVec' k r fun v => by rw [← Matrix.mulVec_mulVec, Hpk_mulVec_mulVec, Matrix.one_mulVec]

theorem UH_left_inv {g : Mat k r} (hg : g ∈ GV k r) : Hpk k r * gᴴ * Hpk k r * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', Hpk_sq]

theorem GV_mul {g x : Mat k r} (hg : g ∈ GV k r) (hx : x ∈ GV k r) : g * x ∈ GV k r := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hx' : xᴴ * Hpk k r * x = Hpk k r := hx
  show (g * x)ᴴ * Hpk k r * (g * x) = Hpk k r
  rw [conjTranspose_mul]
  calc xᴴ * gᴴ * Hpk k r * (g * x) = xᴴ * (gᴴ * Hpk k r * g) * x := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hx']

end hpk

theorem gN_le_mul {k r : ℕ} {g : Mat k r} (hg : g ∈ GV k r) (x : Mat k r) :
    gN x ≤ gN (Hpk k r) ^ 2 * (gN g * gN (g * x)) := by
  have hx : x = Hpk k r * gᴴ * Hpk k r * (g * x) := by
    rw [← Matrix.mul_assoc, UH_left_inv k r hg, Matrix.one_mul]
  have h0 := gN_nonneg (Hpk k r)
  calc gN x = gN (Hpk k r * gᴴ * Hpk k r * (g * x)) := by rw [← hx]
    _ ≤ gN (Hpk k r * gᴴ * Hpk k r) * gN (g * x) := gN_mul_le _ _
    _ ≤ gN (Hpk k r) * gN g * gN (Hpk k r) * gN (g * x) := by
        gcongr
        · exact gN_nonneg _
        · calc gN (Hpk k r * gᴴ * Hpk k r) ≤ gN (Hpk k r * gᴴ) * gN (Hpk k r) := gN_mul_le _ _
            _ ≤ gN (Hpk k r) * gN gᴴ * gN (Hpk k r) := by gcongr; exact gN_mul_le _ _
            _ = gN (Hpk k r) * gN g * gN (Hpk k r) := by rw [gN_conjTranspose]
    _ = gN (Hpk k r) ^ 2 * (gN g * gN (g * x)) := by ring

theorem real_key {A B X c a b : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hX : 0 < X) (hc : 0 < c) (hb : 0 ≤ b)
    (hab : b ≤ a) (hXle : X ≤ c * (B * A)) :
    A ^ (-a) * B ^ (-a) ≤ (X * c⁻¹) ^ (-(a - b)) * B ^ (-b) := by
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hP : 0 < B * A := mul_pos hB0 hA0
  have e1 : A ^ (-a) * B ^ (-a) = (B * A) ^ (-(a - b)) * (B * A) ^ (-b) := by
    rw [← Real.rpow_add hP, Real.mul_rpow hB0.le hA0.le, mul_comm]; ring_nf
  rw [e1]
  have hXc : 0 < X * c⁻¹ := mul_pos hX (inv_pos.2 hc)
  have h1 : (B * A) ^ (-(a - b)) ≤ (X * c⁻¹) ^ (-(a - b)) := by
    refine Real.rpow_le_rpow_of_nonpos hXc ?_ (by linarith)
    rw [mul_inv_le_iff₀ hc]; linarith [hXle]
  have h2 : (B * A) ^ (-b) ≤ B ^ (-b) :=
    Real.rpow_le_rpow_of_nonpos hB0 (by nlinarith) (by linarith)
  exact mul_le_mul h1 h2 (Real.rpow_nonneg hP.le _) (Real.rpow_nonneg hXc.le _)

theorem AB_le_AG (k r : ℕ) : AB k r ≤ AG k r + 1 := by
  simp only [AB, AG, nR]
  push_cast
  nlinarith [sq_nonneg ((k : ℝ) + r - (r + 1)), (Nat.cast_nonneg k : (0 : ℝ) ≤ k),
    (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]

end ReciprocityTheory.ChartRestriction.DS.Mult1.ConjugateNormInequalities
end
end
