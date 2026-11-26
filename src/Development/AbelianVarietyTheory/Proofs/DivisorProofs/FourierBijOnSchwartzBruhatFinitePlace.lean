module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridNuUnitTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeometricLemmaCellOneBlockSwapEquiv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierBijOnSchwartzBruhatFinitePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierBijOnSchwartzBruhatFinitePlace
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section
namespace GlobalTheory.FourierLocBij

def toCircle {k : Type} [AddMonoid k] (ψ : AddChar k ℂ) (hn : ∀ t, ‖ψ t‖ = 1) : AddChar k Circle where
  toFun t := ⟨ψ t, by simp [Submonoid.unitSphere, hn t]⟩
  map_zero_eq_one' := Circle.ext (by simp)
  map_add_eq_mul' a b := Circle.ext (AddChar.map_add_eq_mul ψ a b)

theorem coe_toCircle {k : Type} [AddMonoid k] (ψ : AddChar k ℂ) (hn : ∀ t, ‖ψ t‖ = 1) (t : k) :
    ((toCircle ψ hn t : Circle) : ℂ) = ψ t := rfl

section General
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem translate_fourier [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) {κ : Type} [Fintype κ]
    (m : Measure (κ → k)) [m.IsAddRightInvariant] (φ : (κ → k) → ℂ) (a y : κ → k) :
    ∫ x, φ (x + a) * (ψ (x ⬝ᵥ y) : ℂ) ∂m = (ψ (-(a ⬝ᵥ y)) : ℂ) * ∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m := by
  rw [← integral_add_right_eq_self (μ := m) (fun x => φ (x + a) * (ψ (x ⬝ᵥ y) : ℂ)) (-a), ← integral_const_mul]
  congr 1
  funext x
  rw [neg_add_cancel_right, add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, neg_dotProduct]
  ring

theorem bijOn_circle [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1)
    (κ : Type) [Fintype κ] (μ : Measure (κ → k)) [μ.IsAddHaarMeasure] :
    Set.BijOn (fun (φ : (κ → k) → ℂ) (y : κ → k) => ∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ)
      (SB (κ → k) : Set _) (SB (κ → k) : Set _) := by
  classical
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  obtain ⟨ν, hν⟩ := (GlobalTheory.SplitWeil.selfDual_measure k ψ hc h1).1
  haveI := hν.1
  set m : Measure (κ → k) := Measure.pi fun _ => ν with hm
  have hμ : μ = μ.addHaarScalarFactor m • m := Measure.isAddLeftInvariant_eq_smul μ m
  set r := μ.addHaarScalarFactor m with hr_def
  have hr : r ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hμ
    exact NeZero.ne μ hμ
  have hT : ∀ φ : (κ → k) → ℂ, (fun y => ∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) =
      fun y => ((r : ℝ) : ℂ) * ∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m := by
    intro φ
    funext y
    rw [hμ, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have key := fun φ hφ => GlobalTheory.SplitWeil.FourierPi.fourier_pi k κ ψ hc h1 ν hν φ hφ
  have hcomp : ∀ (e : (κ → k) ≃ₜ (κ → k)), ∀ f ∈ SB (κ → k), (fun x => f (e x)) ∈ SB (κ → k) :=
    fun e f hf => ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩
  have hr' : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
  refine ⟨fun φ hφ => ?_, fun φ₁ h₁ φ₂ h₂ he => ?_, fun g hg => ?_⟩
  · show (fun y => ∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) ∈ SB (κ → k)
    rw [hT]
    exact Submodule.smul_mem _ ((r : ℝ) : ℂ) (key φ hφ).1
  · have he' : ∀ y, ∫ x, φ₁ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m = ∫ x, φ₂ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m := by
      intro y
      have := congrFun he y
      simp only at this
      rw [hμ, integral_smul_nnreal_measure, integral_smul_nnreal_measure, NNReal.smul_def, NNReal.smul_def,
        Complex.real_smul, Complex.real_smul] at this
      exact mul_left_cancel₀ hr' this
    funext a
    have h1a := (key _ (hcomp (Homeomorph.addRight a) _ h₁)).2
    have h2a := (key _ (hcomp (Homeomorph.addRight a) _ h₂)).2
    simp only [Homeomorph.coe_addRight, zero_add] at h1a h2a
    rw [← h1a, ← h2a]
    congr 1
    funext y
    rw [translate_fourier, translate_fourier, he']
  · obtain ⟨Φ, hΦ⟩ := (GlobalTheory.SplitWeil.FourierSurj.hat_surjective k κ ψ hc h1 ν hν).2 ⟨g, hg⟩
    refine ⟨((r : ℝ) : ℂ)⁻¹ • Φ.1, Submodule.smul_mem _ _ Φ.2, ?_⟩
    simp only
    rw [hT]
    funext y
    have hΦ' : GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν Φ.1 = g := hΦ
    rw [← hΦ']
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [integral_const_mul, ← mul_assoc, mul_inv_cancel₀ hr', one_mul]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat, dotProduct_comm y]
    rfl

end General

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem fourier_bijOn : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (Fv F v) ℂ), Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 → ∀ (κ : Type) [Fintype κ]
    [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)] (μ : Measure (κ → Fv F v)) [μ.IsAddHaarMeasure],
    Set.BijOn (fun (φ : (κ → Fv F v) → ℂ) (y : κ → Fv F v) => ∫ x, φ x * ψ (x ⬝ᵥ y) ∂μ)
      (SB (κ → Fv F v) : Set _) (SB (κ → Fv F v) : Set _) := by
  intro F _ _ v ψ hc hn h1 κ _ inst _ μ _
  letI : MeasurableSpace (Fv F v) := borel _
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := GlobalTheory.SplitWeil.secondCountable (Fv F v)
  have e : inst = MeasurableSpace.pi := by
    rw [BorelSpace.measurable_eq (α := κ → Fv F v)]
    exact (BorelSpace.measurable_eq (α := κ → Fv F v) (self := Pi.borelSpace)).symm
  subst e
  have hcont : Continuous (toCircle ψ hn) := Continuous.subtype_mk hc _
  have hne : toCircle ψ hn ≠ 1 := by
    intro h
    apply h1
    ext t
    simpa [coe_toCircle] using congrArg (fun χ : AddChar (Fv F v) Circle => ((χ t : Circle) : ℂ)) h
  exact bijOn_circle (toCircle ψ hn) hcont hne κ μ

end GlobalTheory.FourierLocBij
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierBijOnSchwartzBruhatFinitePlaceStatement
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_bijOn_schwartzBruhat_finitePlace : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (Fv F v) ℂ), Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 → ∀ (κ : Type) [Fintype κ]
    [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)] (μ : Measure (κ → Fv F v)) [μ.IsAddHaarMeasure],
    Set.BijOn (fun (φ : (κ → Fv F v) → ℂ) (y : κ → Fv F v) => ∫ x, φ x * ψ (x ⬝ᵥ y) ∂μ)
      (SB (κ → Fv F v) : Set _) (SB (κ → Fv F v) : Set _) := by
  first | exact @GlobalTheory.FourierLocBij.fourier_bijOn | exact GlobalTheory.FourierLocBij.fourier_bijOn | (intros; apply GlobalTheory.FourierLocBij.fourier_bijOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalIdempotentDivisibleCongruent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalIdempotentDivisibleCongruent
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.BotPairSmall.IdemChoice

open GlobalTheory.FunObj.StdDatum

theorem exists_idem_of_limit : (∀ (D : D7) (x : 𝓞 D.host.E), ∃ e ∈ OhE D, e * e = e ∧ ∀ N : ℕ, 0 < N → ∃ n : ℕ, 0 < n ∧ ∃ w ∈ OhE D, e = inc D (x : D.host.E) ^ n + (N : AE D) * w) → ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ → ∀ (δ u : 𝓞 D.host.E), inc D ((δ * u : 𝓞 D.host.E) : D.host.E) - 1 ∈ hatId D (D.host.conj • 𝔪) → ∃ f ∈ OhE D, ∃ w ∈ OhE D, f * f = f ∧ f * sgA D f = 0 ∧ f = inc D (δ : D.host.E) * w ∧ 1 - f ∈ hatId D (D.host.conj • 𝔪) := by
  intro hB1 D 𝔪 hsup δ u hδu
  set 𝔫 : Ideal (𝓞 D.host.E) := D.host.conj • 𝔪 with h𝔫
  have gen : ∀ {b : 𝓞 D.host.E}, b ∈ 𝔫 → ∀ {y : AE D}, y ∈ OhE D → inc D (b : D.host.E) * y ∈ hatId D 𝔫 :=
    fun {b} hb {y} hy => AddSubgroup.subset_closure ⟨b, hb, y, hy, rfl⟩
  have gen1 : ∀ {b : 𝓞 D.host.E}, b ∈ 𝔫 → inc D (b : D.host.E) ∈ hatId D 𝔫 := fun hb => by
    simpa using gen hb (one_mem (OhE D))
  by_cases hδ : δ = 0
  · subst hδ
    refine ⟨0, zero_mem _, 0, zero_mem _, by simp, by simp, by simp, ?_⟩
    have : inc D ((0 * u : 𝓞 D.host.E) : D.host.E) - 1 = -1 := by simp
    rw [this] at hδu
    simpa using neg_mem hδu
  have h1m : (1 : 𝓞 D.host.E) ∈ 𝔪 ⊔ 𝔫 := by rw [hsup]; exact Submodule.mem_top
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 h1m
  have h𝔫0 : 𝔫 ≠ ⊥ := by
    intro e
    have h𝔪 : 𝔪 = ⊥ := by
      by_contra h
      exact GlobalTheory.BotPairSmall.conj_smul_ne_bot D h e
    rw [e, h𝔪, sup_bot_eq] at hsup
    exact bot_ne_top hsup
  set x : 𝓞 D.host.E := s * δ * u with hx
  set X : AE D := inc D (x : D.host.E) with hX
  have hXO : X ∈ OhE D := GlobalTheory.CongIdx.inc_int_mem x

  have h1X : 1 - X ∈ hatId D 𝔫 := by
    have e : 1 - X = inc D (t : D.host.E) + inc D (s : D.host.E) * (-(inc D ((δ * u : 𝓞 D.host.E) : D.host.E) - 1)) := by
      have e1 : inc D (s : D.host.E) + inc D (t : D.host.E) = 1 := by
        rw [← map_add (f := _), show (s : D.host.E) + t = ((s + t : 𝓞 D.host.E) : D.host.E) from rfl, hst]; simp
      rw [hX, hx]
      push_cast
      simp only [map_mul]
      linear_combination -e1
    rw [e]
    exact add_mem (gen1 ht) (GlobalTheory.CongIdx.mul_mem_hatId (GlobalTheory.CongIdx.inc_int_mem s) (neg_mem hδu))

  have hxm : x ∈ 𝔪 := by rw [hx, mul_assoc]; exact Ideal.mul_mem_right _ _ hs
  have hsX : sgA D X ∈ hatId D 𝔫 := by
    rw [hX, GlobalTheory.NormSum.PtsMem.sgA_inc]
    exact gen1 (Ideal.smul_mem_pointwise_smul _ _ _ hxm)
  have hsXO : sgA D X ∈ OhE D := VacMove.sgA_mem D hXO

  have hN₁ : 0 < Ideal.absNorm (Ideal.span {δ}) := by
    rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hδ
  have hN₂ : 0 < Ideal.absNorm 𝔫 := by
    rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact h𝔫0
  set N := Ideal.absNorm (Ideal.span {δ}) * Ideal.absNorm 𝔫 with hN
  have hNδ : (N : 𝓞 D.host.E) ∈ Ideal.span {δ} := by
    rw [hN, Nat.cast_mul]; exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
  have hN𝔫 : (N : 𝓞 D.host.E) ∈ 𝔫 := by
    rw [hN, Nat.cast_mul]; exact Ideal.mul_mem_left _ _ (Ideal.absNorm_mem _)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hNδ
  have hNinc : (N : AE D) = inc D ((N : 𝓞 D.host.E) : D.host.E) := by simp
  obtain ⟨e, heO, hee, hlim⟩ := hB1 D x
  obtain ⟨n, hn, w, hwO, hew⟩ := hlim N (Nat.mul_pos hN₁ hN₂)
  set ē := sgA D e with hē
  have hēO : ē ∈ OhE D := VacMove.sgA_mem D heO
  have hēē : ē * ē = ē := by rw [hē, ← map_mul, hee]
  refine ⟨e * (1 - ē), mul_mem heO (sub_mem (one_mem _) hēO), ?_⟩

  have hXd : X = inc D (δ : D.host.E) * inc D ((s * u : 𝓞 D.host.E) : D.host.E) := by
    rw [hX, hx, ← map_mul]; congr 1; push_cast; ring
  have hNd : (N : AE D) = inc D (δ : D.host.E) * inc D (c : D.host.E) := by
    rw [hNinc, ← hc, ← map_mul]; congr 1; push_cast; ring
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hed : e = inc D (δ : D.host.E) *
      (inc D ((s * u : 𝓞 D.host.E) : D.host.E) * X ^ m + inc D (c : D.host.E) * w) := by
    rw [hew, pow_succ, hNd, ← hX]
    linear_combination X ^ m * hXd
  refine ⟨(inc D ((s * u : 𝓞 D.host.E) : D.host.E) * X ^ m + inc D (c : D.host.E) * w) * (1 - ē),
    mul_mem (add_mem (mul_mem (GlobalTheory.CongIdx.inc_int_mem _) (pow_mem hXO m))
      (mul_mem (GlobalTheory.CongIdx.inc_int_mem _) hwO)) (sub_mem (one_mem _) hēO), ?_, ?_, ?_, ?_⟩
  · linear_combination (1 - ē) ^ 2 * hee + e * hēē
  · have hs2 : sgA D (e * (1 - ē)) = ē * (1 - e) := by
      rw [map_mul, map_sub, map_one, hē, GlobalTheory.NormSum.VacMove.sgA_sgA]
    rw [hs2]
    linear_combination (-(1 - ē) * ē) * hee
  · conv_lhs => rw [hed]
    ring
  ·
    have e1 : 1 - e * (1 - ē) = (1 - X ^ (m + 1)) - (N : AE D) * w + e * ē := by rw [hew, ← hX]; ring
    rw [e1]
    refine add_mem (sub_mem ?_ ?_) ?_
    · rw [← mul_neg_geom_sum]
      rw [mul_comm]
      exact GlobalTheory.CongIdx.mul_mem_hatId (sum_mem fun i _ => pow_mem hXO i) h1X
    · rw [hNinc]; exact gen hN𝔫 hwO
    · refine GlobalTheory.CongIdx.mul_mem_hatId heO ?_
      rw [hē, hew, ← hX, map_add (f := _), map_pow, map_mul, pow_succ, map_natCast]
      refine add_mem ?_ ?_
      · exact GlobalTheory.CongIdx.mul_mem_hatId (pow_mem hsXO m) hsX
      · rw [hNinc]; exact gen hN𝔫 (VacMove.sgA_mem D hwO)

end GlobalTheory.BotPairSmall.IdemChoice
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalIdempotentDivisibleCongruentStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonalIdempotent_divisible_congruent : (∀ (D : D7) (x : 𝓞 D.host.E), ∃ e ∈ OhE D, e * e = e ∧ ∀ N : ℕ, 0 < N → ∃ n : ℕ, 0 < n ∧ ∃ w ∈ OhE D, e = inc D (x : D.host.E) ^ n + (N : AE D) * w) → ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ → ∀ (δ u : 𝓞 D.host.E), inc D ((δ * u : 𝓞 D.host.E) : D.host.E) - 1 ∈ hatId D (D.host.conj • 𝔪) → ∃ f ∈ OhE D, ∃ w ∈ OhE D, f * f = f ∧ f * sgA D f = 0 ∧ f = inc D (δ : D.host.E) * w ∧ 1 - f ∈ hatId D (D.host.conj • 𝔪) := by
  first | exact @GlobalTheory.BotPairSmall.IdemChoice.exists_idem_of_limit | exact GlobalTheory.BotPairSmall.IdemChoice.exists_idem_of_limit | (intros; apply GlobalTheory.BotPairSmall.IdemChoice.exists_idem_of_limit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePairingTrivialMatricesSubMem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePairingTrivialMatricesSubMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.VacShapeBd

variable {D : D7} {a a' : ℕ}

theorem symp_add_left' (ξ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)) {n d : ℕ}
    (JA : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)))
    (JB : Matrix (Fin d) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)))
    (x x' y : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E))) :
    GlobalTheory.WeilM.symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ JA JB (x + x') y =
      GlobalTheory.WeilM.symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ JA JB x y +
        GlobalTheory.WeilM.symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ JA JB x' y := by
  unfold GlobalTheory.WeilM.symp GlobalTheory.WeilM.hTens
  simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib, mul_add, map_add (f := _)]

theorem det_ne_zero_skew (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) {d : ℕ} (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d)
    {r s : ℕ} (hY : Y.IsSkew D.sp.cm.sig B r s) : Y.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
  have h := GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hY.sig w)
  intro h0
  apply h
  have hm : (Y.J.map (B.emb w).1).det = (B.emb w).1 Y.J.det := (RingHom.map_det _ _).symm
  rw [Matrix.det_smul, hm, h0, map_zero, mul_zero]

theorem exists_local (v : HeightOneSpectrum (𝓞 D.host.F)) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (c : Fv D.host.F v) :
    ∃ e : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F v) e ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ e = 0 ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp D.sp.cm.sig) e = c := by
  refine ⟨GlobalTheory.SrcHalfOne.plcC τ c, ?_, GlobalTheory.SrcHalfOne.piW_plcC τ c, ?_⟩
  · intro u hu
    have h0 : u * GlobalTheory.LatVac.liftV v c = 0 := GlobalTheory.LatVac.at_liftV v c u hu
    change u • (Formalism.L2.Theta.cA D (GlobalTheory.EmbChart.idem τ) *
      algebraMap (AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)) (GlobalTheory.LatVac.liftV v c)) = 0
    rw [Algebra.smul_def, mul_left_comm, ← map_mul, h0, map_zero, mul_zero]
  · have h := GlobalTheory.SrcHalfOne.piW_cA_plcC τ c
    rw [GlobalTheory.SrcHalfOne.piW_cA] at h
    exact h

theorem coBar_onto (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (hV' : Γ.V'.J.det ≠ 0) (hW : Γ.W.J.det ≠ 0) (Y : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁)) :
    ∃ x : Matrix (Fin a') (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) x ∧ x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = 0 ∧
        GlobalTheory.VacShape.coBar Bs Γ x = Y := by
  set A := Γ.V'.J.map Bs.τ₁ with hAdef
  set B := (Γ.W.J.map Bs.τ₁)ᵀ with hBdef
  have hA : IsUnit A.det := by
    rw [isUnit_iff_ne_zero, hAdef]
    have hm : (Γ.V'.J.map Bs.τ₁).det = (Bs.τ₁ : D.host.E →+* Fv D.host.F Bs.v₁) Γ.V'.J.det :=
      (RingHom.map_det _ _).symm
    rw [hm]
    exact (map_ne_zero _).2 hV'
  have hB : IsUnit B.det := by
    rw [isUnit_iff_ne_zero, hBdef, Matrix.det_transpose]
    have hm : (Γ.W.J.map Bs.τ₁).det = (Bs.τ₁ : D.host.E →+* Fv D.host.F Bs.v₁) Γ.W.J.det :=
      (RingHom.map_det _ _).symm
    rw [hm]
    exact (map_ne_zero _).2 hW
  choose e he using fun c => exists_local (D := D) Bs.v₁ Bs.τ₁ c
  set z : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁) := -(A⁻¹ * Y * B⁻¹) with hz
  refine ⟨z.map e, ?_, ?_, ?_⟩
  · intro u hu
    ext i j
    exact (he (z i j)).1 u hu
  · funext i j
    exact (he (z i j)).2.1
  · have hx : (z.map e).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp D.sp.cm.sig)) = z := by
      funext i j
      exact (he (z i j)).2.2
    unfold GlobalTheory.VacShape.coBar
    rw [hx, ← hAdef, ← hBdef, hz]
    simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hB, Matrix.mul_one]

theorem bd_sub : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om') (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E)),
    ∀ Y h : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁), Y ∈ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂ → Y + h ∈ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂ → h ∈ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂ := by
  intro D a a' Bs Γ X om om' hTr L₁ L₂ Y h hY hYh
  have hV' := GlobalTheory.WeilSchrodingerHerm.det_J_ne_zero D Bs Γ.V' hTr.geo.hV'
  have hW := det_ne_zero_skew Bs Γ.W hTr.geo.hW
  intro x hx hx0 hxh u hu hu0
  obtain ⟨x', hx', hx'0, hx'Y⟩ := coBar_onto Bs Γ hV' hW Y
  have hat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin D.host.F Bs.v₁) (x' + x) := by
    intro w hw
    rw [smul_add, hx' w hw, hx w hw, add_zero]
  have h1 := hYh (x' + x) hat (by rw [Matrix.map_add _ (map_add _), hx'0, hx0, add_zero])
    (by rw [GlobalTheory.VacShape.coBar_add, hx'Y, hxh]) u hu hu0
  have h2 := hY x' hx' hx'0 hx'Y u hu hu0
  rw [symp_add_left', AddChar.map_add_eq_mul, h2, one_mul] at h1
  exact h1

end GlobalTheory.VacShapeBd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePairingTrivialMatricesSubMemStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticePairingTrivialMatrices_sub_mem : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om') (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E)),
    ∀ Y h : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁), Y ∈ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂ → Y + h ∈ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂ → h ∈ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂ := by
  first | exact @GlobalTheory.VacShapeBd.bd_sub | exact GlobalTheory.VacShapeBd.bd_sub | (intros; apply GlobalTheory.VacShapeBd.bd_sub <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralUnitaryGlueIdempotent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralUnitaryGlueIdempotent
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.GlueUnitary

theorem tri_mul {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (e1 e2 e3 : R) (h12 : e1 * e2 = 0) (h13 : e1 * e3 = 0) (h23 : e2 * e3 = 0)
    (A B C A' B' C' : Matrix n n R) :
    (e1 • A + e2 • B + e3 • C) * (e1 • A' + e2 • B' + e3 • C') =
      (e1 * e1) • (A * A') + (e2 * e2) • (B * B') + (e3 * e3) • (C * C') := by
  have h21 : e2 * e1 = 0 := by rw [mul_comm]; exact h12
  have h31 : e3 * e1 = 0 := by rw [mul_comm]; exact h13
  have h32 : e3 * e2 = 0 := by rw [mul_comm]; exact h23
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h12, h13, h23, h21, h31, h32,
    zero_smul, add_zero, zero_add]

theorem st_mul {R : Type*} [CommRing R] {n : Type*} [Fintype n] (s : R →+* R) (A B : Matrix n n R) :
    ((A * B).map s).transpose = (B.map s).transpose * (A.map s).transpose := by
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem st_smul {R : Type*} [CommRing R] {n : Type*} (s : R →+* R) (c : R) (A : Matrix n n R) :
    ((c • A).map s).transpose = s c • (A.map s).transpose := by
  ext i j; simp [Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply]

theorem st_add {R : Type*} [CommRing R] {n : Type*} (s : R →+* R) (A B : Matrix n n R) :
    ((A + B).map s).transpose = (A.map s).transpose + (B.map s).transpose := by
  ext i j; simp [Matrix.map_apply, Matrix.transpose_apply]

theorem st_one {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] (s : R →+* R) :
    (((1 : Matrix n n R)).map s).transpose = 1 := by
  ext i j; by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply, h, Ne.symm h]

theorem st_st {R : Type*} [CommRing R] {n : Type*} (s : R →+* R) (hs : ∀ y, s (s y) = y)
    (A : Matrix n n R) : ((((A.map s).transpose).map s).transpose) = A := by
  ext i j; simp [Matrix.map_apply, Matrix.transpose_apply, hs]

end GlobalTheory.GlueUnitary

namespace GlobalTheory.GlueUnitary

theorem key_alg {R : Type*} [CommRing R] (z p d f fb g : R) (hg : g = 1 - f - fb) (h : fb * f = 0) :
    z - (f * z + fb * p + g * d) = (z - fb * p - (1 - fb) * d) * (1 - f) := by
  subst hg; linear_combination (d - p) * h

theorem glue_unitary : ∀ (D : D7) (𝔫 : Ideal (𝓞 D.host.E)) (a : ℕ) (Z : Matrix (Fin a) (Fin a) (𝓞 D.host.E)) (f w : AE D), f ∈ OhE D → w ∈ OhE D → f * f = f → f * sgA D f = 0 → f = inc D ((Z.det : 𝓞 D.host.E) : D.host.E) * w → 1 - f ∈ hatId D 𝔫 → ∃ k ∈ intG D a, ∀ i l, (Z.map (fun z : 𝓞 D.host.E => inc D (z : D.host.E)) - (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i l ∈ hatId D 𝔫 := by
  intro D 𝔫 a Z f w hf hw hff hffb hfdet h1f
  set s := sgA D with hs
  have hss : ∀ y, s (s y) = y := VacMove.sgA_sgA D
  set φ : 𝓞 D.host.E →+* AE D := (inc D).comp (algebraMap (𝓞 D.host.E) D.host.E) with hφ
  have hφapp : ∀ z : 𝓞 D.host.E, φ z = inc D (z : D.host.E) := fun z => rfl
  have hφint : ∀ z : 𝓞 D.host.E, φ z ∈ OhE D := fun z => VacMove.inc_int D z
  set fb := s f with hfb
  set g := 1 - f - fb with hg
  have hfbf : fb * f = 0 := by rw [mul_comm]; exact hffb
  have hfbfb : fb * fb = fb := by rw [hfb, ← map_mul, hff]
  have hfg : f * g = 0 := by rw [hg]; linear_combination -hff - hffb
  have hfbg : fb * g = 0 := by rw [hg]; linear_combination -hfbf - hfbfb
  have hgg : g * g = g := by rw [hg]; linear_combination hff + hfbfb + 2 * hffb
  have hsg : s g = g := by rw [hg, map_sub, map_sub, map_one, hss]; ring
  have hfO : fb ∈ OhE D := VacMove.sgA_mem D hf
  have hgO : g ∈ OhE D := by
    rw [hg]; exact sub_mem (sub_mem (one_mem _) hf) hfO
  let st : Matrix (Fin a) (Fin a) (AE D) → Matrix (Fin a) (Fin a) (AE D) := fun M => (M.map s).transpose
  let Zi : Matrix (Fin a) (Fin a) (AE D) := Z.map φ
  let P : Matrix (Fin a) (Fin a) (AE D) := w • Z.adjugate.map φ
  have hZP : Zi * P = f • (1 : Matrix (Fin a) (Fin a) (AE D)) := by
    simp only [Zi, P, Matrix.mul_smul, ← Matrix.map_mul, Matrix.mul_adjugate]
    rw [hfdet]
    ext i j
    by_cases h : i = j
    · subst h; simp [Matrix.smul_apply, hφapp, mul_comm]
    · simp [Matrix.smul_apply, Matrix.one_apply, h]
  let X : Matrix (Fin a) (Fin a) (AE D) := f • Zi + fb • st P + g • 1
  let X' : Matrix (Fin a) (Fin a) (AE D) := f • P + fb • st Zi + g • 1
  have hXX' : X * X' = 1 := by
    simp only [X, X']
    rw [tri_mul f fb g hffb hfg hfbg, ← st_mul s Zi P, hZP]
    simp only [st, st_smul, st_one, hff, hfbfb, hgg, Matrix.mul_one, smul_smul]
    rw [← hfb, hfbfb, ← add_smul, ← add_smul, hg]; simp
  have hstX' : st X' = X := by
    simp only [X, X', st, st_add, st_smul, st_one, hsg]
    rw [← hfb, hss, st_st s hss]
    abel
  have hX'X : X' * X = 1 := mul_eq_one_comm.mp hXX'
  let u : GL (Fin a) (AE D) := ⟨X', X, hX'X, hXX'⟩
  have huGA : u ∈ GA D a := by
    rw [PtsMem.mem_GA]
    change st X' * X' = 1
    rw [hstX', hXX']
  let k : GA D a := ⟨u, huGA⟩
  have hkinv : (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) = X := rfl
  have hentO : ∀ (M : Matrix (Fin a) (Fin a) (AE D)), (∀ i j, M i j ∈ OhE D) → ∀ i j, st M i j ∈ OhE D := by
    intro M hM i j; exact VacMove.sgA_mem D (hM j i)
  have hZiO : ∀ i j, Zi i j ∈ OhE D := fun i j => hφint _
  have hPO : ∀ i j, P i j ∈ OhE D := fun i j => mul_mem hw (hφint _)
  have h1O : ∀ i j, (1 : Matrix (Fin a) (Fin a) (AE D)) i j ∈ OhE D := by
    intro i j; by_cases h : i = j
    · subst h; simp [one_mem]
    · simp [Matrix.one_apply, h, zero_mem]
  have hXO : ∀ i j, X i j ∈ OhE D := by
    intro i j
    simp only [X, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact add_mem (add_mem (mul_mem hf (hZiO i j)) (mul_mem hfO (hentO P hPO i j))) (mul_mem hgO (h1O i j))
  have hX'O : ∀ i j, X' i j ∈ OhE D := by
    intro i j
    simp only [X', Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact add_mem (add_mem (mul_mem hf (hPO i j)) (mul_mem hfO (hentO Zi hZiO i j))) (mul_mem hgO (h1O i j))
  refine ⟨k, ?_, ?_⟩
  · rw [mem_intG]
    intro i j
    exact ⟨hX'O i j, hXO i j⟩
  · intro i l
    rw [hkinv]
    have hZ : Z.map (fun z : 𝓞 D.host.E => inc D (z : D.host.E)) = Zi := rfl
    rw [hZ]
    rw [Matrix.sub_apply]
    simp only [X, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [key_alg (Zi i l) (st P i l) ((1 : Matrix (Fin a) (Fin a) (AE D)) i l) f fb g hg hfbf]
    refine GlobalTheory.CongIdx.mul_mem_hatId ?_ h1f
    exact sub_mem (sub_mem (hZiO i l) (mul_mem hfO (hentO P hPO i l))) (mul_mem (sub_mem (one_mem _) hfO) (h1O i l))

end GlobalTheory.GlueUnitary
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralUnitaryGlueIdempotentStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralUnitary_glue_idempotent : ∀ (D : D7) (𝔫 : Ideal (𝓞 D.host.E)) (a : ℕ) (Z : Matrix (Fin a) (Fin a) (𝓞 D.host.E)) (f w : AE D), f ∈ OhE D → w ∈ OhE D → f * f = f → f * sgA D f = 0 → f = inc D ((Z.det : 𝓞 D.host.E) : D.host.E) * w → 1 - f ∈ hatId D 𝔫 → ∃ k ∈ intG D a, ∀ i l, (Z.map (fun z : 𝓞 D.host.E => inc D (z : D.host.E)) - (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i l ∈ hatId D 𝔫 := by
  first | exact @GlobalTheory.GlueUnitary.glue_unitary | exact GlobalTheory.GlueUnitary.glue_unitary | (intros; apply GlobalTheory.GlueUnitary.glue_unitary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiProdCompInvTranspose
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.InvTransposeProd

open Matrix GlobalTheory.TypeTame
open scoped TensorProduct

variable {k : Type} [Field k] {h n : ℕ} {d : Fin h → ℕ}

def revPlace (e : (Σ a, Fin (d a)) ≃ Fin n) : (Σ a : Fin h, Fin (d (Fin.rev a))) ≃ Fin n :=
  (Equiv.sigmaCongrLeft (β := fun b => Fin (d b)) Fin.revPerm).trans e

theorem revPlace_apply (e : (Σ a, Fin (d a)) ≃ Fin n) (a : Fin h) (i : Fin (d (Fin.rev a))) :
    revPlace e ⟨a, i⟩ = e ⟨Fin.rev a, i⟩ := rfl

theorem blk_revPlace (e : (Σ a, Fin (d a)) ≃ Fin n) (x : Fin n) :
    blk e x = Fin.rev (blk (revPlace e) x) := by
  obtain ⟨⟨a, i⟩, rfl⟩ := (revPlace e).surjective x
  rw [blk_apply, revPlace_apply, blk_apply]

theorem mem_parab_revPlace (e : (Σ a, Fin (d a)) ≃ Fin n) {q : GL (Fin n) k} (hq : q ∈ parab k e) :
    invTranspose n q ∈ parab k (revPlace e) := by
  refine mem_parab.2 fun i j hij => ?_
  rw [invTranspose_val, Matrix.transpose_apply]
  refine mem_parab.1 (inv_mem hq) j i ?_
  rw [blk_revPlace e i, blk_revPlace e j]
  exact Fin.rev_lt_rev.2 hij

theorem mem_parab_of_revPlace (e : (Σ a, Fin (d a)) ≃ Fin n) {p : GL (Fin n) k}
    (hp : p ∈ parab k (revPlace e)) : invTranspose n p ∈ parab k e := by
  refine mem_parab.2 fun i j hij => ?_
  rw [invTranspose_val, Matrix.transpose_apply]
  refine mem_parab.1 (inv_mem hp) j i ?_
  rw [blk_revPlace e i, blk_revPlace e j] at hij
  exact Fin.rev_lt_rev.1 hij

theorem leviProj_revPlace (e : (Σ a, Fin (d a)) ≃ Fin n) (q : parab k e)
    (hq : invTranspose n (q : GL (Fin n) k) ∈ parab k (revPlace e)) (b : Fin h) :
    leviProj k (revPlace e) ⟨invTranspose n q, hq⟩ b =
      invTranspose (d (Fin.rev b)) (leviProj k e q (Fin.rev b)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [invTranspose_val, Matrix.transpose_apply, ← Pi.inv_apply, ← map_inv, leviProj_apply, leviProj_apply]
  rfl

theorem det_invTranspose (m : ℕ) (g : GL (Fin m) k) :
    GeneralLinearGroup.det (invTranspose m g) = (GeneralLinearGroup.det g)⁻¹ := by
  ext
  rw [GeneralLinearGroup.val_det_apply, invTranspose_val, Matrix.det_transpose, ← GeneralLinearGroup.val_det_apply,
    map_inv]

omit [Field k] in
theorem modExp_rev (b : Fin h) :
    modExp (fun a => Fin (d (Fin.rev a))) b = -modExp (fun a => Fin (d a)) (Fin.rev b) := by
  unfold modExp
  simp only [Fintype.card_fin, Finset.sum_filter]
  have h1 : (∑ c : Fin h, if b < c then (d (Fin.rev c) : ℤ) else 0) =
      ∑ c : Fin h, if c < Fin.rev b then (d c : ℤ) else 0 :=
    Fintype.sum_equiv Fin.revPerm _ _ fun c => by simp [Fin.rev_lt_rev]
  have h2 : (∑ c : Fin h, if c < b then (d (Fin.rev c) : ℤ) else 0) =
      ∑ c : Fin h, if Fin.rev b < c then (d c : ℤ) else 0 :=
    Fintype.sum_equiv Fin.revPerm _ _ fun c => by simp [Fin.rev_lt_rev]
  rw [h1, h2]
  ring

section Local

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem deltaHalf_revPlace (e : (Σ a, Fin (d a)) ≃ Fin n) (q : parab k e)
    (hq : invTranspose n (q : GL (Fin n) k) ∈ parab k (revPlace e)) :
    deltaHalf k (fun a => Fin (d (Fin.rev a))) (leviProj k (revPlace e) ⟨invTranspose n q, hq⟩) =
      deltaHalf k (fun a => Fin (d a)) (leviProj k e q) := by
  rw [deltaHalf_apply, deltaHalf_apply]
  refine Fintype.prod_equiv Fin.revPerm _ _ fun b => ?_
  rw [leviProj_revPlace e q hq b, det_invTranspose, modExp_rev]
  simp only [Int.cast_neg, neg_div, absPow_neg, MonoidHom.inv_apply, map_inv, inv_inv, Fin.revPerm_apply]
  rfl

variable (X : Fin h → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]

def revTensor : (⨂[ℂ] a, X a) ≃ₗ[ℂ] ⨂[ℂ] a, X (Fin.rev a) :=
  PiTensorProduct.reindex ℂ X Fin.revPerm

theorem revTensor_tprod (z : ∀ a, X a) :
    revTensor X (PiTensorProduct.tprod ℂ z) = PiTensorProduct.tprod ℂ fun a => z (Fin.rev a) :=
  PiTensorProduct.reindex_tprod _ _

variable {X}

def revRep (π' : ∀ a, Representation ℂ (GL (Fin (d (Fin.rev a))) k) (X (Fin.rev a))) :
    Representation ℂ (Levi k fun a => Fin (d (Fin.rev a))) (⨂[ℂ] a, X a) where
  toFun g := (revTensor X).symm.toLinearMap ∘ₗ piTensor π' g ∘ₗ (revTensor X).toLinearMap
  map_one' := by ext; simp
  map_mul' g g' := by ext; simp

def revRepEquiv (π' : ∀ a, Representation ℂ (GL (Fin (d (Fin.rev a))) k) (X (Fin.rev a))) :
    (revRep π').Equiv (piTensor π') :=
  Representation.Equiv.mk (revTensor X) fun g => LinearMap.ext fun v => by
    simp [revRep]

theorem revRep_leviProj (e : (Σ a, Fin (d a)) ≃ Fin n)
    (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (q : parab k e)
    (hq : invTranspose n (q : GL (Fin n) k) ∈ parab k (revPlace e)) :
    revRep (fun a => (π (Fin.rev a)).comp (invTranspose (d (Fin.rev a))))
        (leviProj k (revPlace e) ⟨invTranspose n q, hq⟩) = piTensor π (leviProj k e q) := by
  have key : (piTensor fun a => (π (Fin.rev a)).comp (invTranspose (d (Fin.rev a))))
        (leviProj k (revPlace e) ⟨invTranspose n q, hq⟩) ∘ₗ (revTensor X).toLinearMap =
      (revTensor X).toLinearMap ∘ₗ piTensor π (leviProj k e q) := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun z => ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      revTensor_tprod, piTensor_tprod]
    congr 1
  refine LinearMap.ext fun v => ?_
  show (revTensor X).symm _ = _
  rw [(revTensor X).symm_apply_eq]
  exact LinearMap.congr_fun key v

end Local

theorem multiProd_comp_invTranspose : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h n : ℕ) (d : Fin h → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : (Σ a, Fin (d (Fin.rev a))) ≃ Fin n) (X : Fin h → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)), (∀ a, IsSmooth (π a)) → Nonempty (Representation.Equiv ((multiProd e π).comp (GlobalTheory.TypeTame.invTranspose n)) (multiProd e' fun a => ((π (Fin.rev a)).comp (GlobalTheory.TypeTame.invTranspose (d (Fin.rev a))) : Representation ℂ (GL (Fin (d (Fin.rev a))) k) (X (Fin.rev a))))) := by
  intro k _ _ _ _ h n d e e' X _ _ π _
  set π' : ∀ a, Representation ℂ (GL (Fin (d (Fin.rev a))) k) (X (Fin.rev a)) :=
    fun a => (π (Fin.rev a)).comp (invTranspose (d (Fin.rev a))) with hπ'
  have key : ∀ (q : parab k e) (hq : invTranspose n (q : GL (Fin n) k) ∈ parab k (revPlace e)),
      ((GlobalTheory.SmGL.twist (revRep π') (deltaHalf k _)).comp (leviProj k (revPlace e))) ⟨invTranspose n q, hq⟩ =
        ((GlobalTheory.SmGL.twist (piTensor π) (deltaHalf k _)).comp (leviProj k e)) q := by
    intro q hq
    refine LinearMap.ext fun v => ?_
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, GlobalTheory.SmGL.twist_apply, GlobalTheory.SmGL.twist_apply, deltaHalf_revPlace e q hq,
      hπ', revRep_leviProj e π q hq]
  obtain ⟨A⟩ : Nonempty ((parInd (revPlace e) (revRep π')).Equiv
      ((multiProd e π).comp (invTranspose n))) := by
    refine Relabel.smInd_equiv_comp (P := parab k (revPlace e)) (Q := parab k e)
      (σ := (GlobalTheory.SmGL.twist (revRep π') (deltaHalf k _)).comp (leviProj k (revPlace e)))
      (τ := (GlobalTheory.SmGL.twist (piTensor π) (deltaHalf k _)).comp (leviProj k e))
      (invTranspose n) (invTranspose n) (continuous_invTranspose n) (continuous_invTranspose n)
      (invTranspose_invTranspose n) (invTranspose_invTranspose n)
      (fun q => ⟨⟨_, mem_parab_revPlace e q.2⟩, rfl, key q _⟩) (fun p => ?_)
    have hp : invTranspose n (invTranspose n (p : GL (Fin n) k)) ∈ parab k (revPlace e) := by
      rw [invTranspose_invTranspose]
      exact p.2
    refine ⟨⟨_, mem_parab_of_revPlace e p.2⟩, rfl, ?_⟩
    refine (key ⟨_, mem_parab_of_revPlace e p.2⟩ hp).symm.trans ?_
    exact congrArg _ (Subtype.ext (invTranspose_invTranspose n (p : GL (Fin n) k)))
  obtain ⟨B⟩ := GlobalTheory.T.product_representation_reorder_equiv k h n (fun a => d (Fin.rev a)) (revPlace e) e' (fun a => X (Fin.rev a)) π'
  exact ⟨A.symm.trans ((parIndEquiv (revPlace e) (revRepEquiv π')).trans B)⟩

end GlobalTheory.InvTransposeProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergFixedInvariantOpenCompactCompactSuppor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergFixedInvariantOpenCompactCompactSuppor
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilAdm

open Filter Topology

theorem fixSupp_exists_box {κ X : Type} [Fintype κ] [TopologicalSpace X] {S : Set (κ → X)} {x0 : X}
    (hS : S ∈ 𝓝 (fun _ : κ => x0)) : ∃ O ∈ 𝓝 x0, ∀ u : κ → X, (∀ i, u i ∈ O) → u ∈ S := by
  rw [nhds_pi, Filter.mem_pi] at hS
  obtain ⟨I, -, t, ht, hsub⟩ := hS
  exact ⟨⋂ i, t i, Filter.iInter_mem.2 ht, fun u hu => hsub fun i _ => Set.mem_iInter.1 (hu i) i⟩

variable {F : Type} [Field F] [NumberField F]

theorem fixSupp_finE_zero {κ : Type} : finE F (0 : κ → FiniteAdeleRing (𝓞 F) F) = 0 := by
  funext i; rfl

theorem fixSupp_finE_single {κ : Type} [DecidableEq κ] (j : κ) (t : FiniteAdeleRing (𝓞 F) F) :
    finE F (Pi.single j t : κ → FiniteAdeleRing (𝓞 F) F) = Pi.single j (pairA F 0 t) := by
  funext i
  by_cases hij : i = j
  · subst hij
    show pairA F 0 ((Pi.single i t : κ → FiniteAdeleRing (𝓞 F) F) i) = (Pi.single i (pairA F 0 t) : κ → AdeleRing (𝓞 F) F) i
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · simp only [finE, Pi.single_eq_of_ne hij]; rfl

theorem fixed_schroedinger_invariant_compactSupport_bounded_annihilator (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (hann : ∀ O ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F), ∃ K : Set (FiniteAdeleRing (𝓞 F) F), IsCompact K ∧
      ∀ x : FiniteAdeleRing (𝓞 F) F, (∀ t ∈ O, ψ (pairA F 0 (t * x)) = 1) → x ∈ K)
    (κ : Type) [Fintype κ]
    (M : AddSubgroup ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)))
    (hM : IsOpen (M : Set ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)))) :
    ∃ (U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)) (K : Set (κ → FiniteAdeleRing (𝓞 F) F)),
      IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ IsCompact (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      IsCompact K ∧ ∀ Φ : (κ → AdeleRing (𝓞 F) F) → ℂ, (∀ m ∈ M, GlobalTheory.WeilM.schr ψ (finE2 F m) Φ = Φ) →
        (∀ x, ∀ u ∈ U, Φ (x + finE F u) = Φ x) ∧ ∀ x, (fun i => (x i).2) ∉ K → Φ x = 0 := by
  classical
  have hc1 : Continuous fun u : κ → FiniteAdeleRing (𝓞 F) F => (u, (0 : κ → FiniteAdeleRing (𝓞 F) F)) :=
    continuous_id.prodMk continuous_const
  have hc2 : Continuous fun v : κ → FiniteAdeleRing (𝓞 F) F => ((0 : κ → FiniteAdeleRing (𝓞 F) F), v) :=
    continuous_const.prodMk continuous_id
  have hM1 : (fun u : κ → FiniteAdeleRing (𝓞 F) F => (u, (0 : κ → FiniteAdeleRing (𝓞 F) F))) ⁻¹'
      (M : Set _) ∈ 𝓝 (fun _ : κ => (0 : FiniteAdeleRing (𝓞 F) F)) :=
    (hM.preimage hc1).mem_nhds M.zero_mem
  have hM2 : (fun v : κ → FiniteAdeleRing (𝓞 F) F => ((0 : κ → FiniteAdeleRing (𝓞 F) F), v)) ⁻¹'
      (M : Set _) ∈ 𝓝 (fun _ : κ => (0 : FiniteAdeleRing (𝓞 F) F)) :=
    (hM.preimage hc2).mem_nhds M.zero_mem
  obtain ⟨O₁, hO₁, hbox₁⟩ := fixSupp_exists_box hM1
  obtain ⟨O₂, hO₂, hbox₂⟩ := fixSupp_exists_box hM2
  obtain ⟨N, hN, hNO⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F O₁ hO₁
  obtain ⟨K₀, hK₀, hK₀mem⟩ := hann O₂ hO₂
  let c : FiniteAdeleRing (𝓞 F) F := algebraMap F _ ((N : F)⁻¹)
  have hcN : (N : FiniteAdeleRing (𝓞 F) F) * c = 1 := by
    rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) N, ← map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), map_one]
  have hNc : c * (N : FiniteAdeleRing (𝓞 F) F) = 1 := by rw [mul_comm]; exact hcN
  let h : (κ → FiniteAdeleRing (𝓞 F) F) ≃ₜ (κ → FiniteAdeleRing (𝓞 F) F) :=
    { toFun := fun u i => c * u i
      invFun := fun u i => (N : FiniteAdeleRing (𝓞 F) F) * u i
      left_inv := fun u => funext fun i => by
        show (N : FiniteAdeleRing (𝓞 F) F) * (c * u i) = u i
        rw [← mul_assoc, hcN, one_mul]
      right_inv := fun u => funext fun i => by
        show c * ((N : FiniteAdeleRing (𝓞 F) F) * u i) = u i
        rw [← mul_assoc, hNc, one_mul]
      continuous_toFun := continuous_pi fun i => continuous_const.mul (continuous_apply i)
      continuous_invFun := continuous_pi fun i => continuous_const.mul (continuous_apply i) }
  let φ : (κ → FiniteAdeleRing (𝓞 F) F) →+ (κ → FiniteAdeleRing (𝓞 F) F) :=
    { toFun := fun u i => c * u i
      map_zero' := by funext i; exact mul_zero c
      map_add' := fun u w => by funext i; exact mul_add c (u i) (w i) }
  let U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) :=
    (AddSubgroup.pi Set.univ fun _ => (Formalism.UG.intAd F).toAddSubgroup).comap φ
  have hUset : (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) =
      h ⁻¹' Set.univ.pi fun _ => (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := rfl
  have hint_c : IsCompact (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := Formalism.L2.Col.rlt_isCompact_intAd
  have hint_o : IsOpen (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := Formalism.L2.SG.Pf.top_isOpen_intAd F
  refine ⟨U, Set.univ.pi fun _ => K₀, ?_, ?_, isCompact_univ_pi fun _ => hK₀, fun Φ hΦ => ⟨?_, ?_⟩⟩
  · rw [hUset]; exact (isOpen_set_pi Set.finite_univ fun _ _ => hint_o).preimage h.continuous
  · rw [hUset]; exact h.isCompact_preimage.2 (isCompact_univ_pi fun _ => hint_c)
  · intro x u hu
    have hu1 : ∀ i, u i ∈ O₁ := by
      intro i
      have hi : c * u i ∈ Formalism.UG.intAd F := hu i (Set.mem_univ i)
      have := hNO (c * u i) hi
      rwa [nsmul_eq_mul, ← mul_assoc, hcN, one_mul] at this
    have hm : (u, (0 : κ → FiniteAdeleRing (𝓞 F) F)) ∈ M := hbox₁ u hu1
    have := congrFun (hΦ _ hm) x
    simp only [GlobalTheory.WeilM.schr, finE2, fixSupp_finE_zero, dotProduct_zero, mul_zero, add_zero,
      AddChar.map_zero_eq_one, one_mul] at this
    exact this
  · intro x hx
    by_contra hne
    apply hx
    intro j _
    apply hK₀mem
    intro t ht
    have hv : ∀ i, (Pi.single j t : κ → FiniteAdeleRing (𝓞 F) F) i ∈ O₂ := by
      intro i
      by_cases hij : i = j
      · subst hij; rw [Pi.single_eq_same]; exact ht
      · rw [Pi.single_eq_of_ne hij]; exact mem_of_mem_nhds hO₂
    have hm : ((0 : κ → FiniteAdeleRing (𝓞 F) F), (Pi.single j t : κ → FiniteAdeleRing (𝓞 F) F)) ∈ M :=
      hbox₂ _ hv
    have h1 := congrFun (hΦ _ hm) x
    simp only [GlobalTheory.WeilM.schr, finE2, fixSupp_finE_zero, zero_dotProduct, mul_zero, add_zero] at h1
    rw [fixSupp_finE_single, dotProduct_single] at h1
    have hdot : x j * pairA F 0 t = pairA F 0 (t * (x j).2) :=
      Prod.ext (by show (x j).1 * 0 = 0; exact mul_zero _) (by show (x j).2 * t = t * (x j).2; exact mul_comm _ _)
    rw [hdot] at h1
    exact mul_right_cancel₀ hne (h1.trans (one_mul _).symm)

theorem fixed_invariant_compactSupport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (κ : Type) [Fintype κ]
    (M : AddSubgroup ((κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F) × (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F))), IsOpen (M : Set ((κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F) × (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F))) →
      ∃ (U : AddSubgroup (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (K : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)), IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
        IsCompact (U : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧ IsCompact K ∧
        ∀ Φ : (κ → AF D.host.F) → ℂ, (∀ m ∈ M, GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilAdm.finE2 D.host.F m) Φ = Φ) →
          (∀ x, ∀ u ∈ U, Φ (x + GlobalTheory.WeilAdm.finE D.host.F u) = Φ x) ∧ ∀ x, (fun i => (x i).2) ∉ K → Φ x = 0 := by
  intro D ψ hψ κ _ M hM
  exact fixed_schroedinger_invariant_compactSupport_bounded_annihilator ψ (GlobalTheory.ScalarAnnih.exists_compact_of_annih D ψ hψ) κ M hM

end GlobalTheory.WeilAdm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergFixedInvariantOpenCompactCompactSupporStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_fixed_invariant_open_compact_compact_support : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (κ : Type) [Fintype κ]
    (M : AddSubgroup ((κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F) × (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F))), IsOpen (M : Set ((κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F) × (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F))) →
      ∃ (U : AddSubgroup (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (K : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)), IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧
        IsCompact (U : Set (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧ IsCompact K ∧
        ∀ Φ : (κ → AF D.host.F) → ℂ, (∀ m ∈ M, GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilAdm.finE2 D.host.F m) Φ = Φ) →
          (∀ x, ∀ u ∈ U, Φ (x + GlobalTheory.WeilAdm.finE D.host.F u) = Φ x) ∧ ∀ x, (fun i => (x i).2) ∉ K → Φ x = 0 := by
  first | exact @GlobalTheory.WeilAdm.fixed_invariant_compactSupport | exact GlobalTheory.WeilAdm.fixed_invariant_compactSupport | (intros; apply GlobalTheory.WeilAdm.fixed_invariant_compactSupport <;> assumption)
end
end
