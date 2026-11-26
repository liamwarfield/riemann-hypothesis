module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LagrangianGraphsSumEqMatrixCoeffIntegral
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilRepresentationContinuous
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RallisNonGraphLagrangianSumEqZeroCuspidalStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TermInv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilLagrangianTermsAbsTsumLeHeightPoly

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralNeTopOfBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilTsumEnormRationalInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilTsumEnormRationalInvariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.SWAbsInv

open GlobalTheory.RallisCusp

variable {D : D7}

def lagSwap (W : HSp D) (Y : Lag W) : Lag W :=
  ⟨Y.1.map (LinearEquiv.prodComm D.host.E (Fin W.rank → D.host.E) (Fin W.rank → D.host.E)).toLinearMap, by rw [LinearEquiv.finrank_map_eq]; exact Y.2.1, by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
    exact (Y.2.2 y hy y' hy').symm⟩

theorem lagSwap_lagSwap (W : HSp D) (Y : Lag W) : lagSwap W (lagSwap W Y) = Y := by
  apply Subtype.ext
  ext y
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact hz
  · intro hy
    exact ⟨y.swap, ⟨y, hy, rfl⟩, rfl⟩

theorem isLagFrame_lagSwap (W : HSp D) (Y : Lag W) (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E ×
    Matrix (Fin W.rank) (Fin W.rank) D.host.E) (h : IsLagFrame W Y C) : IsLagFrame W (lagSwap W Y) (C.2, C.1) := by
  unfold IsLagFrame at h ⊢
  change _ = Submodule.map (LinearEquiv.prodComm D.host.E _ _).toLinearMap Y.1
  rw [← h, Submodule.map_span, ← Set.range_comp]
  congr 2

theorem lagTerm_swap {V W : HSp D} (μ : Measure (WO V W)) (𝓕 : Set (WO V W))
    (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E) (f₁ f₂ : WO V W → ℂ) :
    lagTerm μ 𝓕 (C.2, C.1) f₂ f₁ = star (lagTerm μ 𝓕 C f₁ f₂) := by
  unfold lagTerm
  rw [Complex.star_def, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp [mul_comm]

section

variable {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {χV χW : (AE D)ˣ →* Circle} {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {νV : Measure (GA D V)}
    {𝓗 : Set (GA D V)} {νW : Measure (GA D W)} {𝓖 : Set (GA D W)} {μ : Measure (WO V W)} {𝓕 : Set (WO V W)}
    {fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E}

theorem tsum_comm (hS : SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr) {f₁ f₂ : WO V W → ℂ} (h₁ : IsThetaFunO ψ V W f₁)
    (h₂ : IsThetaFunO ψ V W f₂) :
    ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) f₂ f₁‖ₑ = ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) f₁ f₂‖ₑ := by
  let e : Lag W ≃ Lag W := ⟨lagSwap W, lagSwap W, lagSwap_lagSwap W, lagSwap_lagSwap W⟩
  rw [← e.tsum_eq]
  refine tsum_congr fun Y => ?_
  have h := (Move.termMove D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS f₂ f₁ h₂ h₁).1 (lagSwap W Y) _
    (isLagFrame_lagSwap W Y (fr Y) (hS.frame Y))
  change ‖lagTerm μ 𝓕 (fr (lagSwap W Y)) f₂ f₁‖ₑ = _
  rw [← h, lagTerm_swap, ← ofReal_norm_eq_enorm, norm_star, ofReal_norm_eq_enorm]

theorem tsum_left (hS : SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr) {f₁ f₂ : WO V W → ℂ} (h₁ : IsThetaFunO ψ V W f₁)
    (h₂ : IsThetaFunO ψ V W f₂) {γ : GA D W} (hγ : γ ∈ GQ W) :
    ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, γ) f₁) f₂‖ₑ = ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) f₁ f₂‖ₑ := by
  let g : GQ W := ⟨γ, hγ⟩
  let e : Lag W ≃ Lag W := ⟨lagAct W g, lagAct W g⁻¹,
    fun Y => by rw [← lagAct_mul, inv_mul_cancel, lagAct_one],
    fun Y => by rw [← lagAct_mul, mul_inv_cancel, lagAct_one]⟩
  rw [← e.tsum_eq]
  refine tsum_congr fun Y => ?_
  have h := (Move.termMove D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS _ f₂ (hS.weil.om_pres (1, γ) f₁ h₁) h₂).1
    (lagAct W g Y) _ (isLagFrame_lagAct W g Y (fr Y) (hS.frame Y))
  have h' := ((Move.termMove D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS f₁ f₂ h₁ h₂).2 γ hγ (gqMat W g)
    (gqMat_map W g).symm).1 (fr Y)
  change ‖lagTerm μ 𝓕 (fr (lagAct W g Y)) (om (1, γ) f₁) f₂‖ₑ = _
  rw [← h, h']

end

theorem tsum_enorm_lagTerm_rat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (F₁ F₂ : WO V W → ℂ), IsThetaFunO ψ V W F₁ → IsThetaFunO ψ V W F₂ → ∀ γ₁ ∈ GQ W, ∀ γ₂ ∈ GQ W, ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, γ₁) F₁) (om (1, γ₂) F₂)‖ₑ = ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) F₁ F₂‖ₑ := by
  intro D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS F₁ F₂ h₁ h₂ γ₁ hγ₁ γ₂ hγ₂
  have p₂ := hS.weil.om_pres (1, γ₂) F₂ h₂
  rw [tsum_left hS h₁ p₂ hγ₁, tsum_comm hS p₂ h₁, tsum_left hS h₂ h₁ hγ₂, tsum_comm hS h₁ h₂]

end GlobalTheory.SWAbsInv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilTsumEnormRationalInvariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelWeil_tsum_enorm_rational_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (F₁ F₂ : WO V W → ℂ), IsThetaFunO ψ V W F₁ → IsThetaFunO ψ V W F₂ → ∀ γ₁ ∈ GQ W, ∀ γ₂ ∈ GQ W, ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, γ₁) F₁) (om (1, γ₂) F₂)‖ₑ = ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) F₁ F₂‖ₑ := by
  first | exact @GlobalTheory.SWAbsInv.tsum_enorm_lagTerm_rat | exact GlobalTheory.SWAbsInv.tsum_enorm_lagTerm_rat | (intros; apply GlobalTheory.SWAbsInv.tsum_enorm_lagTerm_rat <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.EisAbsPf

abbrev LA : Prop := ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∃ (M : ℕ) (C : ℝ), ∀ g₁ g₂ : GA D W, ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ ≤ ENNReal.ofReal (C * ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ W g₁ : ℝ) * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ W g₂ : ℝ)) ^ M)

abbrev LB : Prop := ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (F₁ F₂ : WO V W → ℂ), IsThetaFunO ψ V W F₁ → IsThetaFunO ψ V W F₂ → ∀ γ₁ ∈ GQ W, ∀ γ₂ ∈ GQ W, ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, γ₁) F₁) (om (1, γ₂) F₂)‖ₑ = ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) F₁ F₂‖ₑ

theorem lintegral_ne_top_of_bounds {X : Type*} [MeasurableSpace X] [Mul X] (ν : Measure X) (𝓖 : Set X)
    (hfin : ν 𝓖 < ⊤) (Γ : Set X) (h q : X → ℝ) (hq : ∀ g, 0 ≤ q g)
    (htr : ∀ g, ∃ γ ∈ Γ, h (γ * g) ≤ 2 * q g) (hh : ∀ g, 0 ≤ h g)
    (S : X → X → ENNReal) (hinv : ∀ γ₁ ∈ Γ, ∀ γ₂ ∈ Γ, ∀ g₁ g₂, S (γ₁ * g₁) (γ₂ * g₂) = S g₁ g₂)
    (M : ℕ) (C : ℝ) (hC : ∀ g₁ g₂, S g₁ g₂ ≤ ENNReal.ofReal (C * (h g₁ * h g₂) ^ M))
    (a b : X → ℂ) (C₁ C₂ : ℝ) (hC₁ : ∀ g, ‖a g‖ * q g ^ M ≤ C₁) (hC₂ : ∀ g, ‖b g‖ * q g ^ M ≤ C₂) :
    ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, S g₁ g₂ * ‖a g₁‖ₑ * ‖b g₂‖ₑ ∂ν ∂ν ≠ ⊤ := by
  have hpt : ∀ g₁ g₂, S g₁ g₂ * ‖a g₁‖ₑ * ‖b g₂‖ₑ ≤ ENNReal.ofReal (|C| * 4 ^ M * C₁ * C₂) := by
    intro g₁ g₂
    obtain ⟨γ₁, hγ₁, e1⟩ := htr g₁
    obtain ⟨γ₂, hγ₂, e2⟩ := htr g₂
    have hq₁ := hq g₁
    have hq₂ := hq g₂
    have hS1 : S g₁ g₂ ≤ ENNReal.ofReal (|C| * 4 ^ M * (q g₁ ^ M * q g₂ ^ M)) := by
      rw [← hinv γ₁ hγ₁ γ₂ hγ₂ g₁ g₂]
      refine (hC _ _).trans (ENNReal.ofReal_le_ofReal ?_)
      have hh' : h (γ₁ * g₁) * h (γ₂ * g₂) ≤ (2 * q g₁) * (2 * q g₂) :=
        mul_le_mul e1 e2 (hh _) (by linarith)
      calc C * (h (γ₁ * g₁) * h (γ₂ * g₂)) ^ M
          ≤ |C| * ((2 * q g₁) * (2 * q g₂)) ^ M :=
            mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (mul_nonneg (hh _) (hh _)) hh' M) (pow_nonneg (mul_nonneg (hh _) (hh _)) M)
              (abs_nonneg _)
        _ = |C| * 4 ^ M * (q g₁ ^ M * q g₂ ^ M) := by
            rw [show (2 * q g₁) * (2 * q g₂) = 4 * (q g₁ * q g₂) by ring, mul_pow, mul_pow]; ring
    have hn1 : ‖a g₁‖ₑ = ENNReal.ofReal ‖a g₁‖ := (ofReal_norm_eq_enorm _).symm
    have hn2 : ‖b g₂‖ₑ = ENNReal.ofReal ‖b g₂‖ := (ofReal_norm_eq_enorm _).symm
    have a1 := hC₁ g₁
    have a2 := hC₂ g₂
    have p1 : 0 ≤ ‖a g₁‖ * q g₁ ^ M := mul_nonneg (norm_nonneg _) (pow_nonneg hq₁ M)
    have p2 : 0 ≤ ‖b g₂‖ * q g₂ ^ M := mul_nonneg (norm_nonneg _) (pow_nonneg hq₂ M)
    have c0 : 0 ≤ |C| * 4 ^ M := by positivity
    calc S g₁ g₂ * ‖a g₁‖ₑ * ‖b g₂‖ₑ
        ≤ ENNReal.ofReal (|C| * 4 ^ M * (q g₁ ^ M * q g₂ ^ M)) * ENNReal.ofReal ‖a g₁‖ * ENNReal.ofReal ‖b g₂‖ := by
          rw [hn1, hn2]; gcongr
      _ = ENNReal.ofReal (|C| * 4 ^ M * (‖a g₁‖ * q g₁ ^ M) * (‖b g₂‖ * q g₂ ^ M)) := by
          have c1 : 0 ≤ |C| * 4 ^ M * (q g₁ ^ M * q g₂ ^ M) := mul_nonneg c0 (mul_nonneg (pow_nonneg hq₁ M) (pow_nonneg hq₂ M))
          rw [← ENNReal.ofReal_mul c1, ← ENNReal.ofReal_mul (mul_nonneg c1 (norm_nonneg _))]
          congr 1; ring
      _ ≤ ENNReal.ofReal (|C| * 4 ^ M * C₁ * C₂) := by
          refine ENNReal.ofReal_le_ofReal ?_
          calc |C| * 4 ^ M * (‖a g₁‖ * q g₁ ^ M) * (‖b g₂‖ * q g₂ ^ M)
              ≤ |C| * 4 ^ M * C₁ * (‖b g₂‖ * q g₂ ^ M) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left a1 c0) p2
            _ ≤ |C| * 4 ^ M * C₁ * C₂ :=
                mul_le_mul_of_nonneg_left a2 (mul_nonneg c0 (p1.trans a1))
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal (|C| * 4 ^ M * C₁ * C₂) * ν 𝓖 * ν 𝓖) ?_ ?_
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne) hfin.ne
  · calc ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, S g₁ g₂ * ‖a g₁‖ₑ * ‖b g₂‖ₑ ∂ν ∂ν
        ≤ ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, ENNReal.ofReal (|C| * 4 ^ M * C₁ * C₂) ∂ν ∂ν :=
          lintegral_mono fun g₁ => lintegral_mono fun g₂ => hpt g₁ g₂
      _ = ENNReal.ofReal (|C| * 4 ^ M * C₁ * C₂) * ν 𝓖 * ν 𝓖 := by
          rw [setLIntegral_const, setLIntegral_const]

theorem eisAbs_of_bounds (hP : GlobalTheory.Published.CuspRapidDecay) (hV : GlobalTheory.Mem.Vol.FiniteVolume₂) (hA : LA) (hB : LB) :
    ∀ D : D7, EisAbs D := by
  intro D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ h1 h2 φ₁ φ₂ hA1 hC1 hA2 hC2
  obtain ⟨M, C, hC⟩ := hA D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ h1 h2
  have e : ∀ γ g : GA D W, om (1, γ * g) = om (1, γ) * om (1, g) := by
    intro γ g; rw [← map_mul, Prod.mk_mul_mk, one_mul]
  have hinv : ∀ γ₁ ∈ (GQ W : Set (GA D W)), ∀ γ₂ ∈ (GQ W : Set (GA D W)), ∀ g₁ g₂ : GA D W,
      (∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, γ₁ * g₁) f₁) (om (1, γ₂ * g₂) f₂)‖ₑ) =
        ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ := by
    intro γ₁ hγ₁ γ₂ hγ₂ g₁ g₂
    rw [e γ₁ g₁, e γ₂ g₂, Module.End.mul_apply, Module.End.mul_apply]
    exact hB D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS _ _ (hS.weil.om_pres _ _ h1) (hS.weil.om_pres _ _ h2)
      γ₁ hγ₁ γ₂ hγ₂
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.CuspDecay.isRapidDecay_of_cuspForm hP hθ hA1 hC1 M
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.CuspDecay.isRapidDecay_of_cuspForm hP hθ hA2 hC2 M
  have hfin : νW 𝓖 < ⊤ := GlobalTheory.CuspDecay.measure_lt_top hV W νW 𝓖 hS.haarW hS.fdW
  have key := lintegral_ne_top_of_bounds νW 𝓖 hfin (GQ W : Set (GA D W))
    (fun g => (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ W g : ℝ)) (fun g => (GlobalTheory.CuspDecay.quotHeight θ W g : ℝ))
    (fun g => NNReal.coe_nonneg _)
    (fun g => by
      obtain ⟨γ, hγ, hle⟩ := GlobalTheory.CuspDecay.exists_height_le (θ := θ) g
      exact ⟨γ, hγ, by exact_mod_cast hle⟩)
    (fun g => NNReal.coe_nonneg _)
    (fun g₁ g₂ => ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ) hinv M C hC φ₁ φ₂ C₁ C₂ hC₁ hC₂
  refine ne_top_of_le_ne_top key (le_of_eq ?_)
  refine lintegral_congr fun g₁ => lintegral_congr fun g₂ => ?_
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right]

theorem eisAbs : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, EisAbs D :=
  fun hP => eisAbs_of_bounds hP GlobalTheory.Mem.VolFin.finVol GlobalTheory.T.siegelWeilLagrangianTerms_abs_tsum_le_heightPoly GlobalTheory.T.siegelWeil_tsum_enorm_rational_invariant

end GlobalTheory.EisAbsPf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SwSection
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SWPairProof

open GlobalTheory.RawLift

variable {D : D7}

theorem kernel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χV χW om →
    ∃ omh : GA D (GlobalTheory.Doubling.dblSp W) × GA D V →* Module.End ℂ (WO (GlobalTheory.Doubling.dblSp W) V → ℂ),
      IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp W) V 1 χV omh ∧
      ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsThetaFunO ψ (GlobalTheory.Doubling.dblSp W) V (dbl V W f₁ f₂) ∧
        ∀ h, thetaKO omh 1 h (dbl V W f₁ f₂) = thetaKO om h 1 f₁ * star (thetaKO om h 1 f₂) := by
  intro D ψ V W χV χW om hw
  have hS := GlobalTheory.AdjLawPf.adjLaw D ψ hw.std V W
  have hom' := GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint D ψ V W χV χW om hw
  have hr : ResEta D 1 (GlobalTheory.Doubling.dblSp W).rank := by
    have := GlobalTheory.Eis.SimplePoleModel.resEta_one_two_mul D W.rank
    convert this using 2
    simp [GlobalTheory.Doubling.dblSp]
    omega
  obtain ⟨omh, homh⟩ := GlobalTheory.weilRepresentationUnitaryPair D ψ (GlobalTheory.Doubling.dblSp W) V 1 χV hw.std
    ⟨continuous_const, fun _ => rfl⟩ hw.hecS hr hw.resS
  refine ⟨omh, homh, fun f₁ f₂ h₁ h₂ => ?_⟩
  have TC := GlobalTheory.DoublingTheta.thetaClause D ψ W V χW χV (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint om) omh hom' homh
  obtain ⟨hth, hrest⟩ := TC (GlobalTheory.PairLift.dag V W f₂) (GlobalTheory.PairLift.dag V W f₁) (hS.theta _ h₂) (hS.theta _ h₁)
  refine ⟨hth, fun h => ?_⟩
  have e := (hrest 1 1 h).2
  have dd : ∀ f : WO V W → ℂ, GlobalTheory.PairLift.dag W V (GlobalTheory.PairLift.dag V W f) = f := fun f => by
    funext y; simp only [GlobalTheory.PairLift.dag, hS.invol, Complex.conj_conj]
  have d0 : GlobalTheory.PairLift.adjO V W 0 = 0 := by
    have := hS.add 0 0
    rw [add_zero] at this
    exact (add_eq_left.1 this.symm)
  have k : ∀ f : WO V W → ℂ, thetaKO (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint om) 1 h (GlobalTheory.PairLift.dag V W f) =
      starRingEnd ℂ (thetaKO om h 1 f) := fun f => by
    simp only [thetaKO, GlobalTheory.ConjAdjWeil.conjAdjoint_apply, dd]
    simp only [GlobalTheory.PairLift.dag, d0]
  have i1 : GlobalTheory.Doubling.io W (1, 1) = 1 := map_one _
  rw [i1, k, k, Complex.conj_conj] at e
  simp only [map_one, inv_one, Circle.coe_one, mul_one] at e
  rw [show dbl V W f₁ f₂ = GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta W V (GlobalTheory.PairLift.dag V W f₂) (GlobalTheory.PairLift.dag V W f₁) from rfl, e]
  simp only [Complex.star_def]
  ring

theorem terms : ∀ (D : D7) ψ (V W : HSp D) χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr,
    SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ →
    ∀ (χ : (AE D)ˣ →* Circle) (omh : GA D (GlobalTheory.Doubling.dblSp W) × GA D V →* Module.End ℂ (WO (GlobalTheory.Doubling.dblSp W) V → ℂ)),
      IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp W) V 1 χ omh →
    ∀ (ν : Measure (Mx D V.rank W.rank)) (𝓖' : Set (Mx D V.rank W.rank)), IsCovolOne (ratL V W) ν 𝓖' →
      ∃ e : GlobalTheory.Eis.Cosets (GlobalTheory.Doubling.siegel W) (GQ (GlobalTheory.Doubling.dblSp W)) ≃ Lag W, ∀ q,
        GlobalTheory.Eis.term (GlobalTheory.Doubling.siegel W) (GQ (GlobalTheory.Doubling.dblSp W))
          (GlobalTheory.SiegelFormula.swSection W V ν 𝓖' omh (dbl V W f₁ f₂)) 1 q = lagTerm μ 𝓕 (fr (e q)) f₁ f₂ := by
  intro D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hs f₁ f₂ h₁ h₂ χ omh hω ν 𝓖' hν
  obtain ⟨omh', -, hK⟩ := kernel D ψ V W χV χW om hs.weil
  have hF := (hK f₁ f₂ h₁ h₂).1
  obtain ⟨e, he⟩ := GlobalTheory.T.siegelEisenstein_doubledTheta_terms_eq_lagrangianIntegrals D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hs f₁ f₂ h₁ h₂ ν 𝓖' hν
  refine ⟨e, fun q => ?_⟩
  obtain ⟨C, hC, hq⟩ := he q
  rw [← GlobalTheory.T.doubled_lagrangian_term_frame_independent D ψ V W μ 𝓕 hs.covol hs.weil.std f₁ f₂ h₁ h₂ (e q) C (fr (e q)) hC (hs.frame _), ← hq]
  simp only [GlobalTheory.Eis.term, mul_one, GlobalTheory.SiegelFormula.swSection, GlobalTheory.SiegelFormula.valZero]
  congr 1
  funext y
  exact GlobalTheory.T.rational_source_acts_on_orientedTheta_by_substitution D ψ _ V 1 χ omh hω _ hF _ (q.out : GQ (GlobalTheory.Doubling.dblSp W)).2 _

theorem swPair (hW : GlobalTheory.Published.WeilSiegelFormulaUnitary) (D : D7) : SWPair D := by
  intro ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hs f₁ f₂ h₁ h₂
  rcases Nat.eq_zero_or_pos W.rank with h0 | hr
  · exact Model.swPair_rank_zero hs h0 f₁ f₂
  obtain ⟨omh, hω, hK⟩ := kernel D ψ V W χV χW om hs.weil
  obtain ⟨hF, hθ⟩ := hK f₁ f₂ h₁ h₂
  haveI := hs.haarV
  have hwitt : Formalism.MainNotions.SchurIrreducible.wittIdx V = 0 := by
    rw [GlobalTheory.RallisIP.wittIdx_eq_wittIndex]
    exact GlobalTheory.Cusp.wittIndex_eq_zero_iff_isAniso.2 (GlobalTheory.Per.isAniso_of_posDef hs.sigOK hs.pos)
  obtain ⟨ν, 𝓖', hν⟩ := GlobalTheory.Size.exists_isCovolOne W V
  have P := (hW D W V νV hs.haarV hr (Or.inl hwitt)).2 ψ χV omh hω (dbl V W f₁ f₂) hF
  obtain ⟨-, hconv⟩ := P.2 hs.big ν 𝓖' hν
  obtain ⟨hc, hsum⟩ := hconv 1
  obtain ⟨e, he⟩ := terms D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hs f₁ f₂ h₁ h₂ χV omh hω ν 𝓖' hν
  have H1 := hc.hasSum
  rw [hsum] at H1
  have H2 : HasSum (fun Y : Lag W => lagTerm μ 𝓕 (fr Y) f₁ f₂)
      (⨍ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (fun h => thetaKO omh 1 h (dbl V W f₁ f₂)) q ∂GlobalTheory.AutomorphicL2Unitary.autMeasure V νV) := by
    refine e.hasSum_iff.1 ?_
    convert H1 using 1
    funext q
    simp [he]
  have A : (⨍ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (fun h => thetaKO omh 1 h (dbl V W f₁ f₂)) q ∂GlobalTheory.AutomorphicL2Unitary.autMeasure V νV) =
      ⨍ h in 𝓗, thetaKO omh 1 h (dbl V W f₁ f₂) ∂νV :=
    GlobalTheory.ThetaMean.thetaMean_eq hω hF hs.fdV 1
  have vol := GlobalTheory.Mem.QuotVol.quot_volume_ne_zero_ne_top D V νV 𝓗 ⟨hs.haarV, hs.fdV⟩
  have hv : ((νV 𝓗).toReal : ℂ) ≠ 0 := by
    exact_mod_cast (ENNReal.toReal_ne_zero.2 vol)
  have key : ∫ h in 𝓗, thetaKO om h 1 f₁ * star (thetaKO om h 1 f₂) ∂νV = ((νV 𝓗).toReal : ℂ) *
      (⨍ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (fun h => thetaKO omh 1 h (dbl V W f₁ f₂)) q ∂GlobalTheory.AutomorphicL2Unitary.autMeasure V νV) := by
    rw [A, setAverage_eq, Complex.real_smul, Measure.real, Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hv, one_mul]
    simp_rw [hθ]
  rw [key]
  exact H2.mul_left _

end GlobalTheory.SWPairProof

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KerAbsOfCuspRapidDecay
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift

theorem kerAbs_of_cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, KerAbs D := by
  intro hP D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ
  have hfinV := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V νV 𝓗 hS.haarV hS.fdV
  refine ⟨hfinV.ne, fun f hf φ hφ hc => ?_⟩
  have : BorelSpace (GA D W) := ⟨rfl⟩
  obtain ⟨A, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D V.rank W.rank
  obtain ⟨U, hU, hl⟩ := GlobalTheory.Size.isTheta_iff_level.1 hf
  obtain ⟨μ', 𝓕', hμ'⟩ := GlobalTheory.Size.exists_isCovolOne V W
  obtain ⟨C, hC0, hC⟩ := (H V W rfl rfl).real ψ hθ hU
  have hb := (hC χV χW om hS.weil μ' 𝓕' hμ' f hl).2
  set s := (GlobalTheory.Size.sobO ψ θ μ' 𝓕' d f).toReal with hs
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.DefiniteQuotient.exists_compact V (fun τ => hS.posDef (tauE D τ))
  obtain ⟨M₀, hM₀⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact V hK
  set M := max M₀ 1 with hMdef
  have hM : ∀ c ∈ K, GlobalTheory.Grow.height V c ≤ M := fun c hc => (hM₀ c hc).trans (le_max_left _ _)
  have hM0 : 0 ≤ M := zero_le_one.trans (le_max_right _ _)

  have hunif : ∀ h g, ‖thetaKO om h g f‖ ≤ C * s * M ^ A * GlobalTheory.Grow.height W g ^ A := by
    intro h g
    obtain ⟨γ, hγ, c, hc', rfl⟩ := hcov h
    rw [GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_left_fst hS.weil hf g γ hγ c]
    calc ‖thetaKO om c g f‖ ≤ C * s * (GlobalTheory.Grow.height V c * GlobalTheory.Grow.height W g) ^ A := hb c g
      _ = C * s * GlobalTheory.Grow.height V c ^ A * GlobalTheory.Grow.height W g ^ A := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (GlobalTheory.Grow.height_pos V c).le (hM c hc') A) (mul_nonneg hC0 hs0))
            (pow_nonneg (GlobalTheory.Grow.height_pos W g).le A)
  have hR := GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ hφ hc
  obtain ⟨B0, hB0⟩ := hR.decay A
  have hq : ∀ h g, ‖star (thetaKO om h g f)‖ ≤ C * s * M ^ A * 2 ^ A * GlobalTheory.Grow.quotHeight W g ^ A := by
    intro h g
    rw [norm_star]
    exact GlobalTheory.Grow.norm_le_quotHeight_pow (f := fun g => thetaKO om h g f)
      (GlobalTheory.Chain.LiftConv.thetaKO_left hS.weil hf h) (hunif h) g
  have hfinW := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol W νW 𝓖 hS.haarW hS.fdW
  refine ⟨C * s * M ^ A * 2 ^ A * B0 * νW.real 𝓖, fun h => ⟨?_, ?_⟩⟩
  · exact hR.integrableOn_mul_of_le hS.haarW hS.fdW
      (GlobalTheory.Chain.LiftConv.thetaKO_continuous hS.weil hf h).star.aestronglyMeasurable (hq h)
  · refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    refine norm_setIntegral_le_of_norm_le_const hfinW fun g _ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    have h1 := hq h g
    rw [norm_star] at h1
    have hK0 : 0 ≤ C * s * M ^ A * 2 ^ A := by positivity
    calc ‖thetaKO om h g f‖ * ‖φ g‖ ≤ C * s * M ^ A * 2 ^ A * GlobalTheory.Grow.quotHeight W g ^ A * ‖φ g‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = C * s * M ^ A * 2 ^ A * (‖φ g‖ * GlobalTheory.Grow.quotHeight W g ^ A) := by ring
      _ ≤ C * s * M ^ A * 2 ^ A * B0 := mul_le_mul_of_nonneg_left (hB0 g) hK0

end GlobalTheory.RawLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RallisConvOfSteps
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilSumDoubleIntegralExchangeCuspForms
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilSumDoubleIntegralExchangeCuspForms
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RallisExch

theorem exch_general {X ι : Type*} [MeasurableSpace X] [Countable ι] (ν : Measure X) [SFinite ν] (𝓖 : Set X)
    (T : ι → X × X → ℂ) (a b : X → ℂ)
    (hT : ∀ Y, AEStronglyMeasurable (T Y) ((ν.prod ν).restrict (𝓖 ×ˢ 𝓖)))
    (ha : AEStronglyMeasurable a (ν.restrict 𝓖)) (hb : AEStronglyMeasurable b (ν.restrict 𝓖))
    (hfin : ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, ∑' Y, ‖T Y (g₁, g₂)‖ₑ * ‖a g₁‖ₑ * ‖b g₂‖ₑ ∂ν ∂ν ≠ ⊤) :
    (∀ Y, IntegrableOn (fun p : X × X => star (a p.1) * b p.2 * T Y p) (𝓖 ×ˢ 𝓖) (ν.prod ν)) ∧
    Summable (fun Y => ∫ p in 𝓖 ×ˢ 𝓖, star (a p.1) * b p.2 * T Y p ∂(ν.prod ν)) ∧
    ∫ p in 𝓖 ×ˢ 𝓖, star (a p.1) * b p.2 * ∑' Y, T Y p ∂(ν.prod ν) =
      ∑' Y, ∫ p in 𝓖 ×ˢ 𝓖, star (a p.1) * b p.2 * T Y p ∂(ν.prod ν) := by
  have hρ : (ν.prod ν).restrict (𝓖 ×ˢ 𝓖) = (ν.restrict 𝓖).prod (ν.restrict 𝓖) :=
    (Measure.prod_restrict 𝓖 𝓖).symm
  set ρ := (ν.prod ν).restrict (𝓖 ×ˢ 𝓖) with hρdef
  set F : ι → X × X → ℂ := fun Y p => star (a p.1) * b p.2 * T Y p with hFdef
  have ha' : AEStronglyMeasurable (fun p : X × X => star (a p.1)) ρ := by
    rw [hρ]; exact ha.star.comp_fst
  have hb' : AEStronglyMeasurable (fun p : X × X => b p.2) ρ := by
    rw [hρ]; exact hb.comp_snd
  have hF : ∀ Y, AEStronglyMeasurable (F Y) ρ := fun Y => (ha'.mul hb').mul (hT Y)
  have hnorm : ∀ Y p, ‖F Y p‖ₑ = ‖T Y p‖ₑ * ‖a p.1‖ₑ * ‖b p.2‖ₑ := by
    intro Y p
    have hs : ‖star (a p.1)‖ₑ = ‖a p.1‖ₑ := by rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, norm_star]
    simp only [F, enorm_mul, hs]; ring
  have hsum : ∑' Y, ∫⁻ p, ‖F Y p‖ₑ ∂ρ ≠ ⊤ := by
    rw [← lintegral_tsum (fun Y => (hF Y).enorm)]
    simp_rw [hnorm]
    rw [hρ, lintegral_prod _ ?_]
    · exact hfin
    · rw [← hρ]
      exact AEMeasurable.tsum fun Y => by
        simpa [hnorm] using (hF Y).enorm
  have hint : ∀ Y, Integrable (F Y) ρ := fun Y =>
    ⟨hF Y, lt_of_le_of_lt (ENNReal.le_tsum (f := fun Y => ∫⁻ p, ‖F Y p‖ₑ ∂ρ) Y)
      (lt_top_iff_ne_top.2 hsum)⟩
  refine ⟨hint, ?_, ?_⟩
  · refine Summable.of_norm_bounded (ENNReal.summable_toReal hsum) fun Y => ?_
    have h1 := enorm_integral_le_lintegral_enorm (μ := ρ) (F Y)
    rw [← ofReal_norm_eq_enorm] at h1
    exact (ENNReal.ofReal_le_iff_le_toReal (ne_top_of_le_ne_top hsum (ENNReal.le_tsum Y))).1 h1
  · have : (fun p : X × X => star (a p.1) * b p.2 * ∑' Y, T Y p) = fun p => ∑' Y, F Y p := by
      funext p; exact tsum_mul_left.symm
    rw [this]
    exact integral_tsum hF hsum

end GlobalTheory.RallisExch

namespace GlobalTheory.RallisExch

open scoped GlobalTheory.GaugeEx

theorem eisAbs_exchange : ∀ D : D7, EisAbs D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ → (∀ Y : Lag W, IntegrableOn (fun p : GA D W × GA D W => star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂)) (𝓖 ×ˢ 𝓖) (νW.prod νW)) ∧ Summable (fun Y : Lag W => ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW)) ∧ ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * ∑' Y : Lag W, lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) = ∑' Y : Lag W, ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) := by
  intro D hE ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ φ₁ φ₂ h1 h2 hA1 hC1 hA2 hC2
  haveI : Countable (Lag W) := GlobalTheory.T.countable_doubled_hermitian_lagrangians D W
  haveI : SigmaFinite νW := by haveI := hS.haarW; infer_instance
  have hT : ∀ Y : Lag W, AEStronglyMeasurable
      (fun p : GA D W × GA D W => lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂))
      ((νW.prod νW).restrict (𝓖 ×ˢ 𝓖)) := fun Y =>
    (GlobalTheory.T.siegelWeil_lagrangian_term_stronglyMeasurable D ψ V W χV χW om μ 𝓕 hS.weil hS.covol f₁ f₂ h1 h2 (fr Y)).aestronglyMeasurable
  exact exch_general νW 𝓖 (fun Y p => lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂)) φ₁ φ₂ hT
    hA1.cont.aestronglyMeasurable hA2.cont.aestronglyMeasurable
    (hE ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ h1 h2 φ₁ φ₂ hA1 hC1 hA2 hC2)

end GlobalTheory.RallisExch
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilSumDoubleIntegralExchangeCuspFormsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelWeilSum_doubleIntegral_exchange_cuspForms : ∀ D : D7, EisAbs D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ → (∀ Y : Lag W, IntegrableOn (fun p : GA D W × GA D W => star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂)) (𝓖 ×ˢ 𝓖) (νW.prod νW)) ∧ Summable (fun Y : Lag W => ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW)) ∧ ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * ∑' Y : Lag W, lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) = ∑' Y : Lag W, ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) := by
  first | exact @GlobalTheory.RallisExch.eisAbs_exchange | exact GlobalTheory.RallisExch.eisAbs_exchange | (intros; apply GlobalTheory.RallisExch.eisAbs_exchange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RallisInnerProductKernelIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RallisInnerProductKernelIdentity
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift

theorem rallis_kernel_step : ∀ D : D7, KerAbs D → SWPair D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ → (∀ h, IntegrableOn (fun g => star (thetaKO om h g f₁) * φ₁ g) 𝓖 νW) ∧ IntegrableOn (fun h => star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h) 𝓗 νV ∧ ∫ h in 𝓗, star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h ∂νV = ((νV 𝓗).toReal : ℂ) * ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * ∑' Y : Lag W, lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) := by
  intro D hKer hSW ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂ hφ₁ hc₁ hφ₂ hc₂
  obtain ⟨lcV, scV, t2V⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V
  obtain ⟨lcW, scW, t2W⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D W
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : BorelSpace (GA D W) := ⟨rfl⟩
  haveI := hS.haarV
  haveI := hS.haarW
  obtain ⟨hfin, hK⟩ := hKer ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ
  obtain ⟨B₁, hB₁⟩ := hK f₁ hf₁ φ₁ hφ₁ hc₁
  obtain ⟨B₂, hB₂⟩ := hK f₂ hf₂ φ₂ hφ₂ hc₂
  haveI : IsFiniteMeasure (νV.restrict 𝓗) := isFiniteMeasure_restrict.2 hfin
  have hk : ∀ f, IsThetaFunO ψ V W f → Continuous fun p : GA D V × GA D W => thetaKO om p.1 p.2 f :=
    fun f hf => hS.weil.om_cont f hf 0
  set μG := νW.restrict 𝓖 with hμG
  set μH := νV.restrict 𝓗 with hμH
  set F : GA D V → GA D W × GA D W → ℂ := fun h p =>
    thetaKO om h p.1 f₁ * star (φ₁ p.1) * (star (thetaKO om h p.2 f₂) * φ₂ p.2) with hF
  have hFc : Continuous (Function.uncurry F) := by
    have a1 : Continuous fun q : GA D V × (GA D W × GA D W) => thetaKO om q.1 q.2.1 f₁ :=
      (hk f₁ hf₁).comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
    have a2 : Continuous fun q : GA D V × (GA D W × GA D W) => thetaKO om q.1 q.2.2 f₂ :=
      (hk f₂ hf₂).comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
    have b1 : Continuous fun q : GA D V × (GA D W × GA D W) => φ₁ q.2.1 :=
      hφ₁.cont.comp (continuous_fst.comp continuous_snd)
    have b2 : Continuous fun q : GA D V × (GA D W × GA D W) => φ₂ q.2.2 :=
      hφ₂.cont.comp (continuous_snd.comp continuous_snd)
    exact (a1.mul b1.star).mul (a2.star.mul b2)
  have hFm : AEStronglyMeasurable (Function.uncurry F) (μH.prod (μG.prod μG)) := hFc.aestronglyMeasurable
  have hI1 : ∀ h, Integrable (fun g => thetaKO om h g f₁ * star (φ₁ g)) μG := by
    intro h
    refine ((hB₁ h).1.norm).mono' (((hk f₁ hf₁).comp (continuous_const.prodMk continuous_id)).mul
      hφ₁.cont.star).aestronglyMeasurable (ae_of_all _ fun g => ?_)
    simp [norm_mul]
  have hI2 : ∀ h, Integrable (fun g => star (thetaKO om h g f₂) * φ₂ g) μG := fun h => (hB₂ h).1
  have hFh : ∀ h, star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h = ∫ p, F h p ∂(μG.prod μG) := by
    intro h
    rw [integral_prod_mul (fun g => thetaKO om h g f₁ * star (φ₁ g)) (fun g => star (thetaKO om h g f₂) * φ₂ g)]
    unfold upLift
    congr 1
    rw [← hμG]
    show (starRingEnd ℂ) _ = _
    rw [← integral_conj]
    congr 1
    funext g
    simp [Complex.star_def]
  have hB₁0 : 0 ≤ B₁ := le_trans (integral_nonneg fun g => by positivity) ((hB₁ 1).2)
  have hB₂0 : 0 ≤ B₂ := le_trans (integral_nonneg fun g => by positivity) ((hB₂ 1).2)
  have hnorm : ∀ h, ∫ p, ‖F h p‖ ∂(μG.prod μG) =
      (∫ g, ‖thetaKO om h g f₁‖ * ‖φ₁ g‖ ∂μG) * ∫ g, ‖thetaKO om h g f₂‖ * ‖φ₂ g‖ ∂μG := by
    intro h
    rw [← integral_prod_mul (fun g => ‖thetaKO om h g f₁‖ * ‖φ₁ g‖) (fun g => ‖thetaKO om h g f₂‖ * ‖φ₂ g‖)]
    congr 1
    funext p
    simp [hF, norm_mul]
  have hInt : Integrable (Function.uncurry F) (μH.prod (μG.prod μG)) := by
    rw [integrable_prod_iff hFm]
    refine ⟨ae_of_all _ fun h => (hI1 h).mul_prod (hI2 h), ?_⟩
    refine (integrable_const (B₁ * B₂)).mono' hFm.norm.integral_prod_right' (ae_of_all _ fun h => ?_)
    simp only [Function.uncurry_apply_pair]
    rw [hnorm h, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul (hB₁ h).2 (hB₂ h).2 (integral_nonneg fun g => by positivity) hB₁0
  have hsplit : ∀ (h : GA D V) (g : GA D W) (f : WO V W → ℂ), thetaKO om h g f = thetaKO om h 1 (om (1, g) f) := by
    intro h g f
    unfold thetaKO
    rw [show ((h, g) : GA D V × GA D W) = (h, 1) * (1, g) by simp, map_mul, Module.End.mul_apply]
  have hup : (fun h => star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h) =
      fun h => ∫ p, F h p ∂(μG.prod μG) := funext hFh
  refine ⟨fun h => (hB₁ h).1, ?_, ?_⟩
  · show Integrable _ μH
    rw [hup]
    exact hInt.integral_prod_left
  · have hpt : ∀ p : GA D W × GA D W, ∫ h, F h p ∂μH = ((νV 𝓗).toReal : ℂ) * (star (φ₁ p.1) * φ₂ p.2 *
        ∑' Y : Lag W, lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂)) := by
      intro p
      have hsw := hSW ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS (om (1, p.1) f₁) (om (1, p.2) f₂)
        (hS.weil.om_pres _ _ hf₁) (hS.weil.om_pres _ _ hf₂)
      have he := hsw.tsum_eq
      rw [← hμH, tsum_mul_left] at he
      have hfun : (fun h => F h p) = fun h => (star (φ₁ p.1) * φ₂ p.2) *
          (thetaKO om h 1 (om (1, p.1) f₁) * star (thetaKO om h 1 (om (1, p.2) f₂))) := by
        funext h
        simp only [hF]
        rw [hsplit h p.1 f₁, hsplit h p.2 f₂]
        ring
      rw [hfun, integral_const_mul, ← he]
      ring
    show ∫ h, star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h ∂μH = _
    rw [hup, integral_integral_swap hInt, ← Measure.prod_restrict, ← hμG, ← integral_const_mul]
    congr 1
    funext p
    rw [hpt p]

end GlobalTheory.RawLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RallisInnerProductKernelIdentityStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rallis_inner_product_kernel_identity : ∀ D : D7, KerAbs D → SWPair D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ → (∀ h, IntegrableOn (fun g => star (thetaKO om h g f₁) * φ₁ g) 𝓖 νW) ∧ IntegrableOn (fun h => star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h) 𝓗 νV ∧ ∫ h in 𝓗, star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h ∂νV = ((νV 𝓗).toReal : ℂ) * ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * ∑' Y : Lag W, lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) := by
  first | exact @GlobalTheory.RawLift.rallis_kernel_step | exact GlobalTheory.RawLift.rallis_kernel_step | (intros; apply GlobalTheory.RawLift.rallis_kernel_step <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousLagTerm
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open Filter
open scoped TensorProduct InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RawLift.TermCont

open GlobalTheory.RawLift

theorem continuous_lagTerm : ∀ D : D7, ∀ ψ (V W : HSp D) χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr,
    SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ →
      ∀ Y : Lag W, Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥ →
        Continuous fun g : GA D W => lagTerm μ 𝓕 (fr Y) (om (1, g) f₁) f₂ := by
  intro D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS f₁ f₂ h₁ h₂ Y _
  have hw := hS.weil
  have hψ := hw.std
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  have : BorelSpace (WO V W) := ⟨rfl⟩
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ h₂
  have hJ := GlobalTheory.ThetaJointCont.continuous_om_oriented hw h₁
  have hrm : ∀ (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E), Continuous fun u : WO V W => ratMul C u := fun C => by
    unfold ratMul
    exact continuous_const.matrix_mul continuous_id
  have hμ1 : μ 𝓕 = 1 := hS.covol.2.2
  have : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (by rw [hμ1]; exact ENNReal.one_ne_top)
  have : SecondCountableTopology (GA D W) := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D W).2.1
  refine continuous_iff_continuousAt.2 fun g₀ => ?_

  have hc0 : Continuous fun w : WO V W => om ((1 : GA D V), g₀) f₁ w :=
    hJ.comp (continuous_const.prodMk continuous_id)
  obtain ⟨κ, hκ⟩ := hK.exists_bound_of_continuousOn hc0.continuousOn
  have hev : ∀ᶠ g in 𝓝 g₀, ∀ w ∈ K, ‖om ((1 : GA D V), g) f₁ w‖ ≤ κ + 1 := by
    refine hK.eventually_forall_of_forall_eventually fun w hw' => ?_
    have hc : Continuous fun y : GA D W × WO V W => ‖om ((1 : GA D V), y.1) f₁ y.2‖ :=
      (hJ.comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)).norm
    exact (hc.continuousAt.eventually_lt continuousAt_const ((hκ w hw').trans_lt (lt_add_one κ))).mono
      fun y hy => hy.le
  have hall : ∀ᶠ g in 𝓝 g₀, ∀ w, ‖om ((1 : GA D V), g) f₁ w‖ ≤ κ + 1 := hev.mono fun g hg w => by
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← GlobalTheory.OrientedHeis.theta_norm_periodic hψ (hw.om_pres _ f₁ h₁) γ hγ w]
    exact hg _ h
  unfold lagTerm
  refine continuousAt_of_dominated (bound := fun _ => (κ + 1) * C₂) ?_ ?_ (integrable_const _) ?_
  · refine Eventually.of_forall fun g => ?_
    exact ((((hw.om_pres _ f₁ h₁).cont.comp (hrm _)).mul
      (continuous_star.comp (h₂.cont.comp (hrm _))))).aestronglyMeasurable
  · refine hall.mono fun g hg => Eventually.of_forall fun u => ?_
    rw [norm_mul, norm_star]
    exact mul_le_mul (hg _) (hC₂ _) (norm_nonneg _) ((norm_nonneg _).trans (hg 0))
  · refine Eventually.of_forall fun u => ?_
    exact ((hw.om_cont f₁ h₁ _).comp (continuous_const.prodMk continuous_id)).continuousAt.mul continuousAt_const

end GlobalTheory.RawLift.TermCont

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LagFrameIsLagFrame
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RawLift

variable {D : D7}

def lagFrame (W : HSp D) (Y : Lag W) :
    Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E :=
  let b := Module.finBasisOfFinrankEq D.host.E Y.1 Y.2.1
  (Matrix.of fun a j => (b j : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)).1 a,
    Matrix.of fun a j => (b j : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)).2 a)

theorem lagFrame_isLagFrame (W : HSp D) (Y : Lag W) : IsLagFrame W Y (lagFrame W Y) := by
  unfold IsLagFrame lagFrame
  have h : (Set.range fun j =>
      ((fun a => (Matrix.of fun a j => ((Module.finBasisOfFinrankEq D.host.E Y.1 Y.2.1) j :
          (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)).1 a) a j),
        (fun a => (Matrix.of fun a j => ((Module.finBasisOfFinrankEq D.host.E Y.1 Y.2.1) j :
          (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)).2 a) a j))) =
      (Y.1.subtype) '' Set.range (Module.finBasisOfFinrankEq D.host.E Y.1 Y.2.1) := by
    rw [← Set.range_comp]
    rfl
  rw [h, Submodule.span_image, Module.Basis.span_eq, Submodule.map_top, Submodule.range_subtype]

end GlobalTheory.RawLift

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RawLift

theorem rallisConv_of_steps : ∀ D : D7, SWPair D → EisAbs D → KerAbs D → TermMove D → TermInv D → CuspKill D → RallisConv D := by
  intro D hSW hEis hKer hMove hInv hKill θ ψ V W χV χW om hθ hω hsig hpos hbig νV 𝓗 νW 𝓖 μ 𝓕 hνV h𝓗 hνW h𝓖
    hμ h𝓕 h1 f₁ f₂ φ₁ φ₂ hf₁ hf₂ hφ₁ hc₁ hφ₂ hc₂
  have hS : SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 (lagFrame W) :=
    { weil := hω, sigOK := hsig, pos := hpos, big := hbig, haarV := hνV, fdV := h𝓗, haarW := hνW, fdW := h𝓖,
      covol := ⟨hμ, h𝓕, h1⟩, frame := lagFrame_isLagFrame W }
  obtain ⟨K1, K2, K3⟩ := GlobalTheory.T.rallis_inner_product_kernel_identity D hKer hSW ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 _ hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂ hφ₁ hc₁
    hφ₂ hc₂
  obtain ⟨-, E2, E3⟩ := GlobalTheory.T.siegelWeilSum_doubleIntegral_exchange_cuspForms D hEis ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 _ hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂ hφ₁ hc₁ hφ₂ hc₂
  obtain ⟨G1, G2⟩ := GlobalTheory.T.lagrangianGraphs_sum_eq_matrixCoeff_integral D hEis hMove ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 _ hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂ hφ₁ hc₁
    hφ₂ hc₂
  have N := GlobalTheory.T.rallis_nonGraphLagrangian_sum_eq_zero_cuspidal D hEis hMove hInv hKill (GlobalTheory.RawLift.TermCont.continuous_lagTerm D) ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 _ hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂
    hφ₁ hc₁ hφ₂ hc₂
  refine ⟨K1, K2, G1, ?_⟩
  rw [K3, E3, ← E2.tsum_subtype_add_tsum_subtype_compl {Y : Lag W | Y.1.comap (LinearMap.inl D.host.E _ _) = ⊥}]
  erw [N, add_zero]
  rw [← G2]
  rfl

end GlobalTheory.RawLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspKillHolds
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.CuspKillProof

theorem cuspKill_holds : ∀ D : D7, CuspKill D := by
  intro D W ν hν s I hI Γ hΓQ hNΓ hnorm 𝓓 h𝓓 Φ φ hΦc hΦΓ hΦN hφ hcusp hint
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D W
  haveI : BorelSpace (GA D W) := ⟨rfl⟩
  haveI : Countable (GQ W) := GlobalTheory.AutomorphicL2Unitary.countable_of_discrete
  haveI : Countable Γ := Function.Injective.countable (Subgroup.inclusion_injective hΓQ)
  have hNc : IsClosed (NI W I : Set (GA D W)) := by
    rw [← GlobalTheory.Cusp.NA_frameFlag hI]
    haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
    exact GlobalTheory.Cusp.IsoFlag.isClosed_unip _ _ _
  have hcc : GlobalTheory.Cusp.Cocompact (GQ W) (NI W I) := by
    rw [← GlobalTheory.Cusp.NA_frameFlag hI]
    exact GlobalTheory.Cusp.cocompact_single _
  haveI : LocallyCompactSpace (NI W I) := hNc.locallyCompactSpace
  have hsub : Γ.subgroupOf (NI W I) = (GQ W).subgroupOf (NI W I) := by
    ext x
    simp only [Subgroup.mem_subgroupOf]
    exact ⟨fun h => hΓQ h, fun h => hNΓ ⟨x.2, h⟩⟩
  set κ : Measure (NI W I) := Measure.haar
  set 𝓝 : Set (NI W I) := GlobalTheory.AutomorphicL2Unitary.stdDom ((GQ W).subgroupOf (NI W I))
  have h𝓝Q : IsFundamentalDomain ((GQ W).subgroupOf (NI W I)) 𝓝 κ := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ κ
  have h𝓝Γ : IsFundamentalDomain (Γ.subgroupOf (NI W I)) 𝓝 κ := by rw [hsub]; exact h𝓝Q
  have h𝓝t : κ 𝓝 ≠ ⊤ := hcc.measure_ne_top h𝓝Q
  have h0 : ∀ g, ∫ n in 𝓝, φ ((n : GA D W) * g) ∂κ = 0 := hcusp s I hI κ 𝓝 inferInstance h𝓝Q
  exact GlobalTheory.UnfoldNormal.unfold_zero_mean (GA D W) ν Γ (NI W I) inferInstance hNc hnorm κ 𝓝 inferInstance h𝓝Γ h𝓝t
    Φ φ hΦc.measurable hφ.cont.measurable hΦN hΦΓ (fun γ hγ g => hφ.left γ (hΓQ hγ) g) h0 𝓓 h𝓓 hint

end GlobalTheory.CuspKillProof
end

open Formalism.BasicNotions

namespace GlobalTheory.RawLift.Assembled

theorem rallisConv_of_siegelWeil : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary →
    ∀ D : D7, GlobalTheory.RawLift.RallisConv D :=
  fun hP hW D => GlobalTheory.RawLift.rallisConv_of_steps D (GlobalTheory.SWPairProof.swPair hW D) (GlobalTheory.EisAbsPf.eisAbs hP D)
    (GlobalTheory.RawLift.kerAbs_of_cuspRapidDecay hP D) (GlobalTheory.RawLift.Move.termMove D) (GlobalTheory.TermInvProof.termInv D)
    (GlobalTheory.CuspKillProof.cuspKill_holds D)

end GlobalTheory.RawLift.Assembled
