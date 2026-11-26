module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupActionPreservesPrincipalFlagMultiplic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MixedLaplacianKillsProductOfMinors
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodFormsEqKilledByGroupAlgebra

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TotallyIsotropicDimBoundsOddRank
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TotallyIsotropicDimBoundsOddRank
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
open MeasureTheory IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Orb
open GlobalTheory.AutomorphicL2Unitary (starFn)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH)
open GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoDim

theorem finrank_perp_add {E : Type} [Field E] [NumberField E] [StarRing E] (V : HSpace E)
    (W : Submodule E V.V) :
    Module.finrank E (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V W) + Module.finrank E W = V.rank := by
  classical
  set a := Module.finrank E W
  let b := Module.finBasis E W
  let ψ : V.V →ₗ[E] (Fin a → E) := LinearMap.pi fun i => V.hT (b i : V.V)
  have hker : LinearMap.ker ψ = GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V W := by
    ext y
    simp only [LinearMap.mem_ker, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp, Submodule.mem_iInf]
    constructor
    · intro h w hw
      have e := congrArg (fun v : Fin a → E => v) h
      have hw' : (⟨w, hw⟩ : W) = ∑ i, (b.repr ⟨w, hw⟩ i) • b i := (b.sum_repr _).symm
      have : w = ∑ i, (b.repr ⟨w, hw⟩ i) • (b i : V.V) := by
        have := congrArg Subtype.val hw'
        rw [Submodule.coe_sum] at this
        simp only [Submodule.coe_smul] at this
        exact this
      set_option synthInstance.maxHeartbeats 100000 in
        rw [this, map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply]
      have := congrFun h i
      simp only [ψ, LinearMap.pi_apply, Pi.zero_apply] at this
      rw [this, smul_zero]
    · intro h
      funext i
      simpa [ψ] using h (b i) (b i).2
  have hsurj : LinearMap.range ψ = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
    let c : Fin a → E := fun i => f (Pi.single i 1)
    have hfc : ∀ v : Fin a → E, f v = ∑ i, v i * c i := by
      intro v
      rw [LinearMap.pi_apply_eq_sum_univ f v]
      simp only [smul_eq_mul, c]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 2
      funext j
      simp [Pi.single_apply, eq_comm]
    have hy : ∀ y, V.hT (∑ i, (star (c i)) • (b i : V.V)) y = 0 := by
      intro y
      have h1 : f (ψ y) = 0 := by
        have : f (ψ y) ∈ (LinearMap.range ψ).map f := ⟨ψ y, ⟨y, rfl⟩, rfl⟩
        rw [hf] at this
        exact (Submodule.mem_bot E).1 this
      rw [hfc] at h1
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, LinearMap.sum_apply]
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
      simp [ψ, mul_comm]
    have hx := V.nondeg.1 _ hy
    have hli : LinearIndependent E (fun i => (b i : V.V)) :=
      b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
    have hc : ∀ i, star (c i) = 0 := by
      have := (Fintype.linearIndependent_iff.1 hli) (fun i => star (c i)) hx
      exact this
    apply hf0
    apply LinearMap.ext
    intro v
    rw [hfc]
    simp [fun i => star_eq_zero.1 (hc i)]
  have hrn := LinearMap.finrank_range_add_finrank_ker ψ
  rw [hsurj, hker, finrank_top, Module.finrank_fin_fun, V.rank_eq] at hrn
  omega

end GlobalTheory.IsoDim

theorem GlobalTheory.IsoDim.isotropic_dim_bounds : ∀ (D : D7) (V : HSp D), Odd V.rank → ∀ W : Submodule D.host.E V.V, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V W →
    0 < Module.finrank D.host.E W ∧ 2 * Module.finrank D.host.E W + 1 ≤ V.rank := by
  intro D V hodd W hW
  have h := GlobalTheory.IsoDim.finrank_perp_add V W
  have hle : Module.finrank D.host.E W ≤ Module.finrank D.host.E (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V W) :=
    Submodule.finrank_mono hW.2
  have hpos : 0 < Module.finrank D.host.E W :=
    Nat.pos_of_ne_zero fun h0 => hW.1 (Submodule.finrank_eq_zero.1 h0)
  obtain ⟨k, hk⟩ := hodd
  refine ⟨hpos, ?_⟩
  omega
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TotallyIsotropicDimBoundsOddRankStatement
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
open MeasureTheory IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Orb
open GlobalTheory.AutomorphicL2Unitary (starFn)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH)
open GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totallyIsotropic_dim_bounds_oddRank : ∀ (D : D7) (V : HSp D), Odd V.rank → ∀ W : Submodule D.host.E V.V, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V W →
    0 < Module.finrank D.host.E W ∧ 2 * Module.finrank D.host.E W + 1 ≤ V.rank := by
  first | exact @GlobalTheory.IsoDim.isotropic_dim_bounds | exact GlobalTheory.IsoDim.isotropic_dim_bounds | (intros; apply GlobalTheory.IsoDim.isotropic_dim_bounds <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexDerivativeRightDerivativeCommutator
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexDerivativeRightDerivativeCommutator
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DerBracket

open GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem bracket_mem_lieAt {τ : D.what₂.Tau} {X Y : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (hY : Y ∈ lieAt V τ) : X * Y - Y * X ∈ lieAt V τ := by

  have hX0 : Xᴴ * gramAt D V τ + gramAt D V τ * X = 0 := hX
  have hY0 : Yᴴ * gramAt D V τ + gramAt D V τ * Y = 0 := hY
  have hX' : Xᴴ * gramAt D V τ = -(gramAt D V τ * X) := eq_neg_of_add_eq_zero_left hX0
  have hY' : Yᴴ * gramAt D V τ = -(gramAt D V τ * Y) := eq_neg_of_add_eq_zero_left hY0
  have e1 : Yᴴ * Xᴴ * gramAt D V τ = gramAt D V τ * Y * X := by
    rw [Matrix.mul_assoc Yᴴ Xᴴ, hX', Matrix.mul_neg, ← Matrix.mul_assoc Yᴴ, hY', Matrix.neg_mul, neg_neg]
  have e2 : Xᴴ * Yᴴ * gramAt D V τ = gramAt D V τ * X * Y := by
    rw [Matrix.mul_assoc Xᴴ Yᴴ, hY', Matrix.mul_neg, ← Matrix.mul_assoc Xᴴ, hX', Matrix.neg_mul, neg_neg]
  show (X * Y - Y * X)ᴴ * gramAt D V τ + gramAt D V τ * (X * Y - Y * X) = 0
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Matrix.sub_mul, e1, e2]
  noncomm_ring

private theorem mem_smF_of_mem_smFun (R : GlobalTheory.SmoothForms.RealPoints θ V) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) :
    φ ∈ GlobalTheory.SmoothForms.SmF θ V :=
  (GlobalTheory.SmoothForms.isSmoothInf_iff φ).1 ((GlobalTheory.SmoothForms.smooth_iff R φ).1 hφ)

private theorem rder_eq_opInf_atPlace (R : GlobalTheory.SmoothForms.RealPoints θ V) (τ : D.what₂.Tau) (X : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ)
    (ψ : GlobalTheory.SmoothForms.SmF θ V) :
    Rder θ V τ X.1 ψ.1 = (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ X) ψ).1 := by
  rw [GlobalTheory.SmoothForms.opInf_coe]
  exact GlobalTheory.SmoothForms.Rder_eq R τ X ψ.1

theorem Rder_bracket (hθ : IsInfFam θ) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) {τ : D.what₂.Tau}
    {X Y : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (hY : Y ∈ lieAt V τ) :
    Rder θ V τ X (Rder θ V τ Y φ) = Rder θ V τ Y (Rder θ V τ X φ) + Rder θ V τ (X * Y - Y * X) φ := by

  have R : GlobalTheory.SmoothForms.RealPoints θ V := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  have hXY := bracket_mem_lieAt hX hY
  set ψ : GlobalTheory.SmoothForms.SmF θ V := ⟨φ, mem_smF_of_mem_smFun R hφ⟩ with hψ
  set Xl : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ := ⟨X, (GlobalTheory.SmoothForms.mem_lieAt_iff τ X).1 hX⟩ with hXl
  set Yl : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ := ⟨Y, (GlobalTheory.SmoothForms.mem_lieAt_iff τ Y).1 hY⟩ with hYl
  set Zl : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ := ⟨X * Y - Y * X, (GlobalTheory.SmoothForms.mem_lieAt_iff τ _).1 hXY⟩ with hZl
  have e := GlobalTheory.SmoothForms.opAt_bracket R τ Xl Yl Zl rfl
  have a1 : Rder θ V τ Y φ = (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Yl) ψ).1 := rder_eq_opInf_atPlace R τ Yl ψ
  have a2 : Rder θ V τ X φ = (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl) ψ).1 := rder_eq_opInf_atPlace R τ Xl ψ
  have a3 : Rder θ V τ X (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Yl) ψ).1 =
      (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl)
        (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Yl) ψ)).1 := rder_eq_opInf_atPlace R τ Xl _
  have a4 : Rder θ V τ Y (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl) ψ).1 =
      (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Yl)
        (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl) ψ)).1 := rder_eq_opInf_atPlace R τ Yl _
  have a5 : Rder θ V τ (X * Y - Y * X) φ = (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Zl) ψ).1 :=
    rder_eq_opInf_atPlace R τ Zl ψ
  rw [a1, a3, a2, a4, a5, e, LinearMap.sub_apply, Submodule.coe_sub]
  change _ = _ + ((GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl)
        (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Yl) ψ)).1 -
      (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Yl)
        (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl) ψ)).1)
  abel

theorem Rder_comm (hθ : IsInfFam θ) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) {τ τ' : D.what₂.Tau} (hτ : τ ≠ τ')
    {X Y : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (hY : Y ∈ lieAt V τ') :
    Rder θ V τ X (Rder θ V τ' Y φ) = Rder θ V τ' Y (Rder θ V τ X φ) := by

  have R : GlobalTheory.SmoothForms.RealPoints θ V := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  set ψ : GlobalTheory.SmoothForms.SmF θ V := ⟨φ, mem_smF_of_mem_smFun R hφ⟩ with hψ
  set Xl : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ := ⟨X, (GlobalTheory.SmoothForms.mem_lieAt_iff τ X).1 hX⟩ with hXl
  set Yl : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ' := ⟨Y, (GlobalTheory.SmoothForms.mem_lieAt_iff τ' Y).1 hY⟩ with hYl
  have hc := (GlobalTheory.SmoothForms.opAt_comm R hτ Xl Yl).eq
  have a1 : Rder θ V τ' Y φ = (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ' Yl) ψ).1 := rder_eq_opInf_atPlace R τ' Yl ψ
  have a2 : Rder θ V τ X φ = (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl) ψ).1 := rder_eq_opInf_atPlace R τ Xl ψ
  rw [a1, a2, rder_eq_opInf_atPlace R τ Xl, rder_eq_opInf_atPlace R τ' Yl]
  exact congrArg Subtype.val (LinearMap.congr_fun hc ψ)

private theorem commutator_add_I_smul' {n : ℕ} (A B X : Matrix (Fin n) (Fin n) ℂ) :
    (A + Complex.I • B) * X - X * (A + Complex.I • B) = (A * X - X * A) + Complex.I • (B * X - X * B) := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_sub]
  abel

theorem RderC_Rder : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ τ' : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ), ∀ X ∈ lieAt V τ, ∀ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, (RderC θ V τ Z (Rder θ V τ X φ) = Rder θ V τ X (RderC θ V τ Z φ) + RderC θ V τ (Z * X - X * Z) φ) ∧ (τ' ≠ τ → RderC θ V τ' Z (Rder θ V τ X φ) = Rder θ V τ X (RderC θ V τ' Z φ)) := by
  intro D θ hθ V τ τ' Z X hX φ hφ
  constructor
  ·
    obtain ⟨hA, hB⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
    have hZ := GlobalTheory.SmoothAutCheck.parts_sum V τ Z
    set A := (1 / 2 : ℂ) • (Z + conjAt V τ Z) with hAdef
    set B := (1 / (2 * Complex.I)) • (Z - conjAt V τ Z) with hBdef
    have hc := commutator_add_I_smul' A B X
    rw [hZ] at hc
    have hAX := bracket_mem_lieAt hA hX
    have hBX := bracket_mem_lieAt hB hX
    have e1 : RderC θ V τ (Z * X - X * Z) φ =
        Rder θ V τ (A * X - X * A) φ + Complex.I • Rder θ V τ (B * X - X * B) φ := by
      rw [hc, GlobalTheory.Mem.RealTranslate.RderC_add hθ hφ, GlobalTheory.Mem.RealTranslate.RderC_smul hθ hφ,
        GlobalTheory.SmoothAutCheck.RderC_eq θ V τ hAX, GlobalTheory.SmoothAutCheck.RderC_eq θ V τ hBX]
    rw [e1]
    show Rder θ V τ A (Rder θ V τ X φ) + Complex.I • Rder θ V τ B (Rder θ V τ X φ) =
      Rder θ V τ X (Rder θ V τ A φ + Complex.I • Rder θ V τ B φ) + _
    rw [Rder_bracket hθ hφ hA hX, Rder_bracket hθ hφ hB hX,
      Rder_add (Rder_mem hφ hA) ((SmFun θ V).smul_mem _ (Rder_mem hφ hB)) hX, Rder_smul]
    rw [smul_add]
    abel
  ·
    intro hne
    obtain ⟨hA, hB⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ' Z
    show Rder θ V τ' ((1 / 2 : ℂ) • (Z + conjAt V τ' Z)) (Rder θ V τ X φ) +
        Complex.I • Rder θ V τ' ((1 / (2 * Complex.I)) • (Z - conjAt V τ' Z)) (Rder θ V τ X φ) =
      Rder θ V τ X (Rder θ V τ' ((1 / 2 : ℂ) • (Z + conjAt V τ' Z)) φ +
        Complex.I • Rder θ V τ' ((1 / (2 * Complex.I)) • (Z - conjAt V τ' Z)) φ)
    rw [Rder_add (Rder_mem hφ hA) ((SmFun θ V).smul_mem _ (Rder_mem hφ hB)) hX, Rder_smul,
      Rder_comm hθ hφ hne hA hX, Rder_comm hθ hφ hne hB hX]

end GlobalTheory.DerBracket

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexDerivativeRightDerivativeCommutatorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexDerivative_rightDerivative_commutator : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ τ' : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ), ∀ X ∈ lieAt V τ, ∀ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, (RderC θ V τ Z (Rder θ V τ X φ) = Rder θ V τ X (RderC θ V τ Z φ) + RderC θ V τ (Z * X - X * Z) φ) ∧ (τ' ≠ τ → RderC θ V τ' Z (Rder θ V τ X φ) = Rder θ V τ X (RderC θ V τ' Z φ)) := by
  first | exact @GlobalTheory.DerBracket.RderC_Rder | exact GlobalTheory.DerBracket.RderC_Rder | (intros; apply GlobalTheory.DerBracket.RderC_Rder <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalFrameStabiliserNormalisesUnipotentRadica
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalFrameStabiliserNormalisesUnipotentRadica
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FrameStab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem incA_injective (D : D7) : Function.Injective (incA D) :=
  Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)

theorem mt_mul (W : HSp D) (g h : GA D W) : Formalism.L2.Theta.mt W (g * h) = Formalism.L2.Theta.mt W g * Formalism.L2.Theta.mt W h := by
  simp [Formalism.L2.Theta.mt]

theorem mt_inv_mul (W : HSp D) (g : GA D W) : Formalism.L2.Theta.mt W g⁻¹ * Formalism.L2.Theta.mt W g = 1 := by
  rw [← mt_mul]; simp [Formalism.L2.Theta.mt]

theorem mt_mul_inv (W : HSp D) (g : GA D W) : Formalism.L2.Theta.mt W g * Formalism.L2.Theta.mt W g⁻¹ = 1 := by
  rw [← mt_mul]; simp [Formalism.L2.Theta.mt]

theorem mt_mul_frame (W : HSp D) {s : ℕ} (L : Matrix (Fin W.rank) (Fin s) D.host.E) (n : GA D W) (hn : n ∈ NI W L) :
    Formalism.L2.Theta.mt W n * L.map (incA D) = L.map (incA D) := by
  induction hn using Subgroup.closure_induction with
  | mem g hg =>
    have h1 : (Formalism.L2.Theta.mt W g - 1) * L.map (incA D) = 0 := hg.1
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
    exact h1
  | one => simp [Formalism.L2.Theta.mt]
  | mul x y _ _ hx hy => rw [mt_mul, Matrix.mul_assoc, hy, hx]
  | inv x _ hx =>
    calc Formalism.L2.Theta.mt W x⁻¹ * L.map (incA D)
        = Formalism.L2.Theta.mt W x⁻¹ * (Formalism.L2.Theta.mt W x * L.map (incA D)) := by rw [hx]
      _ = L.map (incA D) := by rw [← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]

theorem mt_conj_sub_one (W : HSp D) (γ m : GA D W) : Formalism.L2.Theta.mt W (γ * m * γ⁻¹) - 1 =
    Formalism.L2.Theta.mt W γ * (Formalism.L2.Theta.mt W m - 1) * Formalism.L2.Theta.mt W γ⁻¹ := by
  rw [mt_mul, mt_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, mt_mul_inv]

theorem conj_sub_one_kills_frame_of_fixed (W : HSp D) {s : ℕ} (L : Matrix (Fin W.rank) (Fin s) D.host.E) (γ m : GA D W)
    (hΓiL : Formalism.L2.Theta.mt W γ⁻¹ * L.map (incA D) = L.map (incA D))
    (h1 : (Formalism.L2.Theta.mt W m - 1) * L.map (incA D) = 0) :
    (Formalism.L2.Theta.mt W (γ * m * γ⁻¹) - 1) * L.map (incA D) = 0 := by
  rw [mt_conj_sub_one, Matrix.mul_assoc, hΓiL, Matrix.mul_assoc, h1, Matrix.mul_zero]

theorem rowFrame_mul_conj_sub_one_eq_zero_of_fixed (W : HSp D) {s : ℕ} (P : Matrix (Fin s) (Fin W.rank) D.host.E) (γ m : GA D W)
    (hPΓ : P.map (incA D) * Formalism.L2.Theta.mt W γ = P.map (incA D))
    (h2 : P.map (incA D) * (Formalism.L2.Theta.mt W m - 1) = 0) :
    P.map (incA D) * (Formalism.L2.Theta.mt W (γ * m * γ⁻¹) - 1) = 0 := by
  rw [mt_conj_sub_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPΓ, h2, Matrix.zero_mul]

theorem conj_unipotentRadical_kernelCondition_of_rationalFixed (W : HSp D) {s : ℕ} (L : Matrix (Fin W.rank) (Fin s) D.host.E) (P : Matrix (Fin s) (Fin W.rank) D.host.E)
    (γ m : GA D W) (γ₀ γi : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    (hγ₀ : Formalism.L2.Theta.mt W γ = γ₀.map (incA D)) (hγγi : γ₀ * γi = 1) (hPγi : P * γi = P)
    (hΓL : Formalism.L2.Theta.mt W γ * L.map (incA D) = L.map (incA D))
    (h3 : ∀ x : Fin W.rank → D.host.E, P *ᵥ x = 0 → ∃ a : Fin s → AE D,
        (Formalism.L2.Theta.mt W m - 1) *ᵥ (fun i => incA D (x i)) = L.map (incA D) *ᵥ a)
    (x : Fin W.rank → D.host.E) (hx : P *ᵥ x = 0) : ∃ a : Fin s → AE D,
        (Formalism.L2.Theta.mt W (γ * m * γ⁻¹) - 1) *ᵥ (fun i => incA D (x i)) = L.map (incA D) *ᵥ a := by
  have hy : P *ᵥ (γi *ᵥ x) = 0 := by
    rw [Matrix.mulVec_mulVec, hPγi]; exact hx
  obtain ⟨a, ha⟩ := h3 _ hy
  refine ⟨a, ?_⟩
  have hyb : (fun i => incA D ((γi *ᵥ x) i)) = γi.map (incA D) *ᵥ (fun i => incA D (x i)) := by
    funext i; exact RingHom.map_mulVec (incA D) γi x i
  have hxb : Formalism.L2.Theta.mt W γ *ᵥ (fun i => incA D ((γi *ᵥ x) i)) = fun i => incA D (x i) := by
    rw [hyb, Matrix.mulVec_mulVec, hγ₀, ← Matrix.map_mul, hγγi, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.one_mulVec]
  have hxi : Formalism.L2.Theta.mt W γ⁻¹ *ᵥ (fun i => incA D (x i)) = fun i => incA D ((γi *ᵥ x) i) := by
    rw [← hxb, Matrix.mulVec_mulVec, mt_inv_mul, Matrix.one_mulVec]
  rw [mt_conj_sub_one, ← Matrix.mulVec_mulVec, hxi, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_mulVec, hΓL]

theorem stab : ∀ (D : D7) (W : HSp D) (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W L →
    (∀ γ ∈ GQ W, ∀ γ₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E, Formalism.L2.Theta.mt W γ = γ₀.map (incA D) →
      γ₀ * L = L → ∀ n ∈ NI W L, γ * n * γ⁻¹ ∈ NI W L) ∧
    (∀ n ∈ NI W L, ∀ n₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E, Formalism.L2.Theta.mt W n = n₀.map (incA D) →
      n₀ * L = L) := by
  intro D W s L _
  refine ⟨?_, fun n hn n₀ hn₀ => ?_⟩
  swap
  · apply Matrix.map_injective (incA_injective D)
    show (n₀ * L).map (incA D) = L.map (incA D)
    rw [Matrix.map_mul, ← hn₀]
    exact mt_mul_frame W L n hn
  intro γ hγ γ₀ hγ₀ hL
  obtain ⟨g, hg, e⟩ := hγ
  have hg0 : (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) = γ₀ := by
    apply Matrix.map_injective (incA_injective D)
    show (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D) = γ₀.map (incA D)
    rw [← hγ₀]
    exact congrArg Units.val e

  obtain ⟨σ, hσ⟩ : ∃ σ : D.host.E →+* D.host.E, σ = (D.sp.cm.sig : D.host.E →+* D.host.E) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = W.gram := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin s) (Fin W.rank) D.host.E, P = Formalism.UG.cT σ L * G := ⟨_, rfl⟩
  obtain ⟨γi, hγi⟩ : ∃ γi : Matrix (Fin W.rank) (Fin W.rank) D.host.E, γi = (g⁻¹ : GL (Fin W.rank) D.host.E).1 :=
    ⟨_, rfl⟩
  have hγγi : γ₀ * γi = 1 := by rw [← hg0, hγi]; exact Units.mul_inv g
  have hU : Formalism.UG.cT σ γ₀ * G * γ₀ = G := by rw [← hg0, hσ, hG]; exact hg
  have hPγ : P * γ₀ = P := by
    calc P * γ₀ = Formalism.UG.cT σ (γ₀ * L) * G * γ₀ := by rw [hL, hP]
      _ = Formalism.UG.cT σ L * (Formalism.UG.cT σ γ₀ * G * γ₀) := by
        rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = P := by rw [hU, hP]
  have hPγi : P * γi = P := by
    calc P * γi = P * γ₀ * γi := by rw [hPγ]
      _ = P := by rw [Matrix.mul_assoc, hγγi, Matrix.mul_one]

  have hΓL : Formalism.L2.Theta.mt W γ * L.map (incA D) = L.map (incA D) := by
    rw [hγ₀, ← Matrix.map_mul, hL]
  have hΓiL : Formalism.L2.Theta.mt W γ⁻¹ * L.map (incA D) = L.map (incA D) := by
    calc Formalism.L2.Theta.mt W γ⁻¹ * L.map (incA D)
        = Formalism.L2.Theta.mt W γ⁻¹ * (Formalism.L2.Theta.mt W γ * L.map (incA D)) := by rw [hΓL]
      _ = L.map (incA D) := by rw [← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
  have hPΓ : P.map (incA D) * Formalism.L2.Theta.mt W γ = P.map (incA D) := by
    rw [hγ₀, ← Matrix.map_mul, hPγ]
  have hPΓi : P.map (incA D) * Formalism.L2.Theta.mt W γ⁻¹ = P.map (incA D) := by
    calc P.map (incA D) * Formalism.L2.Theta.mt W γ⁻¹
        = P.map (incA D) * Formalism.L2.Theta.mt W γ * Formalism.L2.Theta.mt W γ⁻¹ := by rw [hPΓ]
      _ = P.map (incA D) := by rw [Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one]

  have key : NI W L ≤ (NI W L).comap (MulAut.conj γ).toMonoidHom := by
    refine (Subgroup.closure_le _).2 fun m hm => ?_
    have h1 : (Formalism.L2.Theta.mt W m - 1) * L.map (incA D) = 0 := hm.1
    have h2 : P.map (incA D) * (Formalism.L2.Theta.mt W m - 1) = 0 := by
      have := hm.2.1
      rw [hP, hσ, hG]; exact this
    have h3 : ∀ x : Fin W.rank → D.host.E, P *ᵥ x = 0 → ∃ a : Fin s → AE D,
        (Formalism.L2.Theta.mt W m - 1) *ᵥ (fun i => incA D (x i)) = L.map (incA D) *ᵥ a := by
      rw [hP, hσ, hG]; exact hm.2.2
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine Subgroup.subset_closure ⟨conj_sub_one_kills_frame_of_fixed W L γ m hΓiL h1, ?_, ?_⟩
    · have := rowFrame_mul_conj_sub_one_eq_zero_of_fixed W P γ m hPΓ h2
      rw [hP, hσ, hG] at this; exact this
    · intro x hx
      rw [← hG, ← hσ, ← hP] at hx
      exact conj_unipotentRadical_kernelCondition_of_rationalFixed W L P γ m γ₀ γi hγ₀ hγγi hPγi hΓL h3 x hx
  intro n hn
  exact key hn

end GlobalTheory.FrameStab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalFrameStabiliserNormalisesUnipotentRadicaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalFrameStabiliser_normalises_unipotentRadical : ∀ (D : D7) (W : HSp D) (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W L → (∀ γ ∈ GQ W, ∀ γ₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E, Formalism.L2.Theta.mt W γ = γ₀.map (incA D) → γ₀ * L = L → ∀ n ∈ NI W L, γ * n * γ⁻¹ ∈ NI W L) ∧ (∀ n ∈ NI W L, ∀ n₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E, Formalism.L2.Theta.mt W n = n₀.map (incA D) → n₀ * L = L) := by
  first | exact @GlobalTheory.FrameStab.stab | exact GlobalTheory.FrameStab.stab | (intros; apply GlobalTheory.FrameStab.stab <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionIsotropicRestrictionNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionIsotropicRestrictionNeZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TowerResNonzero

variable {D : D7}

theorem exists_right_inv {V : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    (hC : LinearIndependent D.host.E C.transpose) :
    ∃ N : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * N = 1 := by
  set P := adj D C * V.gram with hP
  have hinj : Function.Injective (Matrix.toLin' Pᵀ) := by
    refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    rw [Matrix.toLin'_apply] at ha
    rw [Matrix.mulVec_transpose, hP, ← Matrix.vecMul_vecMul] at ha
    have hG := GlobalTheory.LatVac.gram_det_isUnit V
    have h1 : a ᵥ* adj D C = 0 := by
      have := congrArg (fun v => v ᵥ* V.gram⁻¹) ha
      simp only [Matrix.vecMul_vecMul, Matrix.zero_vecMul] at this
      rwa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.mul_one] at this
    have h2 : C *ᵥ star a = 0 := by
      have e : a ᵥ* adj D C = star (C *ᵥ star a) := by
        rw [Matrix.star_mulVec, star_star]; rfl
      rw [e] at h1
      exact star_eq_zero.1 h1
    have h3 : star a = 0 := by
      funext j
      refine Fintype.linearIndependent_iff.1 hC (star a) ?_ j
      funext i
      have := congrFun h2 i
      simp only [Matrix.mulVec, dotProduct] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.transpose_apply, Pi.zero_apply] at this ⊢
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    exact star_eq_zero.1 h3
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' Pᵀ) (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨(LinearMap.toMatrix' g)ᵀ, ?_⟩
  have e : LinearMap.toMatrix' g * Pᵀ = 1 := by
    have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  have := congrArg Matrix.transpose e
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this

theorem lattice_ratMx (D : D7) (m n : ℕ) : IsTopologicalAddGroup (Mx D m n) ∧ LocallyCompactSpace (Mx D m n) ∧
    SecondCountableTopology (Mx D m n) ∧ T2Space (Mx D m n) ∧ DiscreteTopology (ratMx D m n) ∧
    ∃ K : Set (Mx D m n), IsCompact K ∧ ∀ x : Mx D m n, ∃ γ ∈ ratMx D m n, γ + x ∈ K :=
  GlobalTheory.AdelicMatrixLattice.lattice D (Examples₂.posSpace Examples₂.star_isIntegral m) (Examples₂.posSpace Examples₂.star_isIntegral n)

theorem isoPart_add' {V W : HSp D} {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (y y' : Mx D W.rank r) :
    isoPart V W C (y + y') = isoPart V W C y + isoPart V W C y' :=
  Matrix.add_mul _ _ _

theorem isoPart_zero' {V W : HSp D} {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) :
    isoPart V W C (0 : Mx D W.rank r) = 0 := Matrix.zero_mul _

theorem midPart_zero' {V V' W : HSp D} (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) :
    midPart V V' W B (0 : WO V' W) = 0 := Matrix.zero_mul _

theorem isoPart_mem_iff {V W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    (hC : LinearIndependent D.host.E C.transpose) (y : Mx D W.rank r) :
    isoPart V W C y ∈ ratL W V ↔ y ∈ ratMx D W.rank r := by
  constructor
  · rintro ⟨Q, hQ⟩
    obtain ⟨N, hN⟩ := exists_right_inv (V := V) hC
    refine ⟨Q * N, ?_⟩
    change (Q * N).map (incA D) = y
    have hQ' : Q.map (incA D) = y * (adj D C * V.gram).map (incA D) := hQ
    rw [Matrix.map_mul, hQ', Matrix.mul_assoc, ← Matrix.map_mul, hN, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.mul_one]
  · rintro ⟨γ₀, rfl⟩
    exact ⟨γ₀ * (adj D C * V.gram), by
      show (γ₀ * (adj D C * V.gram)).map (incA D) = _
      rw [Matrix.map_mul]; rfl⟩

theorem exists_res_ne_zero : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → (∀ (y y' : Mx D W.rank r) (x x' : WO V' W), symplOH V W (isoPart V W C y + midPart V V' W B x) (isoPart V W C y' + midPart V V' W B x') = symplOH V' W x x') → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ f, IsThetaFunO ψ V W f ∧ res V V' W C B μ 𝓨 f ≠ 0 := by
  intro D V V' W r C B hs hF ψ hψ μ 𝓨 h
  obtain ⟨f₀, hf₀, hne₀⟩ := GlobalTheory.Mem.ThetaNonzero.exists_thetaO_ne_zero hψ V W
  obtain ⟨x₀, hx₀⟩ : ∃ x, f₀ x ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hne₀ (funext hc)
  have hf₁ : IsThetaFunO ψ V W (heisO ψ V W x₀ f₀) := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf₀ x₀
  have h0 : heisO ψ V W x₀ f₀ 0 ≠ 0 := by
    simp only [heisO, zero_add, GlobalTheory.FinTranslate.symplOH_zero_left, AddChar.map_zero_eq_one, one_mul]
    exact hx₀

  have hiso : ∀ y y' : Mx D W.rank r, symplOH V W (isoPart V W C y) (isoPart V W C y') = 0 := fun y y' => by
    have := hF y y' 0 0
    rwa [midPart_zero', add_zero, add_zero, GlobalTheory.FinTranslate.symplOH_zero_left] at this

  have hc : ∀ (g : WO V W → ℂ), IsThetaFunO ψ V W g → ∀ a ∈ ratL W V, ∀ z,
      heisO ψ V W a g z = ψ (symplO V W z a) * g z := by
    intro g hg a ha z
    have := GlobalTheory.ThetaCoefficient.char_mul_heisO hg ha 0 z
    simp only [heisO, GlobalTheory.FinTranslate.symplOH_zero_right, add_zero, AddChar.map_zero_eq_one, one_mul] at this
    exact this.symm
  refine by_contra fun hall => ?_
  push_neg at hall
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := lattice_ratMx D W.rank r
  have : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  have hcont : Continuous (isoPart V W C : Mx D W.rank r → WO V W) := continuous_id.matrix_mul continuous_const
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (Mx D W.rank r) (ratMx D W.rank r) K hK hKc
    (ratL W V) (fun a y => ψ (symplO V W (isoPart V W C y) a))
    (fun a => by
      simp only [GlobalTheory.ThetaCoefficient.symplO_eq]
      exact hψ.1.1.comp (((GlobalTheory.FinTranslate.continuous_symplOH V W _).comp hcont).add
        ((GlobalTheory.FinTranslate.continuous_symplOH V W _).comp hcont)))
    (fun a x y => by
      simp only [isoPart_add', GlobalTheory.ThetaCoefficient.symplO_eq, GlobalTheory.FinTranslate.symplOH_add_left,
        ← AddChar.map_add_eq_mul]
      rw [add_add_add_comm])
    (fun a b x => by
      show ψ (symplO V W (isoPart V W C x) (a + b)) = _
      simp only [GlobalTheory.ThetaCoefficient.symplO_eq, GlobalTheory.FinTranslate.symplOH_add_right, ← AddChar.map_add_eq_mul]
      rw [add_add_add_comm])
    (fun x => by
      show ψ (symplO V W (isoPart V W C x) 0) = 1
      rw [GlobalTheory.ThetaCoefficient.symplO_eq, GlobalTheory.FinTranslate.symplOH_zero_right, add_zero, AddChar.map_zero_eq_one])
    (fun a x => hψ.1.2.1 _)
    (fun y => by
      rw [← isoPart_mem_iff hs.frame.2.1 y, ← GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ V W]
      exact Subtype.forall)
    μ 𝓨 h.1 h.2.1 (fun y => heisO ψ V W x₀ f₀ (isoPart V W C y)) (hf₁.cont.comp hcont)
    (fun γ hγ y => by
      obtain ⟨γ₀, hγ₀⟩ := (isoPart_mem_iff (V := V) hs.frame.2.1 γ).2 hγ
      have e := hf₁.quasi γ₀ (isoPart V W C y)
      change ratW W V γ₀ = isoPart V W C γ at hγ₀
      rw [hγ₀, hiso, neg_zero, AddChar.map_zero_eq_one, one_mul] at e
      simp only [isoPart_add']
      exact e)
    (fun a => by
      have e := congrFun (hall _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf₁ (a : WO V W))) 0
      simp only [res, midPart_zero', add_zero, Pi.zero_apply] at e
      rw [← e]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => (hc _ hf₁ a a.2 _).symm))
  have := congrFun key 0
  simp only [isoPart_zero', Pi.zero_apply] at this
  exact h0 this

end GlobalTheory.TowerResNonzero

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionIsotropicRestrictionNeZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaFunction_isotropicRestriction_ne_zero : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → (∀ (y y' : Mx D W.rank r) (x x' : WO V' W), symplOH V W (isoPart V W C y + midPart V V' W B x) (isoPart V W C y' + midPart V V' W B x') = symplOH V' W x x') → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ f, IsThetaFunO ψ V W f ∧ res V V' W C B μ 𝓨 f ≠ 0 := by
  first | exact @GlobalTheory.TowerResNonzero.exists_res_ne_zero | exact GlobalTheory.TowerResNonzero.exists_res_ne_zero | (intros; apply GlobalTheory.TowerResNonzero.exists_res_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OntoPartAtOfZeroOrInjAt
section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParameterTransferTypes
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ParameterTransferTypes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Satake

def SpanAt (V : HSp D) (e : AE D) (M : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))
    (γ : GA D V) : Prop :=
  (∀ y ∈ Formalism.L2.NTheta.LamHat V, ∃ z, IntVec z ∧
    (fun a => finPart D e * (finMat D.sp.cm.sig V.gram γ).mulVec y a) = fun a => finPart D e * M.mulVec z a) ∧
  (∀ z, IntVec z → ∃ y ∈ Formalism.L2.NTheta.LamHat V,
    (fun a => finPart D e * (finMat D.sp.cm.sig V.gram γ).mulVec y a) = fun a => finPart D e * M.mulVec z a)


open Classical in
def sphVal {n : ℕ} (inert : Prop) (q : ℕ) (α : Fin n → ℂ) (a : Fin n → ℤ) : ℂ :=
  ∏ i : Fin n, if inert → 2 * (i : ℕ) + 1 < n then
    (α i * (((q : ℝ) ^ (-(((n : ℝ) - 1 - 2 * (i : ℕ)) / 2)) : ℝ) : ℂ)) ^ a i else 1

def str (x : ℂ) (q t : ℕ) : Multiset ℂ :=
  (Multiset.range t).map fun k => x * (((q : ℝ) ^ (((t : ℝ) - 1) / 2 - (k : ℝ)) : ℝ) : ℂ)

end Satake

section Spaces

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (R : _root_.Formalism.IndefR.Links.RealDat D A Ks) (F : Face D A)


open Classical in
def badS (t : T) : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  (R.Pg ∪ R.Q t).image fun PP => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)

variable (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ)

end Spaces

end GlobalTheory.IndefiniteRowSideFullHecke.ParameterTransferTypes

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.ParameterTransferTypes GlobalTheory.Hk3 GlobalTheory.SplitHeckeAdj

namespace GlobalTheory.LiftOntoCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Abstract

variable {H Γ W : Type} [Group H] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ι : Γ →* H}
  {ρ : Γ →* Module.End ℂ W} {J : Subgroup H} {χ : J →* ℂˣ} {Φ : H → W}

theorem mem_adForms_iff : Φ ∈ Bridge.AdForms ι ρ J χ ↔
    (∀ γ u, Φ (ι γ * u) = ρ γ (Φ u)) ∧ ∀ u k (hk : k ∈ J), Φ (u * k) = (χ ⟨k, hk⟩ : ℂ) • Φ u :=
  ⟨fun h => ⟨fun γ u => by simpa using h γ u 1, fun u k hk => by simpa using h 1 u ⟨k, hk⟩⟩,
    fun h γ u k => by rw [h.2 _ _ k.2, h.1]⟩

theorem eq_of_dual {x y : W} (h : ∀ ℓ : W →ₗ[ℂ] ℂ, ℓ x = ℓ y) : x = y :=
  sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => by rw [map_sub, h ℓ, sub_self])

end Abstract

section General

variable {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} (c : CoefA V)

variable {c}

theorem hasType_form {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ρ : GQ V →* Module.End ℂ W} {Φ : Bridge.Gf V → W}
    (hΦ : Φ ∈ Bridge.AdForms (Bridge.ratF V) ρ (levEnv V β L).J (levEnv V β L).χ)
    (ℓ : W →ₗ[ℂ] ℂ) : HasType V β (flag1L L) fun g => ℓ (Φ (fin V g)) := fun κ hκ g =>
  (congrArg (fun u => ℓ (Φ u)) ((fin V).map_mul g κ)).trans
    ((congrArg ℓ ((mem_adForms_iff.1 hΦ).2 (fin V g) _ ((mem_J V β L hκ.1).2 hκ))).trans (ℓ.map_smul _ _))

theorem forall_fin {p : Bridge.Gf V → Prop} (h : ∀ g ∈ GfC V, p (fin V g)) (u : Bridge.Gf V) : p u :=
  (fin_lift V u).elim fun g hg => hg.2 ▸ h g hg.1

theorem hkF_mem {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ρ : GQ V →* Module.End ℂ W} {w : Pl D.host.E}
    (a : List ℤ →₀ ℂ) (h3 : ∀ Φ, HasType V β (flag1L L) Φ → HasType V β (flag1L L) (hk V w a Φ))
    {Φ : Bridge.Gf V → W} (hΦ : Φ ∈ Bridge.AdForms (Bridge.ratF V) ρ (levEnv V β L).J (levEnv V β L).χ) :
    hkF V w a Φ ∈ Bridge.AdForms (Bridge.ratF V) ρ (levEnv V β L).J (levEnv V β L).χ := by
  have hc : ∀ (ℓ : W →ₗ[ℂ] ℂ) g, hk V w a (fun g => ℓ (Φ (fin V g))) g = ℓ (hkF V w a Φ (fin V g)) := fun ℓ g => by
    rw [GlobalTheory.LevOp.hk_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hkF, Finsupp.sum, map_sum, LinearMap.map_smul, smul_eq_mul, heckeLin_apply, MonoidHom.map_mul]
  refine mem_adForms_iff.2 ⟨fun γ u => ?_, fun u k => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [hkF, Finsupp.sum, mul_assoc, (mem_adForms_iff.1 hΦ).1, map_sum, LinearMap.map_smul]
  · refine forall_fin (p := fun k => ∀ hk : k ∈ (levEnv V β L).J,
      hkF V w a Φ (u * k) = ((levEnv V β L).χ ⟨k, hk⟩ : ℂ) • hkF V w a Φ u) (fun κ hκ hk => ?_) k
    refine forall_fin (p := fun u => hkF V w a Φ (u * fin V κ) = ((levEnv V β L).χ ⟨fin V κ, hk⟩ : ℂ) • hkF V w a Φ u)
      (fun g _ => eq_of_dual fun ℓ => ?_) u
    have := h3 _ (hasType_form hΦ ℓ) κ ((mem_J V β L hκ).1 hk) g
    rw [hc, hc, MonoidHom.map_mul] at this
    exact this.trans (ℓ.map_smul _ _).symm

theorem one_notMem (w : Pl D.host.E) (n : ℕ) : ((1 ^ n : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
  rw [one_pow, Nat.cast_one]
  exact (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top

end General

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem offS_iff_good (t : T) (w : Pl D.host.E) : OffS D (badS R t) w ↔ Good R t w := by
  classical
  rw [GlobalTheory.GoodPrimes.offS_iff]
  unfold badS
  simp only [Finset.mem_image, Finset.mem_union, not_exists, not_and]
  refine forall₂_congr fun PP _ => ⟨fun h => ⟨fun e => h (by rw [e]), fun e => h (GlobalTheory.LevelPlaces.under_eq_of_isConjPl e)⟩, fun h e => ?_⟩
  rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with h1 | h1
  · exact h.1 h1.symm
  · exact h.2 (GlobalTheory.GoodPrimes.isConjPl_iff.2 h1)

theorem exists_opsV (hL : R.toLevCh.Is A.μ0) (hM : R.IsModels) (i : Fin D.R.m) (t : T) : ∃ h, IsOpsV R i t h := by
  have key : ∀ w a, ∃ s : Module.End ℂ (R.HV i t).H, Good R t w → ∀ x, (R.HV i t).e (s x) = hkF (Vc D i) w a ((R.HV i t).e x) := by
    intro w a
    by_cases hw : Good R t w
    swap
    · exact ⟨0, fun h => absurd h hw⟩
    refine (hL.βV i).elim fun n hn => ?_
    have h3 := (GlobalTheory.LevOp.level_operators (Vc D i) (R.βV i) (R.ΛV i) _ (flag1L (R.datVt i t)) hn w (one_notMem w n) hw).2.2.1 a
    exact (GlobalTheory.DefiniteOps.exists_lift (R.HV i t) _ _ (hM.HV i t)
      (opOf (GlobalTheory.DefiniteOps.rtr (fin (Vc D i)) (R.cV i).W) w a)
      fun Φ hΦ => GlobalTheory.DefiniteOps.hkF_eq (Vc D i) w a Φ ▸ hkF_mem a h3 hΦ).imp
      fun s hs _ x => (hs x).trans (GlobalTheory.DefiniteOps.hkF_eq _ _ _ _).symm
  choose h hh using key
  exact ⟨h, fun w hw c x => hh w c hw x⟩

section Levels

variable (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ)

end Levels

section Compare

variable (R) (F : Face D A)

variable {R}

variable (R)

end Compare

end GlobalTheory.LiftOntoCompare

end
end
