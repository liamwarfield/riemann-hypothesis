module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedSchrodingerStandardLeviAction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylFormulaStandardUnitaryGroupWeilDatum
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.LeftInvOfIsSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableThetaKernelWeilRangeStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfCharOfCharOfHasInfQ

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinConvergent
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinConvergent
open scoped TensorProduct ENNReal Matrix Classical NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

noncomputable section

namespace GlobalTheory.CompanionTheory.Godement

open GlobalTheory.StdUnn.HeightExists GlobalTheory.StdUnn.PolesModel

theorem cosetConv_of_continuous_law : ∀ (D : D7) (n : ℕ) (χ : (AE D)ˣ →* Circle) (s₁ : ℂ) (φ : G D n → ℂ), Continuous φ →
    (∀ p ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat p) = a.1 → ∀ g,
      φ (p * g) = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) (s₁ + (n : ℂ) / 2) * φ g) →
    (n : ℝ) / 2 < s₁.re → ∀ g : G D n, CosetConv (P D n) (GF D n) φ g := by
  intro D n χ s₁ φ hcont hlaw hs g
  obtain ⟨H, φ₀, -, -, hH, hsec, hne⟩ :=
    GlobalTheory.StdUnn.PolesModel.hypotheses_hold D n 0 (s₁.re : ℂ)
  have hconv0 := GlobalTheory.StdUnn.PolesModel.cosetConv_stdSec hH hsec
    (s := (s₁.re : ℂ)) (by simpa using hs) g
  have hstd : GlobalTheory.StdUnn.stdSec H φ₀ (s₁.re : ℂ) (s₁.re : ℂ) = φ₀ := by
    funext x
    simp [GlobalTheory.StdUnn.stdSec, GlobalTheory.Doubling.npow]
  rw [hstd] at hconv0
  have hK : IsCompact (↑(GlobalTheory.StdUnn.K D n) : Set (G D n)) :=
    GlobalTheory.StdUnn.HeightExists.isCompact_K
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 1 (GlobalTheory.StdUnn.K D n).one_mem)
  obtain ⟨k₀, -, hk₀⟩ := hK.exists_isMinOn ⟨1, (GlobalTheory.StdUnn.K D n).one_mem⟩
    hsec.2.1.norm.continuousOn
  have hc : 0 < ‖φ₀ k₀‖ := norm_pos_iff.mpr (hne k₀)
  have hχ : ∀ u : Circle, ‖(u : ℂ)‖ = 1 := fun u => by
    first
      | exact Circle.norm_coe u
      | exact mem_sphere_zero_iff_norm.mp u.2
      | simp [Circle.abs_coe]
  have key : ∀ x, ‖φ x‖ ≤ C / ‖φ₀ k₀‖ * ‖φ₀ x‖ := by
    intro x
    obtain ⟨p, hp, k, hk, rfl⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D n x
    obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hp
    rw [hlaw p hp a ha k, hsec.1 p hp a ha k]
    have hu : IsUnit (GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a)) :=
      (Group.isUnit _).map _
    have hr : (0 : ℝ) < (GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a) : ℝ) :=
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hu.ne_zero)
    have hRR : ‖GlobalTheory.Doubling.npow (GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a))
          ((s₁.re : ℂ) + (n : ℂ) / 2)‖ =
        ‖GlobalTheory.Doubling.npow (GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a))
          (s₁ + (n : ℂ) / 2)‖ := by
      simp only [GlobalTheory.Doubling.npow]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hr, Complex.norm_cpow_eq_rpow_re_of_pos hr]
      congr 1 <;> simp
    have hb : ‖φ k‖ ≤ C / ‖φ₀ k₀‖ * ‖φ₀ k‖ := by
      refine le_trans (hC k hk) ?_
      calc C = C / ‖φ₀ k₀‖ * ‖φ₀ k₀‖ := (div_mul_cancel₀ C hc.ne').symm
        _ ≤ C / ‖φ₀ k₀‖ * ‖φ₀ k‖ :=
          mul_le_mul_of_nonneg_left (isMinOn_iff.mp hk₀ k hk) (div_nonneg hC0 hc.le)
    simp only [norm_mul, hχ, hRR]
    calc 1 * ‖GlobalTheory.Doubling.npow (GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a))
            (s₁ + (n : ℂ) / 2)‖ * ‖φ k‖
        ≤ 1 * ‖GlobalTheory.Doubling.npow (GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a))
            (s₁ + (n : ℂ) / 2)‖ * (C / ‖φ₀ k₀‖ * ‖φ₀ k‖) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = C / ‖φ₀ k₀‖ * (1 * ‖GlobalTheory.Doubling.npow (GlobalTheory.Doubling.absA D
            (Matrix.GeneralLinearGroup.det a)) (s₁ + (n : ℂ) / 2)‖ * ‖φ₀ k‖) := by ring
  unfold GlobalTheory.Eis.CosetConv at hconv0 ⊢
  refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_)
    (hconv0.mul_left (C / ‖φ₀ k₀‖))
  simp only [GlobalTheory.Eis.term]
  exact key _

end GlobalTheory.CompanionTheory.Godement

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinConvergentStatement
open scoped TensorProduct ENNReal Matrix Classical NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_eisenstein_convergent : ∀ (D : D7) (n : ℕ) (χ : (AE D)ˣ →* Circle) (s₁ : ℂ) (φ : G D n → ℂ), Continuous φ →
    (∀ p ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat p) = a.1 → ∀ g,
      φ (p * g) = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) (s₁ + (n : ℂ) / 2) * φ g) →
    (n : ℝ) / 2 < s₁.re → ∀ g : G D n, CosetConv (P D n) (GF D n) φ g := by
  first | exact @GlobalTheory.CompanionTheory.Godement.cosetConv_of_continuous_law | exact GlobalTheory.CompanionTheory.Godement.cosetConv_of_continuous_law | (intros; apply GlobalTheory.CompanionTheory.Godement.cosetConv_of_continuous_law <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalProdSpan
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalProdSpan
noncomputable section

open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LimV

theorem finiteDimensional_prodSpan_of_fd : ∀ {A B : Type} (U₁ : Submodule ℂ (A → ℂ)) (U₂ : Submodule ℂ (B → ℂ)),
    FiniteDimensional ℂ U₁ → FiniteDimensional ℂ U₂ → FiniteDimensional ℂ (prodSpan U₁ U₂) := by
  intro A B U₁ U₂ h₁ h₂
  let φ : U₁ →ₗ[ℂ] U₂ →ₗ[ℂ] (A × B → ℂ) :=
    LinearMap.mk₂ ℂ (fun a b x => a.1 x.1 * b.1 x.2)
      (fun a a' b => by ext x; simp [add_mul])
      (fun c a b => by ext x; simp [mul_assoc])
      (fun a b b' => by ext x; simp [mul_add])
      (fun c a b => by ext x; simp [mul_left_comm])
  let T : U₁ ⊗[ℂ] U₂ →ₗ[ℂ] (A × B → ℂ) := TensorProduct.lift φ
  have hle : prodSpan U₁ U₂ ≤ LinearMap.range T := by
    refine Submodule.span_le.2 ?_
    rintro F ⟨a, ha, b, hb, rfl⟩
    exact ⟨(⟨a, ha⟩ : U₁) ⊗ₜ[ℂ] (⟨b, hb⟩ : U₂), by simp [T, φ]⟩
  haveI : FiniteDimensional ℂ (LinearMap.range T) := LinearMap.finiteDimensional_range T
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.CompanionTheory.LimV

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalProdSpanStatement
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_prodSpan : ∀ {A B : Type} (U₁ : Submodule ℂ (A → ℂ)) (U₂ : Submodule ℂ (B → ℂ)), FiniteDimensional ℂ U₁ → FiniteDimensional ℂ U₂ → FiniteDimensional ℂ (prodSpan U₁ U₂) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.finiteDimensional_prodSpan_of_fd | exact GlobalTheory.CompanionTheory.LimV.finiteDimensional_prodSpan_of_fd | (intros; apply GlobalTheory.CompanionTheory.LimV.finiteDimensional_prodSpan_of_fd <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatAbsoluteCharacter
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatAbsoluteCharacter
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.LimV

open GlobalTheory.Mem.Chr.CharModel

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem logFin_eq_zero_of_integral (t : (Af E)ˣ)
    (h1 : (t : Af E) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E)
    (h2 : ((t⁻¹ : (Af E)ˣ) : Af E) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) : logFin E t = 0 := by
  have : GlobalTheory.Idele.idealOf t = 1 := by
    rw [← GlobalTheory.Idele.smul_one_eq, GlobalTheory.Idele.smul_eq_self_iff t one_ne_zero]
    intro v
    have e := congrArg Valued.v (GlobalTheory.Idele.idele_apply_mul_inv t v)
    rw [map_mul, map_one] at e
    have a1 : Valued.v ((t : Af E) v) ≤ 1 := GroundTheory.Global.mem_integralFiniteAdeles.1 h1 v
    have a2 : Valued.v (((t⁻¹ : (Af E)ˣ) : Af E) v) ≤ 1 := GroundTheory.Global.mem_integralFiniteAdeles.1 h2 v
    refine le_antisymm a1 ?_
    rw [← e]
    exact mul_le_of_le_one_right' a2
  simp [logFin, this]

theorem det_mem_of_entries {R : Type*} [CommRing R] (S : Subring R) {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (h : ∀ a b, M a b ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply']
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.prod_mem fun i _ => h _ _)

theorem logFin_det_of_mem {N : ℕ} {c : GL (Fin N) (Af E)} (hc : c ∈ KO E N) :
    logFin E (GeneralLinearGroup.det c) = 0 := by
  obtain ⟨h1, h2⟩ := (GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E N).1 hc
  refine logFin_eq_zero_of_integral _ (det_mem_of_entries _ _ h1) ?_
  rw [← map_inv]
  exact det_mem_of_entries _ _ h2

theorem logNorm_finId (u : (Af E)ˣ) : logNorm E (finId E u) = - logFin E u := by
  have h1 : finPart E (finId E u) = u := Units.ext (by
    change (1 : Af E) - 1 + u = u
    simp)
  have h2 : infPart E (finId E u) = 1 := Units.ext (by
    change (1 : InfiniteAdeleRing E) - 0 + 0 = 1
    simp)
  rw [logNorm, h1, h2, logInf_one, zero_sub]

theorem norm_det_unitary_at {N : ℕ} (k : Kinf E N) (v : InfinitePlace E) :
    ‖((GeneralLinearGroup.det (Unitary.toUnits k) : (Cinf E)ˣ) : Cinf E) v‖ = 1 := by
  have hd : (k : Matrix (Fin N) (Fin N) (Cinf E)).det ∈ unitary (Cinf E) := Matrix.det_of_mem_unitary k.2
  have h : star ((k : Matrix (Fin N) (Fin N) (Cinf E)).det v) * (k : Matrix (Fin N) (Fin N) (Cinf E)).det v = 1 :=
    congrFun (Unitary.star_mul_self_of_mem hd) v
  have h2 := congrArg norm h
  rw [norm_mul, norm_star, norm_one] at h2
  exact (mul_self_eq_one_iff.1 h2).resolve_right (by linarith [norm_nonneg ((k : Matrix (Fin N) (Fin N) (Cinf E)).det v)])

theorem logNorm_det_cf (N : ℕ) (k : Kinf E N) {c : GL (Fin N) (Af E)} (hc : c ∈ KO E N) :
    logNorm E (GeneralLinearGroup.det (cf N k c)) = 0 := by
  rw [cf, map_mul, logNorm_mul, det_infGL, det_finGL, Model.logNorm_infId, logNorm_finId, logFin_det_of_mem hc,
    Finset.sum_eq_zero fun v _ => by rw [norm_det_unitary_at, Real.log_one, mul_zero]]
  simp

theorem chiDet_absC_cf (N : ℕ) (w : ℂ) (k : Kinf E N) {c : GL (Fin N) (Af E)} (hc : c ∈ KO E N) :
    chiDet N (GlobalTheory.CuspRep.Model.absC E w) (cf N k c) = 1 := by
  apply Units.ext
  change Complex.exp (w * (logNorm E (GeneralLinearGroup.det (cf N k c)) : ℂ)) = 1
  rw [logNorm_det_cf N k hc]
  simp

end

theorem absFn_flat : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (w : ℂ),
    FlatFn (absFn (E := E) N w) := by
  intro E _ _ _ N w
  refine ⟨fun x => Units.ne_zero _, fun x k c hc => ?_, ?_⟩
  · simp only [absFn, map_mul, chiDet_absC_cf N w k hc, mul_one]
  · have h : absFn (E := E) N w = (mulChi N (GlobalTheory.CuspRep.Model.absC E w) (oneFn E N)).1 := funext fun x => by
      rw [mulChi_apply]
      simp [absFn, oneFn]
    rw [h]
    exact (mulChi N (GlobalTheory.CuspRep.Model.absC E w) (oneFn E N)).2

end GlobalTheory.CompanionTheory.LimV

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatAbsoluteCharacterStatement
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_absolute_character : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (w : ℂ), FlatFn (absFn (E := E) N w) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.absFn_flat | exact GlobalTheory.CompanionTheory.LimV.absFn_flat | (intros; apply GlobalTheory.CompanionTheory.LimV.absFn_flat <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemProdSpanInf
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemProdSpanInf
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV.Slices

variable {A B : Type}

theorem span_eval_eq_top (W : Submodule ℂ (B → ℂ)) [FiniteDimensional ℂ W] :
    Submodule.span ℂ (Set.range fun y : B =>
      ((LinearMap.proj y : (B → ℂ) →ₗ[ℂ] ℂ) ∘ₗ W.subtype : Module.Dual ℂ W)) = ⊤ := by
  set E := Submodule.span ℂ (Set.range fun y : B =>
      ((LinearMap.proj y : (B → ℂ) →ₗ[ℂ] ℂ) ∘ₗ W.subtype : Module.Dual ℂ W)) with hE
  have hbot : E.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_dualCoannihilator] at hw
    have : (w : B → ℂ) = 0 := by
      funext y
      exact hw _ (Submodule.subset_span ⟨y, rfl⟩)
    exact (Submodule.mem_bot ℂ).2 (Subtype.ext this)
  have h := Subspace.dualCoannihilator_dualAnnihilator_eq (W := E)
  rw [hbot] at h
  rw [← h]
  simp

theorem mem_prodSpan_inf_left (U S : Submodule ℂ (A → ℂ)) (V : Submodule ℂ (B → ℂ))
    (G : A × B → ℂ) (hG : G ∈ prodSpan U V) (hS : ∀ y, (fun x => G (x, y)) ∈ S) :
    G ∈ prodSpan (U ⊓ S) V := by
  obtain ⟨n, f, g, hsum⟩ := Submodule.mem_span_set'.1 hG
  choose a ha b hb hg using fun i => (g i).2
  let W : Submodule ℂ (B → ℂ) := Submodule.span ℂ (Set.range b)
  haveI : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range b)
  have hWV : W ≤ V := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hb i)
  let bw : Fin n → W := fun i => ⟨b i, Submodule.subset_span ⟨i, rfl⟩⟩
  let T : A → W := fun x => ∑ i, (f i * a i x) • bw i
  have hG' : ∀ x y, G (x, y) = ∑ i, f i * a i x * b i y := by
    intro x y
    rw [← hsum]
    simp only [Finset.sum_apply, Pi.smul_apply, hg, smul_eq_mul, mul_assoc]
  have hT : ∀ x y, (T x : B → ℂ) y = G (x, y) := by
    intro x y
    rw [hG']
    simp [T, bw]
  have hφS : ∀ φ : Module.Dual ℂ W, (fun x => φ (T x)) ∈ S := by
    intro φ
    have hφ : φ ∈ Submodule.span ℂ (Set.range fun y : B =>
        ((LinearMap.proj y : (B → ℂ) →ₗ[ℂ] ℂ) ∘ₗ W.subtype : Module.Dual ℂ W)) := by
      rw [span_eval_eq_top]; trivial
    induction hφ using Submodule.span_induction with
    | mem φ h =>
      obtain ⟨y, rfl⟩ := h
      simpa [hT] using hS y
    | zero => exact S.zero_mem
    | add φ ψ _ _ h₁ h₂ => exact S.add_mem h₁ h₂
    | smul r φ _ h => exact S.smul_mem r h
  have hφU : ∀ φ : Module.Dual ℂ W, (fun x => φ (T x)) ∈ U := by
    intro φ
    have : (fun x => φ (T x)) = ∑ i, (f i * φ (bw i)) • a i := by
      funext x
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [T, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    exact U.sum_mem fun i _ => U.smul_mem _ (ha i)
  let c := Module.finBasis ℂ W
  have hdec : G = ∑ j, fun p : A × B => c.coord j (T p.1) * (c j : B → ℂ) p.2 := by
    funext ⟨x, y⟩
    rw [← hT, Finset.sum_apply]
    have h := congrArg (fun w : W => (w : B → ℂ) y) (c.sum_repr (T x))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at h
    simpa [Module.Basis.coord_apply] using h.symm
  rw [hdec]
  exact Submodule.sum_mem _ fun j _ => Submodule.subset_span
    ⟨_, ⟨hφU (c.coord j), hφS (c.coord j)⟩, _, hWV (c j).2, rfl⟩

theorem swap_mem_prodSpan (U : Submodule ℂ (A → ℂ)) (V : Submodule ℂ (B → ℂ))
    (G : A × B → ℂ) (hG : G ∈ prodSpan U V) : (fun p : B × A => G p.swap) ∈ prodSpan V U := by
  induction hG using Submodule.span_induction with
  | mem F h =>
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    exact Submodule.subset_span ⟨b, hb, a, ha, by funext p; simp [mul_comm]⟩
  | zero => exact Submodule.zero_mem _
  | add F F' _ _ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂
  | smul r F _ h => exact Submodule.smul_mem _ r h

theorem mem_prodSpan_inf_of_slices : ∀ {A B : Type} (U₁ S₁ : Submodule ℂ (A → ℂ))
    (U₂ S₂ : Submodule ℂ (B → ℂ)) (G : A × B → ℂ), G ∈ prodSpan U₁ U₂ →
    (∀ y, (fun x => G (x, y)) ∈ S₁) → (∀ x, (fun y => G (x, y)) ∈ S₂) →
    G ∈ prodSpan (U₁ ⊓ S₁) (U₂ ⊓ S₂) := by
  intro A B U₁ S₁ U₂ S₂ G hG h₁ h₂
  have hL := mem_prodSpan_inf_left U₁ S₁ U₂ G hG h₁
  have hR := mem_prodSpan_inf_left U₂ S₂ (U₁ ⊓ S₁) (fun p : B × A => G p.swap)
    (swap_mem_prodSpan _ _ G hL) (fun x => h₂ x)
  simpa using swap_mem_prodSpan _ _ _ hR

end GlobalTheory.CompanionTheory.LimV.Slices

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemProdSpanInfStatement
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_prodSpan_inf : ∀ {A B : Type} (U₁ S₁ : Submodule ℂ (A → ℂ)) (U₂ S₂ : Submodule ℂ (B → ℂ)) (G : A × B → ℂ), G ∈ prodSpan U₁ U₂ → (∀ y, (fun x => G (x, y)) ∈ S₁) → (∀ x, (fun y => G (x, y)) ∈ S₂) → G ∈ prodSpan (U₁ ⊓ S₁) (U₂ ⊓ S₂) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.Slices.mem_prodSpan_inf_of_slices | exact GlobalTheory.CompanionTheory.LimV.Slices.mem_prodSpan_inf_of_slices | (intros; apply GlobalTheory.CompanionTheory.LimV.Slices.mem_prodSpan_inf_of_slices <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NodeFunctionLeviDecomposition
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviFactorOfUnipotentDecomp
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviFactorOfUnipotentDecomp
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV.LeviCf

theorem entries_of_unip_lev {R : Type} [CommRing R] {r s : ℕ} (S : Set R) (x : BlockIx (r + s) r → R)
    (g : GL (Fin r) R × GL (Fin s) R)
    (h : ∀ a b : Fin (r + s), ((unip x * lev R r s g : GL (Fin (r + s)) R) : Matrix (Fin (r + s)) (Fin (r + s)) R) a b ∈ S)
    (h' : ∀ a b : Fin (r + s),
      (((unip x * lev R r s g)⁻¹ : GL (Fin (r + s)) R) : Matrix (Fin (r + s)) (Fin (r + s)) R) a b ∈ S) :
    ((∀ a b : Fin r, (g.1 : Matrix (Fin r) (Fin r) R) a b ∈ S) ∧
        ∀ a b : Fin r, ((g.1⁻¹ : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) a b ∈ S) ∧
      ((∀ a b : Fin s, (g.2 : Matrix (Fin s) (Fin s) R) a b ∈ S) ∧
        ∀ a b : Fin s, ((g.2⁻¹ : GL (Fin s) R) : Matrix (Fin s) (Fin s) R) a b ∈ S) := by
  obtain ⟨v, hv⟩ := lev_mul_unip (g⁻¹) (-x)
  have hu : (unip x : GL (Fin (r + s)) R)⁻¹ = unip (-x) := by
    rw [inv_eq_iff_mul_eq_one, ← D.unip_add', add_neg_cancel, unip_zero]
  have hi : (unip x * lev R r s g : GL (Fin (r + s)) R)⁻¹ = unip v * lev R r s g⁻¹ := by
    rw [_root_.mul_inv_rev, hu, ← map_inv, hv]
  rw [hi] at h'
  refine ⟨⟨fun a b => ?_, fun a b => ?_⟩, fun a b => ?_, fun a b => ?_⟩
  · rw [← unip_lev_cc x g a b]; exact h _ _
  · have := unip_lev_cc v g⁻¹ a b
    rw [Prod.fst_inv] at this
    rw [← this]; exact h' _ _
  · rw [← unip_lev_nn x g a b]; exact h _ _
  · have := unip_lev_nn v g⁻¹ a b
    rw [Prod.snd_inv] at this
    rw [← this]; exact h' _ _

theorem levi_cf_integral {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}
    (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s)) (c : GL (Fin (r + s)) (Af E))
    (hc : c ∈ KO E (r + s)) (h : unip u * lev (Ad E) r s m = cf (r + s) k c) :
    ∃ (k₁ : Kinf E r) (c₁ : GL (Fin r) (Af E)) (k₂ : Kinf E s) (c₂ : GL (Fin s) (Af E)),
      c₁ ∈ KO E r ∧ c₂ ∈ KO E s ∧ m = (cf r k₁ c₁, cf s k₂ c₂) := by
  obtain ⟨k₁, g₁, k₂, g₂, hm⟩ := levi_cf h
  have f1 : GeneralLinearGroup.map (pFin E) m.1 = g₁ := by
    rw [hm, cf, map_mul, pFin_infGL, pFin_finGL, one_mul]
  have f2 : GeneralLinearGroup.map (pFin E) m.2 = g₂ := by
    rw [show m.2 = cf s k₂ g₂ by rw [hm], cf, map_mul, pFin_infGL, pFin_finGL, one_mul]
  have h2 := congrArg (GeneralLinearGroup.map (pFin E)) h
  rw [map_mul, IwaAd.map_unip, IwaAd.map_lev, cf, map_mul, pFin_infGL, pFin_finGL, one_mul, f1, f2] at h2
  obtain ⟨hc1, hc2⟩ := (GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E (r + s)).1 hc
  obtain ⟨⟨a1, a2⟩, b1, b2⟩ := entries_of_unip_lev (↑(GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) : Set (Af E)) _ (g₁, g₂)
    (by rw [h2]; exact hc1) (by rw [h2]; exact hc2)
  exact ⟨k₁, g₁, k₂, g₂, (GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E r).2 ⟨a1, a2⟩,
    (GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E s).2 ⟨b1, b2⟩, hm⟩

end GlobalTheory.CompanionTheory.LimV.LeviCf

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviFactorOfUnipotentDecompStatement
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_factor_of_unipotent_decomp : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ} (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s)) (c : GL (Fin (r + s)) (Af E)), c ∈ KO E (r + s) → unip u * lev (Ad E) r s m = cf (r + s) k c → ∃ (k₁ : Kinf E r) (c₁ : GL (Fin r) (Af E)) (k₂ : Kinf E s) (c₂ : GL (Fin s) (Af E)), c₁ ∈ KO E r ∧ c₂ ∈ KO E s ∧ m = (cf r k₁ c₁, cf s k₂ c₂) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.LeviCf.levi_cf_integral | exact GlobalTheory.CompanionTheory.LimV.LeviCf.levi_cf_integral | (intros; apply GlobalTheory.CompanionTheory.LimV.LeviCf.levi_cf_integral <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NodeFunctionLeviDecomposition
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.LimV.NodeApply

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}

theorem levi_eq_mul_cf (u u' : BlockIx (r + s) r → Ad E) (m m' : GA E r × GA E s) (k k' : Kinf E (r + s))
    (c c' : GL (Fin (r + s)) (Af E)) (hc : c ∈ KO E (r + s)) (hc' : c' ∈ KO E (r + s))
    (h : unip u * lev (Ad E) r s m * cf (r + s) k c = unip u' * lev (Ad E) r s m' * cf (r + s) k' c') :
    ∃ (k₁ : Kinf E r) (c₁ : GL (Fin r) (Af E)) (k₂ : Kinf E s) (c₂ : GL (Fin s) (Af E)),
      c₁ ∈ KO E r ∧ c₂ ∈ KO E s ∧ m' = (m.1 * cf r k₁ c₁, m.2 * cf s k₂ c₂) := by
  obtain ⟨v, hv⟩ := lev_mul_unip (m⁻¹) (-u + u')
  have hu : (unip u : GA E (r + s))⁻¹ = unip (-u) := by
    rw [inv_eq_iff_mul_eq_one, ← D.unip_add', add_neg_cancel, unip_zero]
  have key : unip v * lev (Ad E) r s (m⁻¹ * m') = cf (r + s) (k * k'⁻¹) (c * c'⁻¹) := by
    rw [← cf_mul, ← cf_inv, map_mul, ← mul_assoc, ← hv, D.unip_add', map_inv, ← hu]
    have h2 : unip u' * lev (Ad E) r s m' =
        unip u * lev (Ad E) r s m * cf (r + s) k c * (cf (r + s) k' c')⁻¹ := by
      rw [h]; group
    rw [mul_assoc (lev (Ad E) r s m)⁻¹, mul_assoc (unip u)⁻¹, h2]
    group
  obtain ⟨k₁, c₁, k₂, c₂, h₁, h₂, hm⟩ := GlobalTheory.T.levi_factor_of_unipotent_decomp v (m⁻¹ * m') _ _
    (mul_mem hc (inv_mem hc')) key
  refine ⟨k₁, c₁, k₂, c₂, h₁, h₂, ?_⟩
  calc m' = m * (m⁻¹ * m') := (mul_inv_cancel_left m m').symm
    _ = _ := by rw [hm]; rfl

theorem nodeFn_apply : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ} (e₁ : GA E r → ℂ) (e₂ : GA E s → ℂ), FlatFn e₁ → FlatFn e₂ → ∀ (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s)) (c : GL (Fin (r + s)) (Af E)), c ∈ KO E (r + s) → nodeFn e₁ e₂ (unip u * lev (Ad E) r s m * cf (r + s) k c) = e₁ m.1 * e₂ m.2 := by
  intro E _ _ _ r s e₁ e₂ f₁ f₂ u m k c hc
  obtain ⟨k', c', hc', hx'⟩ :=
    (exists_iw (unip u * lev (Ad E) r s m * cf (r + s) k c)).choose_spec.choose_spec
  obtain ⟨k₁, c₁, k₂, c₂, h₁, h₂, hm⟩ := levi_eq_mul_cf u _ m _ k k' c c' hc hc' hx'
  have hl : leviOf (unip u * lev (Ad E) r s m * cf (r + s) k c) =
      (m.1 * cf r k₁ c₁, m.2 * cf s k₂ c₂) := hm
  rw [nodeFn, hl, f₁.rinv _ _ _ h₁, f₂.rinv _ _ _ h₂]

end GlobalTheory.CompanionTheory.LimV.NodeApply

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NodeFunctionLeviDecompositionStatement
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.node_function_levi_decomposition : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ} (e₁ : GA E r → ℂ) (e₂ : GA E s → ℂ), FlatFn e₁ → FlatFn e₂ → ∀ (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s)) (c : GL (Fin (r + s)) (Af E)), c ∈ KO E (r + s) → nodeFn e₁ e₂ (unip u * lev (Ad E) r s m * cf (r + s) k c) = e₁ m.1 * e₂ m.2 := by
  first | exact @GlobalTheory.CompanionTheory.LimV.NodeApply.nodeFn_apply | exact GlobalTheory.CompanionTheory.LimV.NodeApply.nodeFn_apply | (intros; apply GlobalTheory.CompanionTheory.LimV.NodeApply.nodeFn_apply <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TendstoAbsoluteCharacterOne
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TendstoAbsoluteCharacterOne
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV

theorem absFn_tendsto_one : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (x : GA E N) (w : ℕ → ℂ), Tendsto w atTop (𝓝 0) → Tendsto (fun k => absFn N (w k) x) atTop (𝓝 1) := by
  intro E _ _ _ N x w hw
  have hL : ∀ t : ℂ, absFn N t x =
      Complex.exp (t * (GlobalTheory.Mem.Chr.CharModel.logNorm E (GeneralLinearGroup.det x) : ℝ)) := by
    intro t
    exact GlobalTheory.Mem.Chr.CharModel.absHom_val E t (GeneralLinearGroup.det x)
  have h0 : Tendsto (fun k => Complex.exp (w k *
      (GlobalTheory.Mem.Chr.CharModel.logNorm E (GeneralLinearGroup.det x) : ℝ))) atTop
      (𝓝 (Complex.exp (0 * (GlobalTheory.Mem.Chr.CharModel.logNorm E (GeneralLinearGroup.det x) : ℝ)))) :=
    (Complex.continuous_exp.tendsto _).comp (hw.mul_const _)
  simpa [hL] using h0

end GlobalTheory.CompanionTheory.LimV
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TendstoAbsoluteCharacterOneStatement
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_absolute_character_one : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (x : GA E N) (w : ℕ → ℂ), Tendsto w atTop (𝓝 0) → Tendsto (fun k => absFn N (w k) x) atTop (𝓝 1) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.absFn_tendsto_one | exact GlobalTheory.CompanionTheory.LimV.absFn_tendsto_one | (intros; apply GlobalTheory.CompanionTheory.LimV.absFn_tendsto_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSectionContinuous
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSectionContinuous
open scoped TensorProduct ENNReal Matrix Classical NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace GlobalTheory.CompanionTheory.SiegelWeil

theorem swSection_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χ : (AE D)ˣ →* Circle)
    (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ ω →
    ∀ (f : WO (dblSp A) B → ℂ), IsThetaFunO ψ (dblSp A) B f →
    ∀ (ν : Measure (Mx D B.rank A.rank)) (𝓖 : Set (Mx D B.rank A.rank)), IsCovolOne (ratL B A) ν 𝓖 →
    Continuous (swSection A B ν 𝓖 ω f) := by
  intro D ψ A B χ ω hω f hf ν 𝓖 hν
  rw [GlobalTheory.Core.Rk.IP.swSection_eq_swSec A B ν 𝓖 ω f]
  exact (GlobalTheory.Core.Rk.IP.swSec_integrable_continuous D ψ A B χ ω hω ν 𝓖 hν f hf).2

end GlobalTheory.CompanionTheory.SiegelWeil
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSectionContinuousStatement
open scoped TensorProduct ENNReal Matrix Classical NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_section_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χ : (AE D)ˣ →* Circle)
    (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ ω →
    ∀ (f : WO (dblSp A) B → ℂ), IsThetaFunO ψ (dblSp A) B f →
    ∀ (ν : Measure (Mx D B.rank A.rank)) (𝓖 : Set (Mx D B.rank A.rank)), IsCovolOne (ratL B A) ν 𝓖 →
    Continuous (swSection A B ν 𝓖 ω f) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelWeil.swSection_continuous | exact GlobalTheory.CompanionTheory.SiegelWeil.swSection_continuous | (intros; apply GlobalTheory.CompanionTheory.SiegelWeil.swSection_continuous <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilSchwartzParabolicEquivariant
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilSchwartzParabolicEquivariant
open scoped TensorProduct ENNReal Matrix Classical NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace GlobalTheory.CompanionTheory.WeilLaw

theorem weil_parabolic_law : ∀ (D : D7) (n : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D) (V : HSp D)
    (μ : Measure (Mx D V.rank n)) (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)),
    IsWeilSch ψ χ θ V μ ω → ∀ (Φ : schwartzA θ V.rank n),
    ∀ p ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat p) = a.1 → ∀ g,
      (ω (p * g) Φ).1 0 = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) (s0 V n + (n : ℂ) / 2) * (ω g Φ).1 0 := by
  intro D n ψ χ θ V μ ω hω Φ p hp a ha g
  obtain ⟨m, v, b, e, hm, hv⟩ := LeftInvSect.exists_levi_unip hp a ha
  have e' : ω (p * g) Φ = ω m (ω v (ω g Φ)) := by
    rw [e, map_mul, map_mul]; rfl
  have z1 : ∀ a : Mx D n n, ((0 : Mx D V.rank n) ⬝ a : Mx D V.rank n) = 0 := fun a => Matrix.zero_mul a
  have z2 : StdUnn.inner V (0 : Mx D V.rank n) 0 = 0 := by rw [StdUnn.inner, adj_zero, Matrix.zero_mul]
  have hs : s0 V n + (n : ℂ) / 2 = (V.rank : ℂ) / 2 := by
    rw [s0]; ring
  rw [e', hω.levi m _ hm, z1, hω.unip v b hv, z2, hs]
  simp [halfTr]

end GlobalTheory.CompanionTheory.WeilLaw
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilSchwartzParabolicEquivariantStatement
open scoped TensorProduct ENNReal Matrix Classical NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_schwartz_parabolic_equivariant : ∀ (D : D7) (n : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D) (V : HSp D)
    (μ : Measure (Mx D V.rank n)) (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)),
    IsWeilSch ψ χ θ V μ ω → ∀ (Φ : schwartzA θ V.rank n),
    ∀ p ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat p) = a.1 → ∀ g,
      (ω (p * g) Φ).1 0 = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) (s0 V n + (n : ℂ) / 2) * (ω g Φ).1 0 := by
  first | exact @GlobalTheory.CompanionTheory.WeilLaw.weil_parabolic_law | exact GlobalTheory.CompanionTheory.WeilLaw.weil_parabolic_law | (intros; apply GlobalTheory.CompanionTheory.WeilLaw.weil_parabolic_law <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisRepresentationAdmitted
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.HeckeAlg

open GlobalTheory.CuspRep GlobalTheory.CuspRep.InfType

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem dchi_atEmb (χ : HChar E) (τ : E →+* ℂ) (z : ℂ) :
    dchi χ (atEmb τ z) = expo χ τ * z + expo χ (ComplexEmbedding.conjugate τ) * starRingEnd ℂ z := by
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq]; simp
  rw [atEmb_eq, map_add (f := _), map_smul, map_smul]
  simp only [expo, atEmb_conj, map_one, Complex.conj_I, e, map_neg, Complex.real_smul]
  conv_rhs => rw [← Complex.re_add_im z]
  simp only [map_add (f := _), map_mul, Complex.conj_ofReal, Complex.conj_I]
  linear_combination (z.im * dchi χ (atEmb τ Complex.I)) * Complex.I_mul_I

theorem dchi_eq_sum (χ : HChar E) (z : Cinf E) : dchi χ z = ∑ φ : E →+* ℂ, expo χ φ * coord φ z := by
  classical
  have hz : z = ∑ w : InfinitePlace E, atEmb w.embedding (z w) := by
    funext v
    rw [Finset.sum_apply, Finset.sum_eq_single v]
    · simp [atEmb, InfinitePlace.mk_embedding]
    · intro b _ hb
      simp [atEmb, InfinitePlace.mk_embedding, Pi.single_eq_of_ne hb.symm]
    · simp
  conv_lhs => rw [hz]
  conv_rhs => rw [hz]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [dchi_atEmb]
  simp only [coord_atEmb', mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end GlobalTheory.CompanionTheory.HeckeAlg

namespace GlobalTheory.CompanionTheory.RankOneGal

open GlobalTheory.CuspRep GlobalTheory.CuspRep.InfType GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.TripleGal GlobalTheory.Pst GlobalTheory.GalOfCusp
open Formalism.BasicNotions.Loc Neutral.B1

section Char

variable {E Ω : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {l : ℕ} [Fact l.Prime]

end Char

end GlobalTheory.CompanionTheory.RankOneGal

namespace GlobalTheory.CompanionTheory.RankOneGal

open GlobalTheory.CuspRep GlobalTheory.CuspRep.InfType GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.TripleGal GlobalTheory.Pst GlobalTheory.GalOfCusp
open Formalism.BasicNotions.Loc

end GlobalTheory.CompanionTheory.RankOneGal

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TypedSecondBlockRestriction
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TypedSecondBlockRestriction
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV.SliceR

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}

def levelTwo (K : Subgroup (GL (Fin (r + s)) (Af E))) (t : GL (Fin (r + s)) (Af E)) :
    Subgroup (GL (Fin s) (Af E)) :=
  K.comap ((MulAut.conj t⁻¹).toMonoidHom.comp (Slice2.lev2 (Af E) r s))

theorem mem_levelTwo {K : Subgroup (GL (Fin (r + s)) (Af E))} {t : GL (Fin (r + s)) (Af E)}
    {u : GL (Fin s) (Af E)} : u ∈ levelTwo K t ↔ t⁻¹ * lev (Af E) r s (1, u) * t ∈ K := by
  simp [levelTwo, MulAut.conj_apply, Slice2.lev2]

theorem isOpen_levelTwo {K : Subgroup (GL (Fin (r + s)) (Af E))}
    (hK : IsOpen (K : Set (GL (Fin (r + s)) (Af E)))) (t : GL (Fin (r + s)) (Af E)) :
    IsOpen (levelTwo K t : Set (GL (Fin s) (Af E))) := by
  have hc : Continuous fun u : GL (Fin s) (Af E) => t⁻¹ * Slice2.lev2 (Af E) r s u * t :=
    (continuous_const.mul Slice2.continuous_lev2).mul continuous_const
  convert hK.preimage hc using 1
  ext u
  exact mem_levelTwo

def sliceMap (k : Kinf E (r + s)) : (Kinf E (r + s) → ℂ) →ₗ[ℂ] (Kinf E s → ℂ) :=
  LinearMap.funLeft ℂ ℂ fun κ => Slice2.levK E r s κ * k

theorem lev_finGL_right (x : GA E r) (g : GA E s) (u : GL (Fin s) (Af E)) (k : Kinf E (r + s))
    (t : GL (Fin (r + s)) (Af E)) :
    lev (Ad E) r s (x, g * finGL E s u) * cf (r + s) k t =
      lev (Ad E) r s (x, g) * cf (r + s) k t * finGL E (r + s) (t⁻¹ * lev (Af E) r s (1, u) * t) := by
  have hY : finGL E (r + s) (lev (Af E) r s (1, u)) * finGL E (r + s) t =
      finGL E (r + s) t * finGL E (r + s) (t⁻¹ * lev (Af E) r s (1, u) * t) := by
    rw [← map_mul, ← map_mul]
    congr 1
    group
  rw [Slice2.lev_mul_right, Slice2.lev_finGL_one, cf, mul_assoc (lev (Ad E) r s (x, g)),
    ← mul_assoc (finGL E (r + s) _), ← infGL_comm, mul_assoc (infGL E (r + s) _), hY]
  simp only [mul_assoc]

theorem lev_infGL_right (x : GA E r) (g : GA E s) (κ : Kinf E s) (k : Kinf E (r + s))
    (t : GL (Fin (r + s)) (Af E)) :
    lev (Ad E) r s (x, g * infGL E s (Unitary.toUnits κ)) * cf (r + s) k t =
      (lev (Ad E) r s (x, g) * finGL E (r + s) t) *
        infGL E (r + s) (Unitary.toUnits (Slice2.levK E r s κ * k)) := by
  rw [Slice2.lev_mul_right, Slice2.lev_infGL_one, cf, map_mul Unitary.toUnits, Slice2.toUnits_levK,
    map_mul (infGL E (r + s)), mul_assoc (lev (Ad E) r s (x, g)) (finGL E (r + s) t), infGL_comm _ t]
  rw [mul_assoc (lev (Ad E) r s (x, g)) (infGL E (r + s) _), ← mul_assoc (infGL E (r + s) _) (finGL E (r + s) t),
    infGL_comm]
  simp only [mul_assoc]

end GlobalTheory.CompanionTheory.LimV.SliceR

theorem GlobalTheory.CompanionTheory.LimV.SliceR.slice_right : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ} (k : Kinf E (r + s)) (t : GL (Fin (r + s)) (Af E)) (K : Subgroup (GL (Fin (r + s)) (Af E))) (W : Submodule ℂ (Kinf E (r + s) → ℂ)), IsOpen (K : Set (GL (Fin (r + s)) (Af E))) → FiniteDimensional ℂ W → ∃ (K₂ : Subgroup (GL (Fin s) (Af E))) (W₂ : Submodule ℂ (Kinf E s → ℂ)), IsOpen (K₂ : Set (GL (Fin s) (Af E))) ∧ FiniteDimensional ℂ W₂ ∧ ∀ f ∈ typeF K W, ∀ x : GA E r, (fun y : GA E s => f (lev (Ad E) r s (x, y) * cf (r + s) k t)) ∈ typeF K₂ W₂ := by
  intro E _ _ _ r s k t K W hK hW
  refine ⟨SliceR.levelTwo K t, W.map (SliceR.sliceMap k), SliceR.isOpen_levelTwo hK t, inferInstance,
    fun f hf x => ⟨fun u hu g => ?_, fun g => ?_⟩⟩
  · change f (lev (Ad E) r s (x, g * finGL E s u) * cf (r + s) k t) = f (lev (Ad E) r s (x, g) * cf (r + s) k t)
    rw [SliceR.lev_finGL_right]
    exact hf.1 _ (SliceR.mem_levelTwo.1 hu) _
  · refine ⟨_, hf.2 (lev (Ad E) r s (x, g) * finGL E (r + s) t), ?_⟩
    funext κ
    change f _ = f (lev (Ad E) r s (x, g * infGL E s (Unitary.toUnits κ)) * cf (r + s) k t)
    rw [SliceR.lev_infGL_right]

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TypedSecondBlockRestrictionStatement
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typed_second_block_restriction : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ} (k : Kinf E (r + s)) (t : GL (Fin (r + s)) (Af E)) (K : Subgroup (GL (Fin (r + s)) (Af E))) (W : Submodule ℂ (Kinf E (r + s) → ℂ)), IsOpen (K : Set (GL (Fin (r + s)) (Af E))) → FiniteDimensional ℂ W → ∃ (K₂ : Subgroup (GL (Fin s) (Af E))) (W₂ : Submodule ℂ (Kinf E s → ℂ)), IsOpen (K₂ : Set (GL (Fin s) (Af E))) ∧ FiniteDimensional ℂ W₂ ∧ ∀ f ∈ typeF K W, ∀ x : GA E r, (fun y : GA E s => f (lev (Ad E) r s (x, y) * cf (r + s) k t)) ∈ typeF K₂ W₂ := by
  first | exact @GlobalTheory.CompanionTheory.LimV.SliceR.slice_right | exact GlobalTheory.CompanionTheory.LimV.SliceR.slice_right | (intros; apply GlobalTheory.CompanionTheory.LimV.SliceR.slice_right <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CarriesTwistAbsoluteCharacter
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CarriesTwistAbsoluteCharacter
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV

theorem carries_absFn_tw {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}
    (U : Submodule ℂ (Sm E N)) (z z' : ℂ) : Carries (absFn N (z' - z)) (tw U z) (tw U z') := by
  rintro φ ⟨ψ, hψ, rfl⟩
  refine ⟨mulChi N (GlobalTheory.CuspRep.Model.absC E z') ψ, ⟨ψ, hψ, rfl⟩, fun x => ?_⟩
  have e : ∀ s : ℂ, ((chiDet N (GlobalTheory.CuspRep.Model.absC E s) x : ℂˣ) : ℂ) =
      Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm E (GeneralLinearGroup.det x)) := fun _ => rfl
  simp only [LinearEquiv.coe_coe, mulChi_apply, absFn]
  rw [e z', e (z' - z), e z, mul_left_comm, ← Complex.exp_add, ← add_mul, sub_add_cancel]

end GlobalTheory.CompanionTheory.LimV

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CarriesTwistAbsoluteCharacterStatement
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carries_twist_absolute_character : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ} (U : Submodule ℂ (Sm E N)) (z z' : ℂ), Carries (absFn N (z' - z)) (tw U z) (tw U z') := by
  first | exact @GlobalTheory.CompanionTheory.LimV.carries_absFn_tw | exact GlobalTheory.CompanionTheory.LimV.carries_absFn_tw | (intros; apply GlobalTheory.CompanionTheory.LimV.carries_absFn_tw <;> assumption)
end
end
