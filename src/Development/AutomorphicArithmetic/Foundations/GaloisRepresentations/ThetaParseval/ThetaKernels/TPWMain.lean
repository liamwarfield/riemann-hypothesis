module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.EtaProdK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IdxSign
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpDatum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutTrace
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkFacArch

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InfiniteNormOneField
theorem UpperTheory.Reformulated.B.InfiniteNormOneField.infinite_norm_one_k {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E} {nS nT : ℕ}
    {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
    {θ : NumberField.InfinitePlace F → TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) E →+* ℂ}
    {ι : (NumberField.InfinitePlace F → ℂ) →+ Formalism.IndefR.DatumF.AEF F E}
    (h : PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) : {t | t * σ t = 1}.Infinite :=
  have hcm : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ := h.1.cm
  UpperTheory.Reformulated.B.CapelliAbsoluteValue.abs σ hcm.2.1 hcm.2.2.2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPWDatumK
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutProd
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
namespace PositivityTheory.ThKW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}
variable {η : (AEF F E)ˣ →* Circle} {ε : AEF F E} {of oi : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)}
theorem fin_inf_comm_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hO : _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om)
    (hof : ∀ p, ∃ z : ℂ, ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, of p f = z • (Om p f : WOF F E nS nT → ℂ))
    (hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi) (p q : GAF σ JS × GAF σ JT) (f : WOF F E nS nT → ℂ)
    (hf : IsThetaFunOF σ JS JT ξ₀ B.ψ f) : of p (oi q f) = oi q (of p f) :=
  _root_.PositivityTheory.ThKW.fin_inf_comm_A_k C hO hof hi p q f hf
theorem datum_of_aut_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hO : _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om)
    (h1 : IsHeckeCharF η) (h2 : ResEtaF η 1) (hf : IsFinWeilF σ JS JT ξ₀ B.ψ (η ^ nS) (η ^ nT) of)
    (hof : ∀ p, ∃ z : ℂ, ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, of p f = z • (Om p f : WOF F E nS nT → ℂ))
    (hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi)
    (haut : ∀ γ ∈ GQF σ JS, ∀ γ' ∈ GQF σ JT, ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → of (γ, γ') (oi (γ, γ') f) 0 = f 0) :
    ∃ ω, IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ (η ^ nS) (η ^ nT) ω :=
  _root_.PositivityTheory.ThKW.datum_of_aut_A_k C hO h1 h2 hf hof hi haut
end PositivityTheory.ThKW
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LintegralEnormSqLatRepApplyEq
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LintegralSqOmK
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaSubspaceHaarIntegral
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsInvariantFormK
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil
noncomputable section
namespace GlobalTheory.ThetaMeanSquareF
theorem exists_invariant_form_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ M : Submodule ℂ (WOF F E nS nT → ℂ), (∀ f ∈ M, IsThetaFunOF σ JS JT ξ₀ B.ψ f) →
      ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ →
        ∃ Bf : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ, (∀ (u : WOF F E nS nT) (f g f' g' : M),
          (f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ u f → (g' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ u g →
            Bf f' g' = Bf f g) ∧
          ∀ f : M, ∫⁻ w in 𝓕, ‖(f : WOF F E nS nT → ℂ) w‖ₑ ^ 2 ∂μ = ENNReal.ofReal (Bf f f).re := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ M hM μ 𝓕 hμ h𝓕
  have hψ : IsCharAF F B.ψ := GlobalTheory.StdCharFromIsStd.isCharAF hB.std
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable (ratLF F E nS nT) := countable_of_discrete_addSubgroup _
  haveI := hμ
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hKc μ h𝓕⟩
  have hb : ∀ f ∈ M, ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C := fun f hf => by
    have hp : ∀ γ ∈ ratLF F E nS nT, ∀ w, ‖f (γ + w)‖ = ‖f w‖ := by
      rintro _ ⟨γ, rfl⟩ w
      exact (congrArg norm ((hM f hf).quasi γ w)).trans (by rw [norm_mul, hψ.2.1, one_mul])
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hM f hf).cont.continuousOn
    refine ⟨C, fun w => ?_⟩
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← hp γ hγ w]
    exact hC _ h
  obtain ⟨Bf, hBf, hN⟩ := GlobalTheory.ThetaMeanSquareForm.exists_form (μ.restrict 𝓕) M
    (fun f hf => (hM f hf).cont.measurable) hb
  refine ⟨Bf, fun u f g f' g' hf hg => ?_, hN⟩
  rw [hBf, hBf, hf, hg]
  have key := GlobalTheory.HeisOrtho.setIntegral_add_right (G := WOF F E nS nT) (ratLF F E nS nT) μ 𝓕 h𝓕
    (fun w => (f : WOF F E nS nT → ℂ) w * (starRingEnd ℂ) ((g : WOF F E nS nT → ℂ) w)) (by
      rintro _ ⟨γ, rfl⟩ w
      have h0 := GlobalTheory.HeisOrtho.mul_conj_of_norm_one (hψ.2.1 (-(symplOHF σ JS JT ξ₀ (ratWF γ) w)))
      have h1 := (hM f f.2).quasi γ w
      have h2 := (hM g g.2).quasi γ w
      show (f : WOF F E nS nT → ℂ) (ratWF γ + w) * (starRingEnd ℂ) ((g : WOF F E nS nT → ℂ) (ratWF γ + w)) = _
      rw [h1, h2, map_mul, mul_mul_mul_comm, h0, one_mul]) u
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  have h0 := GlobalTheory.HeisOrtho.mul_conj_of_norm_one (hψ.2.1 (symplOHF σ JS JT ξ₀ w u))
  show B.ψ (symplOHF σ JS JT ξ₀ w u) * (f : WOF F E nS nT → ℂ) (w + u) *
    (starRingEnd ℂ) (B.ψ (symplOHF σ JS JT ξ₀ w u) * (g : WOF F E nS nT → ℂ) (w + u)) = _
  rw [map_mul, mul_mul_mul_comm, h0, one_mul]
end GlobalTheory.ThetaMeanSquareF
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_subspace_haar_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ M : Submodule ℂ (WOF F E nS nT → ℂ), (∀ f ∈ M, IsThetaFunOF σ JS JT ξ₀ B.ψ f) →
      ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ →
        ∃ Bf : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ, (∀ (u : WOF F E nS nT) (f g f' g' : M),
          (f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ u f → (g' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ u g →
            Bf f' g' = Bf f g) ∧
          ∀ f : M, ∫⁻ w in 𝓕, ‖(f : WOF F E nS nT → ℂ) w‖ₑ ^ 2 ∂μ = ENNReal.ofReal (Bf f f).re := by
  first | exact @_root_.GlobalTheory.ThetaMeanSquareF.exists_invariant_form_k | exact _root_.GlobalTheory.ThetaMeanSquareF.exists_invariant_form_k | (intros; apply _root_.GlobalTheory.ThetaMeanSquareF.exists_invariant_form_k <;> assumption)
end
end

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil
noncomputable section
namespace GlobalTheory.FinLatUnitF
open GlobalTheory.FinLatF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
theorem lintegral_sq_Om_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
          IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ p f,
            ∫⁻ w in 𝓕, ‖(Om p f : WOF F E nS nT → ℂ) w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖(f : WOF F E nS nT → ℂ) w‖ₑ ^ 2 ∂μ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ0 hξ hc Λ w lam Om h μ 𝓕 hμ h𝓕 p f
  have hσ : ∀ x, σ (σ x) = x := sigma_sigma hB.cm
  have hn : ∀ a, ‖B.ψ a‖ = 1 := GlobalTheory.StdCharWeilDatum.norm_psi hB.std
  obtain ⟨Bf, hB1, hB2⟩ := _root_.GlobalTheory.T.theta_subspace_haar_integral F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hξ
    (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ) (fun _ hf => hf) μ 𝓕 hμ h𝓕
  rw [hB2, hB2, GlobalTheory.T.invariantForm_normalizedHeisenbergIntertwiner (isHeis_opFF hσ hS hT hξ hc h.hw) (fun x y => hn _) lam h.good _ h.sd h.span
    (rhoFF σ JS JT p) (gamFF_rhoFF hS ξ₀ B.ψ p) (h.sd' p) (h.fin p) (Om p) (h.op p) (h.vac p) Bf]
  intro x u v
  have h1 : ∀ u : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ, opFF hc w x u =
      phaseF σ JS JT ξ₀ B.ψ w x • (⟨heisOF σ JS JT ξ₀ B.ψ x u, hc x u u.2⟩ : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ) :=
    fun u => rfl
  have h2 : phaseF σ JS JT ξ₀ B.ψ w x * (starRingEnd ℂ) (phaseF σ JS JT ξ₀ B.ψ w x) = 1 := by
    rw [Complex.mul_conj', show ‖phaseF σ JS JT ξ₀ B.ψ w x‖ = 1 from hn _]; simp
  rw [h1, h1, Bf.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_smul, h2, one_smul]
  exact hB1 x u v _ _ rfl rfl
end GlobalTheory.FinLatUnitF
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_enorm_sq_latRep_apply_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
          IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ p f,
            ∫⁻ w in 𝓕, ‖(Om p f : WOF F E nS nT → ℂ) w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖(f : WOF F E nS nT → ℂ) w‖ₑ ^ 2 ∂μ := by
  first | exact @_root_.GlobalTheory.FinLatUnitF.lintegral_sq_Om_k | exact _root_.GlobalTheory.FinLatUnitF.lintegral_sq_Om_k | (intros; apply _root_.GlobalTheory.FinLatUnitF.lintegral_sq_Om_k <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutGen
section
noncomputable section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
namespace PositivityTheory.ThKW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}
theorem infinite_norm_one_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) : {t : E | t * σ t = 1}.Infinite :=
  _root_.UpperTheory.Reformulated.B.InfiniteNormOneField.infinite_norm_one_k C
theorem det_kron_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) :
    (b ⊗ₖ aᵀ).det * σ (b ⊗ₖ aᵀ).det = 1 ∧
      (b ⊗ₖ aᵀ).det * σ (b ⊗ₖ aᵀ - 1).det = (-1) ^ Fintype.card (Fin nT × Fin nS) * (b ⊗ₖ aᵀ - 1).det := by
  have hu : IsUnit JS.det := isUnit_iff_ne_zero.2 C.hS.2
  have hP : (JT ⊗ₖ JS⁻¹ᵀ).det ≠ 0 := by
    rw [det_kronecker, det_transpose]
    exact mul_ne_zero (pow_ne_zero _ C.hT.2) (pow_ne_zero _ (Matrix.isUnit_nonsing_inv_det JS hu).ne_zero)
  have hunitary {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : GAF σ J} {a}
      (h : IsRatF σ J g a) : (a.map σ)ᵀ * J * a = J := by
    have e := GenA.mt_unitary σ J g
    rw [show mtF σ J g = _ from h, GenA.map_unitary] at e
    exact Matrix.map_injective GenA.incAF_injective e
  exact GenA.det_unit_sig σ hP (GenA.kron_unit_sig σ hu (hunitary ha) (hunitary hb))
namespace GenR
theorem compAt_rat_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : GAF σ J} {a}
    (h : IsRatF σ J g a) (w : InfinitePlace F) : compAtF θ w (mtF σ J g) = a.map (tauB B w) := by
  rw [show mtF σ J g = _ from h]
  ext i j
  show θ w (infPartF F E (incAF F E (a i j))) = tauB B w (a i j)
  rw [GenA.infPart_incAF]
  exact (C.inf w).1 (a i j)
theorem cart_blk_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) {sS : InfinitePlace F → Matrix (Fin nS) (Fin nS) ℂ}
    {sT : InfinitePlace F → Matrix (Fin nT) (Fin nT) ℂ}
    (hS : ∀ w, Formalism.IndefR.Datum.IsCartanInv (JS.map (tauB B w)) (sS w))
    (hT : ∀ w, Formalism.IndefR.Datum.IsCartanInv (((2 * (tauB B w ξ₀).im : ℝ) : ℂ) • JT.map (tauB B w)) (sT w)) :
    CartF σ JS JT ξ₀ B θ (GlobalTheory.RealWeil.blk sT sS) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [GlobalTheory.RealWeil.blk_mul]
    simp only [fun w => (hS w).1, fun w => (hT w).1]
    exact GlobalTheory.RealWeil.blk_one
  · unfold HMF
    rw [GlobalTheory.RealWeil.blk_mul]
    refine GlobalTheory.RealWeil.blk_posDef (fun w => (hT w).2.2) fun w => ?_
    rw [← GlobalTheory.RealSymplForm.cartan_inv_mul (hS w)]
    exact (hS w).2.2.inv
  · intro k t hk
    rw [mMF_apply]
    refine GenA.blk_comm (fun w => ?_) (fun w => ?_)
    · rw [_root_.PositivityTheory.ThKW.GenR.compAt_rat_k C hk]
      have e : (t • (1 : Matrix (Fin nT) (Fin nT) E)).map (tauB B w) = tauB B w t • 1 := by
        ext i j
        by_cases hij : i = j <;> simp [hij]
      rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
    · have hone : compAtF θ w (mtF σ JS 1) = 1 := by
        rw [GenA.mt_one, compAtF, Matrix.map_one _ (map_zero _) (map_one _)]
      rw [inv_one, hone, Matrix.one_mul, Matrix.mul_one]
end GenR
theorem rat_gen_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (Q : GAF σ JS × GAF σ JT → Prop)
    (hm : ∀ p q, p.1 ∈ GQF σ JS → p.2 ∈ GQF σ JT → q.1 ∈ GQF σ JS → q.2 ∈ GQF σ JT → Q p → Q q → Q (p * q))
    (hs : ∀ p s, p.1 ∈ GQF σ JS → p.2 ∈ GQF σ JT → CartF σ JS JT ξ₀ B θ s →
      s * mMF σ JS JT θ p = mMF σ JS JT θ p * s → Q p) :
    ∀ p, p.1 ∈ GQF σ JS → p.2 ∈ GQF σ JT → Q p := by
  have hcm := C.good.cm
  have hσ := GlobalTheory.SplitDetCharF.sig_invol hcm
  obtain ⟨c, hc⟩ : ∃ c : E ≃ₐ[F] E, (c : E →ₐ[F] E) = σ :=
    ⟨AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ), rfl⟩
  subst hc
  have hmem {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : GAF (c : E →ₐ[F] E) J} {a}
      (hJ : IsHermND (c : E →ₐ[F] E) J) (h : IsRatF (c : E →ₐ[F] E) J g a) :
      g ∈ GQF (c : E →ₐ[F] E) J := by
    have e := GenA.mt_unitary (c : E →ₐ[F] E) J g
    rw [show mtF (c : E →ₐ[F] E) J g = _ from h, GenA.map_unitary] at e
    have hu : (a.map (c : E →ₐ[F] E))ᵀ * J * a = J :=
      Matrix.map_injective GenA.incAF_injective e
    exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero a (GenA.det_ne_of_unitary hJ hu), hu, Units.ext h.symm⟩
  have hone {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (w : InfinitePlace F) :
      compAtF θ w (mtF (c : E →ₐ[F] E) J 1) = 1 := by
    rw [GenA.mt_one, compAtF, Matrix.map_one _ (map_zero _) (map_one _)]
  have hr : ∀ w, (2 * (tauB B w ξ₀).im : ℝ) ≠ 0 := fun w => mul_ne_zero two_ne_zero (GenA.im_ne hcm C.h0 C.hξ _)
  have hcS : ∀ w, ∃ s, Formalism.IndefR.Datum.IsCartanInv (JS.map (tauB B w)) s := fun w => by
    simpa using GenA.cart_exists _ (GenA.herm_map hcm C.hS (tauB B w)) (GenA.det_map_ne C.hS (tauB B w)) 1 one_ne_zero
  have hcT : ∀ w, ∃ s, Formalism.IndefR.Datum.IsCartanInv (((2 * (tauB B w ξ₀).im : ℝ) : ℂ) • JT.map (tauB B w)) s :=
    fun w => GenA.cart_exists _ (GenA.herm_map hcm C.hT (tauB B w)) (GenA.det_map_ne C.hT (tauB B w)) _ (hr w)
  choose sS0 hS0 using hcS
  choose sT0 hT0 using hcT
  have Q11 : Q (1, 1) := hs (1, 1) (GlobalTheory.RealWeil.blk sT0 sS0) (one_mem _) (one_mem _) (_root_.PositivityTheory.ThKW.GenR.cart_blk_k C hS0 hT0)
    (by
      show _ * mMF _ JS JT θ 1 = mMF _ JS JT θ 1 * _
      rw [map_one, Matrix.mul_one, Matrix.one_mul])
  have hT : ∀ h ∈ GQF (c : E →ₐ[F] E) JT, Q (1, h) := by
    refine GenR.rat_ind c hcm C.hT (fun h => Q (1, h)) Q11 (fun g hg g' hg' a b => ?_) (fun g x u hx hg => ?_)
    · have := hm (1, g) (1, g') (one_mem _) hg (one_mem _) hg' a b
      rwa [Prod.mk_mul_mk, mul_one] at this
    · have := fun w => GenA.cart_refl (JT.map (tauB B w)) (GenA.herm_map hcm C.hT (tauB B w))
        (GenA.det_map_ne C.hT (tauB B w)) _ (hr w) (tauB B w ∘ x)
        (by rw [GenA.quad_map hcm c rfl]; exact (map_ne_zero _).2 hx) (tauB B w ((u - 1) / GlobalTheory.UnRep.hermE c JTᵀ x x))
      choose sT hT1 hT2 using this
      refine hs (1, g) (GlobalTheory.RealWeil.blk sT sS0) (one_mem _) (hmem C.hT hg) (_root_.PositivityTheory.ThKW.GenR.cart_blk_k C hS0 hT1) ?_
      rw [mMF_apply]
      refine GenA.blk_comm (fun w => ?_) (fun w => ?_)
      · rw [_root_.PositivityTheory.ThKW.GenR.compAt_rat_k C hg, GenA.refl_map hcm c rfl]
        exact hT2 w
      · rw [inv_one, hone, Matrix.one_mul, Matrix.mul_one]
  have hS : ∀ g ∈ GQF (c : E →ₐ[F] E) JS, Q (g⁻¹, 1) := by
    refine GenR.rat_ind c hcm C.hS (fun g => Q (g⁻¹, 1)) (by rw [inv_one]; exact Q11) (fun g hg g' hg' a b => ?_)
      (fun g x u hx hg => ?_)
    · have := hm (g'⁻¹, 1) (g⁻¹, 1) (inv_mem hg') (one_mem _) (inv_mem hg) (one_mem _) b a
      rwa [Prod.mk_mul_mk, mul_one, ← _root_.mul_inv_rev] at this
    · have := fun w => GenA.cart_refl (JS.map (tauB B w)) (GenA.herm_map hcm C.hS (tauB B w))
        (GenA.det_map_ne C.hS (tauB B w)) 1 one_ne_zero (tauB B w ∘ x)
        (by rw [GenA.quad_map hcm c rfl]; exact (map_ne_zero _).2 hx) (tauB B w ((u - 1) / GlobalTheory.UnRep.hermE c JSᵀ x x))
      choose sS hS1 hS2 using this
      have hS1' : ∀ w, Formalism.IndefR.Datum.IsCartanInv (JS.map (tauB B w)) (sS w) := fun w => by simpa using hS1 w
      refine hs (g⁻¹, 1) (GlobalTheory.RealWeil.blk sT0 sS) (inv_mem (hmem C.hS hg)) (one_mem _) (_root_.PositivityTheory.ThKW.GenR.cart_blk_k C hS1' hT0) ?_
      rw [mMF_apply, inv_inv]
      refine GenA.blk_comm (fun w => ?_) (fun w => ?_)
      · rw [hone, Matrix.one_mul, Matrix.mul_one]
      · rw [_root_.PositivityTheory.ThKW.GenR.compAt_rat_k C hg, GenA.refl_map hcm c rfl]
        exact (hS2 w).symm
  intro p h1 h2
  have e : p = (p.1, 1) * (1, p.2) := by
    rw [Prod.mk_mul_mk, mul_one, one_mul]
  have a1 : Q (p.1, 1) := by
    have := hS _ (inv_mem h1)
    rwa [inv_inv] at this
  rw [e]
  exact hm _ _ h1 (one_mem _) (one_mem _) h2 a1 (hT _ h2)
end PositivityTheory.ThKW
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsChartArchimedeanFamily
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsChartFK
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
namespace GlobalTheory.RealWeilF.CMChart
open _root_.Formalism.L2.Fam.ThC
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem exists_chartF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∃ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι := by
  intro F E _ _ _ _ _ σ B hB θ hθ
  refine exists_chart_of_cm hB.cm (fun w => (B.emb w).1) (fun w => ?_) θ hθ
  show InfinitePlace.mk ((B.emb w).1.comp (algebraMap F E)) = w
  rw [(B.emb w).2, InfinitePlace.mk_embedding]
end GlobalTheory.RealWeilF.CMChart
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chart_archimedean_family : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∃ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι := by
  first | exact @_root_.GlobalTheory.RealWeilF.CMChart.exists_chartF_k | exact _root_.GlobalTheory.RealWeilF.CMChart.exists_chartF_k | (intros; apply _root_.GlobalTheory.RealWeilF.CMChart.exists_chartF_k <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.FiniteLatticeThetaLevel
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LatRepFContK
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil
namespace GlobalTheory.FinLatF
theorem latRepF_cont_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ f (w : WOF F E nS nT), Continuous fun p : GAF σ JS × GAF σ JT => (Om p f : WOF F E nS nT → ℂ) w := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ _ hξ hc Λ w lam Om h f u
  have hσ : ∀ x, σ (σ x) = x := fun x => GlobalTheory.AdelicU.cm_conj_conj hB.cm x
  have H := isHeis_opFF hσ hS hT hξ hc h.hw
  have hfix : ∀ p : GAF σ JS × GAF σ JT, (∀ a ∈ latF F E nS nT Λ, rhoFF σ JS JT p a ∈ latF F E nS nT Λ) →
      ∀ e, Fixes (opFF hc w) (latF F E nS nT Λ) e → Om p e = e := by
    intro p hp e he
    rw [h.vac p e he]
    exact GlobalTheory.FinWeilO.normOp_of_le H lam (h.sd' p) (by rintro _ ⟨a, ha, rfl⟩; exact hp a ha) he
  have hev : ∀ f : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ, ∀ᶠ p in 𝓝 (1 : GAF σ JS × GAF σ JT), Om p f = f := by
    intro f
    have hf : f ∈ Submodule.span ℂ {m | ∃ x e, Fixes (opFF hc w) (latF F E nS nT Λ) e ∧ m = opFF hc w x e} := by
      rw [h.span]; trivial
    induction hf using Submodule.span_induction with
    | mem _ hm =>
      obtain ⟨x, e, he, rfl⟩ := hm
      obtain ⟨N, hN, hNl⟩ := h.lev (w • x)
      filter_upwards [h.near, h.near' x N hN] with p hp hp'
      obtain ⟨l, hl, hl'⟩ := hp'
      have e2 : gamFF σ JS JT ξ₀ B.ψ (w • x) (N • l) = 1 := by
        rw [gamFF, ← symplOHF_add_self, AddChar.map_add_eq_mul, XFF.coe_nsmul, hNl l hl, one_mul]
      have e4 := H.comp x (N • l) e
      rw [he _ (nsmul_mem hl N), e2, one_smul] at e4
      rw [h.op, hfix p hp e he, hl', ← e4]
    | zero => exact Filter.Eventually.of_forall fun p => map_zero _
    | add u v _ _ hu hv => filter_upwards [hu, hv] with p h3 h4 using by rw [map_add (f := _), h3, h4]
    | smul c u _ hu => filter_upwards [hu] with p h3 using by rw [map_smul, h3]
  haveI : IsTopologicalGroup (GAF σ JS) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : IsTopologicalGroup (GAF σ JT) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  refine continuous_iff_continuousAt.2 fun q => ?_
  have h1 : Filter.Tendsto (fun p => q⁻¹ * p) (𝓝 q) (𝓝 1) :=
    (continuous_const.mul continuous_id).tendsto' q 1 (inv_mul_cancel q)
  refine continuousAt_const.congr (f := fun _ => (Om q f : WOF F E nS nT → ℂ) u) ?_
  filter_upwards [h1.eventually (hev f)] with p hp
  conv_rhs => rw [← mul_inv_cancel_left q p, map_mul, Module.End.mul_apply, hp]
end GlobalTheory.FinLatF
end
end

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_lattice_theta_level : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ f (w : WOF F E nS nT), Continuous fun p : GAF σ JS × GAF σ JT => (Om p f : WOF F E nS nT → ℂ) w := by
  first | exact @_root_.GlobalTheory.FinLatF.latRepF_cont_k | exact _root_.GlobalTheory.FinLatF.latRepF_cont_k | (intros; apply _root_.GlobalTheory.FinLatF.latRepF_cont_k <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.FiniteLatticeThetaInvariant
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RealTriv
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil
noncomputable section
namespace GlobalTheory.FinLatF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
section Abstract
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R}
  {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}
end Abstract
variable {nS nT : ℕ}
theorem _root_.UpperTheory.TP.W.IsLatRepL.real_triv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ g ∈ GlobalTheory.WeilPartsF.GinfCF σ JS, ∀ h ∈ GlobalTheory.WeilPartsF.GinfCF σ JT, ∀ f, Om (g, h) f = f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ _ hξ hc Λ w lam Om hR g hg h hh f
  have hσ : ∀ z : E, σ (σ z) = z := fun z => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have H := isHeis_opFF hσ hS hT hξ hc hR.hw
  have key : Om (g, h) = LinearMap.id := by
    refine LinearMap.ext_on hR.span ?_
    rintro _ ⟨x, e, he, rfl⟩
    have hfix : Om (g, h) e = e := by
      rw [hR.vac _ e he]
      exact normOp_eq_self_of_le H lam (hR.sd' _)
        (by rintro _ ⟨a, ha, rfl⟩; rw [rhoFF_real hg hh]; exact ha) he
    rw [hR.op, rhoFF_real hg hh, hfix, LinearMap.id_apply]
  rw [key, LinearMap.id_apply]
end GlobalTheory.FinLatF
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_lattice_theta_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ g ∈ GlobalTheory.WeilPartsF.GinfCF σ JS, ∀ h ∈ GlobalTheory.WeilPartsF.GinfCF σ JT, ∀ f, Om (g, h) f = f := by
  first | exact @_root_.UpperTheory.TP.W.IsLatRepL.real_triv | exact _root_.UpperTheory.TP.W.IsLatRepL.real_triv | (intros; apply _root_.UpperTheory.TP.W.IsLatRepL.real_triv <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.FiniteLatticeThetaSupport
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsLatRepFHeisK
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil
noncomputable section
namespace GlobalTheory.FinLatHeis
open GlobalTheory.FinLatF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
end GlobalTheory.FinLatHeis
namespace GlobalTheory.FinLatHeis
open GlobalTheory.FinLatF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {ψ : AddChar (AF F) ℂ}
variable {hc : HeisClosedF σ JS JT ξ₀ ψ} {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {w : 𝓞 E}
  {lam : ℕ →* ℂ} {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ)}
theorem comm_k (hσ : ∀ x, σ (σ x) = x) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : σ ξ₀ = -ξ₀)
    (hR : _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ ψ hc Λ w lam Om)
    (L : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ →ₗ[ℂ] GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ)
    (hL : ∀ x v, L (opFF hc w x v) = opFF hc w x (L v))
    (p : GAF σ JS × GAF σ JT) (f : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ) : Om p (L f) = L (Om p f) := by
  have H := isHeis_opFF hσ hS hT hξ hc hR.hw
  have : Om p ∘ₗ L = L ∘ₗ Om p := by
    refine LinearMap.ext_on hR.span ?_
    rintro _ ⟨x, e, he, rfl⟩
    have he' : Fixes (opFF hc w) (latF F E nS nT Λ) (L e) := fun a ha => by rw [← hL, he a ha]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hL, hR.op, hR.op, hL, hR.vac p e he, hR.vac p _ he',
      GlobalTheory.FinWeilO.normOp_comm H lam (hR.sd' p) (hR.fin p) L hL he]
  exact LinearMap.congr_fun this f
theorem heis_fin_k (hS : IsHermND σ JS) (hR : _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ ψ hc Λ w lam Om)
    (p : GAF σ JS × GAF σ JT) (x : XFF F E nS nT) (f f' : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ)
    (hf : (f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ ψ x f) :
    (Om p f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ ψ (actOF σ JS JT p.1 p.2 x) (Om p f) := by
  have h1 : opFF hc w x f = phaseF σ JS JT ξ₀ ψ w x • f' := Subtype.ext (by rw [coe_opFF, Submodule.coe_smul, hf])
  have h2 := congrArg Subtype.val (hR.op p x f)
  rw [h1, map_smul, Submodule.coe_smul, coe_opFF, phaseF_rhoFF hS, coe_rhoFF] at h2
  exact smul_right_injective _ (phaseF_ne_zero w x) h2
end GlobalTheory.FinLatHeis
open GlobalTheory.FinLatF GlobalTheory.FinLatHeis in
theorem GlobalTheory.FinLatHeis.isLatRepF_heis_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ g ∈ GlobalTheory.WeilPartsF.GfCF σ JS, ∀ h ∈ GlobalTheory.WeilPartsF.GfCF σ JT, ∀ (w₀ : WOF F E nS nT)
          (f f' : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ),
          (f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ w₀ f →
          (Om (g, h) f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ (actOF σ JS JT g h w₀) (Om (g, h) f) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ _ hξ hc Λ w lam Om hR g hg h hh w₀ f f' hf
  have hσ : ∀ x, σ (σ x) = x := by
    intro x
    let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
    apply τ.injective
    rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]
  set r := realIdF F E
  let L : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ →ₗ[ℂ] GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ :=
    (heisLF σ JS JT ξ₀ B.ψ (r • w₀)).restrict fun f hf => hc _ f hf
  have hL : ∀ m, (L m : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ (r • w₀) m := fun _ => rfl
  have hLop : ∀ x v, L (opFF hc w x v) = opFF hc w x (L v) := fun x v => Subtype.ext (by
    rw [hL, coe_opFF, coe_opFF, hL, GlobalTheory.WeilPartsF.heisOF_smul, heisOF_heisOF', heisOF_heisOF',
      symplOHF_real_fin hσ ξ₀ w₀ x.fin, symplOHF_fin_real hσ hS hT hξ w₀ x.fin, add_comm])
  let f₁ : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ := ⟨_, hc ((1 - r) • w₀) f f.2⟩
  have hf' : f' = L f₁ := Subtype.ext (by
    rw [hf, hL]
    show heisOF σ JS JT ξ₀ B.ψ w₀ f = heisOF σ JS JT ξ₀ B.ψ (r • w₀) (heisOF σ JS JT ξ₀ B.ψ ((1 - r) • w₀) f)
    rw [heisOF_heisOF', symplOHF_real_fin hσ ξ₀ w₀ (fin_part w₀), AddChar.map_zero_eq_one, one_smul, ← decomp])
  have h1 := _root_.GlobalTheory.FinLatHeis.heis_fin_k hS hR (g, h) (XFF.mk _ (fin_part w₀)) f f₁ rfl
  rw [XFF.coe_mk] at h1
  rw [hf', _root_.GlobalTheory.FinLatHeis.comm_k hσ hS hT hξ hR L hLop, hL, h1, heisOF_heisOF',
    symplOHF_real_fin hσ ξ₀ w₀ (actOF_mem_finSubF g h (fin_part w₀)), AddChar.map_zero_eq_one, one_smul]
  congr 1
  conv_rhs => rw [decomp w₀, actOF_add, actOF_real hg hh]
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_lattice_theta_support : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ g ∈ GlobalTheory.WeilPartsF.GfCF σ JS, ∀ h ∈ GlobalTheory.WeilPartsF.GfCF σ JT, ∀ (w₀ : WOF F E nS nT)
          (f f' : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ),
          (f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ w₀ f →
          (Om (g, h) f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ (actOF σ JS JT g h w₀) (Om (g, h) f) := by
  first | exact @_root_.GlobalTheory.FinLatHeis.isLatRepF_heis_k | exact _root_.GlobalTheory.FinLatHeis.isLatRepF_heis_k | (intros; apply _root_.GlobalTheory.FinLatHeis.isLatRepF_heis_k <;> assumption)
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA
namespace UpperTheory.TP.W
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}
variable {η κ χS χT : (AEF F E)ˣ →* Circle} {ε : AEF F E} {of oi : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)}
open GlobalTheory.FinLatSplitF in
theorem splitK_k (hI : IdxSign) (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hL : _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om)
    (hκ : IsKap σ lam κ) {e : AEF F E} (he : IsSplitIdemF σ e) {g k} (hg : SuppAtF σ e JS g) (hk : SuppAtF σ e JT k) {x y}
    (hx : IsDetAtF σ e JS g x) (hy : IsDetAtF σ e JT k y) : ∃ r : ℝ, 0 < r ∧ ∀ ℓ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WOF F E nS nT, (∀ i j, cAF σ e * u i j = u i j) → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
        ℓ (heisOF σ JS JT ξ₀ B.ψ u f) = ℓ f) →
      ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, ℓ (Om (g, k) f) = ((κ x ^ nT * κ y ^ nS : Circle) : ℂ) * ((r : ℂ) * ℓ f) := by
  have hB := C.good
  have hS := C.hS
  have hT := C.hT
  have hξ := C.hξ
  have hσ : ∀ x, σ (σ x) = x := conj_conj_of_cm hB.cm
  have he' : IsSplitIdemF σ (cAF σ e) := isSplitIdemF_conj he
  have hm : ∀ (a b : AEF F E) (x : XFF F E nS nT), mulFF a (mulFF b x) = (a * b) • x := fun a b x => smul_smul a b x
  have hcm : ∀ (a : AEF F E) (x : XFF F E nS nT),
      rhoFF σ JS JT (g, k) (mulFF a x) = mulFF a (rhoFF σ JS JT (g, k) x) :=
    fun a x => XFF.ext (actOF_smul _ _ _ _)
  obtain ⟨n, hn, hℓ⟩ := GlobalTheory.T.invariantForm_normalizedHeisenbergIntertwiner_eq (isHeis_opFF hσ hS hT hξ hc hL.hw) lam _ hL.sd hL.span (rhoFF σ JS JT (g, k))
    (gamFF_rhoFF hS ξ₀ B.ψ _) (hL.sd' _) (hL.fin _) (Om (g, k)) (hL.op _) (hL.vac _) (mulFF e) (mulFF (cAF σ e))
    (fun x => by rw [hm, he.1]; rfl) (fun x => by rw [hm, he'.1]; rfl)
    (fun x => by rw [hm, he.2.1, zero_smul]) (fun x => by rw [hm, mul_comm, he.2.1, zero_smul])
    (fun x y => by rw [gamFF, gamFF, coe_mulFF, coe_mulFF, symplOF_smul σ JS JT hσ])
    (fun a ha => (hL.splitStab e he a ha).1) (fun a ha => (hL.splitStab e he a ha).2) (hcm e) (hcm _)
    (fun x => XFF.ext (by
      have := off_smul_actOF hg hk (x : WOF F E nS nT)
      rw [sub_smul, sub_smul, add_smul, add_smul, one_smul, one_smul, ← sub_sub, ← sub_sub] at this
      exact this))
  have hi := hL.fin (g, k)
  have hl := hI F E σ hB.cm nS nT JS JT hS hT ξ₀ hξ B.ψ hc w hL.hw Λ hG hL.sd' hL.fin lam hL.good κ hκ e he g k hg hk x y hx hy
  refine ⟨(Real.sqrt (idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, k))) : ℕ))⁻¹ * n,
    mul_pos (inv_pos.2 (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hi)))) (Nat.cast_pos.2 hn),
    fun ℓ h1 f => ?_⟩
  have := hℓ (ℓ ∘ₗ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ).subtype) (fun u m => by
    have hu : ((mulFF (cAF σ e) u : XFF F E nS nT) : WOF F E nS nT) ∈ GlobalTheory.SplitInvFormF.conjHalf σ e nS nT :=
      fun i j => by
        show cAF σ e * (cAF σ e * (u : WOF F E nS nT) i j) = cAF σ e * (u : WOF F E nS nT) i j
        rw [← mul_assoc, he'.1]
    have hwu : (intAF F w • ((mulFF (cAF σ e) u : XFF F E nS nT) : WOF F E nS nT)) ∈
        GlobalTheory.SplitInvFormF.conjHalf σ e nS nT := fun i j => by
      show cAF σ e * (intAF F w * (cAF σ e * (u : WOF F E nS nT) i j)) =
        intAF F w * (cAF σ e * (u : WOF F E nS nT) i j)
      rw [mul_left_comm, ← mul_assoc (cAF σ e), he'.1]
    show ℓ (opFF hc w (mulFF (cAF σ e) u) m : WOF F E nS nT → ℂ) = ℓ m
    rw [coe_opFF, phaseF, GlobalTheory.SplitInvFormF.symplOHF_half he hwu hu, neg_zero, AddChar.map_zero_eq_one, one_smul]
    exact h1 _ hu _ m.2) f
  have hz : ∀ z : Circle, z * z = 1 → ((z : ℂ))⁻¹ = z := fun z hz => by
    rw [← Circle.coe_inv, inv_eq_of_mul_eq_one_right hz]
  rw [hl, mul_inv, hz _ (by rw [mul_mul_mul_comm, ← mul_pow, ← mul_pow, hκ.sq, hκ.sq, one_pow, one_pow, one_mul])] at this
  refine this.trans ?_
  generalize ((κ x ^ nT * κ y ^ nS : Circle) : ℂ) = c
  push_cast
  show _ * (ℓ (f : WOF F E nS nT → ℂ)) = _
  ring
theorem existsFinK_k (hI : IdxSign) (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hO : _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om)
    (h1 : IsHeckeCharF η) (h2 : ResEtaF η 1) (hκ : IsKap σ lam κ) (hε : IsHalfF σ ε) :
    ∃ of, IsFinWeilF σ JS JT ξ₀ B.ψ (η ^ nS) (η ^ nT) of ∧
      ∀ p (f : thetaSubF σ JS JT ξ₀ B.ψ), of p f = (zF σ JS JT (η * κ) ε hε.idem p : ℂ) • (Om p f : WOF F E nS nT → ℂ) := by
  have hcn : ∀ n : ℕ, Continuous ((η * κ) ^ n : (AEF F E)ˣ →* Circle) := fun n =>
    ((h1.1.mul hκ.cont).pow n).congr fun x => by simp
  have h2' := resEta_mul h2 hκ
  have hB := C.good
  have hreal := _root_.GlobalTheory.T.finite_lattice_theta_invariant F E σ B hB nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ hc Λ w lam Om hO
  have hheis := _root_.GlobalTheory.T.finite_lattice_theta_support F E σ B hB nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ hc Λ w lam Om hO
  have hcont := _root_.GlobalTheory.T.finite_lattice_theta_level F E σ B hB nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ hc Λ w lam Om hO
  have hunit := _root_.GlobalTheory.T.lintegral_enorm_sq_latRep_apply_eq F E σ B hB nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ hc Λ w lam Om hO
  let z : GAF σ JS × GAF σ JT → Circle := zF σ JS JT (η * κ) ε hε.idem
  have z1 : z 1 = 1 := by simp [z, zF]
  have z2 : ∀ p q, z (p * q) = z p * z q := fun p q => by
    simp only [z, zF, Prod.fst_mul, Prod.snd_mul, map_mul, _root_.mul_inv]
    exact mul_mul_mul_comm _ _ _ _
  have z3 : Continuous z := by
    show Continuous fun p : GAF σ JS × GAF σ JT =>
      (((η * κ) ^ nT) (GlobalTheory.SplitDetCharF.cutDet σ JS ε hε.idem p.1))⁻¹ * ((η * κ) ^ nS) (GlobalTheory.SplitDetCharF.cutDet σ JT ε hε.idem p.2)
    exact ((hcn nT).comp ((GlobalTheory.SplitDetCharF.continuous_cutDet ε hε.idem).comp continuous_fst)).inv.mul
      ((hcn nS).comp ((GlobalTheory.SplitDetCharF.continuous_cutDet ε hε.idem).comp continuous_snd))
  obtain ⟨om, hom⟩ := exists_extend (thetaSubF σ JS JT ξ₀ B.ψ)
    ({ toFun := fun p => (z p : ℂ) • Om p
       map_one' := by rw [z1, Circle.coe_one, one_smul, map_one]
       map_mul' := fun p q => by rw [z2, map_mul, Circle.coe_mul, smul_mul_smul_comm] } :
      GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ))
  have ho : ∀ p f (hf : IsThetaFunOF σ JS JT ξ₀ B.ψ f),
      om p f = (z p : ℂ) • (Om p ⟨f, hf⟩ : WOF F E nS nT → ℂ) :=
    fun p f hf => hom p ⟨f, hf⟩
  refine ⟨om, ⟨⟨fun p f hf => ?_, fun f hf u => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_⟩, fun g hg k hk f hf => ?_,
    fun g hg k hk u f hf => ?_, fun e he g k hg hk x y hx hy => ?_⟩, fun p f => hom p f⟩
  · rw [ho p f hf]
    exact (thetaSubF σ JS JT ξ₀ B.ψ).smul_mem _ (Om p ⟨f, hf⟩).2
  · simp only [ho _ f hf, Pi.smul_apply, smul_eq_mul]
    exact (continuous_subtype_val.comp z3).mul (hcont ⟨f, hf⟩ u)
  · rw [← hunit μ 𝓕 hμ h𝓕 p ⟨f, hf⟩, ho p f hf]
    refine lintegral_congr fun u => ?_
    rw [Pi.smul_apply, enorm_smul, ← ofReal_norm_eq_enorm (z p : ℂ), Circle.norm_coe, ENNReal.ofReal_one, one_mul]
  · rw [ho _ f hf, hreal g hg k hk, show z (g, k) = 1 by
      simp [z, zF, GlobalTheory.SplitDetCharF.cutDet_real ε hε.idem hε.fin g hg, GlobalTheory.SplitDetCharF.cutDet_real ε hε.idem hε.fin k hk],
      Circle.coe_one, one_smul]
  · have hf' := GlobalTheory.T.heisenbergOperatorF_preserves_isThetaFunction F E σ nS nT JS JT ξ₀ B.ψ hB.std.1 u f hf
    rw [ho _ f hf, ho _ _ hf', heisOF_smul, hheis g hg k hk u ⟨f, hf⟩ ⟨_, hf'⟩ rfl]
  · obtain ⟨r, hr, h1⟩ := _root_.UpperTheory.TP.W.splitK_k hI C hG hO hκ he hg hk hx hy
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    rw [ho _ f hf, map_smul, h1 ℓ hℓ, smul_eq_mul,
      show z (g, k) = splitFacOF (η ^ nS) (η ^ nT) x y * (κ x ^ nT * κ y ^ nS)⁻¹ by
        simp only [z, zF, splitFacOF, _root_.PositivityTheory.ThKW.cut_char_k hB C.hS (resEtaF_pow h2' nT) hε he hg hx,
          _root_.PositivityTheory.ThKW.cut_char_k hB C.hT (resEtaF_pow h2' nS) hε he hk hy]
        have e1 : (κ y ^ nS)⁻¹ = κ y ^ nS := inv_eq_of_mul_eq_one_right (by rw [← mul_pow, hκ.sq, one_pow])
        simp only [MonoidHom.pow_apply, MonoidHom.mul_apply, mul_pow, _root_.mul_inv, e1]
        exact mul_mul_mul_comm _ _ _ _, Circle.coe_mul, Circle.coe_inv, mul_assoc,
      inv_mul_cancel_left₀ (Circle.coe_ne_zero _)]
    ring
structure PartsK_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hc : HeisClosedF σ JS JT ξ₀ B.ψ) (lam : ℕ →* ℂ)
    (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)) (η χS χT : (AEF F E)ˣ →* Circle) (ε : AEF F E)
    (of oi : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)) : Prop where
  res : ResEtaF η 1
  half : IsHalfF σ ε
  prod : ∀ (x : E) (k : ℕ), x ≠ 0 → (k : ℚ) = |Algebra.norm ℚ x| → ∀ y : (AEF F E)ˣ,
      (y : AEF F E) = (ε + cAF σ ε) * incAF F E x + (1 - (ε + cAF σ ε)) →
        ∃ r : ℝ, 0 < r ∧ (η y : ℂ) * lam k * ∏ v, tauB B v x = r
  hf : IsFinWeilF σ JS JT ξ₀ B.ψ χS χT of
  hof : ∀ p (f : thetaSubF σ JS JT ξ₀ B.ψ), of p f = (zF σ JS JT η ε half.idem p : ℂ) • (Om p f : WOF F E nS nT → ℂ)
  hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi
  vac : ∀ s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ, s * s = 1 → (HMF JS JT ξ₀ (tauB B) * s).PosDef → ∀ p,
      s * mMF σ JS JT θ p = mMF σ JS JT θ p * s → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsVacF σ JS JT ξ₀ B.ψ ι s f →
        oi p f = GlobalTheory.RealWeil.dP s (mMF σ JS JT θ p) • f
theorem PartsK_k.prod' {C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι} (P : _root_.UpperTheory.TP.W.PartsK_k C hc lam Om η χS χT ε of oi) {N x : E} (hN : N ≠ 0) (hx : x ≠ 0)
    {c n : ℕ} (h : ((c * n : ℕ) : ℚ) = |Algebra.norm ℚ (N * x)|) : ∃ r : ℝ, 0 < r ∧
      (η (cutRat _ (_root_.PositivityTheory.ThKW.half_add_k C.good P.half) (Units.mk0 _ hN * Units.mk0 _ hx)) : ℂ) * (lam c * lam n) *
        ((∏ v, tauB B v N) * ∏ v, tauB B v x) = r := by
  obtain ⟨r, p, e⟩ := P.prod _ _ (mul_ne_zero hN hx) h (cutRat _ (_root_.PositivityTheory.ThKW.half_add_k C.good P.half) (Units.mk0 _ hN * Units.mk0 _ hx))
    (by rw [cutRat_val, add_comm, Units.val_mul, Units.val_mk0, Units.val_mk0])
  refine ⟨r, p, ?_⟩
  rw [← e, map_mul lam, ← Finset.prod_mul_distrib]
  simp only [map_mul]
theorem PartsK_k.kappa {C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι} (P : _root_.UpperTheory.TP.W.PartsK_k C hc lam Om η χS χT ε of oi)
    (hO : _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om) (hs : CartF σ JS JT ξ₀ B θ s) {g : GAF σ JS} {h : GAF σ JT}
    (hcm : s * mMF σ JS JT θ (g, h) = mMF σ JS JT θ (g, h) * s) {c : ℂ} (hc0 : c ≠ 0) (H : IsScalarF B ξ₀ of oi (g, h) c)
    (f : thetaSubF σ JS JT ξ₀ B.ψ) (f1 : Fixes (opFF hc w) (latF F E nS nT Λ) f) (f2 : IsVacF σ JS JT ξ₀ B.ψ ι s f)
    (x : WOF F E nS nT) :
    (f : WOF F E nS nT → ℂ) (actOF σ JS JT g⁻¹ h⁻¹ x) = (c⁻¹ * GlobalTheory.RealWeil.dP s (mMF σ JS JT θ (g, h)) *
      zF σ JS JT η ε P.half.idem (g, h) *
      (lam (idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h)))))⁻¹) *
      ((sumOp (opFF hc w) (latF F E nS nT Λ)
        ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))) f : thetaSubF σ JS JT ξ₀ B.ψ) : WOF F E nS nT → ℂ) x := by
  have e1 := congrFun (H f f.2) x
  rw [P.vac s hs.sq hs.pos (g, h) hcm f f.2 f2, map_smul, P.hof, hO.vac _ f f1, normOp, Submodule.coe_smul] at e1
  simp only [Pi.smul_apply, smul_eq_mul, substF_apply] at e1
  rw [← one_mul (f.1 _), ← inv_mul_cancel₀ hc0, mul_assoc, ← e1]
  ring
theorem scalar_constK_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om) (P : _root_.UpperTheory.TP.W.PartsK_k C hc lam Om η χS χT ε of oi) (hs : CartF σ JS JT ξ₀ B θ s) :
    ∃ e s₀ : ℂ, s₀ ≠ 0 ∧ ∀ g h a b, IsRatF σ JS g a → IsRatF σ JT h⁻¹ b →
      s * mMF σ JS JT θ (g, h) = mMF σ JS JT θ (g, h) * s → (b ⊗ₖ aᵀ - 1).det ≠ 0 →
      ∀ c : ℂ, c ≠ 0 → IsScalarF B ξ₀ of oi (g, h) c → ∃ r : ℝ, 0 < r ∧ c * e = r * s₀ := by
  refine ⟨(-s).det, η (cutRat ε P.half.idem ((-1) ^ Fintype.card (Fin nT × Fin nS))), Circle.coe_ne_zero _,
    fun g h a b ha hb hcm hd c hc0 H => ?_⟩
  obtain ⟨d1, d2⟩ := _root_.PositivityTheory.ThKW.det_kron_k C ha hb
  have hΔ := left_ne_zero_of_mul_eq_one d1
  obtain ⟨hbij, n, t, c₀, N, M, hn, hc₀, hN, t1, t2, g1, g2, i1, i2⟩ := _root_.PositivityTheory.ThKW.finite_data_k C hG hR hO ha hb hΔ hd
  obtain ⟨hI, hδ0, r₂, p₂, h2⟩ := _root_.PositivityTheory.ThKW.real_data_k C hs ha hb hcm hd
  obtain ⟨r₁, p₁, h1⟩ := _root_.PositivityTheory.ThKW.gauss_mul_integral_k C hG hR hO hs ha hb hbij hI _ (P.kappa hO hs hcm hc0 H) n t t1 t2
  rw [g1] at h1
  have hN' : (N : E) ^ M ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hN)
  obtain ⟨r₃, p₃, h3⟩ := P.prod' hN' hd i1
  obtain ⟨r₄, p₄, h4⟩ := P.prod' hN' hΔ i2
  exact GlobalTheory.RatAut.final_algebra p₁ p₂ p₃ p₄ hn hc0 hδ0 (Circle.coe_ne_zero _) h1 h2 h3 h4 g2
    (_root_.PositivityTheory.ThKW.phase_rat_k C P.res P.half hΔ hd hN' d1 d2 (_root_.PositivityTheory.ThKW.zF_rat_k C P.half.idem ha hb hΔ))
set_option maxHeartbeats 1000000 in
theorem isScalar_one_of_commK_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om) (P : _root_.UpperTheory.TP.W.PartsK_k C hc lam Om η χS χT ε of oi) (hs : CartF σ JS JT ξ₀ B θ s)
    {g : GAF σ JS} {h : GAF σ JT} (hg : g ∈ GQF σ JS) (hh : h ∈ GQF σ JT)
    (hcm : s * mMF σ JS JT θ (g, h) = mMF σ JS JT θ (g, h) * s) : IsScalarF B ξ₀ of oi (g, h) 1 := by
  obtain ⟨a, ha⟩ := exists_isRatF hg
  obtain ⟨b, hb⟩ := exists_isRatF (inv_mem hh)
  obtain ⟨e, s₀, hs₀, H⟩ := _root_.UpperTheory.TP.W.scalar_constK_k C hG hR hO P hs
  obtain ⟨t, ht, ht'⟩ := (_root_.PositivityTheory.ThKW.infinite_norm_one_k C).exists_notMem_finite
    ((GlobalTheory.RatAut.finite_det_smul_sub_one (b ⊗ₖ aᵀ)).union (GlobalTheory.RatAut.finite_det_smul_sub_one
      ((1 : Matrix (Fin nT) (Fin nT) E) ⊗ₖ (1 : Matrix (Fin nS) (Fin nS) E)ᵀ)))
  rw [Set.mem_union, not_or] at ht'
  obtain ⟨k, rk⟩ := exists_of_unitary (σ := σ) C.hT (a := t • 1) (by
    have e : ((t • (1 : Matrix (Fin nT) (Fin nT) E)).map σ)ᵀ = σ t • 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij)]
    rw [e, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, show t * σ t = 1 from ht, one_smul])
  have hk := rk.mem
  have hcomm := _root_.PositivityTheory.ThKW.fin_inf_comm_k C hO (fun p => ⟨_, P.hof p⟩) P.hi
  have ck : s * mMF σ JS JT θ (1, k⁻¹) = mMF σ JS JT θ (1, k⁻¹) * s := by
    have := comm_inv (mMF σ JS JT θ) (hs.cen k t rk)
    rwa [Prod.inv_mk, inv_one] at this
  obtain ⟨c, hc1, sc⟩ := _root_.PositivityTheory.ThKW.exists_isScalarF_k (p := (g, h)) C P.hf P.hi hg hh
  obtain ⟨c', hc', sc'⟩ := _root_.PositivityTheory.ThKW.exists_isScalarF_k (p := (1, k⁻¹)) C P.hf P.hi (one_mem _) (inv_mem hk)
  have hc0 : c ≠ 0 := norm_ne_zero_iff.1 (hc1 ▸ one_ne_zero)
  have hc0' : c' ≠ 0 := norm_ne_zero_iff.1 (hc' ▸ one_ne_zero)
  obtain ⟨r', p', e'⟩ := H 1 k⁻¹ 1 (t • 1) (isRatF_one JS) (by rwa [inv_inv]) ck
    (by rw [Matrix.smul_kronecker]; exact ht'.2) c' hc0' sc'
  obtain ⟨r, p, e''⟩ := H (g * 1) (h * k⁻¹) a (t • b) (by rwa [mul_one])
    (by
      have := rk.mul hb
      rwa [Matrix.smul_mul, Matrix.one_mul, ← inv_inv k, ← _root_.mul_inv_rev] at this)
    (by rw [← Prod.mk_mul_mk, map_mul, ← mul_assoc, hcm, mul_assoc, ck, mul_assoc])
    (by rw [Matrix.smul_kronecker]; exact ht'.1) (c * c') (mul_ne_zero hc0 hc0')
    (sc.mul_k C P.hi hcomm sc' (one_mem _) (inv_mem hk))
  have q' : (r' : ℂ) ≠ 0 := by exact_mod_cast p'.ne'
  have e1 : c = ((r / r' : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, eq_div_iff q']
    refine mul_right_cancel₀ hs₀ ?_
    rw [← e'', mul_assoc, ← e', mul_assoc]
  have e2 : r / r' = 1 := by
    rw [e1, Complex.norm_real, Real.norm_of_nonneg (div_pos p p').le] at hc1
    exact hc1
  rwa [e1, e2, Complex.ofReal_one] at sc
theorem datumK_of_k (hK : KapEx) (hE : EtaProdK) (hI : IdxSign) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E), GoodLat Λ → RatSD σ JS JT ξ₀ Λ →
      ∀ (hc : HeisClosedF σ JS JT ξ₀ B.ψ) (w : 𝓞 E) (lam : ℕ →* ℂ)
        (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)), _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om →
      ∀ η : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF η → ResEtaF η 1 → HasExp B.emb η (fun _ => 1) → UnramInert σ η →
        ∃ ω, IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ (η ^ nS) (η ^ nT) ω := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ h0 hξ Λ hG hR hc w lam Om hO η h1 h2 h3 h4
  obtain ⟨θ, hθ⟩ := (_root_.GlobalTheory.T.standard_additive_character_sign F E σ B hB).2.1
  obtain ⟨ι, hι⟩ := _root_.GlobalTheory.T.exists_chart_archimedean_family F E σ B hB θ hθ
  have C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι := ⟨hB, hS, hT, h0, hξ, hθ, hι⟩
  obtain ⟨κ, hκ⟩ := hK F E σ hB.cm lam hO.good
  obtain ⟨ε, hε, hprod⟩ := hE F E σ B hB.cm hB.unram η h1 h2 h3 h4 lam hO.good κ hκ
  obtain ⟨of, hf, hof⟩ := _root_.UpperTheory.TP.W.existsFinK_k hI C hG hO h1 h2 hκ hε
  obtain ⟨oi, hi, hvac⟩ := _root_.PositivityTheory.ThKW.exists_inf_k C
  have P : _root_.UpperTheory.TP.W.PartsK_k C hc lam Om (η * κ) (η ^ nS) (η ^ nT) ε of oi := ⟨resEta_mul h2 hκ, hε, hprod, hf, hof, hi, hvac⟩
  have hcomm := _root_.PositivityTheory.ThKW.fin_inf_comm_k C hO (fun p => ⟨_, hof p⟩) hi
  refine _root_.PositivityTheory.ThKW.datum_of_aut_k C hG hO h1 h2 hf (fun p => ⟨_, hof p⟩) hi fun γ hγ γ' hγ' f hf' => ?_
  have := _root_.PositivityTheory.ThKW.rat_gen_k C (fun p => IsScalarF B ξ₀ of oi p 1)
    (fun p q _ _ q1 q2 a b => mul_one (1 : ℂ) ▸ a.mul_k C hi hcomm b q1 q2)
    (fun p s p1 p2 hs hcm => _root_.UpperTheory.TP.W.isScalar_one_of_commK_k C hG hR hO P hs p1 p2 hcm) (γ, γ') hγ hγ' f hf'
  rw [this, one_smul]
  show f (actOF σ JS JT γ⁻¹ γ'⁻¹ 0) = f 0
  rw [actOF, Matrix.mul_zero, Matrix.zero_mul]
end UpperTheory.TP.W
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open PositivityTheory.ThKW PositivityTheory.ThKW.AutEtaA
theorem UpperTheory.TP.W.datumK_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E), GoodLat Λ → RatSD σ JS JT ξ₀ Λ →
      ∀ (hc : HeisClosedF σ JS JT ξ₀ B.ψ) (w : 𝓞 E) (lam : ℕ →* ℂ)
        (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)), _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om →
      ∀ η : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF η → ResEtaF η 1 → HasExp B.emb η (fun _ => 1) → UnramInert σ η →
        ∃ ω, IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ (η ^ nS) (η ^ nT) ω :=
  _root_.UpperTheory.TP.W.datumK_of_k UpperTheory.TP.W.kapEx UpperTheory.TP.W.etaProdK (UpperTheory.TP.W.idxSign UpperTheory.TP.W.cardDet UpperTheory.TP.W.idxHalf)
end
