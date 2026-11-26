module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfIsSmoothModerate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonsplitCentraliserNormElement
public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticCharpolySelfReciprocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramKernelSignNonsplitBaseChangeEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilIntegralPointSkewLatticeUnitVectorSameEigen
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianIsSchwartzFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarScalingMultiplicative
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.AdeleUnitModule

open scoped Pointwise ENNReal

theorem map_smul_eq_inv_smul {G A : Type} [Group G] [AddCommGroup A] [DistribMulAction G A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A]
    [ContinuousConstSMul G A] [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure] (g : G) :
    μ.map (fun x => g • x) = ((distribHaarChar A g : ℝ≥0∞))⁻¹ • μ := by
  have h1 : DomMulAct.mk g⁻¹ • μ = μ.map (fun x => g • x) := by
    ext s hs
    rw [Measure.domSMul_apply, Measure.map_apply (measurable_const_smul g) hs, Set.preimage_smul]
    simp
  have h2 := Measure.isAddLeftInvariant_eq_smul (DomMulAct.mk g⁻¹ • μ) μ
  rw [addHaarScalarFactor_smul_eq_distribHaarChar μ g⁻¹, map_inv (distribHaarChar A)] at h2
  rw [← h1, h2, ENNReal.smul_def, ENNReal.coe_inv (distribHaarChar_pos).ne']

open GroundTheory.Global GroundTheory.Global.AdeleBaseChange

theorem distribHaarChar_eq_absE (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTopologicalRing (AE F E)] [LocallyCompactSpace (AE F E)] [SecondCountableTopology (AE F E)] [T2Space (AE F E)]
    (t : (AE F E)ˣ) : distribHaarChar (AE F E) t = absE F E t := by
  have : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  have := IsModuleTopology.toContinuousSMul (AF F) (AE F E)
  have : IsModuleTopology (AF F) (AdeleRing (𝓞 E) E) := isModuleTopology_adeleRing
  let φ : AE F E ≃ₜ+ AdeleRing (𝓞 E) E :=
    { (adeleTensorAlgEquivLeft F E).toAddEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap (adeleTensorAlgEquivLeft F E).toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap (adeleTensorAlgEquivLeft F E).symm.toLinearMap }
  haveI : SecondCountableTopology (AdeleRing (𝓞 E) E) := φ.symm.toHomeomorph.secondCountableTopology
  haveI : T2Space (AdeleRing (𝓞 E) E) := φ.symm.toHomeomorph.isEmbedding.t2Space
  have h1 : distribHaarChar (AdeleRing (𝓞 E) E) (GlobalTheory.IdeleLogHom.toE F E t) = distribHaarChar (AE F E) t :=
    GlobalTheory.JR.ModuleNorm.distribHaarChar_transport φ t (GlobalTheory.IdeleLogHom.toE F E t) (fun x => by
      change adeleTensorAlgEquivLeft F E ((t : AE F E) * x) = _
      rw [map_mul]
      rfl)
  apply NNReal.eq
  rw [← h1, GlobalTheory.ModuAdele.distribHaarChar_adeleRing, GlobalTheory.IdeleLogHom.absE_eq_ideleModule]

theorem map_mul_eq_absE_inv_smul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ [MeasurableSpace (AE F E)] [BorelSpace (AE F E)] (ν : Measure (AE F E)), ν.IsAddHaarMeasure →
  ∀ t : (AE F E)ˣ, ν.map (fun x => (t : AE F E) * x) = ((absE F E t : ENNReal))⁻¹ • ν := by
  intro F E _ _ _ _ _ σ _ _ _ ν _ t
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  have h := map_smul_eq_inv_smul ν t
  rw [distribHaarChar_eq_absE] at h
  exact h

end GlobalTheory.AdeleUnitModule
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnThetaKernelDefiniteSeesawStage
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnThetaKernelDefiniteSeesawStage
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.SqTower

theorem integrableOn_ker'_of_stage_zero : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (W : G.Weil) (i j : Fin D.R.m) (p : ℕ)
    (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p 0 X →
    ∀ (t : T) (P' : PolF D WW.rank A'.rank) (h : GA D WW), MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m' := by
  intro D T Lc sc G W i j p A A' WW X hX t P' h
  obtain ⟨-, -, -, -, -, hA', -, hIs⟩ := hX
  have hom : IsWeilDatumO W.ψ A' WW _ _ (X.ω' t) := hIs.weil' t
  have hpos : ∀ τ, (gramAt D A' τ).PosDef := fun τ =>
    GlobalTheory.DefiniteQuotient.posDef_of_signature (hA' τ)
  have hf : IsThetaFunO W.ψ A' WW (pureTensorO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.B X.rW.B (X.f' t) P') :=
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hIs.isVac'.1 hIs.isVac'.2.inf X.rA'.s X.rA'.B X.rW.s X.rW.B
      (GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hIs.isVac'.1 hIs.isVac'.2.inf (hIs.snd t) hIs.isVac'.2.theta) P'
  have key := GlobalTheory.DefiniteQuotient.integrableOn_theta D W.ψ hom.std A' WW _ _ (X.ω' t) hom hpos ℂ
    (LinearMap.toSpanSingleton ℂ _ (pureTensorO W.ψ W.θ A' WW X.rA'.s X.rW.s X.rA'.B X.rW.B (X.f' t) P'))
    (fun x => GlobalTheory.OrientedHeis.theta_smul x hf) (fun _ => (1 : ℂ)) continuous_const (fun _ _ _ => rfl)
    X.m' X.fd' hIs.meas'.1 hIs.meas'.2 h
  simp only [LinearMap.toSpanSingleton_apply, one_smul] at key
  exact key

end GlobalTheory.SqTower

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnThetaKernelDefiniteSeesawStageStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_thetaKernel_definiteSeesawStage : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (W : G.Weil) (i j : Fin D.R.m) (p : ℕ)
    (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p 0 X →
    ∀ (t : T) (P' : PolF D WW.rank A'.rank) (h : GA D WW), MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m' := by
  first | exact @GlobalTheory.SqTower.integrableOn_ker'_of_stage_zero | exact GlobalTheory.SqTower.integrableOn_ker'_of_stage_zero | (intros; apply GlobalTheory.SqTower.integrableOn_ker'_of_stage_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerComposition
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThKEvAdm

theorem comp_mem_adm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁) (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e → ∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ ι ι' I e hM hM₁ hev l hl g hg
  classical
  obtain ⟨ei, ev, -, hvac, hpure⟩ := hev.loc
  obtain ⟨Bx, hBo, hBs, hBe, hinv⟩ := GlobalTheory.T.exists_open_subgroups_integers F _ g hg
  obtain ⟨R, hR⟩ := GlobalTheory.T.scaling_open_subgroups_finite F _ Bx hBo hBs hBe g hg.2 hinv
  let φ : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ∀ v : HeightOneSpectrum (𝓞 F),
      (Fin n × Fin d → v.adicCompletion F) → ℂ :=
    fun r v => Set.indicator {x : Fin n × Fin d → v.adicCompletion F | ∀ i, x i - evalV F v (r i) ∈ Bx v} 1
  have hφSB : ∀ r v, φ r v ∈ SB _ := fun r => (GlobalTheory.T.translate_open_subgroups_finite F _ Bx hBo hBs hBe r).1
  have hφvac : ∀ r, ∀ᶠ v in cofinite, φ r v = M.vac v := fun r => by
    filter_upwards [(GlobalTheory.T.translate_open_subgroups_finite F _ Bx hBo hBs hBe r).2, hM.std] with v h1 h2
    exact h1.trans h2.symm
  let ψ : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → ∀ v : HeightOneSpectrum (𝓞 F),
      (Fin n₁ × Fin d₁ → v.adicCompletion F) → ℂ :=
    fun r v => ev v (φ r v)
  have hψSB : ∀ r v, ψ r v ∈ SB _ := fun r v => by
    rw [← (hvac v).2]; exact Submodule.mem_map_of_mem (hφSB r v)
  have hψint : ∀ r, ∀ᶠ v in cofinite,
      ψ r v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := fun r => by
    filter_upwards [hφvac r, hM₁.std] with v h1 h2
    show ev v (φ r v) = _
    rw [h1, (hvac v).1, h2]
  let g' : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) → (Fin n₁ × Fin d₁ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
    fun r y => ∏ᶠ v, ψ r v fun i => evalV F v (y i)
  have hg'SB : ∀ r, g' r ∈ SB _ := fun r => GlobalTheory.T.restricted_product_mem_schwartz F _ (ψ r) (hψSB r) (hψint r)
  have hT : ∀ r, ∃ T : SchwartzMap (Fin n₁ × Fin d₁ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
      ∀ f : SchwartzMap (Fin n₁ × Fin d₁ → mixedEmbedding.mixedSpace F) ℂ, l (pureA F f (g' r)) = T f := fun r => hl (g' r) (hg'SB r)
  choose T hT using hT
  have key : ∀ f : SInf F (Fin n × Fin d), pureA F f g = ∑ r ∈ R, g r • pure f (φ r) := by
    intro f
    funext x
    rw [Finset.sum_apply]
    conv_lhs => rw [hR]
    simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [mul_left_comm]
    rfl
  have key2 : ∀ (f : SInf F (Fin n₁ × Fin d₁)) r, pure f (ψ r) = pureA F f (g' r) := fun f r => rfl
  refine ⟨∑ r ∈ R, g r • (T r).comp ei, fun f => ?_⟩
  have hL : l (e (pureA F (⇑f) g)) = ∑ r ∈ R, g r * T r (ei f) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [key, map_sum, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_smul, map_smul, hpure f (φ r) (hφSB r) (hφvac r), key2, hT, smul_eq_mul]
  rw [LinearMap.comp_apply, hL, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rfl

end GlobalTheory.ThKEvAdm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivHeisenbergCMThetaQuasiInvariantRational
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivHeisenbergCMThetaQuasiInvariantRational
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

noncomputable section

namespace GlobalTheory.ThetaDerivQuasi

open Formalism.IndefR.DatumF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem symplOHF_add_left' (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (xi0 : E) (x x' y : WOF F E nS nT) :
    symplOHF σ JS JT xi0 (x + x') y = symplOHF σ JS JT xi0 x y + symplOHF σ JS JT xi0 x' y := by
  simp only [symplOHF, symplOF, hOF, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add (f := _)]

theorem symplOHF_add_right' (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (xi0 : E) (x y y' : WOF F E nS nT) :
    symplOHF σ JS JT xi0 x (y + y') = symplOHF σ JS JT xi0 x y + symplOHF σ JS JT xi0 x y' := by
  simp only [symplOHF, symplOF, hOF, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add (f := _)]

end GlobalTheory.ThetaDerivQuasi

theorem GlobalTheory.ThetaDerivQuasi.deriv_heis_quasi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ (γ : Matrix (Fin nT) (Fin nS) E) (w : Formalism.IndefR.DatumF.WOF F E nS nT),
      deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (Formalism.IndefR.DatumF.ratWF γ + w)) 0 = B.ψ (-(Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) w)) * deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w)) 0 := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ _ f hf L _ _ γ w
  have key : ∀ t : ℝ, Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (Formalism.IndefR.DatumF.ratWF γ + w) =
      B.ψ (-(Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) w)) *
        Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f w := by
    intro t
    simp only [Formalism.IndefR.DatumF.heisOF]
    rw [add_assoc, hf.quasi γ (w + L t), GlobalTheory.ThetaDerivQuasi.symplOHF_add_left',
      GlobalTheory.ThetaDerivQuasi.symplOHF_add_right', neg_add, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
    have h1 : B.ψ (Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) (L t)) *
        B.ψ (-Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) (L t)) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    linear_combination (B.ψ (Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ w (L t)) *
      B.ψ (-Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) w) * f (w + L t)) * h1
  simp_rw [key]
  exact congrFun (deriv_const_mul_field' _) 0

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivHeisenbergCMThetaQuasiInvariantRationalStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deriv_heisenbergCM_theta_quasiInvariant_rational : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ (γ : Matrix (Fin nT) (Fin nS) E) (w : Formalism.IndefR.DatumF.WOF F E nS nT),
      deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (Formalism.IndefR.DatumF.ratWF γ + w)) 0 = B.ψ (-(Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) w)) * deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w)) 0 := by
  first | exact @GlobalTheory.ThetaDerivQuasi.deriv_heis_quasi | exact GlobalTheory.ThetaDerivQuasi.deriv_heis_quasi | (intros; apply GlobalTheory.ThetaDerivQuasi.deriv_heis_quasi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueCentreFunctionFieldPlaceCurve
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueCentreFunctionFieldPlaceCurve
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

theorem existsUnique_centre : ∀ (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E] [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ p : Place k E, ∃! b : Sp p.O ⟶ C, spMap p.O.subtype ≫ b = spMap (algebraMap K E) ≫ x := by
  intro k K E _ _ _ _ _ _ _ _ _ _ C _ x hx p
  obtain ⟨⟨-, hproj, -⟩, -, hxs⟩ := hx
  have hprop : IsProper (strHom k (X := C)) := (isProper_and_exists_isAmpleLB_of_isProjOver hproj).1
  have hk : ∀ c : k, algebraMap k E c ∈ p.O := by
    intro c
    rw [Valuation.mem_valuationSubring_iff]
    by_cases hc : c = 0
    · simp [hc]
    · rw [p.2.2 c hc]
  let ik : k →+* p.O := (algebraMap k E).codRestrict p.O hk
  have hik : p.O.subtype.comp ik = algebraMap k E := RingHom.ext fun _ => rfl
  have hsq : (spMap (algebraMap K E) ≫ x) ≫ strHom k C = spMap (algebraMap p.O E) ≫ spMap ik := by
    rw [Category.assoc, hxs, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]
    rfl
  have hv : ValuativeCriterion (strHom k C) := by
    rw [IsProper.eq_valuativeCriterion] at hprop
    exact hprop.1.1.1
  let S : ValuativeCommSq (strHom k C) :=
    { R := p.O, K := E, i₁ := spMap (algebraMap K E) ≫ x, i₂ := spMap ik, commSq := ⟨hsq⟩ }
  obtain ⟨U⟩ := hv S

  have hover : ∀ b : Sp p.O ⟶ C, spMap p.O.subtype ≫ b = spMap (algebraMap K E) ≫ x → b ≫ strHom k C = spMap ik := by
    intro b hb
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (b ≫ strHom k C)
    have e : Spec.map (φ ≫ CommRingCat.ofHom p.O.subtype) = Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
      rw [Spec.map_comp, hφ, ← Category.assoc, hb, Category.assoc, hxs, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← IsScalarTower.algebraMap_eq]
    have e2 := Spec.map_injective e
    rw [← hφ]
    congr 1
    ext c
    exact congrArg (fun f => (CommRingCat.Hom.hom f) c) e2
  refine ⟨U.default.l, U.default.fac_left, fun b hb => ?_⟩
  let L : S.commSq.LiftStruct := { l := b, fac_left := hb, fac_right := hover b hb }
  exact congrArg CommSq.LiftStruct.l (U.uniq L)

end GlobalTheory.Nef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueCentreFunctionFieldPlaceCurveStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_centre_functionFieldPlace_curve : ∀ (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E] [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ p : Place k E, ∃! b : Sp p.O ⟶ C, spMap p.O.subtype ≫ b = spMap (algebraMap K E) ≫ x := by
  first | exact @GlobalTheory.Nef.existsUnique_centre | exact GlobalTheory.Nef.existsUnique_centre | (intros; apply GlobalTheory.Nef.existsUnique_centre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormSignatureRealisation
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.UnitaryClasses

theorem gramOn_map_eq_H {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (H : Matrix (Fin n) (Fin n) E) (V : Submodule E (Fin n → E)) (τ : E →+* ℂ) :
    (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H V).map τ =
      (Matrix.of fun k i => τ ((Module.finBasis E V i).1 k) :
        Matrix (Fin n) (Fin (Module.finrank E V)) ℂ)ᴴ * H.map τ *
      (Matrix.of fun k i => τ ((Module.finBasis E V i).1 k)) := by
  ext i j
  simp [gramOn, hform, Matrix.mul_apply, Matrix.conjTranspose_apply,
    IsCMField.complexEmbedding_complexConj, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

theorem gramOn_det_totallyPositive_of_posDef {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (H : Matrix (Fin n) (Fin n) E)
    (hH : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H.map τ = cT (starRingEnd ℂ) Q * Q)
    (V : Submodule E (Fin n → E)) :
    (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H V).det ≠ 0 ∧
      ∀ τ : E →+* ℂ, ∃ r : ℝ, 0 < r ∧ τ (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H V).det = r := by
  have key : ∀ τ : E →+* ℂ, 0 < τ (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H V).det := by
    intro τ
    obtain ⟨Q, hQ, hHQ⟩ := hH τ
    rw [RingHom.map_det]
    have e1 : τ.mapMatrix (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H V) =
        (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H V).map τ := rfl
    have e2 : cT (starRingEnd ℂ) Q = Qᴴ := by
      ext i j; simp [cT, Matrix.conjTranspose_apply]
    set A : Matrix (Fin n) (Fin (Module.finrank E V)) ℂ :=
      Matrix.of fun k i => τ ((Module.finBasis E V i).1 k) with hA
    have e3 : Aᴴ * (Qᴴ * Q) * A = (Q * A)ᴴ * (Q * A) := by
      rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [e1, gramOn_map_eq_H, ← hA, hHQ, e2, e3]
    have hQi : Function.Injective Q.mulVec := by
      rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det]
      exact isUnit_iff_ne_zero.mpr hQ
    have hinj : Function.Injective (Q * A).mulVec := by
      intro v w hvw
      simp only [← Matrix.mulVec_mulVec] at hvw
      exact gramOn_basis_mulVec_injective V τ (hQi hvw)
    exact (Matrix.PosDef.conjTranspose_mul_self _ hinj).det_pos
  refine ⟨fun h0 => ?_, fun τ => ?_⟩
  · have τ0 := (Classical.arbitrary (NumberField.InfinitePlace E)).embedding
    have := key τ0
    rw [h0, map_zero] at this
    exact lt_irrefl _ this
  · have h := Complex.lt_def.mp (key τ)
    refine ⟨(τ (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom H V).det).re, h.1, ?_⟩
    apply Complex.ext
    · simp
    · simpa using h.2.symm

theorem refSign_prod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ S : Set (Pl E), IsSection S → ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → (∀ P₁ : E[X], P₁.Monic → P₁ ∣ γ₀.val.charpoly → ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else sgnOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) (atPl w P₁) (γ₀.val.map (algebraMap E (w.adicCompletion E)))) = 1) := by
  intro E _ _ _ hU S hS n γ₀ _ H₀ _ _ _ hpos P₁ _ _
  obtain ⟨hd0, hdpos⟩ := gramOn_det_totallyPositive_of_posDef H₀ hpos
    (LinearMap.ker (Matrix.toLin' (aeval γ₀.val P₁)))
  refine Eq.trans ?_ (GlobalTheory.T.finprod_nonsplit_sign_totallyPositive_eq_one E hU S hS _ hd0 hdpos)
  apply finprod_mem_congr rfl
  intro w _
  split_ifs with hw
  · rfl
  · unfold sgnOn
    rw [aeval_map_mat]
    exact GlobalTheory.T.gramKernelSign_nonsplit_baseChange_eq E hU w hw n H₀ (aeval γ₀.val P₁)

end GlobalTheory.UnitaryClasses
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitUnitaryLiftTendstoOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitUnitaryLiftTendstoOne
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Filter Topology

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.SplitUnitLiftCont

open GlobalTheory.SplitGLLift GlobalTheory.SplitUnitLift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl (F := F)}

theorem continuous_liftPair (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) :
    Continuous (liftPair h τ) := by
  have hj : Continuous (LinearMap.inr F (Ainf F) (Af F) ∘ₗ GlobalTheory.AdelicU.singleFin v) := by
    change Continuous fun a => ((0 : Ainf F), GlobalTheory.AdelicU.singleFin v a)
    exact continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)
  have h1 : Continuous (GlobalTheory.AdelicU.Supp.singleTens E v) :=
    GlobalTheory.AutFunCompare.continuous_tensNU (E := E) _ _ hj
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  have h2 : Continuous ((splitAlgEquiv h τ).symm : Fv F v × Fv F v → Fv F v ⊗[F] E) :=
    IsModuleTopology.continuous_of_linearMap (splitAlgEquiv h τ).symm.toLinearMap
  exact h1.comp h2

theorem continuous_liftMat (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {n : ℕ} :
    Continuous (liftMat (n := Fin n) h τ) := by
  refine continuous_matrix fun i j => ?_
  show Continuous fun p : Matrix (Fin n) (Fin n) (Fv F v) × Matrix (Fin n) (Fin n) (Fv F v) =>
    liftPair h τ (p.1 i j, p.2 i j)
  exact (continuous_liftPair h τ).comp
    (((continuous_fst.matrix_elem i j)).prodMk (continuous_snd.matrix_elem i j))

theorem continuous_liftN (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : IsUnit (J.map τ).det) : Continuous (liftN h τ J hJ) := by
  have : IsTopologicalRing (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := IsModuleTopology.isTopologicalRing (AF F) _
  have hp : Continuous (pairHom (J.map τ) hJ) := by
    show Continuous fun g : GL (Fin n) (Fv F v) => ((g : Matrix (Fin n) (Fin n) (Fv F v)),
      (J.map τ)⁻¹ * ((g⁻¹ : GL (Fin n) (Fv F v)) : Matrix (Fin n) (Fin n) (Fv F v))ᵀ * J.map τ)
    refine Units.continuous_val.prodMk ?_
    exact (continuous_const.matrix_mul (Units.continuous_coe_inv.matrix_transpose)).matrix_mul continuous_const
  show Continuous fun g => 1 + liftMat h τ (pairHom (J.map τ) hJ g - 1)
  exact continuous_const.add ((continuous_liftMat h τ).comp (hp.sub continuous_const))

theorem continuous_liftU (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ε : F)
    (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det) :
    Continuous (liftU h τ J ε herm hJ) := by
  refine Continuous.subtype_mk ?_ _
  refine Units.continuous_iff.2 ⟨continuous_liftN h τ J hJ, ?_⟩
  exact (continuous_liftN h τ J hJ).comp continuous_inv

theorem tendsto_liftU (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ε : F)
    (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det) :
    Tendsto (liftU h τ J ε herm hJ) (𝓝 1) (𝓝 1) := by
  have := (continuous_liftU h τ J ε herm hJ).tendsto 1
  rwa [map_one] at this

theorem tendsto_liftU_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl (F := F)} {n : ℕ} (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (ε : F) (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det), Tendsto (GlobalTheory.SplitUnitLift.liftU h τ J ε herm hJ) (𝓝 1) (𝓝 1) := fun h τ J ε herm hJ => tendsto_liftU h τ J ε herm hJ

end GlobalTheory.SplitUnitLiftCont

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitUnitaryLiftTendstoOneStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_unitary_lift_tendsto_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl (F := F)} {n : ℕ} (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (ε : F) (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det), Tendsto (GlobalTheory.SplitUnitLift.liftU h τ J ε herm hJ) (𝓝 1) (𝓝 1) := by
  first | exact @GlobalTheory.SplitUnitLiftCont.tendsto_liftU_one | exact GlobalTheory.SplitUnitLiftCont.tendsto_liftU_one | (intros; apply GlobalTheory.SplitUnitLiftCont.tendsto_liftU_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeUnitStalkDataGerm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeUnitStalkDataGerm
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem fromSpecStalk_preimage_top {X : Scheme.{0}} (x : X) (U : X.Opens) (hx : x ∈ U) :
    ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := by
  intro z _
  have hz : X.fromSpecStalk x z ⤳ x := by
    have : X.fromSpecStalk x z ∈ Set.range (X.fromSpecStalk x) := ⟨z, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  exact hz.mem_open U.2 hx

theorem fromSpecStalk_appLE_top {X : Scheme.{0}} (x : X) (U : X.Opens) (hx : x ∈ U) :
    (X.fromSpecStalk x).appLE U ⊤ (fromSpecStalk_preimage_top x U hx) =
      X.presheaf.germ U x hx ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
  simp only [Category.assoc, ← Functor.map_comp]
  have e : ((homOfLE le_top).op ≫ (homOfLE (fromSpecStalk_preimage_top x U hx)).op :
      Opposite.op (⊤ : (Spec (X.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := rfl
  rw [e, CategoryTheory.Functor.map_id, Category.comp_id]

theorem appLE_eq_of_eq {X Y : Scheme.{0}} {g g' : X ⟶ Y} (hg : g = g') (V : Y.Opens) (W : X.Opens)
    (h : W ≤ g ⁻¹ᵁ V) (h' : W ≤ g' ⁻¹ᵁ V) : g.appLE V W h = g'.appLE V W h' := by
  subst hg; rfl

theorem germ_comp_of_spec {X Y : Scheme.{0}} {x : X} {y : Y} (φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x)
    (f : X ⟶ Y) (hφ : Spec.map φ ≫ Y.fromSpecStalk y = X.fromSpecStalk x ≫ f)
    (V : Y.Opens) (hy : y ∈ V) (U : X.Opens) (hx : x ∈ U) (h : U ≤ f ⁻¹ᵁ V) :
    Y.presheaf.germ V y hy ≫ φ = f.appLE V U h ≫ X.presheaf.germ U x hx := by
  have h1 : ⊤ ≤ (Spec.map φ ≫ Y.fromSpecStalk y) ⁻¹ᵁ V := by
    intro z _
    exact fromSpecStalk_preimage_top y V hy (Set.mem_univ _)
  have h2 : ⊤ ≤ (X.fromSpecStalk x ≫ f) ⁻¹ᵁ V := hφ ▸ h1
  have key := appLE_eq_of_eq hφ V ⊤ h1 h2
  have eL : (Spec.map φ ≫ Y.fromSpecStalk y).appLE V ⊤ h1 =
      (Y.fromSpecStalk y).appLE V ⊤ (fromSpecStalk_preimage_top y V hy) ≫
        (Spec.map φ).appLE ⊤ ⊤ (by simp) := by
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have eR : (X.fromSpecStalk x ≫ f).appLE V ⊤ h2 =
      f.appLE V U h ≫ (X.fromSpecStalk x).appLE U ⊤ (fromSpecStalk_preimage_top x U hx) := by
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have eT : (Spec.map φ).appLE ⊤ ⊤ (by simp) = (Spec.map φ).appTop := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.preimage_top, Category.comp_id]
    first | rfl | simp
  rw [eL, eR, eT, fromSpecStalk_appLE_top y V hy, fromSpecStalk_appLE_top x U hx, Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, ← Category.assoc, ← Category.assoc] at key
  exact (cancel_mono _).1 key

theorem germ_apply_of_spec {X Y : Scheme.{0}} {x : X} {y : Y} (φ : Y.presheaf.stalk y →+* X.presheaf.stalk x)
    (f : X ⟶ Y) (hφ : Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecStalk y = X.fromSpecStalk x ≫ f)
    (V : Y.Opens) (hy : y ∈ V) (U : X.Opens) (hx : x ∈ U) (h : U ≤ f ⁻¹ᵁ V) (a : Γ(Y, V)) :
    φ (Y.presheaf.germ V y hy a) = X.presheaf.germ U x hx (f.appLE V U h a) := by
  have e := congrArg (fun g => g.hom a) (germ_comp_of_spec (CommRingCat.ofHom φ) f hφ V hy U hx h)
  exact e

theorem stalkData_germ : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], ∀ (s : S) (π : S.presheaf.stalk s →+* G.left.presheaf.stalk (unitSec G s)) (ε : G.left.presheaf.stalk (unitSec G s) →+* S.presheaf.stalk s) (m : G.left.presheaf.stalk (unitSec G s) →+* G.left.presheaf.stalk (unitSec G s)), StalkData G s π ε m → (∀ (V : S.Opens) (hs : s ∈ V) (U : G.left.Opens) (hU : unitSec G s ∈ U) (h : U ≤ G.hom ⁻¹ᵁ V) (a : Γ(S, V)), π (S.presheaf.germ V s hs a) = G.left.presheaf.germ U _ hU (G.hom.appLE V U h a)) ∧ (∀ (U : G.left.Opens) (hU : unitSec G s ∈ U) (V : S.Opens) (hs : s ∈ V) (h : V ≤ unitSec G ⁻¹ᵁ U) (f : Γ(G.left, U)), ε (G.left.presheaf.germ U _ hU f) = S.presheaf.germ V s hs ((unitSec G).appLE U V h f)) ∧ (∀ (U : G.left.Opens) (hU : unitSec G s ∈ U) (U' : G.left.Opens) (hU' : unitSec G s ∈ U') (h : U' ≤ sqr G ⁻¹ᵁ U) (f : Γ(G.left, U)), m (G.left.presheaf.germ U _ hU f) = G.left.presheaf.germ U' _ hU' ((sqr G).appLE U U' h f)) := by
  intro S G _ s π ε m hD
  exact ⟨fun V hs U hU h a => germ_apply_of_spec π G.hom hD.str V hs U hU h a,
    fun U hU V hs h f => germ_apply_of_spec ε (unitSec G) hD.unit U hU V hs h f,
    fun U hU U' hU' h f => germ_apply_of_spec m (sqr G) hD.sq U hU U' hU' h f⟩

end GlobalTheory.Nef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeUnitStalkDataGermStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupSchemeUnitStalkData_germ : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], ∀ (s : S) (π : S.presheaf.stalk s →+* G.left.presheaf.stalk (unitSec G s)) (ε : G.left.presheaf.stalk (unitSec G s) →+* S.presheaf.stalk s) (m : G.left.presheaf.stalk (unitSec G s) →+* G.left.presheaf.stalk (unitSec G s)), StalkData G s π ε m → (∀ (V : S.Opens) (hs : s ∈ V) (U : G.left.Opens) (hU : unitSec G s ∈ U) (h : U ≤ G.hom ⁻¹ᵁ V) (a : Γ(S, V)), π (S.presheaf.germ V s hs a) = G.left.presheaf.germ U _ hU (G.hom.appLE V U h a)) ∧ (∀ (U : G.left.Opens) (hU : unitSec G s ∈ U) (V : S.Opens) (hs : s ∈ V) (h : V ≤ unitSec G ⁻¹ᵁ U) (f : Γ(G.left, U)), ε (G.left.presheaf.germ U _ hU f) = S.presheaf.germ V s hs ((unitSec G).appLE U V h f)) ∧ (∀ (U : G.left.Opens) (hU : unitSec G s ∈ U) (U' : G.left.Opens) (hU' : unitSec G s ∈ U') (h : U' ≤ sqr G ⁻¹ᵁ U) (f : Γ(G.left, U)), m (G.left.presheaf.germ U _ hU f) = G.left.presheaf.germ U' _ hU' ((sqr G).appLE U U' h f)) := by
  first | exact @GlobalTheory.Nef.stalkData_germ | exact GlobalTheory.Nef.stalkData_germ | (intros; apply GlobalTheory.Nef.stalkData_germ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroWeightTensorIntertwiningAutRep
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroWeightTensorIntertwiningAutRep
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer

theorem exists_ne_zero_wsp_intertwining : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (lam : InfinitePlace E → DomWeight n) (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π →
    (∀ v : InfinitePlace E, HasWeightAt π v.embedding (lam v)) →
    ∃ T : Wsp lam →ₗ[ℂ] (UA E n → ℂ), T ≠ 0 ∧ (∀ w, T w ∈ π) ∧
      ∀ x ∈ infU E n, ∀ w, T (wInf lam x w) = RU E n x (T w) := by
  intro E _ _ _ n lam π hπ hW
  let π' : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
  let s : ∀ v : InfinitePlace E, embU n v.embedding →* UA E n := fun v => (embU n v.embedding).subtype
  let σ : ∀ v : InfinitePlace E, Representation ℂ (embU n v.embedding) (nablaSq ℂ n (lam v)) := fun v =>
    (GlobalTheory.Branching.sqRep ℂ n (lam v)).comp ((cEmb v.embedding).comp (embU n v.embedding).subtype)
  have hirr : ∀ v, (σ v).IsIrreducible := fun v => by
    obtain ⟨e, he⟩ := GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E n v.embedding
    obtain ⟨h1, h2⟩ := (CuspRep.isIrreducible_iff _).1 (GlobalTheory.Branching.isIrreducible_smallRep_unitary n (lam v))
    refine (CuspRep.isIrreducible_iff _).2 ⟨h1, fun S hS => h2 S fun g w hw => ?_⟩
    obtain ⟨x, rfl⟩ := e.surjective g
    have := hS x w hw
    change GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb v.embedding (x : UA E n)) w ∈ S at this
    change GlobalTheory.Branching.sqRep ℂ n (lam v) (GlobalTheory.Branching.unitaryIncl n (e x)) w ∈ S
    rwa [he]
  have hcomm : ∀ u v, u ≠ v → ∀ a b, Commute (s u a) (s v b) := fun u v huv a b =>
    GlobalTheory.T.commute_unitaryArchimedeanPoints_distinct_places E n u.embedding v.embedding (by rwa [InfinitePlace.mk_embedding, InfinitePlace.mk_embedding])
      _ a.2 _ b.2
  have hspan : ∀ v, (⨆ f : (σ v).IntertwiningMap (π'.rep.comp (s v)), LinearMap.range f.toLinearMap) = ⊤ :=
    fun v => GlobalTheory.T.iSup_range_weightMaps_eq_top_definiteUnitary E n π' v.embedding (lam v) (hW v)
  haveI : Nontrivial π'.V := Submodule.nontrivial_iff_ne_bot.2 π'.isAut.ne_bot
  obtain ⟨F, hF0, hF⟩ := GlobalTheory.T.exists_multilinearMap_of_isotypic_commuting_subgroups (InfinitePlace E) (UA E n) π'.V (fun v => embU n v.embedding)
    (fun v => nablaSq ℂ n (lam v)) π'.rep s σ inferInstance hirr hcomm hspan
  let T : Wsp lam →ₗ[ℂ] (UA E n → ℂ) := π.subtype ∘ₗ PiTensorProduct.lift F
  have hT : ∀ u, T (PiTensorProduct.tprod ℂ u) = (F u).1 := fun u => by
    simp only [T, LinearMap.comp_apply, PiTensorProduct.lift.tprod]
    rfl
  obtain ⟨u0, hu0⟩ : ∃ u, F u ≠ 0 := by
    by_contra h
    push_neg at h
    exact hF0 (MultilinearMap.ext h)
  refine ⟨T, fun h => hu0 ?_, fun w => (PiTensorProduct.lift F w).2, fun x hx w => ?_⟩
  · apply Subtype.ext
    rw [← hT, h]
    rfl
  · obtain ⟨y, hy, hyc, hprod⟩ := GlobalTheory.T.definiteUnitaryInfinitePoint_eq_list_prod_placeParts E n x hx
    let y' : ∀ v : InfinitePlace E, embU n v.embedding := fun v => ⟨y v, hy v⟩
    have key : ∀ u, T (wInf lam x (PiTensorProduct.tprod ℂ u)) = RU E n x (T (PiTensorProduct.tprod ℂ u)) := by
      intro u
      have h1 := GlobalTheory.DefU.prod_list_apply_multilinear π'.rep s σ F hF y' u Finset.univ.toList
        (Finset.nodup_toList _)
      have h2 : (Finset.univ.toList.map fun v => s v (y' v)).prod = x := hprod
      rw [h2] at h1
      simp only [Finset.mem_toList, Finset.mem_univ, if_true] at h1
      have h3 : wInf lam x (PiTensorProduct.tprod ℂ u) =
          PiTensorProduct.tprod ℂ (fun v => σ v (y' v) (u v)) := by
        change PiTensorProduct.map _ _ = _
        rw [PiTensorProduct.map_tprod]
        refine congrArg _ (funext fun v => ?_)
        change _ = GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb v.embedding (y v)) (u v)
        rw [hyc v]
      rw [h3, hT, hT, ← h1]
      rfl
    have hext : T ∘ₗ wInf lam x = RU E n x ∘ₗ T := PiTensorProduct.ext (MultilinearMap.ext fun u => by
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply]
      exact key u)
    exact LinearMap.congr_fun hext w

end GlobalTheory.BCT.TrKer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroWeightTensorIntertwiningAutRepStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_weightTensor_intertwining_autRep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : InfinitePlace E → DomWeight n) (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π → (∀ v : InfinitePlace E, HasWeightAt π v.embedding (lam v)) → ∃ T : Wsp lam →ₗ[ℂ] (UA E n → ℂ), T ≠ 0 ∧ (∀ w, T w ∈ π) ∧ ∀ x ∈ infU E n, ∀ w, T (wInf lam x w) = RU E n x (T w) := by
  first | exact @GlobalTheory.BCT.TrKer.exists_ne_zero_wsp_intertwining | exact GlobalTheory.BCT.TrKer.exists_ne_zero_wsp_intertwining | (intros; apply GlobalTheory.BCT.TrKer.exists_ne_zero_wsp_intertwining <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHermitianSignatureHyperbolicPlaneOrthCompleme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHermitianSignatureHyperbolicPlaneOrthCompleme
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

noncomputable section

namespace GlobalTheory.PlaneSkewSig

open Matrix

theorem conjTranspose_eq_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : Mᴴ = M := by
  obtain ⟨hn, A, hA⟩ := h
  set D : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ := Matrix.fromBlocks 1 0 0 (-1) with hD
  have hDD : D * D = 1 := by
    simp [hD, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  have hDh : Dᴴ = D := by
    simp [hD, Matrix.fromBlocks_conjTranspose]
  have hAh : Aᵀ * Mᴴ * A.map star = D := by
    have a1 : (A.map star)ᴴ = Aᵀ := by ext; simp [conjTranspose_apply]
    have a2 : (Aᵀ)ᴴ = A.map star := by ext; simp [conjTranspose_apply]
    have : (Aᵀ * M * A.map star)ᴴ = Aᵀ * Mᴴ * A.map star := by
      rw [conjTranspose_mul, conjTranspose_mul, a1, a2, Matrix.mul_assoc]
    rw [← this, hA, hDh]
  have e : Fin r ⊕ Fin s ≃ Fin n := (finSumFinEquiv).trans (finCongr hn)
  have k1 : M * (A.map star * D * Aᵀ) = 1 := by
    have : Aᵀ * (M * A.map star * D) = 1 := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hA, hDD]
    have := (Matrix.mul_eq_one_comm_of_equiv e).1 this
    simpa [Matrix.mul_assoc] using this
  have k2 : Mᴴ * (A.map star * D * Aᵀ) = 1 := by
    have : Aᵀ * (Mᴴ * A.map star * D) = 1 := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hAh, hDD]
    have := (Matrix.mul_eq_one_comm_of_equiv e).1 this
    simpa [Matrix.mul_assoc] using this
  have k3 : (A.map star * D * Aᵀ) * M = 1 := mul_eq_one_comm.1 k1
  calc Mᴴ = Mᴴ * ((A.map star * D * Aᵀ) * M) := by rw [k3, Matrix.mul_one]
    _ = M := by rw [← Matrix.mul_assoc, k2, Matrix.one_mul]

theorem exists_left_inverse {m k : ℕ} (ι : Matrix (Fin m) (Fin k) ℂ) (h : Function.Injective ι.mulVec) :
    ∃ P : Matrix (Fin k) (Fin m) ℂ, P * ι = 1 := by
  have hker : LinearMap.ker (Matrix.mulVecLin ι) = ⊥ := LinearMap.ker_eq_bot.2 h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at this
  have e : LinearMap.toMatrix' ι.mulVecLin = ι := LinearMap.toMatrix'_toLin' ι
  rwa [e] at this

theorem transpose_mulVec_eq_zero {m k : ℕ} (ι : Matrix (Fin m) (Fin k) ℂ) (v : Fin m → ℂ)
    (h : ∀ u, (ι *ᵥ u) ⬝ᵥ v = 0) : ιᵀ *ᵥ v = 0 := by
  ext j
  have := h (Pi.single j 1)
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm, single_dotProduct] at this
  simpa using this

theorem hasSig_complement : ∀ (n₁ : ℕ) (M : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ) (X Y : Fin (n₁ + 2) → ℂ)
    (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) ℂ) (r s : ℕ), HasSig M r s → 1 ≤ r → 1 ≤ s →
    X ⬝ᵥ M *ᵥ star X = 0 → Y ⬝ᵥ M *ᵥ star Y = 0 → X ⬝ᵥ M *ᵥ star Y ≠ 0 →
    (∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star X = 0 ∧ (ι *ᵥ u) ⬝ᵥ M *ᵥ star Y = 0) → Function.Injective ι.mulVec →
    HasSig (ιᵀ * M * ι.map star) (r - 1) (s - 1) := by
  intro n₁ M X Y ι r s hs _ _ hXX hYY hXY horth hinj
  set c := X ⬝ᵥ M *ᵥ star Y with hc
  set Y' : Fin (n₁ + 2) → ℂ := (star c)⁻¹ • Y with hY'
  have hsY : star Y' = c⁻¹ • star Y := by
    rw [hY', star_smul, star_inv₀, star_star]
  have hXY' : X ⬝ᵥ M *ᵥ star Y' = 1 := by
    rw [hsY, mulVec_smul, dotProduct_smul, smul_eq_mul, ← hc, inv_mul_cancel₀ hXY]
  have hYY' : Y' ⬝ᵥ M *ᵥ star Y' = 0 := by
    rw [hsY, mulVec_smul, dotProduct_smul, hY', smul_dotProduct, hYY]; simp
  have hιX : ιᵀ *ᵥ (M *ᵥ star X) = 0 := transpose_mulVec_eq_zero ι _ fun u => (horth u).1
  have hιY : ιᵀ *ᵥ (M *ᵥ star Y') = 0 := by
    rw [hsY, mulVec_smul, mulVec_smul, transpose_mulVec_eq_zero ι _ fun u => (horth u).2, smul_zero]
  obtain ⟨P, hP⟩ := exists_left_inverse ι hinj
  exact GlobalTheory.PlaneSig.hasSig_complement_plane (n₁ + 2) n₁ M X Y' ι P r s rfl (conjTranspose_eq_of_hasSig hs)
    hXX hYY' hXY' hιX hιY hP hs

end GlobalTheory.PlaneSkewSig
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHermitianSignatureHyperbolicPlaneOrthComplemeStatement
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasHermitianSignature_hyperbolicPlane_orthComplement : ∀ (n₁ : ℕ) (M : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ) (X Y : Fin (n₁ + 2) → ℂ)
    (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) ℂ) (r s : ℕ), HasSig M r s → 1 ≤ r → 1 ≤ s →
    X ⬝ᵥ M *ᵥ star X = 0 → Y ⬝ᵥ M *ᵥ star Y = 0 → X ⬝ᵥ M *ᵥ star Y ≠ 0 →
    (∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star X = 0 ∧ (ι *ᵥ u) ⬝ᵥ M *ᵥ star Y = 0) → Function.Injective ι.mulVec →
    HasSig (ιᵀ * M * ι.map star) (r - 1) (s - 1) := by
  first | exact @GlobalTheory.PlaneSkewSig.hasSig_complement | exact GlobalTheory.PlaneSkewSig.hasSig_complement | (intros; apply GlobalTheory.PlaneSkewSig.hasSig_complement <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianDerivative
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.ThK.EvAt0
open GlobalTheory.ThK.EvAt0.PolD

namespace GlobalTheory.ThK.EvAt0.GaussForm

theorem exists_schwartz_gauss_form {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Q : LinearMap.BilinForm ℝ E) (hs : ∀ p p', Q p p' = Q p' p) (hp : ∀ p, p ≠ 0 → 0 < Q p p) :
    ∃ G : SchwartzMap E ℂ, ∀ s, G s = Complex.exp (-(Real.pi : ℂ) * (Q s s : ℂ)) ∧
      ∀ v, fderiv ℝ (⇑G) s v = -(2 * (Real.pi : ℂ)) * (Q s v : ℂ) * G s := by
  let B : E →L[ℝ] E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ ((-Real.pi) • Q))
  have hB : ∀ x y, B x y = -Real.pi * Q x y := fun x y => rfl
  obtain ⟨G, hG⟩ := GlobalTheory.GaussSchwartz.exists_schwartz_exp_diag B (fun x hx => by
    rw [hB]
    have := mul_pos Real.pi_pos (hp x hx)
    linarith)
  refine ⟨G, fun s => ⟨?_, fun v => ?_⟩⟩
  · rw [hG, hB]; push_cast; rfl
  · have hfun : (⇑G) = fun x => Complex.ofRealCLM (Real.exp (B x x)) := funext fun x => hG x
    have h1 := (B.hasFDerivAt (x := s)).clm_apply (hasFDerivAt_id s)
    have h2 := Complex.ofRealCLM.hasFDerivAt.comp s h1.exp
    have h3 := congrArg (fun f => fderiv ℝ f s) hfun
    rw [h3.trans h2.fderiv, hG]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply, id, Complex.ofRealCLM_apply, hB, smul_eq_mul,
      hs v s]
    push_cast
    ring

end GlobalTheory.ThK.EvAt0.GaussForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedAbsDetMulIntegralCompMulVecFinitePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedAbsDetMulIntegralCompMulVecFinitePlace
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.InertLagChar

theorem haarChar_det_mul_integral_comp_mulVec_localField (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (m : MeasurableSpace (Fin N → k)) (hm : m = borel _)
    (ν : @Measure (Fin N → k) m) (hν : @Measure.IsAddHaarMeasure _ _ _ m ν)
    (T : GL (Fin N) k) (f : (Fin N → k) → ℂ) :
    ((distribHaarChar k (Matrix.GeneralLinearGroup.det T) : ℝ) : ℂ) * ∫ y, f (T.val *ᵥ y) ∂ν = ∫ y, f y ∂ν := by
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  have h2 : m = MeasurableSpace.pi := hm.trans (@BorelSpace.measurable_eq (Fin N → k) _ MeasurableSpace.pi Pi.borelSpace).symm
  subst h2
  have hc := Measure.isAddLeftInvariant_eq_smul ν (Measure.pi fun _ : Fin N => (Measure.addHaar : Measure k))
  rw [hc, integral_smul_nnreal_measure, integral_smul_nnreal_measure,
    ← GlobalTheory.WeilM.integral_comp_mulVec (Measure.addHaar : Measure k) T f, mul_smul_comm]

theorem nabs_det_mul_integral_comp_mulVec :
    ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)),
    @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∀ (T : GL (Fin N) (Fv F v)) (f : (Fin N → Fv F v) → ℂ),
      ((GlobalTheory.SplitWeil.nabs (Fv F v) (Matrix.GeneralLinearGroup.det T) : ℝ) : ℂ) * ∫ y, f (T.val *ᵥ y) ∂ν = ∫ y, f y ∂ν := by
  intro F _ _ v N ν hν T f
  exact haarChar_det_mul_integral_comp_mulVec_localField (Fv F v) N _ rfl ν hν T f

end GlobalTheory.InertLagChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedAbsDetMulIntegralCompMulVecFinitePlaceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedAbsDet_mul_integral_comp_mulVec_finitePlace : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)),
    @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∀ (T : GL (Fin N) (Fv F v)) (f : (Fin N → Fv F v) → ℂ),
      ((GlobalTheory.SplitWeil.nabs (Fv F v) (Matrix.GeneralLinearGroup.det T) : ℝ) : ℂ) * ∫ y, f (T.val *ᵥ y) ∂ν = ∫ y, f y ∂ν := by
  first | exact @GlobalTheory.InertLagChar.nabs_det_mul_integral_comp_mulVec | exact GlobalTheory.InertLagChar.nabs_det_mul_integral_comp_mulVec | (intros; apply GlobalTheory.InertLagChar.nabs_det_mul_integral_comp_mulVec <;> assumption)
end
end
