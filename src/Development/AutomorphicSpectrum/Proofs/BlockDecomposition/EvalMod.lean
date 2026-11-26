module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasicoherentSupSections
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.TiedAInvOfTheta
public import GroundTheory.PAdicHodge.BCrisRegularSenTate

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.CompanionTheory.LTPer

section Abs

variable {B : Type} [CommRing B]

def ltIter (ϖ : B) (q n : ℕ) : B → B := (fun x => ϖ * x + x ^ q)^[n]

def Near (S : Subring B) (ϖ : B) (J : Ideal B) (m : ℕ) (x : B) : Prop :=
  ∃ s ∈ S, x - ϖ ^ m * s ∈ J

structure PerEnv (S : Subring B) (F : ℕ → Ideal B) (ϖ : B) : Prop where
  top : F 0 = ⊤
  anti : ∀ k, F (k + 1) ≤ F k
  mul_le : ∀ a b, F a * F b ≤ F (a + b)
  sep : ∀ x, (∀ k, x ∈ F k) → x = 0
  complete : ∀ x : ℕ → B, (∀ k, x (k + 1) - x k ∈ F k) → ∃ t, ∀ k, t - x k ∈ F k
  unit : IsUnit ϖ
  mem : ϖ ∈ S
  sumS : ∀ s : ℕ → B, (∀ n, s n ∈ S) → ∃ r ∈ S, ∀ N, ∃ a ∈ S,
    r - ∑ n ∈ Finset.range N, ϖ ^ n * s n = ϖ ^ N * a
  closed : ∀ k, ∀ x ∈ S, (∀ m, Near S ϖ (F k) m x) → x ∈ F k

def Tends (S : Subring B) (F : ℕ → Ideal B) (ϖ : B) (x : ℕ → B) (t : B) : Prop :=
  ∀ k, ∃ c : ℕ, ∀ m, ∃ N, ∀ n ≥ N, Near S ϖ (F k) m (ϖ ^ c * (x n - t))

def EvalMod {R : Type} [CommRing R] (S : Subring B) (F : ℕ → Ideal B) (ϖ : B) (h : R →+* B)
    (φ : PowerSeries R) (y r : B) (m : ℕ) : Prop :=
  ∀ k, ∃ D, ∀ D' ≥ D, Near S ϖ (F k) m
    ((∑ i ∈ Finset.range D', h (PowerSeries.coeff i φ) * y ^ i) - r)

end Abs

section Conc

variable (l : ℕ) [Fact l.Prime]

open scoped Formalism.Per6

abbrev Tl : Type := PreTilt ↥(GroundTheory.PAdicHodge.normInteger ℂ_[l]) l

abbrev Wl : Type := WittVector l (Tl l)

def wB : Wl l →+* Formalism.Per6.BdRp l :=
  GroundTheory.PAdicHodge.wittToBDeRhamPlus ↥(GroundTheory.PAdicHodge.normInteger ℂ_[l]) l

def tch (x : Tl l) : Formalism.Per6.BdRp l := wB l (WittVector.teichmuller l x)

def rB : Om l →+* Formalism.Per6.BdRp l := (GroundTheory.PAdicHodge.algClToBdR l).toRingHom

def thB : Formalism.Per6.BdRp l →+* ℂ_[l] := (GroundTheory.PAdicHodge.thetaAlgHom l).toRingHom

def FB (k : ℕ) : Ideal (Formalism.Per6.BdRp l) := RingHom.ker (thB l) ^ k

variable {l}

def actB (g : GQ l) : Formalism.Per6.BdRp l →+* Formalism.Per6.BdRp l := MulSemiringAction.toRingHom _ _ (Formalism.Per6.toBot g)

def actT (g : GQ l) : Tl l →+* Tl l :=
  GroundTheory.PAdicHodge.preTiltMap l (GroundTheory.PAdicHodge.galCp (Formalism.Per6.toBot g) : ℂ_[l] →+* ℂ_[l])
    (GroundTheory.PAdicHodge.AInf.norm_galCp_toRingHom (Formalism.Per6.toBot g))

abbrev qOf {K : FinExt l} (π : ↥(OL K)) : ℕ := Nat.card (↥(OL K) ⧸ Ideal.span {π})

def oB (K : FinExt l) (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) : ↥(OL K) →+* Formalism.Per6.BdRp l :=
  (rB l).comp ((μ : ↥K.1 →+* Om l).comp (algebraMap ↥(OL K) ↥K.1))

def LTData (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l) : Prop :=
  Irreducible π ∧ z 0 = 0 ∧ z 1 ≠ 0 ∧
    (∀ n, z (n + 1) ^ Nat.card (↥(OL K) ⧸ Ideal.span {π}) +
      (((π : ↥K.1) : Om l)) * z (n + 1) = z n) ∧
    ∀ (g : ↥(GK K)) (φ : PowerSeries ↥(OL K)), PowerSeries.constantCoeff φ = 0 →
      ((PowerSeries.coeff 1 φ : ↥(OL K)) : ↥K.1) = ((χ g : (↥K.1)ˣ) : ↥K.1) →
      PowerSeries.subst φ (GlobalTheory.CompanionTheory.LTHodge.ltSeries π) = PowerSeries.subst (GlobalTheory.CompanionTheory.LTHodge.ltSeries π) φ →
      ∀ n, HasSum (fun k : ℕ => (((PowerSeries.coeff k φ : ↥(OL K)) : ↥K.1) : Om l) * z n ^ k)
        ((g : GQ l) (z n))

def PrePer (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) (t : Formalism.Per6.BdRp l) : Prop :=
  t ≠ 0 ∧ (∀ (g : GQ l) (hg : g ∈ GK K), (∀ x : ↥K.1, g (μ x) = μ x) →
      actB g t = rB l (μ ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1)) * t) ∧
    (μ = K.1.val → thB l t = 0)

end Conc

end GlobalTheory.CompanionTheory.LTPer
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularRepresentationContinuous
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularRepresentationContinuous
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA

theorem translations_strongly_continuous :
    ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
      (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod →
      ∀ x : Lp V 2 μ, Continuous (fun h : G n => rR μ V h x) ∧
        Continuous (fun y : G n => lT μ V y x) := by
  intro n _ _ μ _ V _ _ _ hU x
  have := (hU n μ).1
  constructor
  · let g : G n → C(G n, G n) := fun h => ⟨fun y => y * h, continuous_id.mul continuous_const⟩
    have hg : Continuous g :=
      ContinuousMap.continuous_of_continuous_uncurry _ (continuous_snd.mul continuous_fst)
    have hm : ∀ h, MeasurePreserving (g h) μ μ := fun h => measurePreserving_mul_right μ h
    have key := Continuous.compMeasurePreservingLp (f := fun _ : G n => x) continuous_const hg hm
      (by norm_num : (2 : ENNReal) ≠ ⊤)
    refine key.congr fun h => ?_
    have hm' : MeasurePreserving (fun y : G n => y * h) μ μ := measurePreserving_mul_right μ h
    simp only [rR, dif_pos hm']
    rfl
  · let g : G n → C(G n, G n) := fun y => ⟨fun z => y⁻¹ * z, continuous_const.mul continuous_id⟩
    have hg : Continuous g :=
      ContinuousMap.continuous_of_continuous_uncurry _ (continuous_fst.inv.mul continuous_snd)
    have hm : ∀ y, MeasurePreserving (g y) μ μ := fun y => measurePreserving_mul_left μ y⁻¹
    have key := Continuous.compMeasurePreservingLp (f := fun _ : G n => x) continuous_const hg hm
      (by norm_num : (2 : ENNReal) ≠ ⊤)
    exact key

end GlobalTheory.CompanionTheory.PresSobA
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularRepresentationContinuousStatement
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_representation_continuous : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod → ∀ x : Lp V 2 μ, Continuous (fun h : G n => rR μ V h x) ∧ Continuous (fun y : G n => lT μ V y x) := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.translations_strongly_continuous | exact GlobalTheory.CompanionTheory.PresSobA.translations_strongly_continuous | (intros; apply GlobalTheory.CompanionTheory.PresSobA.translations_strongly_continuous <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeRightBasisExpansion
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeRightBasisExpansion
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA

namespace GlobalTheory.CompanionTheory.PresSobA.Frame

section Norm

attribute [-instance] instTopologicalSpaceMatrix

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
  Matrix.linftyOpNormedSpace

def chartM (n : ℕ) : (Fin n → Fin n → ℂ) ≃L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv

theorem contDiffOn_invPi (n : ℕ) :
    ContDiffOn ℝ ∞ (fun M : Fin n → Fin n → ℂ => (chartM n).symm (Ring.inverse (chartM n M)))
      {M | IsUnit (chartM n M)} := by
  have : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.completeSpace ℝ _
  intro M hM
  obtain ⟨u, hu⟩ := hM
  have h1 : ContDiffAt ℝ ∞ (Ring.inverse : Matrix (Fin n) (Fin n) ℂ → _) (chartM n M) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℝ u
  have h2 : ContDiffAt ℝ ∞ (fun M => (chartM n).symm (Ring.inverse (chartM n M))) M :=
    (chartM n).symm.contDiff.contDiffAt.comp M (h1.comp M (chartM n).contDiff.contDiffAt)
  exact h2.contDiffWithinAt

end Norm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem contDiffOn_inverse : ContDiffOn ℝ ∞ (Ring.inverse : Mat n → Mat n) (GLs n) := by
  refine (contDiffOn_invPi n).mono ?_
  intro M hM
  exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hM)

def mulB (n : ℕ) : CLof (Mat n) (CLof (Mat n) (Mat n)) :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
      (Mat n →ₗ[ℝ] Mat n) ≃ₗ[ℝ] CLof (Mat n) (Mat n)).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun P Z : Mat n => P * Z) add_mul (fun c P Z => Matrix.smul_mul c P Z)
        mul_add (fun c P Z => Matrix.mul_smul P c Z))

def coordL (p : Bool × Fin n × Fin n) : CLof (Mat n) ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.proj p : ((Bool × Fin n × Fin n) → ℝ) →ₗ[ℝ] ℝ) ∘ₗ
      (GlobalTheory.CompanionTheory.SobGL.HaarDom.cmE n).symm.toLinearMap)

theorem sum_coordL (M : Mat n) : ∑ p, coordL p M • bs p = M :=
  (GlobalTheory.CompanionTheory.SobGL.HaarDom.cmE n).apply_symm_apply M

def frameA (p : Bool × Fin n × Fin n) (z : Mat n) : CLof (Mat n) ℝ :=
  (coordL p).comp (mulB n (Ring.inverse z))

theorem contDiffOn_frameA (p : Bool × Fin n × Fin n) : ContDiffOn ℝ ∞ (frameA p) (GLs n) := by
  let L : Mat n →ₗ[ℝ] CLof (Mat n) ℝ :=
    { toFun := fun x => (coordL p).comp (mulB n x)
      map_add' := by
        intro x y
        ext v
        simp
      map_smul' := by
        intro c x
        ext v
        simp }
  exact L.toContinuousLinearMap.contDiff.comp_contDiffOn contDiffOn_inverse

theorem frame_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (D : CLof (Mat n) V)
    {z : Mat n} (hz : z ∈ GLs n) : D = ∑ p, (frameA p z).smulRight (D (z * bs p)) := by
  have hu : IsUnit z := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hz)
  apply ContinuousLinearMap.ext
  intro v
  have hv : z * (Ring.inverse z * v) = v := by
    rw [← mul_assoc, Ring.mul_inverse_cancel z hu, one_mul]
  have hs := sum_coordL (Ring.inverse z * v)
  have h0 : v = ∑ p, coordL p (Ring.inverse z * v) • (z * bs p) := by
    conv_lhs => rw [← hv, ← hs]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => Matrix.mul_smul _ _ _
  simp only [sum_apply, ContinuousLinearMap.smulRight_apply]
  conv_lhs => rw [h0]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun p _ => D.map_smul _ _

theorem frame :
    ∀ n : ℕ, ∃ A : (Bool × Fin n × Fin n) → Mat n → CLof (Mat n) ℝ,
      (∀ p, ContDiffOn ℝ ∞ (A p) (GLs n)) ∧
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (D : CLof (Mat n) V), ∀ z ∈ GLs n,
        D = ∑ p, (A p z).smulRight (D (z * bs p)) :=
  fun _ => ⟨frameA, contDiffOn_frameA, fun _ _ _ D _ hz => frame_eq D hz⟩

end GlobalTheory.CompanionTheory.PresSobA.Frame
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeRightBasisExpansionStatement
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_right_basis_expansion : ∀ n : ℕ, ∃ A : (Bool × Fin n × Fin n) → Mat n → CLof (Mat n) ℝ, (∀ p, ContDiffOn ℝ ∞ (A p) (GLs n)) ∧ ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (D : CLof (Mat n) V), ∀ z ∈ GLs n, D = ∑ p, (A p z).smulRight (D (z * bs p)) := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.Frame.frame | exact GlobalTheory.CompanionTheory.PresSobA.Frame.frame | (intros; apply GlobalTheory.CompanionTheory.PresSobA.Frame.frame <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LpIntegralAePointwise
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LpIntegralAePointwise
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.LpBochner

variable {Y V : Type} [MeasurableSpace Y] {ν : Measure Y}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem integrableOn_of_memLp_two {h : Y → V} (hh : MemLp h 2 ν) {s : Set Y} (hs : ν s ≠ ⊤) :
    IntegrableOn h s ν := by
  haveI : IsFiniteMeasure (ν.restrict s) := ⟨by simpa using hs.lt_top⟩
  have h2 : MemLp h 2 (ν.restrict s) := hh.restrict s
  exact memLp_one_iff_integrable.1 (h2.mono_exponent (by norm_num))

theorem integral_norm_restrict_le {h : Y → V} (hh : MemLp h 2 ν) {s : Set Y} (hs : ν s ≠ ⊤) :
    ∫ y in s, ‖h y‖ ∂ν ≤ ((ν s) ^ (1 / 2 : ℝ)).toReal * (eLpNorm h 2 ν).toReal := by
  haveI : IsFiniteMeasure (ν.restrict s) := ⟨by simpa using hs.lt_top⟩
  have hm : AEStronglyMeasurable h (ν.restrict s) := hh.aestronglyMeasurable.restrict
  have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := ν.restrict s) (p := 1) (q := 2)
    (by norm_num) hm
  have h3 : eLpNorm h 2 (ν.restrict s) ≤ eLpNorm h 2 ν := eLpNorm_restrict_le _ _ _ _
  have hexp : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by
    norm_num
  rw [hexp, Measure.restrict_apply_univ] at h1
  have hfin : (ν s) ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hs
  have h4 : eLpNorm h 1 (ν.restrict s) ≤ (ν s) ^ (1 / 2 : ℝ) * eLpNorm h 2 ν := by
    calc _ ≤ _ := h1
      _ ≤ eLpNorm h 2 ν * (ν s) ^ (1 / 2 : ℝ) := by gcongr
      _ = _ := mul_comm _ _
  have h5 : ∫ y in s, ‖h y‖ ∂ν = (eLpNorm h 1 (ν.restrict s)).toReal := by
    rw [integral_norm_eq_lintegral_eNorm hm, eLpNorm_one_eq_lintegral_eNorm hm]
  rw [h5, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top hfin hh.ne) h4

variable [CompleteSpace V]

def setIntegralCLM (ν : Measure Y) (s : Set Y) (hs : ν s ≠ ⊤) : Lp V 2 ν →L[ℝ] V :=
  LinearMap.mkContinuous
    { toFun := fun h => ∫ y in s, h y ∂ν
      map_add' := fun f g => by
        have hf := integrableOn_of_memLp_two (Lp.memLp f) hs
        have hg := integrableOn_of_memLp_two (Lp.memLp g) hs
        rw [← integral_add hf hg]
        exact integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_add f g))
      map_smul' := fun r f => by
        simp only [RingHom.id_apply]
        rw [← integral_smul]
        exact integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_smul r f)) }
    ((ν s) ^ (1 / 2 : ℝ)).toReal
    (fun h => by
      refine (norm_integral_le_integral_norm _).trans ?_
      refine (integral_norm_restrict_le (Lp.memLp h) hs).trans ?_
      rw [Lp.norm_def])

theorem setIntegralCLM_apply (s : Set Y) (hs : ν s ≠ ⊤) (h : Lp V 2 ν) :
    setIntegralCLM ν s hs h = ∫ y in s, h y ∂ν := rfl

theorem bochner_Lp_ae (A : Type) [MeasurableSpace A] (α : Measure A) [SFinite α]
    [SigmaFinite ν] (c : A → Lp V 2 ν) (F : A → Y → V)
    (hc : Integrable c α) (hF : AEStronglyMeasurable (Function.uncurry F) (α.prod ν))
    (hcF : ∀ᵐ a ∂α, c a =ᵐ[ν] F a) :
    (⇑(∫ a, c a ∂α) : Y → V) =ᵐ[ν] fun y => ∫ a, F a y ∂α := by
  have hFs : ∀ s : Set Y, AEStronglyMeasurable (Function.uncurry F) (α.prod (ν.restrict s)) := by
    intro s
    refine hF.mono_measure ?_
    exact Measure.prod_mono le_rfl Measure.restrict_le_self
  have hint : ∀ s : Set Y, ν s ≠ ⊤ → Integrable (Function.uncurry F) (α.prod (ν.restrict s)) := by
    intro s hs
    rw [integrable_prod_iff (hFs s)]
    constructor
    · filter_upwards [hcF] with a ha
      exact (integrableOn_of_memLp_two (Lp.memLp (c a)) hs).congr (ae_restrict_of_ae ha)
    · refine Integrable.mono' (hc.norm.const_mul ((ν s) ^ (1 / 2 : ℝ)).toReal)
        (hFs s).norm.integral_prod_right' ?_
      filter_upwards [hcF] with a ha
      have hnn : 0 ≤ ∫ y, ‖Function.uncurry F (a, y)‖ ∂(ν.restrict s) :=
        integral_nonneg fun _ => norm_nonneg _
      rw [Real.norm_of_nonneg hnn, Lp.norm_def]
      have : ∫ y, ‖Function.uncurry F (a, y)‖ ∂(ν.restrict s) = ∫ y in s, ‖c a y‖ ∂ν :=
        integral_congr_ae (ae_restrict_of_ae (ha.mono fun y hy => by simp [hy]))
      rw [this]
      exact integral_norm_restrict_le (Lp.memLp (c a)) hs
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite ?_ ?_ ?_
  · intro s _ hs
    exact integrableOn_of_memLp_two (Lp.memLp _) hs.ne
  · intro s _ hs
    exact (hint s hs.ne).integral_prod_right
  · intro s hsm hs
    have h1 : ∫ y in s, (∫ a, c a ∂α) y ∂ν = ∫ a, ∫ y in s, c a y ∂ν ∂α := by
      rw [← setIntegralCLM_apply s hs.ne, ← ContinuousLinearMap.integral_comp_comm _ hc]
      rfl
    have h2 : ∫ a, ∫ y in s, c a y ∂ν ∂α = ∫ a, ∫ y in s, F a y ∂ν ∂α := by
      refine integral_congr_ae ?_
      filter_upwards [hcF] with a ha
      exact integral_congr_ae (ae_restrict_of_ae ha)
    rw [h1, h2]
    exact integral_integral_swap (hint s hs.ne)

theorem coe_integral_ae_eq : ∀ (A Y V : Type) [MeasurableSpace A] [MeasurableSpace Y] (α : Measure A) [SFinite α] (ν : Measure Y) [SigmaFinite ν] [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (c : A → Lp V 2 ν) (F : A → Y → V), Integrable c α → AEStronglyMeasurable (Function.uncurry F) (α.prod ν) → (∀ᵐ a ∂α, c a =ᵐ[ν] F a) → (⇑(∫ a, c a ∂α) : Y → V) =ᵐ[ν] fun y => ∫ a, F a y ∂α := by
  intro A Y V _ _ α _ ν _ _ _ _ c F hc hF hcF
  exact bochner_Lp_ae A α c F hc hF hcF

end GlobalTheory.CompanionTheory.LpBochner
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LpIntegralAePointwiseStatement
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lp_integral_ae_pointwise : ∀ (A Y V : Type) [MeasurableSpace A] [MeasurableSpace Y] (α : Measure A) [SFinite α] (ν : Measure Y) [SigmaFinite ν] [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (c : A → Lp V 2 ν) (F : A → Y → V), Integrable c α → AEStronglyMeasurable (Function.uncurry F) (α.prod ν) → (∀ᵐ a ∂α, c a =ᵐ[ν] F a) → (⇑(∫ a, c a ∂α) : Y → V) =ᵐ[ν] fun y => ∫ a, F a y ∂α := by
  first | exact @GlobalTheory.CompanionTheory.LpBochner.coe_integral_ae_eq | exact GlobalTheory.CompanionTheory.LpBochner.coe_integral_ae_eq | (intros; apply GlobalTheory.CompanionTheory.LpBochner.coe_integral_ae_eq <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixExpCurveDerivative
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixExpCurveDerivative
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA

noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA.ExpCurve

section Entries

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem hasDerivAt_exp_entry {n : ℕ} (X : Mat n) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) : Mat n) i j)
      ((NormedSpace.exp (t • X) * X : Mat n) i j) t := by
  haveI : FiniteDimensional ℝ (Mat n) := inferInstanceAs (FiniteDimensional ℝ (Matrix (Fin n) (Fin n) ℂ))
  haveI : CompleteSpace (Mat n) := FiniteDimensional.complete ℝ (Mat n)
  have h : HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) : Mat n))
      (NormedSpace.exp (t • X) * X : Mat n) t := hasDerivAt_exp_smul_const X t
  let L : Mat n →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  exact L.hasFDerivAt.comp_hasDerivAt t h

end Entries

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hasDerivAt_exp {n : ℕ} (X : Mat n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (expC X s).val) ((expC X t).val * X) t := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
  exact hasDerivAt_exp_entry X t i j

theorem expC_continuous_hasDerivAt :
    ∀ (n : ℕ) (X : Mat n), Continuous (expC X) ∧
      ∀ t : ℝ, HasDerivAt (fun s : ℝ => (expC X s).val) ((expC X t).val * X) t := by
  intro n X
  refine ⟨?_, hasDerivAt_exp X⟩
  refine (GlobalTheory.CompanionTheory.SobGL.HaarDom.isOpenEmbedding_valG (n := n)).isInducing.continuous_iff.2 ?_
  exact continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp X t).continuousAt

end GlobalTheory.CompanionTheory.PresSobA.ExpCurve
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixExpCurveDerivativeStatement
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_exp_curve_derivative : ∀ (n : ℕ) (X : Mat n), Continuous (expC X) ∧ ∀ t : ℝ, HasDerivAt (fun s : ℝ => (expC X s).val) ((expC X t).val * X) t := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.ExpCurve.expC_continuous_hasDerivAt | exact GlobalTheory.CompanionTheory.PresSobA.ExpCurve.expC_continuous_hasDerivAt | (intros; apply GlobalTheory.CompanionTheory.PresSobA.ExpCurve.expC_continuous_hasDerivAt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeOfAffineCover
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeOfAffineCover
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE

theorem hom_eq_zero_of_basicOpen_cover {X : Scheme.{0}} {M N : X.Modules} (φ : M ⟶ N)
    {ι : Type} (V : ι → X.Opens) (hV : ∀ i, IsAffineOpen (V i)) (hcov : iSup V = ⊤)
    (h : ∀ i (f : Γ(X, V i)) (s : Γ(M, X.basicOpen f)), φ.app (X.basicOpen f) s = 0) :
    φ = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun W ↦ ?_
  ext s
  have hcov' : W ≤ ⨆ p : {p : Σ i, Γ(X, V i) // X.basicOpen p.2 ≤ W}, X.basicOpen p.1.2 := by
    intro x hx
    have hx' : x ∈ iSup V := by rw [hcov]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
    obtain ⟨f, hfW, hxf⟩ := (hV i).exists_basicOpen_le ⟨x, hx⟩ hi
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨i, f⟩, hfW⟩, hxf⟩
  refine TopCat.Sheaf.eq_of_locally_eq' (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf Ab X)
    (fun p : {p : Σ i, Γ(X, V i) // X.basicOpen p.2 ≤ W} ↦ X.basicOpen p.1.2) W
    (fun p ↦ homOfLE p.2) hcov' _ _ fun p ↦ ?_
  have nat := ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE p.2).op) s
  have e1 : (ConcreteCategory.hom (N.presheaf.map (homOfLE p.2).op)) (φ.app W s) = 0 :=
    nat.symm.trans (h p.1.1 p.1.2 _)
  refine e1.trans ?_
  rw [Scheme.Modules.Hom.zero_app]
  simp

theorem app_basicOpen_eq_zero {X : Scheme.{0}} {M N : X.Modules} [M.IsQuasicoherent] (φ : M ⟶ N)
    {U : X.Opens} (hU : IsAffineOpen U) (h0 : ∀ t : Γ(M, U), φ.app U t = 0) (f : Γ(X, U))
    (s : Γ(M, X.basicOpen f)) : φ.app (X.basicOpen f) s = 0 := by
  obtain ⟨n, t, ht⟩ := ((GlobalTheory.QCoh.isLocalizedModule_resBasicOpen_iff M f).1
    (GlobalTheory.QCoh.isLocalizedModule_resBasicOpen M hU f)).1 s
  have hu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f ^ n) :=
    (GlobalTheory.QCoh.isUnit_res_of_le_basicOpen f (X.basicOpen_le f) le_rfl).pow n
  have nat := ConcreteCategory.congr_hom
    (φ.mapPresheaf.naturality (homOfLE (X.basicOpen_le f)).op) t
  have key : X.presheaf.map (homOfLE (X.basicOpen_le f)).op f ^ n • φ.app (X.basicOpen f) s = 0 := by
    rw [← Scheme.Modules.Hom.app_smul, ht]
    refine nat.trans ?_
    change (ConcreteCategory.hom (N.presheaf.map (homOfLE (X.basicOpen_le f)).op)) (φ.app U t) = 0
    rw [h0 t]
    simp
  exact (hu.smul_eq_zero).1 key

theorem le_of_secs_subset_cover {X : Scheme.{0}} {E : X.Modules} [E.IsQuasicoherent]
    (S T : Subobject E) (hS : (S : X.Modules).IsQuasicoherent)
    (_hT : (T : X.Modules).IsQuasicoherent) {ι : Type} (V : ι → X.Opens)
    (hV : ∀ i, IsAffineOpen (V i)) (hcov : iSup V = ⊤)
    (h : ∀ i, secs S (V i) ⊆ secs T (V i)) : S ≤ T := by
  have h0 : S.arrow ≫ cokernel.π T.arrow = 0 := by
    refine hom_eq_zero_of_basicOpen_cover _ V hV hcov fun i f s ↦ ?_
    refine app_basicOpen_eq_zero _ (hV i) (fun t ↦ ?_) f s
    obtain ⟨y, hy⟩ := h i ⟨t, rfl⟩
    have hz : (T.arrow ≫ cokernel.π T.arrow).app (V i) y = 0 := by
      rw [cokernel.condition]; rfl
    change (cokernel.π T.arrow).app (V i) (S.arrow.app (V i) t) = 0
    rw [← hy]
    exact hz
  exact Subobject.le_of_comm (Abelian.monoLift T.arrow S.arrow h0) (Abelian.monoLift_comp _ _ _)

end GlobalTheory.CompanionTheory.GE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeOfAffineCoverStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subobject_le_of_affine_cover : ∀ {X : Scheme.{0}} {E : X.Modules} [E.IsQuasicoherent] (S T : Subobject E), (S : X.Modules).IsQuasicoherent → (T : X.Modules).IsQuasicoherent → ∀ {ι : Type} (V : ι → X.Opens), (∀ i, IsAffineOpen (V i)) → iSup V = ⊤ → (∀ i, secs S (V i) ⊆ secs T (V i)) → S ≤ T := by
  first | exact @GlobalTheory.CompanionTheory.GE.le_of_secs_subset_cover | exact GlobalTheory.CompanionTheory.GE.le_of_secs_subset_cover | (intros; apply GlobalTheory.CompanionTheory.GE.le_of_secs_subset_cover <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperPushforwardCoherent
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperPushforwardCoherent
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh TensorProduct
open TopologicalSpace Opposite

namespace GlobalTheory.CompanionTheory.GE.PushCoh

abbrev overAffine {X Z : Scheme.{0}} (φ : Z ⟶ X) {V : X.Opens} (hV : IsAffineOpen V) :
    (φ ⁻¹ᵁ V).toScheme.Over (Spec (.of Γ(X, V))) :=
  ⟨φ ∣_ V ≫ hV.isoSpec.hom⟩

attribute [local instance] algebraOfOver

lemma algebraMap_overAffine {X Z : Scheme.{0}} (φ : Z ⟶ X) {V : X.Opens} (hV : IsAffineOpen V)
    (b : Γ(X, V)) :
    letI := overAffine φ hV
    Z.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V)).symm).op
      (algebraMap Γ(X, V) Γ((φ ⁻¹ᵁ V).toScheme, ⊤) b : Γ(Z, (φ ⁻¹ᵁ V).ι ''ᵁ ⊤)) =
      φ.app V b := by
  letI := overAffine φ hV
  have s1 : algebraMap Γ(X, V) Γ((φ ⁻¹ᵁ V).toScheme, ⊤) b = (φ ∣_ V).appTop (V.topIso.inv b) := by
    change (φ ∣_ V ≫ hV.isoSpec.hom).appTop ((Scheme.ΓSpecIso (.of Γ(X, V))).inv b) = _
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, IsAffineOpen.isoSpec_hom_appTop,
      CommRingCat.comp_apply]
    erw [Iso.inv_hom_id_apply]
  rw [s1]
  erw [morphismRestrict_appTop, Scheme.Opens.topIso_inv, CommRingCat.comp_apply]
  refine (RelSerre.app_eqToHom_apply φ (Scheme.Opens.ι_image_top V) _ _ b).trans ?_
  simp

def zerothCohomologyToSections {X Z : Scheme.{0}} (φ : Z ⟶ X) {V : X.Opens} (hV : IsAffineOpen V) (M : Z.Modules) :
    letI := overAffine φ hV
    Sheaf.H.{0} (modulesAb (M.restrict (φ ⁻¹ᵁ V).ι)) 0 →ₗ[Γ(X, V)]
      Γ((Scheme.Modules.pushforward φ).obj M, V) :=
  letI := overAffine φ hV
  { toFun := fun x => M.presheaf.map (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V)).symm).op
      (Sheaf.H.equiv₀ (modulesAb (M.restrict (φ ⁻¹ᵁ V).ι)) isTerminalTop x :
        Γ(M, (φ ⁻¹ᵁ V).ι ''ᵁ ⊤))
    map_add' := fun x y => by
      rw [map_add (f := _)]
      exact map_add _ _ _
    map_smul' := fun b x => by
      rw [H.smul_def, ← Sheaf.H.equiv₀_naturality]
      refine (RelSerre.smul_restrict_top M (φ ⁻¹ᵁ V) _ _).trans ?_
      refine (congrArg (· • _) (algebraMap_overAffine φ hV b)).trans ?_
      exact (smul_pushforward φ M b _).symm }

lemma zeroth_cohomology_to_sections_surjective {X Z : Scheme.{0}} (φ : Z ⟶ X) {V : X.Opens} (hV : IsAffineOpen V)
    (M : Z.Modules) : Function.Surjective (zerothCohomologyToSections φ hV M) := by
  letI := overAffine φ hV
  exact ((ConcreteCategory.bijective_of_isIso (M.presheaf.map
    (eqToHom (Scheme.Opens.ι_image_top (φ ⁻¹ᵁ V)).symm).op)).comp
    (Sheaf.H.equiv₀ (modulesAb (M.restrict (φ ⁻¹ᵁ V).ι)) isTerminalTop).bijective).2

theorem isCoherent_pushforward_of_isProper {X Z : Scheme.{0}} [IsLocallyNoetherian X] (φ : Z ⟶ X)
    (hφ : IsProper φ) {G : Z.Modules} (hG : IsCoherent G) :
    IsCoherent ((Scheme.Modules.pushforward φ).obj G) := by
  haveI := hG.1
  refine ⟨isQuasicoherent_pushforward_of_qcqs φ G, fun V hV => ?_⟩
  letI := overAffine φ hV
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  haveI : IsProper ((φ ⁻¹ᵁ V).toScheme ↘ Spec (.of Γ(X, V))) := by
    change IsProper (φ ∣_ V ≫ hV.isoSpec.hom)
    infer_instance
  have hfin := finite_H_of_isProper (A := Γ(X, V)) (G.restrict (φ ⁻¹ᵁ V).ι) (hG.restrict _) 0
  exact Module.Finite.of_surjective (zerothCohomologyToSections φ hV G) (zeroth_cohomology_to_sections_surjective φ hV G)

end GlobalTheory.CompanionTheory.GE.PushCoh

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperPushforwardCoherentStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_pushforward_coherent : ∀ {X Z : Scheme.{0}} [IsLocallyNoetherian X] (φ : Z ⟶ X), IsProper φ → ∀ {G : Z.Modules}, IsCoherent G → IsCoherent ((Scheme.Modules.pushforward φ).obj G) := by
  first | exact @GlobalTheory.CompanionTheory.GE.PushCoh.isCoherent_pushforward_of_isProper | exact GlobalTheory.CompanionTheory.GE.PushCoh.isCoherent_pushforward_of_isProper | (intros; apply GlobalTheory.CompanionTheory.GE.PushCoh.isCoherent_pushforward_of_isProper <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowExists
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowExists
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem rowExists_of_factor (hFac : FactorRapid) (hEv : EvAdj) : RowExists := by
  intro n _ _ μ _ E _ Ω T F c hS h hh v
  have hS' := hS
  obtain ⟨hLg, hUn, hRC, hSG, hAE, -, -, hCS, hSO, -, -, -, -, -, hOm, -⟩ := hS'
  obtain ⟨h₁, h₂, r₁, r₂, r₂s, rfl⟩ := hFac h hh
  obtain ⟨κ, hκ, hrow⟩ := hEv n μ E Ω T F c hS h₁ r₁ v
  obtain ⟨C₁, hC₁⟩ := hSO n μ E Ω T F hLg hUn hRC hSG hAE hCS hOm (star h₂) r₂s
  obtain ⟨C₂, hC₂⟩ := hSO n μ E Ω T F hLg hUn hRC hSG hAE hCS hOm h₂ r₂
  obtain ⟨f, hfS, hfE, hfc, -⟩ := hC₁ κ hκ
  refine ⟨f, hfS, hfE, ?_⟩
  intro φ f' hφS hφE hf'S hf'E hf'
  obtain ⟨φ₂, hφ₂S, hφ₂E, hφ₂c, -⟩ := hC₂ (cls μ φ) (subset_closure ⟨φ, hφS, hφE, rfl⟩)
  have hmul : cls μ f' = F.Φ h₁ (cls μ φ₂) := by
    rw [hf', F.map_mul, hφ₂c]
    rfl
  rw [hfc, F.map_star, ContinuousLinearMap.adjoint_inner_left, ← hφ₂c]
  exact hrow φ₂ f' hφ₂S hφ₂E hf'S hf'E hmul

end GlobalTheory.CompanionTheory.KerFc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowExistsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_row_exists : GlobalTheory.CompanionTheory.KerFc.FactorRapid → GlobalTheory.CompanionTheory.KerFc.EvAdj → GlobalTheory.CompanionTheory.KerFc.RowExists := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.rowExists_of_factor | exact GlobalTheory.CompanionTheory.KerFc.rowExists_of_factor | (intros; apply GlobalTheory.CompanionTheory.KerFc.rowExists_of_factor <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelAdjointSmooth
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelAdjointSmooth
noncomputable section

open scoped ContDiff InnerProductSpace

namespace GlobalTheory.CompanionTheory.KerFc

def innerSmulRightR {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (e : V) :
    V →L[ℝ] (V →L[ℂ] V) :=
  LinearMap.mkContinuous
    { toFun := fun x => (innerSL ℂ x).smulRight e
      map_add' := fun x y => by
        ext w
        simp [inner_add_left, add_smul]
      map_smul' := fun r x => by
        ext w
        change ⟪r • x, w⟫_ℂ • e = r • (⟪x, w⟫_ℂ • e)
        rw [← Complex.coe_smul r x, inner_smul_left, Complex.conj_ofReal, mul_smul, Complex.coe_smul] }
    ‖e‖
    (fun x => by
      refine (ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_)
      have h1 : ‖⟪x, w⟫_ℂ‖ ≤ ‖x‖ * ‖w‖ := norm_inner_le_norm x w
      simp only [LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, norm_smul]
      calc ‖⟪x, w⟫_ℂ‖ * ‖e‖ ≤ (‖x‖ * ‖w‖) * ‖e‖ := by gcongr
        _ = ‖e‖ * ‖x‖ * ‖w‖ := by ring)

theorem innerSmulRightR_apply {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (e x : V) :
    innerSmulRightR e x = (innerSL ℂ x).smulRight e := rfl

theorem adjoint_eq_sum {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [CompleteSpace V] (B : V →L[ℂ] V) :
    ContinuousLinearMap.adjoint B =
      ∑ i, innerSmulRightR (stdOrthonormalBasis ℂ V i) (B (stdOrthonormalBasis ℂ V i)) := by
  ext w
  rw [ContinuousLinearMap.sum_apply]
  simp only [innerSmulRightR_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  rw [← (stdOrthonormalBasis ℂ V).sum_repr' (ContinuousLinearMap.adjoint B w)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.adjoint_inner_right]

theorem adjSmooth : AdjSmooth := by
  intro W V _ _ _ _ _ _ A s hA
  have hEq : (fun y => ContinuousLinearMap.adjoint (A y)) = fun y =>
      ∑ i, innerSmulRightR (stdOrthonormalBasis ℂ V i) (A y (stdOrthonormalBasis ℂ V i)) := by
    funext y
    exact adjoint_eq_sum (A y)
  rw [hEq]
  refine ContDiffOn.sum fun i _ => ?_
  exact (innerSmulRightR (stdOrthonormalBasis ℂ V i)).contDiff.comp_contDiffOn (hA _)

end GlobalTheory.CompanionTheory.KerFc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelAdjointSmoothStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_adjoint_smooth : GlobalTheory.CompanionTheory.KerFc.AdjSmooth := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.adjSmooth | exact GlobalTheory.CompanionTheory.KerFc.adjSmooth | (intros; apply GlobalTheory.CompanionTheory.KerFc.adjSmooth <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftTranslateCommutes
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftTranslateCommutes
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def lTrL {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x : G n) : Lp V 2 μ →L[ℂ] Lp V 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun y : G n => x * y) (measurePreserving_mul_left μ x)).toContinuousLinearMap

theorem memLp_lTr {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x : G n) {f : Mat n → V}
    (hf : MemLp (fun y : G n => f y.val) 2 μ) : MemLp (fun y : G n => lTr x f y.val) 2 μ :=
  hf.comp_measurePreserving (measurePreserving_mul_left μ x)

theorem lTrL_cls {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x : G n) {f : Mat n → V}
    (hf : MemLp (fun y : G n => f y.val) 2 μ) : lTrL μ V x (cls μ f) = cls μ (lTr x f) := by
  unfold cls
  rw [dite_eq_left hf, dite_eq_left (memLp_lTr μ x hf)]
  exact Lp.toLp_compMeasurePreserving hf (measurePreserving_mul_left μ x)

theorem ltComm_of_ltSob : LtSob → LtComm := by
  intro hL n _ _ μ _ E _ Ω T F c hS h x f f' hf hf' hff'
  obtain ⟨hLg, hU, hR, -, -, -, -, hCS, -, -, hM, -, -, -, hO, -⟩ := hS
  obtain ⟨-, -, -, -, hCl, hOps, -⟩ := hCS
  have hcomm : lTrL μ E.V x * F.Φ h = F.Φ h * lTrL μ E.V x := by
    refine F.comm _ (fun m => ?_) h
    obtain ⟨f₀, hf₀, hc⟩ := hM m.1 m.2
    have hL₀ := hL n μ E.V hLg hU hR x f₀ hf₀
    have hmem : cls μ (lTr x f₀) ∈ Msob μ E.V := Submodule.subset_span ⟨_, hL₀.1, rfl⟩
    have hm₀ : cls μ f₀ ∈ Msob μ E.V := hc ▸ m.2
    have hm : m = ⟨cls μ f₀, hm₀⟩ := Subtype.ext hc.symm
    have hO₀ : Sob μ (Om f₀) := (hOps n μ E.V hLg hU hR f₀ hf₀).1
    have hf₀m : MemLp (fun y : G n => f₀ y.val) 2 μ := hf₀.2 []
    have hO₀m : MemLp (fun y : G n => Om f₀ y.val) 2 μ := hO₀.2 []
    refine ⟨⟨_, hmem⟩, ?_, ?_⟩
    · change cls μ (lTr x f₀) = lTrL μ E.V x m.1
      rw [← hc, lTrL_cls μ x hf₀m]
    · rw [hO _ hmem hL₀.1, hm, hO _ hm₀ hf₀, lTrL_cls μ x hO₀m]
      exact (hCl n μ E.V hU).2.2.1 _ _ hL₀.2
  have hfm : MemLp (fun y : G n => f y.val) 2 μ := hf.2 []
  have hfm' : MemLp (fun y : G n => f' y.val) 2 μ := hf'.2 []
  rw [← lTrL_cls μ x hfm', hff', ← lTrL_cls μ x hfm]
  exact DFunLike.congr_fun hcomm (cls μ f)

end GlobalTheory.CompanionTheory.KerFc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftTranslateCommutesStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.left_translate_commutes : GlobalTheory.CompanionTheory.KerFc.LtSob → GlobalTheory.CompanionTheory.KerFc.LtComm := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.ltComm_of_ltSob | exact GlobalTheory.CompanionTheory.KerFc.ltComm_of_ltSob | (intros; apply GlobalTheory.CompanionTheory.KerFc.ltComm_of_ltSob <;> assumption)
end
end
