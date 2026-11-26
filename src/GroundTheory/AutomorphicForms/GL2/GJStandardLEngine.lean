module

public import GroundTheory.AutomorphicForms.GL2.GJStandardLTensor
public import GroundTheory.AutomorphicForms.GL2.GJStandardLBump

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.GL2.GJStandardLPartial
section -- merged from GroundTheory.AutomorphicForms.GL2.GJStandardLEuler
open MeasureTheory Filter Set Topology IsDedekindDomain NumberField NumberField.mixedEmbedding
open scoped NumberField.AdeleRing RestrictedProduct SchwartzMap Classical ENNReal NNReal

namespace GroundTheory.Automorphic

noncomputable section

namespace GJStandardL

open GodementJacquet GLnLocal

section Local

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem continuous_matrixCoeff_of_smooth (π : Representation ℂ (GL (Fin n) F) V) {ξ : V}
    (hξ : ξ ∈ smoothVectors π) (ℓ : Module.Dual ℂ V) : Continuous (Parabolic.matrixCoeff π ξ ℓ) := by
  refine continuous_iff_continuousAt.2 fun g ↦ ?_
  have hopen : IsOpen ((fun h ↦ g⁻¹ * h) ⁻¹' (stabilizerOf π ξ : Set (GL (Fin n) F))) :=
    (mem_smoothVectors.1 hξ).preimage (continuous_const.mul continuous_id)
  have hg : g ∈ (fun h ↦ g⁻¹ * h) ⁻¹' (stabilizerOf π ξ : Set (GL (Fin n) F)) := by
    simp only [mem_preimage, inv_mul_cancel, SetLike.mem_coe]
    exact (stabilizerOf π ξ).one_mem
  refine (continuousAt_const (y := Parabolic.matrixCoeff π ξ ℓ g)).congr ?_
  filter_upwards [hopen.mem_nhds hg] with h hh
  have hfix : π (g⁻¹ * h) ξ = ξ := mem_stabilizerOf.1 hh
  have : π h ξ = π g ξ := by
    calc π h ξ = π (g * (g⁻¹ * h)) ξ := by rw [mul_inv_cancel_left]
      _ = π g (π (g⁻¹ * h) ξ) := by rw [map_mul, Module.End.mul_apply]
      _ = π g ξ := by rw [hfix]
  simp only [Parabolic.matrixCoeff]
  rw [this]

theorem continuous_localIntegrand [MeasurableSpace (GL (Fin n) F)] {Φ : Matrix (Fin n) (Fin n) F → ℂ}
    (hΦ : Continuous Φ) (π : Representation ℂ (GL (Fin n) F) V) {ξ : V} (hξ : ξ ∈ smoothVectors π)
    (ℓ : Module.Dual ℂ V) (s : ℂ) :
    Continuous fun g : GL (Fin n) F ↦
      Φ (g : Matrix (Fin n) (Fin n) F) * Parabolic.matrixCoeff π ξ ℓ g * detPow g (s + ((n : ℂ) - 1) / 2) :=
  ((hΦ.comp Units.continuous_val).mul (continuous_matrixCoeff_of_smooth π hξ ℓ)).mul (continuous_detPow _)

theorem localIntegrand_of_mem_integralGL (π : Representation ℂ (GL (Fin n) F) V) {ξ : V}
    (hξ : ξ ∈ fixedVectors π (integralGL F n)) {ℓ : Module.Dual ℂ V} (hℓ : ℓ ξ = 1) (s : ℂ)
    {k : GL (Fin n) F} (hk : k ∈ integralGL F n) :
    integralIndicator F n (k : Matrix (Fin n) (Fin n) F) * Parabolic.matrixCoeff π ξ ℓ k *
      detPow k (s + ((n : ℂ) - 1) / 2) = 1 := by
  have h1 : integralIndicator F n (k : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [integralIndicator, Set.indicator_of_mem (mem_integralMatrixSet.2 ((mem_integralGL_iff F n).1 hk).1)]
    rfl
  have h2 : Parabolic.matrixCoeff π ξ ℓ k = 1 := by
    rw [Parabolic.matrixCoeff, hξ k hk, hℓ]
  rw [h1, h2, detPow_of_mem_integralGL hk, one_mul, one_mul]

end Local

section Det

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def adeleToLocal (v : HeightOneSpectrum (𝓞 K)) : 𝔸[K] →+* v.adicCompletion K :=
  (GodementSection.adeleAt v).comp (RingHom.snd _ _)

theorem det_localMat (v : HeightOneSpectrum (𝓞 K)) (x : Matrix (Fin n) (Fin n) 𝔸[K]) :
    (localMat v x).det = (x.det).2 v :=
  (RingHom.map_det (adeleToLocal v) x).symm

theorem det_archMat (x : Matrix (Fin n) (Fin n) 𝔸[K]) : (archMat x).det = (x.det).1 :=
  (RingHom.map_det (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) x).symm

theorem absDet_localComp (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGLn.AdelicGL K n) :
    absDet (localComp n v g) = ‖((g : Matrix (Fin n) (Fin n) 𝔸[K]).det).2 v‖ := by
  rw [absDet, coe_localComp, det_localMat, GodementSection.modulus_adicCompletion]

theorem archAbsDet_archComp (g : AdelicGLn.AdelicGL K n) :
    archAbsDet (archComp K n g) =
      ∏ w : InfinitePlace K, ‖((g : Matrix (Fin n) (Fin n) 𝔸[K]).det).1 w‖ ^ w.mult := by
  rw [archAbsDet, coe_archComp, det_archMat]

theorem detModule_eq (g : AdelicGLn.AdelicGL K n) :
    (Reduction.detModule K n g : ℝ) = archAbsDet (archComp K n g) * ∏ᶠ v, absDet (localComp n v g) := by
  rw [archAbsDet_archComp]
  simp_rw [absDet_localComp]
  show (GroundTheory.Global.IdeleGroup.ideleModule K (AdelicGLn.det K n g) : ℝ) = _
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq, AdelicGLn.coe_det]

theorem absDet_of_mem_integralGL {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {k : GL (Fin n) F} (hk : k ∈ integralGL F n) : absDet k = 1 := by
  have h := detPow_of_mem_integralGL hk 1
  rw [detPow, Complex.cpow_one] at h
  exact_mod_cast h

theorem finite_setOf_not_mem (g : AdelicGLn.AdelicGL K n) :
    {v : HeightOneSpectrum (𝓞 K) | localComp n v g ∉ integralGL (v.adicCompletion K) n}.Finite :=
  Filter.eventually_cofinite.1 (eventually_localComp_mem g)

theorem detPow_eq (g : AdelicGLn.AdelicGL K n) (s : ℂ) :
    GJGlobal.detPow g s = archDetPow (archComp K n g) s * ∏ᶠ v, detPow (localComp n v g) s := by
  set T := (finite_setOf_not_mem g).toFinset with hT
  have hsub : ∀ v ∉ T, localComp n v g ∈ integralGL (v.adicCompletion K) n := fun v hv ↦ by
    by_contra h
    exact hv ((finite_setOf_not_mem g).mem_toFinset.2 h)
  have h1 : ∏ᶠ v, absDet (localComp n v g) = ∏ v ∈ T, absDet (localComp n v g) :=
    finprod_eq_prod_of_mulSupport_subset _ fun v hv ↦ by
      by_contra hvT
      exact hv (absDet_of_mem_integralGL (hsub v hvT))
  have h2 : ∏ᶠ v, detPow (localComp n v g) s = ∏ v ∈ T, detPow (localComp n v g) s :=
    finprod_eq_prod_of_mulSupport_subset _ fun v hv ↦ by
      by_contra hvT
      exact hv (detPow_of_mem_integralGL (hsub v hvT) s)
  have hA : 0 ≤ archAbsDet (archComp K n g) :=
    Finset.prod_nonneg fun w _ ↦ pow_nonneg (norm_nonneg _) _
  have hB : ∀ v, 0 ≤ absDet (localComp n v g) := fun v ↦ NNReal.coe_nonneg _
  rw [GJGlobal.detPow, detModule_eq, h1, h2, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hA (Finset.prod_nonneg fun v _ ↦ hB v),
    GodementSection.ofReal_prod_cpow T _ hB]
  rfl

end Det

section Product

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def prodConst (ν : Measure (AdelicGLn.AdelicGL K n)) [ν.IsHaarMeasure]
    (μi : Measure (AdelicGLn.InfiniteAdelicGL K n)) [μi.IsHaarMeasure] : ℝ≥0 :=
  Measure.haarScalarFactor (ν.map (AdelicGLn.prodEquiv K n))
    (μi.prod (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K n)))

theorem prodConst_pos (ν : Measure (AdelicGLn.AdelicGL K n)) [ν.IsHaarMeasure]
    (μi : Measure (AdelicGLn.InfiniteAdelicGL K n)) [μi.IsHaarMeasure] : 0 < prodConst ν μi :=
  Measure.haarScalarFactor_pos_of_isHaarMeasure _ _

theorem map_prodEquiv_eq (ν : Measure (AdelicGLn.AdelicGL K n)) [ν.IsHaarMeasure]
    (μi : Measure (AdelicGLn.InfiniteAdelicGL K n)) [μi.IsHaarMeasure] :
    ν.map (AdelicGLn.prodEquiv K n) =
      prodConst ν μi • μi.prod (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K n)) :=
  by
    set_option synthInstance.maxHeartbeats 200000 in
      exact Measure.isMulLeftInvariant_eq_smul _ _

theorem integral_eq_mul (ν : Measure (AdelicGLn.AdelicGL K n)) [ν.IsHaarMeasure]
    (μi : Measure (AdelicGLn.InfiniteAdelicGL K n)) [μi.IsHaarMeasure]
    (A : AdelicGLn.InfiniteAdelicGL K n → ℂ) (B : AdelicGLn.FiniteAdelicGL K n → ℂ) :
    ∫ g, A (archComp K n g) * B (finComp K n g) ∂ν =
      ((prodConst ν μi : ℝ) : ℂ) * ((∫ x, A x ∂μi) * ∫ y, B y ∂Measure.haar) := by
  set me := (AdelicGLn.prodEquiv K n).toHomeomorph.toMeasurableEquiv
  have h1 : ∫ g, A (archComp K n g) * B (finComp K n g) ∂ν = ∫ p, A p.1 * B p.2 ∂(ν.map me) := by
    rw [integral_map_equiv me (fun p ↦ A p.1 * B p.2)]
    rfl
  have hme : ν.map me = ν.map (AdelicGLn.prodEquiv K n) := rfl
  set_option synthInstance.maxHeartbeats 200000 in
    rw [h1, hme, map_prodEquiv_eq ν μi, integral_smul_nnreal_measure, integral_prod_mul, NNReal.smul_def,
      Complex.real_smul]

theorem lintegral_eq_mul (ν : Measure (AdelicGLn.AdelicGL K n)) [ν.IsHaarMeasure]
    (μi : Measure (AdelicGLn.InfiniteAdelicGL K n)) [μi.IsHaarMeasure]
    {A : AdelicGLn.InfiniteAdelicGL K n → ℂ} {B : AdelicGLn.FiniteAdelicGL K n → ℂ}
    (hA : Measurable A) (hB : Measurable B) :
    ∫⁻ g, ‖A (archComp K n g) * B (finComp K n g)‖ₑ ∂ν =
      prodConst ν μi * ((∫⁻ x, ‖A x‖ₑ ∂μi) * ∫⁻ y, ‖B y‖ₑ ∂Measure.haar) := by
  set me := (AdelicGLn.prodEquiv K n).toHomeomorph.toMeasurableEquiv
  have h1 : ∫⁻ g, ‖A (archComp K n g) * B (finComp K n g)‖ₑ ∂ν =
      ∫⁻ p, ‖A p.1‖ₑ * ‖B p.2‖ₑ ∂(ν.map me) := by
    rw [lintegral_map_equiv (fun p ↦ ‖A p.1‖ₑ * ‖B p.2‖ₑ) me]
    refine lintegral_congr fun g ↦ ?_
    rw [enorm_mul]
    rfl
  have hme : ν.map me = ν.map (AdelicGLn.prodEquiv K n) := rfl
  rw [h1, hme, map_prodEquiv_eq ν μi, lintegral_smul_measure,
    lintegral_prod_mul hA.enorm.aemeasurable hB.enorm.aemeasurable, ENNReal.smul_def, smul_eq_mul]

end Product

section Finite

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

instance fact_isOpen_integralGL : Fact (∀ v : HeightOneSpectrum (𝓞 K),
    IsOpen (integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K)))) :=
  ⟨fun _ ↦ isOpen_integralGL _ n⟩

instance measurableSpace_finRes : MeasurableSpace (Πʳ v : HeightOneSpectrum (𝓞 K),
    [GL (Fin n) (v.adicCompletion K), (integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K)))]) :=
  _root_.borel _

instance borelSpace_finRes : BorelSpace (Πʳ v : HeightOneSpectrum (𝓞 K),
    [GL (Fin n) (v.adicCompletion K), (integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K)))]) :=
  ⟨rfl⟩


variable (K n) in
def finHaar : Measure (Πʳ v : HeightOneSpectrum (𝓞 K),
    [GL (Fin n) (v.adicCompletion K), (integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K)))]) :=
  (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K n)).map (AdelicGLn.finiteRestrictedEquiv K n)

instance isHaarMeasure_finHaar : (finHaar K n).IsHaarMeasure := by
  unfold finHaar
  infer_instance


variable (K n) in
def finConst : ℝ :=
  (finHaar K n).real {x | ∀ v, x v ∈ integralGL (v.adicCompletion K) n}

theorem finConst_pos : 0 < finConst K n :=
  RestrictedHaar.measureReal_setOf_forall_mem_pos _ (fun _ ↦ isOpen_integralGL _ n)
    (fun _ ↦ isCompact_integralGL _ n) _

theorem integral_finHaar_eq {B : AdelicGLn.FiniteAdelicGL K n → ℂ}
    (Φ : (Πʳ v : HeightOneSpectrum (𝓞 K),
      [GL (Fin n) (v.adicCompletion K), (integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K)))]) → ℂ)
    (hB : ∀ y, B y = Φ (AdelicGLn.finiteRestrictedEquiv K n y)) :
    ∫ y, B y ∂Measure.haar = ∫ x, Φ x ∂finHaar K n := by
  set me := (AdelicGLn.finiteRestrictedEquiv K n).toHomeomorph.toMeasurableEquiv
  rw [finHaar, show (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K n)).map
    (AdelicGLn.finiteRestrictedEquiv K n) = (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K n)).map me from rfl,
    integral_map_equiv me Φ]
  exact integral_congr_ae (Eventually.of_forall fun y ↦ hB y)

theorem integrable_finHaar_iff {B : AdelicGLn.FiniteAdelicGL K n → ℂ}
    (Φ : (Πʳ v : HeightOneSpectrum (𝓞 K),
      [GL (Fin n) (v.adicCompletion K), (integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K)))]) → ℂ)
    (hB : ∀ y, B y = Φ (AdelicGLn.finiteRestrictedEquiv K n y)) :
    Integrable B Measure.haar ↔ Integrable Φ (finHaar K n) := by
  set me := (AdelicGLn.finiteRestrictedEquiv K n).toHomeomorph.toMeasurableEquiv
  rw [finHaar, show (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K n)).map
    (AdelicGLn.finiteRestrictedEquiv K n) = (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K n)).map me from rfl,
    integrable_map_equiv me Φ]
  have : B = Φ ∘ me := funext hB
  rw [this]

theorem hasProd_finite (F : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin n) (v.adicCompletion K) → ℂ)
    (hF : ∀ v, Measurable (F v))
    (hF1 : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ∀ k ∈ integralGL (v.adicCompletion K) n, F v k = 1)
    {B : AdelicGLn.FiniteAdelicGL K n → ℂ}
    (hB : ∀ y, B y = ∏ᶠ v, F v (AdelicGLn.finiteRestrictedEquiv K n y v))
    (hint : Integrable B Measure.haar) :
    HasProd (fun v ↦ ∫ h, F v h ∂localHaar n v) ((finConst K n)⁻¹ * ∫ y, B y ∂Measure.haar) := by
  rw [integral_finHaar_eq (fun x ↦ ∏ᶠ v, F v (x v)) hB]
  have hν1 : ∀ v : HeightOneSpectrum (𝓞 K), localHaar n v
      (integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K))) = 1 :=
    fun v ↦ localHaar_integralGL v
  exact RestrictedHaar.hasProd_integral (G := fun v : HeightOneSpectrum (𝓞 K) ↦ GL (Fin n) (v.adicCompletion K))
    (fun v ↦ integralGL (v.adicCompletion K) n)
    (fun v ↦ isOpen_integralGL _ n) (fun v ↦ isCompact_integralGL _ n) (finHaar K n)
    (fun v ↦ localHaar n v) hν1 F hF hF1 (fun x ↦ ∏ᶠ v, F v (x v)) (fun x ↦ rfl)
    ((integrable_finHaar_iff _ hB).1 hint)

theorem integrable_factor_finite (F : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin n) (v.adicCompletion K) → ℂ)
    (hF : ∀ v, Measurable (F v))
    (hF1 : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ∀ k ∈ integralGL (v.adicCompletion K) n, F v k = 1)
    {B : AdelicGLn.FiniteAdelicGL K n → ℂ}
    (hB : ∀ y, B y = ∏ᶠ v, F v (AdelicGLn.finiteRestrictedEquiv K n y v))
    (hint : Integrable B Measure.haar)
    (hne : ∀ v : HeightOneSpectrum (𝓞 K), (¬ ∀ k ∈ integralGL (v.adicCompletion K) n, F v k = 1) → ∫⁻ h, ‖F v h‖ₑ ∂localHaar n v ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) : Integrable (F v) (localHaar n v) := by
  have hν1 : ∀ v : HeightOneSpectrum (𝓞 K), localHaar n v
      (integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K))) = 1 :=
    fun v ↦ localHaar_integralGL v
  exact RestrictedHaar.integrable_factor (G := fun v : HeightOneSpectrum (𝓞 K) ↦ GL (Fin n) (v.adicCompletion K))
    (fun v ↦ integralGL (v.adicCompletion K) n)
    (fun v ↦ isOpen_integralGL _ n) (fun v ↦ isCompact_integralGL _ n) (finHaar K n)
    (fun v ↦ localHaar n v) hν1 F hF hF1 (fun x ↦ ∏ᶠ v, F v (x v)) (fun x ↦ rfl)
    ((integrable_finHaar_iff _ hB).1 hint) hne v

end Finite

section ZetaNonvanishing₂

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
  {V : HeightOneSpectrum (𝓞 K) → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

def localIntegrand (Φ : ∀ v : HeightOneSpectrum (𝓞 K), Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ)
    (π : ∀ v, Representation ℂ (GL (Fin n) (v.adicCompletion K)) (V v)) (ξ : ∀ v, V v)
    (ℓ : ∀ v, Module.Dual ℂ (V v)) (s : ℂ) (v : HeightOneSpectrum (𝓞 K))
    (h : GL (Fin n) (v.adicCompletion K)) : ℂ :=
  Φ v (h : Matrix (Fin n) (Fin n) (v.adicCompletion K)) * Parabolic.matrixCoeff (π v) (ξ v) (ℓ v) h *
    detPow h (s + ((n : ℂ) - 1) / 2)

def finIntegrand (Φ : ∀ v : HeightOneSpectrum (𝓞 K), Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ)
    (π : ∀ v, Representation ℂ (GL (Fin n) (v.adicCompletion K)) (V v)) (ξ : ∀ v, V v)
    (ℓ : ∀ v, Module.Dual ℂ (V v)) (s : ℂ) (y : AdelicGLn.FiniteAdelicGL K n) : ℂ :=
  ∏ᶠ v, localIntegrand Φ π ξ ℓ s v (AdelicGLn.finiteRestrictedEquiv K n y v)

variable {S : Finset (HeightOneSpectrum (𝓞 K))}
  {Φ : ∀ v : HeightOneSpectrum (𝓞 K), Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ}
  {π : ∀ v, Representation ℂ (GL (Fin n) (v.adicCompletion K)) (V v)} {ξ : ∀ v, V v}
  {ℓ : ∀ v, Module.Dual ℂ (V v)}

theorem localIntegrand_eq_one (hS0 : ∀ v ∉ S, Φ v = integralIndicator (v.adicCompletion K) n)
    (hsph : ∀ v ∉ S, ξ v ∈ fixedVectors (π v) (integralGL (v.adicCompletion K) n) ∧ ℓ v (ξ v) = 1)
    (s : ℂ) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) {k : GL (Fin n) (v.adicCompletion K)}
    (hk : k ∈ integralGL (v.adicCompletion K) n) : localIntegrand Φ π ξ ℓ s v k = 1 := by
  rw [localIntegrand, hS0 v hv]
  exact localIntegrand_of_mem_integralGL (π v) (hsph v hv).1 (hsph v hv).2 s hk

theorem continuous_localIntegrand' (hSB : ∀ v ∈ S, IsSchwartzBruhat (Φ v))
    (hS0 : ∀ v ∉ S, Φ v = integralIndicator (v.adicCompletion K) n)
    (hξ : ∀ v, ξ v ∈ smoothVectors (π v)) (s : ℂ) (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (localIntegrand Φ π ξ ℓ s v) := by
  have hΦ : Continuous (Φ v) := by
    by_cases hv : v ∈ S
    · exact (hSB v hv).1.continuous
    · rw [hS0 v hv]
      exact isSchwartzBruhat_integralIndicator.1.continuous
  exact continuous_localIntegrand hΦ (π v) (hξ v) (ℓ v) s

theorem continuous_finIntegrand (hSB : ∀ v ∈ S, IsSchwartzBruhat (Φ v))
    (hS0 : ∀ v ∉ S, Φ v = integralIndicator (v.adicCompletion K) n)
    (hsph : ∀ v ∉ S, ξ v ∈ fixedVectors (π v) (integralGL (v.adicCompletion K) n) ∧ ℓ v (ξ v) = 1)
    (hξ : ∀ v, ξ v ∈ smoothVectors (π v)) (s : ℂ) :
    Continuous (finIntegrand Φ π ξ ℓ s) := by
  refine continuous_iff_continuousAt.2 fun y ↦ ?_
  set e := AdelicGLn.finiteRestrictedEquiv K n
  have hfin : {v : HeightOneSpectrum (𝓞 K) | e y v ∉ integralGL (v.adicCompletion K) n}.Finite :=
    Filter.eventually_cofinite.1 (e y).2
  set T := S ∪ hfin.toFinset with hT
  have hopen : IsOpen (e ⁻¹' (RestrictedHaar.box (fun v ↦ integralGL (v.adicCompletion K) n) T :
      Set (Πʳ v : HeightOneSpectrum (𝓞 K), [GL (Fin n) (v.adicCompletion K),
        (integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K)))]))) :=
    (RestrictedHaar.isOpen_box _ (fun v ↦ isOpen_integralGL _ n) T).preimage e.continuous
  have hy : y ∈ e ⁻¹' (RestrictedHaar.box (fun v ↦ integralGL (v.adicCompletion K) n) T :
      Set (Πʳ v : HeightOneSpectrum (𝓞 K), [GL (Fin n) (v.adicCompletion K),
        (integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K)))])) := by
    intro v hv
    by_contra h
    exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 h))
  have heq : ∀ z ∈ e ⁻¹' (RestrictedHaar.box (fun v ↦ integralGL (v.adicCompletion K) n) T :
      Set (Πʳ v : HeightOneSpectrum (𝓞 K), [GL (Fin n) (v.adicCompletion K),
        (integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K)))])),
      finIntegrand Φ π ξ ℓ s z = ∏ v ∈ T, localIntegrand Φ π ξ ℓ s v (e z v) := by
    intro z hz
    refine RestrictedHaar.finprod_eq_prod_of_mem_box
      (G := fun v : HeightOneSpectrum (𝓞 K) ↦ GL (Fin n) (v.adicCompletion K))
      (fun v ↦ integralGL (v.adicCompletion K) n) (F := fun v ↦ localIntegrand Φ π ξ ℓ s v)
      (fun v hv k hk ↦ ?_) hz
    exact localIntegrand_eq_one hS0 hsph s (fun h ↦ hv (Finset.mem_union_left _ h)) hk
  have hc : Continuous fun z : AdelicGLn.FiniteAdelicGL K n ↦ ∏ v ∈ T, localIntegrand Φ π ξ ℓ s v (e z v) :=
    continuous_finsetProd _ fun v _ ↦ (continuous_localIntegrand' hSB hS0 hξ s v).comp
      ((RestrictedProduct.continuous_eval v).comp e.continuous)
  refine hc.continuousAt.congr ?_
  filter_upwards [hopen.mem_nhds hy] with z hz
  exact (heq z hz).symm

theorem zetaIntegrand_eq (φ : 𝓢(Fin n × Fin n → mixedSpace K, ℂ))
    (hS0 : ∀ v ∉ S, Φ v = integralIndicator (v.adicCompletion K) n)
    (hsph : ∀ v ∉ S, ξ v ∈ fixedVectors (π v) (integralGL (v.adicCompletion K) n) ∧ ℓ v (ξ v) = 1)
    {f : AdelicGLn.AdelicGL K n → ℂ} {fi : AdelicGLn.InfiniteAdelicGL K n → ℂ}
    (hf : ∀ g, f g = fi (archComp K n g) *
      ∏ᶠ v, Parabolic.matrixCoeff (π v) (ξ v) (ℓ v) (localComp n v g)) (s : ℂ)
    (g : AdelicGLn.AdelicGL K n) :
    GJGlobal.zetaIntegrand (matrixTensor φ Φ) f s g =
      archIntegrand φ fi s (archComp K n g) * finIntegrand Φ π ξ ℓ s (finComp K n g) := by
  set U := S ∪ (finite_setOf_not_mem g).toFinset with hU
  have hout : ∀ v ∉ U, v ∉ S ∧ localComp n v g ∈ integralGL (v.adicCompletion K) n := by
    intro v hv
    refine ⟨fun h ↦ hv (Finset.mem_union_left _ h), ?_⟩
    by_contra h
    exact hv (Finset.mem_union_right _ ((finite_setOf_not_mem g).mem_toFinset.2 h))
  have h1 : ∏ᶠ v, Φ v (localComp n v g : Matrix (Fin n) (Fin n) (v.adicCompletion K)) =
      ∏ v ∈ U, Φ v (localComp n v g : Matrix (Fin n) (Fin n) (v.adicCompletion K)) :=
    finprod_eq_prod_of_mulSupport_subset _ fun v hv ↦ by
      by_contra hvU
      obtain ⟨hvS, hvK⟩ := hout v hvU
      apply hv
      dsimp only
      rw [hS0 v hvS, integralIndicator,
        Set.indicator_of_mem (mem_integralMatrixSet.2 ((mem_integralGL_iff _ n).1 hvK).1)]
      rfl
  have h2 : ∏ᶠ v, Parabolic.matrixCoeff (π v) (ξ v) (ℓ v) (localComp n v g) =
      ∏ v ∈ U, Parabolic.matrixCoeff (π v) (ξ v) (ℓ v) (localComp n v g) :=
    finprod_eq_prod_of_mulSupport_subset _ fun v hv ↦ by
      by_contra hvU
      obtain ⟨hvS, hvK⟩ := hout v hvU
      apply hv
      show (ℓ v) ((π v) (localComp n v g) (ξ v)) = 1
      rw [(hsph v hvS).1 _ hvK, (hsph v hvS).2]
  have h3 : ∏ᶠ v, detPow (localComp n v g) (s + ((n : ℂ) - 1) / 2) =
      ∏ v ∈ U, detPow (localComp n v g) (s + ((n : ℂ) - 1) / 2) :=
    finprod_eq_prod_of_mulSupport_subset _ fun v hv ↦ by
      by_contra hvU
      exact hv (detPow_of_mem_integralGL (hout v hvU).2 _)
  have h4 : finIntegrand Φ π ξ ℓ s (finComp K n g) = ∏ v ∈ U, localIntegrand Φ π ξ ℓ s v (localComp n v g) :=
    finprod_eq_prod_of_mulSupport_subset _ fun v hv ↦ by
      by_contra hvU
      exact hv (localIntegrand_eq_one hS0 hsph s (hout v hvU).1 (hout v hvU).2)
  rw [GJGlobal.zetaIntegrand, matrixTensor_coe, hf g, detPow_eq, h1, h2, h3, h4, archIntegrand]
  simp only [localIntegrand, Finset.prod_mul_distrib]
  ring

end ZetaNonvanishing₂

section Euler

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
  {V : HeightOneSpectrum (𝓞 K) → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
  {S : Finset (HeightOneSpectrum (𝓞 K))}
  {Φ : ∀ v : HeightOneSpectrum (𝓞 K), Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ}
  {π : ∀ v, Representation ℂ (GL (Fin n) (v.adicCompletion K)) (V v)} {ξ : ∀ v, V v}
  {ℓ : ∀ v, Module.Dual ℂ (V v)}

theorem continuous_archSchwartz (φ : 𝓢(Fin n × Fin n → mixedSpace K, ℂ)) :
    Continuous fun x : AdelicGLn.InfiniteAdelicGL K n ↦
      archSchwartz φ (x : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) :=
  by
    simp_rw [archSchwartz_eq]
    exact φ.continuous.comp ((archEntries K n).continuous.comp
      (Units.continuous_val : Continuous (Units.val : AdelicGLn.InfiniteAdelicGL K n →
        Matrix (Fin n) (Fin n) (InfiniteAdeleRing K))))

theorem continuous_archIntegrand (φ : 𝓢(Fin n × Fin n → mixedSpace K, ℂ))
    {fi : AdelicGLn.InfiniteAdelicGL K n → ℂ} (hfi : Continuous fi) (s : ℂ) :
    Continuous (archIntegrand φ fi s) :=
  ((continuous_archSchwartz φ).mul hfi).mul (continuous_archDetPow _)

theorem globalZeta_eq_euler (ν : Measure (AdelicGLn.AdelicGL K n)) [ν.IsHaarMeasure]
    (μi : Measure (AdelicGLn.InfiniteAdelicGL K n)) [μi.IsHaarMeasure]
    (φ : 𝓢(Fin n × Fin n → mixedSpace K, ℂ))
    (hSB : ∀ v ∈ S, IsSchwartzBruhat (Φ v))
    (hS0 : ∀ v ∉ S, Φ v = integralIndicator (v.adicCompletion K) n)
    (hξ : ∀ v, ξ v ∈ smoothVectors (π v))
    (hsph : ∀ v ∉ S, ξ v ∈ fixedVectors (π v) (integralGL (v.adicCompletion K) n) ∧ ℓ v (ξ v) = 1)
    {f : AdelicGLn.AdelicGL K n → ℂ} {fi : AdelicGLn.InfiniteAdelicGL K n → ℂ} (hfi : Continuous fi)
    (hf : ∀ g, f g = fi (archComp K n g) *
      ∏ᶠ v, Parabolic.matrixCoeff (π v) (ξ v) (ℓ v) (localComp n v g))
    {s : ℂ} (hint : Integrable (GJGlobal.zetaIntegrand (matrixTensor φ Φ) f s) ν) :
    GJGlobal.globalZeta ν (matrixTensor φ Φ) f s =
        (((prodConst ν μi : ℝ) * finConst K n : ℝ) : ℂ) * archZeta μi φ fi s *
          ∏' v, zetaIntegral (localHaar n v) (Φ v) (Parabolic.matrixCoeff (π v) (ξ v) (ℓ v)) s ∧
      (¬ (archIntegrand φ fi s =ᵐ[μi] 0) →
        Integrable (finIntegrand Φ π ξ ℓ s) Measure.haar ∧
        HasProd (fun v ↦ zetaIntegral (localHaar n v) (Φ v) (Parabolic.matrixCoeff (π v) (ξ v) (ℓ v)) s)
          (∏' v, zetaIntegral (localHaar n v) (Φ v) (Parabolic.matrixCoeff (π v) (ξ v) (ℓ v)) s)) := by
  set A := archIntegrand φ fi s with hAdef
  set B := finIntegrand Φ π ξ ℓ s with hBdef
  have hA : Continuous A := continuous_archIntegrand φ hfi s
  have hB : Continuous B := continuous_finIntegrand hSB hS0 hsph hξ s
  have hH : GJGlobal.zetaIntegrand (matrixTensor φ Φ) f s =
      fun g ↦ A (archComp K n g) * B (finComp K n g) := funext (zetaIntegrand_eq φ hS0 hsph hf s)
  have hZ : GJGlobal.globalZeta ν (matrixTensor φ Φ) f s =
      ((prodConst ν μi : ℝ) : ℂ) * ((∫ x, A x ∂μi) * ∫ y, B y ∂Measure.haar) := by
    rw [GJGlobal.globalZeta, hH]
    exact integral_eq_mul ν μi A B
  have hzA : archZeta μi φ fi s = ∫ x, A x ∂μi := rfl
  by_cases h0 : A =ᵐ[μi] 0
  · have hA0 : ∫ x, A x ∂μi = 0 := by
      rw [integral_congr_ae h0]
      simp
    refine ⟨?_, fun h ↦ absurd h0 h⟩
    rw [hZ, hzA, hA0]
    simp
  · have hBint : Integrable B Measure.haar := by
      have hl := lintegral_eq_mul ν μi hA.measurable hB.measurable
      have hfin : ∫⁻ g, ‖A (archComp K n g) * B (finComp K n g)‖ₑ ∂ν < ⊤ := by
        have := hint.2
        rwa [hH] at this
      rw [hl] at hfin
      have hAne : ∫⁻ x, ‖A x‖ₑ ∂μi ≠ 0 := by
        intro h
        apply h0
        rw [lintegral_eq_zero_iff hA.measurable.enorm] at h
        filter_upwards [h] with x hx
        simpa using hx
      have hc0 : (prodConst ν μi : ℝ≥0∞) ≠ 0 := by exact_mod_cast (prodConst_pos ν μi).ne'
      refine ⟨hB.aestronglyMeasurable, ?_⟩
      have h1 := ENNReal.lt_top_of_mul_ne_top_right hfin.ne hc0
      exact ENNReal.lt_top_of_mul_ne_top_right h1.ne hAne
    have hP := hasProd_finite (fun v ↦ localIntegrand Φ π ξ ℓ s v)
      (fun v ↦ (continuous_localIntegrand' hSB hS0 hξ s v).measurable)
      (by
        filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv k hk
        exact localIntegrand_eq_one hS0 hsph s hv hk)
      (fun y ↦ rfl) hBint
    have hval := hP.tprod_eq
    refine ⟨?_, fun _ ↦ ⟨hBint, hP.multipliable.hasProd⟩⟩
    have hzv : (fun v ↦ zetaIntegral (localHaar n v) (Φ v) (Parabolic.matrixCoeff (π v) (ξ v) (ℓ v)) s) =
        fun v ↦ ∫ h, localIntegrand Φ π ξ ℓ s v h ∂localHaar n v := rfl
    rw [hZ, hzA, hzv, hval]
    have hf0 : (finConst K n : ℂ) ≠ 0 := by exact_mod_cast (finConst_pos (K := K) (n := n)).ne'
    push_cast
    field_simp
    rfl

end Euler

end GJStandardL

end

end GroundTheory.Automorphic
end

open MeasureTheory Filter Set Topology IsDedekindDomain NumberField NumberField.mixedEmbedding
open scoped NumberField.AdeleRing RestrictedProduct SchwartzMap Classical ENNReal NNReal

namespace GroundTheory.Automorphic

noncomputable section

namespace GJStandardL

open GodementJacquet GLnLocal

set_option linter.unusedSectionVars false

section Continuity

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem exists_norm_le_of_cusp (hn : 0 < n) {φ : AdelicGLn.AdelicGL K n → ℂ}
    (hφ : φ ∈ AutomorphicForm.cuspForms K n)
    (hA : ∀ (t : {r : ℝ // 0 < r}) (x : AdelicGLn.AdelicGL K n), φ (Reduction.centralSection K n t * x) = φ x) :
    ∃ C : ℝ, ∀ y, ‖φ y‖ ≤ C := by
  obtain ⟨C, hC⟩ := CuspidalSpectrum.exists_norm_le_of_mem_cuspForms hφ
  refine ⟨C, fun y ↦ ?_⟩
  set p := (GJGlobal.splitEquiv (K := K) hn).symm y
  have hy : y = (p.1 : AdelicGLn.AdelicGL K n) * Reduction.centralSection K n p.2 := by
    rw [← GJGlobal.splitEquiv_apply hn p, MeasurableEquiv.apply_symm_apply]
  rw [hy, ← Reduction.centralSection_mul_comm, hA]
  exact hC _ p.1.2

theorem continuous_globalMatrixCoeff (hn : 0 < n) (μ : Measure (Reduction.normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    {φ₁ φ₂ : AdelicGLn.AdelicGL K n → ℂ} (h₁ : φ₁ ∈ AutomorphicForm.cuspForms K n)
    (h₂ : φ₂ ∈ AutomorphicForm.cuspForms K n)
    (hA : ∀ (t : {r : ℝ // 0 < r}) (x : AdelicGLn.AdelicGL K n), φ₁ (Reduction.centralSection K n t * x) = φ₁ x) :
    Continuous (GJGlobal.matrixCoeff μ φ₁ φ₂) := by
  set_option synthInstance.maxHeartbeats 200000 in
  haveI : FirstCountableTopology (AdelicGLn.AdelicGL K n) := inferInstance
  obtain ⟨C₁, hC₁⟩ := exists_norm_le_of_cusp hn h₁ hA
  obtain ⟨C₂, hC₂⟩ := CuspidalSpectrum.exists_norm_le_of_mem_cuspForms h₂
  have h1c : Continuous φ₁ := h₁.1.continuous
  have h2c : Continuous φ₂ := h₂.1.continuous
  have hfin : μ (RightCosetSpace.fundamentalDomain (Reduction.rationalGLOne (K := K) (n := n))) < ⊤ :=
    GJGlobal.measure_fundamentalDomain_rationalGLOne_lt_top μ
  have : IsFiniteMeasure (μ.restrict (RightCosetSpace.fundamentalDomain (Reduction.rationalGLOne (K := K) (n := n)))) :=
    isFiniteMeasure_restrict.2 hfin.ne
  refine continuous_of_dominated (bound := fun _ ↦ C₁ * C₂) (fun g ↦ ?_) (fun g ↦ ?_)
    (integrable_const _) (Eventually.of_forall fun x ↦ ?_)
  · exact ((h1c.comp (continuous_subtype_val.mul continuous_const)).mul
      (continuous_star.comp (h2c.comp continuous_subtype_val))).aestronglyMeasurable
  · refine Eventually.of_forall fun x ↦ ?_
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hC₁ _) (hC₂ _ x.2) (norm_nonneg _) ((norm_nonneg _).trans (hC₁ 1))
  · exact (h1c.comp (continuous_const.mul continuous_id)).mul continuous_const

end Continuity

theorem hasProd_compl_of_hasProd {ι : Type*} {f : ι → ℂ} {a : ℂ} (h : HasProd f a) (S : Finset ι)
    (hS : ∀ i ∈ S, f i ≠ 0) :
    HasProd (fun i : {i // i ∉ S} ↦ f i) (a / ∏ i ∈ S, f i) := by
  set g : ι → ℂ := (S : Set ι).mulIndicator fun i ↦ (f i)⁻¹ with hg
  have hgp : HasProd g (∏ i ∈ S, (f i)⁻¹) := by
    have : HasProd g (∏ i ∈ S, g i) := hasProd_prod_of_ne_finset_one fun i hi ↦ by
      rw [hg, Set.mulIndicator_of_notMem (by simpa using hi)]
    rwa [Finset.prod_congr rfl fun i hi ↦ by rw [hg, Set.mulIndicator_of_mem (by simpa using hi)]] at this
  have hfg := h.mul hgp
  have heq : (fun i ↦ f i * g i) = ({i | i ∉ S} : Set ι).mulIndicator f := by
    funext i
    by_cases hi : i ∈ S
    · rw [hg, Set.mulIndicator_of_mem (by simpa using hi),
        Set.mulIndicator_of_notMem (by simpa using hi), mul_inv_cancel₀ (hS i hi)]
    · rw [hg, Set.mulIndicator_of_notMem (by simpa using hi),
        Set.mulIndicator_of_mem (by simpa using hi), mul_one]
  rw [heq, Finset.prod_inv_distrib, ← div_eq_mul_inv] at hfg
  exact (hasProd_subtype_iff_mulIndicator (s := {i | i ∉ S})).2 hfg

section Partial

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

end Partial

section Main

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem detPow_ne_zero' {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (g : GL (Fin n) F) (s : ℂ) : detPow g s ≠ 0 := by
  have hq : (LocalField.residueCard F : ℂ) ≠ 0 := Nat.cast_ne_zero.2 LocalField.residueCard_ne_zero
  rw [detPow_eq_qs_zpow, qs]
  exact zpow_ne_zero _ fun h ↦ hq ((Complex.cpow_eq_zero_iff _ _).1 h).1

theorem archComp_prodEquiv_symm (x : AdelicGLn.InfiniteAdelicGL K n) (y : AdelicGLn.FiniteAdelicGL K n) :
    archComp K n ((AdelicGLn.prodEquiv K n).symm (x, y)) = x := by
  show ((AdelicGLn.prodEquiv K n) ((AdelicGLn.prodEquiv K n).symm (x, y))).1 = x
  rw [ContinuousMulEquiv.apply_symm_apply]

theorem localComp_prodEquiv_symm (v : HeightOneSpectrum (𝓞 K)) (x : AdelicGLn.InfiniteAdelicGL K n)
    (y : AdelicGLn.FiniteAdelicGL K n) :
    localComp n v ((AdelicGLn.prodEquiv K n).symm (x, y)) = AdelicGLn.finiteRestrictedEquiv K n y v := by
  show AdelicGLn.finiteRestrictedEquiv K n
    ((AdelicGLn.prodEquiv K n) ((AdelicGLn.prodEquiv K n).symm (x, y))).2 v = _
  rw [ContinuousMulEquiv.apply_symm_apply]

end Main

end GJStandardL

end

end GroundTheory.Automorphic
end

open MeasureTheory Filter Set Topology IsDedekindDomain NumberField NumberField.mixedEmbedding
open scoped NumberField.AdeleRing RestrictedProduct SchwartzMap Classical ENNReal NNReal

namespace GroundTheory.Automorphic

noncomputable section

namespace GJStandardL

open GodementJacquet GLnLocal

theorem hasProd_of_hasProd_compl {ι : Type*} {f : ι → ℂ} {b : ℂ} (S : Finset ι)
    (h : HasProd (fun i : {i // i ∉ S} ↦ f i) b) : HasProd f ((∏ i ∈ S, f i) * b) := by
  have h1 : HasProd ((S : Set ι).mulIndicator f) (∏ i ∈ S, f i) := by
    have : HasProd ((S : Set ι).mulIndicator f) (∏ i ∈ S, (S : Set ι).mulIndicator f i) :=
      hasProd_prod_of_ne_finset_one fun i hi ↦ Set.mulIndicator_of_notMem (by simpa using hi) _
    rwa [Finset.prod_congr rfl fun i hi ↦ Set.mulIndicator_of_mem (by simpa using hi) f] at this
  have h2 : HasProd (({i | i ∉ S} : Set ι).mulIndicator f) b :=
    (hasProd_subtype_iff_mulIndicator (s := {i | i ∉ S})).1 h
  have h3 := h1.mul h2
  have heq : (fun i ↦ (S : Set ι).mulIndicator f i * ({i | i ∉ S} : Set ι).mulIndicator f i) = f := by
    funext i
    by_cases hi : i ∈ S
    · rw [Set.mulIndicator_of_mem (by simpa using hi), Set.mulIndicator_of_notMem (by simpa using hi),
        mul_one]
    · rw [Set.mulIndicator_of_notMem (by simpa using hi), Set.mulIndicator_of_mem (by simpa using hi),
        one_mul]
  rwa [heq] at h3

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem exists_sphericalIntegrable (ν : Measure (AdelicGLn.AdelicGL K n)) [ν.IsHaarMeasure]
    {f : AdelicGLn.AdelicGL K n → ℂ} (hfc : Continuous f)
    (hP : ∀ Ψ ∈ GJMatrix.matrixSchwartzBruhat K n, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (GJGlobal.zetaIntegrand Ψ f s) ν)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    {V : HeightOneSpectrum (𝓞 K) → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
    (π : ∀ v, Representation ℂ (GL (Fin n) (v.adicCompletion K)) (V v)) (ξ : ∀ v, V v)
    (ℓ : ∀ v, Module.Dual ℂ (V v)) (hξ : ∀ v, ξ v ∈ smoothVectors (π v))
    (hsph : ∀ v ∉ S, ξ v ∈ fixedVectors (π v) (integralGL (v.adicCompletion K) n) ∧ ℓ v (ξ v) = 1)
    (fi : AdelicGLn.InfiniteAdelicGL K n → ℂ)
    (hf : ∀ g, f g = fi (archComp K n g) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v)
        (localComp n v g))
    (hf0 : ∃ g, f g ≠ 0) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      (∀ v ∉ S, Integrable (fun g : GL (Fin n) (v.adicCompletion K) ↦
        integralIndicator (v.adicCompletion K) n (g : Matrix (Fin n) (Fin n) (v.adicCompletion K)) *
          Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v) g *
            detPow g (s + ((n : ℂ) - 1) / 2)) (localHaar n v)) ∧
      Multipliable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} ↦
        zetaIntegral (localHaar n (v : HeightOneSpectrum (𝓞 K)))
          (integralIndicator ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K) n)
          (Parabolic.matrixCoeff (F := (v : HeightOneSpectrum (𝓞 K)).adicCompletion K) (π v) (ξ v) (ℓ v)) s := by
  obtain ⟨g₀, hg₀⟩ := hf0
  set c₀ := ∏ᶠ v : HeightOneSpectrum (𝓞 K),
    Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v) (localComp n v g₀) with hc₀
  have hsupp : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) ↦
      Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v) (localComp n v g₀)).Finite := by
    refine ((finite_setOf_not_mem g₀).union S.finite_toSet).subset fun v hv ↦ ?_
    by_contra hc
    simp only [mem_union, Finset.mem_coe, not_or] at hc
    have hK : localComp n v g₀ ∈ integralGL (v.adicCompletion K) n := by
      by_contra h
      exact hc.1 h
    apply hv
    show ℓ v (π v (localComp n v g₀) (ξ v)) = 1
    rw [(hsph v hc.2).1 _ hK, (hsph v hc.2).2]
  rw [hf g₀] at hg₀
  have hfi0 : fi (archComp K n g₀) ≠ 0 := left_ne_zero_of_mul hg₀
  have hc₀0 : c₀ ≠ 0 := right_ne_zero_of_mul hg₀
  have hloc0 : ∀ v : HeightOneSpectrum (𝓞 K),
      Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v) (localComp n v g₀) ≠ 0 :=
    fun v h ↦ hc₀0 (finprod_eq_zero _ v h hsupp)
  have hfic : Continuous fi := by
    have key : ∀ x, fi x = f ((AdelicGLn.prodEquiv K n).symm (x, finComp K n g₀)) / c₀ := by
      intro x
      have : f ((AdelicGLn.prodEquiv K n).symm (x, finComp K n g₀)) = fi x * c₀ := by
        rw [hf, archComp_prodEquiv_symm]
        simp_rw [localComp_prodEquiv_symm]
        rfl
      rw [this, mul_div_cancel_right₀ _ hc₀0]
    have hc : Continuous fun x ↦ f ((AdelicGLn.prodEquiv K n).symm (x, finComp K n g₀)) / c₀ :=
      (hfc.comp ((AdelicGLn.prodEquiv K n).symm.continuous.comp
        (continuous_id.prodMk continuous_const))).div_const c₀
    exact hc.congr fun x ↦ (key x).symm
  set μi : Measure (AdelicGLn.InfiniteAdelicGL K n) := Measure.haar
  obtain ⟨φ, -, hφne, -, -⟩ := exists_archBump μi hfic hfi0
  have hbump : ∀ v ∈ S, ∃ Φ : Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ, IsSchwartzBruhat Φ ∧
      ∃ a : ℂ, a ≠ 0 ∧ ∀ s : ℂ,
        Integrable (fun g : GL (Fin n) (v.adicCompletion K) ↦ Φ (g : Matrix (Fin n) (Fin n) (v.adicCompletion K)) *
          Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v) g *
            detPow g (s + ((n : ℂ) - 1) / 2)) (localHaar n v) ∧
        ∫⁻ g : GL (Fin n) (v.adicCompletion K), ‖Φ (g : Matrix (Fin n) (Fin n) (v.adicCompletion K)) *
          Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v) g *
            detPow g (s + ((n : ℂ) - 1) / 2)‖ₑ ∂localHaar n v ≠ 0 ∧
        zetaIntegral (localHaar n v) Φ (Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v)) s =
          a * detPow (localComp n v g₀) (s + ((n : ℂ) - 1) / 2) :=
    fun v _ ↦ exists_localBump (localHaar n v) (π v) (hξ v) (ℓ v) (hloc0 v)
  choose Φb hΦbSB a ha hΦb using hbump
  set Φ : ∀ v : HeightOneSpectrum (𝓞 K), Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ :=
    fun v ↦ if h : v ∈ S then Φb v h else integralIndicator (v.adicCompletion K) n with hΦdef
  have hΦS : ∀ v (hv : v ∈ S), Φ v = Φb v hv := fun v hv ↦ by simp only [hΦdef, dif_pos hv]
  have hSB : ∀ v ∈ S, IsSchwartzBruhat (Φ v) := fun v hv ↦ by rw [hΦS v hv]; exact hΦbSB v hv
  have hS0 : ∀ v ∉ S, Φ v = integralIndicator (v.adicCompletion K) n :=
    fun v hv ↦ by simp only [hΦdef, dif_neg hv]
  obtain ⟨σ₀, hσ₀⟩ := hP _ (matrixTensor_mem φ S Φ hSB hS0)
  refine ⟨σ₀, fun s hs ↦ ?_⟩
  obtain ⟨-, hE2⟩ := globalZeta_eq_euler ν μi φ hSB hS0 hξ hsph hfic hf (hσ₀ s hs)
  have hAne : ¬ (archIntegrand φ fi s =ᵐ[μi] 0) := by
    intro h0
    apply hφne s
    have h0' : (fun x ↦ ‖archIntegrand φ fi s x‖ₑ) =ᵐ[μi] 0 := h0.mono fun x hx ↦ by simp [hx]
    rw [lintegral_congr_ae h0']
    simp
  obtain ⟨hBint, hP'⟩ := hE2 hAne
  have hlocint : ∀ v, Integrable (localIntegrand Φ π ξ ℓ s v) (localHaar n v) :=
    integrable_factor_finite (localIntegrand Φ π ξ ℓ s)
      (fun v ↦ (continuous_localIntegrand' hSB hS0 hξ s v).measurable)
      (by
        filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv k hk
        exact localIntegrand_eq_one hS0 hsph s hv hk)
      (fun y ↦ rfl) hBint (fun v hv ↦ by
        by_cases hvS : v ∈ S
        · have := (hΦb v hvS s).2.1
          simp only [localIntegrand, hΦS v hvS]
          exact this
        · exact absurd (fun k hk ↦ localIntegrand_eq_one hS0 hsph s hvS hk) hv)
  have hram0 : ∀ v ∈ S, zetaIntegral (localHaar n v) (Φ v)
      (Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v)) s ≠ 0 := by
    intro v hv
    rw [hΦS v hv, (hΦb v hv s).2.2]
    exact mul_ne_zero (ha v hv) (detPow_ne_zero' _ _)
  refine ⟨fun v hv ↦ ?_, ?_⟩
  · refine (hlocint v).congr (Eventually.of_forall fun g ↦ ?_)
    simp only [localIntegrand, hS0 v hv]
  · refine (hasProd_compl_of_hasProd hP' S hram0).multipliable.congr fun v ↦ ?_
    rw [hS0 v v.2]

end GJStandardL

end

end GroundTheory.Automorphic
