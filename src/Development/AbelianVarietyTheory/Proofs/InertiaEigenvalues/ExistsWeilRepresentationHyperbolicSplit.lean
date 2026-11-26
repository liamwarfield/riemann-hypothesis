module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordInjectiveRangeMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PiExteriorTensorFlattenedIndexEquivNested

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentCoordinatesStructure
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentCoordinatesStructure
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Hyp

theorem coord_structure : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (e : A.L), e * e = e → star e = 1 - e → (∀ p, Hyp.ci A e (Hyp.cc A e p) = p) ∧ (∀ y, Hyp.cc A e (Hyp.ci A e y) = y) ∧ (∀ p, A.NL (Hyp.cc A e p) = p.1 * p.2) ∧ (∀ (ψ : AddChar F ℂ) (x : A.K) (p q : A.K × A.K), A.kerL ψ x (Hyp.cc A e q) (Hyp.cc A e p) = Hyp.kx A ψ x q.1 p.2 * Hyp.kx A ψ x q.2 p.1) ∧ (∀ (s : A.K) p, s • Hyp.cc A e p = Hyp.cc A e (s * p.1, s * p.2)) ∧ ∀ s : A.Kˣ, IsUnit (Hyp.cc A e ((s : A.K), 1)) := by
  intro F E _ _ _ _ _ A e hee hse
  obtain ⟨-, hinj, hnorm, htr, -⟩ := Et.quadratic_structure F E A
  have htrs : ∀ (a : A.K) (f : A.L),
      Algebra.trace A.K A.L (algebraMap A.K A.L a * f) = a * Algebra.trace A.K A.L f := by
    intro a f
    rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  have hone : ∀ f : A.L, star f = 1 - f → Algebra.trace A.K A.L f = 1 := by
    intro f hf
    apply hinj
    rw [htr, hf, map_one]
    ring
  have hte : Algebra.trace A.K A.L e = 1 := hone e hse
  have htf : Algebra.trace A.K A.L (1 - e) = 1 :=
    hone (1 - e) (by rw [star_sub, star_one, hse])
  have hst : ∀ p : A.K × A.K, star (Hyp.cc A e p) =
      algebraMap A.K A.L p.1 * (1 - e) + algebraMap A.K A.L p.2 * e := by
    intro p
    simp only [Hyp.cc, star_add, star_mul, star_sub, star_one, hse, A.star_K]
    ring
  have hme : ∀ p : A.K × A.K, Hyp.cc A e p * e = algebraMap A.K A.L p.1 * e := by
    intro p
    simp only [Hyp.cc]
    linear_combination (algebraMap A.K A.L p.1 - algebraMap A.K A.L p.2) * hee
  have hmf : ∀ p : A.K × A.K, Hyp.cc A e p * (1 - e) = algebraMap A.K A.L p.2 * (1 - e) := by
    intro p
    simp only [Hyp.cc]
    linear_combination (algebraMap A.K A.L p.2 - algebraMap A.K A.L p.1) * hee
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    simp only [Hyp.ci]
    rw [hme p, hmf p, htrs, htrs, hte, htf, mul_one, mul_one]
  · intro y
    simp only [Hyp.cc, Hyp.ci, htr, star_mul, star_sub, star_one, hse]
    linear_combination (2 * y - 2 * star y) * hee
  · intro p
    apply hinj
    rw [hnorm, hst, map_mul]
    simp only [Hyp.cc]
    linear_combination (-(algebraMap A.K A.L p.1 - algebraMap A.K A.L p.2) ^ 2) * hee
  · intro ψ x p q
    have hprod : star (Hyp.cc A e q) * Hyp.cc A e p =
        algebraMap A.K A.L (q.1 * p.2) * (1 - e) + algebraMap A.K A.L (q.2 * p.1) * e := by
      rw [hst]
      simp only [Hyp.cc, map_mul]
      linear_combination
        (algebraMap A.K A.L q.1 * algebraMap A.K A.L p.2 + algebraMap A.K A.L q.2 * algebraMap A.K A.L p.1
          - algebraMap A.K A.L q.1 * algebraMap A.K A.L p.1
          - algebraMap A.K A.L q.2 * algebraMap A.K A.L p.2) * hee
    have ht : Algebra.trace A.K A.L (star (Hyp.cc A e q) * Hyp.cc A e p) = q.1 * p.2 + q.2 * p.1 := by
      rw [hprod, map_add (f := _), htrs, htrs, hte, htf, mul_one, mul_one]
    simp only [Et.kerL, Hyp.kx, Et.psiK]
    rw [ht]
    rw [show x * (q.1 * p.2 + q.2 * p.1) = x * q.1 * p.2 + x * q.2 * p.1 by ring, map_add (f := _),
      AddChar.map_add_eq_mul]
  · intro s p
    simp only [Hyp.cc, Algebra.smul_def, map_mul]
    ring
  · intro s
    have hs : algebraMap A.K A.L (s : A.K) * algebraMap A.K A.L ((s⁻¹ : A.Kˣ) : A.K) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    refine isUnit_iff_exists_inv.mpr ⟨Hyp.cc A e (((s⁻¹ : A.Kˣ) : A.K), 1), ?_⟩
    simp only [Hyp.cc, map_one]
    linear_combination
      (2 - algebraMap A.K A.L (s : A.K) - algebraMap A.K A.L ((s⁻¹ : A.Kˣ) : A.K)) * hee + e * e * hs

end GlobalTheory.JR.Hyp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentCoordinatesStructureStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentCoordinates_structure : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (e : A.L), e * e = e → star e = 1 - e → (∀ p, Hyp.ci A e (Hyp.cc A e p) = p) ∧ (∀ y, Hyp.cc A e (Hyp.ci A e y) = y) ∧ (∀ p, A.NL (Hyp.cc A e p) = p.1 * p.2) ∧ (∀ (ψ : AddChar F ℂ) (x : A.K) (p q : A.K × A.K), A.kerL ψ x (Hyp.cc A e q) (Hyp.cc A e p) = Hyp.kx A ψ x q.1 p.2 * Hyp.kx A ψ x q.2 p.1) ∧ (∀ (s : A.K) p, s • Hyp.cc A e p = Hyp.cc A e (s * p.1, s * p.2)) ∧ ∀ s : A.Kˣ, IsUnit (Hyp.cc A e ((s : A.K), 1)) := by
  first | exact @GlobalTheory.JR.Hyp.coord_structure | exact GlobalTheory.JR.Hyp.coord_structure | (intros; apply GlobalTheory.JR.Hyp.coord_structure <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportIdempotentCoordin
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportIdempotentCoordin
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Hyp

theorem isTest_coord : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (e : A.L), (∀ p, Hyp.ci A e (Hyp.cc A e p) = p) → (∀ y, Hyp.cc A e (Hyp.ci A e y) = y) → (∀ φ : A.L → ℂ, IsTest φ → IsTest (fun p => φ (Hyp.cc A e p))) ∧ ∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (fun y => Φ (Hyp.ci A e y)) := by
  intro F E _ _ _ _ _ A e h1 h2
  let ι : A.K →ₗ[F] A.L := (Algebra.linearMap A.K A.L).restrictScalars F
  let f : (A.K × A.K) →ₗ[F] A.L :=
    LinearMap.mulRight F e ∘ₗ ι ∘ₗ LinearMap.fst F A.K A.K +
      LinearMap.mulRight F (1 - e) ∘ₗ ι ∘ₗ LinearMap.snd F A.K A.K
  let tr : A.L →ₗ[F] A.K := (Algebra.trace A.K A.L).restrictScalars F
  let g : A.L →ₗ[F] A.K × A.K :=
    LinearMap.prod (tr ∘ₗ LinearMap.mulRight F e) (tr ∘ₗ LinearMap.mulRight F (1 - e))
  haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L
  have hf : ∀ p, f p = cc A e p := fun p => rfl
  have hg : ∀ y, g y = ci A e y := fun y => rfl
  have cf : Continuous (cc A e) := by
    have := IsModuleTopology.continuous_of_linearMap f
    simpa [funext hf] using this
  have cg : Continuous (ci A e) := by
    have := IsModuleTopology.continuous_of_linearMap g
    simpa [funext hg] using this
  let H : (A.K × A.K) ≃ₜ A.L :=
    { toFun := cc A e, invFun := ci A e, left_inv := h1, right_inv := h2,
      continuous_toFun := cf, continuous_invFun := cg }
  refine ⟨fun φ hφ => ⟨hφ.1.comp_continuous cf, hφ.2.comp_homeomorph H⟩,
    fun Φ hΦ => ⟨hΦ.1.comp_continuous cg, hΦ.2.comp_homeomorph H.symm⟩⟩

end GlobalTheory.JR.Hyp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportIdempotentCoordinStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyConstantCompactSupport_idempotentCoordinates_iff : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (e : A.L), (∀ p, Hyp.ci A e (Hyp.cc A e p) = p) → (∀ y, Hyp.cc A e (Hyp.ci A e y) = y) → (∀ φ : A.L → ℂ, IsTest φ → IsTest (fun p => φ (Hyp.cc A e p))) ∧ ∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (fun y => Φ (Hyp.ci A e y)) := by
  first | exact @GlobalTheory.JR.Hyp.isTest_coord | exact GlobalTheory.JR.Hyp.isTest_coord | (intros; apply GlobalTheory.JR.Hyp.isTest_coord <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantEtaleTraceAddCharHermitianKerne
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantEtaleTraceAddCharHermitianKerne
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Hyp

theorem isLocallyConstant_of_isStdChar {F : Type} [NontriviallyNormedField F] (ψ : AddChar F ℂ)
    (hψ : IsStdChar ψ) : IsLocallyConstant (fun t : F => ψ t) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  filter_upwards [Metric.closedBall_mem_nhds x one_pos] with y hy
  have hs : ‖y - x‖ ≤ 1 := by simpa [dist_eq_norm] using hy
  have : y = x + (y - x) := by abel
  rw [this, AddChar.map_add_eq_mul, hψ.1 _ hs, mul_one]

def kerLinF {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    (A : Et F E) (x : A.K) (y' : A.L) : A.L →ₗ[F] F where
  toFun y := Algebra.trace F A.K (x * Algebra.trace A.K A.L (star y * y'))
  map_add' a b := by simp [star_add, add_mul, mul_add, map_add (f := _)]
  map_smul' c a := by
    have hc : star (algebraMap F A.L c) = algebraMap F A.L c := by
      rw [IsScalarTower.algebraMap_apply F A.K A.L]; exact A.star_K _
    have h1 : star (c • a) * y' = (algebraMap F A.K c) • (star a * y') := by
      rw [Algebra.smul_def, star_mul, hc, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]; ring
    rw [h1, map_smul, smul_eq_mul, ← mul_assoc, mul_comm x, mul_assoc, ← Algebra.smul_def, map_smul]
    rfl

theorem isLocallyConstant_psiK_kerL (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) :
    IsLocallyConstant (A.psiK ψ) ∧ ∀ (x : A.K) (y' : A.L), IsLocallyConstant (fun y => A.kerL ψ x y y') := by
  have hl := isLocallyConstant_of_isStdChar ψ hψ
  refine ⟨?_, fun x y' => ?_⟩
  · have hc : Continuous (Algebra.trace F A.K) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.trace F A.K)
    exact hl.comp_continuous hc
  · have hc : Continuous (kerLinF A x y') := IsModuleTopology.continuous_of_linearMap _
    exact hl.comp_continuous hc

end GlobalTheory.JR.Hyp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantEtaleTraceAddCharHermitianKerneStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyConstant_etaleTraceAddChar_hermitianKernel : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → IsLocallyConstant (A.psiK ψ) ∧ ∀ (x : A.K) (y' : A.L), IsLocallyConstant (fun y => A.kerL ψ x y y') := by
  first | exact @GlobalTheory.JR.Hyp.isLocallyConstant_psiK_kerL | exact GlobalTheory.JR.Hyp.isLocallyConstant_psiK_kerL | (intros; apply GlobalTheory.JR.Hyp.isLocallyConstant_psiK_kerL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyperbolicPartialFourierTwiceEqReflection
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyperbolicPartialFourierTwiceEqReflection
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR.Hyp

theorem pt_pt_eq_reflect : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (ν : Measure A.K), SelfDual ν (Hyp.kx A ψ x) → ∀ Φ : A.K × A.K → ℂ, IsTest Φ → Hyp.pt A ν ψ x (Hyp.pt A ν ψ x Φ) = fun p => Φ (p.1, -p.2) := by
  intro F E _ _ _ _ _ A ψ x ν hsd Φ hΦ

  haveI : T2Space A.K := by
    let e := (Module.finBasis F A.K).equivFun
    have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    first
      | exact T2Space.of_continuous_injective e.injective he
      | exact T2Space.of_injective_continuous e.injective he
      | exact e.injective.t2Space he
  funext p
  have hemb : Topology.IsClosedEmbedding (Prod.mk p.1 : A.K → A.K × A.K) := by
    refine ⟨isEmbedding_prodMkRight p.1, ?_⟩
    have : Set.range (Prod.mk p.1 : A.K → A.K × A.K) = ({p.1} : Set A.K) ×ˢ Set.univ := by
      ext ⟨a, b⟩
      simp only [Set.mem_range, Prod.mk.injEq, Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, and_true]
      constructor
      · rintro ⟨y, rfl, rfl⟩; rfl
      · rintro rfl; exact ⟨b, rfl, rfl⟩
    rw [this]
    exact isClosed_singleton.prod isClosed_univ
  have hf : IsTest (fun b => Φ (p.1, b)) :=
    ⟨hΦ.1.comp_continuous hemb.continuous, hΦ.2.comp_isClosedEmbedding hemb⟩
  exact hsd.2 _ hf p.2

end GlobalTheory.JR.Hyp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyperbolicPartialFourierTwiceEqReflectionStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolicPartialFourier_twice_eq_reflection : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (ν : Measure A.K), SelfDual ν (Hyp.kx A ψ x) → ∀ Φ : A.K × A.K → ℂ, IsTest Φ → Hyp.pt A ν ψ x (Hyp.pt A ν ψ x Φ) = fun p => Φ (p.1, -p.2) := by
  first | exact @GlobalTheory.JR.Hyp.pt_pt_eq_reflect | exact GlobalTheory.JR.Hyp.pt_pt_eq_reflect | (intros; apply GlobalTheory.JR.Hyp.pt_pt_eq_reflect <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualMeasureEtaleHermitianEqCoords
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualMeasureEtaleHermitianEqCoords
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Hyp

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def ccLin (A : Et F E) (e : A.L) : (A.K × A.K) →ₗ[F] A.L where
  toFun := cc A e
  map_add' p q := by simp only [cc, Prod.fst_add, Prod.snd_add, map_add (f := _)]; ring
  map_smul' c p := by
    simp only [cc, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply]
    simp only [Algebra.smul_def, IsScalarTower.algebraMap_apply F A.K A.L, map_mul]
    ring

def ccEquiv [Unram F E] (A : Et F E) (e : A.L) (h1 : ∀ p, ci A e (cc A e p) = p)
    (h2 : ∀ y, cc A e (ci A e y) = y) : (A.K × A.K) ≃L[F] A.L :=
  haveI := EtMeas.finite_L A
  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  let l : (A.K × A.K) ≃ₗ[F] A.L := { ccLin A e with invFun := ci A e, left_inv := h1, right_inv := h2 }
  { l with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap l.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap l.symm.toLinearMap }

def tt (A : Et F E) (ν : Measure A.K) (ψ : AddChar F ℂ) (x : A.K) (Φ : A.K × A.K → ℂ) : A.K × A.K → ℂ :=
  pt A ν ψ x (fun q => pt A ν ψ x Φ (q.2, q.1))

theorem measure_eq_coords : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.Kˣ) (e : A.L), e * e = e → star e = 1 - e → ∀ (ν : Measure A.K) (μ : Measure A.L), SelfDual ν (Hyp.kx A ψ x) → SelfDual μ (A.kerL ψ x) → ∀ h : A.L → ℂ, IsTest h → ∫ y, h y ∂μ = ∫ a, ∫ b, h (Hyp.cc A e (a, b)) ∂ν ∂ν := by
  intro F E _ _ _ _ _ A ψ hψ x e he hse ν μ hν hμ h hh
  haveI : LocallyCompactSpace F := Unram.lcF E
  haveI : IsUltrametricDist F := Unram.ultraF E
  haveI := EtMeas.finite_L A
  haveI := GlobalTheory.FourKFub.secondCountableK A
  obtain ⟨_, _, _, _, hS⟩ := EtMeas.top_facts F A.L
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
  obtain ⟨h1, h2, -, hker, -⟩ := GlobalTheory.T.idempotentCoordinates_structure F E A e he hse
  obtain ⟨htc, htc'⟩ := GlobalTheory.T.isLocallyConstantCompactSupport_idempotentCoordinates_iff F E A e h1 h2
  have hlc := (GlobalTheory.T.isLocallyConstant_etaleTraceAddChar_hermitianKernel F E A ψ hψ).2 (x : A.K)
  haveI : ν.IsAddHaarMeasure := hν.1
  let C := ccEquiv A e h1 h2
  have hC : (C : A.K × A.K → A.L) = cc A e := rfl
  set μ₀ := Measure.map (cc A e) (ν.prod ν) with hμ₀
  haveI : μ₀.IsAddHaarMeasure := by rw [hμ₀, ← hC]; exact C.isAddHaarMeasure_map _
  have hint : ∀ g : A.L → ℂ, IsTest g → ∫ y, g y ∂μ₀ = ∫ a, ∫ b, g (cc A e (a, b)) ∂ν ∂ν := by
    intro g hg
    have e1 : ∫ y, g y ∂μ₀ = ∫ p, g (cc A e p) ∂(ν.prod ν) := C.toHomeomorph.measurableEmbedding.integral_map g
    rw [e1]
    exact integral_prod _ (((htc g hg).1.continuous).integrable_of_hasCompactSupport (htc g hg).2)
  have hsw : ∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (fun q : A.K × A.K => Φ (q.2, q.1)) := fun Φ hΦ =>
    ⟨hΦ.1.comp_continuous continuous_swap, hΦ.2.comp_homeomorph (Homeomorph.prodComm A.K A.K)⟩
  have hpt : ∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (pt A ν ψ x Φ) := fun Φ hΦ =>
    GlobalTheory.T.partialFourier_psiK_preserves_testFunctions F E A ψ hψ x ν hν.1 Φ hΦ
  have hT : ∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (tt A ν ψ x Φ) := fun Φ hΦ =>
    hpt _ (hsw _ (hpt Φ hΦ))
  have hTT : ∀ Φ : A.K × A.K → ℂ, IsTest Φ → tt A ν ψ x (tt A ν ψ x Φ) = fun p => Φ (-p.1, -p.2) := by
    intro Φ hΦ
    have i1 := GlobalTheory.T.hyperbolicPartialFourier_twice_eq_reflection F E A ψ x ν hν _ (hsw _ (hpt Φ hΦ))
    have i2 := GlobalTheory.T.hyperbolicPartialFourier_twice_eq_reflection F E A ψ x ν hν Φ hΦ
    funext p
    show pt A ν ψ x (fun q => pt A ν ψ x (pt A ν ψ x (fun q' => pt A ν ψ x Φ (q'.2, q'.1))) (q.2, q.1)) p = _
    rw [i1]
    show pt A ν ψ x (pt A ν ψ x Φ) (-p.1, p.2) = _
    rw [i2]
  have hA : ∀ f : A.L → ℂ, IsTest f → ∀ p,
      fourB μ₀ (A.kerL ψ x) f (cc A e p) = tt A ν ψ x (fun q => f (cc A e q)) p := by
    intro f hf p
    have ht : IsTest (fun z => f z * A.kerL ψ x z (cc A e p)) := ⟨hf.1.mul (hlc _), hf.2.mul_right⟩
    unfold fourB
    rw [hint _ ht]
    show _ = ∫ a, (∫ b, f (cc A e (a, b)) * kx A ψ x b p.1 ∂ν) * kx A ψ x a p.2 ∂ν
    congr 1; funext a
    rw [← integral_mul_const]
    congr 1; funext b
    rw [hker]; dsimp only; ring
  have hB : ∀ f : A.L → ℂ, IsTest f → IsTest (fourB μ₀ (A.kerL ψ x) f) := by
    intro f hf
    have : fourB μ₀ (A.kerL ψ x) f = fun y => tt A ν ψ x (fun q => f (cc A e q)) (ci A e y) := by
      funext y; have := hA f hf (ci A e y); rwa [h2] at this
    rw [this]; exact htc' _ (hT _ (htc f hf))
  have hsd : SelfDual μ₀ (A.kerL ψ x) := by
    refine ⟨inferInstance, fun f hf y => ?_⟩
    rw [← h2 y, hA _ (hB f hf)]
    have : (fun q => fourB μ₀ (A.kerL ψ x) f (cc A e q)) = tt A ν ψ x (fun q => f (cc A e q)) :=
      funext (hA f hf)
    rw [this, hTT _ (htc f hf)]
    dsimp only
    congr 1
    simp only [cc, map_neg]; ring
  have heq : μ = μ₀ := MeasScale.selfDual_unique hS (A.kerL ψ x) hsd hμ
  rw [heq]; exact hint h hh

end GlobalTheory.JR.Hyp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualMeasureEtaleHermitianEqCoordsStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualMeasure_etaleHermitian_eq_coords : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.Kˣ) (e : A.L), e * e = e → star e = 1 - e → ∀ (ν : Measure A.K) (μ : Measure A.L), SelfDual ν (Hyp.kx A ψ x) → SelfDual μ (A.kerL ψ x) → ∀ h : A.L → ℂ, IsTest h → ∫ y, h y ∂μ = ∫ a, ∫ b, h (Hyp.cc A e (a, b)) ∂ν ∂ν := by
  first | exact @GlobalTheory.JR.Hyp.measure_eq_coords | exact GlobalTheory.JR.Hyp.measure_eq_coords | (intros; apply GlobalTheory.JR.Hyp.measure_eq_coords <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSelfDualHaarHyperbolicKernelPsiK
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSelfDualHaarHyperbolicKernelPsiK
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Hyp

noncomputable def trxForm {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] (A : Et F E) (x : A.K) : LinearMap.BilinForm F A.K :=
  LinearMap.mk₂ F (fun u b => Algebra.trace F A.K (x * u * b))
    (fun m₁ m₂ n => by simp [mul_add, add_mul])
    (fun c m n => by simp [mul_smul_comm, smul_mul_assoc])
    (fun m n₁ n₂ => by simp [mul_add])
    (fun c m n => by simp [mul_smul_comm, smul_mul_assoc])

theorem selfDual_kx_exists : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ x : A.Kˣ, ∃ ν : Measure A.K, SelfDual ν (Hyp.kx A ψ x) := by
  intro F E _ _ _ _ _ A ψ hψ x
  have hT := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.1
  obtain ⟨hL, -⟩ := hT
  have hsymm : (trxForm A (x : A.K)).IsSymm := by
    refine ⟨fun u b => ?_⟩
    simp only [trxForm, LinearMap.mk₂_apply, RingHom.id_apply]
    ring_nf
  have hleft : ∀ u : A.K, (∀ b, trxForm A (x : A.K) u b = 0) → u = 0 := by
    intro u hu
    have h0 : (x : A.K) * u = 0 := hL _ (fun b => by
      have := hu b
      simpa [trxForm, Algebra.traceForm_apply, mul_assoc] using this)
    have := congrArg (fun t => ((x⁻¹ : A.Kˣ) : A.K) * t) h0
    simpa [← mul_assoc] using this
  have hnd : (trxForm A (x : A.K)).Nondegenerate := by
    refine ⟨hleft, fun b hb => hleft b (fun u => ?_)⟩
    have := hb u
    simp only [trxForm, LinearMap.mk₂_apply] at this ⊢
    rw [show (x : A.K) * b * u = x * u * b by ring]
    exact this
  obtain ⟨⟨μ, hμ, -⟩, -⟩ := GlobalTheory.T.selfDual_measure_exists_unique_fourier_inversion F E ψ hψ A.K (trxForm A (x : A.K)) hsymm hnd
  refine ⟨μ, ?_⟩
  have hk : (fun u b => ψ (trxForm A (x : A.K) u b)) = Hyp.kx A ψ x := by
    funext u b
    simp [trxForm, Hyp.kx, Et.psiK]
  rw [← hk]
  exact hμ

end GlobalTheory.JR.Hyp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSelfDualHaarHyperbolicKernelPsiKStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfDual_haar_hyperbolicKernelPsiK : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ x : A.Kˣ, ∃ ν : Measure A.K, SelfDual ν (Hyp.kx A ψ x) := by
  first | exact @GlobalTheory.JR.Hyp.selfDual_kx_exists | exact GlobalTheory.JR.Hyp.selfDual_kx_exists | (intros; apply GlobalTheory.JR.Hyp.selfDual_kx_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentStarEqOneSubOfNotIsField
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentStarEqOneSubOfNotIsField
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Hyp

theorem exists_idempotent_of_not_isField : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → ¬ IsField A.L → ∃ e : A.L, e * e = e ∧ star e = 1 - e := by
  intro F E _ _ _ _ _ A hK hL
  obtain ⟨-, hinj, hN, hT, hnd⟩ := Et.quadratic_structure F E A
  have hnt : ∃ x y : A.L, x ≠ y := by
    obtain ⟨x, y, hxy⟩ := hK.exists_pair_ne
    exact ⟨_, _, hinj.ne hxy⟩
  have hy : ∃ y : A.L, y ≠ 0 ∧ ∀ b, y * b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hL ⟨hnt, mul_comm, fun {a} ha => hcon a ha⟩
  obtain ⟨y, hy0, hyu⟩ := hy
  have hz : ∃ z, Algebra.trace A.K A.L (star y * z) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hy0 (hnd y hcon)
  obtain ⟨z, hz⟩ := hz
  obtain ⟨s, hs⟩ := hK.mul_inv_cancel hz
  have hn : y * star y = 0 := by
    by_contra hne
    have h1 : A.NL y ≠ 0 := by
      intro h0
      apply hne
      rw [← hN, h0, map_zero]
    obtain ⟨n, hn⟩ := hK.mul_inv_cancel h1
    apply hyu (star y * algebraMap A.K A.L n)
    rw [← mul_assoc, ← hN, ← map_mul, hn, map_one]
  have hs' := congrArg (algebraMap A.K A.L) hs
  rw [map_mul, hT, map_one, star_mul', star_star] at hs'
  have hst : star (star y * z * algebraMap A.K A.L s) = y * star z * algebraMap A.K A.L s := by
    rw [star_mul', star_mul', star_star, A.star_K]
  refine ⟨star y * z * algebraMap A.K A.L s, ?_, ?_⟩
  · linear_combination (star y * z * algebraMap A.K A.L s) * hs'
      - (z * star z * algebraMap A.K A.L s ^ 2) * hn
  · rw [hst]
    linear_combination hs'

end GlobalTheory.JR.Hyp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentStarEqOneSubOfNotIsFieldStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotent_star_eq_one_sub_of_not_isField : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → ¬ IsField A.L → ∃ e : A.L, e * e = e ∧ star e = 1 - e := by
  first | exact @GlobalTheory.JR.Hyp.exists_idempotent_of_not_isField | exact GlobalTheory.JR.Hyp.exists_idempotent_of_not_isField | (intros; apply GlobalTheory.JR.Hyp.exists_idempotent_of_not_isField <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyperbolicPartialFourierScaleEqTorusAction
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyperbolicPartialFourierScaleEqTorusAction
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open scoped NNReal ENNReal Pointwise

noncomputable section

namespace GlobalTheory.JR.Hyp

theorem integral_comp_unit_mul {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ν : Measure A.K) [ν.IsAddHaarMeasure]
    (s : A.Kˣ) (g : A.K → ℂ) :
    ∫ b, g ((s : A.K) * b) ∂ν = ((A.absK (s : A.K) : ℂ))⁻¹ * ∫ b, g b ∂ν := by
  haveI : LocallyCompactSpace F := Unram.lcF (E := E)
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : SecondCountableTopology A.K := by
    let e : A.K ≃ₗ[F] (Fin (Module.finrank F A.K) → F) := (Module.finBasis F A.K).equivFun
    have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
    let h : A.K ≃ₜ (Fin (Module.finrank F A.K) → F) := ⟨e.toEquiv, h1, h2⟩
    exact h.isEmbedding.secondCountableTopology
  have hme : MeasurableEmbedding (fun b : A.K => s • b) := (Homeomorph.smul s).measurableEmbedding
  have hmap : Measure.map (fun b : A.K => s • b) ν = ((distribHaarChar A.K s : ℝ≥0∞))⁻¹ • ν := by
    ext S hS
    rw [hme.map_apply, Measure.smul_apply, smul_eq_mul]
    have h1 := distribHaarChar_mul ν s⁻¹ S
    rw [Set.preimage_smul, ← h1, map_inv, ENNReal.coe_inv (distribHaarChar_pos).ne']
  have hint : ∫ b, g ((s : A.K) * b) ∂ν = ∫ b, g b ∂(Measure.map (fun b : A.K => s • b) ν) := by
    rw [hme.integral_map]; rfl
  have habs : A.absK (s : A.K) = (distribHaarChar A.K s : ℝ) := by
    unfold Et.absK
    rw [dite_eq_left s.isUnit]
    congr 2
    ext; rfl
  rw [hint, hmap, integral_smul_measure, habs]
  simp [Complex.real_smul]

theorem pt_scale_eq_rg_mS : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ν : Measure A.K), ν.IsAddHaarMeasure → ∀ (ψ : AddChar F ℂ) (x : A.K) (s : A.Kˣ) (Φ : A.K × A.K → ℂ), Hyp.pt A ν ψ x (fun p => (A.absK (s : A.K) : ℂ) * Φ ((s : A.K) * p.1, (s : A.K) * p.2)) = Hyp.rg A (mS s) (Hyp.pt A ν ψ x Φ) := by
  intro F E _ _ _ _ _ A ν hν ψ x s Φ
  funext p
  obtain ⟨a, u⟩ := p
  have hs0 : A.absK (s : A.K) ≠ 0 := by
    unfold Et.absK
    rw [dite_eq_left s.isUnit]
    exact_mod_cast (distribHaarChar_pos).ne'
  have key := integral_comp_unit_mul A ν s
    (fun b' => Φ (a * (s : A.K), b') * A.psiK ψ (x * b' * (u * ((s⁻¹ : A.Kˣ) : A.K))))
  simp only [pt, rg, mS, fourB, kx]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const, mul_zero, add_zero, zero_add]
  rw [eq_inv_mul_iff_mul_eq₀ (by exact_mod_cast hs0)] at key
  rw [← key, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  have e1 : x * ((s : A.K) * b) * (u * ((s⁻¹ : A.Kˣ) : A.K)) = x * b * u := by
    rw [show x * ((s : A.K) * b) * (u * ((s⁻¹ : A.Kˣ) : A.K)) = x * b * u * ((s : A.K) * ((s⁻¹ : A.Kˣ) : A.K)) by ring,
      Units.mul_inv, mul_one]
  simp only [e1, mul_comm a (s : A.K)]
  ring

end GlobalTheory.JR.Hyp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyperbolicPartialFourierScaleEqTorusActionStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolicPartialFourier_scale_eq_torusAction : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ν : Measure A.K), ν.IsAddHaarMeasure → ∀ (ψ : AddChar F ℂ) (x : A.K) (s : A.Kˣ) (Φ : A.K × A.K → ℂ), Hyp.pt A ν ψ x (fun p => (A.absK (s : A.K) : ℂ) * Φ ((s : A.K) * p.1, (s : A.K) * p.2)) = Hyp.rg A (mS s) (Hyp.pt A ν ψ x Φ) := by
  first | exact @GlobalTheory.JR.Hyp.pt_scale_eq_rg_mS | exact GlobalTheory.JR.Hyp.pt_scale_eq_rg_mS | (intros; apply GlobalTheory.JR.Hyp.pt_scale_eq_rg_mS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyperbolicWeylActionEqFourierEtaleL
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyperbolicWeylActionEqFourierEtaleL
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Hyp

theorem wHyp_wS_eq_fourB : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (e : A.L) (ν : Measure A.K) (μ : Measure A.L), (∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (Hyp.pt A ν ψ x Φ)) → (∀ Φ : A.K × A.K → ℂ, IsTest Φ → Hyp.pt A ν ψ x (Hyp.pt A ν ψ x Φ) = fun p => Φ (p.1, -p.2)) → (∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (Hyp.rg A (wS A.K) Φ)) → (∀ φ : A.L → ℂ, IsTest φ → IsTest (fun p => φ (Hyp.cc A e p))) → (∀ y, Hyp.cc A e (Hyp.ci A e y) = y) → (∀ p q : A.K × A.K, A.kerL ψ x (Hyp.cc A e q) (Hyp.cc A e p) = Hyp.kx A ψ x q.1 p.2 * Hyp.kx A ψ x q.2 p.1) → (∀ y' : A.L, IsLocallyConstant (fun y => A.kerL ψ x y y')) → (∀ h : A.L → ℂ, IsTest h → ∫ y, h y ∂μ = ∫ a, ∫ b, h (Hyp.cc A e (a, b)) ∂ν ∂ν) → ∀ φ : A.L → ℂ, IsTest φ → ∀ y, Hyp.wHyp A e ν ψ x (wS A.K) φ y = fourB μ (A.kerL ψ x) φ y := by
  intro F E _ _ _ _ _ A ψ x e ν μ hpt hinv hrg hcc hci hker hlc hint φ hφ y
  set p := ci A e y with hp
  have hy : y = cc A e p := (hci y).symm
  have hG : IsTest (rg A (wS A.K) (pt A ν ψ x (fun q => φ (cc A e q)))) := hrg _ (hpt _ (hcc φ hφ))
  have hh : IsTest (fun y' => φ y' * A.kerL ψ x y' (cc A e p)) :=
    ⟨hφ.1.mul (hlc _), hφ.2.mul_right⟩
  unfold wHyp
  rw [hinv _ hG]
  rw [← hp]
  conv_rhs => rw [hy]
  unfold fourB
  rw [hint _ hh]
  simp only [pt, fourB, rg, wS, hker]
  simp
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  rw [← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  simp only
  ring

end GlobalTheory.JR.Hyp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyperbolicWeylActionEqFourierEtaleLStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolicWeylAction_eq_fourierEtaleL : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (e : A.L) (ν : Measure A.K) (μ : Measure A.L), (∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (Hyp.pt A ν ψ x Φ)) → (∀ Φ : A.K × A.K → ℂ, IsTest Φ → Hyp.pt A ν ψ x (Hyp.pt A ν ψ x Φ) = fun p => Φ (p.1, -p.2)) → (∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (Hyp.rg A (wS A.K) Φ)) → (∀ φ : A.L → ℂ, IsTest φ → IsTest (fun p => φ (Hyp.cc A e p))) → (∀ y, Hyp.cc A e (Hyp.ci A e y) = y) → (∀ p q : A.K × A.K, A.kerL ψ x (Hyp.cc A e q) (Hyp.cc A e p) = Hyp.kx A ψ x q.1 p.2 * Hyp.kx A ψ x q.2 p.1) → (∀ y' : A.L, IsLocallyConstant (fun y => A.kerL ψ x y y')) → (∀ h : A.L → ℂ, IsTest h → ∫ y, h y ∂μ = ∫ a, ∫ b, h (Hyp.cc A e (a, b)) ∂ν ∂ν) → ∀ φ : A.L → ℂ, IsTest φ → ∀ y, Hyp.wHyp A e ν ψ x (wS A.K) φ y = fourB μ (A.kerL ψ x) φ y := by
  first | exact @GlobalTheory.JR.Hyp.wHyp_wS_eq_fourB | exact GlobalTheory.JR.Hyp.wHyp_wS_eq_fourB | (intros; apply GlobalTheory.JR.Hyp.wHyp_wS_eq_fourB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyperbolicPartialFourierLinearOnTest
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyperbolicPartialFourierLinearOnTest
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Hyp

theorem pt_linear : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.K) (ν : Measure A.K), ν.IsAddHaarMeasure → ∀ (c : ℂ) (Φ Φ' : A.K × A.K → ℂ), IsTest Φ → IsTest Φ' → Hyp.pt A ν ψ x (c • Φ + Φ') = c • Hyp.pt A ν ψ x Φ + Hyp.pt A ν ψ x Φ' := by
  intro F E _ _ _ _ _ A ψ hψ x ν hν c Φ Φ' hΦ hΦ'
  haveI := hν
  haveI : T2Space A.K := T2Space.of_injective_continuous (Module.finBasis F A.K).equivFun.injective
    (IsModuleTopology.continuous_of_linearMap _)
  have hψc : Continuous (fun t : F => ψ t) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hev : (fun s => ψ s) =ᶠ[𝓝 t] fun _ => ψ t := by
      filter_upwards [Metric.closedBall_mem_nhds t one_pos] with s hs
      have hst : s = t + (s - t) := by ring
      have hn : ‖s - t‖ ≤ 1 := by simpa [dist_eq_norm] using hs
      rw [hst, AddChar.map_add_eq_mul, hψ.1 (s - t) hn, mul_one]
    exact continuousAt_const.congr hev.symm
  have htr : Continuous (fun t : A.K => Algebra.trace F A.K t) := IsModuleTopology.continuous_of_linearMap _
  have hk : ∀ u, Continuous (fun b => kx A ψ x b u) := fun u => by
    unfold kx Et.psiK
    exact hψc.comp (htr.comp ((continuous_const.mul continuous_id).mul continuous_const))
  have hint : ∀ Ψ : A.K × A.K → ℂ, IsTest Ψ → ∀ a u, Integrable (fun b => Ψ (a, b) * kx A ψ x b u) ν := by
    intro Ψ hΨ a u
    have hc : Continuous (fun b => Ψ (a, b)) := hΨ.1.continuous.comp (Continuous.prodMk_right a)
    have hs : HasCompactSupport (fun b => Ψ (a, b)) := by
      apply HasCompactSupport.intro (hΨ.2.isCompact.image continuous_snd)
      intro b hb
      by_contra h
      exact hb ⟨(a, b), subset_tsupport _ h, rfl⟩
    exact (hc.mul (hk u)).integrable_of_hasCompactSupport hs.mul_right
  funext p
  have h1 := hint Φ hΦ p.1 p.2
  have h2 := hint Φ' hΦ' p.1 p.2
  simp only [pt, fourB, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul, ← integral_add (h1.const_mul c) h2]
  congr 1
  funext b
  ring

end GlobalTheory.JR.Hyp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyperbolicPartialFourierLinearOnTestStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolicPartialFourier_linear_on_test : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.K) (ν : Measure A.K), ν.IsAddHaarMeasure → ∀ (c : ℂ) (Φ Φ' : A.K × A.K → ℂ), IsTest Φ → IsTest Φ' → Hyp.pt A ν ψ x (c • Φ + Φ') = c • Hyp.pt A ν ψ x Φ + Hyp.pt A ν ψ x Φ' := by
  first | exact @GlobalTheory.JR.Hyp.pt_linear | exact GlobalTheory.JR.Hyp.pt_linear | (intros; apply GlobalTheory.JR.Hyp.pt_linear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportHyperbolicOperati
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportHyperbolicOperati
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Hyp

theorem isTest_comp_homeomorph {X : Type} [TopologicalSpace X] (h : X ≃ₜ X) {Φ : X → ℂ} (hΦ : IsTest Φ) :
    IsTest (Φ ∘ h) :=
  ⟨hΦ.1.comp_continuous h.continuous, hΦ.2.comp_homeomorph h⟩

theorem isTest_ops : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), (∀ (g : SpecialLinearGroup (Fin 2) A.K) (Φ : A.K × A.K → ℂ), IsTest Φ → IsTest (Hyp.rg A g Φ)) ∧ (∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (fun p : A.K × A.K => Φ (p.1, -p.2))) ∧ (∀ (s : A.Kˣ) (Φ : A.K × A.K → ℂ), IsTest Φ → IsTest (fun p : A.K × A.K => Φ ((s : A.K) * p.1, (s : A.K) * p.2))) ∧ (∀ (h Φ : A.K × A.K → ℂ), IsLocallyConstant h → IsTest Φ → IsTest (fun p => h p * Φ p)) ∧ ∀ (c : ℂ) (Φ Φ' : A.K × A.K → ℂ), IsTest Φ → IsTest Φ' → IsTest (c • Φ + Φ') := by
  intro F E _ _ _ _ _ A
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g Φ hΦ
    set a := (g : Matrix (Fin 2) (Fin 2) A.K) 0 0
    set b := (g : Matrix (Fin 2) (Fin 2) A.K) 0 1
    set c := (g : Matrix (Fin 2) (Fin 2) A.K) 1 0
    set d := (g : Matrix (Fin 2) (Fin 2) A.K) 1 1
    have hdet : a * d - b * c = 1 := by
      have := g.2
      rw [Matrix.det_fin_two] at this
      simpa [a, b, c, d] using this
    let e : A.K × A.K ≃ₜ A.K × A.K :=
      { toFun := fun p => (p.1 * a + p.2 * c, p.1 * b + p.2 * d)
        invFun := fun p => (p.1 * d - p.2 * c, -(p.1 * b) + p.2 * a)
        left_inv := by
          intro p
          ext
          · simp only; linear_combination p.1 * hdet
          · simp only; linear_combination p.2 * hdet
        right_inv := by
          intro p
          ext
          · simp only; linear_combination p.1 * hdet
          · simp only; linear_combination p.2 * hdet
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    exact isTest_comp_homeomorph e hΦ
  · intro Φ hΦ
    let e : A.K × A.K ≃ₜ A.K × A.K :=
      { toFun := fun p => (p.1, -p.2)
        invFun := fun p => (p.1, -p.2)
        left_inv := by intro p; simp
        right_inv := by intro p; simp
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    exact isTest_comp_homeomorph e hΦ
  · intro s Φ hΦ
    let e : A.K × A.K ≃ₜ A.K × A.K :=
      { toFun := fun p => ((s : A.K) * p.1, (s : A.K) * p.2)
        invFun := fun p => (((s⁻¹ : A.Kˣ) : A.K) * p.1, ((s⁻¹ : A.Kˣ) : A.K) * p.2)
        left_inv := by intro p; ext <;> simp [← mul_assoc]
        right_inv := by intro p; ext <;> simp [← mul_assoc]
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    exact isTest_comp_homeomorph e hΦ
  · intro h Φ hh hΦ
    exact ⟨hh.mul hΦ.1, hΦ.2.mul_left⟩
  · intro c Φ Φ' hΦ hΦ'
    refine ⟨?_, ?_⟩
    · exact (hΦ.1.comp (fun z : ℂ => c • z)).add hΦ'.1
    · exact (hΦ.2.smul_left).add hΦ'.2

end GlobalTheory.JR.Hyp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportHyperbolicOperatiStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyConstantCompactSupport_hyperbolic_operations : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), (∀ (g : SpecialLinearGroup (Fin 2) A.K) (Φ : A.K × A.K → ℂ), IsTest Φ → IsTest (Hyp.rg A g Φ)) ∧ (∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (fun p : A.K × A.K => Φ (p.1, -p.2))) ∧ (∀ (s : A.Kˣ) (Φ : A.K × A.K → ℂ), IsTest Φ → IsTest (fun p : A.K × A.K => Φ ((s : A.K) * p.1, (s : A.K) * p.2))) ∧ (∀ (h Φ : A.K × A.K → ℂ), IsLocallyConstant h → IsTest Φ → IsTest (fun p => h p * Φ p)) ∧ ∀ (c : ℂ) (Φ Φ' : A.K × A.K → ℂ), IsTest Φ → IsTest Φ' → IsTest (c • Φ + Φ') := by
  first | exact @GlobalTheory.JR.Hyp.isTest_ops | exact GlobalTheory.JR.Hyp.isTest_ops | (intros; apply GlobalTheory.JR.Hyp.isTest_ops <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeilRepresentationHyperbolicSplit
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem weilHyp_rg : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), (∀ Φ : A.K × A.K → ℂ, Hyp.rg A 1 Φ = Φ) ∧ ∀ (g h : SpecialLinearGroup (Fin 2) A.K) (Φ : A.K × A.K → ℂ), Hyp.rg A g (Hyp.rg A h Φ) = Hyp.rg A (g * h) Φ := by
  intro F E _ _ _ _ _ A
  refine ⟨fun Φ => ?_, fun g h Φ => ?_⟩
  · funext p
    simp [Hyp.rg]
  · funext p
    have hm : ((g * h : Matrix.SpecialLinearGroup (Fin 2) A.K) : Matrix (Fin 2) (Fin 2) A.K) =
        (g : Matrix (Fin 2) (Fin 2) A.K) * (h : Matrix (Fin 2) (Fin 2) A.K) := Matrix.SpecialLinearGroup.coe_mul g h
    unfold Hyp.rg
    rw [hm]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    congr 1
    ext <;> ring

theorem weilHyp_nS : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ν : Measure A.K) (ψ : AddChar F ℂ) (x z : A.K) (Φ : A.K × A.K → ℂ), Hyp.pt A ν ψ x (fun p => A.psiK ψ (z * x * (p.1 * p.2)) * Φ p) = Hyp.rg A (nS z) (Hyp.pt A ν ψ x Φ) := by
  intro F E _ _ _ _ _ A ν ψ x z Φ
  funext p
  simp only [Hyp.pt, Hyp.rg, nS, fourB, Hyp.kx, Et.psiK]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, mul_one, mul_zero, add_zero, zero_add]
  congr 1
  funext b
  rw [show x * b * (p.1 * z + p.2) = z * x * (p.1 * b) + x * b * p.2 by ring, map_add (f := _), AddChar.map_add_eq_mul]
  ring

theorem weil_hyperbolic : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → IsField A.K → ¬ IsField A.L → ∀ (x : A.Kˣ) (μ : Measure A.L), SelfDual μ (A.kerL ψ x) → ∃ W, A.IsWeil ψ x A.etaK μ 1 W := by
  intro F E _ _ _ _ _ A ψ hψ hK hL x μ hμ
  obtain ⟨e, he, hse⟩ := GlobalTheory.T.exists_idempotent_star_eq_one_sub_of_not_isField F E A hK hL
  obtain ⟨hci, hcc, hN, hker, hsm, hunit⟩ := GlobalTheory.T.idempotentCoordinates_structure F E A e he hse
  obtain ⟨ν, hν⟩ := GlobalTheory.T.exists_selfDual_haar_hyperbolicKernelPsiK F E A ψ hψ x
  have hνH : ν.IsAddHaarMeasure := hν.1
  have hT := GlobalTheory.T.partialFourier_psiK_preserves_testFunctions F E A ψ hψ x ν hνH
  have hDD := GlobalTheory.T.hyperbolicPartialFourier_twice_eq_reflection F E A ψ (x : A.K) ν hν
  obtain ⟨hTcc, hTci⟩ := GlobalTheory.T.isLocallyConstantCompactSupport_idempotentCoordinates_iff F E A e hci hcc
  obtain ⟨hTrg, hTneg, hTsc, hTmul, hTlin⟩ := GlobalTheory.T.isLocallyConstantCompactSupport_hyperbolic_operations F E A
  obtain ⟨hpsi, hkerlc⟩ := GlobalTheory.T.isLocallyConstant_etaleTraceAddChar_hermitianKernel F E A ψ hψ
  obtain ⟨hrg1, hrgm⟩ := weilHyp_rg F E A
  have hlin := GlobalTheory.T.hyperbolicPartialFourier_linear_on_test F E A ψ hψ (x : A.K) ν hνH
  set P := Hyp.pt A ν ψ (x : A.K) with hP
  have h4 : ∀ Φ, IsTest Φ → P (P (P (P Φ))) = Φ := by
    intro Φ hΦ
    rw [hDD Φ hΦ, hDD _ (hTneg Φ hΦ)]
    funext p
    simp
  have hW : ∀ g φ, Hyp.wHyp A e ν ψ x g φ = fun y => P (P (P (Hyp.rg A g (P (fun p => φ (Hyp.cc A e p)))))) (Hyp.ci A e y) :=
    fun _ _ => rfl

  have hkey : ∀ g φ (Φ' : A.K × A.K → ℂ), IsTest Φ' → Hyp.rg A g (P (fun p => φ (Hyp.cc A e p))) = P Φ' →
      Hyp.wHyp A e ν ψ x g φ = fun y => Φ' (Hyp.ci A e y) := by
    intro g φ Φ' hΦ' h
    rw [hW, h, h4 Φ' hΦ']
  have hetaK : ∀ s : A.Kˣ, A.etaK s = 1 := by
    intro s
    have h1 := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.2.1 (Hyp.cc A e ((s : A.K), 1)) (hunit s)
    rwa [hN, mul_one] at h1
  refine ⟨Hyp.wHyp A e ν ψ x, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro g φ hφ
    rw [hW]
    exact hTci _ (hT _ (hT _ (hT _ (hTrg g _ (hT _ (hTcc φ hφ))))))
  · intro φ hφ
    rw [hW, hrg1, h4 _ (hTcc φ hφ)]
    funext y
    show φ (Hyp.cc A e (Hyp.ci A e y)) = φ y
    rw [hcc]
  · intro g h φ hφ
    have hin : (fun p => Hyp.wHyp A e ν ψ x h φ (Hyp.cc A e p)) = P (P (P (Hyp.rg A h (P (fun p => φ (Hyp.cc A e p)))))) := by
      funext p
      rw [hW]
      simp only [hci]
    rw [hW (g * h) φ, hW g (Hyp.wHyp A e ν ψ x h φ), hin, h4 _ (hTrg h _ (hT _ (hTcc φ hφ))), hrgm]
  · intro g c φ φ' hφ hφ'
    have hc1 : (fun p => (c • φ + φ') (Hyp.cc A e p)) = c • (fun p => φ (Hyp.cc A e p)) + (fun p => φ' (Hyp.cc A e p)) := rfl
    have t1 := hTcc φ hφ
    have t2 := hTcc φ' hφ'
    have hrl : ∀ (Φ Φ' : A.K × A.K → ℂ), Hyp.rg A g (c • Φ + Φ') = c • Hyp.rg A g Φ + Hyp.rg A g Φ' := fun _ _ => rfl
    rw [hW, hW, hW, hc1, hlin c _ _ t1 t2, hrl, hlin c _ _ (hTrg g _ (hT _ t1)) (hTrg g _ (hT _ t2)),
      hlin c _ _ (hT _ (hTrg g _ (hT _ t1))) (hT _ (hTrg g _ (hT _ t2))),
      hlin c _ _ (hT _ (hT _ (hTrg g _ (hT _ t1)))) (hT _ (hT _ (hTrg g _ (hT _ t2))))]
    rfl
  · intro φ hφ
    refine ⟨?_, ?_, ?_⟩
    · intro z y
      have hΦ : IsTest (fun p : A.K × A.K => A.psiK ψ (z * (x : A.K) * (p.1 * p.2)) * φ (Hyp.cc A e p)) :=
        hTmul _ _ (hpsi.comp_continuous (by fun_prop)) (hTcc φ hφ)
      rw [hkey (nS z) φ _ hΦ (weilHyp_nS F E A ν ψ (x : A.K) z _).symm]
      simp only
      rw [← hN, hcc]
    · intro s y
      have hΦ : IsTest (fun p : A.K × A.K => (A.absK (s : A.K) : ℂ) * φ (Hyp.cc A e ((s : A.K) * p.1, (s : A.K) * p.2))) :=
        hTmul _ _ (IsLocallyConstant.const _) (hTsc s _ (hTcc φ hφ))
      rw [hkey (mS s) φ _ hΦ (GlobalTheory.T.hyperbolicPartialFourier_scale_eq_torusAction F E A ν hνH ψ (x : A.K) s (fun p => φ (Hyp.cc A e p))).symm]
      simp only
      rw [hetaK, one_mul, ← hsm, hcc]
    · intro y
      rw [one_mul]
      exact GlobalTheory.T.hyperbolicWeylAction_eq_fourierEtaleL F E A ψ (x : A.K) e ν μ hT hDD (fun Φ hΦ => hTrg _ Φ hΦ) hTcc hcc (hker ψ (x : A.K))
        (hkerlc (x : A.K)) (GlobalTheory.T.selfDualMeasure_etaleHermitian_eq_coords F E A ψ hψ x e he hse ν μ hν hμ) φ hφ y

end GlobalTheory.JR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeilRepresentationHyperbolicSplitStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilRepresentation_hyperbolic_split : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → IsField A.K → ¬ IsField A.L → ∀ (x : A.Kˣ) (μ : Measure A.L), SelfDual μ (A.kerL ψ x) → ∃ W, A.IsWeil ψ x A.etaK μ 1 W := by
  first | exact @GlobalTheory.JR.weil_hyperbolic | exact GlobalTheory.JR.weil_hyperbolic | (intros; apply GlobalTheory.JR.weil_hyperbolic <;> assumption)
end
