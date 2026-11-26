module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarMapLinearScalingByDeterminant
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteProductMultipliable
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.Bruhat
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductSupport
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductSupport
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageValue

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem one_tmul_algebraMap (t : F) :
    (1 : R) ⊗ₜ[F] (algebraMap F E t) = (algebraMap F R t) ⊗ₜ[F] (1 : E) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul']

theorem corner_half_trace_eq_of_pure_tensor [CharZero F] (hfr : Module.finrank F E = 2) {n : ℕ}
    (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) {x : R}
    (h : S 0 0 = x ⊗ₜ[F] (1 : E)) : s0 R S = x := by
  have hfin : Module.Finite F E := Module.finite_of_finrank_eq_succ hfr
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hfr
  have htr : Algebra.trace R (R ⊗[F] E) (x ⊗ₜ[F] (1 : E)) = 2 * x := by
    have h1 := Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R b) x
    rw [Algebra.TensorProduct.algebraMap_apply] at h1
    simpa [two_mul, two_nsmul] using h1
  have h2 : algebraMap F R (1 / 2) * 2 = 1 := by
    calc algebraMap F R (1 / 2) * 2 = algebraMap F R (1 / 2) * algebraMap F R 2 := by rw [map_ofNat]
      _ = algebraMap F R (1 / 2 * 2) := (map_mul _ _ _).symm
      _ = 1 := by rw [show (1 / 2 * 2 : F) = 1 by norm_num, map_one]
  unfold s0
  rw [h, htr, ← mul_assoc, h2, one_mul]

theorem vec_one_zero {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) :
    vec ((1 : R) ⊗ₜ[F] (1 : E)) (0 : Fin n → R ⊗[F] E) X = consTup X := by
  rw [← Algebra.TensorProduct.one_def]
  rfl

end Alg

section Main

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) (t : F) (a : R → Rˣ) {n : ℕ}

theorem corner_half_trace_block_one [CharZero F] (hfr : Module.finrank F E = 2) (T : Matrix (Fin n) (Fin n) E) :
    s0 R ((blockOne (algebraMap F E t) T).map (inclR (F := F) R)) = algebraMap F R t := by
  apply corner_half_trace_eq_of_pure_tensor R hfr
  rw [← one_tmul_algebraMap]
  rfl

theorem cvec_block (T : Matrix (Fin n) (Fin n) E) :
    cvec R t a ((blockOne (algebraMap F E t) T).map (inclR R)) = 0 := by
  funext j
  simp [cvec, blockOne]

theorem schurM_block (T : Matrix (Fin n) (Fin n) E) :
    schurM R σ t a ((blockOne (algebraMap F E t) T).map (inclR R)) = T.map (inclR R) := by
  ext i j
  have hc := cvec_block R t a T
  simp only [schurM, hc, Pi.zero_apply, map_zero, zero_mul, sub_zero]
  simp [blockOne]

theorem schur_block (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b)
    (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b) :
    schur R σ t a (hermOf R σ _ hT') = hermOf R σ T hT := by
  apply Subtype.ext
  have hm : schurM R σ t a ((hermOf R σ _ hT' : HermR R σ (n + 1)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ HermR R σ n := by
    show schurM R σ t a ((blockOne (algebraMap F E t) T).map (inclR R)) ∈ HermR R σ n
    rw [schurM_block]
    exact map_mem_HermR R σ T hT
  rw [schur_coe R σ t a _ hm]
  exact schurM_block R σ t a T

theorem isUnit_det_map (T : Matrix (Fin n) (Fin n) E) (hdet : T.det ≠ 0) :
    IsUnit (T.map (inclR (F := F) R)).det := by
  have h := (IsUnit.mk0 _ hdet).map (inclR (F := F) R)
  rw [RingHom.map_det] at h
  exact h

end Main

theorem family_at_block : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), hermOf R σ _ hT' ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) ∧ fibS σ J t m₁ m' s B₀ a κ₁ cm (hermOf R σ _ hT') = cm 1 ^ n • ((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (hermOf R σ T hT))).map (fun p => actW R σ _ (s p.1) (consTup p.2)) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D T hT hdet hT'
  have hfr : Module.finrank F E = 2 := D.hCM.2.2.1
  have hs0 : s0 R ((hermOf R σ _ hT' : HermR R σ (n + 1)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = algebraMap F R t :=
    corner_half_trace_block_one R t hfr T
  have hsch := schur_block R σ t a T hT hT'
  have hmem : hermOf R σ _ hT' ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) := by
    refine ⟨by rw [hs0]; exact D.htB, ?_⟩
    rw [hsch]
    exact isUnit_det_map R T hdet
  refine ⟨hmem, ?_⟩
  have hc : cvec R t a ((hermOf R σ _ hT' : HermR R σ (n + 1)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = 0 := cvec_block R t a T
  unfold fibS
  rw [Set.indicator_of_mem hmem]
  simp only [hs0, D.ha1, hsch, hc, D.hκ1, one_mul, Units.val_one, vec_one_zero]

end GlobalTheory.CompanionTheory.SW.StageValue
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberConsProductSupportStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_fiber_cons_at_block_one_eq_map_prod : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), hermOf R σ _ hT' ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) ∧ fibS σ J t m₁ m' s B₀ a κ₁ cm (hermOf R σ _ hT') = cm 1 ^ n • ((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (hermOf R σ T hT))).map (fun p => actW R σ _ (s p.1) (consTup p.2)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageValue.family_at_block | exact GlobalTheory.CompanionTheory.SW.StageValue.family_at_block | (intros; apply GlobalTheory.CompanionTheory.SW.StageValue.family_at_block <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FundamentalDomainTransportCongruentForm
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FundamentalDomainTransportCongruentForm
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.FTransfer

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem actTup_ratTup {M n : ℕ} (g : GL (Fin M) E) (X : Fin n → Fin M → E) :
    actTup R (bc (inclR (F := F) R) g) (ratTup R X) =
      ratTup R (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ X a) := by
  funext a i
  have h := RingHom.map_mulVec (inclR (F := F) R) (g : Matrix (Fin M) (Fin M) E) (X a) i
  exact h.symm

theorem actTup_mul {M n : ℕ} (a b : GL (Fin M) (R ⊗[F] E)) (X : Fin n → Fin M → R ⊗[F] E) :
    actTup R (a * b) X = actTup R a (actTup R b X) := by
  funext c
  simp [actTup, Matrix.mulVec_mulVec]

end Alg

section Group

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R]

theorem isTopologicalGroup_HA [IsTopologicalRing R] [Module.Finite F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : IsTopologicalGroup (HA R σ J) := by
  haveI : IsTopologicalRing (R ⊗[F] E) := GlobalTheory.CompanionTheory.SW.HIsom.isTopologicalRing_tens F E R
  exact inferInstanceAs (IsTopologicalGroup (HR R σ J))

theorem borelSpace_HA (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    BorelSpace (HA R σ J) := ⟨rfl⟩

end Group

end GlobalTheory.CompanionTheory.SW.FTransfer


open GlobalTheory.CompanionTheory.SW.FTransfer in
theorem GlobalTheory.CompanionTheory.SW.FTransfer.cntI_transfer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (g : GL (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), J' = cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∃ (μ' : Measure (HA (AF F) σ J')) (𝓕' : Set (HA (AF F) σ J')), IsHaarH F E σ M J' μ' ∧ IsFDH F E σ M J' μ' 𝓕' ∧ μ' 𝓕' = μ 𝓕 ∧ ∀ (n : ℕ) (S : Set (Fin n → Fin M → E)) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞), cntI σ J μ 𝓕 S Φ = cntI σ J' μ' 𝓕' {X | (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ X a) ∈ S} (fun Y => Φ (actTup (AF F) (bc (inclR (AF F)) g) Y)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ g J' hJ' μ 𝓕 hμ h𝓕
  obtain ⟨e, he1, he2⟩ := GlobalTheory.CompanionTheory.SW.HIsom.unitaryIsom_of_isometry F E σ hCM M J hJ g J' hJ' (AF F)
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  haveI := isTopologicalGroup_HA (F := F) (E := E) (AF F) σ J
  haveI := isTopologicalGroup_HA (F := F) (E := E) (AF F) σ J'
  haveI := borelSpace_HA (F := F) (E := E) (AF F) σ J
  haveI := borelSpace_HA (F := F) (E := E) (AF F) σ J'
  haveI : μ.IsHaarMeasure := hμ
  let em : HA (AF F) σ J' ≃ᵐ HA (AF F) σ J := e.toHomeomorph.toMeasurableEquiv
  have hmp : MeasurePreserving em (μ.map em.symm) μ := by
    refine ⟨em.measurable, ?_⟩
    rw [Measure.map_map em.measurable em.symm.measurable]
    simp
  refine ⟨μ.map em.symm, em ⁻¹' 𝓕, ?_, ?_, ?_, ?_⟩
  · exact ContinuousMulEquiv.isHaarMeasure_map μ e.symm
  · have hq : Measure.QuasiMeasurePreserving em (μ.map em.symm) μ := hmp.quasiMeasurePreserving
    have hin₀ : ∀ x : HA (AF F) σ J, HA.mat (AF F) σ J x ∈ HFin (AF F) σ J →
        HA.mat (AF F) σ J' (e.symm x) ∈ HFin (AF F) σ J' := by
      intro x hx
      apply (he2 _).1
      rw [e.apply_symm_apply]
      exact hx
    have hin : ∀ a : HFinIn (AF F) σ J,
        HA.mat (AF F) σ J' (e.symm (a.1 : HA (AF F) σ J)) ∈ HFin (AF F) σ J' :=
      fun a => hin₀ a.1 a.2
    have hmulx : ∀ (y : HA (AF F) σ J) (x : HA (AF F) σ J'), e (e.symm y * x) = y * e x := by
      intro y x
      rw [map_mul, e.apply_symm_apply]
    let e' : HFinIn (AF F) σ J → HFinIn (AF F) σ J' := fun a =>
      ⟨(e.symm (a.1 : HA (AF F) σ J) : HA (AF F) σ J'), Subgroup.mem_subgroupOf.2 (hin a)⟩
    refine IsFundamentalDomain.preimage_of_equiv h𝓕 hq (e := e') ⟨?_, ?_⟩ ?_
    · intro a b hab
      have h1 : e.symm (a.1 : HA (AF F) σ J) = e.symm (b.1 : HA (AF F) σ J) :=
        congrArg (fun x : HFinIn (AF F) σ J' => (x.1 : HA (AF F) σ J')) hab
      exact Subtype.ext (e.symm.injective h1)
    · intro b
      have hb : HA.mat (AF F) σ J (e (b.1 : HA (AF F) σ J')) ∈ HFin (AF F) σ J :=
        (he2 _).2 b.2
      refine ⟨⟨(e (b.1 : HA (AF F) σ J') : HA (AF F) σ J), Subgroup.mem_subgroupOf.2 hb⟩, ?_⟩
      exact Subtype.ext (e.symm_apply_apply (b.1 : HA (AF F) σ J'))
    · intro a x
      exact hmulx a.1 x
  · rw [em.symm.map_apply]
    congr 1
    ext x
    simp
  · intro n S Φ
    have hrest : (μ.map em.symm).restrict (em ⁻¹' 𝓕) = (μ.restrict 𝓕).map em.symm := by
      rw [MeasurableEquiv.restrict_map]
      congr 2
      ext x
      simp
    unfold cntI
    rw [hrest, lintegral_map_equiv]
    refine lintegral_congr fun h => ?_
    have key : ∀ X : Fin n → Fin M → E,
        actTup (AF F) (bc (inclR (AF F)) g)
            (actW (AF F) σ J' (em.symm h)⁻¹ (ratTup (AF F) X)) =
          actW (AF F) σ J h⁻¹
            (ratTup (AF F) (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ X a)) := by
      intro X
      have hu : e (em.symm h) = h := e.apply_symm_apply h
      have h1 := he1 (em.symm h)⁻¹
      rw [map_inv, hu] at h1
      simp only [actW]
      rw [← actTup_ratTup, h1, ← actTup_mul, ← actTup_mul]
      congr 1
      group
    let T : {X : Fin n → Fin M → E | (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ X a) ∈ S} ≃ S :=
      { toFun := fun X => ⟨fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ X.1 a, X.2⟩
        invFun := fun Y => ⟨fun a => ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ Y.1 a, by
          have : (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ
              (((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ Y.1 a)) = Y.1 := by
            funext a
            rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
              Matrix.one_mulVec]
          change (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ
              (((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ Y.1 a)) ∈ S
          rw [this]
          exact Y.2⟩
        left_inv := fun X => by
          apply Subtype.ext
          funext a
          change ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ
            ((g : Matrix (Fin M) (Fin M) E) *ᵥ X.1 a) = X.1 a
          rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
            Matrix.one_mulVec]
        right_inv := fun Y => by
          apply Subtype.ext
          funext a
          change (g : Matrix (Fin M) (Fin M) E) *ᵥ
            (((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ Y.1 a) = Y.1 a
          rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
            Matrix.one_mulVec] }
    refine (T.tsum_eq (fun X : S => Φ (actW (AF F) σ J h⁻¹
      (ratTup (AF F) (X : Fin n → Fin M → E))))).symm.trans (tsum_congr fun X => ?_)
    exact congrArg Φ (key X.1).symm
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FundamentalDomainTransportCongruentFormStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_transport_congruent_form : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (g : GL (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), J' = cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∃ (μ' : Measure (HA (AF F) σ J')) (𝓕' : Set (HA (AF F) σ J')), IsHaarH F E σ M J' μ' ∧ IsFDH F E σ M J' μ' 𝓕' ∧ μ' 𝓕' = μ 𝓕 ∧ ∀ (n : ℕ) (S : Set (Fin n → Fin M → E)) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞), cntI σ J μ 𝓕 S Φ = cntI σ J' μ' 𝓕' {X | (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ X a) ∈ S} (fun Y => Φ (actTup (AF F) (bc (inclR (AF F)) g) Y)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.FTransfer.cntI_transfer | exact GlobalTheory.CompanionTheory.SW.FTransfer.cntI_transfer | (intros; apply GlobalTheory.CompanionTheory.SW.FTransfer.cntI_transfer <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.QuotientMeasureTower
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ClosedSubgroupQuotientMeasure
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ClosedSubgroupQuotientMeasure
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

noncomputable def closedEmbeddingRangeEquiv {G G₁ : Type} [Group G] [TopologicalSpace G]
    [Group G₁] [TopologicalSpace G₁] (ι : G₁ →* G) (hι : IsClosedEmbedding ι) :
    G₁ ≃ₜ* ι.range :=
  have hemb : IsEmbedding ι.rangeRestrict :=
    IsEmbedding.of_comp (hι.continuous.subtype_mk _) continuous_subtype_val hι.isEmbedding
  { MulEquiv.ofBijective ι.rangeRestrict
      ⟨hemb.injective, ι.rangeRestrict_surjective⟩ with
    continuous_toFun := hemb.continuous
    continuous_invFun :=
      (hemb.toHomeomorphOfSurjective ι.rangeRestrict_surjective).symm.continuous }

theorem exists_weight_mass_one_right_coset :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (G₁ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* G), IsClosedEmbedding ι → ∀ (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] [μ₁.IsMulRightInvariant], ∃ w : G → ℝ≥0∞, Measurable w ∧ ∀ g, ∫⁻ u, w (ι u * g) ∂μ₁ = 1 := by
  intro G _ _ _ _ _ _ _ _ G₁ _ _ _ _ _ _ _ ι hι μ₁ _ _
  have hclosed : IsClosed ((ι.range : Subgroup G) : Set G) := by
    rw [MonoidHom.coe_range]; exact hι.isClosed_range
  let e : G₁ ≃ₜ* ι.range := closedEmbeddingRangeEquiv ι hι
  haveI : IsFiniteMeasureOnCompacts μ₁.inv :=
    ⟨fun K hK => by rw [Measure.inv_apply]; exact hK.inv.measure_lt_top⟩
  haveI : μ₁.inv.IsOpenPosMeasure :=
    ⟨fun U hU hne => by
      rw [Measure.inv_apply]; exact hU.inv.measure_ne_zero μ₁ hne.inv⟩
  haveI hinv : μ₁.inv.IsHaarMeasure := {}
  have hν : (μ₁.inv.map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ₁.inv e
  obtain ⟨β, hβ, hmass⟩ := PI.WeilQuotMeas.UnitaryGroupMassFormula.stepBruhat G ι.range hclosed _ hν
  refine ⟨fun g => β g⁻¹, hβ.comp measurable_inv, fun g => ?_⟩
  have hem : Measurable e := e.continuous.measurable
  have hf : Measurable fun h : ι.range => β (g⁻¹ * (h : G)) :=
    hβ.comp (measurable_const.mul measurable_subtype_coe)
  have h1 := hmass g⁻¹
  have hcomp : Measurable fun a : G₁ => β (g⁻¹ * (e a : G)) := hf.comp hem
  rw [lintegral_map hf hem, Measure.inv, lintegral_map hcomp measurable_inv] at h1
  refine Eq.trans (lintegral_congr fun u => ?_) h1
  have : ((e u⁻¹ : ι.range) : G) = (ι u)⁻¹ := by
    show ι u⁻¹ = _
    exact map_inv ι u
  show β (ι u * g)⁻¹ = β (g⁻¹ * ((e u⁻¹ : ι.range) : G))
  rw [this, mul_inv_rev]

end GlobalTheory.CompanionTheory.SW
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ClosedSubgroupQuotientMeasureStatement
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_subgroup_quotient_measure : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (G₁ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* G), IsClosedEmbedding ι → ∀ (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] [μ₁.IsMulRightInvariant], ∃ w : G → ℝ≥0∞, Measurable w ∧ ∀ g, ∫⁻ u, w (ι u * g) ∂μ₁ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.exists_weight_mass_one_right_coset | exact GlobalTheory.CompanionTheory.SW.exists_weight_mass_one_right_coset | (intros; apply GlobalTheory.CompanionTheory.SW.exists_weight_mass_one_right_coset <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.QuotientMeasureTower
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.Averaging

section
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {G₁ : Type} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
  [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁]

theorem setLIntegral_mul_right_eq (μ₁ : Measure G₁) [SFinite μ₁] [μ₁.IsMulLeftInvariant]
    [μ₁.IsMulRightInvariant] (Γ₁ : Subgroup G₁) [Countable Γ₁] (𝓕₁ : Set G₁)
    (h𝓕₁ : IsFundamentalDomain Γ₁ 𝓕₁ μ₁) (f : G₁ → ℝ≥0∞)
    (hf : ∀ γ ∈ Γ₁, ∀ u, f (γ * u) = f u) (u₀ : G₁) :
    ∫⁻ u in 𝓕₁, f (u * u₀) ∂μ₁ = ∫⁻ u in 𝓕₁, f u ∂μ₁ := by
  rw [(measurePreserving_mul_right μ₁ u₀).setLIntegral_comp_emb
    (MeasurableEquiv.mulRight u₀).measurableEmbedding f 𝓕₁]
  have h2 : IsFundamentalDomain Γ₁ ((Equiv.mulRight u₀) '' 𝓕₁) μ₁ :=
    h𝓕₁.image_of_equiv (Equiv.mulRight u₀)
      (by
        rw [Equiv.mulRight_symm]
        exact (measurePreserving_mul_right μ₁ u₀⁻¹).quasiMeasurePreserving)
      (Equiv.refl _) (fun g => by
        intro x
        simp only [Equiv.coe_mulRight, Equiv.refl_apply, Subgroup.smul_def, smul_eq_mul, mul_assoc])
  exact h2.setLIntegral_eq h𝓕₁ f (fun g x => by
    rw [Subgroup.smul_def, smul_eq_mul]
    exact hf g g.2 x)

theorem bijective_pair (ι : G₁ →* G) (hι : Function.Injective ι)
    (Γ : Subgroup G) (Γ₁ : Subgroup G₁) (hΓ : ∀ u ∈ Γ₁, ι u ∈ Γ)
    {Q : Type} (r : Q → G) (hr : ∀ q, r q ∈ Γ)
    (hQ : ∀ γ ∈ Γ, ∃! q, ∃ u ∈ Γ₁, γ = ι u * r q) :
    Function.Bijective (fun p : Q × Γ₁ =>
      (⟨ι (p.2 : G₁)⁻¹ * r p.1, Γ.mul_mem (hΓ _ (Γ₁.inv_mem p.2.2)) (hr p.1)⟩ : Γ)) := by
  constructor
  · rintro ⟨q, v⟩ ⟨q', v'⟩ h
    have hval : ι (v : G₁)⁻¹ * r q = ι (v' : G₁)⁻¹ * r q' := congrArg Subtype.val h
    obtain ⟨q₀, -, huniq⟩ := hQ _ (Γ.mul_mem (hΓ _ (Γ₁.inv_mem v.2)) (hr q))
    have hq : q = q' := by
      rw [huniq q ⟨(v : G₁)⁻¹, Γ₁.inv_mem v.2, rfl⟩, huniq q' ⟨(v' : G₁)⁻¹, Γ₁.inv_mem v'.2, hval⟩]
    subst hq
    have h3 : ι (v : G₁)⁻¹ = ι (v' : G₁)⁻¹ := mul_right_cancel hval
    have hv : (v : G₁) = v' := inv_injective (hι h3)
    simp only [Prod.mk.injEq, true_and]
    exact Subtype.ext hv
  · rintro ⟨γ, hγ⟩
    obtain ⟨q, ⟨u, hu, hγu⟩, -⟩ := hQ γ hγ
    refine ⟨(q, ⟨u⁻¹, Γ₁.inv_mem hu⟩), ?_⟩
    apply Subtype.ext
    show ι (u⁻¹)⁻¹ * r q = γ
    rw [inv_inv]
    exact hγu.symm

theorem lintegral_sum_cosets_eq (ι : G₁ →* G) (hιc : Continuous ι) (hι : Function.Injective ι)
    (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant]
    (μ₁ : Measure G₁) [SFinite μ₁] [μ₁.IsMulLeftInvariant] [μ₁.IsInvInvariant]
    (Γ : Subgroup G) [Countable Γ] (Γ₁ : Subgroup G₁) [Countable Γ₁]
    (𝓕 : Set G) (𝓕₁ : Set G₁)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (h𝓕₁ : IsFundamentalDomain Γ₁ 𝓕₁ μ₁)
    (hΓ : ∀ u ∈ Γ₁, ι u ∈ Γ) {Q : Type} [Countable Q] (r : Q → G) (hr : ∀ q, r q ∈ Γ)
    (hQ : ∀ γ ∈ Γ, ∃! q, ∃ u ∈ Γ₁, γ = ι u * r q)
    (w : G → ℝ≥0∞) (hw : Measurable w) (hw1 : ∀ g, ∫⁻ u, w (ι u * g) ∂μ₁ = 1)
    (ψ : G → ℝ≥0∞) (hψ : Measurable ψ) (hinv : ∀ u ∈ Γ₁, ∀ g, ψ (ι u * g) = ψ g) :
    ∫⁻ h in 𝓕, ∑' q, ψ (r q * h) ∂μ = ∫⁻ g, w g * ∫⁻ u in 𝓕₁, ψ (ι u * g) ∂μ₁ ∂μ := by
  have hιm : Measurable ι := hιc.measurable
  have hm1 : Measurable (fun p : G × G₁ => ι p.2 * p.1) :=
    ((hιc.comp continuous_snd).mul continuous_fst).measurable
  have hm2 : Measurable (fun p : G₁ × G => (ι p.1)⁻¹ * p.2) :=
    ((hιc.comp continuous_fst).inv.mul continuous_snd).measurable
  have hm3 : Measurable (fun p : G × G₁ => (ι p.2)⁻¹ * p.1) :=
    ((hιc.comp continuous_snd).inv.mul continuous_fst).measurable
  have hWm : Measurable (fun g : G => ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * g) ∂μ₁) :=
    (hw.comp hm3).lintegral_prod_right'
  have hFm : Measurable (fun g : G => ψ g * ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * g) ∂μ₁) := hψ.mul hWm
  have hsumW : ∀ x : G, ∑' v : Γ₁, ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * (ι (v : G₁)⁻¹ * x)) ∂μ₁ = 1 := by
    intro x
    have h0 : ∫⁻ y, w ((ι y)⁻¹ * x) ∂μ₁ = 1 := by
      have h := lintegral_inv_eq_self (μ := μ₁) (fun y => w (ι y * x))
      simp only [map_inv] at h
      rw [h, hw1 x]
    rw [← h0, h𝓕₁.lintegral_eq_tsum'' (fun y => w ((ι y)⁻¹ * x))]
    refine tsum_congr fun v => lintegral_congr fun u => ?_
    simp only [Subgroup.smul_def, smul_eq_mul, map_mul, map_inv, mul_inv_rev, mul_assoc]
  have key : ∀ u : G₁, ∫⁻ g, w g * ψ (ι u * g) ∂μ = ∫⁻ g, w ((ι u)⁻¹ * g) * ψ g ∂μ := by
    intro u
    have h := lintegral_mul_left_eq_self (μ := μ) (fun x => w ((ι u)⁻¹ * x) * ψ x) (ι u)
    simp only [inv_mul_cancel_left] at h
    exact h
  have hpt : ∀ h : G, ∑' γ : Γ, ψ (γ • h) * ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * (γ • h)) ∂μ₁ =
      ∑' q, ψ (r q * h) := by
    intro h
    let E := Equiv.ofBijective _ (bijective_pair ι hι Γ Γ₁ hΓ r hr hQ)
    let F : G → ℝ≥0∞ := fun x => ψ x * ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * x) ∂μ₁
    calc ∑' γ : Γ, ψ (γ • h) * ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * (γ • h)) ∂μ₁
        = ∑' p : Q × Γ₁, F (E p • h) := (E.tsum_eq (fun γ => F (γ • h))).symm
      _ = ∑' q, ∑' v : Γ₁, F (E (q, v) • h) := ENNReal.tsum_prod (f := fun q v => F (E (q, v) • h))
      _ = ∑' q, ψ (r q * h) * ∑' v : Γ₁, ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * (ι (v : G₁)⁻¹ * (r q * h))) ∂μ₁ := by
          refine tsum_congr fun q => ?_
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun v => ?_
          show ψ ((ι (v : G₁)⁻¹ * r q) * h) * ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * ((ι (v : G₁)⁻¹ * r q) * h)) ∂μ₁ = _
          rw [mul_assoc, hinv _ (Γ₁.inv_mem v.2)]
      _ = ∑' q, ψ (r q * h) := by simp only [hsumW, mul_one]
  symm
  calc ∫⁻ g, w g * ∫⁻ u in 𝓕₁, ψ (ι u * g) ∂μ₁ ∂μ
      = ∫⁻ g, ∫⁻ u in 𝓕₁, w g * ψ (ι u * g) ∂μ₁ ∂μ := by
        refine lintegral_congr fun g => ?_
        rw [lintegral_const_mul (w g) (f := fun u => ψ (ι u * g)) (hψ.comp (hιm.mul_const g))]
    _ = ∫⁻ u in 𝓕₁, ∫⁻ g, w g * ψ (ι u * g) ∂μ ∂μ₁ :=
        lintegral_lintegral_swap ((hw.comp measurable_fst).mul (hψ.comp hm1)).aemeasurable
    _ = ∫⁻ u in 𝓕₁, ∫⁻ g, w ((ι u)⁻¹ * g) * ψ g ∂μ ∂μ₁ := lintegral_congr fun u => key u
    _ = ∫⁻ g, ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * g) * ψ g ∂μ₁ ∂μ :=
        lintegral_lintegral_swap ((hw.comp hm2).mul (hψ.comp measurable_snd)).aemeasurable
    _ = ∫⁻ g, ψ g * ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * g) ∂μ₁ ∂μ := by
        refine lintegral_congr fun g => ?_
        rw [lintegral_mul_const (ψ g) (f := fun u => w ((ι u)⁻¹ * g)) (hw.comp (hιm.inv.mul_const g))]
        exact mul_comm _ _
    _ = ∑' γ : Γ, ∫⁻ h in 𝓕, ψ (γ • h) * ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * (γ • h)) ∂μ₁ ∂μ :=
        h𝓕.lintegral_eq_tsum'' _
    _ = ∫⁻ h in 𝓕, ∑' γ : Γ, ψ (γ • h) * ∫⁻ u in 𝓕₁, w ((ι u)⁻¹ * (γ • h)) ∂μ₁ ∂μ :=
        (lintegral_tsum fun γ : Γ => (hFm.comp (measurable_const_mul (γ : G))).aemeasurable).symm
    _ = ∫⁻ h in 𝓕, ∑' q, ψ (r q * h) ∂μ := lintegral_congr fun h => hpt h

end

theorem lintegral_sum_cosets_average : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (G₁ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* G), IsClosedEmbedding ι → ∀ (μ : Measure G) [μ.IsHaarMeasure] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ] (Γ₁ : Subgroup G₁) [Countable Γ₁] (𝓕 : Set G) (𝓕₁ : Set G₁), IsFundamentalDomain Γ 𝓕 μ → IsFundamentalDomain Γ₁ 𝓕₁ μ₁ → μ₁ 𝓕₁ < ⊤ → (∀ u ∈ Γ₁, ι u ∈ Γ) → ∀ (Q : Type) [Countable Q] (r : Q → G), (∀ q, r q ∈ Γ) → (∀ γ ∈ Γ, ∃! q, ∃ u ∈ Γ₁, γ = ι u * r q) → ∀ φ : G → ℝ≥0∞, Measurable φ → (∀ u ∈ Γ₁, ∀ g, φ (ι u * g) = φ g) → ∫⁻ h in 𝓕, ∑' q, φ (r q * h) ∂μ = ∫⁻ h in 𝓕, ∑' q, (μ₁ 𝓕₁)⁻¹ * ∫⁻ u in 𝓕₁, φ (ι u * (r q * h)) ∂μ₁ ∂μ := by
  intro G _ _ _ _ _ _ _ _ G₁ _ _ _ _ _ _ _ ι hιce μ _ μ₁ _ Γ _ Γ₁ _ 𝓕 𝓕₁ h𝓕 h𝓕₁ hfin hΓ Q _ r hr hQ φ hφ hinv
  haveI : T2Space G₁ := hιce.isEmbedding.t2Space
  obtain ⟨hne, hright, hinvinv⟩ :=
    GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain G₁ Γ₁ μ₁ 𝓕₁ h𝓕₁ hfin
  haveI := hright
  haveI := hinvinv
  obtain ⟨w, hw, hw1⟩ := GlobalTheory.T.closed_subgroup_quotient_measure G G₁ ι hιce μ₁
  have hιc : Continuous ι := hιce.continuous
  have hι : Function.Injective ι := hιce.injective
  have hm : Measurable (fun p : G × G₁ => φ (ι p.2 * p.1)) :=
    hφ.comp ((hιc.comp continuous_snd).mul continuous_fst).measurable
  have hAm : Measurable (fun g : G => ∫⁻ u in 𝓕₁, φ (ι u * g) ∂μ₁) := hm.lintegral_prod_right'
  have hAinv : ∀ (v : G₁) (g : G),
      ∫⁻ u in 𝓕₁, φ (ι u * (ι v * g)) ∂μ₁ = ∫⁻ u in 𝓕₁, φ (ι u * g) ∂μ₁ := by
    intro v g
    have h := setLIntegral_mul_right_eq μ₁ Γ₁ 𝓕₁ h𝓕₁ (fun u => φ (ι u * g)) (fun γ hγ u => by
      simp only [map_mul, mul_assoc]
      exact hinv γ hγ _) v
    simpa only [map_mul, mul_assoc] using h
  have hA := lintegral_sum_cosets_eq ι hιc hι μ μ₁ Γ Γ₁ 𝓕 𝓕₁ h𝓕 h𝓕₁ hΓ r hr hQ w hw hw1 φ hφ hinv
  have hB := lintegral_sum_cosets_eq ι hιc hι μ μ₁ Γ Γ₁ 𝓕 𝓕₁ h𝓕 h𝓕₁ hΓ r hr hQ w hw hw1
    (fun g => (μ₁ 𝓕₁)⁻¹ * ∫⁻ u in 𝓕₁, φ (ι u * g) ∂μ₁) (hAm.const_mul _)
    (fun u _ g => by simp only [hAinv])
  rw [hA, hB]
  refine lintegral_congr fun g => ?_
  congr 1
  simp only [hAinv]
  rw [setLIntegral_const, mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel hne hfin.ne, one_mul]

end GlobalTheory.CompanionTheory.SW.Averaging
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.QuotientMeasureTowerStatement
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_measure_tower : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (G₁ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* G), IsClosedEmbedding ι → ∀ (μ : Measure G) [μ.IsHaarMeasure] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ] (Γ₁ : Subgroup G₁) [Countable Γ₁] (𝓕 : Set G) (𝓕₁ : Set G₁), IsFundamentalDomain Γ 𝓕 μ → IsFundamentalDomain Γ₁ 𝓕₁ μ₁ → μ₁ 𝓕₁ < ⊤ → (∀ u ∈ Γ₁, ι u ∈ Γ) → ∀ (Q : Type) [Countable Q] (r : Q → G), (∀ q, r q ∈ Γ) → (∀ γ ∈ Γ, ∃! q, ∃ u ∈ Γ₁, γ = ι u * r q) → ∀ φ : G → ℝ≥0∞, Measurable φ → (∀ u ∈ Γ₁, ∀ g, φ (ι u * g) = φ g) → ∫⁻ h in 𝓕, ∑' q, φ (r q * h) ∂μ = ∫⁻ h in 𝓕, ∑' q, (μ₁ 𝓕₁)⁻¹ * ∫⁻ u in 𝓕₁, φ (ι u * (r q * h)) ∂μ₁ ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.SW.Averaging.lintegral_sum_cosets_average | exact GlobalTheory.CompanionTheory.SW.Averaging.lintegral_sum_cosets_average | (intros; apply GlobalTheory.CompanionTheory.SW.Averaging.lintegral_sum_cosets_average <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicBoxLatticeCountRatio
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeBallCountRatioBound
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeBallCountRatioBound
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic.Packing

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Λ : Type} [AddCommGroup Λ]

def Sep (e : Λ →+ V) (r R : ℝ) (s : Finset Λ) : Prop :=
  (∀ l ∈ s, ‖e l‖ ≤ R) ∧ (s : Set Λ).Pairwise fun a b => r ≤ ‖e a - e b‖

theorem Sep.card_le {e : Λ →+ V} {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) {s : Finset Λ}
    (hs : Sep e r R s) : (s.card : ℝ) ≤ (3 * R / r) ^ Module.finrank ℝ V := by
  classical
  have hinj : Set.InjOn e (s : Set Λ) := by
    intro a ha b hb hab
    by_contra hne
    have : r ≤ ‖e a - e b‖ := hs.2 ha hb hne
    rw [hab, sub_self, norm_zero] at this
    linarith
  have hcard : (s.image e).card = s.card := Finset.card_image_of_injOn hinj
  have h1 := GlobalTheory.finset_card_le_of_separated (s.image e) hr (hr.le.trans hrR) (0 : V)
    (by
      intro a ha
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 ha
      simpa using hs.1 l hl)
    (by
      intro a ha b hb hab
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ha)
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb)
      have hlm : l ≠ m := fun h => hab (by rw [h])
      rw [dist_eq_norm]
      exact hs.2 hl hm hlm)
  rw [hcard] at h1
  exact h1.trans (GlobalTheory.one_add_two_mul_div_pow_le hr hrR _)

theorem exists_max_sep (e : Λ →+ V) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    ∃ s : Finset Λ, Sep e r R s ∧ ∀ t : Finset Λ, Sep e r R t → t.card ≤ s.card := by
  let S : Set ℕ := {n | ∃ s : Finset Λ, Sep e r R s ∧ s.card = n}
  have hne : S.Nonempty := ⟨0, ∅, ⟨by simp, by simp⟩, rfl⟩
  have hbd : BddAbove S := by
    refine ⟨⌊(3 * R / r) ^ Module.finrank ℝ V⌋₊, ?_⟩
    rintro n ⟨s, hs, rfl⟩
    exact Nat.le_floor (Sep.card_le hr hrR hs)
  obtain ⟨s, hs, hc⟩ := Nat.sSup_mem hne hbd
  exact ⟨s, hs, fun t ht => hc ▸ le_csSup hbd ⟨t, ht, rfl⟩⟩

theorem Sep.exists_near {e : Λ →+ V} {r R : ℝ} (hr : 0 < r) {s : Finset Λ}
    (hs : Sep e r R s) (hmax : ∀ t : Finset Λ, Sep e r R t → t.card ≤ s.card)
    {l : Λ} (hl : ‖e l‖ ≤ R) : ∃ t ∈ s, ‖e (l - t)‖ ≤ r := by
  classical
  by_contra hcon
  push_neg at hcon
  have hns : l ∉ s := fun h => by
    have := hcon l h
    simp only [sub_self, map_zero, norm_zero] at this
    linarith
  have hins : Sep e r R (insert l s) := by
    refine ⟨?_, ?_⟩
    · intro m hm
      rcases Finset.mem_insert.1 hm with rfl | hm
      · exact hl
      · exact hs.1 m hm
    · rw [Finset.coe_insert]
      refine Set.pairwise_insert.2 ⟨hs.2, ?_⟩
      intro b hb _
      have h := hcon b hb
      rw [map_sub] at h
      exact ⟨h.le, by rw [norm_sub_rev]; exact h.le⟩
  have := hmax _ hins
  rw [Finset.card_insert_of_notMem hns] at this
  omega

end GlobalTheory.CompanionTheory.Adelic.Packing


open GlobalTheory.CompanionTheory.Adelic.Packing in
theorem GlobalTheory.CompanionTheory.Adelic.tsum_indicator_norm_le_packing :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Λ : Type)
      [AddCommGroup Λ] (e : Λ →+ V) (r R : ℝ), 0 < r → r ≤ R →
      ∑' l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l ≤
        ENNReal.ofReal ((5 * R / r) ^ Module.finrank ℝ V) *
          ∑' l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ r} (fun _ => (1 : ℝ≥0∞)) l := by
  intro V _ _ _ Λ _ e r R hr hrR
  classical
  obtain ⟨s, hs, hmax⟩ := exists_max_sep e hr hrR
  set f : Λ → ℝ≥0∞ := Set.indicator {l : Λ | ‖e l‖ ≤ r} (fun _ => (1 : ℝ≥0∞)) with hf
  have hpt : ∀ l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l ≤
      ∑ t ∈ s, f (l - t) := by
    intro l
    by_cases hl : ‖e l‖ ≤ R
    · obtain ⟨t, ht, hlt⟩ := hs.exists_near hr hmax hl
      have h1 : f (l - t) = 1 := Set.indicator_of_mem (s := {l : Λ | ‖e l‖ ≤ r}) hlt _
      calc Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l ≤ 1 :=
            Set.indicator_le_self' (fun _ _ => zero_le) l
        _ = f (l - t) := h1.symm
        _ ≤ ∑ t ∈ s, f (l - t) :=
            Finset.single_le_sum (f := fun t => f (l - t)) (fun _ _ => zero_le) ht
    · rw [Set.indicator_of_notMem (by simpa using hl)]
      exact zero_le
  have hshift : ∀ t : Λ, ∑' l : Λ, f (l - t) = ∑' l : Λ, f l := fun t =>
    (Equiv.subRight t).tsum_eq f
  have hcard : (s.card : ℝ≥0∞) ≤ ENNReal.ofReal ((5 * R / r) ^ Module.finrank ℝ V) := by
    have h3 : (s.card : ℝ) ≤ (5 * R / r) ^ Module.finrank ℝ V := by
      refine (Sep.card_le hr hrR hs).trans (pow_le_pow_left₀ (by have := hr.le.trans hrR; positivity) ?_ _)
      have := hr.le.trans hrR
      gcongr
      norm_num
    calc (s.card : ℝ≥0∞) = ENNReal.ofReal (s.card : ℝ) := (ENNReal.ofReal_natCast _).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal h3
  calc ∑' l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l
      ≤ ∑' l : Λ, ∑ t ∈ s, f (l - t) := ENNReal.tsum_le_tsum hpt
    _ = ∑ t ∈ s, ∑' l : Λ, f (l - t) := by
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ = (s.card : ℝ≥0∞) * ∑' l : Λ, f l := by
        simp only [hshift, Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by gcongr
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeBallCountRatioBoundStatement
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_ball_count_ratio_bound : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Λ : Type) [AddCommGroup Λ] (e : Λ →+ V) (r R : ℝ), 0 < r → r ≤ R → ∑' l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l ≤ ENNReal.ofReal ((5 * R / r) ^ Module.finrank ℝ V) * ∑' l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ r} (fun _ => (1 : ℝ≥0∞)) l := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.tsum_indicator_norm_le_packing | exact GlobalTheory.CompanionTheory.Adelic.tsum_indicator_norm_le_packing | (intros; apply GlobalTheory.CompanionTheory.Adelic.tsum_indicator_norm_le_packing <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicBoxLatticeCountRatio
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Pack

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def intSub {d M : ℕ} (b : Module.Basis (Fin d) F E) {Λ : Type} [AddCommGroup Λ]
    (e : Λ →+ (Fin 1 → Fin M → AF F ⊗[F] E)) (N : ℕ) : AddSubgroup Λ where
  carrier := {l | ∀ v, (fun a i => (N : Fv F v ⊗[F] E) * projV v (projFin (e l)) a i) ∈ latV b v}
  zero_mem' := by
    intro v a i k
    simp [projV, projFin]
  add_mem' := by
    intro x y hx hy v a i k
    have h := add_mem (hx v a i k) (hy v a i k)
    simpa [projV, projFin, mul_add, map_add (f := _)] using h
  neg_mem' := by
    intro x hx v a i k
    have h := neg_mem (hx v a i k)
    simpa [projV, projFin, mul_neg, map_neg] using h

def coord (hF : IsTotallyReal F) {d M : ℕ} (b : Module.Basis (Fin d) F E) :
    (Fin 1 → Fin M → AF F ⊗[F] E) →+ PiLp 1 (fun _ : Fin 1 × Fin M × Fin d × InfinitePlace F => ℝ) :=
  AddMonoidHom.mk' (fun X => WithLp.toLp 1 fun p =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal p.2.2.2)
      ((Algebra.TensorProduct.basis (Ainf F) b).repr (projInf X p.1 p.2.1) p.2.2.1 p.2.2.2)) (by
    intro X Y
    ext p
    simp only [projInf, map_add (f := _), Pi.add_apply, Finsupp.coe_add, PiLp.add_apply]
    exact map_add _ _ _)

theorem norm_coord (hF : IsTotallyReal F) {d M : ℕ} (b : Module.Basis (Fin d) F E)
    (X : Fin 1 → Fin M → AF F ⊗[F] E) : ‖coord hF b X‖ = sizeTup b (projInf X) := by
  rw [PiLp.norm_eq_of_L1]
  simp only [sizeTup, sizeInf, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun v _ => ?_
  exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (IsTotallyReal.isReal v)).norm_map_of_map_zero
    (map_zero _) _

theorem finrank_coord (hF : IsTotallyReal F) (d M : ℕ) :
    Module.finrank ℝ (PiLp 1 (fun _ : Fin 1 × Fin M × Fin d × InfinitePlace F => ℝ)) =
      d * Module.finrank ℚ F * M := by
  have h : Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank F
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F
    simp only [IsTotallyReal.nrComplexPlaces_eq_zero] at h1 h2
    omega
  rw [(WithLp.linearEquiv 1 ℝ _).finrank_eq, Module.finrank_fintype_fun_eq_card]
  simp only [Fintype.card_prod, Fintype.card_fin, h]
  ring

theorem box_packing : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ), ∀ (Λ : Type) [AddCommGroup Λ] (e : Λ →+ (Fin 1 → Fin M → AF F ⊗[F] E)) (N : ℕ) (r R : ℝ), 0 < r → r ≤ R → ∑' l : Λ, (Set.indicator (box b N R) (fun _ => (1 : ℝ≥0∞))) (e l) ≤ ENNReal.ofReal ((5 * R / r) ^ (2 * Module.finrank ℚ F * M)) * ∑' l : Λ, (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) (e l) := by
  intro F E _ _ _ _ _ σ hσ d b M Λ _ e N r R hr hrR
  obtain ⟨hF, -, h2, -⟩ := hσ
  have hd : d = 2 := by
    rw [← h2, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  have key := GlobalTheory.T.lattice_ball_count_ratio_bound (PiLp 1 (fun _ : Fin 1 × Fin M × Fin 2 × InfinitePlace F => ℝ)) (intSub b e N)
    ((coord hF b).comp (e.comp (intSub b e N).subtype)) r R hr hrR
  rw [finrank_coord hF 2 M] at key
  have conv : ∀ t : ℝ, ∑' l : Λ, (Set.indicator (box b N t) (fun _ => (1 : ℝ≥0∞))) (e l) =
      ∑' l : intSub b e N, Set.indicator {l : intSub b e N |
        ‖((coord hF b).comp (e.comp (intSub b e N).subtype)) l‖ ≤ t} (fun _ => (1 : ℝ≥0∞)) l := by
    intro t
    have h := tsum_subtype ((intSub b e N : AddSubgroup Λ) : Set Λ)
      (fun l => Set.indicator {l : Λ | sizeTup b (projInf (e l)) ≤ t} (fun _ => (1 : ℝ≥0∞)) l)
    refine Eq.trans ?_ (Eq.trans h.symm ?_)
    · refine tsum_congr fun l => ?_
      have hb : e l ∈ box b N t ↔ l ∈ ((intSub b e N : AddSubgroup Λ) : Set Λ) ∧
          l ∈ {l : Λ | sizeTup b (projInf (e l)) ≤ t} := Iff.rfl
      by_cases hm : e l ∈ box b N t
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hb.1 hm).1, Set.indicator_of_mem (hb.1 hm).2]
      · rw [Set.indicator_of_notMem hm]
        by_cases h1 : l ∈ ((intSub b e N : AddSubgroup Λ) : Set Λ)
        · rw [Set.indicator_of_mem h1, Set.indicator_of_notMem fun h => hm (hb.2 ⟨h1, h⟩)]
        · rw [Set.indicator_of_notMem h1]
    · refine tsum_congr fun l => ?_
      simp [Set.indicator, norm_coord]
  rw [conv R, conv r]
  exact key

end GlobalTheory.CompanionTheory.SW.Pack
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicBoxLatticeCountRatioStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_box_lattice_count_ratio : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ), ∀ (Λ : Type) [AddCommGroup Λ] (e : Λ →+ (Fin 1 → Fin M → AF F ⊗[F] E)) (N : ℕ) (r R : ℝ), 0 < r → r ≤ R → ∑' l : Λ, (Set.indicator (box b N R) (fun _ => (1 : ℝ≥0∞))) (e l) ≤ ENNReal.ofReal ((5 * R / r) ^ (2 * Module.finrank ℚ F * M)) * ∑' l : Λ, (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) (e l) := by
  first | exact @GlobalTheory.CompanionTheory.SW.Pack.box_packing | exact GlobalTheory.CompanionTheory.SW.Pack.box_packing | (intros; apply GlobalTheory.CompanionTheory.SW.Pack.box_packing <;> assumption)
end
end
