module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicFiniteVolumeIntegralBound
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteVolumeInductionCompactSum

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CountingRationalVectorsBoxBound
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IsotropicVectorSplitsHyperbolicPlane
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IsotropicVectorSplitsHyperbolicPlane
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.HypSplit

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

theorem hE_eq_dot (u v : Fin M → E) :
    hE σ J u v = Matrix.vecMul (fun i => σ (u i)) J ⬝ᵥ v := by
  simp only [hE, hform, Matrix.vecMul, dotProduct, Finset.sum_mul, RingHom.coe_coe]
  exact Finset.sum_comm

def hLin (u : Fin M → E) : (Fin M → E) →ₗ[E] E where
  toFun := hE σ J u
  map_add' v w := by simp only [hE_eq_dot, dotProduct_add]
  map_smul' a v := by simp only [hE_eq_dot, dotProduct_smul, RingHom.id_apply]

@[simp] theorem hLin_apply (u v : Fin M → E) : hLin σ J u v = hE σ J u v := rfl

variable {σ J}

theorem hE_conj (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (u v : Fin M → E) :
    σ (hE σ J u v) = hE σ J v u := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hE, hform, map_sum, map_mul, RingHom.coe_coe, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

theorem exists_partner (hσ : ∀ a, σ (σ a) = a) (hJ : IsHermND σ J) (h2 : (2 : E) ≠ 0)
    (x : Fin M → E) (hx : x ≠ 0) (hxx : hE σ J x x = 0) :
    ∃ y, hE σ J x y = 1 ∧ hE σ J y y = 0 := by
  have hr : Matrix.vecMul (fun i => σ (x i)) J ≠ 0 := by
    intro h0
    have h1 := Matrix.eq_zero_of_vecMul_eq_zero hJ.2 h0
    apply hx
    funext i
    have h3 := congrFun h1 i
    simpa using h3
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hr
  have hj' : Matrix.vecMul (fun i => σ (x i)) J j ≠ 0 := hj
  obtain ⟨y₀, h1⟩ : ∃ y₀, hE σ J x y₀ = 1 := by
    refine ⟨Pi.single j (Matrix.vecMul (fun i => σ (x i)) J j)⁻¹, ?_⟩
    rw [hE_eq_dot, dotProduct_single, mul_inv_cancel₀ hj']
  have conj := hE_conj (J := J) hσ hJ.1
  have h1' : hE σ J y₀ x = 1 := by rw [← conj, h1, map_one]
  have hc : σ (hE σ J y₀ y₀) = hE σ J y₀ y₀ := conj _ _
  set c := hE σ J y₀ y₀ with hcdef
  have hc2 : σ (c / 2) = c / 2 := by rw [map_div₀, hc, map_ofNat]
  have hxy : hE σ J x (y₀ - (c / 2) • x) = 1 := by
    have := (hLin σ J x).map_sub y₀ ((c / 2) • x)
    simp only [map_smul, hLin_apply, smul_eq_mul, hxx, h1] at this
    simpa using this
  have hy₀y : hE σ J y₀ (y₀ - (c / 2) • x) = c / 2 := by
    have := (hLin σ J y₀).map_sub y₀ ((c / 2) • x)
    simp only [map_smul, hLin_apply, smul_eq_mul, h1', ← hcdef] at this
    rw [this]; field_simp; ring
  refine ⟨y₀ - (c / 2) • x, hxy, ?_⟩
  have := (hLin σ J (y₀ - (c / 2) • x)).map_sub y₀ ((c / 2) • x)
  simp only [map_smul, hLin_apply, smul_eq_mul] at this
  rw [this, ← conj y₀, hy₀y, hc2, ← conj x, hxy, map_one]
  ring

theorem finrank_perp (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j)
    {x y : Fin M → E} (hxx : hE σ J x x = 0) (hyy : hE σ J y y = 0) (hxy : hE σ J x y = 1) :
    Module.finrank E (LinearMap.ker ((hLin σ J x).prod (hLin σ J y))) + 2 = M := by
  have hyx : hE σ J y x = 1 := by rw [← hE_conj hσ hJ, hxy, map_one]
  have hs : Function.Surjective ((hLin σ J x).prod (hLin σ J y)) := by
    rintro ⟨a, b⟩
    refine ⟨a • y + b • x, Prod.ext ?_ ?_⟩
    · change hLin σ J x (a • y + b • x) = a
      simp only [map_add (f := _), map_smul, hLin_apply, smul_eq_mul, hxy, hxx, mul_one, mul_zero, add_zero]
    · change hLin σ J y (a • y + b • x) = b
      simp only [map_add (f := _), map_smul, hLin_apply, smul_eq_mul, hyy, hyx, mul_one, mul_zero, zero_add]
  have h := LinearMap.finrank_range_add_finrank_ker ((hLin σ J x).prod (hLin σ J y))
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_prod, Module.finrank_self,
    Module.finrank_fin_fun] at h
  omega

theorem gram_eq {n : ℕ} (c : Fin n → Fin M → E) :
    cT (σ : E →+* E) (Matrix.of c)ᵀ * J * (Matrix.of c)ᵀ = gramE σ J c := by
  ext a b
  simp only [Matrix.mul_apply, cT, gramE, hE, hform, Finset.sum_mul, Matrix.transpose_apply,
    Matrix.map_apply, Matrix.of_apply]
  exact Finset.sum_comm

theorem det_ne_zero_of_hypJ {M₁ : ℕ} (A : Matrix (Fin M₁) (Fin M₁) E) (h : (hypJ A).det ≠ 0) :
    A.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  apply h
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨Fin.cons 0 (Fin.cons 0 v), ?_, ?_⟩
  · intro h1
    apply hv
    funext i
    simpa using congrFun h1 i.succ.succ
  · funext a
    refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun a => ?_) a) a
    · simp [Matrix.mulVec, dotProduct, hypJ, Fin.sum_univ_succ]
    · simp [Matrix.mulVec, dotProduct, hypJ, Fin.sum_univ_succ]
    · have := congrFun hAv a
      simpa [Matrix.mulVec, dotProduct, hypJ, Fin.sum_univ_succ] using this

theorem selfDualLattice_projection_mem_of_unit_length (hσ : ∀ a, σ (σ a) = a) (h2 : (2 : E) ≠ 0) {M₁ : ℕ}
    {J : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E} (hJ : IsHermND σ J)
    {x y : Fin (M₁ + 2) → E} (hxx : hE σ J x x = 0) (hyy : hE σ J y y = 0)
    (hxy : hE σ J x y = 1) :
    ∃ (g : GL (Fin (M₁ + 2)) E) (J₁ : Matrix (Fin M₁) (Fin M₁) E), IsHermND σ J₁ ∧
      hypJ J₁ = cT (σ : E →+* E) (g : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E) * J *
        (g : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E) := by
  have conj := hE_conj (J := J) hσ hJ.1
  have hyx : hE σ J y x = 1 := by rw [← conj, hxy, map_one]
  have hfr := finrank_perp hσ hJ.1 hxx hyy hxy
  set W := LinearMap.ker ((hLin σ J x).prod (hLin σ J y)) with hW
  have hfr' : Module.finrank E W = M₁ := by omega
  let b : Module.Basis (Fin M₁) E W := Module.finBasisOfFinrankEq E W hfr'
  have hbx : ∀ i, hE σ J x (b i : Fin (M₁ + 2) → E) = 0 := fun i => by
    have h3 : ((hLin σ J x).prod (hLin σ J y)) (b i : Fin (M₁ + 2) → E) = 0 :=
      LinearMap.mem_ker.mp (b i).2
    exact congrArg Prod.fst h3
  have hby : ∀ i, hE σ J y (b i : Fin (M₁ + 2) → E) = 0 := fun i => by
    have h3 : ((hLin σ J x).prod (hLin σ J y)) (b i : Fin (M₁ + 2) → E) = 0 :=
      LinearMap.mem_ker.mp (b i).2
    exact congrArg Prod.snd h3
  have hbx' : ∀ i, hE σ J (b i : Fin (M₁ + 2) → E) x = 0 := fun i => by
    rw [← conj, hbx, map_zero]
  have hby' : ∀ i, hE σ J (b i : Fin (M₁ + 2) → E) y = 0 := fun i => by
    rw [← conj, hby, map_zero]
  let c : Fin (M₁ + 2) → Fin (M₁ + 2) → E :=
    Fin.cons x (Fin.cons y fun i => (b i : Fin (M₁ + 2) → E))
  have hli : LinearIndependent E c := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at ha
    simp only [c, Fin.cons_zero, Fin.cons_succ] at ha
    have e1 := congrArg (hLin σ J x) ha
    have e2 := congrArg (hLin σ J y) ha
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_smul, map_sum, hLin_apply, smul_eq_mul, hxx, hyy, hxy, hyx, hbx, hby,
      map_zero, mul_zero, zero_add, add_zero, mul_one, Finset.sum_const_zero] at e1 e2
    rw [e1, e2] at ha
    simp only [zero_smul, zero_add] at ha
    have e3 : ∑ i, a i.succ.succ • b i = 0 := by
      apply Subtype.ext
      simpa using ha
    have e4 := Fintype.linearIndependent_iff.mp b.linearIndependent _ e3
    intro i
    refine Fin.cases e2 (fun i => Fin.cases e1 e4 i) i
  have hunit : IsUnit (Matrix.of c)ᵀ := by
    exact (Matrix.linearIndependent_cols_iff_isUnit (A := (Matrix.of c)ᵀ)).mp hli
  let J₁ : Matrix (Fin M₁) (Fin M₁) E := gramE σ J fun i => (b i : Fin (M₁ + 2) → E)
  have hgram : hypJ J₁ = gramE σ J c := by
    ext a b'
    refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun a => ?_) a) a <;>
      refine Fin.cases ?_ (fun b' => Fin.cases ?_ (fun b' => ?_) b') b' <;>
      simp [hypJ, gramE, c, J₁, hxx, hyy, hxy, hyx, hbx, hby, hbx', hby']
  have hdet : (hypJ J₁).det ≠ 0 := by
    rw [hgram, ← gram_eq, Matrix.det_mul, Matrix.det_mul]
    have hu : (Matrix.of c)ᵀ.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero
    have hcT : (cT (σ : E →+* E) (Matrix.of c)ᵀ).det ≠ 0 := by
      rw [cT, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      simpa using hu
    exact mul_ne_zero (mul_ne_zero hcT hJ.2) hu
  refine ⟨hunit.unit, J₁, ⟨fun i j => conj _ _, det_ne_zero_of_hypJ J₁ hdet⟩, ?_⟩
  rw [hgram, ← gram_eq]
  rfl

end Alg

theorem sigma_invol {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (a : E) : σ (σ a) = a := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem splitHyp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x : Fin M → E, x ≠ 0 → hE σ J x x = 0 → ∃ (M₁ : ℕ) (hM : M = M₁ + 2) (g : GL (Fin (M₁ + 2)) E) (J₁ : Matrix (Fin M₁) (Fin M₁) E), IsHermND σ J₁ ∧ hypJ J₁ = cT (σ : E →+* E) (g : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E) * (hM ▸ J) * (g : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E) := by
  intro F E _ _ _ _ _ σ hcm M J hJ x hx hxx
  have hσ := sigma_invol σ hcm
  have h2 : (2 : E) ≠ 0 := two_ne_zero
  obtain ⟨y, hxy, hyy⟩ := exists_partner hσ hJ h2 x hx hxx
  have hfr := finrank_perp hσ hJ.1 hxx hyy hxy
  obtain ⟨M₁, rfl⟩ : ∃ M₁, M = M₁ + 2 := ⟨_, hfr.symm⟩
  obtain ⟨g, J₁, h1, h3⟩ := selfDualLattice_projection_mem_of_unit_length hσ h2 hJ hxx hyy hxy
  exact ⟨M₁, rfl, g, J₁, h1, h3⟩

end GlobalTheory.CompanionTheory.SW.HypSplit
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IsotropicVectorSplitsHyperbolicPlaneStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_vector_splits_hyperbolic_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x : Fin M → E, x ≠ 0 → hE σ J x x = 0 → ∃ (M₁ : ℕ) (hM : M = M₁ + 2) (g : GL (Fin (M₁ + 2)) E) (J₁ : Matrix (Fin M₁) (Fin M₁) E), IsHermND σ J₁ ∧ hypJ J₁ = cT (σ : E →+* E) (g : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E) * (hM ▸ J) * (g : Matrix (Fin (M₁ + 2)) (Fin (M₁ + 2)) E) := by
  first | exact @GlobalTheory.CompanionTheory.SW.HypSplit.splitHyp | exact GlobalTheory.CompanionTheory.SW.HypSplit.splitHyp | (intros; apply GlobalTheory.CompanionTheory.SW.HypSplit.splitHyp <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CountingRationalVectorsBoxBound
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.IsoBox

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem hform_eq_dot {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (s : A →+* A)
    (J : Matrix n n A) (x y : n → A) :
    hform s J x y = (fun i => s (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (s : A →+* A)
    (J g : Matrix n n A) (x y : n → A) :
    hform s J (g *ᵥ x) (g *ᵥ y) = hform s (cT s g * J * g) x y := by
  rw [hform_eq_dot, hform_eq_dot, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec (fun i => s (x i)) (cT s g)]
  congr 1
  ext i
  simp [cT, Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]

theorem gramE_mulVec (σ : E →ₐ[F] E) {M n : ℕ} (J g : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → E) :
    gramE σ J (fun a => g *ᵥ X a) = gramE σ (cT (σ : E →+* E) g * J * g) X := by
  funext a c
  exact hform_mulVec (σ : E →+* E) J g (X a) (X c)

theorem isotropic_preimage (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (g : GL (Fin M) E) :
    {X : Fin 1 → Fin M → E | (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ X a) ∈
        {X : Fin 1 → Fin M → E | X ≠ 0 ∧ gramE σ J X = 0}} =
      {X : Fin 1 → Fin M → E | X ≠ 0 ∧
        gramE σ (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J *
          (g : Matrix (Fin M) (Fin M) E)) X = 0} := by
  ext X
  simp only [Set.mem_ofPred_eq, gramE_mulVec]
  refine and_congr_left fun _ => not_congr ?_
  constructor
  · intro h
    funext a
    have h1 := congrFun h a
    have h2 : ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ
        ((g : Matrix (Fin M) (Fin M) E) *ᵥ X a) = X a := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel]
      simp
    rw [← h2]
    simp only [Pi.zero_apply] at h1 ⊢
    rw [h1, Matrix.mulVec_zero]
  · intro h
    funext a
    simp [h]

theorem actTup_smul (R : Type) [CommRing R] [Algebra F R] {M n : ℕ} (g : GL (Fin M) (R ⊗[F] E))
    (c : R ⊗[F] E) (Y : Fin n → Fin M → R ⊗[F] E) :
    actTup R g (c • Y) = c • actTup R g Y := by
  funext a
  simp [actTup, Matrix.mulVec_smul]

theorem continuous_actTup (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing (R ⊗[F] E)] {M n : ℕ} (g : GL (Fin M) (R ⊗[F] E)) :
    Continuous (actTup R g : (Fin n → Fin M → R ⊗[F] E) → _) := by
  refine continuous_pi fun a => continuous_pi fun i => ?_
  simp only [actTup, Matrix.mulVec, dotProduct]
  refine continuous_finsetSum _ fun j _ => ?_
  exact continuous_const.mul ((continuous_apply j).comp (continuous_apply a))

end GlobalTheory.CompanionTheory.SW.IsoBox

namespace GlobalTheory.CompanionTheory.SW

theorem mean_isotropic_box : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (N : ℕ), 0 < N → ∃ C : ℝ, ∀ r : ℝ, 0 < r → cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0 ∧ gramE σ J X = 0} (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) ≤ ENNReal.ofReal (C * r ^ (2 * Module.finrank ℚ F * (M - 1))) := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM μ 𝓕 hH hF d b N hN
  by_cases hiso : ∃ x : Fin M → E, x ≠ 0 ∧ hE σ J x x = 0
  · obtain ⟨x, hx, hxx⟩ := hiso
    obtain ⟨M₁, hM₁, g, J₁, hJ₁, hg⟩ := GlobalTheory.T.isotropic_vector_splits_hyperbolic_plane F E σ hCM M J hJ x hx hxx
    subst hM₁
    obtain ⟨μ', 𝓕', hH', hF', -, hT⟩ :=
      GlobalTheory.T.fundamental_domain_transport_congruent_form F E σ hCM (M₁ + 2) J hJ g (hypJ J₁) hg μ 𝓕 hH hF
    obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_real_flow_adelic_units F E σ hCM
    obtain ⟨hbc, -, hsc⟩ := GlobalTheory.T.adelic_boxes_compact_exhaust F E σ hCM d b 1 (M₁ + 2)
    obtain ⟨⟨hA1, hA2, hA3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
    have := hA1
    have := hA2
    have := hA3
    have : IsTopologicalRing (AF F ⊗[F] E) :=
      (GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)).1
    set G : GL (Fin (M₁ + 2)) (AF F ⊗[F] E) := bc (inclR (AF F)) g with hG
    have hΩ : IsCompact (actTup (AF F) G ⁻¹' (box b N 1 : Set (Fin 1 → Fin (M₁ + 2) → AF F ⊗[F] E))) := by
      have himg : actTup (AF F) G ⁻¹' (box b N 1 : Set (Fin 1 → Fin (M₁ + 2) → AF F ⊗[F] E)) =
          actTup (AF F) G⁻¹ '' box b N 1 := by
        ext Y
        constructor
        · intro hY
          refine ⟨_, hY, ?_⟩
          funext a
          simp [actTup, Matrix.mulVec_mulVec]
        · rintro ⟨Z, hZ, rfl⟩
          have : actTup (AF F) G (actTup (AF F) G⁻¹ Z) = Z := by
            funext a
            simp [actTup, Matrix.mulVec_mulVec]
          simpa [Set.mem_preimage, this] using hZ
      rw [himg]
      exact (hbc N 1 hN).image (IsoBox.continuous_actTup (AF F) G⁻¹)
    obtain ⟨C, hC⟩ := GlobalTheory.T.hyperbolic_finite_volume_integral_bound F E σ hCM M₁ J₁ hJ₁ (by omega)
      (GlobalTheory.CompanionTheory.SW.finVol_unitaryGroup F E σ hCM M₁ J₁ hJ₁) τ hτ μ' 𝓕' hH' hF' _ hΩ
    refine ⟨C, fun r hr => ?_⟩
    have hfun : (fun Y : Fin 1 → Fin (M₁ + 2) → AF F ⊗[F] E =>
          Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞)) (actTup (AF F) G Y)) =
        fun Y => (Set.indicator (actTup (AF F) G ⁻¹' box b N 1) (fun _ => (1 : ℝ≥0∞)))
          (((τ (Multiplicative.ofAdd (-Real.log r)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • Y) := by
      funext Y
      have hmem : actTup (AF F) G Y ∈ (box b N r : Set (Fin 1 → Fin (M₁ + 2) → AF F ⊗[F] E)) ↔
          ((τ (Multiplicative.ofAdd (-Real.log r)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • Y ∈
            actTup (AF F) G ⁻¹' (box b N 1 : Set (Fin 1 → Fin (M₁ + 2) → AF F ⊗[F] E)) := by
        have h := hsc τ hτ N r (-Real.log r) (actTup (AF F) G Y)
        have h1 : Real.exp (-Real.log r) * r = 1 := by
          rw [Real.exp_neg, Real.exp_log hr]
          exact inv_mul_cancel₀ hr.ne'
        rw [h1] at h
        rw [Set.mem_preimage, IsoBox.actTup_smul]
        exact h.symm
      by_cases hY : actTup (AF F) G Y ∈ (box b N r : Set (Fin 1 → Fin (M₁ + 2) → AF F ⊗[F] E))
      · rw [Set.indicator_of_mem hY, Set.indicator_of_mem (hmem.1 hY)]
      · rw [Set.indicator_of_notMem hY, Set.indicator_of_notMem (fun h => hY (hmem.2 h))]
    have hset := IsoBox.isotropic_preimage σ J g
    rw [← hg] at hset
    rw [hT 1, hset, hfun]
    simpa using hC r hr
  · refine ⟨0, fun r _ => ?_⟩
    have hempty : {X : Fin 1 → Fin M → E | X ≠ 0 ∧ gramE σ J X = 0} = ∅ := by
      ext X
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hX hgr
      apply hiso
      refine ⟨X 0, fun h0 => hX ?_, congrFun (congrFun hgr 0) 0⟩
      funext a
      rw [Subsingleton.elim a 0, h0]
      rfl
    simp [cntI, hempty]

end GlobalTheory.CompanionTheory.SW
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CountingRationalVectorsBoxBoundStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_vector_count_box_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (N : ℕ), 0 < N → ∃ C : ℝ, ∀ r : ℝ, 0 < r → cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0 ∧ gramE σ J X = 0} (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) ≤ ENNReal.ofReal (C * r ^ (2 * Module.finrank ℚ F * (M - 1))) := by
  first | exact @GlobalTheory.CompanionTheory.SW.mean_isotropic_box | exact GlobalTheory.CompanionTheory.SW.mean_isotropic_box | (intros; apply GlobalTheory.CompanionTheory.SW.mean_isotropic_box <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CountingVectorsBoundedLargeRadius
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaCountCompactFinite
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaCountCompactFinite
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.CntFin

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {σ : E →ₐ[F] E} {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
  {μ : Measure (HA (AF F) σ J)} {𝓕 : Set (HA (AF F) σ J)}

theorem cntI_mono_fun {S : Set (Fin n → Fin M → E)}
    {Φ Ψ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞} (h : ∀ Y, Φ Y ≤ Ψ Y) :
    cntI σ J μ 𝓕 S Φ ≤ cntI σ J μ 𝓕 S Ψ :=
  lintegral_mono fun _ => ENNReal.tsum_le_tsum fun _ => h _

theorem cntI_le_of_contrib {S S' : Set (Fin n → Fin M → E)}
    {Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞}
    (h : ∀ (g : HA (AF F) σ J) (X : Fin n → Fin M → E), X ∈ S →
      Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) X)) ≠ 0 → X ∈ S') :
    cntI σ J μ 𝓕 S Φ ≤ cntI σ J μ 𝓕 S' Φ := by
  refine lintegral_mono fun g => ?_
  rw [tsum_subtype S (fun X => Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) X))),
    tsum_subtype S' (fun X => Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) X)))]
  refine ENNReal.tsum_le_tsum fun X => ?_
  by_cases hX : X ∈ S
  · by_cases h0 : Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) X)) = 0
    · simp [Set.indicator, h0]
    · simp [Set.indicator, hX, h g X hX h0]
  · simp [Set.indicator, hX]

theorem cntI_union_le [Countable E] {S S' : Set (Fin n → Fin M → E)}
    {Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞}
    (hm : ∀ X : Fin n → Fin M → E,
      Measurable fun g : HA (AF F) σ J => Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) X))) :
    cntI σ J μ 𝓕 (S ∪ S') Φ ≤ cntI σ J μ 𝓕 S Φ + cntI σ J μ 𝓕 S' Φ := by
  unfold cntI
  rw [← lintegral_add_left (Measurable.tsum fun X : S => hm X)]
  exact lintegral_mono fun g => ENNReal.tsum_union_le
    (fun X => Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) X))) S S'

end SlopeTestRemainingChoices

theorem cntI_nonzero_lt_top : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M →
    ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 →
    ∀ Ω : Set (Fin 1 → Fin M → AF F ⊗[F] E), IsCompact Ω →
      cntI σ J μ 𝓕 {X | X ≠ 0} (Set.indicator Ω (fun _ => (1 : ℝ≥0∞))) < ⊤ := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM μ 𝓕 hH hFD Ω hΩ
  classical
  obtain ⟨⟨hAlc, hAsc, hAt2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := hAlc
  haveI := hAsc
  haveI := hAt2
  obtain ⟨hTG, -, -, -, hBor, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ (AF F)
  haveI := hTG
  haveI := hBor
  obtain ⟨-, -, -, hKt2, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)
  haveI := hKt2
  haveI : Countable E :=
    ((Module.finBasis ℚ E).equivFun.toEquiv).injective.countable
  haveI : FiniteDimensional F E :=
    Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hcl : IsClosed Ω := hΩ.isClosed
  set Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞ := Set.indicator Ω (fun _ => (1 : ℝ≥0∞)) with hΦ

  have hm : ∀ X : Fin 1 → Fin M → E,
      Measurable fun g : HA (AF F) σ J => Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) X)) := by
    intro X
    have hc : Continuous fun g : HA (AF F) σ J => actW (AF F) σ J g⁻¹ (ratTup (AF F) X) :=
      (hact 1).1.comp (continuous_inv.prodMk continuous_const)
    have hs : MeasurableSet ((fun g : HA (AF F) σ J => actW (AF F) σ J g⁻¹ (ratTup (AF F) X)) ⁻¹' Ω) :=
      (hcl.preimage hc).measurableSet
    have he : (fun g : HA (AF F) σ J => Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) X))) =
        Set.indicator ((fun g : HA (AF F) σ J => actW (AF F) σ J g⁻¹ (ratTup (AF F) X)) ⁻¹' Ω)
          (fun _ => (1 : ℝ≥0∞)) := by
      funext g
      by_cases hg : actW (AF F) σ J g⁻¹ (ratTup (AF F) X) ∈ Ω <;> simp [hΦ, Set.indicator, hg]
    rw [he]
    exact measurable_const.indicator hs

  have hzero : cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0 ∧ gramE σ J X = 0} Φ < ⊤ := by
    obtain ⟨-, hbox, -⟩ := GlobalTheory.T.adelic_boxes_compact_exhaust F E σ hCM _ (Module.finBasis F E) 1 M
    obtain ⟨N, r, hN, hr, hsub⟩ := hbox Ω hΩ
    obtain ⟨C, hC⟩ := GlobalTheory.T.isotropic_vector_count_box_bound F E σ hCM M J hJ hM μ 𝓕 hH hFD _ (Module.finBasis F E) N hN
    refine lt_of_le_of_lt (le_trans (cntI_mono_fun fun Y => ?_) (hC r hr)) ENNReal.ofReal_lt_top
    exact Set.indicator_le_indicator_of_subset hsub (fun _ => zero_le) Y

  have hlen : ∀ t : F, t ≠ 0 →
      cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | gramE σ J X = fun _ _ => algebraMap F E t} Φ < ⊤ := by
    intro t ht
    exact GlobalTheory.T.finite_volume_induction_compact_sum F E σ hCM M J hJ
      (fun M' _ J' hJ' => GlobalTheory.CompanionTheory.SW.finVol_unitaryGroup F E σ hCM M' J' hJ') t ht μ 𝓕 hH hFD Ω hΩ

  have hfinset : ∀ T : Finset F, (∀ t ∈ T, t ≠ 0) →
      cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | (X ≠ 0 ∧ gramE σ J X = 0) ∨
        ∃ t ∈ T, gramE σ J X = fun _ _ => algebraMap F E t} Φ < ⊤ := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      simpa using hzero
    | insert a T _ ih =>
      intro hT
      have hsub : cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | (X ≠ 0 ∧ gramE σ J X = 0) ∨
          ∃ t ∈ insert a T, gramE σ J X = fun _ _ => algebraMap F E t} Φ ≤
          cntI σ J μ 𝓕 ({X : Fin 1 → Fin M → E | gramE σ J X = fun _ _ => algebraMap F E a} ∪
            {X : Fin 1 → Fin M → E | (X ≠ 0 ∧ gramE σ J X = 0) ∨
              ∃ t ∈ T, gramE σ J X = fun _ _ => algebraMap F E t}) Φ := by
        refine cntI_le_of_contrib fun g X hX _ => ?_
        rcases hX with hX | ⟨t, ht, hX⟩
        · exact Or.inr (Or.inl hX)
        · rcases Finset.mem_insert.1 ht with rfl | ht'
          · exact Or.inl hX
          · exact Or.inr (Or.inr ⟨t, ht', hX⟩)
      refine lt_of_le_of_lt (hsub.trans (cntI_union_le hm)) (ENNReal.add_lt_top.2 ⟨?_, ?_⟩)
      · exact hlen a (hT a (Finset.mem_insert_self a T))
      · exact ih fun t ht => hT t (Finset.mem_insert_of_mem ht)
  obtain ⟨hlenQ, hgram, hfin⟩ := GlobalTheory.T.rational_gram_adelic_compact_finite F E σ hCM M J hJ
  refine lt_of_le_of_lt ?_ (hfinset ((hfin Ω hΩ).toFinset.erase 0)
    fun t ht => (Finset.mem_erase.1 ht).1)
  refine cntI_le_of_contrib fun g X hX hne => ?_
  have hY : actW (AF F) σ J g⁻¹ (ratTup (AF F) X) ∈ Ω := by
    by_contra hY
    exact hne (by simp [hΦ, Set.indicator, hY])
  obtain ⟨t, ht⟩ := hlenQ X
  by_cases h0 : t = 0
  · refine Or.inl ⟨hX, ?_⟩
    rw [ht, h0]
    funext a b
    simp
  · refine Or.inr ⟨t, Finset.mem_erase.2 ⟨h0, ?_⟩, ht⟩
    refine (Set.Finite.mem_toFinset _).2 ⟨_, hY, ?_⟩
    rw [((hact 1).2.2.2 g⁻¹ (ratTup (AF F) X)), hgram 1 X, ht]
    funext a b
    rfl

end GlobalTheory.CompanionTheory.SW.CntFin
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaCountCompactFiniteStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_count_compact_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ Ω : Set (Fin 1 → Fin M → AF F ⊗[F] E), IsCompact Ω → cntI σ J μ 𝓕 {X | X ≠ 0} (Set.indicator Ω (fun _ => (1 : ℝ≥0∞))) < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.SW.CntFin.cntI_nonzero_lt_top | exact GlobalTheory.CompanionTheory.SW.CntFin.cntI_nonzero_lt_top | (intros; apply GlobalTheory.CompanionTheory.SW.CntFin.cntI_nonzero_lt_top <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CountingVectorsBoundedLargeRadius
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.CntLarge

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def orbitHom (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA (AF F) σ J) :
    (Fin 1 → Fin M → E) →+ (Fin 1 → Fin M → AF F ⊗[F] E) where
  toFun X := actW (AF F) σ J h (ratTup (AF F) X)
  map_zero' := by
    funext a i
    simp [actW, actTup, ratTup, inclR, Matrix.mulVec, dotProduct]
  map_add' X Y := by
    funext a i
    simp [actW, actTup, ratTup, inclR, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib,
      TensorProduct.tmul_add]

theorem count_le (hpack : ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (Λ : Type) [AddCommGroup Λ]
      (e : Λ →+ (Fin 1 → Fin M → AF F ⊗[F] E)) (N : ℕ) (r R : ℝ), 0 < r → r ≤ R →
      ∑' l : Λ, (Set.indicator (box b N R) (fun _ => (1 : ℝ≥0∞))) (e l) ≤
        ENNReal.ofReal ((5 * R / r) ^ (2 * Module.finrank ℚ F * M)) *
          ∑' l : Λ, (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) (e l))
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA (AF F) σ J)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (N : ℕ) {r₀ r : ℝ} (h0 : 0 < r₀) (hr : r₀ ≤ r) :
    ∑' X : {X : Fin 1 → Fin M → E | X ≠ 0},
        (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞)))
          (actW (AF F) σ J h (ratTup (AF F) (X : Fin 1 → Fin M → E))) ≤
      ENNReal.ofReal ((5 * r / r₀) ^ (2 * Module.finrank ℚ F * M)) *
        (1 + ∑' X : {X : Fin 1 → Fin M → E | X ≠ 0},
          (Set.indicator (box b N r₀) (fun _ => (1 : ℝ≥0∞)))
            (actW (AF F) σ J h (ratTup (AF F) (X : Fin 1 → Fin M → E)))) := by
  classical
  set e := orbitHom σ J h with he
  have key := hpack d b M (Fin 1 → Fin M → E) e N r₀ r h0 hr
  have hsplit : ∑' X : Fin 1 → Fin M → E, (Set.indicator (box b N r₀) (fun _ => (1 : ℝ≥0∞))) (e X) ≤
      1 + ∑' X : {X : Fin 1 → Fin M → E | X ≠ 0},
        (Set.indicator (box b N r₀) (fun _ => (1 : ℝ≥0∞))) (e X) := by
    rw [ENNReal.tsum_eq_add_tsum_ite (0 : Fin 1 → Fin M → E)]
    refine add_le_add (by rw [Set.indicator_apply]; split_ifs <;> simp) ?_
    rw [tsum_subtype {X : Fin 1 → Fin M → E | X ≠ 0}
      (fun X => (Set.indicator (box b N r₀) (fun _ => (1 : ℝ≥0∞))) (e X))]
    refine le_of_eq (tsum_congr fun X => ?_)
    by_cases hX : X = 0 <;> simp [hX]
  have hle : ∑' X : {X : Fin 1 → Fin M → E | X ≠ 0},
      (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) (e X) ≤
      ∑' X : Fin 1 → Fin M → E, (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) (e X) := by
    rw [tsum_subtype {X : Fin 1 → Fin M → E | X ≠ 0}
      (fun X => (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) (e X))]
    exact ENNReal.tsum_le_tsum fun X => Set.indicator_le_self _ _ _
  exact hle.trans (key.trans (mul_le_mul_right hsplit _))

theorem cnt_large : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (N : ℕ) (r₀ : ℝ), 0 < N → 0 < r₀ → ∃ C : ℝ, ∀ r : ℝ, r₀ ≤ r → cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0} (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) ≤ ENNReal.ofReal (C * r ^ (2 * Module.finrank ℚ F * M)) := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM μ 𝓕 hμ h𝓕 d b N r₀ hN h0
  have hvol : μ 𝓕 < ⊤ := ((finVol_unitaryGroup F E σ hσ M J hJ).2 μ hμ).2 𝓕 h𝓕
  have hcomp : IsCompact (box b N r₀ : Set (Fin 1 → Fin M → AF F ⊗[F] E)) :=
    (GlobalTheory.T.adelic_boxes_compact_exhaust F E σ hσ d b 1 M).1 N r₀ hN
  have hcnt := GlobalTheory.T.theta_count_compact_finite F E σ hσ M J hJ hM μ 𝓕 hμ h𝓕 _ hcomp
  set B : ℝ≥0∞ := μ 𝓕 + cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0}
    (Set.indicator (box b N r₀) (fun _ => (1 : ℝ≥0∞))) with hB
  have hBtop : B ≠ ⊤ := (ENNReal.add_lt_top.2 ⟨hvol, hcnt⟩).ne
  set k := 2 * Module.finrank ℚ F * M with hk
  refine ⟨(5 / r₀) ^ k * B.toReal, fun r hr => ?_⟩
  have hpt : ∀ h : HA (AF F) σ J, _ := fun h => count_le (fun d b M Λ _ e N r R => GlobalTheory.T.adelic_box_lattice_count_ratio F E σ hσ d b M Λ e N r R)
    σ J h⁻¹ b N h0 hr
  have hr0 : 0 ≤ r := h0.le.trans hr
  calc cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0} (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞)))
      ≤ ∫⁻ h in 𝓕, ENNReal.ofReal ((5 * r / r₀) ^ k) *
          (1 + ∑' X : {X : Fin 1 → Fin M → E | X ≠ 0},
            (Set.indicator (box b N r₀) (fun _ => (1 : ℝ≥0∞)))
              (actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin 1 → Fin M → E)))) ∂μ :=
        lintegral_mono fun h => hpt h
    _ = ENNReal.ofReal ((5 * r / r₀) ^ k) * B := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left measurable_const]
        simp [hB, cntI]
    _ = ENNReal.ofReal ((5 / r₀) ^ k * B.toReal * r ^ k) := by
        have : (5 / r₀) ^ k * B.toReal * r ^ k = (5 * r / r₀) ^ k * B.toReal := by
          rw [show 5 * r / r₀ = 5 / r₀ * r by ring, mul_pow]; ring
        rw [this, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hBtop]

end GlobalTheory.CompanionTheory.SW.CntLarge
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CountingVectorsBoundedLargeRadiusStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.counting_vectors_bounded_large_radius : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (N : ℕ) (r₀ : ℝ), 0 < N → 0 < r₀ → ∃ C : ℝ, ∀ r : ℝ, r₀ ≤ r → cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0} (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) ≤ ENNReal.ofReal (C * r ^ (2 * Module.finrank ℚ F * M)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.CntLarge.cnt_large | exact GlobalTheory.CompanionTheory.SW.CntLarge.cnt_large | (intros; apply GlobalTheory.CompanionTheory.SW.CntLarge.cnt_large <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SmallBoxGramScalarZero
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SmallBoxGramScalarZero
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.SmallQ

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem gramR_smul {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (s : R)
    (X : Fin n → Fin M → R ⊗[F] E) (a c : Fin n) :
    gramR R σ J ((s ⊗ₜ[F] (1 : E)) • X) a c =
      ((s ⊗ₜ[F] (1 : E)) * (s ⊗ₜ[F] (1 : E))) * gramR R σ J X a c := by
  have hs : sigR R σ (s ⊗ₜ[F] (1 : E)) = s ⊗ₜ[F] (1 : E) := by simp [sigR]
  simp only [gramR, hR, hform, Pi.smul_apply, smul_eq_mul, map_mul, hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem small_length : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (N : ℕ), 0 < N → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ (t : F) (Y : Fin 1 → Fin M → AF F ⊗[F] E), Y ∈ box b N r₀ → (gramR (AF F) σ J Y = fun _ _ => inclR (AF F) (algebraMap F E t)) → t = 0 := by
  intro F E _ _ _ _ _ σ hcm M J hJ d b N hN
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have hcont : Continuous (gramR (AF F) σ J : (Fin 1 → Fin M → AF F ⊗[F] E) → _) :=
    (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)).2.2.2.2.2.2.2.2.2 1 M J
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_real_flow_adelic_units F E σ hcm
  have hbox := GlobalTheory.T.adelic_boxes_compact_exhaust F E σ hcm d b 1 M
  have hΩ : IsCompact (box b N 1 : Set (Fin 1 → Fin M → AF F ⊗[F] E)) := hbox.1 N 1 hN
  let φ : (Fin 1 → Fin M → AF F ⊗[F] E) → Fin 1 → Fin 1 → AF F ⊗[F] E :=
    fun Y a c => gramR (AF F) σ J Y a c
  have hφ : Continuous φ :=
    continuous_pi fun a => continuous_pi fun c => hcont.matrix_elem a c
  obtain ⟨x₀, C, hcount⟩ := GlobalTheory.T.flow_lattice_count_bounded F E σ hcm τ hτ 1 (φ '' box b N 1) (hΩ.image hφ)
  obtain ⟨x, hx⟩ : ∃ x : ℝ, -(2 * x) < x₀ :=
    ⟨|x₀| + 1, by linarith [neg_abs_le x₀, abs_nonneg x₀]⟩
  refine ⟨Real.exp (-x), Real.exp_pos _, ?_⟩
  intro t Y hY hg
  by_contra ht
  have hY' : ((τ (Multiplicative.ofAdd x) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • Y ∈ box b N 1 := by
    have h := (hbox.2.2 τ hτ N (Real.exp (-x)) x Y).2 hY
    rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
  obtain ⟨-, θ, -, hθ⟩ := hτ
  have hc := hθ x
  have hsq : ((τ (Multiplicative.ofAdd (-(-(2 * x)))) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
      ((τ (Multiplicative.ofAdd x) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) *
        ((τ (Multiplicative.ofAdd x) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) := by
    rw [← Units.val_mul, ← map_mul, ← ofAdd_add]
    congr 3
    ring
  let X₀ : {X : Fin 1 → Fin 1 → E // X ≠ 0} :=
    ⟨fun _ _ => algebraMap F E t, fun h0 =>
      ht ((algebraMap F E).injective (by simpa using congrFun (congrFun h0 0) 0))⟩
  have hmem : ((τ (Multiplicative.ofAdd (-(-(2 * x)))) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) •
      ratTup (AF F) X₀.1 ∈ φ '' box b N 1 := by
    refine ⟨_, hY', ?_⟩
    funext a c
    have h1 : gramR (AF F) σ J Y a c = inclR (AF F) (algebraMap F E t) := by rw [hg]
    simp only [φ]
    rw [hc, gramR_smul, h1, hsq, hc]
    rfl
  have hle := hcount (-(2 * x))
  rw [if_pos hx] at hle
  have h1 := (ENNReal.le_tsum X₀).trans hle
  rw [Set.indicator_of_mem hmem] at h1
  simp at h1

end GlobalTheory.CompanionTheory.SW.SmallQ
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SmallBoxGramScalarZeroStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_box_gram_scalar_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (N : ℕ), 0 < N → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ (t : F) (Y : Fin 1 → Fin M → AF F ⊗[F] E), Y ∈ box b N r₀ → (gramR (AF F) σ J Y = fun _ _ => inclR (AF F) (algebraMap F E t)) → t = 0 := by
  first | exact @GlobalTheory.CompanionTheory.SW.SmallQ.small_length | exact GlobalTheory.CompanionTheory.SW.SmallQ.small_length | (intros; apply GlobalTheory.CompanionTheory.SW.SmallQ.small_length <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaMeasureNonzeroVectorsBound
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.MeanCount

theorem box_mono {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d M n : ℕ}
    (b : Module.Basis (Fin d) F E) (N : ℕ) {r r' : ℝ} (h : r ≤ r') :
    (box b N r : Set (Fin n → Fin M → AF F ⊗[F] E)) ⊆ box b N r' :=
  fun _ hX => ⟨hX.1, hX.2.trans h⟩

theorem real_bound {C₁ C₂ x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hxy : x ≤ y) :
    C₁ * x ≤ (|C₁| + |C₂|) * (y + z) := by
  have h1 := abs_nonneg C₁
  have h2 := abs_nonneg C₂
  calc C₁ * x ≤ |C₁| * x := mul_le_mul_of_nonneg_right (le_abs_self _) hx
    _ ≤ |C₁| * y := mul_le_mul_of_nonneg_left hxy h1
    _ ≤ (|C₁| + |C₂|) * (y + z) :=
        mul_le_mul (by linarith) (by linarith) hy (by linarith)

theorem mean_count_box : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ N : ℕ, 0 < N → ∃ C : ℝ, ∀ r : ℝ, 0 < r → thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0} {X | (∀ v, (fun a i => (N : Fv F v ⊗[F] E) * projV v (projFin X) a i) ∈ latV b v) ∧ sizeTup b (projInf X) ≤ r} ≤ ENNReal.ofReal (C * (r ^ (Module.finrank ℚ F * M) + r ^ (2 * Module.finrank ℚ F * M))) := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM d b μ 𝓕 hμ h𝓕 N hN
  obtain ⟨⟨lcA, scA, t2A⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  haveI := lcA
  haveI := scA
  haveI := t2A
  obtain ⟨-, -, -, t2K, -, -, -, borelK, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)
  haveI := t2K
  haveI := borelK 1 M
  have hact := (GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ (AF F))
  have hgram : ∀ (h : HA (AF F) σ J) (X : Fin 1 → Fin M → AF F ⊗[F] E),
      gramR (AF F) σ J (actW (AF F) σ J h X) = gramR (AF F) σ J X :=
    (hact.2.2.2.2.2 1).2.2.2
  obtain ⟨hfin1, hfin2, -⟩ := GlobalTheory.T.rational_gram_adelic_compact_finite F E σ hCM M J hJ
  have h0 : μ 𝓕 ≠ 0 := ((GlobalTheory.T.haar_fundamental_domain_exists_unitary F E σ hCM M J hJ).2 μ hμ).2.2 𝓕 h𝓕
  have hc : (μ 𝓕)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 h0
  obtain ⟨r₀, hr₀, hsmall⟩ := GlobalTheory.T.small_box_gram_scalar_zero F E σ hCM M J hJ d b N hN
  have hr₁ : 0 < min r₀ 1 := lt_min hr₀ one_pos
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.T.isotropic_vector_count_box_bound F E σ hCM M J hJ hM μ 𝓕 hμ h𝓕 d b N hN
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.T.counting_vectors_bounded_large_radius F E σ hCM M J hJ hM μ 𝓕 hμ h𝓕 d b N (min r₀ 1) hN hr₁
  refine ⟨((μ 𝓕)⁻¹).toReal * (|C₁| + |C₂|), fun r hr => ?_⟩
  change thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0} (box b N r) ≤ _
  have hmeas : MeasurableSet (box b N r : Set (Fin 1 → Fin M → AF F ⊗[F] E)) :=
    ((GlobalTheory.T.adelic_boxes_compact_exhaust F E σ hCM d b 1 M).1 N r hN).measurableSet
  have hval : thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0} (box b N r) =
      (μ 𝓕)⁻¹ * cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0}
        (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) := by
    have h := GlobalTheory.T.theta_measure_integral_formula F E σ hCM M J hJ μ 𝓕 hμ h𝓕 1 {X : Fin 1 → Fin M → E | X ≠ 0}
      (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hmeas)
    rw [lintegral_indicator_const hmeas, one_mul] at h
    exact h
  have hx : 0 ≤ r ^ (Module.finrank ℚ F * M) := by positivity
  have hy : 0 ≤ r ^ (2 * Module.finrank ℚ F * M) := by positivity
  have hbound : cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0}
      (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) ≤
      ENNReal.ofReal ((|C₁| + |C₂|) * (r ^ (Module.finrank ℚ F * M) +
        r ^ (2 * Module.finrank ℚ F * M))) := by
    rcases le_total r (min r₀ 1) with hle | hle
    · have hrr₀ : r ≤ r₀ := hle.trans (min_le_left _ _)
      have hr1 : r ≤ 1 := hle.trans (min_le_right _ _)
      have hiso : ∀ (h : HA (AF F) σ J) (X : Fin 1 → Fin M → E),
          actW (AF F) σ J h⁻¹ (ratTup (AF F) X) ∈ (box b N r : Set (Fin 1 → Fin M → AF F ⊗[F] E)) →
          gramE σ J X = 0 := by
        intro h X hX
        obtain ⟨t, ht⟩ := hfin1 X
        have hY : gramR (AF F) σ J (actW (AF F) σ J h⁻¹ (ratTup (AF F) X)) =
            fun _ _ => inclR (AF F) (algebraMap F E t) := by
          rw [hgram, hfin2, ht]
          rfl
        have ht0 : t = 0 := hsmall t _ (box_mono b N hrr₀ hX) hY
        rw [ht, ht0]
        funext a c
        simp
      have heq : cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0}
            (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) =
          cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0 ∧ gramE σ J X = 0}
            (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) := by
        unfold cntI
        refine lintegral_congr fun h => ?_
        rw [tsum_subtype {X : Fin 1 → Fin M → E | X ≠ 0}
            (fun X => Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))
              (actW (AF F) σ J h⁻¹ (ratTup (AF F) X))),
          tsum_subtype {X : Fin 1 → Fin M → E | X ≠ 0 ∧ gramE σ J X = 0}
            (fun X => Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))
              (actW (AF F) σ J h⁻¹ (ratTup (AF F) X)))]
        congr 1
        funext X
        by_cases hB : actW (AF F) σ J h⁻¹ (ratTup (AF F) X) ∈
            (box b N r : Set (Fin 1 → Fin M → AF F ⊗[F] E))
        · have hg := hiso h X hB
          by_cases hX : X ≠ 0
          · rw [Set.indicator_of_mem (show X ∈ {X : Fin 1 → Fin M → E | X ≠ 0} from hX),
              Set.indicator_of_mem
                (show X ∈ {X : Fin 1 → Fin M → E | X ≠ 0 ∧ gramE σ J X = 0} from ⟨hX, hg⟩)]
          · rw [Set.indicator_of_notMem (show X ∉ {X : Fin 1 → Fin M → E | X ≠ 0} from hX),
              Set.indicator_of_notMem
                (show X ∉ {X : Fin 1 → Fin M → E | X ≠ 0 ∧ gramE σ J X = 0} from fun h' => hX h'.1)]
        · simp only [Set.indicator, hB, if_false, ite_self]
      rw [heq]
      refine (hC₁ r hr).trans (ENNReal.ofReal_le_ofReal ?_)
      have hexp : Module.finrank ℚ F * M ≤ 2 * Module.finrank ℚ F * (M - 1) := by
        have h2 : M ≤ 2 * (M - 1) := by omega
        calc Module.finrank ℚ F * M ≤ Module.finrank ℚ F * (2 * (M - 1)) :=
              Nat.mul_le_mul_left _ h2
          _ = 2 * Module.finrank ℚ F * (M - 1) := by ring
      exact real_bound (by positivity) hx hy (pow_le_pow_of_le_one hr.le hr1 hexp)
    · refine (hC₂ r hle).trans (ENNReal.ofReal_le_ofReal ?_)
      have := real_bound (C₁ := C₂) (C₂ := C₁) hy hy hx le_rfl
      rw [add_comm |C₂|, add_comm (r ^ (2 * Module.finrank ℚ F * M))] at this
      exact this
  rw [hval, mul_assoc, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hc]
  exact mul_le_mul_right hbound _

end GlobalTheory.CompanionTheory.SW.MeanCount
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaMeasureNonzeroVectorsBoundStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_measure_nonzero_vectors_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ N : ℕ, 0 < N → ∃ C : ℝ, ∀ r : ℝ, 0 < r → thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0} {X | (∀ v, (fun a i => (N : Fv F v ⊗[F] E) * projV v (projFin X) a i) ∈ latV b v) ∧ sizeTup b (projInf X) ≤ r} ≤ ENNReal.ofReal (C * (r ^ (Module.finrank ℚ F * M) + r ^ (2 * Module.finrank ℚ F * M))) := by
  first | exact @GlobalTheory.CompanionTheory.SW.MeanCount.mean_count_box | exact GlobalTheory.CompanionTheory.SW.MeanCount.mean_count_box | (intros; apply GlobalTheory.CompanionTheory.SW.MeanCount.mean_count_box <;> assumption)
end
