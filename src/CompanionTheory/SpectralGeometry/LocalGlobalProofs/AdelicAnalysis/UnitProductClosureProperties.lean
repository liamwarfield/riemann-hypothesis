module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import GroundTheory.GlobalFields.TateThesis.AdelicChar

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitProductClosureProperties
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitProductClosureProperties
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.UnitProdAlg

variable {F : Type} [Field F] [NumberField F]

theorem mulSupport_finite {a : ℝ≥0} {c : HeightOneSpectrum (𝓞 F) → ℝ≥0} (h : IsUnitProd a c) :
    (Function.mulSupport c).Finite := by
  have := h.1
  rw [Filter.eventually_cofinite] at this
  exact this

theorem map_hom (f : ℝ≥0 →* ℝ≥0) {a : ℝ≥0} {c : HeightOneSpectrum (𝓞 F) → ℝ≥0}
    (h : IsUnitProd a c) : IsUnitProd (f a) (fun v => f (c v)) := by
  have hfin := mulSupport_finite h
  refine ⟨h.1.mono fun v hv => by simp [hv], ?_⟩
  have hsub : Function.mulSupport (fun v => f (c v)) ⊆ (hfin.toFinset : Set _) := by
    intro v hv
    simp only [Function.mem_mulSupport] at hv
    simp only [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    exact hv (by simp [h1])
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub, ← map_prod, ← map_mul,
    ← finprod_eq_prod_of_mulSupport_subset c (by simp), h.2, map_one]

def sqrtHom : ℝ≥0 →* ℝ≥0 where
  toFun := NNReal.sqrt
  map_one' := NNReal.sqrt_one
  map_mul' := NNReal.sqrt_mul

theorem mul {a b : ℝ≥0} {c e : HeightOneSpectrum (𝓞 F) → ℝ≥0}
    (h : IsUnitProd a c) (k : IsUnitProd b e) : IsUnitProd (a * b) (fun v => c v * e v) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [h.1, k.1] with v h1 h2
    simp [h1, h2]
  · rw [finprod_mul_distrib (mulSupport_finite h) (mulSupport_finite k), mul_mul_mul_comm,
      h.2, k.2, one_mul]

theorem ne_zero {a : ℝ≥0} {c : HeightOneSpectrum (𝓞 F) → ℝ≥0} (h : IsUnitProd a c) : a ≠ 0 := by
  rintro rfl
  simpa using h.2

theorem family_ne_zero {a : ℝ≥0} {c : HeightOneSpectrum (𝓞 F) → ℝ≥0} (h : IsUnitProd a c)
    (v : HeightOneSpectrum (𝓞 F)) : c v ≠ 0 := by
  intro hv
  have h2 := h.2
  rw [finprod_eq_zero c v hv (mulSupport_finite h)] at h2
  simp at h2

theorem inv {a : ℝ≥0} {c : HeightOneSpectrum (𝓞 F) → ℝ≥0} (h : IsUnitProd a c) :
    IsUnitProd a⁻¹ (fun v => (c v)⁻¹) :=
  map_hom (invMonoidWithZeroHom (G₀ := ℝ≥0) : ℝ≥0 →* ℝ≥0) h

theorem main : ∀ (F : Type) [Field F] [NumberField F] (a b : ℝ≥0)
    (c e : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd a c → IsUnitProd b e →
    a ≠ 0 ∧ (∀ v, c v ≠ 0) ∧ IsUnitProd (a * b) (fun v => c v * e v) ∧
    IsUnitProd a⁻¹ (fun v => (c v)⁻¹) ∧ IsUnitProd (a / b) (fun v => c v / e v) ∧
    IsUnitProd (NNReal.sqrt a) (fun v => NNReal.sqrt (c v)) ∧
    (∀ n : ℕ, IsUnitProd (a ^ n) (fun v => c v ^ n)) ∧
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S →
      (∀ v, v ∉ S → c v = 1) ∧ a * ∏ v ∈ S, c v = 1 := by
  intro F _ _ a b c e h k
  refine ⟨ne_zero h, family_ne_zero h, mul h k, inv h, ?_, map_hom sqrtHom h,
    fun n => map_hom (powMonoidHom n) h, (mulSupport_finite h).toFinset, fun S hS => ?_⟩
  · simpa only [div_eq_mul_inv] using mul h (inv k)
  · have hsub : Function.mulSupport c ⊆ (S : Set _) := by
      intro v hv
      exact hS ((mulSupport_finite h).mem_toFinset.2 hv)
    refine ⟨fun v hv => ?_, ?_⟩
    · by_contra hne
      exact hv (hsub hne)
    · rw [← finprod_eq_prod_of_mulSupport_subset c hsub]
      exact h.2

end GlobalTheory.CompanionTheory.SW.UnitProdAlg
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitProductClosurePropertiesStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_product_closure_properties : ∀ (F : Type) [Field F] [NumberField F] (a b : ℝ≥0) (c e : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd a c → IsUnitProd b e → a ≠ 0 ∧ (∀ v, c v ≠ 0) ∧ IsUnitProd (a * b) (fun v => c v * e v) ∧ IsUnitProd a⁻¹ (fun v => (c v)⁻¹) ∧ IsUnitProd (a / b) (fun v => c v / e v) ∧ IsUnitProd (NNReal.sqrt a) (fun v => NNReal.sqrt (c v)) ∧ (∀ n : ℕ, IsUnitProd (a ^ n) (fun v => c v ^ n)) ∧ ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S → (∀ v, v ∉ S → c v = 1) ∧ a * ∏ v ∈ S, c v = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.UnitProdAlg.main | exact GlobalTheory.CompanionTheory.SW.UnitProdAlg.main | (intros; apply GlobalTheory.CompanionTheory.SW.UnitProdAlg.main <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneDetHermitianGram
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneDetHermitianGram
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.BlockAlg

section Entries

variable {K : Type} [Zero K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K)

theorem blockOne_zero_zero : blockOne t A 0 0 = t := rfl

theorem blockOne_zero_succ (j : Fin M) : blockOne t A 0 j.succ = 0 := rfl

theorem blockOne_succ_zero (i : Fin M) : blockOne t A i.succ 0 = 0 := rfl

theorem blockOne_succ_succ (i j : Fin M) : blockOne t A i.succ j.succ = A i j := rfl

end Entries

theorem det_blockOne {K : Type} [CommRing K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K) :
    (blockOne t A).det = t * A.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have h0 : (blockOne t A).submatrix Fin.succ (Fin.succAbove (0 : Fin (M + 1))) = A := by
    ext i j
    simp [blockOne_succ_succ]
  rw [h0, Finset.sum_eq_zero]
  · simp [blockOne_zero_zero]
  · intro j _
    simp [blockOne_zero_succ]

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem hE_blockOne_cons (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t a b : E)
    (x y : Fin M → E) :
    hE σ (blockOne t J) (Fin.cons a x : Fin (M + 1) → E) (Fin.cons b y : Fin (M + 1) → E) =
      σ a * t * b + hE σ J x y := by
  simp only [hE, hform, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, blockOne_zero_zero,
    blockOne_zero_succ, blockOne_succ_zero, blockOne_succ_succ]
  simp

theorem hE_zero_left (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (y : Fin M → E) :
    hE σ J 0 y = 0 := by
  simp [hE, hform]

theorem hE_zero_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin M → E) :
    hE σ J x 0 = 0 := by
  simp [hE, hform]

theorem gramE_consTup (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : E) {n : ℕ}
    (X : Fin n → Fin M → E) :
    gramE σ (blockOne t J) (consTup X) = blockOne t (gramE σ J X) := by
  have hz : (fun _ : Fin M => (0 : E)) = 0 := rfl
  ext a b
  refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b
  · change hE σ (blockOne t J) (Fin.cons 1 (fun _ => 0)) (Fin.cons 1 (fun _ => 0)) = t
    rw [hE_blockOne_cons, hz, hE_zero_left]
    simp
  · change hE σ (blockOne t J) (Fin.cons 1 (fun _ => 0)) (Fin.cons 0 (X b)) = 0
    rw [hE_blockOne_cons, hz, hE_zero_left]
    simp
  · change hE σ (blockOne t J) (Fin.cons 0 (X a)) (Fin.cons 1 (fun _ => 0)) = 0
    rw [hE_blockOne_cons, hz, hE_zero_right]
    simp
  · change hE σ (blockOne t J) (Fin.cons 0 (X a)) (Fin.cons 0 (X b)) = hE σ J (X a) (X b)
    rw [hE_blockOne_cons]
    simp

theorem exists_consTup_of_gramE (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {t : E}
    (ht : t ≠ 0) {n : ℕ} (T : Matrix (Fin n) (Fin n) E) (Y : Fin (n + 1) → Fin (M + 1) → E)
    (h0 : Y 0 = Fin.cons 1 (fun _ => 0)) (hY : gramE σ (blockOne t J) Y = blockOne t T) :
    ∃ X, gramE σ J X = T ∧ Y = consTup X := by
  have hz : (fun _ : Fin M => (0 : E)) = 0 := rfl
  have hsplit : ∀ a : Fin n, Y a.succ = Fin.cons (Y a.succ 0) (Fin.tail (Y a.succ)) := fun a =>
    (Fin.cons_self_tail _).symm
  have hfirst : ∀ a : Fin n, Y a.succ 0 = 0 := by
    intro a
    have h := congrFun (congrFun hY 0) a.succ
    change hE σ (blockOne t J) (Y 0) (Y a.succ) = blockOne t T 0 a.succ at h
    rw [h0, hsplit a, hE_blockOne_cons, hz, hE_zero_left, blockOne_zero_succ] at h
    simpa [ht] using h
  have hY' : ∀ a : Fin n, Y a.succ = Fin.cons 0 (Fin.tail (Y a.succ)) := by
    intro a
    conv_lhs => rw [hsplit a, hfirst a]
  refine ⟨fun a => Fin.tail (Y a.succ), ?_, ?_⟩
  · ext a b
    have h := congrFun (congrFun hY a.succ) b.succ
    change hE σ (blockOne t J) (Y a.succ) (Y b.succ) = blockOne t T a.succ b.succ at h
    rw [hY' a, hY' b, hE_blockOne_cons, blockOne_succ_succ] at h
    change hE σ J (Fin.tail (Y a.succ)) (Fin.tail (Y b.succ)) = T a b
    simpa using h
  · funext a
    refine Fin.cases ?_ (fun a => ?_) a
    · exact h0
    · exact hY' a

theorem block_alg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F), (blockOne (algebraMap F E t) J).det = algebraMap F E t * J.det ∧ ((∀ a b, σ (J b a) = J a b) → ∀ a b, σ (blockOne (algebraMap F E t) J b a) = blockOne (algebraMap F E t) J a b) ∧ (∀ (n : ℕ) (X : Fin n → Fin M → E), gramE σ (blockOne (algebraMap F E t) J) (consTup X) = blockOne (algebraMap F E t) (gramE σ J X)) ∧ (t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (Y : Fin (n + 1) → Fin (M + 1) → E), Y 0 = Fin.cons 1 (fun _ => 0) → gramE σ (blockOne (algebraMap F E t) J) Y = blockOne (algebraMap F E t) T → ∃ X, gramE σ J X = T ∧ Y = consTup X) := by
  intro F E _ _ _ _ _ σ _ M J t
  refine ⟨det_blockOne _ _, ?_, fun n X => gramE_consTup σ J _ X, ?_⟩
  · intro hJ a b
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b
    · simp [blockOne_zero_zero]
    · simp [blockOne_zero_succ, blockOne_succ_zero]
    · simp [blockOne_zero_succ, blockOne_succ_zero]
    · simpa [blockOne_succ_succ] using hJ a b
  · intro ht n T Y h0 hY
    have ht' : algebraMap F E t ≠ 0 := by
      simpa using ht
    exact exists_consTup_of_gramE σ J ht' T Y h0 hY

end GlobalTheory.CompanionTheory.SW.BlockAlg
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneDetHermitianGramStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_one_det_hermitian_gram : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F), (blockOne (algebraMap F E t) J).det = algebraMap F E t * J.det ∧ ((∀ a b, σ (J b a) = J a b) → ∀ a b, σ (blockOne (algebraMap F E t) J b a) = blockOne (algebraMap F E t) J a b) ∧ (∀ (n : ℕ) (X : Fin n → Fin M → E), gramE σ (blockOne (algebraMap F E t) J) (consTup X) = blockOne (algebraMap F E t) (gramE σ J X)) ∧ (t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (Y : Fin (n + 1) → Fin (M + 1) → E), Y 0 = Fin.cons 1 (fun _ => 0) → gramE σ (blockOne (algebraMap F E t) J) Y = blockOne (algebraMap F E t) T → ∃ X, gramE σ J X = T ∧ Y = consTup X) := by
  first | exact @GlobalTheory.CompanionTheory.SW.BlockAlg.block_alg | exact GlobalTheory.CompanionTheory.SW.BlockAlg.block_alg | (intros; apply GlobalTheory.CompanionTheory.SW.BlockAlg.block_alg <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorInvolutionAlgebraProperties
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorInvolutionAlgebraProperties
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.KAlg

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem exists_basis_one_delta (σ : E →ₐ[F] E) {δ : E} (hδ : σ δ = -δ) (h0 : δ ≠ 0)
    (hfr : Module.finrank F E = 2) (h2 : (2 : F) ≠ 0) :
    ∃ b : Module.Basis (Fin 2) F E, b 0 = 1 ∧ b 1 = δ := by
  have li : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : s • (1 : E) + t • (-δ) = 0 := by
      have := congrArg σ hst
      simpa [map_add (f := _), map_smul, hδ] using this
    have hs : (2 * s) • (1 : E) = 0 := by
      have : (2 * s) • (1 : E) = (s • (1 : E) + t • δ) + (s • (1 : E) + t • (-δ)) := by module
      rw [this, hst, h1, add_zero]
    have hs0 : s = 0 := by
      rcases smul_eq_zero.1 hs with h | h
      · exact (mul_eq_zero.1 h).resolve_left h2
      · exact absurd h one_ne_zero
    subst hs0
    refine ⟨rfl, ?_⟩
    rcases smul_eq_zero.1 (by simpa using hst : t • δ = 0) with h | h
    · exact h
    · exact absurd h h0
  refine ⟨basisOfLinearIndependentOfCardEqFinrank li (by simp [hfr]), ?_, ?_⟩
  · simp
  · simp

variable {R : Type} [CommRing R] [Algebra F R]

theorem exists_coord (b : Module.Basis (Fin 2) F E) {δ : E} (hb0 : b 0 = 1) (hb1 : b 1 = δ)
    (y : R ⊗[F] E) : ∃ a c : R, y = a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] δ := by
  let B := Algebra.TensorProduct.basis R b
  refine ⟨B.repr y 0, B.repr y 1, ?_⟩
  have h := (B.sum_repr y).symm
  rw [Fin.sum_univ_two] at h
  have e0 : B 0 = (1 : R) ⊗ₜ[F] (1 : E) := by simp [B, hb0]
  have e1 : B 1 = (1 : R) ⊗ₜ[F] δ := by simp [B, hb1]
  rw [e0, e1, TensorProduct.smul_tmul', TensorProduct.smul_tmul'] at h
  simpa using h

theorem coord_inj (b : Module.Basis (Fin 2) F E) {δ : E} (hb0 : b 0 = 1) (hb1 : b 1 = δ)
    {a c a' c' : R} (h : a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] δ = a' ⊗ₜ[F] (1 : E) + c' ⊗ₜ[F] δ) :
    a = a' ∧ c = c' := by
  let B := Algebra.TensorProduct.basis R b
  have e : ∀ p q : R, p ⊗ₜ[F] (1 : E) + q ⊗ₜ[F] δ = p • B 0 + q • B 1 := by
    intro p q
    have e0 : B 0 = (1 : R) ⊗ₜ[F] (1 : E) := by simp [B, hb0]
    have e1 : B 1 = (1 : R) ⊗ₜ[F] δ := by simp [B, hb1]
    rw [e0, e1, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    simp
  rw [e, e] at h
  have h0 := congrArg (fun y => B.repr y 0) h
  have h1 := congrArg (fun y => B.repr y 1) h
  simp at h0 h1
  exact ⟨h0, h1⟩

theorem tmul_one_injective (b : Module.Basis (Fin 2) F E) {δ : E} (hb0 : b 0 = 1) (hb1 : b 1 = δ) :
    Function.Injective (Algebra.TensorProduct.includeLeft : R →ₐ[F] R ⊗[F] E) := by
  intro p q h
  have h' : p ⊗ₜ[F] (1 : E) + (0 : R) ⊗ₜ[F] δ = q ⊗ₜ[F] (1 : E) + (0 : R) ⊗ₜ[F] δ := by
    simpa using h
  exact (coord_inj b hb0 hb1 h').1

end Coord

theorem algebra_tensor_invol : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [IsArtinianRing R] [IsReduced R],
    IsArtinianRing (R ⊗[F] E) ∧ IsReduced (R ⊗[F] E) ∧ IsUnit (2 : R ⊗[F] E) ∧
      (∀ y, sigR R σ (sigR R σ y) = y) ∧ (∃ δ : R ⊗[F] E, IsUnit δ ∧ sigR R σ δ = -δ) ∧
      (∀ y : R ⊗[F] E, sigR R σ y = y → ∃ r : R, y = r ⊗ₜ[F] (1 : E)) ∧
      ∀ r : R, IsUnit (r ⊗ₜ[F] (1 : E) : R ⊗[F] E) ↔ IsUnit r := by
  intro F E _ _ _ _ _ σ h R _ _ _ _
  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  have hne : ∃ x, σ x ≠ x := by
    by_contra hc
    push Not at hc
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have := h.2.1
    apply IsTotallyComplex.complexEmbedding_not_isReal τ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have h' := h.2.2.2 τ x
    rw [hc] at h'
    simpa [ComplexEmbedding.conjugate_coe_eq] using h'.symm
  obtain ⟨x₀, hx₀⟩ := hne
  set δ : E := x₀ - σ x₀ with hδdef
  have hδ : σ δ = -δ := by simp [hδdef, hσσ]
  have hδ0 : δ ≠ 0 := fun e => hx₀ (sub_eq_zero.1 e).symm
  have h2F : (2 : F) ≠ 0 := two_ne_zero
  obtain ⟨b, hb0, hb1⟩ := exists_basis_one_delta σ hδ hδ0 h.2.2.1 h2F
  have : Module.Finite F E := Module.Finite.of_basis b
  have hsig : ∀ (a : R) (e : E), sigR R σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := fun _ _ => rfl
  have h2R : IsUnit (2 : R) := by
    have := (IsUnit.mk0 (2 : F) h2F).map (algebraMap F R)
    rwa [map_ofNat] at this
  have half : ∀ a : R, a + a = 0 → a = 0 := fun a ha =>
    (h2R.mul_right_eq_zero).1 (by rw [two_mul, ha])
  have hnil : ∀ a : R, IsNilpotent (a ⊗ₜ[F] (1 : E) : R ⊗[F] E) → a = 0 := fun a ha =>
    ((IsNilpotent.map_iff (tmul_one_injective (R := R) b hb0 hb1)).1 ha).eq_zero
  have hδu : IsUnit ((1 : R) ⊗ₜ[F] δ : R ⊗[F] E) :=
    (IsUnit.mk0 δ hδ0).map (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E)
  refine ⟨IsArtinianRing.of_finite R _, ⟨fun x hx => ?_⟩, ?_, fun y => ?_, ⟨_, hδu, ?_⟩, fun y hy => ?_, fun r => ⟨?_, ?_⟩⟩
  · obtain ⟨a, c, rfl⟩ := exists_coord b hb0 hb1 x
    have hs := hx.map (sigR R σ)
    have hadd := (Commute.all _ _).isNilpotent_add hx hs
    have e1 : (a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] δ) + sigR R σ (a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] δ) =
        (a + a) ⊗ₜ[F] (1 : E) := by
      rw [map_add (f := _), hsig, hsig, map_one, hδ, TensorProduct.tmul_neg, TensorProduct.add_tmul]
      abel
    rw [e1] at hadd
    have ha : a = 0 := half a (hnil _ hadd)
    subst ha
    rw [TensorProduct.zero_tmul, zero_add] at hx ⊢
    have hm : IsNilpotent ((c ⊗ₜ[F] δ) * ((1 : R) ⊗ₜ[F] δ⁻¹) : R ⊗[F] E) :=
      (Commute.all _ _).isNilpotent_mul_right (show IsNilpotent (c ⊗ₜ[F] δ : R ⊗[F] E) from hx)
    have e2 : ((c ⊗ₜ[F] δ) * ((1 : R) ⊗ₜ[F] δ⁻¹) : R ⊗[F] E) = c ⊗ₜ[F] (1 : E) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hδ0]
    rw [e2] at hm
    rw [hnil c hm, TensorProduct.zero_tmul]
  · have := (IsUnit.mk0 (2 : F) h2F).map (algebraMap F (R ⊗[F] E))
    rwa [map_ofNat] at this
  · induction y using TensorProduct.induction_on with
    | zero => simp
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | tmul a e => rw [hsig, hsig, hσσ]
  · rw [hsig, hδ, TensorProduct.tmul_neg]
  · obtain ⟨a, c, rfl⟩ := exists_coord b hb0 hb1 y
    rw [map_add (f := _), hsig, hsig, map_one, hδ, TensorProduct.tmul_neg, ← TensorProduct.neg_tmul] at hy
    have hc := (coord_inj b hb0 hb1 hy).2
    have : c = 0 := half c (by nth_rewrite 1 [← hc]; simp)
    exact ⟨a, by rw [this, TensorProduct.zero_tmul, add_zero]⟩
  · rintro ⟨u, hu⟩
    obtain ⟨a, c, hac⟩ := exists_coord b hb0 hb1 (u⁻¹ : (R ⊗[F] E)ˣ).val
    have e : (r * a) ⊗ₜ[F] (1 : E) + (r * c) ⊗ₜ[F] δ =
        (1 : R) ⊗ₜ[F] (1 : E) + (0 : R) ⊗ₜ[F] δ := by
      have : (u : R ⊗[F] E) * (u⁻¹ : (R ⊗[F] E)ˣ).val = 1 := u.mul_inv
      rw [hu, hac, mul_add, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, one_mul, Algebra.TensorProduct.one_def] at this
      rw [this, TensorProduct.zero_tmul, add_zero]
    exact IsUnit.of_mul_eq_one a (coord_inj b hb0 hb1 e).1
  · intro hr
    exact hr.map (Algebra.TensorProduct.includeLeft : R →ₐ[F] R ⊗[F] E)

end GlobalTheory.CompanionTheory.SW.KAlg
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorInvolutionAlgebraPropertiesStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_involution_algebra_properties : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [IsArtinianRing R] [IsReduced R], IsArtinianRing (R ⊗[F] E) ∧ IsReduced (R ⊗[F] E) ∧ IsUnit (2 : R ⊗[F] E) ∧ (∀ y, sigR R σ (sigR R σ y) = y) ∧ (∃ δ : R ⊗[F] E, IsUnit δ ∧ sigR R σ δ = -δ) ∧ (∀ y : R ⊗[F] E, sigR R σ y = y → ∃ r : R, y = r ⊗ₜ[F] (1 : E)) ∧ ∀ r : R, IsUnit (r ⊗ₜ[F] (1 : E) : R ⊗[F] E) ↔ IsUnit r := by
  first | exact @GlobalTheory.CompanionTheory.SW.KAlg.algebra_tensor_invol | exact GlobalTheory.CompanionTheory.SW.KAlg.algebra_tensor_invol | (intros; apply GlobalTheory.CompanionTheory.SW.KAlg.algebra_tensor_invol <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousHermScal
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.OneHerm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_sigma {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨-, -, -, h⟩ := hσ
  let τ : E →+* ℂ := Classical.choice (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  rw [h τ, h τ, star_star]

theorem exists_basis {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) :
    ∃ bb : Module.Basis (Fin 2) F E, bb 0 = 1 ∧ σ (bb 1) = - bb 1 := by
  have hcm := hσ
  obtain ⟨-, hc, h2, h⟩ := hσ
  let τ : E →+* ℂ := Classical.choice (inferInstance : Nonempty (E →+* ℂ))
  have hnr : ∃ x : E, star (τ x) ≠ τ x := by
    by_contra hcon
    push_neg at hcon
    have hreal : NumberField.ComplexEmbedding.IsReal τ := by
      ext x
      exact hcon x
    have := hc.isComplex (NumberField.InfinitePlace.mk τ)
    rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex] at this
    exact this ⟨τ, hreal, rfl⟩
  obtain ⟨x, hx⟩ := hnr
  set δ : E := x - σ x with hδ
  have hσδ : σ δ = -δ := by
    simp [hδ, sigma_sigma hcm]
  have hδ0 : δ ≠ 0 := by
    intro h0
    apply hx
    have : τ δ = 0 := by rw [h0, map_zero]
    rw [hδ, map_sub, h τ, sub_eq_zero] at this
    exact this.symm
  have hli : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hσs : ∀ (c : F) (z : E), σ (c • z) = c • σ z := fun c z => by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgHom.commutes]
    have h' := congrArg σ hst
    simp only [map_add (f := _), hσs, map_one, hσδ, map_zero, smul_neg] at h'
    have hs2 : (s + s) • (1 : E) = 0 := by
      rw [add_smul]
      linear_combination hst + h'
    have hs : s = 0 := by
      have h3 : s + s = 0 := by simpa using hs2
      have h4 : (2 : F) * s = 0 := by rw [two_mul]; exact h3
      simpa using h4
    refine ⟨hs, ?_⟩
    rw [hs, zero_smul, zero_add] at hst
    exact (smul_eq_zero.mp hst).resolve_right hδ0
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simpa using h2.symm), ?_, ?_⟩
  · simp
  · simpa using hσδ

variable (R : Type) [CommRing R] [Algebra F R]

theorem half_add (r : R) : algebraMap F R (1 / 2) * (r + r) = r := by
  have h : r + r = algebraMap F R 2 * r := by
    rw [map_ofNat, two_mul]
  rw [h, ← mul_assoc, ← map_mul]
  norm_num

variable {R}

theorem fixed_eq {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {y : R ⊗[F] E} (hy : sigR R σ y = y) :
    ∃ r : R, y = r ⊗ₜ[F] (1 : E) := by
  obtain ⟨bb, h0, h1⟩ := exists_basis hσ
  set B := Algebra.TensorProduct.basis R bb with hB
  have hy' : y = (B.repr y 0) ⊗ₜ[F] (1 : E) + (B.repr y 1) ⊗ₜ[F] bb 1 := by
    conv_lhs => rw [← B.sum_repr y]
    simp [Fin.sum_univ_two, hB, Algebra.TensorProduct.basis_apply, h0, TensorProduct.smul_tmul']
  generalize B.repr y 0 = c0 at hy'
  generalize hc1 : B.repr y 1 = c1 at hy'
  have hs : sigR R σ y = c0 ⊗ₜ[F] (1 : E) - c1 ⊗ₜ[F] bb 1 := by
    rw [hy']
    simp [sigR, h1, TensorProduct.tmul_neg, sub_eq_add_neg]
  have hz : c1 ⊗ₜ[F] bb 1 + c1 ⊗ₜ[F] bb 1 = 0 := by
    have := hs.symm.trans hy
    rw [hy'] at this
    linear_combination (-1 : ℤ) • this
  have hr : ∀ c : R, (B.repr (c ⊗ₜ[F] bb 1)) 1 = c := by
    intro c
    simp [hB, Algebra.TensorProduct.basis_repr_tmul]
  have hc : c1 = 0 := by
    have := congrArg (fun z => B.repr z 1) hz
    simp only [map_add (f := _), Finsupp.add_apply, hr, map_zero, Finsupp.zero_apply] at this
    rw [← half_add (F := F) R c1, this, mul_zero]
  exact ⟨c0, by rw [hy', hc]; simp⟩

theorem trace_tmul_one {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (r : R) :
    Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] (1 : E)) = r + r := by
  obtain ⟨bb, -, -⟩ := exists_basis hσ
  have := Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis R bb) r
  rw [Algebra.TensorProduct.algebraMap_apply] at this
  simpa [two_smul] using this

end GlobalTheory.CompanionTheory.SW.OneHerm

namespace GlobalTheory.CompanionTheory.SW.OneHerm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Top

variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

theorem continuous_tmul_one : Continuous fun s : R => s ⊗ₜ[F] (1 : E) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R (R ⊗[F] E)
  have h := IsModuleTopology.continuous_of_linearMap (Algebra.linearMap R (R ⊗[F] E))
  convert h using 2 with s
  simp [Algebra.TensorProduct.algebraMap_apply]

theorem continuous_trace : Continuous (Algebra.trace R (R ⊗[F] E)) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  exact IsModuleTopology.continuous_of_linearMap (Algebra.trace R (R ⊗[F] E))

def hermHalf (σ : E →ₐ[F] E) (S : HermR R σ 1) : R :=
  algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0)

theorem hermScal_hermHalf {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (S : HermR R σ 1) :
    hermScal R σ (hermHalf R σ S) = S := by
  have hfix : sigR R σ ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0) = (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 :=
    S.2 0 0
  obtain ⟨r, hr⟩ := fixed_eq hσ hfix
  apply Subtype.ext
  ext a b
  have ha : a = 0 := Subsingleton.elim _ _
  have hb : b = 0 := Subsingleton.elim _ _
  subst ha hb
  change (hermHalf R σ S) ⊗ₜ[F] (1 : E) = _
  rw [hr, hermHalf, hr, trace_tmul_one hσ, half_add]

theorem hermHalf_hermScal {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (s : R) :
    hermHalf R σ (hermScal R σ s) = s := by
  change algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (s ⊗ₜ[F] (1 : E)) = s
  rw [trace_tmul_one hσ, half_add]

theorem continuous_hermScal (σ : E →ₐ[F] E) : Continuous (hermScal R σ) := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_pi fun _ => continuous_pi fun _ => continuous_tmul_one R

theorem continuous_hermHalf (σ : E →ₐ[F] E) : Continuous (hermHalf R σ) := by
  refine continuous_const.mul ((continuous_trace R).comp ?_)
  exact (continuous_apply 0).comp ((continuous_apply 0).comp continuous_subtype_val)

def hermHomeo {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) : R ≃ₜ HermR R σ 1 where
  toFun := hermScal R σ
  invFun := hermHalf R σ
  left_inv := hermHalf_hermScal R hσ
  right_inv := hermScal_hermHalf R hσ
  continuous_toFun := continuous_hermScal R σ
  continuous_invFun := continuous_hermHalf R σ

end Top

section Meas

variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]

instance : IsEmpty {p : Fin 1 × Fin 1 // p.1 < p.2} :=
  ⟨fun p => by
    have h := p.2
    rw [Subsingleton.elim p.1.1 p.1.2] at h
    exact lt_irrefl _ h⟩

theorem map_hermScal {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (lam : Measure R) [lam.IsAddHaarMeasure] :
    lam.map (hermScal R σ) = coordHerm R σ b lam 1 := by
  haveI : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  let P := {p : Fin 1 × Fin 1 // p.1 < p.2}
  let x₀ : P → R ⊗[F] E := isEmptyElim
  let ψ : HermR R σ 1 → (Fin 1 → R) × (P → R ⊗[F] E) := fun S =>
      ((fun i : Fin 1 => algebraMap F R (1 / 2) *
          Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) i i)),
        (fun p : P => (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) p.1.1 p.1.2))
  let e : R → (Fin 1 → R) × (P → R ⊗[F] E) := fun s => (fun _ => s, x₀)
  have hHs : MeasurableEmbedding (hermScal R σ) := (hermHomeo R hσ).measurableEmbedding
  have hψe : ∀ S, ψ S = e (hermHalf R σ S) := by
    intro S
    refine Prod.ext ?_ (Subsingleton.elim _ _)
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    rfl
  have hemb : MeasurableEmbedding e := by
    refine MeasurableEmbedding.of_measurable_inverse (g := fun y => y.1 0) ?_ ?_ ?_ ?_
    · exact (Measurable.of_eval fun _ => measurable_id).prodMk measurable_const
    · have : Set.range e = Set.univ := by
        refine Set.eq_univ_of_forall fun y => ⟨y.1 0, ?_⟩
        refine Prod.ext ?_ (Subsingleton.elim _ _)
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst hi
        rfl
      rw [this]
      exact MeasurableSet.univ
    · exact (measurable_pi_apply 0).comp measurable_fst
    · intro s
      rfl
  have hψ : MeasurableEmbedding ψ := by
    have : ψ = e ∘ (hermHomeo R hσ).symm := funext hψe
    rw [this]
    exact hemb.comp (hermHomeo R hσ).symm.measurableEmbedding
  have hprod : (Measure.pi fun _ : Fin 1 => lam).prod (Measure.pi fun _ : P => coordK R b lam) =
      lam.map e := by
    rw [Measure.pi_of_empty _ x₀, Measure.prod_dirac]
    have h1 : (Measure.pi fun _ : Fin 1 => lam) = lam.map (fun s _ => s) :=
      ((measurePreserving_funUnique lam (Fin 1)).symm (MeasurableEquiv.funUnique (Fin 1) R)).map_eq.symm
    have hm1 : Measurable fun (s : R) (_ : Fin 1) => s := Measurable.of_eval fun _ => measurable_id
    have hm2 : Measurable fun y : Fin 1 → R => (y, x₀) := measurable_id.prodMk measurable_const
    rw [h1, Measure.map_map hm2 hm1]
    rfl
  have hcomp : e = ψ ∘ hermScal R σ := by
    funext s
    rw [Function.comp, hψe, hermHalf_hermScal R hσ]
  have hmap : lam.map e = (lam.map (hermScal R σ)).map ψ := by
    rw [Measure.map_map hψ.measurable hHs.measurable, hcomp]
  change _ = Measure.comap ψ _
  rw [hprod, hmap, hψ.comap_map]

end Meas

end GlobalTheory.CompanionTheory.SW.OneHerm

theorem GlobalTheory.CompanionTheory.SW.hermScal_main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), IsHomeomorph (hermScal R σ) ∧ (∀ S : HermR R σ 1, hermScal R σ (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0)) = S) ∧ ∀ (lam : Measure R), lam.IsAddHaarMeasure → lam.map (hermScal R σ) = coordHerm R σ b lam 1 := by
  intro F E _ _ _ _ _ σ hσ R _ _ _ _ _ _ _ _ _ d b
  refine ⟨(GlobalTheory.CompanionTheory.SW.OneHerm.hermHomeo R hσ).isHomeomorph, GlobalTheory.CompanionTheory.SW.OneHerm.hermScal_hermHalf R hσ, ?_⟩
  intro lam hlam
  exact GlobalTheory.CompanionTheory.SW.OneHerm.map_hermScal R hσ b lam
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SelfdualMeasureTransportEquiv
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SelfdualMeasureTransportEquiv
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem selfDual_map_of_comp {V V' : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V']
    [TopologicalSpace V'] [IsTopologicalAddGroup V'] [MeasurableSpace V'] [BorelSpace V']
    (e : V ≃ₜ+ V') (μ : Measure V) (χ : V' → V' → ℂ)
    (h : SelfDual μ (fun x y => χ (e x) (e y))) : SelfDual (μ.map e) χ := by
  obtain ⟨hH, hF⟩ := h
  let eM : V ≃ᵐ V' := e.toHomeomorph.toMeasurableEquiv
  have hcoe : (eM : V → V') = e := rfl
  have hint : ∀ g : V' → ℂ, ∫ y, g y ∂(μ.map e) = ∫ x, g (e x) ∂μ := fun g => by
    rw [← hcoe]; exact integral_map_equiv eM g
  refine ⟨e.isAddHaarMeasure_map μ, fun Φ hc hs hi z => ?_⟩
  have hinner : ∀ y : V, ∫ x, Φ x * χ x (e y) ∂(μ.map e)
      = ∫ x, (Φ ∘ e) x * χ (e x) (e y) ∂μ := fun y => hint _
  have hi' : Integrable (fun y => ∫ x, (Φ ∘ e) x * χ (e x) (e y) ∂μ) μ := by
    have h1 : Integrable ((fun y => ∫ x, Φ x * χ x y ∂(μ.map e)) ∘ eM) μ :=
      (eM.measurableEmbedding.integrable_map_iff).1 (by rw [hcoe]; exact hi)
    refine h1.congr (Filter.Eventually.of_forall fun y => ?_)
    exact hinner y
  have hcs : HasCompactSupport (Φ ∘ e) :=
    hs.comp_homeomorph e.toHomeomorph
  have key := hF (Φ ∘ e) (hc.comp e.continuous) hcs hi' (e.symm z)
  rw [hint]
  simp only [hinner]
  simpa using key

theorem selfDual_transport (V V' : Type) [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V']
    [TopologicalSpace V'] [IsTopologicalAddGroup V'] [MeasurableSpace V'] [BorelSpace V']
    (e : V ≃ₜ+ V') (μ : Measure V) (χ : V' → V' → ℂ) :
    SelfDual μ (fun x y => χ (e x) (e y)) ↔ SelfDual (μ.map e) χ := by
  refine ⟨selfDual_map_of_comp e μ χ, fun h => ?_⟩
  have h2 := selfDual_map_of_comp e.symm (μ.map e) (fun x y => χ (e x) (e y)) (by simpa using h)
  have hm : (μ.map e).map e.symm = μ := by
    have m1 : Measurable (e.symm : V' → V) := e.symm.continuous.measurable
    have m2 : Measurable (e : V → V') := e.continuous.measurable
    rw [Measure.map_map m1 m2]
    have : (e.symm : V' → V) ∘ e = id := by ext x; simp
    rw [this, Measure.map_id]
  rwa [hm] at h2

end GlobalTheory.CompanionTheory.SW
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SelfdualMeasureTransportEquivStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfdual_measure_transport_equiv : ∀ (V V' : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup V'] [TopologicalSpace V'] [IsTopologicalAddGroup V'] [MeasurableSpace V'] [BorelSpace V'] (e : V ≃ₜ+ V') (μ : Measure V) (χ : V' → V' → ℂ), SelfDual μ (fun x y => χ (e x) (e y)) ↔ SelfDual (μ.map e) χ := by
  first | exact @GlobalTheory.CompanionTheory.SW.selfDual_transport | exact GlobalTheory.CompanionTheory.SW.selfDual_transport | (intros; apply GlobalTheory.CompanionTheory.SW.selfDual_transport <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SplitAnisotropic
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.AlgSplit

theorem det_blockOne {K : Type} [CommRing K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K) :
    (blockOne t A).det = t * A.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have hz : ∀ j : Fin M, blockOne t A 0 j.succ = 0 := by intro j; simp [blockOne]
  have h00 : blockOne t A 0 0 = t := by simp [blockOne]
  have h0 : (blockOne t A).submatrix Fin.succ Fin.succ = A := by
    ext i j; simp [blockOne]
  simp [hz, h00, h0]

theorem split_anisotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E), IsHermND σ J → ∀ (t : F) (x : Fin (M + 1) → E), t ≠ 0 → hE σ J x x = algebraMap F E t → ∃ (g : GL (Fin (M + 1)) E) (J₁ : Matrix (Fin M) (Fin M) E), IsHermND σ J₁ ∧ blockOne (algebraMap F E t) J₁ = cT (σ : E →+* E) (g : Matrix (Fin (M + 1)) (Fin (M + 1)) E) * J * g ∧ ∀ i, (g : Matrix (Fin (M + 1)) (Fin (M + 1)) E) i 0 = x i := by
  intro F E _ _ _ _ _ σ hCM M J hJ t x ht hx
  obtain ⟨-, -, -, hconj⟩ := hCM
  have hσ : ∀ e : E, σ (σ e) = e := by
    intro e
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hconj, hconj, star_star]
  have hherm : ∀ y z, σ (hE σ J y z) = hE σ J z y := by
    intro y z
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hE, hform, map_sum, map_mul, AlgHom.coe_toRingHom, RingHom.coe_coe, hσ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hJ.1 i j]
    ring
  set s : E := algebraMap F E t with hs
  have hs0 : s ≠ 0 := (map_ne_zero _).2 ht
  let φ : (Fin (M + 1) → E) →ₗ[E] E :=
    { toFun := fun y => hE σ J x y
      map_add' := by
        intro y z
        simp [hE, hform, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c y
        simp only [hE, hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring }
  have hφ : ∀ y, φ y = hE σ J x y := fun _ => rfl
  have hsurj : Function.Surjective φ := fun e =>
    ⟨(e / s) • x, by rw [map_smul, hφ, hx, smul_eq_mul]; field_simp⟩
  have hfr : Module.finrank E (LinearMap.ker φ) = M := by
    have h := LinearMap.finrank_range_add_finrank_ker φ
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top] at h
    simp at h
    omega
  let b := Module.finBasisOfFinrankEq E (LinearMap.ker φ) hfr
  have hb : ∀ k, hE σ J x (b k : Fin (M + 1) → E) = 0 := fun k => (b k).2
  let col : Fin (M + 1) → Fin (M + 1) → E := Fin.cons x (fun k => (b k : Fin (M + 1) → E))
  let gm : Matrix (Fin (M + 1)) (Fin (M + 1)) E := Matrix.of fun i j => col j i
  have hG : ∀ i j, (cT (σ : E →+* E) gm * J * gm) i j = hE σ J (col i) (col j) := by
    intro i j
    simp only [cT, Matrix.mul_apply, hE, hform, gm, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hdet : gm.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hsum : v 0 • x + ∑ k : Fin M, v k.succ • (b k : Fin (M + 1) → E) = 0 := by
      rw [← hv]
      ext i
      simp [gm, col, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mul_comm]
    have hv00 : v 0 = 0 := by
      have h1 := congrArg φ hsum
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_add (f := _), map_smul, map_sum, map_zero, hφ, hx, smul_eq_mul] at h1
      have h2 : ∀ k : Fin M, φ (v k.succ • (b k : Fin (M + 1) → E)) = 0 := by
        intro k
        rw [map_smul, hφ, hb, smul_zero]
      simp only [h2, Finset.sum_const_zero, add_zero] at h1
      exact (mul_eq_zero.1 h1).resolve_right hs0
    have hker : ∑ k : Fin M, v k.succ • b k = 0 := by
      apply Subtype.ext
      rw [hv00, zero_smul, zero_add] at hsum
      simpa using hsum
    have hvs := Fintype.linearIndependent_iff.1 b.linearIndependent _ hker
    apply hv0
    ext i
    refine Fin.cases hv00 hvs i
  let J₁ : Matrix (Fin M) (Fin M) E := Matrix.of fun k l =>
    hE σ J (b k : Fin (M + 1) → E) (b l : Fin (M + 1) → E)
  have hblock : blockOne s J₁ = cT (σ : E →+* E) gm * J * gm := by
    ext i j
    rw [hG]
    refine Fin.cases ?_ (fun k => ?_) i <;> refine Fin.cases ?_ (fun l => ?_) j
    · simp [blockOne, col, hx, hs]
    · simp [blockOne, col, hb]
    · have h3 : hE σ J (b k : Fin (M + 1) → E) x = 0 := by
        rw [← hherm, hb, map_zero]
      simp [blockOne, col, h3]
    · simp [blockOne, col, J₁]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero gm hdet, J₁, ⟨?_, ?_⟩, hblock, fun i => rfl⟩
  · intro k l
    exact hherm _ _
  · intro hJ0
    have h4 := congrArg Matrix.det hblock
    rw [det_blockOne, hJ0, mul_zero, Matrix.det_mul, Matrix.det_mul] at h4
    have h5 : (cT (σ : E →+* E) gm).det = σ gm.det := by
      rw [cT, Matrix.det_transpose]
      exact ((σ : E →+* E).map_det gm).symm
    rw [h5] at h4
    have h6 : σ gm.det ≠ 0 := (map_ne_zero _).2 hdet
    exact mul_ne_zero (mul_ne_zero h6 hJ.2) hdet h4.symm

end GlobalTheory.CompanionTheory.SW.AlgSplit
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsIsCharAF
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.CharEx

theorem exists_isCharAF : ∀ (F : Type) [Field F] [NumberField F], ∃ ψ, IsCharAF F ψ := by
  intro F _ _
  refine ⟨Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar F), ?_, ?_, ?_, ?_⟩
  · exact continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar (K := F))
  · intro x
    exact Circle.norm_coe _
  · intro a
    show ((GroundTheory.Global.adelicChar F _ : Circle) : ℂ) = 1
    rw [GroundTheory.Global.adelicChar_algebraMap]
    rfl
  · by_contra h
    push Not at h
    apply GroundTheory.Global.adelicChar_ne_one (K := F)
    ext x
    exact h x

end GlobalTheory.CompanionTheory.SW.CharEx
end
