module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PHermAtPlace
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PDiscreteFundamentalDomain
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StReducedBasisBound

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PComplementForm
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open GroundTheory.Automorphic Module

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

namespace ComplementForm

theorem conj_apply (h : HermitianForm F E W) (x y : W) :
    conjHom F E (h.toSesq x y) = h.toSesq y x :=
  LinearMap.isSymm_def.1 h.isSymm x y

theorem apply_w_v {h : HermitianForm F E W} {v w : W} (hp : IsHyperbolicPair h v w) :
    h.toSesq w v = 1 := by
  rw [← conj_apply h v w, hp.2.2, map_one]

def proj (h : HermitianForm F E W) (v w : W) (hp : IsHyperbolicPair h v w) :
    W →ₗ[E] hypComplement h v w :=
  LinearMap.codRestrict (hypComplement h v w)
    (LinearMap.id - (h.toSesq w).smulRight v - (h.toSesq v).smulRight w) fun x => by
      rw [mem_hypComplement]
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply, map_sub,
        map_smul, smul_eq_mul, hp.1, hp.2.1, hp.2.2, apply_w_v hp]
      constructor <;> ring

theorem proj_apply (h : HermitianForm F E W) (v w : W) (hp : IsHyperbolicPair h v w) (x : W) :
    (proj h v w hp x : W) = x - h.toSesq w x • v - h.toSesq v x • w := rfl

theorem eq_add_proj (h : HermitianForm F E W) (v w : W) (hp : IsHyperbolicPair h v w) (x : W) :
    x = h.toSesq w x • v + (proj h v w hp x : W) + h.toSesq v x • w := by
  rw [proj_apply]; abel

theorem proj_of_mem (h : HermitianForm F E W) (v w : W) (hp : IsHyperbolicPair h v w)
    (x : hypComplement h v w) : proj h v w hp x = x := by
  obtain ⟨h1, h2⟩ := mem_hypComplement.1 x.2
  ext
  rw [proj_apply, h1, h2, zero_smul, zero_smul, sub_zero, sub_zero]

def restr (h : HermitianForm F E W) (v w : W) :
    hypComplement h v w →ₛₗ[conjHom F E] hypComplement h v w →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ (conjHom F E) (RingHom.id E) (fun x y => h.toSesq x y)
    (fun _ _ _ => by simp only [Submodule.coe_add, map_add (f := _), LinearMap.add_apply])
    (fun _ _ _ => by simp only [Submodule.coe_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul])
    (fun _ _ _ => by simp only [Submodule.coe_add, map_add (f := _)])
    (fun _ _ _ => by simp only [Submodule.coe_smul, map_smul, smul_eq_mul, RingHom.id_apply])

theorem restr_apply (h : HermitianForm F E W) (v w : W) (x y : hypComplement h v w) :
    restr h v w x y = h.toSesq x y := rfl

def form (h : HermitianForm F E W) (v w : W) (hp : IsHyperbolicPair h v w) :
    HermitianForm F E (hypComplement h v w) where
  toSesq := restr h v w
  isSymm := LinearMap.isSymm_def.2 fun x y => conj_apply h x y
  nonsingular := by
    constructor
    · refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
      obtain ⟨h1, h2⟩ := mem_hypComplement.1 a.2
      have hav : h.toSesq a v = 0 := by rw [← conj_apply, h1, map_zero]
      have haw : h.toSesq a w = 0 := by rw [← conj_apply, h2, map_zero]
      have hall : h.toSesq (a : W) = 0 := by
        ext y
        have hy : h.toSesq (a : W) (proj h v w hp y) = 0 := by
          rw [← restr_apply, ha, LinearMap.zero_apply]
        rw [eq_add_proj h v w hp y, map_add (f := _), map_add (f := _), map_smul, map_smul, hav, haw, hy,
          LinearMap.zero_apply]
        simp
      have : (a : W) = 0 := h.nonsingular.1 (hall.trans (map_zero _).symm)
      exact Subtype.ext this
    · intro φ
      obtain ⟨y, hy⟩ := h.nonsingular.2 (φ ∘ₗ proj h v w hp)
      have hpv : proj h v w hp v = 0 := by
        ext; rw [proj_apply, hp.1, apply_w_v hp, one_smul, zero_smul]; simp
      have hpw : proj h v w hp w = 0 := by
        ext; rw [proj_apply, hp.2.1, hp.2.2, one_smul, zero_smul]; simp
      have hyv : h.toSesq y v = 0 := by
        rw [hy, LinearMap.comp_apply, hpv, map_zero]
      have hyw : h.toSesq y w = 0 := by
        rw [hy, LinearMap.comp_apply, hpw, map_zero]
      have hmem : y ∈ hypComplement h v w := by
        rw [mem_hypComplement, ← conj_apply h y v, ← conj_apply h y w, hyv, hyw, map_zero]
        exact ⟨rfl, rfl⟩
      refine ⟨⟨y, hmem⟩, ?_⟩
      ext z
      rw [restr_apply, hy, LinearMap.comp_apply, proj_of_mem]

end ComplementForm

theorem ComplementForm.proof (h : HermitianForm F E W) : ComplementForm.Statement h :=
  fun v w hp => ⟨ComplementForm.form h v w hp, fun _ _ => rfl⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PBoundedInverseCompact
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology
open scoped ComplexOrder

noncomputable section

namespace BoundedInverseCompact

section SlopeTestRemainingChoices

variable {ι : Type*} [Fintype ι]

theorem posDef_exists_lower {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ y : ι → ℂ, c * ‖y‖ ^ 2 ≤ (star y ⬝ᵥ (P *ᵥ y)).re := by
  set f : (ι → ℂ) → ℝ := fun y => (star y ⬝ᵥ (P *ᵥ y)).re with hf
  have hscale : ∀ (r : ℝ) (y : ι → ℂ), f (r • y) = r ^ 2 * f y := by
    intro r y
    simp only [hf, star_smul, star_trivial, mulVec_smul, dotProduct_smul, smul_dotProduct,
      Complex.smul_re]
    ring
  have hunit : ∀ y : ι → ℂ, y ≠ 0 → ‖y‖⁻¹ • y ∈ Metric.sphere (0 : ι → ℂ) 1 := by
    intro y hy
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]
  have hrecover : ∀ y : ι → ℂ, y ≠ 0 → f y = ‖y‖ ^ 2 * f (‖y‖⁻¹ • y) := by
    intro y hy
    rw [hscale, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy), one_pow,
      one_mul]
  by_cases hne : (Metric.sphere (0 : ι → ℂ) 1).Nonempty
  · have hcont : Continuous f := by simp only [hf]; fun_prop
    obtain ⟨y0, hy0, hmin⟩ :=
      (isCompact_sphere (0 : ι → ℂ) 1).exists_isMinOn hne hcont.continuousOn
    have hy0ne : y0 ≠ 0 := by
      rintro rfl
      simp at hy0
    refine ⟨f y0, by simpa [hf] using hP.re_dotProduct_pos hy0ne, fun y => ?_⟩
    by_cases hy : y = 0
    · subst hy
      simp [hf]
    · change f y0 * ‖y‖ ^ 2 ≤ f y
      rw [hrecover y hy, mul_comm]
      exact mul_le_mul_of_nonneg_left (hmin (hunit y hy)) (sq_nonneg _)
  · refine ⟨1, one_pos, fun y => ?_⟩
    by_cases hy : y = 0
    · subst hy
      simp
    · exact absurd ⟨_, hunit y hy⟩ hne


omit [Fintype ι] in
theorem norm_mul_apply_le {m κ : Type*} [Fintype κ] (A : Matrix m κ ℂ) (B : Matrix κ ι ℂ)
    (i : m) (j : ι) : ‖(A * B) i j‖ ≤ ∑ k, ‖A i k‖ * ‖B k j‖ := by
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  simp

end SlopeTestRemainingChoices

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [_root_.NumberField.IsTotallyComplex E] [Fintype ι] in
theorem exists_rightInv (v : Basis ι E W) {n : ℕ} {e : Fin n → W}
    (he : Submodule.span E (Set.range e) = ⊤) :
    ∃ c : ι → Fin n → E, ∀ w : InfinitePlace E,
      (Matrix.of fun k a => vecAt v (e a) w k) * (Matrix.of fun a i => w.embedding (c i a)) = 1 := by
  have hmem : ∀ i, ∃ c : Fin n → E, ∑ a, c a • e a = v i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun E).mp (he ▸ Submodule.mem_top)
  choose c hc using hmem
  refine ⟨c, fun w => ?_⟩
  ext k i
  have h1 : ∑ a, v.repr (e a) k * c i a = v.repr (v i) k := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hc i, map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, of_apply, vecAt, ← map_mul, ← map_sum, h1, Basis.repr_self, one_apply]
  by_cases hki : k = i
  · subst hki
    simp
  · simp [hki]

end BoundedInverseCompact

open BoundedInverseCompact

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem BoundedInverseCompact.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    BoundedInverseCompact.Statement h v := by
  intro M n e he C
  obtain ⟨c, hc⟩ := exists_rightInv v he
  choose κ hκ hκle using fun w => posDef_exists_lower (M.posDef w)
  set U : InfinitePlace E → Matrix ι (Fin n) ℂ := fun w => Matrix.of fun k a => vecAt v (e a) w k
  set R : InfinitePlace E → Matrix (Fin n) ι ℂ := fun w => Matrix.of fun a i => w.embedding (c i a)
  set H := gramAt h v
  set D : InfinitePlace E → ℝ := fun w => 1 + C ^ 2 / κ w
  set r1 : InfinitePlace E → ι → ι → ℝ := fun w _ i => ∑ a, D w * ‖R w a i‖
  set r2 : InfinitePlace E → ι → ι → ℝ :=
    fun w j i => ∑ l, (∑ k, ‖(H w)⁻¹ j k‖ * r1 w l k) * ‖H w l i‖

  have hBx : ∀ r : ι → ι → ℝ, IsCompact {A : Matrix ι ι ℂ | ∀ i j, ‖A i j‖ ≤ r i j} := by
    intro r
    have : {A : Matrix ι ι ℂ | ∀ i j, ‖A i j‖ ≤ r i j} =
        Set.pi Set.univ fun i => Set.pi Set.univ fun j => Metric.closedBall (0 : ℂ) (r i j) := by
      ext A
      constructor
      · intro hA i _ j _
        simpa using hA i j
      · intro hA i j
        simpa using hA i (Set.mem_univ _) j (Set.mem_univ _)
    rw [this]
    exact isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_closedBall _ _
  set K : InfinitePlace E → Set (GL ι ℂ) := fun w => Units.embedProduct (Matrix ι ι ℂ) ⁻¹'
    ({A | ∀ i j, ‖A i j‖ ≤ r2 w i j} ×ˢ
      (MulOpposite.unop ⁻¹' {A : Matrix ι ι ℂ | ∀ i j, ‖A i j‖ ≤ r1 w i j}))
  have hK : ∀ w, IsCompact (K w) := fun w =>
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      ((hBx _).prod (MulOpposite.opHomeomorph.isCompact_preimage.mp (hBx _)))
  set S := {g : archUnitary h v | ∀ a, M.len (invApply g (vecAt v (e a))) ≤ C}
  have hclosed : IsClosed S := by
    simp only [S, Set.ofPred_forall]
    refine isClosed_iInter fun a => isClosed_le ?_ continuous_const
    have hw : ∀ w, Continuous fun x : archUnitary h v =>
        (((x⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) := fun w =>
      Units.continuous_val.comp ((continuous_apply w).comp (continuous_subtype_val.comp continuous_inv))
    have hm : ∀ w, Continuous fun x : archUnitary h v => invApply x (vecAt v (e a)) w := fun w =>
      (hw w).matrix_mulVec continuous_const
    exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun w _ => Complex.continuous_re.comp
      ((continuous_star.comp (hm w)).dotProduct (continuous_const.matrix_mulVec (hm w))))
  rw [Subtype.isCompact_iff]
  refine (isCompact_univ_pi hK).of_isClosed_subset
    ((isClosed_archUnitary h v).isClosedEmbedding_subtypeVal.isClosedMap _ hclosed) ?_
  rintro _ ⟨g, hg, rfl⟩ w -
  set Gi : Matrix ι ι ℂ := (((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)
  set G : Matrix ι ι ℂ := (((g : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)

  have hy : ∀ a, ‖invApply g (vecAt v (e a)) w‖ ≤ D w := by
    intro a
    set y := invApply g (vecAt v (e a))
    have hnn : ∀ w', 0 ≤ (star (y w') ⬝ᵥ (M.P w' *ᵥ y w')).re := fun w' =>
      (Complex.nonneg_iff.mp ((M.posDef w').posSemidef.dotProduct_mulVec_nonneg (y w'))).1
    have h0 := Finset.sum_nonneg fun w' (_ : w' ∈ Finset.univ) => hnn w'
    have hsum : ∑ w', (star (y w') ⬝ᵥ (M.P w' *ᵥ y w')).re ≤ C ^ 2 := by
      rw [← Real.sq_sqrt h0]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (hg a) 2
    have hterm := (Finset.single_le_sum (fun w' _ => hnn w') (Finset.mem_univ w)).trans hsum
    have hk := hκle w (y w)
    have hq : ‖y w‖ ^ 2 ≤ C ^ 2 / κ w := by
      rw [le_div_iff₀ (hκ w)]
      nlinarith
    simp only [D]
    nlinarith [norm_nonneg (y w)]

  have hGiU : ∀ j a, (Gi * U w) j a = invApply g (vecAt v (e a)) w j := by
    intro j a
    simp [Gi, U, invApply, Matrix.mul_apply, mulVec, dotProduct]
  have hGi_eq : Gi = Gi * U w * R w := by
    rw [Matrix.mul_assoc, hc w, Matrix.mul_one]
  have hGi_le : ∀ j i, ‖Gi j i‖ ≤ r1 w j i := by
    intro j i
    rw [hGi_eq]
    refine (norm_mul_apply_le _ _ j i).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [hGiU]
    exact mul_le_mul_of_nonneg_right ((norm_le_pi_norm _ j).trans (hy a)) (norm_nonneg _)

  have hHdet : IsUnit (H w).det := by
    simp only [H, gramAt]
    rw [show ((gram h.toSesq v).map w.embedding).det = w.embedding (gram h.toSesq v).det from
      (RingHom.map_det w.embedding _).symm]
    exact (isUnit_det_gram h v).map w.embedding
  have hinv : Giᴴ * H w * Gi = H w := (mem_archUnitary.mp (g⁻¹).2) w
  have hGiG : Gi * G = 1 := by
    simp only [Gi, G, Subgroup.coe_inv, Pi.inv_apply]
    exact Units.inv_mul _
  have hG_eq : G = (H w)⁻¹ * Giᴴ * H w := by
    have h1 : Giᴴ * H w = H w * G := by
      calc Giᴴ * H w = Giᴴ * H w * (Gi * G) := by rw [hGiG, Matrix.mul_one]
        _ = H w * G := by rw [← Matrix.mul_assoc, hinv]
    rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hHdet, Matrix.one_mul]
  have hG_le : ∀ j i, ‖G j i‖ ≤ r2 w j i := by
    intro j i
    rw [hG_eq]
    refine (norm_mul_apply_le _ _ j i).trans
      (Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    refine (norm_mul_apply_le _ _ j l).trans
      (Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [conjTranspose_apply, norm_star]
    exact hGi_le l k
  exact ⟨hG_le, hGi_le⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PTraceHermNondegenerate
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]


omit [NumberField E] in
theorem HermitianForm.eq_zero_of_toSesq_eq_zero (h : HermitianForm F E W) {x : W}
    (hx : ∀ w, h.toSesq x w = 0) : x = 0 := by
  apply h.nonsingular.1
  rw [map_zero]
  exact LinearMap.ext hx

theorem TraceHermNondegenerate.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    TraceHermNondegenerate.Statement h v := by
  have hT := (traceForm_nondegenerate ℚ E).1
  constructor
  · intro y hy
    have key : ∀ w, h.toSesq (v.equivFun.symm y) w = 0 := by
      intro w
      apply hT
      intro a
      have := hy (v.equivFun (a • w))
      rw [traceHerm_apply, LinearEquiv.symm_apply_apply, LinearMap.map_smul, smul_eq_mul] at this
      rw [Algebra.traceForm_apply, mul_comm]
      exact this
    have h0 := HermitianForm.eq_zero_of_toSesq_eq_zero h key
    exact (map_eq_zero_iff _ v.equivFun.symm.injective).1 h0
  · intro z hz
    have key : ∀ w, h.toSesq w (v.equivFun.symm z) = 0 := by
      intro w
      apply hT
      intro a
      have := hz (v.equivFun (conj F E a • w))
      rw [traceHerm_apply, LinearEquiv.symm_apply_apply, LinearMap.map_smulₛₗ₂, smul_eq_mul] at this
      rw [Algebra.traceForm_apply, mul_comm]
      simpa [conj_conj] using this
    have key' : ∀ w, h.toSesq (v.equivFun.symm z) w = 0 := by
      intro w
      have e := (LinearMap.isSymm_def.1 h.isSymm) (v.equivFun.symm z) w
      rw [key w] at e
      exact (map_eq_zero_iff _ (conjHom F E).injective).1 e
    have h0 := HermitianForm.eq_zero_of_toSesq_eq_zero h key'
    exact (map_eq_zero_iff _ v.equivFun.symm.injective).1 h0

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PArchCovolumeBound
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module MeasureTheory

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [NumberField F] [IsTotallyReal F] [DecidableEq ι] in
theorem ArchCovolumeBound.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : CoordEmbedBasis.Statement E ι)
    (h₂ : IntegralFormCovolume.Statement (ι → E) (InfinitePlace E → ι → ℂ)
      (Σ _ : ι, Free.ChooseBasisIndex ℤ (𝓞 E)))
    (h₃ : TraceHermNondegenerate.Statement h v) (h₄ : DualLatticeMultiple.Statement h)
    (h₅ : CoordLatticeFullRank.Statement v) : ArchCovolumeBound.Statement h v := by
  intro D
  obtain ⟨k, hk0, hk⟩ := h₄ D
  let e := Pi.basis fun _ : ι => integralBasis E
  obtain ⟨C, hC⟩ := h₂ (coordEmbed E ι) e (traceHerm h v) volume (Measure.pi.isAddHaarMeasure _) h₃ h₁.1
    (by rw [h₁.2, finrank_eq_card_basis e])
  refine ⟨Real.sqrt (C * |(k : ℝ)| ^ Fintype.card (Σ _ : ι, Free.ChooseBasisIndex ℤ (𝓞 E))),
    fun La hLa => ?_⟩
  let φ : W →+ (ι → E) := (v.equivFun : W →ₗ[E] ι → E).toAddMonoidHom
  have hφ : ∀ x, v.equivFun.symm (φ x) = x := fun x => v.equivFun.symm_apply_apply x
  have hmem : ∀ y, y ∈ La.map φ ↔ v.equivFun.symm y ∈ La := by
    intro y
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rwa [hφ]
    · intro hy
      exact ⟨_, hy, v.equivFun.apply_symm_apply y⟩
  have harch : archLattice v La = AddSubgroup.toIntSubmodule ((La.map φ).map (coordEmbed E ι)) := by
    rw [archLattice, AddSubgroup.map_map]
    rfl
  obtain ⟨hfg, hspan⟩ := h₅ La hLa.isLattice
  obtain ⟨hint, hdual⟩ := hk La hLa
  obtain ⟨hD, hZ, hcov⟩ := hC (La.map φ) k hk0 hfg hspan
    (fun x hx y hy => hint _ ((hmem x).1 hx) _ ((hmem y).1 hy))
    (fun y hy => by
      rw [hmem, map_zsmul]
      refine hdual _ fun x hx => ?_
      obtain ⟨n, hn⟩ := hy (φ x) (AddSubgroup.mem_map_of_mem φ hx)
      exact ⟨n, by rw [traceHerm_apply, hφ] at hn; exact hn⟩)
  rw [harch]
  exact ⟨hD, hZ, (le_abs_self _).trans (Real.abs_le_sqrt hcov)⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PBoundedIndexSubgroupsFinite
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

theorem BoundedIndexSubgroupsFinite.proof (G : Type*) [AddCommGroup G] :
    BoundedIndexSubgroupsFinite.Statement G := by
  intro A B hB hAB C
  classical

  have : Module.Finite ℤ B :=
    Module.Finite.iff_addGroup_fg.mpr ((AddGroup.fg_iff_addSubgroup_fg B).mpr hB)
  have : Module.Finite ℤ A :=
    Module.Finite.of_injective (AddSubgroup.inclusion hAB).toIntLinearMap
      (AddSubgroup.inclusion_injective hAB)

  set n := C.factorial with hn
  let K : AddSubgroup A := (nsmulAddMonoidHom n : A →+ A).range

  have : Module.Finite ℤ (A ⧸ K) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' K).toIntLinearMap
      (QuotientAddGroup.mk'_surjective K)
  have htors : Module.IsTorsion ℤ (A ⧸ K) := by
    intro x
    refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast (Nat.factorial_pos C).ne')⟩, ?_⟩
    induction x using QuotientAddGroup.induction_on with
    | H a =>
      show (n : ℤ) • (QuotientAddGroup.mk a : A ⧸ K) = 0
      rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff, natCast_zsmul]
      exact ⟨a, rfl⟩
  have : Finite (A ⧸ K) := Module.finite_of_fg_torsion _ htors

  have hK : ∀ H ∈ {H : AddSubgroup G | H ≤ A ∧ H.relIndex A ≠ 0 ∧ H.relIndex A ≤ C},
      K ≤ H.addSubgroupOf A := by
    rintro H ⟨-, h0, hC⟩ _ ⟨a, rfl⟩
    obtain ⟨k, hk⟩ := Nat.dvd_factorial (Nat.pos_of_ne_zero h0) hC
    rw [AddSubgroup.mem_addSubgroupOf]
    show n • (a : G) ∈ H
    rw [hn, hk, mul_nsmul]
    exact H.nsmul_mem (H.nsmul_relIndex_mem a.2) k

  refine Set.Finite.of_finite_image (f := fun H : AddSubgroup G =>
    (QuotientAddGroup.mk '' ((H.addSubgroupOf A : AddSubgroup A) : Set A) : Set (A ⧸ K)))
    (Set.toFinite _) ?_
  have key : ∀ H₁ ∈ {H : AddSubgroup G | H ≤ A ∧ H.relIndex A ≠ 0 ∧ H.relIndex A ≤ C},
      ∀ H₂ ∈ {H : AddSubgroup G | H ≤ A ∧ H.relIndex A ≠ 0 ∧ H.relIndex A ≤ C},
      (QuotientAddGroup.mk '' ((H₁.addSubgroupOf A : AddSubgroup A) : Set A) : Set (A ⧸ K)) =
        QuotientAddGroup.mk '' ((H₂.addSubgroupOf A : AddSubgroup A) : Set A) → H₁ ≤ H₂ := by
    intro H₁ h₁ H₂ h₂ he x hx
    have hxA : x ∈ A := h₁.1 hx
    have hmem : (QuotientAddGroup.mk (⟨x, hxA⟩ : A) : A ⧸ K) ∈
        QuotientAddGroup.mk '' ((H₁.addSubgroupOf A : AddSubgroup A) : Set A) :=
      ⟨⟨x, hxA⟩, AddSubgroup.mem_addSubgroupOf.mpr hx, rfl⟩
    rw [he] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    have hd : -y + ⟨x, hxA⟩ ∈ H₂.addSubgroupOf A := hK H₂ h₂ (QuotientAddGroup.eq.mp hyx)
    have : (⟨x, hxA⟩ : A) ∈ H₂.addSubgroupOf A := by
      simpa using (H₂.addSubgroupOf A).add_mem hy hd
    exact AddSubgroup.mem_addSubgroupOf.mp this
  exact fun H₁ h₁ H₂ h₂ he => le_antisymm (key H₁ h₁ H₂ h₂ he) (key H₂ h₂ H₁ h₁ he.symm)

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PDualLatticeMultiple
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

theorem inverseDifferent_multiple (E : Type*) [Field E] [NumberField E] :
    ∃ δ : ℤ, δ ≠ 0 ∧ ∀ z : E, (∀ a : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E ((a : E) * z) = n) →
      IsIntegral ℤ ((δ : E) * z) := by
  classical
  set b := integralBasis E
  set bd := (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) b
  obtain ⟨δ, hδ, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image bd)
  refine ⟨δ, hδ, fun z hz => ?_⟩
  have hsum := bd.sum_repr z
  have key : (δ : E) * z = ∑ i, (bd.repr z i) • ((δ : E) * bd i) := by
    conv_lhs => rw [← hsum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def]; ring
  rw [key]
  refine IsIntegral.sum _ fun i _ => ?_
  obtain ⟨n, hn⟩ := hz (RingOfIntegers.basis E i)
  have hr : bd.repr z i = (n : ℚ) := by
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, integralBasis_apply,
      mul_comm, hn]
  rw [hr, show ((n : ℚ) • ((δ : E) * bd i)) = (n : ℤ) • ((δ : E) * bd i) by
    rw [← Int.cast_smul_eq_zsmul ℚ]]
  refine IsIntegral.smul _ ?_
  have := hint (bd i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rwa [zsmul_eq_mul] at this

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

theorem DualLatticeMultiple.proof (h : HermitianForm F E W) : DualLatticeMultiple.Statement h := by
  intro D
  obtain ⟨δ, hδ, hdiff⟩ := inverseDifferent_multiple E
  refine ⟨δ * (D.factorial : ℤ), mul_ne_zero hδ (by exact_mod_cast D.factorial_ne_zero),
    fun La hLa => ⟨fun x hx y hy => ?_, fun y hy => ?_⟩⟩
  · have hi : IsIntegral ℤ (Algebra.trace ℚ E (h.toSesq x y)) :=
      Algebra.isIntegral_trace ((mem_integralClosure_iff ℤ E).mp (hLa.integral x hx y hy))
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
    exact ⟨n, by rw [← hn]; simp⟩
  ·
    have hdual : δ • y ∈ dualLattice h La := by
      intro x hx
      rw [map_zsmul, LinearMap.smul_apply, zsmul_eq_mul]
      refine (mem_integralClosure_iff ℤ E).mpr (hdiff _ fun a => ?_)
      obtain ⟨n, hn⟩ := hy _ (hLa.isLattice.smul_mem a x hx)
      exact ⟨n, by rw [← hn, LinearMap.map_smul, smul_eq_mul]⟩

    have hm := AddSubgroup.nsmul_relIndex_mem La hdual
    obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.pos_of_ne_zero hLa.index_ne_zero) hLa.index_le
    have : (D.factorial : ℤ) • (δ • y) ∈ La := by
      rw [hc, natCast_zsmul, mul_comm, mul_nsmul]
      rw [smul_comm]
      exact AddSubgroup.nsmul_mem _ hm _
    rwa [smul_smul, mul_comm] at this

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLenCauchySchwarz
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix
open scoped ComplexOrder

theorem majorant_cauchySchwarz {ι : Type*} [Fintype ι] [DecidableEq ι] {H P : Matrix ι ι ℂ}
    (hM : IsMajorantOf H P) (a b : ι → ℂ) :
    ‖star a ⬝ᵥ (H *ᵥ b)‖ ≤
      Real.sqrt (star a ⬝ᵥ (P *ᵥ a)).re * Real.sqrt (star b ⬝ᵥ (P *ᵥ b)).re := by
  have key := majorant_mul_inv_mul hM
  obtain ⟨hP, hH, hdet, hPHP⟩ := hM
  have hPdet : IsUnit P.det := isUnit_iff_ne_zero.mpr (ne_of_gt hP.det_pos)
  set c := P⁻¹ *ᵥ (H *ᵥ b) with hc
  have h1 : P *ᵥ c = H *ᵥ b := by
    rw [hc, mulVec_mulVec, Matrix.mul_nonsing_inv _ hPdet, one_mulVec]
  have hPinv : (P⁻¹)ᴴ = P⁻¹ := by rw [conjTranspose_nonsing_inv, hP.1.eq]
  have h2 : star c ⬝ᵥ (P *ᵥ c) = star b ⬝ᵥ (P *ᵥ b) := by
    rw [h1, hc, star_mulVec, star_mulVec, hPinv, hH.eq, vecMul_vecMul, ← dotProduct_mulVec,
      mulVec_mulVec, key]
  let _ := P.toSeminormedAddCommGroup hP.posSemidef
  let _ := P.toInnerProductSpace hP.posSemidef
  have cs := inner_mul_inner_self_le (𝕜 := ℂ) a c
  have e1 : (inner ℂ a c : ℂ) = star a ⬝ᵥ (H *ᵥ b) := by
    change (P *ᵥ c) ⬝ᵥ star a = _
    rw [dotProduct_comm, h1]
  have e2 : (inner ℂ c a : ℂ) = star (star a ⬝ᵥ (H *ᵥ b)) := by
    rw [← e1]; exact (inner_conj_symm (𝕜 := ℂ) c a).symm
  have e3 : (inner ℂ a a : ℂ) = star a ⬝ᵥ (P *ᵥ a) := by
    change (P *ᵥ a) ⬝ᵥ star a = _
    rw [dotProduct_comm]
  have e4 : (inner ℂ c c : ℂ) = star b ⬝ᵥ (P *ᵥ b) := by
    change (P *ᵥ c) ⬝ᵥ star c = _
    rw [dotProduct_comm, h2]
  rw [e1, e2, e3, e4, norm_star] at cs
  simp only [RCLike.re_to_complex] at cs
  have ha : 0 ≤ (star a ⬝ᵥ (P *ᵥ a)).re := hP.posSemidef.re_dotProduct_nonneg a
  have hb : 0 ≤ (star b ⬝ᵥ (P *ᵥ b)).re := hP.posSemidef.re_dotProduct_nonneg b
  rw [← Real.sqrt_mul ha]
  exact Real.le_sqrt_of_sq_le (by nlinarith)

section Places

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Majorant.isMajorantOf {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (w : InfinitePlace E) : IsMajorantOf (gramAt h v w) (M.P w) :=
  ⟨M.posDef w, (GramAtData.proof h v w).1, (GramAtData.proof h v w).2, M.siegel w⟩


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem Majorant.sqrt_le_len {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (y : InfinitePlace E → ι → ℂ) (w : InfinitePlace E) :
    Real.sqrt (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re ≤ M.len y := by
  unfold Majorant.len
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun w => (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re)
    (fun u _ => LenSq.re_nonneg (M.posDef u) (y u)) (Finset.mem_univ w))

theorem LenCauchySchwarz.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    LenCauchySchwarz.Statement h v := by
  intro M g x y w
  rw [HermAtPlace.proof h v w x y, ← ArchInvariant.proof h v g (vecAt v x) (vecAt v y) w]
  refine (majorant_cauchySchwarz (M.isMajorantOf w) _ _).trans ?_
  exact mul_le_mul (M.sqrt_le_len _ w) (M.sqrt_le_len _ w) (Real.sqrt_nonneg _)
    ((Real.sqrt_nonneg _).trans (M.sqrt_le_len _ w))

end Places

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PGramDetermines
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W]

namespace GramDetermines


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem sesq_linearCombination (h : HermitianForm F E W) {n : ℕ} {e e' : Fin n → W}
    (hG : ∀ a b, h.toSesq (e a) (e b) = h.toSesq (e' a) (e' b)) (c d : Fin n → E) :
    h.toSesq (Fintype.linearCombination E e' c) (Fintype.linearCombination E e' d) =
      h.toSesq (Fintype.linearCombination E e c) (Fintype.linearCombination E e d) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Fintype.linearCombination_apply, map_sum, LinearMap.sum_apply, map_smulₛₗ,
    LinearMap.smul_apply, hG]


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem linearCombination_surjective {n : ℕ} {e : Fin n → W}
    (hL : IsLattice E (AddSubgroup.closure (Set.range e))) :
    Function.Surjective (Fintype.linearCombination E e) := by
  have hle : AddSubgroup.closure (Set.range e) ≤
      (LinearMap.range (Fintype.linearCombination E e)).toAddSubgroup := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨a, rfl⟩
    exact ⟨Pi.single a 1, by simp⟩
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hL.span_eq_top, Submodule.span_le]
  intro x hx
  exact hle hx


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem linearCombination_eq_zero (h : HermitianForm F E W) {n : ℕ} {e e' : Fin n → W}
    (hL' : IsLattice E (AddSubgroup.closure (Set.range e')))
    (hG : ∀ a b, h.toSesq (e a) (e b) = h.toSesq (e' a) (e' b)) (c : Fin n → E)
    (hc : Fintype.linearCombination E e c = 0) : Fintype.linearCombination E e' c = 0 := by
  apply h.nonsingular.1
  refine LinearMap.ext fun y => ?_
  obtain ⟨d, rfl⟩ := linearCombination_surjective hL' y
  rw [sesq_linearCombination h hG, hc, map_zero, LinearMap.zero_apply, LinearMap.zero_apply]

theorem proof (h : HermitianForm F E W) : GramDetermines.Statement h := by
  intro n e e' hL hL' hG
  have hG' : ∀ a b, h.toSesq (e' a) (e' b) = h.toSesq (e a) (e b) := fun a b => (hG a b).symm
  have hs := linearCombination_surjective hL
  have hs' := linearCombination_surjective hL'
  have hker : LinearMap.ker (Fintype.linearCombination E e) =
      LinearMap.ker (Fintype.linearCombination E e') := by
    ext c
    simp only [LinearMap.mem_ker]
    exact ⟨linearCombination_eq_zero h hL' hG c, linearCombination_eq_zero h hL hG' c⟩
  let γ : W ≃ₗ[E] W := ((Fintype.linearCombination E e).quotKerEquivOfSurjective hs).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans
      ((Fintype.linearCombination E e').quotKerEquivOfSurjective hs'))
  have hγ : ∀ c, γ (Fintype.linearCombination E e c) = Fintype.linearCombination E e' c :=
    fun c => by simp [γ, Submodule.quotEquivOfEq_mk]
  refine ⟨⟨γ, fun x y => ?_⟩, fun a => ?_⟩
  · obtain ⟨c, rfl⟩ := hs x
    obtain ⟨d, rfl⟩ := hs y
    rw [hγ, hγ]
    exact sesq_linearCombination h hG c d
  · simpa using hγ (Pi.single a 1)

end GramDetermines

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PBoundedGenerators
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem BoundedGenerators.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (hR : ReducedBasisBound.Statement) (hA : ArchCovolumeBound.Statement h v)
    (hT : MajorantTransport.Statement h v) : BoundedGenerators.Statement h v := by
  intro M D t ht
  obtain ⟨c, hc⟩ := hA D
  obtain ⟨d, κ, hκ⟩ := hT M
  obtain ⟨C, hC⟩ := hR d t (|κ| * c) ht
  refine ⟨d, C, fun La g hLa hmin => ?_⟩
  obtain ⟨_, _, hcov⟩ := hc La hLa
  obtain ⟨T, hTn, hTc⟩ := hκ g

  let Φ : W →+ EuclideanSpace ℝ (Fin d) :=
    ((T : (InfinitePlace E → ι → ℂ) →L[ℝ] EuclideanSpace ℝ (Fin d)) : _ →ₗ[ℝ] _).toAddMonoidHom.comp
      (vecAtHom v)
  have hΦ : ∀ x, Φ x = T (vecAt v x) := fun x => rfl
  have hvec : Function.Injective (vecAt v) := by
    intro x y hxy
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
    apply v.repr.injective
    ext i
    exact w.embedding.injective (congrFun (congrFun hxy w) i)
  have hΦinj : Function.Injective Φ := T.injective.comp hvec
  let L := ZLattice.comap ℝ (archLattice v La) T.symm.toLinearMap
  have hmemL : ∀ z, z ∈ L ↔ ∃ x ∈ La, Φ x = z := by
    intro z
    rw [← SetLike.mem_coe, ZLattice.coe_comap, Set.mem_preimage, SetLike.mem_coe, mem_archLattice]
    refine exists_congr fun x => and_congr_right fun _ => ?_
    rw [hΦ]
    constructor
    · intro hx; rw [hx]; simp
    · intro hx; rw [← hx]; simp
  have hLmin : ∀ z ∈ L, z ≠ 0 → t ≤ ‖z‖ := by
    intro z hz hz0
    obtain ⟨x, hx, rfl⟩ := (hmemL z).1 hz
    have hx0 : x ≠ 0 := by rintro rfl; exact hz0 (map_zero Φ)
    rw [hΦ, hTn]
    exact hmin x hx hx0
  have hLcov : ZLattice.covolume L ≤ |κ| * c := by
    rw [hTc]
    have h0 : 0 ≤ ZLattice.covolume (archLattice v La) := ENNReal.toReal_nonneg
    exact (mul_le_mul_of_nonneg_right (le_abs_self κ) h0).trans
      (mul_le_mul_of_nonneg_left hcov (abs_nonneg κ))
  obtain ⟨b, hb⟩ := hC L hLmin hLcov
  choose e he heb using fun i => (hmemL (b i)).1 (b i).2
  refine ⟨e, le_antisymm ((AddSubgroup.closure_le La).2 (Set.range_subset_iff.2 he)) ?_,
    fun i => ?_⟩
  · intro x hx
    have hxL : Φ x ∈ L := (hmemL _).2 ⟨x, hx, rfl⟩
    have hsum := congrArg Subtype.val (b.sum_repr ⟨Φ x, hxL⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
    set r := b.repr ⟨Φ x, hxL⟩
    have hx' : x = ∑ i, r i • e i := by
      apply hΦinj
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hsum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, heb i]
    rw [hx']
    exact AddSubgroup.sum_mem _ fun i _ =>
      AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i)) _
  · rw [← hTn, ← hΦ, heb i]
    exact hb i

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
