module

public import ReciprocityTheory.SemistableReduction.HeightLowerBound

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.OrthogonalProjectorMulVecConjugate
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.OrthogonalProjectorMulVecSmul
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.OrthogonalProjectorMulEmbeddingColumns
namespace ReciprocityTheory.ChartRestriction.G.T0

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

section Proj

variable {K : Type} [Field K] {r k : ℕ}

noncomputable def hBm (σ : K →+* ℂ) (b : Fin k → Fin r → K) : Matrix (Fin r) (Fin k) ℂ :=
  Matrix.of fun l j => σ (b j l)

noncomputable def hPm (σ : K →+* ℂ) (b : Fin k → Fin r → K) : Matrix (Fin r) (Fin r) ℂ :=
  1 - hBm σ b * ((hBm σ b)ᴴ * hBm σ b)⁻¹ * (hBm σ b)ᴴ

noncomputable def hns {r : ℕ} (x : Fin r → ℂ) : ℝ := ∑ i, ‖x i‖ ^ 2

private theorem linearIndependent_map_ringHom_complex' (σ : K →+* ℂ) {s : Type*} [Fintype s] {v : s → Fin r → K}
    (hv : LinearIndependent K v) : LinearIndependent ℂ (fun i => fun l => σ (v i l)) := by
  classical
  let A : Matrix (Fin r) s K := Matrix.of fun l i => v i l
  have hAv : ∀ t : s → K, A *ᵥ t = ∑ i, t i • v i := by
    intro t
    funext l
    simp [A, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hker : LinearMap.ker A.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro t ht
    have h1 : ∑ i, t i • v i = 0 := by rw [← hAv]; exact ht
    funext i
    exact Fintype.linearIndependent_iff.mp hv t h1 i
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective A.mulVecLin hker
  have hLA : LinearMap.toMatrix' g * A = 1 := by
    have e : LinearMap.toMatrix' A.mulVecLin = A := LinearMap.toMatrix'_toLin' A
    have := congrArg LinearMap.toMatrix' hg
    simp only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at this
    rwa [e] at this
  have hLAσ : (LinearMap.toMatrix' g).map σ * A.map σ = 1 := by
    rw [← Matrix.map_mul, hLA]
    exact Matrix.map_one σ (map_zero σ) (map_one σ)
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hAc : A.map σ *ᵥ c = 0 := by
    rw [← hc]
    funext l
    simp [A, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hc0 : c = 0 := by
    calc c = ((LinearMap.toMatrix' g).map σ * A.map σ) *ᵥ c := by rw [hLAσ, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, hAc, Matrix.mulVec_zero]
  intro i
  rw [hc0]
  rfl

theorem linearIndependent_map_embedding (σ : K →+* ℂ) {ι : Type*} {v : ι → Fin r → K}
    (hv : LinearIndependent K v) : LinearIndependent ℂ (fun i => fun l => σ (v i l)) := by
  classical
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  exact linearIndependent_map_ringHom_complex' σ (hv.comp (Subtype.val : s → ι) Subtype.val_injective)

theorem embeddingColumns_mulVec (σ : K →+* ℂ) (b : Fin k → Fin r → K) (z : Fin k → ℂ) :
    hBm σ b *ᵥ z = ∑ j, z j • fun l => σ (b j l) := by
  funext l
  simp [hBm, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem isUnit_det_embeddingGram (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b) :
    IsUnit ((hBm σ b)ᴴ * hBm σ b).det := by
  have hli := linearIndependent_map_embedding σ hb
  have hinj : Function.Injective (hBm σ b).mulVec := by
    intro x y hxy
    have h1 : ∑ j, (x - y) j • (fun l => σ (b j l)) = 0 := by
      rw [← embeddingColumns_mulVec, Matrix.mulVec_sub, hxy, sub_self]
    have h2 := Fintype.linearIndependent_iff.mp hli (x - y) h1
    funext j
    exact sub_eq_zero.mp (h2 j)
  have hker : LinearMap.ker ((hBm σ b)ᴴ * hBm σ b).mulVecLin = ⊥ := by
    rw [Matrix.ker_mulVecLin_conjTranspose_mul_self, LinearMap.ker_eq_bot]
    exact hinj
  have hinj2 : Function.Injective ((hBm σ b)ᴴ * hBm σ b).mulVec := LinearMap.ker_eq_bot.mp hker
  exact (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hinj2)

theorem conjTranspose_mul_orthogonalProjector (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b) :
    (hBm σ b)ᴴ * hPm σ b = 0 := by
  have hG := isUnit_det_embeddingGram σ hb
  unfold hPm
  simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv _ hG, Matrix.one_mul, sub_self]

theorem orthogonalProjector_mul_embeddingColumns (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b) :
    hPm σ b * hBm σ b = 0 := by
  have hG := isUnit_det_embeddingGram σ hb
  unfold hPm
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul _ hG, Matrix.mul_one, sub_self]

theorem orthogonalProjector_conjTranspose (σ : K →+* ℂ) (b : Fin k → Fin r → K) : (hPm σ b)ᴴ = hPm σ b := by
  simp only [hPm, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]

theorem orthogonalProjector_mul_self (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b) :
    hPm σ b * hPm σ b = hPm σ b := by
  have h := conjTranspose_mul_orthogonalProjector σ hb
  calc hPm σ b * hPm σ b
      = (1 - hBm σ b * ((hBm σ b)ᴴ * hBm σ b)⁻¹ * (hBm σ b)ᴴ) * hPm σ b := rfl
    _ = hPm σ b - hBm σ b * ((hBm σ b)ᴴ * hBm σ b)⁻¹ * ((hBm σ b)ᴴ * hPm σ b) := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
    _ = hPm σ b := by rw [h, Matrix.mul_zero, sub_zero]

theorem orthogonalProjector_orthogonal (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (v : Fin r → ℂ) (y : Fin k → ℂ) : star (hPm σ b *ᵥ v) ⬝ᵥ (hBm σ b *ᵥ y) = 0 := by
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, orthogonalProjector_conjTranspose,
    orthogonalProjector_mul_embeddingColumns σ hb, Matrix.vecMul_zero, zero_dotProduct]

theorem normSqSum_add_of_orthogonal {r : ℕ} (a c : Fin r → ℂ) (h : star a ⬝ᵥ c = 0) :
    hns (a + c) = hns a + hns c := by
  unfold hns
  have h' : ∑ i, (a i * (starRingEnd ℂ) (c i)).re = 0 := by
    have h1 : ∑ i, a i * (starRingEnd ℂ) (c i) = (starRingEnd ℂ) (star a ⬝ᵥ c) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [dotProduct, map_sum, map_mul, Pi.star_apply, Complex.star_def, Complex.conj_conj]
    rw [← Complex.re_sum, h1, h, map_zero, Complex.zero_re]
  simp only [Pi.add_apply, ← Complex.normSq_eq_norm_sq, Complex.normSq_add, Finset.sum_add_distrib,
    ← Finset.mul_sum, h', mul_zero, add_zero]

theorem orthogonalProjector_mulVec_ne_zero (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    {q : Fin r → K} (hq : q ∉ Submodule.span K (Set.range b)) :
    hPm σ b *ᵥ (fun i => σ (q i)) ≠ 0 := by
  intro h0
  have hli := linearIndependent_map_embedding σ ((linearIndependent_finCons).mpr ⟨hb, hq⟩)
  have hcons : (fun i l => σ ((Fin.cons q b : Fin (k + 1) → Fin r → K) i l)) =
      (Fin.cons (fun l => σ (q l)) (fun j l => σ (b j l)) : Fin (k + 1) → Fin r → ℂ) := by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp
  rw [hcons, linearIndependent_finCons] at hli
  apply hli.2
  have hv : (fun i => σ (q i)) =
      (hBm σ b * ((hBm σ b)ᴴ * hBm σ b)⁻¹ * (hBm σ b)ᴴ) *ᵥ fun i => σ (q i) := by
    unfold hPm at h0
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
    exact h0
  have hv2 : (fun i => σ (q i)) =
      hBm σ b *ᵥ (((hBm σ b)ᴴ * hBm σ b)⁻¹ *ᵥ ((hBm σ b)ᴴ *ᵥ fun i => σ (q i))) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    exact hv
  rw [hv2, embeddingColumns_mulVec]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem orthogonalProjector_mulVec_eq_zero (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    {q : Fin r → K} (hq : q ∈ Submodule.span K (Set.range b)) :
    hPm σ b *ᵥ (fun i => σ (q i)) = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hq
  have h1 : (fun i => σ ((∑ j, c j • b j) i)) = hBm σ b *ᵥ fun j => σ (c j) := by
    rw [embeddingColumns_mulVec]
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Finset.sum_apply, map_sum, map_mul]
  rw [h1, Matrix.mulVec_mulVec, orthogonalProjector_mul_embeddingColumns σ hb, Matrix.zero_mulVec]

end Proj

section PT

variable {K : Type} [Field K] [NumberField K] {r k : ℕ}

theorem crossGram_eq_embeddingColumns (σ : K →+* ℂ) {m : ℕ} (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) :
    ReciprocityTheory.MultiplicativeHeights.gramX 1 σ b c = (hBm σ b)ᴴ * hBm σ c := by
  ext i j
  simp [ReciprocityTheory.MultiplicativeHeights.gramX, ReciprocityTheory.MultiplicativeHeights.embVec, hBm, Matrix.mul_apply, dotProduct,
    Matrix.conjTranspose_apply]

theorem gramMatrix_eq_embeddingColumns (σ : K →+* ℂ) (b : Fin k → Fin r → K) :
    ReciprocityTheory.MultiplicativeHeights.gramC 1 σ b = (hBm σ b)ᴴ * hBm σ b := by
  ext i j
  simp [ReciprocityTheory.MultiplicativeHeights.gramC, ReciprocityTheory.MultiplicativeHeights.embVec, hBm, Matrix.mul_apply, dotProduct,
    Matrix.conjTranspose_apply]

theorem quotientGram_eq_projector (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    {m : ℕ} (c : Fin m → Fin r → K) (i j : Fin m) :
    ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c i j =
      star (hPm σ b *ᵥ fun l => σ (c i l)) ⬝ᵥ (hPm σ b *ᵥ fun l => σ (c j l)) := by
  have key : ∀ (M : Matrix (Fin r) (Fin r) ℂ) (C : Matrix (Fin r) (Fin m) ℂ) (i j : Fin m),
      (Cᴴ * M * C) i j = star (fun l => C l i) ⬝ᵥ (M *ᵥ fun l => C l j) := by
    intro M C i j
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Pi.star_apply,
      Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  have hq : ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c = (hBm σ c)ᴴ * hPm σ b * hBm σ c := by
    unfold ReciprocityTheory.MultiplicativeHeights.quotGramC
    rw [gramMatrix_eq_embeddingColumns, gramMatrix_eq_embeddingColumns, crossGram_eq_embeddingColumns, crossGram_eq_embeddingColumns]
    unfold hPm
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [hq, key, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, orthogonalProjector_conjTranspose,
    orthogonalProjector_mul_self σ hb]
  rfl

end PT

end ReciprocityTheory.ChartRestriction.G.T0
end

namespace ReciprocityTheory.ChartRestriction.G.T0

open Matrix NumberField ComplexConjugate NumberField.ComplexEmbedding
open scoped ComplexOrder

section Real

variable {K : Type} [Field K] [NumberField K] {r k : ℕ}

abbrev hIdx (K : Type) [Field K] [NumberField K] (r : ℕ) : Type := (K →+* ℂ) × Fin r × Fin 2

noncomputable def hReF (x : (K →+* ℂ) → Fin r → ℂ) : hIdx K r → ℝ :=
  fun p => if p.2.2 = 0 then (x p.1 p.2.1).re else (x p.1 p.2.1).im

noncomputable def hRe (x : (K →+* ℂ) → Fin r → ℂ) : EuclideanSpace ℝ (hIdx K r) :=
  WithLp.toLp 2 (hReF x)

theorem realCoordsFun_add (x y : (K →+* ℂ) → Fin r → ℂ) : hReF (x + y) = hReF x + hReF y := by
  funext p
  simp only [hReF, Pi.add_apply]
  split_ifs <;> simp

theorem inner_hRe (x y : (K →+* ℂ) → Fin r → ℂ) :
    inner ℝ (hRe x) (hRe y) = (∑ σ, star (x σ) ⬝ᵥ y σ).re := by
  simp only [hRe, PiLp.inner_apply, PiLp.toLp_apply, RCLike.inner_apply, conj_trivial,
    Fintype.sum_prod_type, Fin.sum_univ_two, Complex.re_sum, dotProduct, Pi.star_apply,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, hReF]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun l _ => ?_
  simp
  ring

theorem star_dotProduct_self_re {r : ℕ} (v : Fin r → ℂ) : (star v ⬝ᵥ v).re = hns v := by
  simp only [dotProduct, Complex.re_sum, hns, Pi.star_apply, Complex.star_def]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem norm_realCoords_sq (x : (K →+* ℂ) → Fin r → ℂ) : ‖hRe x‖ ^ 2 = ∑ σ, hns (x σ) := by
  rw [← real_inner_self_eq_norm_sq, inner_hRe, Complex.re_sum]
  exact Finset.sum_congr rfl fun σ _ => star_dotProduct_self_re _

noncomputable def hpv (b : Fin k → Fin r → K) (q : Fin r → K) : EuclideanSpace ℝ (hIdx K r) :=
  hRe fun σ => hPm σ b *ᵥ fun l => σ (q l)

theorem projectedVector_add (b : Fin k → Fin r → K) (q q' : Fin r → K) :
    hpv b (q + q') = hpv b q + hpv b q' := by
  have e : (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ ((q + q') l)) =
      (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ (q l)) +
        (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ (q' l)) := by
    funext σ
    rw [Pi.add_apply, ← mulVec_add]
    congr 1
    funext l
    simp [map_add]
  simp only [hpv, hRe, e, realCoordsFun_add, WithLp.toLp_add]

theorem projectedVector_zero (b : Fin k → Fin r → K) : hpv b 0 = 0 := by
  have e : hReF (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ ((0 : Fin r → K) l)) = 0 := by
    funext p
    simp only [hReF, Pi.zero_apply, map_zero]
    rw [show (fun _ : Fin r => (0 : ℂ)) = 0 from rfl, mulVec_zero]
    split_ifs <;> simp
  simp only [hpv, hRe, e, WithLp.toLp_zero]

noncomputable def hpvHom (b : Fin k → Fin r → K) : (Fin r → K) →+ EuclideanSpace ℝ (hIdx K r) where
  toFun := hpv b
  map_zero' := projectedVector_zero b
  map_add' := projectedVector_add b

theorem normSqSum_pos {r : ℕ} {v : Fin r → ℂ} (hv : v ≠ 0) : 0 < hns v := by
  obtain ⟨l, hl⟩ := Function.ne_iff.mp hv
  have h1 : 0 < ‖v l‖ ^ 2 := by
    exact pow_pos (norm_pos_iff.mpr hl) 2
  exact lt_of_lt_of_le h1
    (Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ l))

theorem projectedVector_eq_zero_iff {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (q : Fin r → K) : hpv b q = 0 ↔ q ∈ Submodule.span K (Set.range b) := by
  constructor
  · intro h0
    by_contra hq
    have hpos : Fintype.card (K →+* ℂ) ≠ 0 := by
      rw [NumberField.Embeddings.card K ℂ]; exact Module.finrank_pos.ne'
    obtain ⟨σ0⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hpos)
    have h1 := norm_realCoords_sq (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ (q l))
    rw [← hpv, h0, norm_zero] at h1
    have h2 : 0 < ∑ σ, hns (hPm σ b *ᵥ fun l => σ (q l)) :=
      lt_of_lt_of_le (normSqSum_pos (orthogonalProjector_mulVec_ne_zero σ0 hb hq))
        (Finset.single_le_sum (f := fun σ => hns (hPm σ b *ᵥ fun l => σ (q l)))
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ σ0))
    rw [← h1] at h2
    norm_num at h2
  · intro hq
    have e : (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ (q l)) = 0 := by
      funext σ
      exact orthogonalProjector_mulVec_eq_zero σ hb hq
    have e2 : hReF (fun σ : K →+* ℂ => hPm σ b *ᵥ fun l => σ (q l)) = 0 := by
      rw [e]; funext p; simp [hReF]
    simp only [hpv, hRe, e2, WithLp.toLp_zero]

theorem orthogonalProjector_mulVec_smul (σ : K →+* ℂ) (b : Fin k → Fin r → K) (a : K) (x : Fin r → K) :
    (hPm σ b *ᵥ fun l => σ ((a • x) l)) = σ a • (hPm σ b *ᵥ fun l => σ (x l)) := by
  rw [← mulVec_smul]
  congr 1
  funext l
  simp [map_smul]

theorem inner_projectedVector_smul (b : Fin k → Fin r → K) (a a' : K) (x y : Fin r → K) :
    inner ℝ (hpv b (a • x)) (hpv b (a' • y)) =
      (∑ σ : K →+* ℂ, conj (σ a) * σ a' *
        (star (hPm σ b *ᵥ fun l => σ (x l)) ⬝ᵥ (hPm σ b *ᵥ fun l => σ (y l)))).re := by
  rw [hpv, hpv, inner_hRe]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [orthogonalProjector_mulVec_smul, orthogonalProjector_mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    smul_eq_mul, Complex.star_def]
  ring

end Real

end ReciprocityTheory.ChartRestriction.G.T0
end

namespace ReciprocityTheory.ChartRestriction.G.T0

open Matrix NumberField ComplexConjugate NumberField.ComplexEmbedding
open scoped ComplexOrder Kronecker

section Gram

variable {K : Type} [Field K] [NumberField K] {r k m : ℕ}

theorem embeddingColumns_conjugate (σ : K →+* ℂ) (b : Fin k → Fin r → K) :
    hBm (conjugate σ) b = (hBm σ b).map (starRingEnd ℂ) := by
  ext l j
  simp [hBm, NumberField.ComplexEmbedding.conjugate_coe_eq]

private lemma map_star_inv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    A⁻¹.map (starRingEnd ℂ) = (A.map (starRingEnd ℂ))⁻¹ := by
  have h : ∀ M : Matrix (Fin n) (Fin n) ℂ, M.map (starRingEnd ℂ) = Mᴴᵀ := by
    intro M
    ext i j
    simp [conjTranspose_apply]
  rw [h, h, ← transpose_nonsing_inv, conjTranspose_nonsing_inv]

theorem orthogonalProjector_conjugate (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b) :
    hPm (conjugate σ) b = (hPm σ b).map (starRingEnd ℂ) := by
  unfold hPm
  rw [embeddingColumns_conjugate σ b]
  have h1 : ((hBm σ b).map (starRingEnd ℂ))ᴴ = (hBm σ b)ᴴ.map (starRingEnd ℂ) := by
    ext i j
    simp [conjTranspose_apply]
  rw [h1, ← Matrix.map_mul, ← map_star_inv, Matrix.map_sub _ (map_sub _),
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul, Matrix.map_mul]

theorem orthogonalProjector_mulVec_conjugate (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (x : Fin r → K) :
    (hPm (conjugate σ) b *ᵥ fun l => (conjugate σ) (x l)) = star (hPm σ b *ᵥ fun l => σ (x l)) := by
  rw [orthogonalProjector_conjugate σ hb]
  ext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, NumberField.ComplexEmbedding.conjugate_coe_eq, map_sum,
    mul_comm]

theorem conj_sum_projected_inner (b : Fin k → Fin r → K) (hb : LinearIndependent K b) (a a' : K)
    (x y : Fin r → K) :
    conj (∑ σ : K →+* ℂ, conj (σ a) * σ a' *
        (star (hPm σ b *ᵥ fun l => σ (x l)) ⬝ᵥ (hPm σ b *ᵥ fun l => σ (y l)))) =
      ∑ σ : K →+* ℂ, conj (σ a) * σ a' *
        (star (hPm σ b *ᵥ fun l => σ (x l)) ⬝ᵥ (hPm σ b *ᵥ fun l => σ (y l))) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  have hinv : Function.Involutive (NumberField.ComplexEmbedding.conjugate (K := K)) := by
    intro σ
    ext z
    simp [NumberField.ComplexEmbedding.conjugate_coe_eq]
  refine Fintype.sum_bijective _ hinv.bijective _ _ (fun σ => ?_)
  rw [orthogonalProjector_mulVec_conjugate σ hb x, orthogonalProjector_mulVec_conjugate σ hb y,
    NumberField.ComplexEmbedding.conjugate_coe_eq, NumberField.ComplexEmbedding.conjugate_coe_eq]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [dotProduct, map_sum, mul_comm, mul_left_comm]

theorem quotientGram_conjTranspose (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (c : Fin m → Fin r → K) : (ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c)ᴴ = ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c := by
  unfold ReciprocityTheory.MultiplicativeHeights.quotGramC
  simp only [gramMatrix_eq_embeddingColumns, crossGram_eq_embeddingColumns, conjTranspose_sub, conjTranspose_mul,
    conjTranspose_conjTranspose, conjTranspose_nonsing_inv, Matrix.mul_assoc]

theorem quotientGram_det_re_eq (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (c : Fin m → Fin r → K) :
    (((ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det.re : ℝ) : ℂ) = (ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det := by
  have h := quotientGram_conjTranspose σ hb c
  have h2 : star (ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det = (ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det := by
    rw [← det_conjTranspose, h]
  exact Complex.conj_eq_iff_re.mp h2

end Gram

section GramDet

variable {K : Type} [Field K] [NumberField K] {r k m : ℕ}

noncomputable def hwv (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) :
    Fin m × Module.Free.ChooseBasisIndex ℤ (𝓞 K) → EuclideanSpace ℝ (hIdx K r) :=
  fun p => hpv b (integralBasis K p.2 • c p.1)

theorem det_gram_projectedLatticeVectors (b : Fin k → Fin r → K) (hb : LinearIndependent K b)
    (c : Fin m → Fin r → K) :
    (gram ℝ (hwv b c)).det =
      |(discr K : ℝ)| ^ m * ∏ σ : K →+* ℂ, (ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det.re := by
  classical
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = Fintype.card (K →+* ℂ) := by
    rw [NumberField.Embeddings.card, ← NumberField.RingOfIntegers.rank,
      Module.finrank_eq_card_chooseBasisIndex]
  obtain ⟨e⟩ : Nonempty (Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ (K →+* ℂ)) :=
    ⟨Fintype.equivOfCardEq hcard⟩
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 K))
      (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) ℂ, Ω = Matrix.of fun q p => e q (integralBasis K p) :=
    ⟨_, rfl⟩

  have hent : ∀ j p j' p', ((gram ℝ (hwv b c) (j, p) (j', p') : ℝ) : ℂ) =
      ∑ q, star (Ω q p) * ReciprocityTheory.MultiplicativeHeights.quotGramC 1 (e q) b c j j' * Ω q p' := by
    intro j p j' p'
    rw [Matrix.gram_apply]
    simp only [hwv]
    rw [inner_projectedVector_smul, Complex.conj_eq_iff_re.mp (conj_sum_projected_inner b hb _ _ _ _)]
    symm
    refine Fintype.sum_equiv e _ _ (fun q => ?_)
    rw [quotientGram_eq_projector (e q) hb c j j', hΩ]
    simp only [Matrix.of_apply]
    rw [show star ((e q) (integralBasis K p)) = conj ((e q) (integralBasis K p)) from rfl]
    ring
  have hmat : (gram ℝ (hwv b c)).map Complex.ofRealHom =
      ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Ω)ᴴ *
        Matrix.blockDiagonal (fun q => ReciprocityTheory.MultiplicativeHeights.quotGramC 1 (e q) b c) *
        ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Ω) := by
    ext ⟨j, p⟩ ⟨j', p'⟩
    rw [Matrix.map_apply, Complex.ofRealHom_eq_coe, hent]
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Matrix.kroneckerMap_apply, Matrix.blockDiagonal_apply, Matrix.one_apply, ite_mul, mul_ite,
      Finset.sum_ite_eq, Finset.sum_ite_eq', apply_ite (starRingEnd ℂ), map_zero]
  have hdet : ((gram ℝ (hwv b c)).det : ℂ) =
      star ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Ω).det *
        (Matrix.blockDiagonal (fun q => ReciprocityTheory.MultiplicativeHeights.quotGramC 1 (e q) b c)).det *
        ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Ω).det := by
    have h := RingHom.map_det Complex.ofRealHom (gram ℝ (hwv b c))
    rw [Complex.ofRealHom_eq_coe] at h
    rw [h, RingHom.mapMatrix_apply, hmat, det_mul, det_mul, det_conjTranspose]
  have hT : ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Ω).det = Ω.det ^ m := by
    simp [Matrix.det_kronecker]
  have hdisc : Ω.det ^ 2 = (discr K : ℂ) := by
    have h1 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ (integralBasis K)
      (e.trans (RingHom.equivRatAlgHom K ℂ))
    rw [← NumberField.coe_discr] at h1
    have h2 : Algebra.embeddingsMatrixReindex ℚ ℂ (integralBasis K)
        (e.trans (RingHom.equivRatAlgHom K ℂ)) = Ωᵀ := by
      ext i j
      simp [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, hΩ, RingHom.equivRatAlgHom]
    rw [h2, det_transpose] at h1
    rw [← h1]
    simp
  have hnorm : star Ω.det * Ω.det = ((|(discr K : ℝ)| : ℝ) : ℂ) := by
    rw [show star Ω.det = conj Ω.det from rfl, Complex.conj_mul', ← Complex.ofReal_pow, ← norm_pow,
      hdisc, Complex.norm_intCast]
  apply Complex.ofReal_injective
  rw [hdet, hT, Matrix.det_blockDiagonal]
  push_cast
  rw [← Equiv.prod_comp e (fun σ => (((ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det.re : ℝ) : ℂ))]
  simp_rw [quotientGram_det_re_eq _ hb c]
  rw [star_pow, ← hnorm]
  ring

end GramDet

end ReciprocityTheory.ChartRestriction.G.T0
end

namespace ReciprocityTheory.ChartRestriction.G.T0

open Matrix NumberField
open scoped ComplexOrder

section Deg

variable {K : Type} [Field K] [NumberField K] {r k : ℕ}

def hStd (K : Type) [Field K] [NumberField K] (r : ℕ) : Submodule (𝓞 K) (Fin r → K) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 K) K)

theorem mem_standardLattice_iff {x : Fin r → K} :
    x ∈ hStd K r ↔ ∀ i, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = x i := by
  simp [hStd, Submodule.mem_pi, Submodule.mem_one]

theorem pi_single_one_mem_hStd (i : Fin r) : (Pi.single i (1 : K) : Fin r → K) ∈ hStd K r := by
  rw [mem_standardLattice_iff]
  intro j
  by_cases h : j = i
  · subst h; exact ⟨1, by simp⟩
  · exact ⟨0, by simp [Pi.single_apply, h]⟩

theorem hStd_eq_span_pi_single : hStd K r =
    Submodule.span (𝓞 K) (Set.range fun i : Fin r => (Pi.single i (1 : K) : Fin r → K)) := by
  apply le_antisymm
  · intro x hx
    rw [mem_standardLattice_iff] at hx
    choose y hy using hx
    have e : x = ∑ i, y i • (Pi.single i (1 : K) : Fin r → K) := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · simp [← hy j, Algebra.smul_def]
      · intro i _ hij
        simp [Pi.single_apply, Ne.symm hij]
      · simp
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact pi_single_one_mem_hStd i

theorem exists_integral_completion {b : Fin k → Fin r → K} (hb : LinearIndependent K b) (hk : k ≤ r) :
    ∃ c : Fin (r - k) → Fin r → K, (∀ j, c j ∈ hStd K r) ∧ LinearIndependent K (Fin.append b c) ∧
      ∀ x, x ∈ Submodule.span K (Set.range (Fin.append b c)) := by
  classical
  set W := Submodule.span K (Set.range b) with hW
  let T := W.mkQ
  let v : Fin r → (Fin r → K) ⧸ W := fun i => T (Pi.single i 1)
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent K (Set.range v)
  have hspan_top : Submodule.span K (Set.range v) = ⊤ := by
    have e1 : Set.range v = T '' Set.range (Pi.basisFun K (Fin r)) := by
      ext y
      simp [v, Set.mem_image, Set.mem_range]
    rw [e1, Submodule.span_image, (Pi.basisFun K (Fin r)).span_eq, Submodule.map_top,
      Submodule.range_mkQ]
  have hsfin : s.Finite := (Set.finite_range v).subset hs
  haveI : Fintype s := hsfin.fintype
  have hcard : Fintype.card s = r - k := by
    have h1 : Fintype.card s = Module.finrank K ((Fin r → K) ⧸ W) := by
      rw [← Set.toFinset_card, ← finrank_span_set_eq_card hli, hspan, hspan_top, finrank_top]
    have hWk : Module.finrank K W = k := by rw [hW, finrank_span_eq_card hb, Fintype.card_fin]
    have h2 := Submodule.finrank_quotient_add_finrank W
    rw [hWk, Module.finrank_fin_fun] at h2
    omega
  let eq : Fin (r - k) ≃ s := (Fintype.equivFinOfCardEq hcard).symm
  have hidx : ∀ y : s, ∃ i, v i = y := fun y => hs y.2
  choose idx hidx' using hidx
  let c : Fin (r - k) → Fin r → K := fun j => Pi.single (idx (eq j)) 1
  have hTc : ∀ j, T (c j) = (eq j : (Fin r → K) ⧸ W) := fun j => hidx' (eq j)
  have hTli : LinearIndependent K (fun j => T (c j)) := by
    rw [show (fun j => T (c j)) = Subtype.val ∘ eq from funext hTc]
    exact hli.comp eq eq.injective
  have hTspan : ∀ y, y ∈ Submodule.span K (Set.range fun j => T (c j)) := by
    intro y
    have e2 : Set.range (fun j => T (c j)) = s := by
      ext z
      constructor
      · rintro ⟨j, rfl⟩; show T (c j) ∈ s; rw [hTc]; exact (eq j).2
      · intro hz; exact ⟨eq.symm ⟨z, hz⟩, by show T (c (eq.symm ⟨z, hz⟩)) = z; rw [hTc]; simp⟩
    rw [e2, hspan, hspan_top]
    trivial
  refine ⟨c, fun j => pi_single_one_mem_hStd _, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_add] at hg
    simp only [Fin.append_left, Fin.append_right] at hg
    have h1 : ∑ j, g (Fin.natAdd k j) • T (c j) = 0 := by
      have := congrArg T hg
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_add (f := _), map_zero, map_sum, map_sum] at this
      have h0 : ∑ i, T (g (Fin.castAdd (r - k) i) • b i) = 0 :=
        Finset.sum_eq_zero fun i _ => by
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      rw [h0, zero_add] at this
      simpa using this
    have h2 := Fintype.linearIndependent_iff.mp hTli _ h1
    have h3 : ∑ i, g (Fin.castAdd (r - k) i) • b i = 0 := by
      rw [← hg]
      simp [h2]
    have h4 := Fintype.linearIndependent_iff.mp hb _ h3
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · exact h4 i
    · exact h2 j
  · intro x
    obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hTspan (T x))
    have hT0 : T (x - ∑ j, β j • c j) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum]
      simp only [map_smul]
      rw [hβ, sub_self]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hT0
    obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hT0
    have hx : x = ∑ i, α i • b i + ∑ j, β j • c j := by rw [hα]; abel
    rw [hx]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_)
      (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_)
    · exact Submodule.subset_span ⟨Fin.castAdd (r - k) i, Fin.append_left b c i⟩
    · exact Submodule.subset_span ⟨Fin.natAdd k j, Fin.append_right b c j⟩

end Deg

section Deg2

variable {K : Type} [Field K] [NumberField K] {r k : ℕ}

theorem standardLattice_fg : (hStd K r).FG := by
  rw [hStd_eq_span_pi_single]
  exact Submodule.fg_span (Set.finite_range _)

theorem latDeg_standard_basis {n : ℕ} (h : n = r) (v : Fin n → Fin r → K)
    (hv : ReciprocityTheory.MultiplicativeHeights.IsKBasisIn (hStd K r) v) :
    ReciprocityTheory.MultiplicativeHeights.latDeg (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) (hStd K r) v = 0 := by
  classical
  let std : Fin n → Fin r → K := fun i => Pi.single (finCongr h i) 1
  have hstd_eq : std = ⇑(Pi.basisFun K (Fin r)) ∘ finCongr h := by
    funext i
    simp [std]
  have hrange : Set.range std = Set.range fun i : Fin r => (Pi.single i (1 : K) : Fin r → K) := by
    rw [hstd_eq, (finCongr h).surjective.range_comp]
    ext x
    simp
  have hstd : ReciprocityTheory.MultiplicativeHeights.IsKBasisIn (hStd K r) std := by
    refine ⟨fun i => pi_single_one_mem_hStd _, ?_, fun x _ => ?_⟩
    · rw [hstd_eq]
      exact (Pi.basisFun K (Fin r)).linearIndependent.comp _ (finCongr h).injective
    · rw [hstd_eq, (finCongr h).surjective.range_comp, (Pi.basisFun K (Fin r)).span_eq]
      trivial
  rw [ReciprocityTheory.MultiplicativeHeights.latDegBasis_holds K r n _ (hStd K r) v std (fun _ => PosDef.one) standardLattice_fg
    hv hstd]
  have hspan : Submodule.span (𝓞 K) (Set.range std) = hStd K r := by
    rw [hrange, hStd_eq_span_pi_single]
  have hgram : ∀ σ : K →+* ℂ, ReciprocityTheory.MultiplicativeHeights.gramC 1 σ std = 1 := by
    intro σ
    ext i j
    simp only [ReciprocityTheory.MultiplicativeHeights.gramC, ReciprocityTheory.MultiplicativeHeights.embVec, Matrix.of_apply, one_mulVec, dotProduct,
      Pi.star_apply, std, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      rw [Finset.sum_eq_single (finCongr h i)]
      · simp
      · intro l _ hl
        have hl' : ¬ l = Fin.cast h i := hl
        simp [Pi.single_apply, hl']
      · simp
    · rw [if_neg hij]
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases hl : l = finCongr h i
      · have : l ≠ finCongr h j := by
          rw [hl]; exact fun e => hij ((finCongr h).injective e)
        have this' : ¬ l = Fin.cast h j := this
        simp [Pi.single_apply, this']
      · have hl' : ¬ l = Fin.cast h i := hl
        simp [Pi.single_apply, hl']
  simp only [ReciprocityTheory.MultiplicativeHeights.latDeg, hspan, AddSubgroup.relIndex_self, Nat.cast_one, Real.log_one,
    hgram, det_one, Complex.one_re, Finset.sum_const_zero, mul_zero, sub_zero]

theorem latDeg_saturation {m : ℕ} (h : k + m = r) {b : Fin k → Fin r → K}
    (hbL : ∀ j, b j ∈ hStd K r) (c : Fin m → Fin r → K) (hc : ∀ j, c j ∈ hStd K r)
    (hli : LinearIndependent K (Fin.append b c))
    (hsp : ∀ x, x ∈ Submodule.span K (Set.range (Fin.append b c))) :
    ReciprocityTheory.MultiplicativeHeights.latDeg (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) (ReciprocityTheory.MultiplicativeHeights.satSub (hStd K r) b) b =
      -ReciprocityTheory.MultiplicativeHeights.quotDeg (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) (hStd K r) b c := by
  have hadd := ReciprocityTheory.MultiplicativeHeights.degAdd_holds K r k m (fun _ => 1) (hStd K r) b c (fun _ => PosDef.one)
    standardLattice_fg hbL hc hli (fun x _ => hsp x)
  have hmem : ∀ i, Fin.append b c i ∈ hStd K r := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; exact hbL i
    · rw [Fin.append_right]; exact hc j
  have h0 := latDeg_standard_basis h (Fin.append b c) ⟨hmem, hli, fun x _ => hsp x⟩
  linarith

theorem quotGram_eq_conjTranspose_mul (σ : K →+* ℂ) {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    {m : ℕ} (c : Fin m → Fin r → K) :
    ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c = (hPm σ b * hBm σ c)ᴴ * (hPm σ b * hBm σ c) := by
  have e1 : ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c = (hBm σ c)ᴴ * hPm σ b * hBm σ c := by
    simp only [ReciprocityTheory.MultiplicativeHeights.quotGramC, crossGram_eq_embeddingColumns, gramMatrix_eq_embeddingColumns, hPm, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
  rw [e1]
  simp only [conjTranspose_mul, orthogonalProjector_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (hPm σ b) (hPm σ b), orthogonalProjector_mul_self σ hb]

theorem quotGram_det_pos (σ : K →+* ℂ) {m : ℕ} {b : Fin k → Fin r → K} (hb : LinearIndependent K b)
    (c : Fin m → Fin r → K) (hli : LinearIndependent K (Fin.append b c)) :
    0 < (ReciprocityTheory.MultiplicativeHeights.quotGramC 1 σ b c).det.re := by
  have hinj : Function.Injective (hPm σ b * hBm σ c).mulVec := by
    intro z z' hzz
    have h0 : hPm σ b *ᵥ (hBm σ c *ᵥ (z - z')) = 0 := by
      rw [mulVec_mulVec, mulVec_sub, hzz, sub_self]
    set y := ((hBm σ b)ᴴ * hBm σ b)⁻¹ *ᵥ ((hBm σ b)ᴴ *ᵥ (hBm σ c *ᵥ (z - z'))) with hy
    have h1 : hBm σ c *ᵥ (z - z') - hBm σ b *ᵥ y = 0 := by
      have h2 := h0
      simp only [hPm, sub_mulVec, one_mulVec, ← mulVec_mulVec] at h2
      exact h2
    have hl := linearIndependent_map_embedding σ hli
    have h3 : ∑ i, Fin.append (-y) (z - z') i • (fun l => σ (Fin.append b c i l)) = 0 := by
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [← h1, embeddingColumns_mulVec, embeddingColumns_mulVec]
      simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
      abel
    have h4 := Fintype.linearIndependent_iff.mp hl _ h3
    funext j
    have := h4 (Fin.natAdd k j)
    rw [Fin.append_right] at this
    exact sub_eq_zero.mp this
  have hpd := PosDef.conjTranspose_mul_self (hPm σ b * hBm σ c) hinj
  rw [← quotGram_eq_conjTranspose_mul σ hb c] at hpd
  have hpos := hpd.det_pos
  rw [← quotientGram_det_re_eq σ hb c] at hpos
  exact_mod_cast hpos

end Deg2

end ReciprocityTheory.ChartRestriction.G.T0
