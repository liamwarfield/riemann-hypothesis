module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NegLogLeLcvOfIntegralForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NegRankMulLogLeLogCovolumeHermitian
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EmbGramDetConjugate
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.GramMean

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def embGramDet {d j : ℕ} (H : Matrix (Fin d) (Fin d) K) (E : Matrix (Fin d) (Fin j) K)
    (φ : K →+* ℂ) : ℂ :=
  ((E.map φ)ᴴ * H.map φ * E.map φ).det

omit [NumberField K] [StarRing K] in
theorem embGramDet_conjugate {d j : ℕ} (H : Matrix (Fin d) (Fin d) K)
    (E : Matrix (Fin d) (Fin j) K) (φ : K →+* ℂ) :
    embGramDet H E (ComplexEmbedding.conjugate φ) = starRingEnd ℂ (embGramDet H E φ) := by
  have hm : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) K),
      M.map (ComplexEmbedding.conjugate φ) = (M.map φ).map (starRingEnd ℂ) := by
    intro a b M
    ext i k
    simp [ComplexEmbedding.conjugate_coe_eq]
  unfold embGramDet
  rw [hm E, hm H, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.map_mul]
  congr 2

omit [NumberField K] [StarRing K] in
theorem embGramDet_re_mk {d j : ℕ} (H : Matrix (Fin d) (Fin d) K)
    (E : Matrix (Fin d) (Fin j) K) (φ : K →+* ℂ) :
    (embGramDet H E (InfinitePlace.mk φ).embedding).re = (embGramDet H E φ).re := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [h]
  · rw [h, embGramDet_conjugate, Complex.conj_re]

theorem gram_eq_mul {d j : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (v : InfinitePlace K) (e : Fin j → Fin d → K) :
    gram X v e = (((Matrix.of e)ᵀ).map v.embedding)ᴴ * (((X v)⁻¹)ᴴ * (X v)⁻¹) *
      ((Matrix.of e)ᵀ).map v.embedding := by
  ext a c
  simp only [gram, Formalism.HN.gramPl, Matrix.of_apply, Formalism.DivisionValues.majAt_eq, metMat, cv, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
    Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

theorem map_gramR {d j : ℕ} (H : Matrix (Fin d) (Fin d) K) (e : Fin j → Fin d → K)
    (φ : K →+* ℂ) :
    φ (gramR H e) = ((((Matrix.of e)ᵀ).map (Rb.tw φ))ᴴ * H.map φ *
      ((Matrix.of e)ᵀ).map φ).det := by
  unfold gramR
  rw [RingHom.map_det, RingHom.mapMatrix_apply]
  congr 1
  ext a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.transpose_apply, dotProduct, Matrix.mulVec, Pi.star_apply, map_sum, map_mul,
    Rb.tw_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [Complex.star_def, Complex.conj_conj]
  ring

private theorem det_gram_eq_embGramDet {K : Type} [Field K] [NumberField K] [StarRing K] {d j : ℕ}
    (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (hX : ∀ v : InfinitePlace K, ((X v)⁻¹)ᴴ * (X v)⁻¹ = H.map v.embedding)
    (e : Fin j → Fin d → K) (v : InfinitePlace K) :
    (gram X v e).det = embGramDet H ((Matrix.of e)ᵀ) v.embedding := by
  rw [gram_eq_mul, hX v]
  rfl

private theorem det_gram_re_nonneg' {K : Type} [Field K] [NumberField K] [StarRing K] {d j : ℕ}
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hX : ∀ v : InfinitePlace K, IsUnit (X v).det)
    (e : Fin j → Fin d → K) (v : InfinitePlace K) : 0 ≤ (gram X v e).det.re := by
  have hP : (((X v)⁻¹)ᴴ * (X v)⁻¹).PosDef := Rb.metMat_posDef X v (hX v)
  have hS := hP.posSemidef.conjTranspose_mul_mul_same (((Matrix.of e)ᵀ).map v.embedding)
  rw [← gram_eq_mul] at hS
  exact (Complex.le_def.mp hS.det_nonneg).1

theorem prod_norm_gramR_le (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K]
    (d j : ℕ) (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (hR : IsRatHerm (cmMax K) H X) (e : Fin j → Fin d → K) :
    ∏ v : InfinitePlace K, ‖v.embedding (gramR H e)‖ ≤
      ∏ v : InfinitePlace K, (gram X v e).det.re := by
  have hU : ∀ v : InfinitePlace K, IsUnit (X v).det := fun v => (hR.2 v).1
  have hX : ∀ v : InfinitePlace K, ((X v)⁻¹)ᴴ * (X v)⁻¹ = H.map v.embedding := fun v => (hR.2 v).2
  have hK0 : IsCMSub (cmMax K) := fun σ a ha => ha σ
  set E : Matrix (Fin d) (Fin j) K := (Matrix.of e)ᵀ with hE
  set g : InfinitePlace K → ℝ := fun v => (gram X v e).det.re with hg
  have hg0 : ∀ v, 0 ≤ g v := fun v => det_gram_re_nonneg' X hU e v
  have hloc : ∀ v : InfinitePlace K, ‖v.embedding (gramR H e)‖ ^ 2 ≤ g (Rb.plc v) * g v := by
    intro v
    have hPD : (H.map v.embedding).PosDef := by
      rw [← hX v]; exact Rb.metMat_posDef X v (hU v)
    have hcs := determinant_cauchy_schwarz d j (H.map v.embedding) hPD ((E.map (Rb.tw v.embedding))ᴴ)
      ((E.map v.embedding)ᴴ)
    rw [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose] at hcs
    rw [map_gramR]
    have h1 : g (Rb.plc v) = (embGramDet H E (Rb.tw v.embedding)).re := by
      simp only [hg]
      rw [det_gram_eq_embGramDet H X hX e, Rb.plc, embGramDet_re_mk]
    have h2 : g v = (embGramDet H E v.embedding).re := by
      simp only [hg]
      rw [det_gram_eq_embGramDet H X hX e]
    rw [h1, h2]
    unfold embGramDet
    rw [Rb.Hmap_tw (cmMax K) hK0 H hR.1]
    exact hcs
  have hperm : ∏ v : InfinitePlace K, g (Rb.plc v) = ∏ v : InfinitePlace K, g v :=
    Equiv.prod_comp (Function.Involutive.toPerm _ (fun v => Rb.plc_plc v)) g
  have hsq : (∏ v : InfinitePlace K, ‖v.embedding (gramR H e)‖) ^ 2 ≤
      (∏ v : InfinitePlace K, g v) ^ 2 := by
    have hsq2 : (∏ v : InfinitePlace K, g v) ^ 2 = ∏ v : InfinitePlace K, (g (Rb.plc v) * g v) := by
      rw [Finset.prod_mul_distrib, hperm, sq]
    rw [← Finset.prod_pow, hsq2]
    exact Finset.prod_le_prod₀ (fun v _ => by positivity) (fun v _ => hloc v)
  have ha : 0 ≤ ∏ v : InfinitePlace K, ‖v.embedding (gramR H e)‖ :=
    Finset.prod_nonneg fun v _ => norm_nonneg _
  have hb : 0 ≤ ∏ v : InfinitePlace K, g v := Finset.prod_nonneg fun v _ => hg0 v
  nlinarith

end GlobalTheory.GramMean
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecInjectiveMapOfLinearIndependent
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TestLat

theorem mulVec_injective_map_of_linearIndependent {K L : Type} [Field K] [Field L] (σ : K →+* L) {d j : ℕ}
    (e : Fin j → Fin d → K) (he : LinearIndependent K e) :
    Function.Injective (((Matrix.of e)ᵀ).map σ).mulVec := by
  letI : Algebra K L := σ.toAlgebra
  rw [Matrix.mulVec_injective_iff]
  have h := (linearIndependent_algebraMap_comp_iff (S := L) (v := e)).2 he
  exact h

theorem gram_eq_conjTranspose_mul {K : Type} [Field K] [NumberField K] [StarRing K] {d j : ℕ}
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K) (e : Fin j → Fin d → K) :
    gram X v e = ((X v)⁻¹ * ((Matrix.of e)ᵀ).map v.embedding)ᴴ * ((X v)⁻¹ * ((Matrix.of e)ᵀ).map v.embedding) := by
  ext a b
  simp only [gram, Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Matrix.of_apply]
  rw [Matrix.mul_apply]
  rfl

theorem gramR_ne_zero_and_gram_posDef : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (v₀ : InfinitePlace K), IsConjAt v₀ → ∀ (d j : ℕ) (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), IsMetric H X → ∀ e : Fin j → Fin d → K, LinearIndependent K e → gramR H e ≠ 0 ∧ ∀ v, (gram X v e).PosDef := by
  intro K _ _ _ _ v0 hv0 d j H X hX e he
  have hpos : ∀ v, (gram X v e).PosDef := by
    intro v
    rw [gram_eq_conjTranspose_mul]
    refine Matrix.PosDef.conjTranspose_mul_self _ ?_
    have h1 : Function.Injective ((X v)⁻¹).mulVec :=
      Matrix.mulVec_injective_iff_isUnit.2
        ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ (hX v).1))
    have h2 := mulVec_injective_map_of_linearIndependent v.embedding e he
    intro x y hxy
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hxy
    exact h2 (h1 hxy)
  refine ⟨?_, hpos⟩
  have key : v0.embedding (gramR H e) = (gram X v0 e).det := by
    unfold gramR
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    congr 1
    set σ := v0.embedding
    have hM : H.map σ = ((X v0)⁻¹).conjTranspose * (X v0)⁻¹ := (hX v0).2.symm
    ext a b
    rw [Matrix.map_apply, Matrix.of_apply, RingHom.map_dotProduct]
    have hmv : (⇑σ ∘ (H *ᵥ e b)) = H.map σ *ᵥ (⇑σ ∘ e b) :=
      funext fun i => RingHom.map_mulVec σ _ _ i
    have hs : (⇑σ ∘ star (e a)) = star (⇑σ ∘ e a) := by
      funext i
      simp only [Function.comp_apply, Pi.star_apply]
      rw [← starRingEnd_apply]
      exact hv0 (e a i)
    rw [hmv, hs, hM, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    simp only [gram, Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Matrix.of_apply]
    rfl
  intro h0
  rw [h0, map_zero] at key
  exact (hpos v0).det_pos.ne key

end GlobalTheory.TestLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NegRankMulLogLeLogCovolumeHermitian
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.LcvSub

theorem cnorm_sq_eq {ι : Type} [Fintype ι] (u : ι → ℂ) :
    ((∑ i, ‖u i‖ ^ 2 : ℝ) : ℂ) = star u ⬝ᵥ u := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  push_cast
  rfl

theorem cnorm_mulVec_eq {m n k : Type} [Fintype m] [Fintype n] [Fintype k]
    (A : Matrix m k ℂ) (B : Matrix n k ℂ) (h : Aᴴ * A = Bᴴ * B) (u : k → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm (A *ᵥ u) = Formalism.HermitianLatticesTheory.cnorm (B *ᵥ u) := by
  unfold Formalism.HermitianLatticesTheory.cnorm
  congr 1
  apply Complex.ofReal_injective
  rw [cnorm_sq_eq, cnorm_sq_eq, Matrix.star_mulVec, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, h]

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem fcoord_std {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K)
    (x : Fin d → K) :
    Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin d)) X v x = (X v)⁻¹ *ᵥ (fun i => v.embedding (x i)) := by
  unfold Formalism.HermitianLatticesTheory.fcoord
  congr 1

theorem gram_eq {d j : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K)
    (e : Fin j → Fin d → K) :
    gram X v e = ((X v)⁻¹ * ((Matrix.of e)ᵀ.map v.embedding))ᴴ *
      ((X v)⁻¹ * ((Matrix.of e)ᵀ.map v.embedding)) := by
  ext a b
  simp only [gram, Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, fcoord_std, Matrix.of_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
    Matrix.transpose_apply]

theorem gram_single {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (v : InfinitePlace K) :
    gram X v (fun i => (Pi.single i 1 : Fin d → K)) = ((X v)⁻¹)ᴴ * (X v)⁻¹ := by
  have h : (Matrix.of (fun i => (Pi.single i 1 : Fin d → K)))ᵀ.map v.embedding = 1 := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp [Function.swap, Pi.single_apply]
    · simp [hab, Matrix.one_apply]
  rw [gram_eq, h, Matrix.mul_one]

end GlobalTheory.LcvSub


open GlobalTheory.LcvSub in
theorem GlobalTheory.neg_rank_mul_log_le_lcv : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (v₀ : InfinitePlace K), IsConjAt v₀ → ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), IsRatHerm (cmMax K) H X → ∀ (s : ℕ), 0 < s → ∀ L : Submodule (𝓞 K) (Fin d → K), L.FG → (∀ x ∈ L, ∀ y ∈ L, (s : K) * (star x ⬝ᵥ H *ᵥ y) ∈ (algebraMap (𝓞 K) K).range) → -((Formalism.HN.rkK L : ℝ) * Real.log s) ≤ lcv X L := by
  intro K _ _ _ _ v₀ hv₀ d H X hH s hs L hL hint
  classical
  set j := Formalism.HN.rkK L with hj
  let W : Submodule K (Fin d → K) := Submodule.span K (L : Set (Fin d → K))
  let b : Module.Basis (Fin j) K W := Module.finBasis K W
  let e : Fin j → Fin d → K := fun a => (b a : Fin d → K)
  have he : LinearIndependent K e := b.linearIndependent.map' W.subtype W.ker_subtype
  let ψ : (Fin j → K) →ₗ[K] (Fin d → K) := W.subtype ∘ₗ b.equivFun.symm.toLinearMap
  have hψ : Function.Injective ψ := W.injective_subtype.comp b.equivFun.symm.injective
  have hψE : ∀ x, ψ x = (Matrix.of e)ᵀ *ᵥ x := by
    intro x
    ext i
    simp [ψ, e, Matrix.mulVec, dotProduct, mul_comm]
  have hrange : LinearMap.range ψ = W := by
    simp [ψ, LinearMap.range_comp]
  obtain ⟨hne, hpos⟩ := GlobalTheory.TestLat.gramR_ne_zero_and_gram_posDef K v₀ hv₀ d j H X hH.2 e he
  choose X' hX' hX'g using fun v => GlobalTheory.posDef_exists_frame j _ (hpos v)
  let L' : Submodule (𝓞 K) (Fin j → K) := L.comap (ψ.restrictScalars (𝓞 K))
  have hmap : L'.map (ψ.restrictScalars (𝓞 K)) = L := by
    apply Submodule.map_comap_eq_self
    intro x hx
    have : x ∈ LinearMap.range ψ := by
      rw [hrange]; exact Submodule.subset_span hx
    exact this
  have hfg : L'.FG :=
    Submodule.fg_of_fg_map_injective (ψ.restrictScalars (𝓞 K)) hψ (by rw [hmap]; exact hL)
  have hlat : Submodule.IsFullLattice K L' := by
    refine { toIsLattice := Submodule.IsLattice.of_fg K hfg, span_eq_top := ?_ }
    apply LinearMap.map_injective (LinearMap.ker_eq_bot.mpr hψ)
    have himage : ψ '' (L' : Set (Fin j → K)) = (L : Set (Fin d → K)) :=
      congrArg (fun M : Submodule (𝓞 K) (Fin d → K) => (M : Set (Fin d → K))) hmap
    rw [← Submodule.span_image, himage, Submodule.map_top, hrange]
  have hnorm : ∀ v x, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin d)) X v (ψ x) =
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin j)) X' v x := by
    intro v x
    unfold Formalism.HermitianLatticesTheory.normAt
    rw [fcoord_std, fcoord_std,
      cnorm_mulVec_eq (X' v)⁻¹ ((X v)⁻¹ * ((Matrix.of e)ᵀ.map v.embedding))
        (by rw [hX'g, gram_eq]), ← Matrix.mulVec_mulVec]
    congr 2
    ext i
    rw [hψE]
    simp [Matrix.mulVec, dotProduct]
  have hht := (Formalism.HN.rerealize K (Fin j → K) (Fin j) (Fin d → K) (Fin d) (Pi.basisFun K (Fin j)) X'
    (Pi.basisFun K (Fin d)) X ψ hX' (fun v => (hH.2 v).1) hψ hnorm L' hfg).1
  rw [hmap] at hht
  have hlcv : lcv X L = lcv X' L' := by
    unfold lcv; rw [hht]
  rw [hlcv]
  refine GlobalTheory.TestLat.neg_log_le_lcv_of_integral_form K j X' hX' (Matrix.of fun a c => star (e a) ⬝ᵥ H *ᵥ (e c)) s hs hne ?_ L' (by first | exact hlat | exact hlat.toIsLattice) ?_
  · have h := GlobalTheory.GramMean.prod_norm_gramR_le K d j H X hH e
    simp only [gram_single, hX'g]
    exact h
  · intro x hx y hy
    have h := hint (ψ x) hx (ψ y) hy
    have hG : (Matrix.of fun a c => star (e a) ⬝ᵥ H *ᵥ (e c)) =
        ((Matrix.of e)ᵀ)ᴴ * (H * (Matrix.of e)ᵀ) := by
      ext a c
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [hψE, hψE, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.mul_assoc] at h
    rw [hG]
    exact h
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NegRankMulLogLeLogCovolumeHermitianStatement
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.neg_rank_mul_log_le_log_covolume_hermitian : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (v₀ : InfinitePlace K), IsConjAt v₀ → ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), IsRatHerm (cmMax K) H X → ∀ (s : ℕ), 0 < s → ∀ L : Submodule (𝓞 K) (Fin d → K), L.FG → (∀ x ∈ L, ∀ y ∈ L, (s : K) * (star x ⬝ᵥ H *ᵥ y) ∈ (algebraMap (𝓞 K) K).range) → -((Formalism.HN.rkK L : ℝ) * Real.log s) ≤ lcv X L := by
  first | exact @GlobalTheory.neg_rank_mul_log_le_lcv | exact GlobalTheory.neg_rank_mul_log_le_lcv | (intros; apply GlobalTheory.neg_rank_mul_log_le_lcv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MaxSlopeLeLogOfIntegralHermitianForm
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem muMaxDef_le_log_of_integral : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (v₀ : InfinitePlace K), IsConjAt v₀ → ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), IsRatHerm (cmMax K) H X → ∀ (s : ℕ), 0 < s → ∀ L : Submodule (𝓞 K) (Fin d → K), L.FG → L ≠ ⊥ → (∀ x ∈ L, ∀ y ∈ L, (s : K) * (star x ⬝ᵥ H *ᵥ y) ∈ (algebraMap (𝓞 K) K).range) → Formalism.HN.muMaxDef (Pi.basisFun K (Fin d)) X L ≤ Real.log s := by
  intro K _ _ _ _ v₀ hv d H X hH s hs L hL hL0 hint
  have hX : ∀ v, IsUnit (X v).det := fun v => (hH.2 v).1
  refine Formalism.LFunctionChainParameters.slopeLatticeData.muMaxDef_le _ X hL0 fun Q hQ hQ0 => ?_
  have hQfg : Q.FG := Formalism.LFunctionChainParameters.slopeLatticeData.fg_of_le hL hQ
  have h := GlobalTheory.T.neg_rank_mul_log_le_log_covolume_hermitian K v₀ hv d H X hH s hs Q hQfg fun x hx y hy => hint x (hQ hx) y (hQ hy)
  rw [Formalism.LFunctionChainParameters.slopeLatticeData.muDef_eq_log _ X hX hQfg hQ0]
  have hj : (0 : ℝ) < (Formalism.HN.rkK Q : ℝ) := by exact_mod_cast Formalism.LFunctionChainParameters.slopeLatticeData.rkK_pos hQ0
  have hn : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K)
  unfold Formalism.DivisionValues.lcv at h
  have e : -(2 * Real.log (Formalism.HN.ht (Pi.basisFun K (Fin d)) X Q)) /
      ((Module.finrank ℚ K : ℝ) * (Formalism.HN.rkK Q : ℝ)) =
      -((2 / (Module.finrank ℚ K : ℝ)) * Real.log (Formalism.HN.ht (Pi.basisFun K (Fin d)) X Q)) /
        (Formalism.HN.rkK Q : ℝ) := by
    field_simp
  rw [e, div_le_iff₀ hj]
  linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MaxSlopeLeLogOfIntegralHermitianFormStatement
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maxSlope_le_log_of_integral_hermitian_form : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (v₀ : InfinitePlace K), IsConjAt v₀ → ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ), IsRatHerm (cmMax K) H X → ∀ (s : ℕ), 0 < s → ∀ L : Submodule (𝓞 K) (Fin d → K), L.FG → L ≠ ⊥ → (∀ x ∈ L, ∀ y ∈ L, (s : K) * (star x ⬝ᵥ H *ᵥ y) ∈ (algebraMap (𝓞 K) K).range) → Formalism.HN.muMaxDef (Pi.basisFun K (Fin d)) X L ≤ Real.log s := by
  first | exact @GlobalTheory.muMaxDef_le_log_of_integral | exact GlobalTheory.muMaxDef_le_log_of_integral | (intros; apply GlobalTheory.muMaxDef_le_log_of_integral <;> assumption)
end
