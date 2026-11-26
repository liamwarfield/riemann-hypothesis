module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SymmetricDistance.SymDistOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.DualIncl
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.ArchPlace
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.IndexDual

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeSizeContinuity.NormProd
noncomputable section

open NumberField

namespace PI.UnitaryGroupMassFormula.LSC.NormProd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem algebraMap_norm_eq (hc : Formalism.BasicNotions.CMData F E) (m : E) :
    algebraMap F E (Algebra.norm F m) = m * star m := by
  classical
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hc.deg2]; norm_num)
  have hfix : ∀ r : F, starRingAut (algebraMap F E r) = algebraMap F E r := fun r =>
    (hc.fixed _).mpr ⟨r, rfl⟩
  let σ : E ≃ₐ[F] E := AlgEquiv.ofRingEquiv (f := starRingAut) hfix
  have hσ : ∀ a, σ a = star a := fun _ => rfl
  have hne : (1 : E ≃ₐ[F] E) ≠ σ := by
    intro h
    have hall : ∀ a : E, a ∈ (algebraMap F E).range := fun a => by
      rw [← hc.fixed, ← hσ, ← h]; rfl
    have hbot : (⊥ : Subalgebra F E) = ⊤ := by
      ext a; simpa [Algebra.mem_bot] using hall a
    have h1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.mp hbot
    rw [hc.deg2] at h1; norm_num at h1
  have hle : Fintype.card (E ≃ₐ[F] E) ≤ 2 := by
    rw [← hc.deg2]
    exact (Fintype.card_le_of_injective (fun e : E ≃ₐ[F] E => (e : E →ₐ[F] E))
      (fun a b h => AlgEquiv.coe_algHom_injective h)).trans AlgHom.card_le
  have hge : 2 ≤ Fintype.card (E ≃ₐ[F] E) := by
    rw [← Finset.card_pair hne]; exact Finset.card_le_univ _
  have hcard : Fintype.card (E ≃ₐ[F] E) = Module.finrank F E := by
    rw [hc.deg2]; omega
  haveI : IsGalois F E := IsGalois.of_card_aut_eq_finrank F E (by rw [Nat.card_eq_fintype_card]; exact hcard)
  have huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, σ} :=
    (Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      (by rw [Finset.card_univ, Finset.card_pair hne]; omega)).symm
  rw [Algebra.norm_eq_prod_automorphisms, huniv, Finset.prod_pair hne]
  rfl

end PI.UnitaryGroupMassFormula.LSC.NormProd

namespace PI.UnitaryGroupMassFormula.LSC

open PI.UnitaryGroupMassFormula.LSC.NormProd

theorem norm_product_formula : NormProd := by
  intro I m
  letI := I.fF; letI := I.nF; letI := I.fE; letI := I.nE; letI := I.sE; letI := I.aFE
  have hc := I.cm
  set N := Algebra.norm I.F m with hN
  have hv : ∀ v : InfinitePlace I.F, ‖I.φ v m‖ ^ 2 = v N := by
    intro v
    have h1 : I.φ v (m * star m) = v.embedding N := by
      rw [← algebraMap_norm_eq hc m, I.φ_over]
    rw [map_mul, hc.cmUnram.2.1, Complex.mul_conj] at h1
    rw [← InfinitePlace.norm_embedding_eq, ← h1, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
  simp_rw [hv]
  have hmult : ∀ v : InfinitePlace I.F, v.mult = 1 := fun v =>
    InfinitePlace.mult_isReal ⟨v, hc.totReal.isReal v⟩
  have := InfinitePlace.prod_eq_abs_norm N
  simp only [hmult, pow_one] at this
  rw [this, hN, Algebra.norm_norm, Rat.cast_abs]

end PI.UnitaryGroupMassFormula.LSC
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.LatticeIsDiscreteGroup
noncomputable section

open NumberField Matrix

namespace PI.UnitaryGroupMassFormula.LCG

open PI.LatCountG

theorem hsN_nonneg' {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hsN A := by
  unfold hsN
  exact Real.sqrt_nonneg _

theorem lattice_is_discrete_group : LatIsG := by
  intro I x
  obtain ⟨Λ, h1, h2, h3⟩ := PI.UnitaryGroupMassFormula.LSC.lattice_isometry I x
  exact ⟨Λ, h1, h2, h3⟩

theorem gram_nonneg (hDM : PI.UnitaryGroupMassFormula.LSC.DetMono) (I : Formalism.MainNotions.S.AutInst) (z : I.GA) (v : InfinitePlace I.F) {j : ℕ}
    (b : Fin j → Fin I.n → I.E) : 0 ≤ ((gramV I z v b).det).re := by
  let C : Matrix (Fin I.n) (Fin j) ℂ := Matrix.of fun i a => coordV I z v (b a) i
  have hG : gramV I z v b = Cᴴ * C := by
    ext a c
    simp [gramV, C, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hG]
  exact (hDM I.n j C 1 1 zero_le_one (fun w => by simp)).1

theorem ht_eq (I : Formalism.MainNotions.S.AutInst) {z : I.GA} (s : Sub I z) :
    ht I s = (∏ v, ((gramV I z v s.b).det).re) / (idx I s.B s.b : ℝ) := rfl

theorem tau_pow_le_ht (hDM : PI.UnitaryGroupMassFormula.LSC.DetMono) (I : Formalism.MainNotions.S.AutInst) (z : I.GA) (hz : 0 < tau1 I z) (s : Sub I z) :
    tau1 I z ^ (2 * I.f * s.j) ≤ ht I s ∧ idx I s.B s.b ≠ 0 := by
  have hf : 0 < I.f := Module.finrank_pos
  have hj : 0 < s.j := s.j_pos
  have hN : (0 : ℝ) < 2 * (I.f : ℝ) * (s.j : ℝ) := by
    have : (0 : ℝ) < I.f := by exact_mod_cast hf
    have : (0 : ℝ) < s.j := by exact_mod_cast hj
    positivity
  have hht : ∀ t : Sub I z, 0 ≤ ht I t := by
    intro t
    rw [ht_eq]
    exact div_nonneg (Finset.prod_nonneg fun v _ => gram_nonneg hDM I z v t.b) (Nat.cast_nonneg _)
  have hsize : ∀ t : Sub I z, 0 ≤ size I t := fun t => Real.rpow_nonneg (hht t) _
  have hle : tau1 I z ≤ size I s :=
    (min_le_right _ _).trans (ciInf_le ⟨0, by rintro _ ⟨t, rfl⟩; exact hsize t⟩ s)
  have hpow : size I s ^ (2 * I.f * s.j) = ht I s := by
    unfold size
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hht s)]
    push_cast
    rw [one_div_mul_cancel hN.ne', Real.rpow_one]
  refine ⟨?_, ?_⟩
  · calc tau1 I z ^ (2 * I.f * s.j) ≤ size I s ^ (2 * I.f * s.j) := pow_le_pow_left₀ hz.le hle _
      _ = ht I s := hpow
  · intro h0
    have h1 : ht I s = 0 := by
      rw [ht_eq, h0]
      simp
    have hs0 : size I s = 0 := by
      unfold size
      rw [h1, Real.zero_rpow (one_div_pos.2 hN).ne']
    linarith

theorem separation_of_points : SepOf := by
  intro hLat hDual hCh hArch hIdx hNP hDM _hCard I x y hx hy δ hδ hmap
  obtain ⟨Λ, hFG, hspan, hΛ⟩ := hLat I y
  obtain ⟨k, u, b', hk, hu, hind1, hspan1, hb', hind2, hperp, hspan2⟩ := hCh I y δ hδ
  have huΛ : ∀ c, u c ∈ Λ := fun c => by
    have := hu c
    rw [hΛ] at this
    exact this
  have hbΛ : ∀ a, b' a ∈ Λ := fun a => by
    have := hb' a
    rw [hΛ] at this
    exact this
  let s₁ : Sub I x :=
    { j := k
      j_pos := hk
      b := fun c => δ *ᵥ u c
      b_ind := hind1
      B := imSub I Λ δ
      B_lat := by
        intro z hz
        obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hz
        exact hmap w (by rw [hΛ]; exact hw)
      b_mem := fun c => Submodule.mem_map.2 ⟨u c, huΛ c, rfl⟩
      B_span := by
        intro z hz
        obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hz
        exact hspan1 w }
  let s₂ : Sub I y :=
    { j := k
      j_pos := hk
      b := b'
      b_ind := hind2
      B := perpSub I Λ δ
      B_lat := by
        intro z hz
        rw [hΛ]
        exact (Submodule.mem_inf.1 hz).1
      b_mem := fun a => Submodule.mem_inf.2 ⟨hbΛ a, hperp a⟩
      B_span := fun z hz => hspan2 z (Submodule.mem_inf.1 hz).2 }
  obtain ⟨h1, hi1⟩ := tau_pow_le_ht hDM I x hx s₁
  obtain ⟨h2, hi2⟩ := tau_pow_le_ht hDM I y hy s₂
  rw [ht_eq] at h1 h2
  change tau1 I x ^ (2 * I.f * k) ≤ (∏ v, ((gramV I x v (fun c => δ *ᵥ u c)).det).re) /
    (idx I (imSub I Λ δ) (fun c => δ *ᵥ u c) : ℝ) at h1
  change tau1 I y ^ (2 * I.f * k) ≤ (∏ v, ((gramV I y v b').det).re) / (idx I (perpSub I Λ δ) b' : ℝ) at h2
  change idx I (imSub I Λ δ) (fun c => δ *ᵥ u c) ≠ 0 at hi1
  change idx I (perpSub I Λ δ) b' ≠ 0 at hi2
  have hdualΛ : ∀ w, (∀ w' ∈ Λ, hf I w' w ∈ (algebraMap (𝓞 I.E) I.E).range) → w ∈ Λ := by
    intro w hw
    have := hDual I y w (by rw [hΛ]; exact hw)
    rw [hΛ] at this
    exact this
  have hN := hIdx I Λ hFG hspan hdualΛ δ k u b' huΛ hind1 hspan1 hbΛ hind2 hperp hspan2 hi1 hi2
  have hNP' := hNP I (pairM I b' u).det
  have hi1' : (0 : ℝ) < idx I (imSub I Λ δ) (fun c => δ *ᵥ u c) := by exact_mod_cast Nat.pos_of_ne_zero hi1
  have hi2' : (0 : ℝ) < idx I (perpSub I Λ δ) b' := by exact_mod_cast Nat.pos_of_ne_zero hi2
  have hHp : 0 ≤ ∏ v, hsN (amat I x y v δ) := Finset.prod_nonneg fun v _ => hsN_nonneg' _
  have key : ((tau1 I x * tau1 I y) ^ I.f) ^ (2 * k) ≤ (∏ v, hsN (amat I x y v δ)) ^ (2 * k) := by
    rw [← pow_mul, mul_pow, show I.f * (2 * k) = 2 * I.f * k by ring]
    calc tau1 I x ^ (2 * I.f * k) * tau1 I y ^ (2 * I.f * k)
        ≤ ((∏ v, ((gramV I x v (fun c => δ *ᵥ u c)).det).re) / (idx I (imSub I Λ δ) (fun c => δ *ᵥ u c) : ℝ)) *
          ((∏ v, ((gramV I y v b').det).re) / (idx I (perpSub I Λ δ) b' : ℝ)) :=
          mul_le_mul h1 h2 (pow_nonneg (hy.le) _) ((pow_nonneg hx.le _).trans h1)
      _ = (∏ v, (((gramV I x v (fun c => δ *ᵥ u c)).det).re * ((gramV I y v b').det).re)) /
          ((idx I (imSub I Λ δ) (fun c => δ *ᵥ u c) : ℝ) * (idx I (perpSub I Λ δ) b' : ℝ)) := by
          rw [Finset.prod_mul_distrib, div_mul_div_comm]
      _ ≤ (∏ v, (hsN (amat I x y v δ) ^ (2 * k) * ‖I.φ v (pairM I b' u).det‖ ^ 2)) /
          ((idx I (imSub I Λ δ) (fun c => δ *ᵥ u c) : ℝ) * (idx I (perpSub I Λ δ) b' : ℝ)) := by
          apply div_le_div_of_nonneg_right _ (mul_pos hi1' hi2').le
          exact Finset.prod_le_prod₀ (fun v _ => mul_nonneg (gram_nonneg hDM I x v _) (gram_nonneg hDM I y v _))
            (fun v _ => hArch I x y δ k u b' v hind1 hspan1 hind2 hperp)
      _ = (∏ v, hsN (amat I x y v δ)) ^ (2 * k) * |((Algebra.norm ℚ (pairM I b' u).det : ℚ) : ℝ)| /
          ((idx I (imSub I Λ δ) (fun c => δ *ᵥ u c) : ℝ) * (idx I (perpSub I Λ δ) b' : ℝ)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow, hNP']
      _ ≤ (∏ v, hsN (amat I x y v δ)) ^ (2 * k) := by
          rw [div_le_iff₀ (mul_pos hi1' hi2')]
          exact mul_le_mul_of_nonneg_left hN (pow_nonneg hHp _)
  exact le_of_pow_le_pow_left₀ (by omega) hHp key

end PI.UnitaryGroupMassFormula.LCG
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.ArchIneq
noncomputable section

open Matrix

namespace PI.UnitaryGroupMassFormula.LCG

theorem archimedean_inequality : ArchIneq := by
  intro n k A C D κ hκ hA hker
  have hGdet := (PI.UnitaryGroupMassFormula.LSC.determinant_monotone n k D 1 1 zero_le_one (by intro w; simp)).1
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin k) (Fin k) ℂ, G = Dᴴ * D := ⟨_, rfl⟩
  rw [← hG] at hGdet ⊢
  have hGh : Gᴴ = G := by
    rw [hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have him : G.det.im = 0 := by
    have hstar : star G.det = G.det := by rw [← Matrix.det_conjTranspose, hGh]
    have h1 := congrArg Complex.im hstar
    simp only [Complex.star_def, Complex.conj_im] at h1
    linarith
  by_cases hg : G.det = 0
  · rw [hg, Complex.zero_re, mul_zero]
    exact mul_nonneg (pow_nonneg hκ k) (sq_nonneg _)
  · have hGu : IsUnit G.det := isUnit_iff_ne_zero.mpr hg
    obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin n) (Fin k) ℂ, X = D * G⁻¹ * Dᴴ * C := ⟨_, rfl⟩
    have hAP : A * (D * G⁻¹ * Dᴴ) = A := by
      apply Matrix.ext_of_mulVec_single
      intro j
      have h1 : Dᴴ *ᵥ ((Pi.single j 1 : Fin n → ℂ) - (D * G⁻¹ * Dᴴ) *ᵥ Pi.single j 1) = 0 := by
        have h3 : Dᴴ * (D * G⁻¹ * Dᴴ) = G * G⁻¹ * Dᴴ := by
          rw [hG]
          simp only [Matrix.mul_assoc]
        rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, h3, Matrix.mul_nonsing_inv G hGu, Matrix.one_mul, sub_self]
      have h2 := hker _ h1
      rw [Matrix.mulVec_sub, sub_eq_zero] at h2
      rw [← Matrix.mulVec_mulVec, ← h2]
    have hAX : A * X = A * C := by
      rw [hX, ← Matrix.mul_assoc, hAP]
    have hdm := (PI.UnitaryGroupMassFormula.LSC.determinant_monotone n k X A κ hκ hA).2
    rw [hAX] at hdm
    have hXh : Xᴴ = Cᴴ * D * G⁻¹ * Dᴴ := by
      rw [hX]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_nonsing_inv,
        hGh, Matrix.mul_assoc]
    have hXX : Xᴴ * X = Cᴴ * D * G⁻¹ * (Dᴴ * C) := by
      rw [hXh, hX]
      have hGG : G⁻¹ * (Dᴴ * D) = 1 := by
        rw [← hG]
        exact Matrix.nonsing_inv_mul G hGu
      calc Cᴴ * D * G⁻¹ * Dᴴ * (D * G⁻¹ * Dᴴ * C) = Cᴴ * D * (G⁻¹ * (Dᴴ * D)) * G⁻¹ * (Dᴴ * C) := by
            simp only [Matrix.mul_assoc]
        _ = Cᴴ * D * G⁻¹ * (Dᴴ * C) := by rw [hGG, Matrix.mul_one]
    have hdetX : (Xᴴ * X).det = star (Dᴴ * C).det * (Dᴴ * C).det / G.det := by
      have hCD : Cᴴ * D = (Dᴴ * C)ᴴ := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      rw [hXX, Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hCD,
        Matrix.det_conjTranspose]
      ring
    have h5 : (Xᴴ * X).det * G.det = star (Dᴴ * C).det * (Dᴴ * C).det := by
      rw [hdetX, div_mul_cancel₀ _ hg]
    have hval : (Xᴴ * X).det.re * G.det.re = ‖(Dᴴ * C).det‖ ^ 2 := by
      have h6 := congrArg Complex.re h5
      rw [Complex.mul_re, him, mul_zero, sub_zero] at h6
      rw [h6, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
      ring
    calc (((A * C)ᴴ * (A * C)).det).re * G.det.re ≤ κ ^ k * (Xᴴ * X).det.re * G.det.re :=
          mul_le_mul_of_nonneg_right hdm hGdet
      _ = κ ^ k * ‖(Dᴴ * C).det‖ ^ 2 := by rw [mul_assoc, hval]

end PI.UnitaryGroupMassFormula.LCG
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.PackLem
noncomputable section

open MeasureTheory Metric Module

namespace PI.UnitaryGroupMassFormula.LCG

def matVec {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) : EuclideanSpace ℂ (Fin N × Fin N) :=
  WithLp.toLp 2 (fun ij => A ij.1 ij.2)

theorem norm_matVec {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) : ‖matVec A‖ = hsN A := by
  rw [EuclideanSpace.norm_eq, hsN, Formalism.REAL.hs, Fintype.sum_prod_type]
  rfl

theorem matVec_sub {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ) : matVec (A - B) = matVec A - matVec B := by
  ext ij
  simp [matVec]

theorem finrank_matSpace (N : ℕ) : finrank ℝ (EuclideanSpace ℂ (Fin N × Fin N)) = 2 * N ^ 2 := by
  rw [finrank_real_of_complex, finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin, sq]

theorem lattice_packLem : PackLem := by
  intro ι _ N R ρ hρ hR T hT hsep
  classical
  let W := EuclideanSpace ℂ (Fin N × Fin N)
  let μ : Measure W := Measure.addHaar
  let ν : Measure (ι → W) := Measure.pi fun _ => μ
  let B : (ι → Matrix (Fin N) (Fin N) ℂ) → Set (ι → W) :=
    fun p => Set.univ.pi fun v => ball (matVec (p v)) (ρ v / 2)
  let Big : Set (ι → W) := Set.univ.pi fun v => ball (0 : W) (R v + ρ v / 2)
  have hdisj : (T : Set (ι → Matrix (Fin N) (Fin N) ℂ)).PairwiseDisjoint B := by
    intro p hp q hq hpq
    rw [Function.onFun, Set.disjoint_left]
    intro z hzp hzq
    obtain ⟨v, hv⟩ := hsep p hp q hq hpq
    have h1 := (Set.mem_univ_pi.1 hzp) v
    have h2 := (Set.mem_univ_pi.1 hzq) v
    rw [mem_ball] at h1 h2
    have h3 : dist (matVec (p v)) (matVec (q v)) < ρ v := by
      calc dist (matVec (p v)) (matVec (q v)) ≤ dist (matVec (p v)) (z v) + dist (z v) (matVec (q v)) :=
            dist_triangle _ _ _
        _ < ρ v / 2 + ρ v / 2 := by rw [dist_comm] at h1; exact add_lt_add h1 h2
        _ = ρ v := by ring
    rw [dist_eq_norm, ← matVec_sub, norm_matVec] at h3
    linarith
  have hmeas : ∀ p ∈ T, MeasurableSet (B p) := fun p _ =>
    MeasurableSet.univ_pi fun v => measurableSet_ball
  have hsub : (⋃ p ∈ T, B p) ⊆ Big := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨p, hp, hz⟩ := hz
    refine Set.mem_univ_pi.2 fun v => ?_
    have h1 := (Set.mem_univ_pi.1 hz) v
    rw [mem_ball, dist_eq_norm] at h1
    rw [mem_ball_zero_iff]
    have h2 : ‖matVec (p v)‖ ≤ R v := by rw [norm_matVec]; exact hT p hp v
    calc ‖z v‖ = ‖(z v - matVec (p v)) + matVec (p v)‖ := by rw [sub_add_cancel]
      _ ≤ ‖z v - matVec (p v)‖ + ‖matVec (p v)‖ := norm_add_le _ _
      _ < ρ v / 2 + R v := by linarith
      _ = R v + ρ v / 2 := by ring
  have key : ∑ p ∈ T, ν (B p) ≤ ν Big := by
    rw [← measure_biUnion_finset hdisj hmeas]
    exact measure_mono hsub
  set d := finrank ℝ W with hd
  set c := μ (ball (0 : W) 1) with hc
  have hc0 : c ≠ 0 := (measure_ball_pos μ (0 : W) one_pos).ne'
  have hctop : c ≠ ⊤ := measure_ball_lt_top.ne
  have hB : ∀ p, ν (B p) = ∏ v, ENNReal.ofReal ((ρ v / 2) ^ d) * c := by
    intro p
    simp only [ν, B, Measure.pi_pi]
    refine Finset.prod_congr rfl fun v _ => ?_
    exact Measure.addHaar_ball_of_pos μ _ (by linarith [hρ v])
  have hBig : ν Big = ∏ v, ENNReal.ofReal ((R v + ρ v / 2) ^ d) * c := by
    simp only [ν, Big, Measure.pi_pi]
    refine Finset.prod_congr rfl fun v _ => ?_
    exact Measure.addHaar_ball_of_pos μ _ (by linarith [hρ v, hR v])
  simp only [hB, Finset.sum_const, nsmul_eq_mul] at key
  rw [hBig] at key
  have hfin : ∏ v, ENNReal.ofReal ((R v + ρ v / 2) ^ d) * c ≠ ⊤ :=
    ENNReal.prod_ne_top fun v _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top hctop
  have key' := ENNReal.toReal_mono hfin key
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_prod, ENNReal.toReal_prod] at key'
  simp only [ENNReal.toReal_mul] at key'
  have hc' : 0 < c.toReal := ENNReal.toReal_pos hc0 hctop
  have hpos : ∀ v, 0 < ρ v / 2 := fun v => by linarith [hρ v]
  simp only [fun v => ENNReal.toReal_ofReal (pow_nonneg (hpos v).le d),
    fun v => ENNReal.toReal_ofReal (pow_nonneg (add_pos_of_nonneg_of_pos (hR v) (hpos v)).le d)] at key'
  have hprodpos : 0 < ∏ v, (ρ v / 2) ^ d * c.toReal :=
    Finset.prod_pos fun v _ => mul_pos (pow_pos (hpos v) d) hc'
  rw [← le_div_iff₀ hprodpos, ← Finset.prod_div_distrib] at key'
  have hdN : d = 2 * N ^ 2 := finrank_matSpace N
  calc (T.card : ℝ) ≤ ∏ v, (R v + ρ v / 2) ^ d * c.toReal / ((ρ v / 2) ^ d * c.toReal) := key'
    _ = ∏ v, ((2 * R v + ρ v) / ρ v) ^ (2 * N ^ 2) := by
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [mul_div_mul_right _ _ hc'.ne', ← div_pow, hdN]
      congr 1
      have := hρ v
      field_simp

end PI.UnitaryGroupMassFormula.LCG

end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.SublatticeOfLattice
noncomputable section

open NumberField Matrix

namespace PI.UnitaryGroupMassFormula.LCG

theorem sublattice_of_lattice : LatSub := by
  intro I x u u' hu hu'
  simp only [PI.LatCountG.latSet, Set.mem_setOf_eq] at hu hu' ⊢
  have h : (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) ((u - u') i)) =
      (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (u i)) -
        (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (u' i)) := by
    funext i
    simp [map_sub]
  rw [h, Matrix.mulVec_sub]
  exact Submodule.sub_mem _ hu hu'

theorem lattice_map_image : LatMap := by
  intro I x y γ g hγ hK u hu
  simp only [PI.LatCountG.latSet, Set.mem_setOf_eq] at hu ⊢
  have h1 : (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)
      (((g : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ u) i)) =
      I.fmat γ.2 *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (u i)) := by
    funext i
    rw [hγ]
    exact RingHom.map_mulVec _ _ _ i
  have hK' : ∀ v, v ∈ I.Lf ↔ I.fmat (x⁻¹ * γ * y).2 *ᵥ v ∈ I.Lf := hK
  have hk := (hK' (I.fmat y.2⁻¹ *ᵥ fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (u i))).1 hu
  rw [h1]
  convert hk using 1
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  simp only [Formalism.MainNotions.S.AutInst.fmat, Prod.snd_mul, Prod.snd_inv]
  push_cast
  simp only [Units.val_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)),
    Matrix.mul_one]

theorem norm_positive : NPos := by
  intro I x h
  by_contra hn
  have hn0 : I.n = 0 := by omega
  have hE : IsEmpty (PI.LatCountG.Sub I x) := by
    constructor
    intro s
    have hj := s.j_pos
    apply s.b_ind.ne_zero ⟨0, by omega⟩
    funext i
    exact absurd i.2 (by omega)
  have h0 : PI.LatCountG.tau1 I x = 0 := by
    unfold PI.LatCountG.tau1
    rw [Real.iInf_of_isEmpty]
    exact min_eq_right (by norm_num)
  linarith

theorem card_places_bound : CardPl := by
  intro I
  haveI : NumberField.IsTotallyReal I.F := I.cm.totReal
  have h1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank I.F
  have h2 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := I.F)
  have h3 := NumberField.IsTotallyReal.nrComplexPlaces_eq_zero (K := I.F)
  show _ = Module.finrank ℚ I.F
  omega

end PI.UnitaryGroupMassFormula.LCG
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.BoxBound
noncomputable section

open Matrix

namespace PI.UnitaryGroupMassFormula.LCG

namespace BoxB

variable {n : ℕ}

section Frob

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedRing
  Matrix.frobeniusNormedAlgebra Matrix.frobeniusNormedSpace

lemma frob_sq (A : Matrix (Fin n) (Fin n) ℂ) : ‖A‖ ^ 2 = Formalism.REAL.hs A := by
  rw [Matrix.frobenius_norm_def, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  simp only [Real.rpow_two]
  norm_num [Formalism.REAL.hs]

lemma frob_eq (A : Matrix (Fin n) (Fin n) ℂ) : ‖A‖ = Real.sqrt (Formalism.REAL.hs A) := by
  rw [← frob_sq, Real.sqrt_sq (norm_nonneg A)]

lemma hs_one : Formalism.REAL.hs (1 : Matrix (Fin n) (Fin n) ℂ) = n := by
  unfold Formalism.REAL.hs
  have h1 : ∀ i : Fin n, ∑ j, ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 = 1 := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Matrix.one_apply_ne (Ne.symm hj)]
    · intro h
      exact absurd (Finset.mem_univ i) h
  simp [h1]

lemma norm_one_eq : ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ = Real.sqrt n := by
  rw [frob_eq, hs_one]

lemma term_le (hn : 1 ≤ n) (X : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    ‖((k.factorial : ℂ)⁻¹) • X ^ k‖ ≤ Real.sqrt n * (‖X‖ ^ k / k.factorial) := by
  have hsq : 1 ≤ Real.sqrt n := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hn
  have hpow : ‖X ^ k‖ ≤ Real.sqrt n * ‖X‖ ^ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [norm_one_eq]
    · calc ‖X ^ k‖ ≤ ‖X‖ ^ k := norm_pow_le' X hk
        _ ≤ Real.sqrt n * ‖X‖ ^ k := le_mul_of_one_le_left (by positivity) hsq
  have hc : ‖((k.factorial : ℂ)⁻¹)‖ = (k.factorial : ℝ)⁻¹ := by simp
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  rw [norm_smul, hc, inv_mul_eq_div, mul_div_assoc']
  exact div_le_div_of_nonneg_right hpow hf.le

lemma norm_exp_le (hn : 1 ≤ n) (X : Matrix (Fin n) (Fin n) ℂ) :
    ‖NormedSpace.exp X‖ ≤ Real.sqrt n * Real.exp ‖X‖ := by
  rw [NormedSpace.exp_eq_tsum ℂ]
  have hs := (NormedSpace.expSeries_div_hasSum_exp ‖X‖).mul_left (Real.sqrt n)
  rw [← Real.exp_eq_exp_ℝ] at hs
  exact tsum_of_norm_bounded hs (fun k => term_le hn X k)

lemma hs_exp_le (X : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.hs (NormedSpace.exp X) ≤ (Real.sqrt n * Real.exp (Real.sqrt (Formalism.REAL.hs X))) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [Formalism.REAL.hs]
  · rw [← frob_sq, ← frob_eq]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_exp_le hn X) 2

end Frob

private lemma hs_eq_re_trace_conjTranspose_mul' {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.hs M = (Mᴴ * M).trace.re := by
  unfold Formalism.REAL.hs
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

lemma hs_unitary_mul {k : Matrix (Fin n) (Fin n) ℂ} (hk : kᴴ * k = 1) (M : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.hs (k * M) = Formalism.REAL.hs M := by
  rw [hs_eq_re_trace_conjTranspose_mul', hs_eq_re_trace_conjTranspose_mul', Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc kᴴ k M, hk,
    Matrix.one_mul]

end BoxB

open BoxB in
theorem box_lattice_point_bound : BoxBound := by
  intro n ε g
  have hK : ∀ k : Matrix (Fin n) (Fin n) ℂ, k ∈ Formalism.REAL.Kset ε → kᴴ * k = 1 := by
    intro k hk
    simp only [Formalism.REAL.Kset, Set.mem_setOf_eq] at hk
    exact Matrix.mem_unitaryGroup_iff'.mp hk.1
  have hP : Formalism.REAL.Polar := Formalism.REAL.polar_decomposition_holds
  have hgi : Formalism.REAL.inUJ ε (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)) : Matrix (Fin n) (Fin n) ℂ) := g.2
  obtain ⟨k0, X0, hk0, hX0, hg0⟩ := (hP n ε).1 _ hgi
  set S := {t | ∃ k X : Matrix (Fin n) (Fin n) ℂ, k ∈ Formalism.REAL.Kset ε ∧ Formalism.REAL.inP ε X ∧
      ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = k * NormedSpace.exp X ∧
      t = Real.sqrt (Formalism.REAL.hs X)} with hS
  have hne : S.Nonempty := ⟨_, k0, X0, hk0, hX0, hg0, rfl⟩
  have hbound : ∀ t ∈ S, hsN (Formalism.MainNotions.S.uMat g) ≤ Real.sqrt n * Real.exp t := by
    rintro t ⟨k, X, hk, _, hgk, rfl⟩
    unfold hsN Formalism.MainNotions.S.uMat
    rw [hgk, hs_unitary_mul (hK k hk)]
    calc Real.sqrt (Formalism.REAL.hs (NormedSpace.exp X))
        ≤ Real.sqrt ((Real.sqrt n * Real.exp (Real.sqrt (Formalism.REAL.hs X))) ^ 2) :=
          Real.sqrt_le_sqrt (hs_exp_le X)
      _ = Real.sqrt n * Real.exp (Real.sqrt (Formalism.REAL.hs X)) := Real.sqrt_sq (by positivity)
  show hsN (Formalism.MainNotions.S.uMat g) ≤ Real.sqrt n * Real.exp (sInf S)
  by_contra hlt
  push_neg at hlt
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have h0 : hsN (Formalism.MainNotions.S.uMat g) = 0 := by
      unfold hsN Formalism.REAL.hs
      simp
    rw [h0] at hlt
    simp at hlt
  · have hsqpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hnpos)
    set a := hsN (Formalism.MainNotions.S.uMat g) with ha
    have hapos : 0 < a := lt_of_le_of_lt (by positivity) hlt
    have h1 : sInf S < Real.log (a / Real.sqrt n) := by
      rw [Real.lt_log_iff_exp_lt (div_pos hapos hsqpos), lt_div_iff₀ hsqpos, mul_comm]
      exact hlt
    obtain ⟨t, htS, htlt⟩ := exists_lt_of_csInf_lt hne h1
    have h2 := hbound t htS
    have h3 : Real.exp t < a / Real.sqrt n := by
      rw [← Real.exp_log (div_pos hapos hsqpos)]
      exact Real.exp_lt_exp.mpr htlt
    rw [lt_div_iff₀ hsqpos] at h3
    linarith

end PI.UnitaryGroupMassFormula.LCG
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.LatCountAllOf
noncomputable section

open NumberField Matrix

namespace PI.UnitaryGroupMassFormula.LCG

open PI.LatCountG

theorem hsN_zero {n : ℕ} : hsN (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  simp [hsN, Formalism.REAL.hs]

theorem hsN_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hsN A := Real.sqrt_nonneg _

theorem mem_gf (I : Formalism.MainNotions.S.AutInst) (γ : I.GFset) :
    ∃ g : GL (Fin I.n) I.E, g ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧
      (∀ v, Formalism.MainNotions.S.uMat ((γ : I.GA).1 v) = (I.P v)⁻¹ * (g : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) ∧
      I.fmat (γ : I.GA).2 = (g : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) := γ.2

def gm (I : Formalism.MainNotions.S.AutInst) (γ : I.GFset) : Matrix (Fin I.n) (Fin I.n) I.E :=
  (((mem_gf I γ).choose : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E)

theorem gm_spec (I : Formalism.MainNotions.S.AutInst) (γ : I.GFset) :
    (∀ v, Formalism.MainNotions.S.uMat ((γ : I.GA).1 v) = (I.P v)⁻¹ * (gm I γ).map (I.φ v) * I.P v) ∧
      I.fmat (γ : I.GA).2 = (gm I γ).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) := (mem_gf I γ).choose_spec.2

theorem gm_inj (I : Formalism.MainNotions.S.AutInst) {γ γ' : I.GFset} (h : gm I γ = gm I γ') : γ = γ' := by
  obtain ⟨h1a, h1b⟩ := gm_spec I γ
  obtain ⟨h2a, h2b⟩ := gm_spec I γ'
  rw [h] at h1a h1b
  apply Subtype.ext
  refine Prod.ext (funext fun v => ?_) ?_
  · exact Subtype.ext (Units.ext ((h1a v).trans (h2a v).symm))
  · exact Subtype.ext (Units.ext (h1b.trans h2b.symm))

theorem phi_eq (I : Formalism.MainNotions.S.AutInst) (x y : I.GA) (γ : I.GFset) (v : InfinitePlace I.F) :
    Formalism.MainNotions.S.uMat ((x⁻¹ * (γ : I.GA) * y).1 v) = amat I x y v (gm I γ) := by
  obtain ⟨h1, -⟩ := gm_spec I γ
  rw [amat, ← h1 v]
  simp only [Formalism.MainNotions.S.uMat, Prod.fst_mul, Prod.fst_inv, Pi.mul_apply, Pi.inv_apply, Subgroup.coe_mul,
    Units.val_mul]

theorem amat_sub (I : Formalism.MainNotions.S.AutInst) (x y : I.GA) (v : InfinitePlace I.F) (δ₁ δ₂ : Matrix (Fin I.n) (Fin I.n) I.E) :
    amat I x y v (δ₁ - δ₂) = amat I x y v δ₁ - amat I x y v δ₂ := by
  have hm : (δ₁ - δ₂).map (I.φ v) = δ₁.map (I.φ v) - δ₂.map (I.φ v) := by
    ext i j; simp
  simp only [amat, hm, mul_sub, sub_mul]

theorem latCountAll_of (hB : BoxBound) (hLM : LatMap) (hLS : LatSub) (hS : Sep) (hP : PackLem) (hN : NPos)
    (hC : CardPl) : LatCountAll := by
  classical
  intro I x y hx hy r hr S hSc
  have hn : 1 ≤ I.n := hN I x hx
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, ρ = PI.LatCountG.tau1 I x * PI.LatCountG.tau1 I y := ⟨_, rfl⟩
  rw [← hρdef]
  have hρ : 0 < ρ := by rw [hρdef]; exact mul_pos hx hy
  have hτx : PI.LatCountG.tau1 I x ≤ 1 / 2 := by unfold PI.LatCountG.tau1; exact min_le_left _ _
  have hτy : PI.LatCountG.tau1 I y ≤ 1 / 2 := by unfold PI.LatCountG.tau1; exact min_le_left _ _
  have hρle : ∀ v, ρ ≤ Real.sqrt I.n * Real.exp (r v) := fun v => by
    have h0 : ρ ≤ 1 / 2 * (1 / 2) := by rw [hρdef]; exact mul_le_mul hτx hτy hy.le (by norm_num)
    have h2 : (1 : ℝ) ≤ Real.sqrt I.n := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
    have h3 : (1 : ℝ) ≤ Real.exp (r v) := Real.one_le_exp (hr v)
    nlinarith
  let g : I.GFset → (InfinitePlace I.F → Matrix (Fin I.n) (Fin I.n) ℂ) :=
    fun γ v => amat I x y v (gm I γ)
  have hgsub : ∀ γ γ' : I.GFset, ∀ v, g γ v - g γ' v = amat I x y v (gm I γ - gm I γ') :=
    fun γ γ' v => (amat_sub I x y v _ _).symm
  have hlat : ∀ γ ∈ S, ∀ u ∈ PI.LatCountG.latSet I y, gm I γ *ᵥ u ∈ PI.LatCountG.latSet I x :=
    fun γ hγ u hu => hLM I x y γ (mem_gf I γ).choose (gm_spec I γ).2 (hSc γ hγ).1 u hu
  have hsep : ∀ γ ∈ S, ∀ γ' ∈ S, gm I γ ≠ gm I γ' → ∃ v, ρ ≤ hsN (g γ v - g γ' v) := by
    intro γ hγ γ' hγ' hne
    have hδ : gm I γ - gm I γ' ≠ 0 := sub_ne_zero.mpr hne
    have hmap : ∀ u ∈ PI.LatCountG.latSet I y,
        (gm I γ - gm I γ') *ᵥ u ∈ PI.LatCountG.latSet I x := by
      intro u hu
      rw [Matrix.sub_mulVec]
      exact hLS I x _ _ (hlat γ hγ u hu) (hlat γ' hγ' u hu)
    have hineq := hS I x y hx hy _ hδ hmap
    rw [← hρdef] at hineq
    by_contra hcon
    push_neg at hcon
    have hprod : ∏ v, hsN (g γ v - g γ' v) < ρ ^ I.f := by
      rw [← hC I, ← Finset.card_univ, ← Finset.prod_const]
      by_cases h0 : ∃ v, hsN (g γ v - g γ' v) = 0
      · obtain ⟨v, hv⟩ := h0
        rw [Finset.prod_eq_zero (Finset.mem_univ v) hv]
        exact Finset.prod_pos fun _ _ => hρ
      · push_neg at h0
        have hne' : (Finset.univ : Finset (InfinitePlace I.F)).Nonempty := by
          by_contra he
          rw [Finset.not_nonempty_iff_eq_empty, Finset.univ_eq_empty_iff] at he
          have hf0 : I.f = 0 := by rw [← hC I]; exact Fintype.card_eq_zero
          have hpos : 0 < I.f := by
            first
              | exact (hC I) ▸ Fintype.card_pos
              | unfold Formalism.MainNotions.S.AutInst.f; exact Module.finrank_pos
          omega
        exact Finset.prod_lt_prod_of_nonempty₀
          (fun v _ => lt_of_le_of_ne (hsN_nonneg _) (h0 v).symm) (fun v _ => hcon v) hne'
    simp only [hgsub] at hprod
    linarith
  have hinj : Set.InjOn g S := by
    intro γ hγ γ' hγ' heq
    by_contra hne
    obtain ⟨v, hv⟩ := hsep γ hγ γ' hγ' (fun h => hne (gm_inj I h))
    rw [heq, sub_self, hsN_zero] at hv
    linarith
  have hbound : ∀ p ∈ S.image g, ∀ v, hsN (p v) ≤ Real.sqrt I.n * Real.exp (r v) := by
    intro p hp v
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
    show hsN (amat I x y v (gm I γ)) ≤ _
    rw [← phi_eq]
    refine (hB I.n (I.ε v) ((x⁻¹ * (γ : I.GA) * y).1 v)).trans ?_
    gcongr
    exact (hSc γ hγ).2 v
  have hsepT : ∀ p ∈ S.image g, ∀ q ∈ S.image g, p ≠ q → ∃ v, ρ ≤ hsN (p v - q v) := by
    intro p hp q hq hpq
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨γ', hγ', rfl⟩ := Finset.mem_image.mp hq
    exact hsep γ hγ γ' hγ' (fun h => hpq (by simp only [g, h]))
  have hpack := hP (InfinitePlace I.F) I.n (fun v => Real.sqrt I.n * Real.exp (r v)) (fun _ => ρ)
    (fun _ => hρ) (fun v => by positivity) (S.image g) hbound hsepT
  have hexp : ∏ v, Real.exp (r v) ^ (2 * I.n ^ 2) = Real.exp (2 * (I.n : ℝ) ^ 2 * ∑ v, r v) := by
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hnn : ∀ v, 0 ≤ 2 * (Real.sqrt I.n * Real.exp (r v)) + ρ := fun v => by
    have := Real.sqrt_nonneg (I.n : ℝ)
    have := Real.exp_pos (r v)
    nlinarith
  calc (S.card : ℝ) = ((S.image g).card : ℝ) := by rw [Finset.card_image_of_injOn hinj]
    _ ≤ ∏ v, ((2 * (Real.sqrt I.n * Real.exp (r v)) + ρ) / ρ) ^ (2 * I.n ^ 2) := hpack
    _ ≤ ∏ v, ((3 * Real.sqrt I.n / ρ) * Real.exp (r v)) ^ (2 * I.n ^ 2) := by
        refine Finset.prod_le_prod₀ (fun v _ => pow_nonneg (div_nonneg (hnn v) hρ.le) _)
          (fun v _ => ?_)
        refine pow_le_pow_left₀ (div_nonneg (hnn v) hρ.le) ?_ _
        rw [div_mul_eq_mul_div]
        gcongr
        nlinarith [hρle v]
    _ = (∏ v : InfinitePlace I.F, (3 * Real.sqrt I.n / ρ) ^ (2 * I.n ^ 2)) *
          ∏ v, Real.exp (r v) ^ (2 * I.n ^ 2) := by
        rw [← Finset.prod_mul_distrib]; simp_rw [mul_pow]
    _ = _ := by rw [hexp, Finset.prod_const, Finset.card_univ, hC I, ← pow_mul]

end PI.UnitaryGroupMassFormula.LCG
end
end

noncomputable section

namespace PI.UnitaryGroupMassFormula.LCG

theorem latCountAll_of_steps (hB : BoxBound) (hP : PackLem) (hD : DualIncl) (hCh : Choose) (hA : ArchIneq)
    (hAP : ArchPlaceOf) (hI : IndexIneq) : PI.LatCountG.LatCountAll :=
  latCountAll_of hB lattice_map_image sublattice_of_lattice
    (separation_of_points lattice_is_discrete_group hD hCh (hAP hA) hI PI.UnitaryGroupMassFormula.LSC.norm_product_formula PI.UnitaryGroupMassFormula.LSC.determinant_monotone card_places_bound)
    hP norm_positive card_places_bound

theorem latCountAll_of_open (hD : DualIncl) (hCh : Choose) (hAP : ArchPlaceOf) (hI : IndexIneq) :
    PI.LatCountG.LatCountAll :=
  latCountAll_of_steps box_lattice_point_bound lattice_packLem hD hCh archimedean_inequality hAP hI

theorem latCountAll_of_open2 (hAP : ArchPlaceOf) (hI : IndexIneq) : PI.LatCountG.LatCountAll :=
  latCountAll_of_open dual_lattice_inclusion choice_of_generators hAP hI

theorem latCountAll_of_index (hI : IndexIneq) : PI.LatCountG.LatCountAll :=
  latCountAll_of_open2 archimedean_place_exists hI

theorem latCountAll_of_idx (hD2 : DetIdx) (hIO : IndexOf) : PI.LatCountG.LatCountAll :=
  latCountAll_of_index (hIO dual_index_formula hD2)

end PI.UnitaryGroupMassFormula.LCG
