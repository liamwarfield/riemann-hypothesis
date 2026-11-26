module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QCoreH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Hadamard

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.GlobQuotPf
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.GlobQuotH
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

lemma unzero_toAdd_eq_log (y : WithZero (Multiplicative ℤ)) (hy : y ≠ 0) :
    (WithZero.unzero hy).toAdd = WithZero.log y := by
  induction y using WithZero.recZeroCoe with
  | zero => exact absurd rfl hy
  | coe a => rfl

lemma norm_emb_eq (v : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    ‖FinitePlace.embedding v x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(ordAt v x)) := by
  have hv : v.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  have h1 : Valued.v (FinitePlace.embedding v x) = v.valuation K x :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  rw [FinitePlace.norm_def, h1, WithZeroMulInt.toNNReal_neg_apply _ hv, ordAt, neg_neg]
  push_cast
  rfl

lemma one_lt_absNorm_real (v : HeightOneSpectrum (𝓞 K)) : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

lemma log_norm_emb (v : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    Real.log ‖FinitePlace.embedding v x‖ = -((ordAt v x : ℝ) * logN v) := by
  rw [norm_emb_eq v hx, Real.log_zpow, logN]
  push_cast
  ring

lemma finite_mulSupport_emb {x : K} (hx : x ≠ 0) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => ‖FinitePlace.embedding v x‖).Finite := by
  have h : (Function.mulSupport fun w : FinitePlace K => w x).Finite :=
    NumberField.FinitePlace.hasFiniteMulSupport hx
  refine (h.image FinitePlace.maximalIdeal).subset ?_
  intro v hv
  refine ⟨FinitePlace.mk v, ?_, FinitePlace.maximalIdeal_mk v⟩
  simpa [Function.mem_mulSupport, FinitePlace.mk_apply] using hv

lemma support_ordAt_sub {x : K} (hx : x ≠ 0) :
    (Function.support fun v : HeightOneSpectrum (𝓞 K) => (ordAt v x : ℝ) * logN v) ⊆
      Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => ‖FinitePlace.embedding v x‖ := by
  intro v hv
  rw [Function.mem_support] at hv
  rw [Function.mem_mulSupport]
  intro h
  apply hv
  have h2 := log_norm_emb v hx
  rw [h, Real.log_one] at h2
  linarith

lemma finite_ordAt {x : K} (hx : x ≠ 0) :
    (Function.support fun v : HeightOneSpectrum (𝓞 K) => (ordAt v x : ℝ) * logN v).Finite :=
  (finite_mulSupport_emb hx).subset (support_ordAt_sub hx)

lemma finsum_ordAt {x : K} (hx : x ≠ 0) :
    ∑ᶠ v : HeightOneSpectrum (𝓞 K), (ordAt v x : ℝ) * logN v =
      ∑ σ : InfinitePlace K, (σ.mult : ℝ) * Real.log (σ x) := by
  have hfin : (Function.mulSupport fun w : FinitePlace K => w x).Finite :=
    NumberField.FinitePlace.hasFiniteMulSupport hx
  have hprod := NumberField.prod_abs_eq_one hx
  have hA : 0 < ∏ w : InfinitePlace K, w x ^ w.mult :=
    Finset.prod_pos fun w _ => pow_pos (InfinitePlace.pos_iff.2 hx) _
  set s := hfin.toFinset with hs
  have hBs : ∏ᶠ w : FinitePlace K, w x = ∏ w ∈ s, w x :=
    finprod_eq_prod_of_mulSupport_subset _ (by simp [s])
  have hB : 0 < ∏ w ∈ s, w x := Finset.prod_pos fun w _ => FinitePlace.pos_iff.2 hx
  rw [hBs] at hprod
  have hlog := congrArg Real.log hprod
  rw [Real.log_mul hA.ne' hB.ne', Real.log_one,
    Real.log_prod (fun w _ => (pow_pos (InfinitePlace.pos_iff.2 hx) _).ne'),
    Real.log_prod (fun w _ => (FinitePlace.pos_iff.2 hx).ne')] at hlog
  simp only [Real.log_pow] at hlog
  have hfs : ∑ w ∈ s, Real.log (w x) = ∑ᶠ w : FinitePlace K, Real.log (w x) := by
    rw [finsum_eq_sum_of_support_subset]
    intro w hw
    simp only [Function.mem_support] at hw
    simp only [s, Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h1
    apply hw
    rw [h1, Real.log_one]
  have heq : ∑ᶠ w : FinitePlace K, Real.log (w x) =
      -∑ᶠ v : HeightOneSpectrum (𝓞 K), (ordAt v x : ℝ) * logN v := by
    rw [← finsum_neg_distrib, ← finsum_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    refine finsum_congr fun v => ?_
    have h3 : (FinitePlace.equivHeightOneSpectrum.symm v) x = ‖FinitePlace.embedding v x‖ := by
      rw [← FinitePlace.mk_apply]
      rfl
    rw [h3, log_norm_emb v hx]
  linarith

lemma log_det_le {ρ : ℕ} (m : Matrix (Fin ρ) (Fin ρ) K) (hdet : m.det ≠ 0) (σ : InfinitePlace K)
    (a b : Fin ρ → ℝ) (harch : ∀ i j, m i j ≠ 0 → Real.log (σ (m i j)) + a i ≤ b j) :
    Real.log (σ m.det) ≤ ∑ j, b j - ∑ i, a i + (ρ : ℝ) / 2 * Real.log ρ := by
  rcases Nat.eq_zero_or_pos ρ with rfl | hρ
  · simp [Matrix.det_fin_zero]
  have hpos : 0 < σ m.det := InfinitePlace.pos_iff.2 hdet
  let A : Matrix (Fin ρ) (Fin ρ) ℂ := fun i j => (Real.exp (a i) : ℂ) * σ.embedding (m i j)
  have hAdet : A.det = (∏ i, (Real.exp (a i) : ℂ)) * σ.embedding m.det := by
    have h : A = Matrix.diagonal (fun i => (Real.exp (a i) : ℂ)) * (σ.embedding.mapMatrix m) := by
      ext i j
      simp [A, Matrix.diagonal_mul]
    rw [h, Matrix.det_mul, Matrix.det_diagonal, ← RingHom.map_det]
  have hnormA : ‖A.det‖ = Real.exp (∑ i, a i) * σ m.det := by
    rw [hAdet, norm_mul, norm_prod, InfinitePlace.norm_embedding_eq, Real.exp_sum]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hentry : ∀ i j, ‖A i j‖ ≤ Real.exp (b j) := by
    intro i j
    by_cases h : m i j = 0
    · simp [A, h, (Real.exp_pos _).le]
    · have hp : 0 < σ (m i j) := InfinitePlace.pos_iff.2 h
      have h2 := harch i j h
      simp only [A, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        InfinitePlace.norm_embedding_eq]
      calc Real.exp (a i) * σ (m i j) = Real.exp (a i + Real.log (σ (m i j))) := by
            rw [Real.exp_add, Real.exp_log hp]
        _ ≤ Real.exp (b j) := Real.exp_le_exp.2 (by linarith)
  have hcol : ∀ j, Real.sqrt (∑ i, ‖A i j‖ ^ 2) ≤ Real.sqrt ρ * Real.exp (b j) := by
    intro j
    rw [← Real.sqrt_sq (Real.exp_pos (b j)).le, ← Real.sqrt_mul (Nat.cast_nonneg _)]
    apply Real.sqrt_le_sqrt
    calc ∑ i, ‖A i j‖ ^ 2 ≤ ∑ _i : Fin ρ, Real.exp (b j) ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hentry i j) 2
      _ = ρ * Real.exp (b j) ^ 2 := by simp
  have hH := ReciprocityTheory.ChartRestriction.G.T0.hadamard_det_le A.transpose
  rw [Matrix.det_transpose, hnormA] at hH
  simp only [Matrix.transpose_apply] at hH
  have hprod : ∏ j, Real.sqrt (∑ i, ‖A i j‖ ^ 2) ≤ ∏ j : Fin ρ, (Real.sqrt ρ * Real.exp (b j)) :=
    Finset.prod_le_prod₀ (fun j _ => Real.sqrt_nonneg _) fun j _ => hcol j
  have key : Real.exp (∑ i, a i) * σ m.det ≤ Real.sqrt ρ ^ ρ * Real.exp (∑ j, b j) := by
    calc _ ≤ _ := hH
      _ ≤ _ := hprod
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          Real.exp_sum]
  have hs : 0 < Real.sqrt ρ := Real.sqrt_pos.2 (by exact_mod_cast hρ)
  have h1 := Real.log_le_log (mul_pos (Real.exp_pos _) hpos) key
  rw [Real.log_mul (Real.exp_pos _).ne' hpos.ne', Real.log_exp,
    Real.log_mul (pow_pos hs _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_pow,
    Real.log_sqrt (Nat.cast_nonneg _)] at h1
  linarith

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open NumberField

theorem globalQuot_holds : GlobalQuotStatement := by
  intro K _ _ ρ m hdet s β a b B Bfin hs hβ harch hdeg hfin
  classical
  set n : ℝ := (Module.finrank ℚ K : ℝ) with hn
  have hnpos : 0 < n := by rw [hn]; exact_mod_cast Module.finrank_pos
  have hsum : ∑ σ : InfinitePlace K, (σ.mult : ℝ) = n := by
    rw [hn]; exact_mod_cast InfinitePlace.sum_mult_eq
  have hord := finite_ordAt (K := K) hdet
  have hsU : (⋃ i, Function.support (s i)).Finite := Set.finite_iUnion hs
  set T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
    (hord.union (hsU.union hβ)).toFinset with hT
  have memT : ∀ w, w ∈ (Function.support fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) => (ordAt v m.det : ℝ) * logN v) ∪
      ((⋃ i, Function.support (s i)) ∪ Function.support β) → w ∈ T := by
    intro w hw; rw [hT, Set.Finite.mem_toFinset]; exact hw
  have e1 : ∑ᶠ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K), (ordAt w m.det : ℝ) * logN w = ∑ w ∈ T, (ordAt w m.det : ℝ) * logN w := by
    apply finsum_eq_sum_of_support_subset
    intro w hw; exact memT w (Or.inl hw)
  have e2 : ∀ i, ∑ᶠ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K), s i w * logN w = ∑ w ∈ T, s i w * logN w := by
    intro i; apply finsum_eq_sum_of_support_subset
    intro w hw
    simp only [Function.mem_support, ne_eq] at hw
    refine memT w (Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨i, fun h => hw ?_⟩)))
    rw [h, zero_mul]
  have e3 : ∑ᶠ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K), β w * logN w = ∑ w ∈ T, β w * logN w := by
    apply finsum_eq_sum_of_support_subset
    intro w hw
    simp only [Function.mem_support, ne_eq] at hw
    refine memT w (Or.inr (Or.inr fun h => hw ?_))
    rw [h, zero_mul]
  have e0 : ∑ᶠ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K), ((ordAt w m.det : ℝ) + ∑ i, s i w + ρ * β w) * logN w =
      ∑ w ∈ T, ((ordAt w m.det : ℝ) + ∑ i, s i w + ρ * β w) * logN w := by
    apply finsum_eq_sum_of_support_subset
    intro w hw
    simp only [Function.mem_support, ne_eq] at hw
    by_contra hnot
    apply hw
    have h1 : (ordAt w m.det : ℝ) * logN w = 0 := by
      by_contra h; exact hnot (memT w (Or.inl h))
    have h2 : ∀ i, s i w = 0 := fun i => by
      by_contra h; exact hnot (memT w (Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨i, h⟩))))
    have h3 : β w = 0 := by
      by_contra h; exact hnot (memT w (Or.inr (Or.inr h)))
    rw [add_mul, add_mul, h1]
    simp [h2, h3]

  have hPF : ∑ w ∈ T, (ordAt w m.det : ℝ) * logN w =
      ∑ σ : InfinitePlace K, (σ.mult : ℝ) * Real.log (σ m.det) := by
    rw [← e1]; exact finsum_ordAt hdet
  have hHad : ∀ σ : InfinitePlace K, Real.log (σ m.det) ≤
      ∑ j, b j σ - ∑ i, a i σ + (ρ : ℝ) / 2 * Real.log ρ := fun σ =>
    log_det_le m hdet σ (fun i => a i σ) (fun j => b j σ) fun i j h => harch σ i j h
  have hsumσ : ∑ σ : InfinitePlace K, (σ.mult : ℝ) * Real.log (σ m.det) ≤
      ∑ σ : InfinitePlace K, (σ.mult : ℝ) * (∑ j, b j σ - ∑ i, a i σ + (ρ : ℝ) / 2 * Real.log ρ) :=
    Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (hHad σ) (Nat.cast_nonneg _)
  have hexp : ∑ σ : InfinitePlace K, (σ.mult : ℝ) * (∑ j, b j σ - ∑ i, a i σ + (ρ : ℝ) / 2 * Real.log ρ) =
      ∑ j, ∑ σ : InfinitePlace K, (σ.mult : ℝ) * b j σ -
        ∑ i, ∑ σ : InfinitePlace K, (σ.mult : ℝ) * a i σ + n * ((ρ : ℝ) / 2 * Real.log ρ) := by
    have c1 : ∑ σ : InfinitePlace K, ∑ j, (σ.mult : ℝ) * b j σ =
        ∑ j, ∑ σ : InfinitePlace K, (σ.mult : ℝ) * b j σ := Finset.sum_comm
    have c2 : ∑ σ : InfinitePlace K, ∑ i, (σ.mult : ℝ) * a i σ =
        ∑ i, ∑ σ : InfinitePlace K, (σ.mult : ℝ) * a i σ := Finset.sum_comm
    have c3 : ∑ σ : InfinitePlace K, (σ.mult : ℝ) * ((ρ : ℝ) / 2 * Real.log ρ) =
        n * ((ρ : ℝ) / 2 * Real.log ρ) := by rw [← Finset.sum_mul, hsum]
    rw [← c1, ← c2, ← c3, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [mul_add, mul_sub, Finset.mul_sum, Finset.mul_sum]

  have hdeg' : ∀ i, ∑ w ∈ T, s i w * logN w - ∑ σ : InfinitePlace K, (σ.mult : ℝ) * a i σ ≤ B i * n := by
    intro i
    have := hdeg i
    rw [e2 i, div_le_iff₀ hnpos] at this
    exact this
  have hdegS : ∑ i, ∑ w ∈ T, s i w * logN w - ∑ i, ∑ σ : InfinitePlace K, (σ.mult : ℝ) * a i σ ≤
      (∑ i, B i) * n := by
    rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => hdeg' i
  have hfin' : ∑ w ∈ T, β w * logN w ≤ Bfin * n := by
    have := hfin
    rw [e3, div_le_iff₀ hnpos] at this
    exact this
  have hfinρ : (ρ : ℝ) * ∑ w ∈ T, β w * logN w ≤ ρ * (Bfin * n) :=
    mul_le_mul_of_nonneg_left hfin' (Nat.cast_nonneg _)

  have hL : ∑ w ∈ T, ((ordAt w m.det : ℝ) + ∑ i, s i w + ρ * β w) * logN w =
      ∑ w ∈ T, (ordAt w m.det : ℝ) * logN w + ∑ i, ∑ w ∈ T, s i w * logN w +
        ρ * ∑ w ∈ T, β w * logN w := by
    have hw : ∀ w, ((ordAt w m.det : ℝ) + ∑ i, s i w + ρ * β w) * logN w =
        (ordAt w m.det : ℝ) * logN w + ∑ i, s i w * logN w + ρ * (β w * logN w) := fun w => by
      rw [add_mul, add_mul, Finset.sum_mul]; ring
    rw [Finset.sum_congr rfl fun w _ => hw w, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_comm]
  have hR : (∑ j, (∑ σ : InfinitePlace K, (σ.mult : ℝ) * b j σ) / n) * n =
      ∑ j, ∑ σ : InfinitePlace K, (σ.mult : ℝ) * b j σ := by
    rw [← Finset.sum_div, div_mul_cancel₀ _ hnpos.ne']
  rw [e0, hL, div_le_iff₀ hnpos, add_mul, add_mul, add_mul, hR]
  linarith [hPF, hsumσ, hexp, hdegS, hfinρ]

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open NumberField IsDedekindDomain
open scoped TensorProduct

section Mean

variable {K K₁ : Type*} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]

theorem sum_embeddings_restrict (g : (K →+* ℂ) → ℝ) :
    ∑ φ : K₁ →+* ℂ, g (φ.comp (algebraMap K K₁)) =
      (Module.finrank K K₁ : ℝ) * ∑ τ : K →+* ℂ, g τ := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun φ : K₁ →+* ℂ => φ.comp (algebraMap K K₁)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_congr rfl (fun φ hφ => by rw [(Finset.mem_filter.mp hφ).2]), Finset.sum_const,
    nsmul_eq_mul]
  congr 1
  norm_cast
  letI : Algebra K ℂ := τ.toAlgebra
  let eqv : {φ : K₁ →+* ℂ // φ.comp (algebraMap K K₁) = τ} ≃ (K₁ →ₐ[K] ℂ) :=
    { toFun := fun φ => { φ.1 with commutes' := fun r => RingHom.congr_fun φ.2 r }
      invFun := fun ψ => ⟨ψ.toRingHom, RingHom.ext fun r => ψ.commutes r⟩
      left_inv := fun φ => rfl
      right_inv := fun ψ => rfl }
  rw [← Fintype.card_subtype, Fintype.card_congr eqv, AlgHom.card]

theorem sum_places_restrict (g : (K →+* ℂ) → ℝ) (hg : ∀ τ, g ((starRingEnd ℂ).comp τ) = g τ) :
    ∑ σ : InfinitePlace K₁, (σ.mult : ℝ) * g (σ.embedding.comp (algebraMap K K₁)) =
      (Module.finrank K K₁ : ℝ) * ∑ τ : K →+* ℂ, g τ := by
  rw [← sum_embeddings_restrict g]
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun φ : K₁ →+* ℂ => InfinitePlace.mk φ)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hc : ∀ φ ∈ Finset.univ.filter (fun φ : K₁ →+* ℂ => InfinitePlace.mk φ = σ),
      g (φ.comp (algebraMap K K₁)) = g (σ.embedding.comp (algebraMap K K₁)) := by
    intro φ hφ
    have h1 := (Finset.mem_filter.mp hφ).2
    rw [← InfinitePlace.mk_embedding σ, InfinitePlace.mk_eq_iff] at h1
    rcases h1 with h1 | h1
    · rw [h1]
    · rw [← h1]
      have h2 : (ComplexEmbedding.conjugate φ).comp (algebraMap K K₁)
          = (starRingEnd ℂ).comp (φ.comp (algebraMap K K₁)) := RingHom.ext fun x => rfl
      rw [h2, hg]
  rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul, InfinitePlace.card_filter_mk_eq]

end Mean

section Regroup

variable {K K₁ : Type*} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]

noncomputable def under (w : HeightOneSpectrum (𝓞 K₁)) : HeightOneSpectrum (𝓞 K) where
  asIdeal := w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 K₁))
  isPrime := Ideal.IsPrime.comap _
  ne_bot := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)

theorem liesOver_iff_under (w : HeightOneSpectrum (𝓞 K₁)) (la : HeightOneSpectrum (𝓞 K)) :
    LiesOver w la ↔ under (K := K) w = la := by
  unfold LiesOver
  constructor
  · intro h
    exact HeightOneSpectrum.ext h
  · intro h
    subst h
    rfl

theorem logN_of_liesOver {w : HeightOneSpectrum (𝓞 K₁)} {la : HeightOneSpectrum (𝓞 K)}
    (h : LiesOver w la) : logN w = (w.asIdeal.inertiaDeg (𝓞 K) : ℝ) * logN la := by
  have : w.asIdeal.LiesOver la.asIdeal := ⟨by rw [Ideal.under_def]; exact h.symm⟩
  have hn := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal la.asIdeal la.isPrime la.ne_bot
  rw [Ideal.inertiaDeg'_eq_inertiaDeg] at hn
  simp only [logN, hn, Nat.cast_pow, Real.log_pow]

theorem finsum_regroup (F : HeightOneSpectrum (𝓞 K₁) → ℝ) (hF : (Function.support F).Finite) :
    (Function.support fun la : HeightOneSpectrum (𝓞 K) =>
        ∑ᶠ w : {w // LiesOver w la}, (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w.1).Finite ∧
    ∑ᶠ la : HeightOneSpectrum (𝓞 K),
        (∑ᶠ w : {w // LiesOver w la}, (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w.1) * logN la =
      ∑ᶠ w, F w * logN w := by
  classical
  set S := hF.toFinset
  set T : Finset (HeightOneSpectrum (𝓞 K)) := S.image under
  have hinner : ∀ la : HeightOneSpectrum (𝓞 K),
      ∑ᶠ w : {w // LiesOver w la}, (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w.1 =
        ∑ w ∈ S.filter (fun w => under (K := K) w = la),
          (w.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w := by
    intro la
    rw [finsum_eq_sum_of_support_subset _ (s := S.subtype (fun w => LiesOver w la)) ?_,
      Finset.sum_subtype_eq_sum_filter
        (fun w : HeightOneSpectrum (𝓞 K₁) => (w.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w)]
    · refine Finset.sum_congr ?_ fun _ _ => rfl
      ext w; simp [liesOver_iff_under]
    · intro w hw
      rw [Finset.mem_coe, Finset.mem_subtype, Set.Finite.mem_toFinset, Function.mem_support]
      intro h0
      exact hw (by simp [h0])
  have hsupp : (Function.support fun la : HeightOneSpectrum (𝓞 K) =>
      ∑ᶠ w : {w // LiesOver w la}, (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w.1) ⊆ T := by
    intro la hla
    rw [Function.mem_support, hinner] at hla
    obtain ⟨w, hw, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hla
    rw [Finset.mem_filter] at hw
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨w, hw.1, hw.2⟩)
  refine ⟨T.finite_toSet.subset hsupp, ?_⟩
  rw [finsum_eq_sum_of_support_subset _ (s := T) (fun la hla => hsupp (by
      intro h; apply hla; simp [h])),
    finsum_eq_sum_of_support_subset _ (s := S) (fun w hw => by
      simp only [Finset.mem_coe, Set.Finite.mem_toFinset, S]
      intro h; apply hw; simp [h])]
  simp_rw [hinner, Finset.sum_mul]
  rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := T) (g := under)
    (fun w hw => Finset.mem_image_of_mem _ hw)]
  refine Finset.sum_congr rfl fun la _ => Finset.sum_congr rfl fun w hw => ?_
  rw [Finset.mem_filter] at hw
  rw [logN_of_liesOver ((liesOver_iff_under w la).mpr hw.2)]
  ring

end Regroup

theorem qcoreGlobal_holds : QCoreGlobalStatement := by
  intro K K₁ V _ _ _ _ _ _ _ _ M ρ θ c hD s hs supN a Bθ Carch Bdeg hconj hmean harch hdeg
  classical
  set D := detCT c θ with hDdef
  let F : HeightOneSpectrum (𝓞 K₁) → ℝ := fun w => (ordAt w D : ℝ) + ∑ i, s i w
  have hordfin : (Function.support fun w : HeightOneSpectrum (𝓞 K₁) => (ordAt w D : ℝ)).Finite := by
    refine (finite_ordAt hD).subset fun w hw => ?_
    have hpos : (0 : ℝ) < logN w := Real.log_pos (one_lt_absNorm_real w)
    simp only [Function.mem_support] at hw ⊢
    exact mul_ne_zero hw hpos.ne'
  have hFfin : (Function.support F).Finite := by
    refine (hordfin.union (Set.finite_iUnion fun i => hs i)).subset fun w hw => ?_
    by_contra hnot
    simp only [Set.mem_union, Set.mem_iUnion, Function.mem_support, not_or, not_exists,
      not_not] at hnot
    apply hw
    simp [F, hnot.1, hnot.2]
  obtain ⟨hfinsupp, hregroup⟩ := finsum_regroup (K := K) F hFfin
  have hnn : ∀ la, nnFun (K := K) D s la =
      (∑ᶠ w : {w // LiesOver w la}, (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w.1) /
        (Module.finrank K K₁ : ℝ) := fun la => rfl
  have hK₁K : (0 : ℝ) < Module.finrank K K₁ := by
    have : Module.Finite K K₁ := Module.Finite.of_restrictScalars_finite ℚ K K₁
    exact_mod_cast Module.finrank_pos
  have hKQ : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have htower : (Module.finrank ℚ K₁ : ℝ) = Module.finrank ℚ K * Module.finrank K K₁ := by
    exact_mod_cast (Module.finrank_mul_finrank ℚ K K₁).symm
  refine ⟨hfinsupp.subset fun la hla => by
    rw [Function.mem_support, hnn] at hla
    intro h; apply hla; simp [h], ?_⟩

  have hsum : (∑ᶠ la : HeightOneSpectrum (𝓞 K), nnFun (K := K) D s la * logN la) =
      (∑ᶠ w, F w * logN w) / (Module.finrank K K₁ : ℝ) := by
    have hfin2 : (Function.support fun la : HeightOneSpectrum (𝓞 K) =>
        (∑ᶠ w : {w // LiesOver w la}, (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w.1) * logN la).Finite :=
      hfinsupp.subset fun la hla => by
        rw [Function.mem_support] at hla ⊢
        intro h; apply hla; rw [h, zero_mul]
    rw [← hregroup, div_eq_mul_inv, finsum_mul]
    refine finsum_congr fun la => ?_
    rw [hnn]; ring

  let m : Matrix (Fin ρ) (Fin ρ) K₁ := Matrix.of fun i j => c i ((1 : K₁) ⊗ₜ[K] ((θ j : M) : V))
  have hmD : m.det = D := rfl
  let b : Fin ρ → InfinitePlace K₁ → ℝ := fun j σ =>
    Real.log (supN (σ.embedding.comp (algebraMap K K₁)) ((θ j : M) : V)) + Carch
  have hG := globalQuot_holds K₁ ρ m (by rw [hmD]; exact hD) s (fun _ => 0) a b (fun _ => Bdeg) 0 hs
    (by simp) (fun σ i j hij => harch σ i j hij) hdeg (by simp)
  have hLHS : (∑ᶠ w, ((ordAt w m.det : ℝ) + ∑ i, s i w + (ρ : ℝ) * (fun _ => (0 : ℝ)) w) * logN w) =
      ∑ᶠ w, F w * logN w := finsum_congr fun w => by simp [F, hmD]
  rw [hLHS] at hG
  have hKQc : (Fintype.card (K →+* ℂ) : ℝ) = Module.finrank ℚ K := by
    exact_mod_cast Embeddings.card K ℂ
  have hbj : ∀ j, (∑ σ : InfinitePlace K₁, (σ.mult : ℝ) * b j σ) / (Module.finrank ℚ K₁ : ℝ) ≤
      Bθ + Carch := by
    intro j
    have e0 : ∀ σ : InfinitePlace K₁, (σ.mult : ℝ) * b j σ =
        (σ.mult : ℝ) * Real.log (supN (σ.embedding.comp (algebraMap K K₁)) ((θ j : M) : V)) +
          Carch * (σ.mult : ℝ) := fun σ => by simp only [b]; ring
    have e2 := sum_places_restrict (K := K) (K₁ := K₁)
      (fun τ => Real.log (supN τ ((θ j : M) : V))) (fun τ => by rw [hconj])
    have e3 : (∑ σ : InfinitePlace K₁, (σ.mult : ℝ)) = Module.finrank ℚ K₁ := by
      exact_mod_cast InfinitePlace.sum_mult_eq
    rw [Finset.sum_congr rfl (fun σ _ => e0 σ), Finset.sum_add_distrib, ← Finset.mul_sum, e2, e3]
    have hm := hmean j
    rw [hKQc] at hm
    have hsplit : ((Module.finrank K K₁ : ℝ) * ∑ τ : K →+* ℂ, Real.log (supN τ ((θ j : M) : V)) +
        Carch * (Module.finrank ℚ K₁ : ℝ)) / (Module.finrank ℚ K₁ : ℝ) =
        (∑ τ : K →+* ℂ, Real.log (supN τ ((θ j : M) : V))) / (Module.finrank ℚ K : ℝ) + Carch := by
      rw [htower]; field_simp
    rw [hsplit]; linarith
  have hsumj : ∑ j : Fin ρ, (∑ σ : InfinitePlace K₁, (σ.mult : ℝ) * b j σ) /
      (Module.finrank ℚ K₁ : ℝ) ≤ (ρ : ℝ) * (Bθ + Carch) := by
    calc _ ≤ ∑ _j : Fin ρ, (Bθ + Carch) := Finset.sum_le_sum fun j _ => hbj j
      _ = (ρ : ℝ) * (Bθ + Carch) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hBdeg : ∑ _i : Fin ρ, Bdeg = (ρ : ℝ) * Bdeg := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hBdeg] at hG
  rw [hsum, div_div, mul_comm (Module.finrank K K₁ : ℝ), ← htower]
  nlinarith [hG, hsumj]

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
