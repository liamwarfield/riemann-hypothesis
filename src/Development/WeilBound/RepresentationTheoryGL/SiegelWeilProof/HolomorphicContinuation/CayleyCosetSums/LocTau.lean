module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.RhoPSmul
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Lagr
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.GaussM
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Crux

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.LamTrace
noncomputable section

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.LoweringDerivative

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Main

variable {Kg : Type} [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg]
  [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι)
  (hK : ∀ g, InK g ↔ ∃ k, ι k = g) (m : ℕ) (e : ℤ) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : Continuous ψ)
  (hψc : HasCompactSupport ψ) {a b : M2 n} (ha : InG a) (hb : InG b)

include hι hK hψ hψc ha hb in
theorem Lam_trace (z : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    abelian₂ μ ι m e ψ a b z X = abelian₂ μ ι m e ψ a b z 1 / n * star X.trace := by
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun Y => star (abelian₂ μ ι m e ψ a b z Y)
      map_add' := fun Y W => by simp [Lam_add μ ι hι hK m e hψ hψc ha hb]
      map_smul' := fun c Y => by simp [Lam_smul, mul_comm] }
  have h := inv_trace L (fun U Y hU hY => by
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, Lam_inv μ ι hK m e ha hb z hU hY]) X
  simp only [L, LinearMap.coe_mk, AddHom.coe_mk] at h
  have h' := congrArg star h
  rw [star_star] at h'
  rw [h']
  simp [star_div₀, mul_comm]

include hι hK hψ hψc ha hb in
theorem Lam_diff : Differentiable ℂ fun z => abelian₂ μ ι m e ψ a b z 1 := by
  have hιK : ∀ k, InK (ι k) := ιK ι hK
  have hιG : ∀ k, InG (ι k) := fun k => (hιK k).1
  have hb21 : Continuous fun x : M2 n => toBlocks₂₁ x :=
    continuous_pi fun i => continuous_pi fun j =>
      (continuous_apply (Sum.inl j)).comp (continuous_apply (Sum.inr i))
  have hb22 : Continuous fun x : M2 n => toBlocks₂₂ x :=
    continuous_pi fun i => continuous_pi fun j =>
      (continuous_apply (Sum.inr j)).comp (continuous_apply (Sum.inr i))
  have hu1 : Continuous fun x : M2 n => u1 x := by
    show Continuous fun x : M2 n => Complex.I • toBlocks₂₁ x + toBlocks₂₂ x
    exact (hb21.const_smul Complex.I).add hb22
  have hu2 : Continuous fun x : M2 n => u2 x := by
    show Continuous fun x : M2 n => -(Complex.I • toBlocks₂₁ x) + toBlocks₂₂ x
    exact (hb21.const_smul Complex.I).neg.add hb22
  have hR : (rhoP ⇑ι m e 1) = fun k =>
      star ((det (ι k) ^ e * (u1 (ι k)).det ^ (-(m : ℤ))) * ((u2 (ι k))ᴴ * u1 (ι k)).trace) := by
    funext k
    rw [rhoP, Matrix.mul_one, Matrix.inv_eq_left_inv (second_cayley_block_compact_unitary (hιK k))]
    simp [fz]
  have hRc : Continuous (rhoP ⇑ι m e 1) := by
    rw [hR]
    refine Continuous.star (Continuous.mul (Continuous.mul ?_ ?_) ?_)
    · exact hι.matrix_det.zpow₀ e fun k => Or.inl (LoweringDerivative.isUnit_det_of_inG (hιG k)).ne_zero
    · exact (hu1.comp hι).matrix_det.zpow₀ _ fun k => Or.inl (det_first_block_ne_zero_group (hιG k))
    · exact (((hu2.comp hι).matrix_conjTranspose).matrix_mul (hu1.comp hι)).matrix_trace
  have hH : Continuous fun p : Kg × ℂ => Hf m e ψ a b p.2 (ι p.1) := by
    have h1 := continuous_Hf m e hψ hψc ha hb
    refine h1.comp (f := fun p : Kg × ℂ => ((⟨ι p.1, hιG p.1⟩ : Gs n), p.2)) ?_
    refine Continuous.prodMk ?_ continuous_snd
    refine Continuous.subtype_mk ?_ _
    exact hι.comp continuous_fst
  set G : Kg → ℂ → ℂ := fun k w => rhoP ⇑ι m e 1 k * Hf m e ψ a b w (ι k) with hGdef
  have hG : Continuous (Function.uncurry G) := (hRc.comp continuous_fst).mul hH
  have hGd : ∀ k, Differentiable ℂ (G k) := fun k =>
    (differentiable_Hf m e hψ hψc ha hb (hιG k)).const_mul _
  have hLam : (fun z => abelian₂ μ ι m e ψ a b z 1) = fun z => ∫ k, G k z ∂μ := by
    funext z
    rw [Lam_eq]
  rw [hLam]
  intro z0
  obtain ⟨C, hC⟩ := (isCompact_univ.prod (isCompact_closedBall z0 2)).exists_bound_of_continuousOn
    hG.continuousOn
  have hbd : ∀ k, ∀ z ∈ Metric.ball z0 1, ‖deriv (G k) z‖ ≤ C := by
    intro k z hz
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := z) (R := 1) (C := C) one_pos
      (hGd k).diffContOnCl (fun w hw => by
        apply hC (k, w)
        refine ⟨Set.mem_univ _, ?_⟩
        rw [Metric.mem_closedBall]
        rw [Metric.mem_sphere] at hw
        rw [Metric.mem_ball] at hz
        linarith [dist_triangle w z z0])
    simpa using this
  have hmeas : Measurable fun k => deriv (G k) z0 :=
    by
    have hm := measurable_deriv_with_param (𝕜 := ℂ) (F := ℂ) (f := G) hG
    exact hm.comp (f := fun k : Kg => (k, z0)) (measurable_id.prodMk measurable_const)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := fun z k => G k z)
    (F' := fun z k => deriv (G k) z) (x₀ := z0) (bound := fun _ => C)
    (Metric.ball_mem_nhds z0 one_pos)
    (Filter.Eventually.of_forall fun z => (hG.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
    (integrable_integrand μ ι hι hK m e hψ hψc ha hb z0 1)
    hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun k z hz => hbd k z hz)
    (integrable_const C)
    (Filter.Eventually.of_forall fun k z _ => ((hGd k) z).hasDerivAt)
  exact key.2.differentiableAt

end Main

theorem lt2 : MultiplicityOneTestOperators := by
  intro n m e Kg _ _ _ _ _ _ μ _ ι hι hK ψ a b hψ hψc ha hb
  refine ⟨fun z => -(abelian₂ μ ι m e ψ a b z 1 / n), ?_, ?_⟩
  · exact ((Lam_diff μ ι hι hK m e hψ hψc ha hb).div_const _).neg
  · intro Y z x hx
    obtain ⟨p, k, hp, hk, hpk⟩ := AbsSt.iwa n (AbsSt.mkGR x hx)
    have hxe : x = mR p * mR k := by
      have h := congrArg mR hpk
      rw [AbsSt.mR_mkGR] at h
      rw [h]
      rfl
    obtain ⟨k1, hk1⟩ := (hK (mR k)).mp hk
    have hpG : InG (mR p) := p.2
    have hk1K : InK (ι k1) := hk1 ▸ hk
    rw [hxe, ← hk1, tOp_formula μ ι hK m e ψ ha hb hpG hp k1 Y z]
    change lam m e z (mR p) * fz m e 0 (ι k1) *
      abelian₂ μ ι m e ψ a b z (u2 (ι k1) * Y * (u1 (ι k1))⁻¹) = _
    rw [Lam_trace μ ι hι hK m e hψ hψc ha hb, eQ, fz_up hpG hp hk1K.1, Om_up hpG hp hk1K.1,
      fz_K m e z hk1K, Om_K hk1K, Matrix.inv_eq_left_inv (first_cayley_block_compact_unitary hk1K),
      Matrix.inv_eq_left_inv (second_cayley_block_compact_unitary hk1K)]
    have htr : star (u2 (ι k1) * Y * (u1 (ι k1))ᴴ).trace = ((u2 (ι k1))ᴴ * u1 (ι k1) * Yᴴ).trace := by
      rw [← Matrix.trace_conjTranspose, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
        ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
    rw [htr]
    simp only [Matrix.neg_mul, Matrix.mul_smul, Matrix.trace_neg, Matrix.trace_smul, smul_eq_mul,
      ← Matrix.mul_assoc]
    ring

end PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks

namespace PositivityTheory.Rg.Sw.HSt

theorem lt2 : MultiplicityOneTestOperators := CompactCayleyBlocks.lt2

end PositivityTheory.Rg.Sw.HSt
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.SingularTestsKillVacuum
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.EventuallyUnit
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DetFirstCayleyBlockNeGroup
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.VanishInv
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Imports
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.SecondCoordMulInner
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.InnerGen
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.TraceTransposeMul
noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR.G

variable {m n : ℕ}

theorem det_gram_eq_zero (hmn : m < n) (x : Fin m → Fin n → ℂ) : (gramX (fun _ : Fin m => true) x).det = 0 := by
  have hg : gramX (fun _ : Fin m => true) x = (Matrix.of x)ᴴ * Matrix.of x := by
    ext i j
    simp [gramX, evX, Qp, Qb, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hg]
  by_contra hne
  have hu : IsUnit ((Matrix.of x)ᴴ * Matrix.of x) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hne)
  have h1 := Matrix.rank_of_isUnit _ hu
  have h2 := Matrix.rank_mul_le_right (Matrix.of x)ᴴ (Matrix.of x)
  have h3 := Matrix.rank_le_height (Matrix.of x)
  simp only [Fintype.card_fin] at h1 h3
  omega

theorem trace_transpose_mul' (X Y : Matrix (Fin n) (Fin n) ℂ) : (Xᵀ * Y).trace = (Yᵀ * X).trace := by
  rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]

end PositivityTheory.Rg.Sw.HSt.L3
end
end

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR.G

variable {m n : ℕ}

theorem inner_gen (ψ : (Fin n → Fin n → ℝ) → ℂ) (hψ : IsSingTest ψ) (Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q.IsHermitian) (hd : Q.det = 0) :
    ∫ s, ψ s * Complex.exp (Complex.I * ((herm s)ᵀ * Q).trace) = 0 := by
  obtain ⟨_, _, h⟩ := hψ
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have h0 : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact_mod_cast h0
  have hβH : (((2 * (Real.pi : ℂ)))⁻¹ • Qᵀ).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, hQ.transpose.eq]
    congr 1
    simp [Complex.conj_ofReal]
  have hβd : (((2 * (Real.pi : ℂ)))⁻¹ • Qᵀ).det = 0 := by
    rw [Matrix.det_smul, Matrix.det_transpose, hd, mul_zero]
  have key := h _ hβH hβd
  rw [← key]
  congr 1
  ext s
  simp only [eTr]
  congr 2
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, trace_transpose_mul' (herm s) Q]
  field_simp

open PositivityTheory.Rg.Sw.WR.G.GM in
theorem core2 (hmn : m < n) (R : Matrix (Fin n) (Fin n) ℂ) (hR : IsUnit R.det) (H0 : Matrix (Fin n) (Fin n) ℂ)
    (hH : H0.IsHermitian) (ψ : (Fin n → Fin n → ℝ) → ℂ) (hψ : IsSingTest ψ) :
    ∫ s, ψ s * ((R * Rᴴ - Complex.I • (H0 + herm s)).det)⁻¹ ^ m = 0 := by
  have hψ0 := hψ
  obtain ⟨hψc, hψs, -⟩ := hψ0
  have hRR : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hR
  have hRRh : (R⁻¹)ᴴ * Rᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hRR, Matrix.conjTranspose_one]
  have hBH : ∀ s : Fin n → Fin n → ℝ, (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ).IsHermitian := by
    intro s
    have h := Matrix.isHermitian_conjTranspose_mul_mul (R⁻¹)ᴴ (hH.add (GM.herm_isHermitian s))
    rwa [Matrix.conjTranspose_conjTranspose] at h
  have hD : ∀ s : Fin n → Fin n → ℝ, (1 - Complex.I • (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ)).det ≠ 0 := by
    intro s
    have h := GM.det_ne_zero (hBH s) 1
    simpa using h
  have hfac : ∀ s : Fin n → Fin n → ℝ, R * Rᴴ - Complex.I • (H0 + herm s) =
      R * (1 - Complex.I • (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ)) * Rᴴ := by
    intro s
    have hM : R * (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ) * Rᴴ = H0 + herm s := by
      simp only [← Matrix.mul_assoc, hRR, Matrix.one_mul]
      rw [Matrix.mul_assoc, hRRh, Matrix.mul_one]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, hM]
  have hbase : ∀ s : Fin n → Fin n → ℝ, secN (fun _ : Fin m => true) 1 1 1 (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ) =
      ((Real.pi : ℂ) ^ n / (1 - Complex.I • (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ)).det) ^ m := by
    intro s
    have hA : ∀ a : Fin m, Amat (fun _ : Fin m => true) 1 1 (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ) a =
        (1 - Complex.I • (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ))ᵀ := by
      intro a
      simp [Amat, sgn, Matrix.transpose_sub, Matrix.transpose_smul]
    rw [base m n _ 1 1 one_pos _ (hBH s)]
    simp only [hA, Matrix.det_transpose, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hdR : R.det ≠ 0 := hR.ne_zero
  have hdRh : Rᴴ.det ≠ 0 := by
    rw [Matrix.det_conjTranspose]
    exact star_ne_zero.2 hdR
  have hπ : (Real.pi : ℂ) ^ n ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)
  have halg : ∀ (P D A B Y : ℂ), P ≠ 0 → D ≠ 0 → A ≠ 0 → B ≠ 0 →
      Y * (A * D * B)⁻¹ ^ m = (A * B * P)⁻¹ ^ m * (Y * (P / D) ^ m) := by
    intro P D A B Y hP hD' hA' hB'
    have k : (A * D * B)⁻¹ = (A * B * P)⁻¹ * (P / D) := by
      field_simp
    rw [k, mul_pow]
    ring
  have hpt : ∀ s : Fin n → Fin n → ℝ, ψ s * ((R * Rᴴ - Complex.I • (H0 + herm s)).det)⁻¹ ^ m =
      ((R.det * Rᴴ.det) * (Real.pi : ℂ) ^ n)⁻¹ ^ m *
        (ψ s * secN (fun _ : Fin m => true) 1 1 1 (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ)) := by
    intro s
    rw [hfac s, Matrix.det_mul, Matrix.det_mul, hbase s]
    exact halg _ _ _ _ _ hπ (hD s) hdR hdRh
  have hgi : Integrable (fun x : Fin m → Fin n → ℂ => evX (1 : PX m n) x * gs 1 x) volume :=
    integP m n 1 one_pos 1
  have hψi : Integrable ψ volume := hψc.integrable_of_hasCompactSupport hψs
  have hherm : Continuous (herm : (Fin n → Fin n → ℝ) → Matrix (Fin n) (Fin n) ℂ) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [herm]
    fun_prop
  have hint : Integrable (Function.uncurry fun (s : Fin n → Fin n → ℝ) (x : Fin m → Fin n → ℂ) =>
      ψ s * (evX (1 : PX m n) x * gs 1 x *
        Complex.exp (Complex.I * ((1 : ℝ) : ℂ) *
          (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x).trace)))
      (volume.prod volume) := by
    refine Integrable.mono' (hψi.norm.mul_prod hgi.norm) ?_ ?_
    · apply Continuous.aestronglyMeasurable
      have h1 : Continuous fun p : (Fin n → Fin n → ℝ) × (Fin m → Fin n → ℂ) =>
          R⁻¹ * (H0 + herm p.1) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) p.2 :=
        ((continuous_const.matrix_mul (continuous_const.add (hherm.comp continuous_fst))).matrix_mul
          continuous_const).matrix_mul ((continuous_gramX _).comp continuous_snd)
      exact (hψc.comp continuous_fst).mul ((((GM.continuous_evX 1).comp continuous_snd).mul
        ((GI.continuous_gs 1).comp continuous_snd)).mul
        (Complex.continuous_exp.comp (continuous_const.mul h1.matrix_trace)))
    · refine Filter.Eventually.of_forall fun p => le_of_eq ?_
      obtain ⟨s, x⟩ := p
      simp only [Function.uncurry_apply_pair, norm_mul]
      rw [GM.norm_phase (hBH s) x, mul_one]
  have hin : ∀ x : Fin m → Fin n → ℂ, ∫ s, ψ s * (evX (1 : PX m n) x * gs 1 x *
        Complex.exp (Complex.I * ((1 : ℝ) : ℂ) *
          (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x).trace)) = 0 := by
    intro x
    have hGH : ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)ᵀ.IsHermitian :=
      (Matrix.isHermitian_conjTranspose_mul_mul R⁻¹ (GM.gramX_isHermitian _ x)).transpose
    have hGd : ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)ᵀ.det = 0 := by
      rw [Matrix.det_transpose, Matrix.det_mul, Matrix.det_mul, det_gram_eq_zero hmn x, mul_zero, zero_mul]
    have htr : ∀ s : Fin n → Fin n → ℝ,
        (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x).trace =
          (H0 * ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)).trace +
          ((herm s)ᵀ * ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)ᵀ).trace := by
      intro s
      have h1 : (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x).trace =
          ((H0 + herm s) * ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)).trace := by
        simp only [Matrix.mul_assoc]
        rw [Matrix.trace_mul_comm R⁻¹]
        simp only [Matrix.mul_assoc]
      rw [h1, Matrix.add_mul, Matrix.trace_add]
      congr 1
      rw [← Matrix.trace_transpose (herm s * _), Matrix.transpose_mul, Matrix.trace_mul_comm]
    have hrw : ∀ s : Fin n → Fin n → ℝ, ψ s * (evX (1 : PX m n) x * gs 1 x *
        Complex.exp (Complex.I * ((1 : ℝ) : ℂ) *
          (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x).trace)) =
        (evX (1 : PX m n) x * gs 1 x *
          Complex.exp (Complex.I * (H0 * ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)).trace)) *
        (ψ s * Complex.exp (Complex.I *
          ((herm s)ᵀ * ((R⁻¹)ᴴ * gramX (fun _ : Fin m => true) x * R⁻¹)ᵀ).trace)) := by
      intro s
      rw [htr s, Complex.ofReal_one, mul_one, mul_add, Complex.exp_add]
      ring
    simp only [hrw]
    rw [integral_const_mul, inner_gen ψ hψ _ hGH hGd, mul_zero]
  have hmain : ∫ s, ψ s * secN (fun _ : Fin m => true) 1 1 1 (R⁻¹ * (H0 + herm s) * (R⁻¹)ᴴ) = 0 := by
    simp only [secN]
    simp only [← integral_const_mul]
    rw [integral_integral_swap hint]
    simp only [hin, integral_zero]
  simp only [hpt]
  rw [integral_const_mul, hmain, mul_zero]

end PositivityTheory.Rg.Sw.HSt.L3
end
end

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {m n : ℕ}

def v1 (b : M2 n) : Matrix (Fin n) (Fin n) ℂ := Complex.I • b.toBlocks₁₁ + b.toBlocks₁₂

theorem fz_zero (e : ℤ) (x : M2 n) : fz m e 0 x = x.det ^ e * (u1 x).det ^ (-(m : ℤ)) := by
  simp [fz]

theorem blocks_mul (g b : M2 n) : (g * b).toBlocks₂₁ = g.toBlocks₂₁ * b.toBlocks₁₁ + g.toBlocks₂₂ * b.toBlocks₂₁ ∧
    (g * b).toBlocks₂₂ = g.toBlocks₂₁ * b.toBlocks₁₂ + g.toBlocks₂₂ * b.toBlocks₂₂ := by
  constructor <;> ext i j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₂₁, Matrix.toBlocks₁₁,
      Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, Matrix.add_apply]

theorem second_coord_mul_inner (g b : M2 n) : u1 (g * b) = g.toBlocks₂₁ * v1 b + g.toBlocks₂₂ * u1 b := by
  obtain ⟨h1, h2⟩ := blocks_mul g b
  simp only [u1, v1, h1, h2, Matrix.mul_add, Matrix.mul_smul, smul_add]
  abel

theorem nU_blocks (y : M2 n) (S : Matrix (Fin n) (Fin n) ℂ) :
    (y * nU S).toBlocks₂₁ = y.toBlocks₂₁ ∧ (y * nU S).toBlocks₂₂ = y.toBlocks₂₁ * S + y.toBlocks₂₂ := by
  obtain ⟨h1, h2⟩ := blocks_mul y (nU S)
  simp only [nU, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, Matrix.mul_one, Matrix.mul_zero,
    add_zero] at h1 h2
  exact ⟨h1, h2⟩

theorem det_nU (S : Matrix (Fin n) (Fin n) ℂ) : (nU S).det = 1 := by
  simp [nU]

private theorem mul_JJ_mul_conjTranspose_eq_of_inG (y : M2 n) (hy : InG y) : y * JJ n * yᴴ = JJ n := by
  have hJ : JJ n * JJ n = -1 := by
    ext (i|i) (j|j) <;> simp [JJ, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  have hy' : yᴴ * JJ n * y = JJ n := hy
  have h1 : (-(JJ n * yᴴ * JJ n)) * y = 1 := by
    calc (-(JJ n * yᴴ * JJ n)) * y = -(JJ n * (yᴴ * JJ n * y)) := by
          simp only [Matrix.neg_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hy', hJ, neg_neg]
  have h2 : y * (-(JJ n * yᴴ * JJ n)) = 1 := mul_eq_one_comm.mp h1
  calc y * JJ n * yᴴ = y * JJ n * yᴴ * (-(JJ n * JJ n)) := by rw [hJ, neg_neg, Matrix.mul_one]
    _ = (y * (-(JJ n * yᴴ * JJ n))) * JJ n := by
      simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    _ = JJ n := by rw [h2, Matrix.one_mul]

theorem hermit_cd (y : M2 n) (hy : InG y) (hc : IsUnit y.toBlocks₂₁.det) :
    (y.toBlocks₂₁⁻¹ * y.toBlocks₂₂).IsHermitian := by
  have h := congrArg Matrix.toBlocks₂₂ (mul_JJ_mul_conjTranspose_eq_of_inG y hy)
  rw [← Matrix.fromBlocks_toBlocks y] at h
  simp [JJ, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose] at h
  rw [neg_add_eq_zero] at h
  have hcH : IsUnit (y.toBlocks₂₁)ᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact isUnit_star.mpr hc
  rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv]
  calc (y.toBlocks₂₂)ᴴ * (y.toBlocks₂₁)ᴴ⁻¹
      = (y.toBlocks₂₁)⁻¹ * (y.toBlocks₂₁ * (y.toBlocks₂₂)ᴴ) * (y.toBlocks₂₁)ᴴ⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hc, Matrix.one_mul]
    _ = (y.toBlocks₂₁)⁻¹ * (y.toBlocks₂₂ * (y.toBlocks₂₁)ᴴ) * (y.toBlocks₂₁)ᴴ⁻¹ := by rw [← h]
    _ = (y.toBlocks₂₁)⁻¹ * y.toBlocks₂₂ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hcH, Matrix.mul_one]

theorem v_rel (b : M2 n) (hb : InG b) : (u1 b)ᴴ * v1 b - (v1 b)ᴴ * u1 b = (2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have e := hb
  unfold InG at e
  rw [← Matrix.fromBlocks_toBlocks b] at e
  simp [JJ, Matrix.fromBlocks_multiply, Matrix.fromBlocks_conjTranspose] at e
  obtain ⟨e1, e2, e3, e4⟩ := e
  have key : (u1 b)ᴴ * v1 b - (v1 b)ᴴ * u1 b =
      -(-((b.toBlocks₂₁)ᴴ * b.toBlocks₁₁) + (b.toBlocks₁₁)ᴴ * b.toBlocks₂₁)
      - (-((b.toBlocks₂₂)ᴴ * b.toBlocks₁₂) + (b.toBlocks₁₂)ᴴ * b.toBlocks₂₂)
      + Complex.I • ((-((b.toBlocks₂₁)ᴴ * b.toBlocks₁₂) + (b.toBlocks₁₁)ᴴ * b.toBlocks₂₂)
        - (-((b.toBlocks₂₂)ᴴ * b.toBlocks₁₁) + (b.toBlocks₁₂)ᴴ * b.toBlocks₂₁)) := by
    simp only [u1, v1, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul,
      Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Complex.star_def, Complex.conj_I]
    match_scalars <;>
      first | ring1 | linear_combination Complex.I_sq | linear_combination -Complex.I_sq
  rw [key, e1, e2, e3, e4]
  module

end PositivityTheory.Rg.Sw.HSt.L3
end
end

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {m n : ℕ}

private theorem exists_unitary_mul_blockTriangular_of_inFlagDomain (b : M2 n) (hb : InG b) : IsUnit (u1 b).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hr := congrArg (fun M => star x ⬝ᵥ (M *ᵥ x)) (v_rel b hb)
  simp only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, dotProduct_sub,
    dotProduct_zero, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, star_zero, zero_dotProduct,
    sub_zero, Matrix.zero_vecMul] at hr
  simp [Matrix.vecMul_smul] at hr
  have h2 : ∑ j, Complex.normSq (x j) = 0 := by
    have h3 := congrArg Complex.re hr
    simp only [dotProduct, Pi.star_apply, Complex.re_sum, Complex.mul_re, Complex.star_def,
      Complex.conj_re, Complex.conj_im, Complex.zero_re] at h3
    rw [← h3]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.normSq_apply]
    ring
  rw [Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg _] at h2
  apply hx0
  funext j
  exact Complex.normSq_eq_zero.mp (h2 j (Finset.mem_univ j))

theorem factor (y b : M2 n) (hy : InG y) (hb : InG b) (hc : IsUnit y.toBlocks₂₁.det) :
    ∃ (R H0 : Matrix (Fin n) (Fin n) ℂ) (κ : ℂ), IsUnit R.det ∧ H0.IsHermitian ∧ κ ≠ 0 ∧
      ∀ S, (u1 (y * nU S * b)).det = κ * (R * Rᴴ - Complex.I • (H0 + S)).det := by
  have hU := exists_unitary_mul_blockTriangular_of_inFlagDomain b hb
  have hH := hermit_cd y hy hc
  obtain ⟨U, hUdef⟩ : ∃ U, U = u1 b := ⟨_, rfl⟩
  obtain ⟨V, hVdef⟩ : ∃ V, V = v1 b := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ C, C = y.toBlocks₂₁ := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D, D = y.toBlocks₂₂ := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P, P = V * U⁻¹ := ⟨_, rfl⟩
  have hrel : Uᴴ * V - Vᴴ * U = (2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [hUdef, hVdef]
    exact v_rel b hb
  rw [← hUdef] at hU
  rw [← hCdef] at hc
  rw [← hCdef, ← hDdef] at hH
  have hUU : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv _ hU
  have hUU' : (U⁻¹)ᴴ * Uᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hUU, Matrix.conjTranspose_one]
  have hP : P - Pᴴ = (2 * Complex.I) • ((U⁻¹)ᴴ * U⁻¹) := by
    calc P - Pᴴ = ((U⁻¹)ᴴ * Uᴴ) * V * U⁻¹ - (U⁻¹)ᴴ * Vᴴ * (U * U⁻¹) := by
          rw [hUU', hUU, Matrix.one_mul, Matrix.mul_one, hPdef, Matrix.conjTranspose_mul]
      _ = (U⁻¹)ᴴ * (Uᴴ * V - Vᴴ * U) * U⁻¹ := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      _ = (2 * Complex.I) • ((U⁻¹)ᴴ * U⁻¹) := by
          rw [hrel, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  have hRR : (U⁻¹)ᴴ * ((U⁻¹)ᴴ)ᴴ = (U⁻¹)ᴴ * U⁻¹ := by
    rw [Matrix.conjTranspose_conjTranspose]
  have hI : Complex.I • ((U⁻¹)ᴴ * ((U⁻¹)ᴴ)ᴴ) = (1 / 2 : ℂ) • (P - Pᴴ) := by
    rw [hRR, hP, smul_smul]
    congr 1
    ring
  refine ⟨(U⁻¹)ᴴ, (1 / 2 : ℂ) • (P + Pᴴ) + C⁻¹ * D, C.det * Complex.I ^ n * U.det, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_conjTranspose]
    exact isUnit_star.mpr (Matrix.isUnit_nonsing_inv_det _ hU)
  · refine Matrix.IsHermitian.add ?_ hH
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose, add_comm]
    congr 1
    simp
  · exact mul_ne_zero (mul_ne_zero hc.ne_zero (pow_ne_zero _ Complex.I_ne_zero)) hU.ne_zero
  · intro S
    have hin : Complex.I • ((U⁻¹)ᴴ * ((U⁻¹)ᴴ)ᴴ - Complex.I • ((1 / 2 : ℂ) • (P + Pᴴ) + C⁻¹ * D + S))
        = P + C⁻¹ * D + S := by
      rw [smul_sub, smul_smul, Complex.I_mul_I, hI]
      module
    have e1 : C * P * U = C * V := by
      rw [hPdef, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU, Matrix.mul_one]
    have e2 : C * (C⁻¹ * D) * U = D * U := by
      rw [← Matrix.mul_assoc C, Matrix.mul_nonsing_inv _ hc, Matrix.one_mul]
    have hmain : u1 (y * nU S * b) = C * (Complex.I • ((U⁻¹)ᴴ * ((U⁻¹)ᴴ)ᴴ
        - Complex.I • ((1 / 2 : ℂ) • (P + Pᴴ) + C⁻¹ * D + S))) * U := by
      rw [hin, second_coord_mul_inner, (nU_blocks y S).1, (nU_blocks y S).2, ← hCdef, ← hDdef, ← hUdef, ← hVdef]
      simp only [Matrix.mul_add, Matrix.add_mul]
      rw [e1, e2]
      abel
    rw [hmain, Matrix.det_mul, Matrix.det_mul, Matrix.det_smul, Fintype.card_fin]
    ring

end PositivityTheory.Rg.Sw.HSt.L3
end
end

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {m n : ℕ}

theorem vanish_inv (hmn : m < n) (e : ℤ) (y b : M2 n) (hy : InG y) (hb : InG b) (hc : IsUnit y.toBlocks₂₁.det)
    (ψ : (Fin n → Fin n → ℝ) → ℂ) (hψ : IsSingTest ψ) :
    ∫ s, fz m e 0 (y * nU (herm s) * b) * ψ s = 0 := by
  obtain ⟨R, H0, κ, hR, hH0, hκ, hf⟩ := factor y b hy hb hc
  have key : ∀ s, fz m e 0 (y * nU (herm s) * b) * ψ s =
      ((y.det * b.det) ^ e * κ ^ (-(m : ℤ))) *
        (ψ s * (R * Rᴴ - Complex.I • (H0 + herm s)).det⁻¹ ^ m) := by
    intro s
    rw [fz_zero, hf, Matrix.det_mul, Matrix.det_mul, det_nU, mul_one]
    simp only [mul_zpow, _root_.zpow_neg, zpow_natCast, inv_pow]
    ring
  simp_rw [key]
  rw [MeasureTheory.integral_const_mul, core2 hmn R hR H0 hH0 ψ hψ, mul_zero]

end PositivityTheory.Rg.Sw.HSt.L3
end
end

noncomputable section

open MeasureTheory Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {m n : ℕ}

def nbar (t : ℝ) : M2 n := fromBlocks 1 0 ((t : ℂ) • 1) 1

theorem inG_nbar (t : ℝ) : InG (nbar (n := n) t) := by
  simp [InG, nbar, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]

theorem nbar_block (y : M2 n) (t : ℝ) : (y * nbar t).toBlocks₂₁ = y.toBlocks₂₁ + (t : ℂ) • y.toBlocks₂₂ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks y]
  simp [nbar, Matrix.fromBlocks_multiply]

private theorem JJ_mul_JJ_eq_neg_one : JJ n * JJ n = -1 := by
  rw [JJ, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
  simp

theorem det_ne_of_inG (x : M2 n) (hx : InG x) : x.det ≠ 0 := by
  have hx' : xᴴ * JJ n * x = JJ n := hx
  have h : (-(JJ n * xᴴ * JJ n)) * x = 1 := by
    calc (-(JJ n * xᴴ * JJ n)) * x = -(JJ n * (xᴴ * JJ n * x)) := by
          simp [Matrix.mul_assoc]
      _ = 1 := by rw [hx', JJ_mul_JJ_eq_neg_one, neg_neg]
  exact (Matrix.isUnit_det_of_left_inverse h).ne_zero

theorem det_first_cayley_block_ne_group (x : M2 n) (hx : InG x) : (u1 x).det ≠ 0 := by
  have hx' : xᴴ * JJ n * x = JJ n := hx
  rw [← Matrix.fromBlocks_toBlocks x] at hx'
  simp only [JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj] at hx'
  simp at hx'
  obtain ⟨h1, h2, h3, h4⟩ := hx'
  have hu : u1 x = Complex.I • x.toBlocks₂₁ + x.toBlocks₂₂ := rfl
  rw [hu]
  set A := x.toBlocks₁₁
  set B := x.toBlocks₁₂
  set C := x.toBlocks₂₁
  set D := x.toBlocks₂₂
  have e1 : Aᴴ * C = Cᴴ * A := eq_of_sub_eq_zero (by rw [sub_eq_neg_add]; exact h1)
  have e2 : Aᴴ * D = 1 + Cᴴ * B := by rw [← h2]; abel
  have e3 : Bᴴ * C = Dᴴ * A + -1 := by rw [← h3]; abel
  have e4 : Bᴴ * D = Dᴴ * B := eq_of_sub_eq_zero (by rw [sub_eq_neg_add]; exact h4)
  have key : (Complex.I • A + B)ᴴ * (Complex.I • C + D) - (Complex.I • C + D)ᴴ * (Complex.I • A + B)
      = (-2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.star_def, Complex.conj_I]
    rw [e1, e2, e3, e4]
    match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  intro h0
  obtain ⟨v, hv, huv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
  have hs : star v ᵥ* (Complex.I • C + D)ᴴ = 0 := by
    rw [← Matrix.star_mulVec, huv, star_zero]
  have hz : star v ⬝ᵥ (((Complex.I • A + B)ᴴ * (Complex.I • C + D)
      - (Complex.I • C + D)ᴴ * (Complex.I • A + B)) *ᵥ v) = 0 := by
    rw [Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, huv,
      Matrix.mulVec_zero, dotProduct_zero, Matrix.dotProduct_mulVec, hs, zero_dotProduct, sub_zero]
  rw [key, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] at hz
  have h2I : (-2 * Complex.I) ≠ 0 := by simp [Complex.I_ne_zero]
  open ComplexOrder in
  exact hv (dotProduct_star_self_eq_zero.1 ((mul_eq_zero.1 hz).resolve_left h2I))

end PositivityTheory.Rg.Sw.HSt.L3
end
end

noncomputable section

open MeasureTheory Matrix Filter Topology Polynomial

namespace PositivityTheory.Rg.Sw.HSt.L3

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {m n : ℕ}

theorem eventually_unit (y : M2 n) (hy : InG y) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ), IsUnit (y * nbar t).toBlocks₂₁.det := by
  set C := y.toBlocks₂₁ with hC
  set D := y.toBlocks₂₂ with hD
  let M : Matrix (Fin n) (Fin n) ℂ[X] := C.map Polynomial.C + (Polynomial.X : ℂ[X]) • D.map Polynomial.C
  have hev : ∀ z : ℂ, (M.det).eval z = (C + z • D).det := by
    intro z
    rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp [M]
    ring
  have hp : M.det ≠ 0 := by
    intro h0
    have h1 := hev (-Complex.I)
    rw [h0, Polynomial.eval_zero] at h1
    have hu : u1 y = Complex.I • C + D := rfl
    have hmat : C + (-Complex.I) • D = (-Complex.I) • u1 y := by
      rw [hu, smul_add, smul_smul]
      simp
    rw [hmat, Matrix.det_smul] at h1
    exact (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 Complex.I_ne_zero)) (det_first_cayley_block_ne_group y hy)) h1.symm
  have hfin : {t : ℝ | (M.det).eval (t : ℂ) = 0}.Finite := by
    refine ((M.det.roots.toFinset.finite_toSet).preimage Complex.ofReal_injective.injOn).subset ?_
    intro t ht
    simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hp]
    exact ht
  have hS : IsClosed ({t : ℝ | (M.det).eval (t : ℂ) = 0} \ {0}) :=
    (hfin.subset Set.diff_subset).isClosed
  have hnhds : ({t : ℝ | (M.det).eval (t : ℂ) = 0} \ {0})ᶜ ∈ 𝓝 (0 : ℝ) :=
    hS.isOpen_compl.mem_nhds (by simp)
  filter_upwards [nhdsWithin_le_nhds hnhds, self_mem_nhdsWithin] with t ht ht0
  rw [nbar_block, ← hev]
  exact isUnit_iff_ne_zero.2 (fun h => ht ⟨h, ht0⟩)

private theorem inG_mul' {x y : M2 n} (hx : InG x) (hy : InG y) : InG (x * y) := by
  unfold InG at *
  rw [Matrix.conjTranspose_mul]
  calc yᴴ * xᴴ * JJ n * (x * y) = yᴴ * (xᴴ * JJ n * x) * y := by simp only [Matrix.mul_assoc]
    _ = JJ n := by rw [hx, hy]

private theorem inG_nU_herm' (s : Fin n → Fin n → ℝ) : InG (nU (herm s)) := by
  have hh : (herm s)ᴴ = herm s := by
    ext i j
    simp only [herm, Matrix.conjTranspose_apply, Complex.star_def, map_add (f := _), map_div₀, map_mul,
      Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    push_cast
    ring
  simp [InG, nU, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hh]

theorem vanish_all (hmn : m < n) (e : ℤ) (y b : M2 n) (hy : InG y) (hb : InG b)
    (ψ : (Fin n → Fin n → ℝ) → ℂ) (hψ : IsSingTest ψ) :
    ∫ s, fz m e 0 (y * nU (herm s) * b) * ψ s = 0 := by
  let G : ℝ → (Fin n → Fin n → ℝ) → ℂ := fun t s => fz m e 0 (y * nbar t * nU (herm s) * b) * ψ s
  let X : ℝ × (Fin n → Fin n → ℝ) → M2 n := fun p => y * nbar p.1 * nU (herm p.2) * b
  have hIn : ∀ p, InG (X p) := fun p =>
    inG_mul' (inG_mul' (inG_mul' hy (inG_nbar p.1)) (inG_nU_herm' p.2)) hb
  have h1 : Continuous fun p : ℝ × (Fin n → Fin n → ℝ) => nbar (n := n) p.1 := by
    unfold nbar
    exact Continuous.matrix_fromBlocks continuous_const continuous_const
      ((Complex.continuous_ofReal.comp continuous_fst).smul continuous_const) continuous_const
  have h2 : Continuous fun p : ℝ × (Fin n → Fin n → ℝ) => nU (herm p.2) := by
    unfold nU
    refine Continuous.matrix_fromBlocks continuous_const ?_ continuous_const continuous_const
    unfold herm
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fun_prop
  have hX : Continuous X :=
    ((continuous_const.matrix_mul h1).matrix_mul h2).matrix_mul continuous_const
  have hU : Continuous fun p => u1 (X p) := by
    unfold u1
    refine (Continuous.const_smul ?_ Complex.I).add ?_ <;>
      exact continuous_pi fun i => continuous_pi fun j => hX.matrix_elem _ _
  have hcont : Continuous (Function.uncurry G) := by
    have hG : Function.uncurry G = fun p => (X p).det ^ e * (u1 (X p)).det ^ (-(m : ℤ)) * ψ p.2 := by
      funext ⟨t, s⟩
      simp only [Function.uncurry_apply_pair, G, X, fz_zero]
    rw [hG]
    exact ((hX.matrix_det.zpow₀ e fun p => Or.inl (det_ne_of_inG _ (hIn p))).mul
      (hU.matrix_det.zpow₀ _ fun p => Or.inl (det_first_cayley_block_ne_group _ (hIn p)))).mul (hψ.1.comp continuous_snd)
  have hK : IsCompact (tsupport ψ) := hψ.2.1
  have hInt : ∀ t, ∫ s, G t s = ∫ s in tsupport ψ, G t s := fun t =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun s hs => by simp [G, image_eq_zero_of_notMem_tsupport hs])).symm
  have hc : Continuous fun t => ∫ s in tsupport ψ, G t s :=
    continuous_parametric_integral_of_continuous hcont hK
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∫ s in tsupport ψ, G t s = 0 := by
    filter_upwards [eventually_unit y hy] with t ht
    rw [← hInt]
    exact vanish_inv hmn e (y * nbar t) b (inG_mul' hy (inG_nbar t)) hb ht ψ hψ
  have hlim : Tendsto (fun t => ∫ s in tsupport ψ, G t s) (𝓝[≠] 0) (𝓝 (∫ s in tsupport ψ, G 0 s)) :=
    (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have h0 : ∫ s in tsupport ψ, G 0 s = 0 :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hev.mono fun t ht => ht.symm))
  have hn0 : nbar (n := n) 0 = 1 := by simp [nbar]
  have := (hInt 0).trans h0
  simpa [G, hn0] using this

end PositivityTheory.Rg.Sw.HSt.L3
end
end

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

theorem lt3 : SingularTestsKillVacuum := by
  intro n m e hmn Kg _ _ _ _ _ _ μ _ ι hι hK ρ ψ a b x hρ hψ ha hb hx
  have mulG : ∀ {p q : M2 n}, InG p → InG q → InG (p * q) := by
    intro p q hp hq
    unfold InG at *
    calc (p * q)ᴴ * JJ n * (p * q) = qᴴ * (pᴴ * JJ n * p) * q := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = JJ n := by rw [hp, hq]
  have hG : ∀ k, InG (ι k) := fun k => ((hK (ι k)).2 ⟨k, rfl⟩).1
  have h : ∀ k, ∫ t, fz m e 0 (x * ι k * a * nU (herm t) * b) * ψ t = 0 := fun k =>
    L3.vanish_all hmn e _ b (mulG (mulG hx (hG k)) ha) hb ψ hψ
  simp only [tOp, h, mul_zero, integral_zero]

end PositivityTheory.Rg.Sw.HSt
end
end

namespace PositivityTheory.Rg.Sw.HSt

theorem locTau : LocTau := asmLT lt1 lt2 lt3 crux

end PositivityTheory.Rg.Sw.HSt
