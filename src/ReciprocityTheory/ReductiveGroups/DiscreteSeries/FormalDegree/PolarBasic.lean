module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KSchur

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarBasicA
noncomputable section

open Finset Matrix Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem pmat_continuous (ε : Fin n → Bool) : Continuous (fun z : PCoord ε → ℂ => pmat z) := by
  refine continuous_matrix fun a b => ?_
  by_cases h1 : b < a ∧ ε a ≠ ε b
  · simp only [pmat, dif_pos h1]; exact continuous_apply _
  · by_cases h2 : a < b ∧ ε b ≠ ε a
    · simp only [pmat, dif_neg h1, dif_pos h2]; exact (continuous_apply _).star
    · simp only [pmat, dif_neg h1, dif_neg h2]; exact continuous_const

theorem pb_trace_pow_herm {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (j : ℕ) :
    (A ^ j).trace = ∑ a, ((hA.eigenvalues a : ℝ) : ℂ) ^ j := by
  conv_lhs => rw [hA.spectral_theorem, ← map_pow]
  first
    | (rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul,
        Matrix.diagonal_pow, Matrix.trace_diagonal]
       simp)
    | simp [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Matrix.diagonal_pow, Matrix.trace_diagonal]

theorem psum_continuous (ε : Fin n → Bool) (j : ℕ) :
    Continuous (fun z : PCoord ε → ℂ => ∑ a, pev z a ^ j) := by
  have h : (fun z : PCoord ε → ℂ => ∑ a, pev z a ^ j) = fun z => ((pmat z) ^ j).trace.re := by
    funext z
    rw [pb_trace_pow_herm (pmat_isHermitian z) j, Complex.re_sum]
    exact Finset.sum_congr rfl fun a _ => by
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
      try rfl
  rw [h]
  exact Complex.continuous_re.comp (((pmat_continuous ε).pow j).matrix_trace)

theorem negpsum_continuous (ε : Fin n → Bool) (j : ℕ) :
    Continuous (fun z : PCoord ε → ℂ => ∑ b, (-pev z b) ^ j) := by
  have h : (fun z : PCoord ε → ℂ => ∑ b, (-pev z b) ^ j) = fun z => (-1) ^ j * ∑ b, pev z b ^ j := by
    funext z
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => neg_pow _ _
  rw [h]
  exact continuous_const.mul (psum_continuous ε j)

theorem pairpow_continuous (ε : Fin n → Bool) (k : ℕ) :
    Continuous (fun z : PCoord ε → ℂ => ∑ a, ∑ b, (pev z a - pev z b) ^ k) := by
  have h : (fun z : PCoord ε → ℂ => ∑ a, ∑ b, (pev z a - pev z b) ^ k) =
      fun z => ∑ i ∈ range (k + 1),
        (∑ a, pev z a ^ i) * (∑ b, (-pev z b) ^ (k - i)) * (k.choose i : ℝ) := by
    funext z
    simp_rw [sub_eq_add_neg, add_pow, Finset.sum_mul_sum, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]; arg 2; ext a; rw [Finset.sum_comm]
  rw [h]
  exact continuous_finsetSum _ fun i _ =>
    ((psum_continuous ε i).mul (negpsum_continuous ε (k - i))).mul continuous_const

theorem pairpoly_continuous (ε : Fin n → Bool) (P : Polynomial ℝ) :
    Continuous (fun z : PCoord ε → ℂ => ∑ a, ∑ b, P.eval (pev z a - pev z b)) := by
  have h : (fun z : PCoord ε → ℂ => ∑ a, ∑ b, P.eval (pev z a - pev z b)) =
      fun z => ∑ i ∈ range (P.natDegree + 1), P.coeff i * ∑ a, ∑ b, (pev z a - pev z b) ^ i := by
    funext z
    simp_rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]; arg 2; ext a; rw [Finset.sum_comm]
  rw [h]
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (pairpow_continuous ε i)

theorem pb_abs_pev_le {ε : Fin n → Bool} (z : PCoord ε → ℂ) (a : Fin n) :
    |pev z a| ≤ Real.sqrt (∑ b, pev z b ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun b => pev z b ^ 2)
    (fun b _ => sq_nonneg _) (Finset.mem_univ a))

theorem pairfun_continuous (ε : Fin n → Bool) (h : ℝ → ℝ) (hc : Continuous h) :
    Continuous (fun z : PCoord ε → ℂ => ∑ a, ∑ b, h (pev z a - pev z b)) := by
  have hS : Continuous (fun z : PCoord ε → ℂ => Real.sqrt (∑ b, pev z b ^ 2)) :=
    (psum_continuous ε 2).sqrt
  rw [Metric.continuous_iff]
  intro z0 e he
  obtain ⟨δ1, hδ1, h1⟩ := Metric.continuous_iff.1 hS z0 1 one_pos
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = Real.sqrt (∑ b, pev z0 b ^ 2) + 1 := ⟨_, rfl⟩
  have hbd : ∀ z, dist z z0 < δ1 → ∀ a b, pev z a - pev z b ∈ Set.Icc (-(2 * R)) (2 * R) := by
    intro z hz a b
    have hSz : Real.sqrt (∑ b, pev z b ^ 2) ≤ R := by
      have h1z := h1 z hz
      rw [Real.dist_eq] at h1z
      linarith [(abs_lt.1 h1z).2]
    have ha := abs_le.1 ((pb_abs_pev_le z a).trans hSz)
    have hb := abs_le.1 ((pb_abs_pev_le z b).trans hSz)
    constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = e / (3 * ((n : ℝ) * n + 1)) := ⟨_, rfl⟩
  have hηpos : 0 < η := by rw [hη]; positivity
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-(2 * R)) (2 * R) h hc.continuousOn η hηpos
  obtain ⟨δ2, hδ2, h2⟩ := Metric.continuous_iff.1 (pairpoly_continuous ε p) z0 (e / 3) (by positivity)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun z hz => ?_⟩
  have hz1 : dist z z0 < δ1 := hz.trans_le (min_le_left _ _)
  have hz2 : dist z z0 < δ2 := hz.trans_le (min_le_right _ _)
  have happrox : ∀ w, dist w z0 < δ1 →
      |∑ a, ∑ b, h (pev w a - pev w b) - ∑ a, ∑ b, p.eval (pev w a - pev w b)| ≤ n * n * η := by
    intro w hw
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hrow : ∀ a, |∑ b, h (pev w a - pev w b) - ∑ b, p.eval (pev w a - pev w b)| ≤ n * η := by
      intro a
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ b, |h (pev w a - pev w b) - p.eval (pev w a - pev w b)| ≤ ∑ _b : Fin n, η :=
            Finset.sum_le_sum fun b _ => by
              rw [abs_sub_comm]; exact (hp _ (hbd w hw a b)).le
        _ = n * η := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc ∑ a, |∑ b, h (pev w a - pev w b) - ∑ b, p.eval (pev w a - pev w b)| ≤ ∑ _a : Fin n, (n * η) :=
          Finset.sum_le_sum fun a _ => hrow a
      _ = n * n * η := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hA := abs_le.1 (happrox z hz1)
  have hB := abs_le.1 (happrox z0 (by simpa using hδ1))
  have hC := h2 z hz2
  rw [Real.dist_eq] at hC
  have hsmall : (n : ℝ) * n * η < e / 3 := by
    have hq : (n : ℝ) * n / (n * n + 1) < 1 := (div_lt_one (by positivity)).2 (by linarith)
    have heq : (n : ℝ) * n * η = e / 3 * ((n * n) / (n * n + 1)) := by
      rw [hη]
      first | (field_simp; ring) | field_simp | ring
    rw [heq]
    exact mul_lt_of_lt_one_right (by positivity) hq
  rw [Real.dist_eq]
  have hC' := abs_lt.1 hC
  exact abs_sub_lt_iff.2 ⟨by linarith [hA.1, hA.2, hB.1, hB.2, hC'.1, hC'.2],
    by linarith [hA.1, hA.2, hB.1, hB.2, hC'.1, hC'.2]⟩

theorem pb_shc_eq_update : shc = Function.update (fun u : ℝ => Real.sinh u / u) 0 1 := by
  funext u
  rw [Function.update_apply]
  rfl

theorem pb_shc_continuous : Continuous shc := by
  rw [pb_shc_eq_update, continuous_iff_continuousAt]
  intro u
  by_cases hu : u = 0
  · subst hu
    rw [continuousAt_update_same]
    have hd := Real.hasDerivAt_sinh 0
    rw [hasDerivAt_iff_tendsto_slope, Real.cosh_zero] at hd
    refine hd.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with v hv
    rw [slope_def_field]
    simp
  · rw [continuousAt_update_of_ne hu]
    exact (Real.continuous_sinh.continuousAt).div continuousAt_id hu

theorem pb_shc_pos (u : ℝ) : 0 < shc u := by
  unfold shc
  split_ifs with hu
  · exact one_pos
  · rcases lt_or_gt_of_ne hu with h | h
    · exact div_pos_of_neg_of_neg (Real.sinh_neg_iff.2 h) h
    · exact div_pos (Real.sinh_pos_iff.2 h) h

theorem pb_shc_neg (u : ℝ) : shc (-u) = shc u := by
  by_cases hu : u = 0
  · simp [shc, hu]
  · simp [shc, hu, Real.sinh_neg, neg_div_neg_eq]

theorem pb_sum_pairs_half {f : Fin n → Fin n → ℝ} (hsym : ∀ a b, f a b = f b a) (hd : ∀ a, f a a = 0) :
    ∑ a, ∑ b ∈ univ.filter (fun b => a < b), f a b = (∑ a, ∑ b, f a b) / 2 := by
  have hpt : ∀ a b, f a b = (if a < b then f a b else 0) + (if b < a then f a b else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | rfl | h
    · simp [h, not_lt.2 h.le]
    · simp [hd]
    · simp [h, not_lt.2 h.le]
  have hswap : ∑ a, ∑ b, (if b < a then f a b else 0) = ∑ a, ∑ b, (if a < b then f a b else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hsym]
  have htot : ∑ a, ∑ b, f a b = 2 * ∑ a, ∑ b, (if a < b then f a b else 0) := by
    conv_lhs => enter [2, a, 2, b]; rw [hpt a b]
    simp only [Finset.sum_add_distrib]
    rw [hswap]
    ring
  have hf : ∀ a, ∑ b ∈ univ.filter (fun b => a < b), f a b = ∑ b, (if a < b then f a b else 0) :=
    fun a => Finset.sum_filter _ _
  simp_rw [hf]
  rw [htot]
  ring

theorem pb_jac_eq_exp {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    Jac z = Real.exp ((∑ a, ∑ b, Real.log (shc (pev z a - pev z b))) / 2) := by
  have hsym : ∀ a b, Real.log (shc (pev z a - pev z b)) = Real.log (shc (pev z b - pev z a)) := by
    intro a b
    rw [← neg_sub (pev z a) (pev z b), pb_shc_neg]
  have hd : ∀ a, Real.log (shc (pev z a - pev z a)) = 0 := by
    intro a
    simp [shc]
  have hh := pb_sum_pairs_half (f := fun a b => Real.log (shc (pev z a - pev z b))) hsym hd
  try simp only at hh
  rw [← hh, Real.exp_sum]
  unfold Jac
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [Real.exp_log (pb_shc_pos _)]

theorem pb_jac_continuous (ε : Fin n → Bool) : Continuous (fun z : PCoord ε → ℂ => Jac z) := by
  have h : (fun z : PCoord ε → ℂ => Jac z) =
      fun z => Real.exp ((∑ a, ∑ b, Real.log (shc (pev z a - pev z b))) / 2) := funext pb_jac_eq_exp
  rw [h]
  exact Real.continuous_exp.comp ((pairfun_continuous ε _
    (pb_shc_continuous.log fun u => (pb_shc_pos u).ne')).div_const 2)

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem exp_pmat_inUJ {ε : Fin n → Bool} (z : PCoord ε → ℂ) : inUJ ε (NormedSpace.exp (pmat z)) := by
  have h := inUJ_kexp (1 : KG ε) (pmat_inP z)
  have e : toMK (1 : KG ε) = 1 := rfl
  rwa [e, Matrix.one_mul] at h

theorem polarM_inUJ {ε : Fin n → Bool} (kz : KG ε × (PCoord ε → ℂ)) : inUJ ε (polarM kz) :=
  inUJ_kexp kz.1 (pmat_inP kz.2)

theorem pmat_injective (ε : Fin n → Bool) : Function.Injective (pmat (ε := ε)) := by
  intro z z' h
  funext ab
  have := congrFun (congrFun h ab.1.1) ab.1.2
  simpa [pmat, dif_pos ab.2] using this

theorem polarM_injective (ε : Fin n → Bool) : Function.Injective (polarM (ε := ε)) := by
  rintro ⟨k, z⟩ ⟨k', z'⟩ h
  obtain ⟨hk, hX⟩ := polar_unique (pmat_inP z) (pmat_inP z')
    (show toMK k * NormedSpace.exp (pmat z) = toMK k' * NormedSpace.exp (pmat z') from h)
  rw [hk, pmat_injective ε hX]

theorem polarM_surj {ε : Fin n → Bool} (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) :
    ∃ kz : KG ε × (PCoord ε → ℂ), polarM kz = g := by
  obtain ⟨k, X, hX, rfl⟩ := polar_exists hg
  refine ⟨(k, fun ab => X ab.1.1 ab.1.2), ?_⟩
  show toMK k * NormedSpace.exp (pmat fun ab : PCoord ε => X ab.1.1 ab.1.2) = _
  rw [pmat_coords X hX]

open scoped Matrix.Norms.L2Operator in
theorem polarL_continuousOn (ε : Fin n → Bool) :
    ContinuousOn (PolarDecomposition.polar_L (n := n)) {g | inUJ ε g} := by
  have h : ContinuousOn (fun g : Matrix (Fin n) (Fin n) ℂ => CFC.log (gᴴ * g)) {g | inUJ ε g} := by
    refine CFC.continuousOn_log.comp (by fun_prop) ?_
    intro g hg
    obtain ⟨hsa, hu, -⟩ := PolarDecomposition.polar_isSelfAdjoint_isUnit_spectrum_pos hg
    exact ⟨hsa, hu⟩
  exact h.const_smul (1 / 2 : ℝ)

section Emb

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem polarM_continuous (ε : Fin n → Bool) : Continuous (polarM (ε := ε)) := by
  unfold polarM
  exact ((continuous_toM ε).comp (continuous_subtype_val.comp continuous_fst)).mul
    (NormedSpace.exp_continuous.comp ((pmat_continuous ε).comp continuous_snd))

def polarInvK (ε : Fin n → Bool) (g : UJset ε) : KG ε :=
  Classical.choose (exists_toMK (PolarDecomposition.polar_k_mem (ε := ε) (g := g.1) g.2))

theorem toMK_polarInvK (ε : Fin n → Bool) (g : UJset ε) :
    toMK (polarInvK ε g) = g.1 * NormedSpace.exp (-PolarDecomposition.polar_L g.1) :=
  Classical.choose_spec (exists_toMK (PolarDecomposition.polar_k_mem (ε := ε) (g := g.1) g.2))

def polarInv (ε : Fin n → Bool) (g : UJset ε) : KG ε × (PCoord ε → ℂ) :=
  (polarInvK ε g, fun ab => PolarDecomposition.polar_L g.1 ab.1.1 ab.1.2)

theorem polarM_polarInv (ε : Fin n → Bool) (g : UJset ε) : polarM (polarInv ε g) = g.1 := by
  show toMK (polarInvK ε g) * NormedSpace.exp (pmat fun ab : PCoord ε => PolarDecomposition.polar_L g.1 ab.1.1 ab.1.2) = g.1
  rw [pmat_coords _ (PolarDecomposition.polar_L_inP (ε := ε) (g := g.1) g.2), toMK_polarInvK]
  exact PolarDecomposition.eq_mul_exp_neg_polar_L_mul_exp_polar_L.symm

theorem polarInv_continuous (ε : Fin n → Bool) : Continuous (polarInv ε) := by
  have hL : Continuous fun g : UJset ε => PolarDecomposition.polar_L g.1 :=
    (polarL_continuousOn ε).comp_continuous continuous_subtype_val (fun g => g.2)
  have hind : Topology.IsInducing (fun k : KG ε => toMK k) :=
    (isClosedEmbedding_toM ε).isInducing.comp Topology.IsInducing.subtypeVal
  have hK : Continuous (polarInvK ε) := by
    rw [hind.continuous_iff]
    have : (fun k : KG ε => toMK k) ∘ polarInvK ε =
        fun g : UJset ε => g.1 * NormedSpace.exp (-PolarDecomposition.polar_L g.1) := by
      funext g; exact toMK_polarInvK ε g
    rw [this]
    exact continuous_subtype_val.mul (NormedSpace.exp_continuous.comp hL.neg)
  exact hK.prodMk (continuous_pi fun ab => hL.matrix_elem ab.1.1 ab.1.2)

def polarHomeo (ε : Fin n → Bool) : KG ε × (PCoord ε → ℂ) ≃ₜ UJset ε where
  toFun kz := ⟨polarM kz, polarM_inUJ kz⟩
  invFun := polarInv ε
  left_inv kz := polarM_injective ε (polarM_polarInv ε ⟨polarM kz, polarM_inUJ kz⟩)
  right_inv g := Subtype.ext (polarM_polarInv ε g)
  continuous_toFun := (polarM_continuous ε).subtype_mk _
  continuous_invFun := polarInv_continuous ε

theorem polarM_isClosedEmbedding (ε : Fin n → Bool) : Topology.IsClosedEmbedding (polarM (ε := ε)) := by
  have h : Topology.IsClosedEmbedding ((Subtype.val : UJset ε → Matrix (Fin n) (Fin n) ℂ) ∘ polarHomeo ε) :=
    (isClosed_inUJ ε).isClosedEmbedding_subtypeVal.comp (polarHomeo ε).isClosedEmbedding
  exact h

end Emb

theorem jac_continuous (ε : Fin n → Bool) : Continuous (fun z : PCoord ε → ℂ => Jac z) :=
  pb_jac_continuous ε

end ReciprocityTheory.ChartRestriction.DS
