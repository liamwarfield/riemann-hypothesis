module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapSameBaseOrbit
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryTwistMinorScalar
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryTwistMinorScalar
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Plane

variable {N : ℕ}

theorem minorIJ_image_of_tri {R : Type} [CommRing R] (M : Matrix (Fin N) (Fin N) R) (S : Finset (Fin N))
    (σ : Fin N → Fin N) (hσ : StrictMonoOn σ S)
    (hT : ∀ x ∈ S, ∀ y ∈ S, y < x → M (σ x) y = 0) :
    minorIJ M (S.image σ) S = ∏ c ∈ S, M (σ c) c := by
  have e : (S.image σ).card = S.card := Finset.card_image_of_injOn hσ.injOn
  unfold minorIJ
  rw [dite_eq_left e]
  have hf : (fun i => σ (S.orderEmbOfFin rfl i)) = ⇑((S.image σ).orderEmbOfFin e) := by
    apply Finset.orderEmbOfFin_unique e
    · intro i
      exact Finset.mem_image_of_mem σ (Finset.orderEmbOfFin_mem S rfl i)
    · intro i i' hii
      exact hσ (Finset.orderEmbOfFin_mem S rfl i) (Finset.orderEmbOfFin_mem S rfl i')
        ((S.orderEmbOfFin rfl).strictMono hii)
  rw [← hf, Matrix.det_of_upperTriangular]
  · simp only [Matrix.submatrix_apply]
    conv_rhs => rw [← Finset.map_orderEmbOfFin_univ S rfl]
    rw [Finset.prod_map]
    rfl
  · intro i i' hii
    exact hT _ (Finset.orderEmbOfFin_mem S rfl i) _ (Finset.orderEmbOfFin_mem S rfl i')
      ((S.orderEmbOfFin rfl).strictMono hii)

theorem mul_entry (B : Matrix (Fin N) (Fin N) ℂ) (ca cb x y : Fin N) (s : ℂ) :
    (B * (1 + Matrix.single cb ca s)) x y = B x y + if y = ca then s * B x cb else 0 := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  congr 1
  by_cases hy : y = ca
  · subst hy
    simp [Matrix.mul_single_apply_same, mul_comm]
  · simp [Matrix.mul_single_apply_of_ne, hy]

theorem one_entry (ca cb x y : Fin N) (s : ℂ) :
    (1 + Matrix.single cb ca s : Matrix (Fin N) (Fin N) ℂ) x y =
      (if x = y then 1 else 0) + if cb = x ∧ ca = y then s else 0 := by
  simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]

theorem param_core (S : Finset (Fin N)) (ca cb : Fin N) (hca : ca ∈ S) (hmax : ∀ c ∈ S, c ≤ ca) (hlt : ca < cb)
    (B : Matrix (Fin N) (Fin N) ℂ) (hB : B.BlockTriangular id) (t t' μ : ℂ)
    (H : ∀ J, minorIJ (B * (1 + Matrix.single cb ca t')) J S = μ * minorIJ (1 + Matrix.single cb ca t) J S) :
    μ = (∏ c ∈ S.erase ca, B c c) * (B ca ca + t' * B ca cb) ∧
      μ * t = (∏ c ∈ S.erase ca, B c c) * (t' * B cb cb) := by
  have hne : ∀ c ∈ S, c ≠ cb := fun c hc => ne_of_lt ((hmax c hc).trans_lt hlt)
  have hcaNe : ca ≠ cb := ne_of_lt hlt
  let σ : Fin N → Fin N := fun c => if c = ca then cb else c
  have hσca : σ ca = cb := if_pos rfl
  have hσne : ∀ c, c ≠ ca → σ c = c := fun c hc => if_neg hc
  have hσ : StrictMonoOn σ S := by
    intro x _ y hy hxy
    have hx' : x ≠ ca := ne_of_lt (hxy.trans_le (hmax y hy))
    rw [hσne x hx']
    by_cases hy' : y = ca
    · rw [hy', hσca]
      exact (hxy.trans_le (hmax y hy)).trans hlt
    · rw [hσne y hy']
      exact hxy
  have hge : ∀ x ∈ S, x ≤ σ x := by
    intro x hx
    by_cases hx' : x = ca
    · rw [hx', hσca]
      exact hlt.le
    · rw [hσne x hx']
  have hyne : ∀ x ∈ S, ∀ y, y < x → y ≠ ca := fun x hx y hy => ne_of_lt (hy.trans_le (hmax x hx))

  have L1 : minorIJ (B * (1 + Matrix.single cb ca t')) S S =
      (∏ c ∈ S.erase ca, B c c) * (B ca ca + t' * B ca cb) := by
    have h0 := minorIJ_image_of_tri (B * (1 + Matrix.single cb ca t')) S id strictMonoOn_id (by
      intro x hx y _ hy
      rw [mul_entry, if_neg (hyne x hx y hy), add_zero]
      exact hB hy)
    rw [Finset.image_id] at h0
    rw [h0, ← Finset.prod_erase_mul S _ hca]
    congr 1
    · refine Finset.prod_congr rfl fun c hc => ?_
      rw [id, mul_entry, if_neg (Finset.ne_of_mem_erase hc), add_zero]
    · rw [id, mul_entry, if_pos rfl]
  have R1 : minorIJ (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) S S = 1 := by
    have h0 := minorIJ_image_of_tri (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) S id strictMonoOn_id (by
      intro x hx y _ hy
      rw [id, one_entry, if_neg (ne_of_gt hy), if_neg (fun h => hne x hx h.1.symm), add_zero])
    rw [Finset.image_id] at h0
    rw [h0]
    refine Finset.prod_eq_one fun c hc => ?_
    rw [id, one_entry, if_pos rfl, if_neg (fun h => hne c hc h.1.symm), add_zero]

  have L2 : minorIJ (B * (1 + Matrix.single cb ca t')) (S.image σ) S =
      (∏ c ∈ S.erase ca, B c c) * (t' * B cb cb) := by
    rw [minorIJ_image_of_tri _ S σ hσ (by
      intro x hx y _ hy
      rw [mul_entry, if_neg (hyne x hx y hy), add_zero]
      exact hB (hy.trans_le (hge x hx))), ← Finset.prod_erase_mul S _ hca]
    congr 1
    · refine Finset.prod_congr rfl fun c hc => ?_
      have hc' := Finset.ne_of_mem_erase hc
      rw [hσne c hc', mul_entry, if_neg hc', add_zero]
    · have h0 : B cb ca = 0 := hB hlt
      rw [hσca, mul_entry, if_pos rfl, h0, zero_add]
  have R2 : minorIJ (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) (S.image σ) S = t := by
    rw [minorIJ_image_of_tri _ S σ hσ (by
      intro x hx y _ hy
      rw [one_entry, if_neg (ne_of_gt (hy.trans_le (hge x hx))),
        if_neg (fun h => hyne x hx y hy h.2.symm), add_zero]), ← Finset.prod_erase_mul S _ hca]
    have h1 : ∏ c ∈ S.erase ca, (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) (σ c) c = 1 := by
      refine Finset.prod_eq_one fun c hc => ?_
      have hc' := Finset.ne_of_mem_erase hc
      rw [hσne c hc', one_entry, if_pos rfl,
        if_neg (fun h => hne c (Finset.mem_of_mem_erase hc) h.1.symm), add_zero]
    rw [h1, one_mul, hσca, one_entry, if_neg (Ne.symm hcaNe), if_pos ⟨rfl, rfl⟩, zero_add]
  have e1 := H S
  have e2 := H (S.image σ)
  rw [L1, R1, mul_one] at e1
  rw [L2, R2] at e2
  exact ⟨e1.symm, e2.symm⟩

theorem param_relation : ∀ (N j : ℕ) (a b ca cb : Fin N), j ≤ N → (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (h B : Matrix (Fin N) (Fin N) ℂ) (t t' μ : ℂ), h.det ≠ 0 → IsBlockDiag j B → B.BlockTriangular id → (∀ I, minorIJ (h * B * (1 + Matrix.single cb ca t')) I (stepCols N j a) = μ * minorIJ (h * (1 + Matrix.single cb ca t)) I (stepCols N j a)) → μ = (∏ c ∈ (stepCols N j a).erase ca, B c c) * (B ca ca + t' * B ca cb) ∧ μ * t = (∏ c ∈ (stepCols N j a).erase ca, B c c) * (t' * B cb cb) := by
  intro N j a b ca cb hj hb hab hca hcb h B t t' μ hdet _ hBt hyp
  have hinv : h⁻¹ * h = 1 := Matrix.nonsing_inv_mul h (isUnit_iff_ne_zero.2 hdet)
  have hcaS : ca ∈ stepCols N j a := by
    unfold lastCol at hca
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs at hca ⊢ <;> omega
  have hmax : ∀ c ∈ stepCols N j a, c ≤ ca := by
    intro c hc
    unfold lastCol at hca
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rw [Fin.le_def]
    split_ifs at hca hc <;> omega
  have hlt : ca < cb := by
    rw [Fin.lt_def]
    omega
  refine param_core _ ca cb hcaS hmax hlt B hBt t t' μ fun J => ?_
  calc minorIJ (B * (1 + Matrix.single cb ca t')) J (stepCols N j a)
      = minorIJ (h⁻¹ * (h * B * (1 + Matrix.single cb ca t'))) J (stepCols N j a) := by
        rw [Matrix.mul_assoc h, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
    _ = ∑ I, minorIJ h⁻¹ J I * minorIJ (h * B * (1 + Matrix.single cb ca t')) I (stepCols N j a) :=
        minorIJ_mul_sum _ _ _ _
    _ = μ * ∑ I, minorIJ h⁻¹ J I * minorIJ (h * (1 + Matrix.single cb ca t)) I (stepCols N j a) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [hyp I]
        ring
    _ = μ * minorIJ (h⁻¹ * (h * (1 + Matrix.single cb ca t))) J (stepCols N j a) := by
        rw [minorIJ_mul_sum]
    _ = μ * minorIJ (1 + Matrix.single cb ca t) J (stepCols N j a) := by
        rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Plane
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryTwistMinorScalarStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elementary_twist_minor_scalar : ∀ (N j : ℕ) (a b ca cb : Fin N), j ≤ N → (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (h B : Matrix (Fin N) (Fin N) ℂ) (t t' μ : ℂ), h.det ≠ 0 → IsBlockDiag j B → B.BlockTriangular id → (∀ I, minorIJ (h * B * (1 + Matrix.single cb ca t')) I (stepCols N j a) = μ * minorIJ (h * (1 + Matrix.single cb ca t)) I (stepCols N j a)) → μ = (∏ c ∈ (stepCols N j a).erase ca, B c c) * (B ca ca + t' * B ca cb) ∧ μ * t = (∏ c ∈ (stepCols N j a).erase ca, B c c) * (t' * B cb cb) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Plane.param_relation | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Plane.param_relation | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Plane.param_relation <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapPullbackSecond
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapPullbackSecond
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightProp

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j n : ℕ}
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)]

theorem sameOrbit_basePart {M : FlagModel y Ψ N j} {BM : BaseMetric M n} {p : Ψ × Fin N} {κ : Kk → K}
    {v : (Σ k, ιk k) → (Σ k, ι k)} {e : ℕ} {R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e} {pr : R.X → BM.Rb.X}
    (hS : IsStepHyp M BM p κ v R pr) (x : R.X) {z : (Σ k, ι k) → ℂ} (hz : z ∘ v = R.lift x x) :
    SameOrbit (basePart M.blk z) (BM.Rb.lift (pr x) (pr x)) := by
  obtain ⟨hbm, hcov, -, hall⟩ := hS
  obtain ⟨z₁, -, h1, h2⟩ := hall x
  have e : basePart M.blk z = basePart M.blk z₁ := by
    funext q
    obtain ⟨r, hr⟩ := hbm.2.2.2 ⟨q.1.1, q.2⟩ (hcov _ (Or.inl q.1.2))
    have h3 : z (v r) = z₁ (v r) := congrFun (hz.trans h1.symm) r
    rw [hr] at h3
    exact h3
  rw [e]
  exact h2

theorem exists_base_const {L : Type} {μ : L → Type} {b₁ b₂ b : (Σ k, μ k) → ℂ} (h₁ : SameOrbit b₁ b)
    (h₂ : SameOrbit b₂ b) : ∃ c : L → ℂ, (∀ k, c k ≠ 0) ∧ ∀ q, b₁ q = c q.1 * b₂ q := by
  obtain ⟨c₁, hc₁, rfl⟩ := h₁
  obtain ⟨c₂, hc₂, rfl⟩ := h₂
  refine ⟨fun k => c₁ k / c₂ k, fun k => div_ne_zero (hc₁ k) (hc₂ k), fun q => ?_⟩
  have := hc₂ q.1
  field_simp

theorem exists_coord {κ : Kk → K} {v : (Σ k, ιk k) → (Σ k, ι k)} (hbm : IsBlockMap κ v) (k : Kk) (i : ι (κ k)) :
    ∃ m : ιk k, v ⟨k, m⟩ = ⟨κ k, i⟩ := by
  obtain ⟨r, hr⟩ := hbm.2.2.2 ⟨κ k, i⟩ ⟨k, rfl⟩
  have h1 : κ r.1 = κ k := by rw [← hbm.2.2.1 r, hr]
  have h2 : r.1 = k := hbm.1 h1
  obtain ⟨r1, m⟩ := r
  obtain rfl : r1 = k := h2
  exact ⟨m, hr⟩

theorem stepGap_eq {M : FlagModel y Ψ N j} [Fintype Ψ] [DecidableEq Ψ] {BM : BaseMetric M n} {p : Ψ × Fin N} {κ : Kk → K}
    {v : (Σ k, ιk k) → (Σ k, ι k)} {e : ℕ} {R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e} {pr : R.X → BM.Rb.X}
    (hS : IsStepHyp M BM p κ v R pr) {x x' : R.X} (hpr : pr x = pr x') (hb : pr x ∉ bdry BM.s)
    (hblk : ∀ k (m : ιk k), M.blk p = some (κ k) → ∃ a : ℂ, ∀ m' : ιk k,
      R.lift x x ⟨k, m'⟩ = a * R.lift x' x' ⟨k, m'⟩)
    {z z' : (Σ k, ι k) → ℂ} (hzm : z ∈ mcPts (mCoordIdeal y)) (hz'm : z' ∈ mcPts (mCoordIdeal y))
    (hz : z ∘ v = R.lift x x) (hz' : z' ∘ v = R.lift x' x') :
    stepGap M BM p z = stepGap M BM p z' := by
  have so := sameOrbit_basePart hS x hz
  have so' := sameOrbit_basePart hS x' hz'
  rw [← hpr] at so'
  obtain ⟨cb, hcb, hcbq⟩ := exists_base_const so so'
  obtain ⟨hbm, hcov, -, -⟩ := hS
  have e1 : ∀ r, z (v r) = R.lift x x r := congrFun hz
  have e2 : ∀ r, z' (v r) = R.lift x' x' r := congrFun hz'
  have ha : ∃ a : ℂ, a ≠ 0 ∧ ∀ k, M.blk p = some k → ∀ m : ι k, z ⟨k, m⟩ = a * z' ⟨k, m⟩ := by
    rcases hp : M.blk p with _ | k₀
    · exact ⟨1, one_ne_zero, fun k hk => by simp at hk⟩
    · obtain ⟨k', rfl⟩ := hcov k₀ (Or.inr hp)
      obtain ⟨i, hi⟩ := hzm.1 (κ k')
      obtain ⟨m, hm⟩ := exists_coord hbm k' i
      obtain ⟨a, ha⟩ := hblk k' m hp
      refine ⟨a, fun h0 => hi ?_, fun k hk m' => ?_⟩
      · rw [← hm, e1, ha, h0, zero_mul]
      · obtain rfl : κ k' = k := Option.some.inj hk
        obtain ⟨m'', hm''⟩ := exists_coord hbm k' m'
        rw [← hm'', e1, e2, ha]
  obtain ⟨a, ha0, ha⟩ := ha
  let c : K → ℂ := fun k =>
    if h : ∀ p', M.blk p' ≠ some k then cb ⟨k, h⟩ else if M.blk p = some k then a else 1
  have hc : ∀ k, c k ≠ 0 := fun k => by
    simp only [c]
    split_ifs
    · exact hcb _
    · exact ha0
    · exact one_ne_zero
  have hT := GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.main K ι Φ y z' c hc
  have h1 : stepGap M BM p (fun q => c q.1 * z' q) = stepGap M BM p z' :=
    GlobalTheory.T.flag_gap_torus_invariant K ι Φ y Ψ N j M n BM p z' c hc hz'm.1
  rw [← h1]
  refine GlobalTheory.T.flag_gap_same_base_orbit K ι Φ y Ψ N j M n BM p (pr x) z _ hb hzm (hT.2 hz'm).1 so ?_ ?_
  · funext q
    have : c q.1.1 = cb q.1 := dif_pos q.1.2
    show basePart M.blk z q = c q.1.1 * z' ⟨q.1.1, q.2⟩
    rw [this, hcbq]
    rfl
  · intro k hk m
    have : c k = a := (dif_neg fun h => h p hk).trans (if_pos hk)
    show z ⟨k, m⟩ = c k * z' ⟨k, m⟩
    rw [this, ha k hk]

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X), IsStepHyp M BM p κ v R pr → ∀ x x', pr x = pr x' → (∀ k (m : ιk k), M.blk p = some (κ k) → ∃ a : ℂ, ∀ m' : ιk k, R.lift x x ⟨k, m'⟩ = a * R.lift x' x' ⟨k, m'⟩) → stepPh M BM p v R pr x = stepPh M BM p v R pr x' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p Kk _ ιk _ κ v e R pr hS x x' hpr hblk
  by_cases hb : pr x ∈ bdry BM.s
  · have hb' : pr x' ∈ bdry BM.s := hpr ▸ hb
    rw [stepPh, stepPh, dif_neg fun h => h.1 hb, dif_neg fun h => h.1 hb']
  · have hb' : pr x' ∉ bdry BM.s := hpr ▸ hb
    obtain ⟨z₁, hz₁, hv₁, -⟩ := hS.2.2.2 x
    obtain ⟨z₂, hz₂, hv₂, -⟩ := hS.2.2.2 x'
    have h1 : pr x ∉ bdry BM.s ∧ ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x := ⟨hb, z₁, hz₁, hv₁⟩
    have h2 : pr x' ∉ bdry BM.s ∧ ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x' x' := ⟨hb', z₂, hz₂, hv₂⟩
    rw [stepPh, stepPh, dif_pos h1, dif_pos h2]
    exact stepGap_eq hS hpr hb hblk h1.2.choose_spec.1 h2.2.choose_spec.1 h1.2.choose_spec.2 h2.2.choose_spec.2

end GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightProp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapPullbackSecondStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_gap_pullback_second : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X), IsStepHyp M BM p κ v R pr → ∀ x x', pr x = pr x' → (∀ k (m : ιk k), M.blk p = some (κ k) → ∃ a : ℂ, ∀ m' : ιk k, R.lift x x ⟨k, m'⟩ = a * R.lift x' x' ⟨k, m'⟩) → stepPh M BM p v R pr x = stepPh M BM p v R pr x' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightProp.main | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightProp.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightProp.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameTwistCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameTwistCompat
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.AdFrame

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

section Pure

theorem values_adapted {Ω Φ : Type} [Field Ω] [Field Φ] (i : Ω →+* Φ) (R : Subring Φ) {n r : ℕ}
    (A : Matrix (Fin n) (Fin r) Ω) (T : Matrix (Fin r) (Fin r) Ω) (C₀ : Matrix (Fin r) (Fin n) Ω) (z : Ω)
    (u U Rm Rm' : Matrix (Fin r) (Fin r) Φ) (F : Matrix (Fin n) (Fin r) Φ)
    (hF : F = A.map i * u) (hu : u * U = T.map i * Rm) (hRm : ∀ a b, Rm a b ∈ R) (hRm' : ∀ a b, Rm' a b ∈ R)
    (hR : Rm * Rm' = 1) (hB : ∀ a b, i ((A * T) a b / z) ∈ R) (hC₀ : ∀ a b, i (C₀ a b) ∈ R)
    (hinv : ∀ a b, ∑ k, C₀ a k * ((A * T) k b / z) = if a = b then 1 else 0) :
    ∃ C : Matrix (Fin r) (Fin n) Φ, (∀ a b, (F * U) a b / i z ∈ R) ∧ (∀ a b, C a b ∈ R) ∧
      ∀ a b, ∑ k, C a k * ((F * U) k b / i z) = if a = b then 1 else 0 := by
  set B : Matrix (Fin n) (Fin r) Ω := Matrix.of fun a b => (A * T) a b / z with hBdef
  have hFU : F * U = (A * T).map i * Rm := by
    rw [hF, Matrix.mul_assoc, hu, ← Matrix.mul_assoc, Matrix.map_mul]
  have hval : ∀ a b, (F * U) a b / i z = (B.map i * Rm) a b := by
    intro a b
    rw [hFU, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.map_apply, hBdef, Matrix.of_apply, map_div₀]
    ring
  have hCB : C₀ * B = 1 := by
    ext a b
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact hinv a b
  have hRm2 : Rm' * Rm = 1 := mul_eq_one_comm.1 hR
  refine ⟨Rm' * C₀.map i, fun a b => ?_, fun a b => ?_, fun a b => ?_⟩
  · rw [hval, Matrix.mul_apply]
    exact sum_mem fun k _ => mul_mem (hB a k) (hRm k b)
  · rw [Matrix.mul_apply]
    exact sum_mem fun k _ => mul_mem (hRm' a k) (hC₀ k b)
  · have h1 : (Rm' * C₀.map i) * (B.map i * Rm) = 1 := by
      have h2 : C₀.map i * B.map i = 1 := by
        rw [← Matrix.map_mul, hCB]
        exact Matrix.map_one _ (map_zero i) (map_one i)
      calc (Rm' * C₀.map i) * (B.map i * Rm) = Rm' * (C₀.map i * B.map i) * Rm := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h2, Matrix.mul_one, hRm2]
    have h3 := congrFun (congrFun h1 a) b
    rw [Matrix.mul_apply, Matrix.one_apply] at h3
    simpa only [hval] using h3

theorem colFrame_semi {Ω Φ E F : Type} [Field Ω] [Field Φ] [AddCommGroup E] [Module Ω E] [AddCommGroup F] [Module Φ F]
    {i : Ω →+* Φ} {j : E →+ F} (hj : ∀ (a : Ω) (e : E), j (a • e) = i a • j e) {r : ℕ} (e : Fin r → E)
    (T : Matrix (Fin r) (Fin r) Ω) :
    (fun k => j (colFrame e T k)) = colFrame (fun a => j (e a)) (T.map i) := by
  funext k
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [colFrame, map_sum, hj, Matrix.map_apply]

theorem isFrameAt_of_map {X : Scheme.{0}} {Ω E E' : Type} [Field Ω] [AddCommGroup E] [Module Ω E] [AddCommGroup E']
    [Module Ω E'] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (L : Lat ξ E) (f : E →ₗ[Ω] E') (hf : Function.Injective f) {r : ℕ}
    (b : Fin r → E) (p : Cpt ξ) (h : (L.map f).IsFrameAt (fun k => f (b k)) p) : L.IsFrameAt b p := by
  refine ⟨LinearIndependent.of_comp f h.1, ?_⟩
  have h2 : (L p).map (f.restrictScalars (regAt ξ p)) =
      (Submodule.span (regAt ξ p) (Set.range b)).map (f.restrictScalars (regAt ξ p)) := by
    have : (Set.range fun k => f (b k)) = (f.restrictScalars (regAt ξ p)) '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [Submodule.map_span, ← this]
    exact h.2
  exact Submodule.map_injective_of_injective (f := f.restrictScalars (regAt ξ p)) hf h2

end Pure

section Main

theorem adapted_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → ∀ (𝔐' : HodgeCpt Y S (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li) (Fl : 𝔐'.Flag), HodgeOver 𝔐' 𝔐 pr (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) j → (∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ pr j) → ColFlags 𝔐 bW bO j Fl → ∀ (τ : CMType H) (p' : Cpt 𝔐'.ξ) (hp : genPt 𝔐.ξ ⤳ pr p'.1) (c₁ : ∀ k, J₀ k), InChart 𝔐.ξ (seg x₀) c₁ ⟨pr p'.1, hp⟩ → ∃ (U : Matrix (Fin (rk (CMType H) D.p D.q (.inl τ))) (Fin (rk (CMType H) D.p D.q (.inl τ))) (GenField Ω (rk (CMType H) D.p D.q))) (C : Matrix (Fin (rk (CMType H) D.p D.q (.inl τ))) (Fin (n (.inl τ))) (GenField Ω (rk (CMType H) D.p D.q))), U.BlockTriangular id ∧ (∀ a b, (fMat (aOf 𝔐 bW bO φ) (.inl τ) * U) a b / algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ c₁ ^ m (.inl τ)) ∈ regAt 𝔐'.ξ p') ∧ (∀ a b, C a b ∈ regAt 𝔐'.ξ p') ∧ (∀ a b, ∑ k, C a k * ((fMat (aOf 𝔐 bW bO φ) (.inl τ) * U) k b / algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ c₁ ^ m (.inl τ))) = if a = b then 1 else 0) ∧ ∀ l, ((𝔐'.V (.inl τ)).gr (Fl.b (.inl τ)) l).IsGenAt p' (U l l) := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K₀ _ J₀ _ x₀ 𝔐 bW bO n m φ hF 𝔐' pr j Fl hO hV hC τ p' hp c₁ hch
  obtain ⟨T, C₀, -, hfr, hreg, hC₀r, hinv⟩ := GlobalTheory.T.exists_local_twist_trivialization 𝔐.X Ω 𝔐.ξ (EE 𝔐) ((k : K₀) → J₀ k) (seg x₀)
    (LL 𝔐 (.inl τ)) (m (.inl τ)) (rk (CMType H) D.p D.q (.inl τ)) (n (.inl τ)) (VV 𝔐 (.inl τ)) (φ (.inl τ))
    (cc 𝔐 bW bO (.inl τ)) (hF.2.2.1 _) (hF.1 _) (hF.2.1 _).1 (hF.2.1 _).2 ⟨pr p'.1, hp⟩ c₁ hch
  let e : Fin (rk (CMType H) D.p D.q (.inl τ)) → 𝔐.Li := fun a => (bW τ a : 𝔐.Li)
  have hfrV : (𝔐.V (.inl τ)).IsFrameAt (colFrame e T) ⟨pr p'.1, hp⟩ := by
    refine isFrameAt_of_map _ (inW 𝔐) (GenBases.inW_injective 𝔐) _ _ ?_
    have h : (fun k => inW 𝔐 (colFrame e T k)) = colFrame (cc 𝔐 bW bO (.inl τ)) T := by
      funext k
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [colFrame, map_sum, map_smul]
      rfl
    rw [h]
    exact hfr
  have hE := hO.2.2.2.1
  have hpull := FlagPull.pull_isFrameAt hO.1 hE p' hp hfrV
  rw [← hV (.inl τ), colFrame_semi hE.1] at hpull
  have he : LinearIndependent Ω e :=
    (bW τ).linearIndependent.map' (𝔐.Vgen (.inl τ)).subtype (Submodule.ker_subtype _)
  have hw := hE.2 _ e he
  have hb : Fl.b (.inl τ) = colFrame (fun a => j (e a)) (genU Ω (rk (CMType H) D.p D.q) (.inl τ)) := by
    funext k
    rw [hC.1 τ k, DetG.wBlock_gMat]
    rfl
  have hflag := Fl.sub (.inl τ)
  rw [hb] at hflag
  obtain ⟨U, Rm, Rm', hU, hRm, hRm', hR, hu, hgen⟩ := GlobalTheory.T.exists_triangular_regular_frame_change 𝔐'.X _ 𝔐'.ξ 𝔐'.Li (𝔐'.V (.inl τ))
    (rk (CMType H) D.p D.q (.inl τ)) (fun a => j (e a)) _ (genU Ω (rk (CMType H) D.p D.q) (.inl τ)) p' hw
    (by rw [DetG.det_genU]; exact isUnit_one) hpull hflag
  obtain ⟨C, h1, h2, h3⟩ := values_adapted (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) (regAt 𝔐'.ξ p')
    (aOf 𝔐 bW bO φ (.inl τ)) T C₀ (seg x₀ c₁ ^ m (.inl τ)) _ U Rm Rm' (fMat (aOf 𝔐 bW bO φ) (.inl τ)) rfl hu hRm hRm' hR
    (fun a b => LatModel.dominates_regAt hO.1 p' hp (hreg a b))
    (fun a b => LatModel.dominates_regAt hO.1 p' hp (hC₀r a b)) hinv
  refine ⟨U, C, hU, h1, h2, h3, fun l => ?_⟩
  rw [hb]
  exact hgen l

end Main

end GlobalTheory.CompanionTheory.Ar.PB.FMX.AdFrame
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameTwistCompatStatement
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCpt_frame_twist_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → ∀ (𝔐' : HodgeCpt Y S (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li) (Fl : 𝔐'.Flag), HodgeOver 𝔐' 𝔐 pr (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) j → (∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ pr j) → ColFlags 𝔐 bW bO j Fl → ∀ (τ : CMType H) (p' : Cpt 𝔐'.ξ) (hp : genPt 𝔐.ξ ⤳ pr p'.1) (c₁ : ∀ k, J₀ k), InChart 𝔐.ξ (seg x₀) c₁ ⟨pr p'.1, hp⟩ → ∃ (U : Matrix (Fin (rk (CMType H) D.p D.q (.inl τ))) (Fin (rk (CMType H) D.p D.q (.inl τ))) (GenField Ω (rk (CMType H) D.p D.q))) (C : Matrix (Fin (rk (CMType H) D.p D.q (.inl τ))) (Fin (n (.inl τ))) (GenField Ω (rk (CMType H) D.p D.q))), U.BlockTriangular id ∧ (∀ a b, (fMat (aOf 𝔐 bW bO φ) (.inl τ) * U) a b / algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ c₁ ^ m (.inl τ)) ∈ regAt 𝔐'.ξ p') ∧ (∀ a b, C a b ∈ regAt 𝔐'.ξ p') ∧ (∀ a b, ∑ k, C a k * ((fMat (aOf 𝔐 bW bO φ) (.inl τ) * U) k b / algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q)) (seg x₀ c₁ ^ m (.inl τ))) = if a = b then 1 else 0) ∧ ∀ l, ((𝔐'.V (.inl τ)).gr (Fl.b (.inl τ)) l).IsGenAt p' (U l l) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.AdFrame.adapted_frame | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.AdFrame.adapted_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.AdFrame.adapted_frame <;> assumption)
end
end
