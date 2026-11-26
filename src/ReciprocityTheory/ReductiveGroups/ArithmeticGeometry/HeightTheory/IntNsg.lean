module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HintLogFinprod

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HintChain
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HintISBounds
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def hintSm (c : ι) (sg : K →+* ℂ) (φ : (Ω c →+* ℂ) → ℝ)
    (z : BlockSphere d.D (d.N + 1)) : ℝ :=
  ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)), φ P

def HintIS (c : ι) (sg : K →+* ℂ) (φ : (Ω c →+* ℂ) → ℝ) : Prop :=
  Integrable (d.hintSm c sg φ) (blockSphereProb d.D (d.N + 1))

theorem hint_fs (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (sg : K →+* ℂ) :
    ∀ᵐ z ∂(blockSphereProb d.D (d.N + 1)), ∃ s : Finset (Ω c →+* ℂ), s.card = d.delc c ∧
      (∀ P ∈ s, P ∈ PT (Ω := Ω c) sg) ∧ ∀ φ, d.hintSm c sg φ z = ∑ P ∈ s, φ P := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  refine (d.norm_at_sg_B hd h c sg).mono ?_
  intro z hz
  obtain ⟨hfin, hcard, -, -⟩ := hz
  refine ⟨hfin.toFinset, ?_, fun P hP => (hfin.mem_toFinset.1 hP).1, fun φ => ?_⟩
  · rw [← hcard, Set.ncard_eq_toFinset_card _ hfin]
  · exact finsum_mem_eq_finite_toFinset_sum _ hfin

theorem hintIS_lin (hd : d.AxH 𝒜) (h : d.S1) {c : ι} {sg : K →+* ℂ}
    {φ₁ φ₂ : (Ω c →+* ℂ) → ℝ} (h₁ : d.HintIS c sg φ₁) (h₂ : d.HintIS c sg φ₂) (a₁ a₂ b : ℝ) :
    d.HintIS c sg (fun P => a₁ * φ₁ P + a₂ * φ₂ P + b) := by
  have hfs := d.hint_fs hd h c sg
  haveI : IsFiniteMeasure (blockSphereProb d.D (d.N + 1)) := by
    unfold blockSphereProb; infer_instance
  unfold HintIS at *
  refine (((h₁.const_mul a₁).add (h₂.const_mul a₂)).add
    (integrable_const (b * (d.delc c : ℝ)))).congr ?_
  filter_upwards [hfs] with z hz
  obtain ⟨s, hs, -, hφ⟩ := hz
  simp only [Pi.add_apply, hφ, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, hs,
    nsmul_eq_mul]
  ring

theorem hintIS_congr (hd : d.AxH 𝒜) (h : d.S1) {c : ι} {sg : K →+* ℂ}
    {φ ψ : (Ω c →+* ℂ) → ℝ} (hφ : d.HintIS c sg φ) (heq : ∀ P ∈ PT (Ω := Ω c) sg, φ P = ψ P) :
    d.HintIS c sg ψ := by
  unfold HintIS at *
  refine hφ.congr (Filter.Eventually.of_forall fun z => ?_)
  exact finsum_mem_congr rfl fun P hP => heq P hP.1

theorem hintIS_bounds (hd : d.AxH 𝒜) (h : d.S1) {c : ι} {sg : K →+* ℂ}
    {φ ψ : (Ω c →+* ℂ) → ℝ}
    (hm : AEStronglyMeasurable (d.hintSm c sg φ) (blockSphereProb d.D (d.N + 1)))
    (hψ : d.HintIS c sg ψ) (hle : ∀ P ∈ PT (Ω := Ω c) sg, ψ P ≤ φ P) (B : ℝ)
    (hB : ∀ P ∈ PT (Ω := Ω c) sg, φ P ≤ B) : d.HintIS c sg φ := by
  have hfs := d.hint_fs hd h c sg
  haveI : IsFiniteMeasure (blockSphereProb d.D (d.N + 1)) := by
    unfold blockSphereProb; infer_instance
  unfold HintIS at *
  refine Integrable.mono' (hψ.abs.add (integrable_const |(d.delc c : ℝ) * B|)) hm ?_
  filter_upwards [hfs] with z hz
  obtain ⟨s, hs, hsP, hφ⟩ := hz
  have h1 : d.hintSm c sg ψ z ≤ d.hintSm c sg φ z := by
    rw [hφ, hφ]
    exact Finset.sum_le_sum fun P hP => hle P (hsP P hP)
  have h2 : d.hintSm c sg φ z ≤ (d.delc c : ℝ) * B := by
    rw [hφ, ← hs, ← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun P hP => hB P (hsP P hP)
  simp only [Real.norm_eq_abs, Pi.add_apply]
  refine abs_le.mpr ⟨?_, ?_⟩
  · linarith [neg_abs_le (d.hintSm c sg ψ z), abs_nonneg ((d.delc c : ℝ) * B)]
  · linarith [le_abs_self ((d.delc c : ℝ) * B), abs_nonneg (d.hintSm c sg ψ z)]

theorem hint_bsp_smul : blockSphereProb d.D (d.N + 1) =
    (((volume : Measure (EuclideanSpace ℂ (Fin (d.N + 1)))).toSphere Set.univ)⁻¹ ^ d.D) •
      d.sphMeasure := by
  unfold blockSphereProb
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, smul_eq_mul, sphMeasure, Measure.pi_pi]
  simp only [sphereProb, ProbabilityTheory.cond_apply MeasurableSet.univ, Set.univ_inter,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private theorem eq_ratio_smul_of_mem_graded {d' : Data K ι Ω WT A} (hd : d'.AxH 𝒜) {c : ι} {G : WT} {f e : A c}
    (he : e ∈ 𝒜 c G) (he0 : e ≠ 0) (hf : f ∈ 𝒜 c G) : f = ratio (Ω := Ω c) f e • e := by
  have hnz : (⟨e, he⟩ : 𝒜 c G) ≠ 0 := fun h0 => he0 (by simpa using congrArg Subtype.val h0)
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨e, he⟩ : 𝒜 c G) hnz).mp (hd.finrank_one c G) ⟨f, hf⟩
  have hex : ∃ a : Ω c, f = a • e := ⟨a, by simpa using (congrArg Subtype.val ha).symm⟩
  rw [ratio, dite_eq_left hex]
  exact hex.choose_spec

theorem hint_meas (hd : d.AxH 𝒜) (c : ι) (sg : K →+* ℂ) {G : WT} {f : A c} (hf : f ∈ 𝒜 c G)
    (hf0 : f ≠ 0) :
    AEStronglyMeasurable (d.hintSm c sg fun P => Real.log (d.nrm c G f P))
      (blockSphereProb d.D (d.N + 1)) := by
  rw [d.hint_bsp_smul]
  exact ((hd.a13 c sg hf hf0).smul_measure _).aestronglyMeasurable

variable {d} in
theorem hint_ratio_ne (hd : d.AxH 𝒜) {c : ι} {G : WT} {f e : A c} (he : e ∈ 𝒜 c G) (he0 : e ≠ 0)
    (hf : f ∈ 𝒜 c G) (hf0 : f ≠ 0) : ratio (Ω := Ω c) f e ≠ 0 := by
  intro h0
  have h1 := eq_ratio_smul_of_mem_graded hd he he0 hf
  rw [h0, zero_smul] at h1
  exact hf0 h1

theorem hint_log_line (hd : d.AxH 𝒜) {c : ι} {G : WT} {f e : A c} (he : e ∈ 𝒜 c G) (he0 : e ≠ 0)
    (hf : f ∈ 𝒜 c G) (hf0 : f ≠ 0) (P : Ω c →+* ℂ) :
    Real.log (d.nrm c G f P) = Real.log ‖P (ratio (Ω := Ω c) f e)‖ + Real.log (d.nrm c G e P) := by
  have hfe := eq_ratio_smul_of_mem_graded hd he he0 hf
  have hr := hint_ratio_ne hd he he0 hf hf0
  calc Real.log (d.nrm c G f P)
      = Real.log (d.nrm c G (ratio (Ω := Ω c) f e • e) P) := by rw [← hfe]
    _ = _ := by
      rw [hd.nrm_smul c P _ he he0 hr,
        Real.log_mul (norm_ne_zero_iff.mpr ((map_ne_zero P).mpr hr)) (hd.nrm_pos c P he he0).ne']

theorem hint_log_mul (hd : d.AxH 𝒜) {c : ι} {G G' : WT} {f g : A c} (hf : f ∈ 𝒜 c G)
    (hg : g ∈ 𝒜 c G') (hf0 : f ≠ 0) (hg0 : g ≠ 0) (P : Ω c →+* ℂ) :
    Real.log (d.nrm c (G + G') (f * g) P) =
      Real.log (d.nrm c G f P) + Real.log (d.nrm c G' g P) := by
  rw [hd.nrm_mul c P hf hg hf0 hg0,
    Real.log_mul (hd.nrm_pos c P hf hf0).ne' (hd.nrm_pos c P hg hg0).ne']

theorem hint_pow (hd : d.AxH 𝒜) {c : ι} {G : WT} {f : A c} (hf : f ∈ 𝒜 c G) (hf0 : f ≠ 0) :
    ∀ k : ℕ, 0 < k → f ^ k ∈ 𝒜 c (k • G) ∧ f ^ k ≠ 0 ∧
      ∀ P, Real.log (d.nrm c (k • G) (f ^ k) P) = k * Real.log (d.nrm c G f P) := by
  intro k hk
  haveI := hd.graded c
  induction k with
  | zero => exact absurd hk (lt_irrefl 0)
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine ⟨by simpa using hf, by simpa using hf0, fun P => by simp⟩
    · obtain ⟨h1, h2, h3⟩ := ih hn
      have hmem : f ^ (n + 1) ∈ 𝒜 c ((n + 1) • G) := by
        rw [pow_succ, succ_nsmul]; exact SetLike.mul_mem_graded h1 hf
      have hne : f ^ (n + 1) ≠ 0 := by
        rw [pow_succ]; exact hd.mul_ne_zero c h1 hf h2 hf0
      refine ⟨hmem, hne, fun P => ?_⟩
      rw [pow_succ, succ_nsmul, hd.nrm_mul c P h1 hf h2 hf0,
        Real.log_mul (hd.nrm_pos c P h1 h2).ne' (hd.nrm_pos c P hf hf0).ne', h3 P]
      push_cast
      ring

theorem hint_log_be (hd : d.AxH 𝒜) (c : ι) (P : Ω c →+* ℂ) :
    Real.log (d.be c P) =
      Real.log (d.nrm c d.wL (d.w (d.jc c) c) P) + Real.log ‖d.hintU c P‖ := by
  have he := hd.w_mem (d.jc c) c
  have he0 := hd.w_base c
  have key : ∀ j, d.nrm c d.wL (d.w j c) P =
      ‖P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))‖ * d.nrm c d.wL (d.w (d.jc c) c) P := by
    intro j
    by_cases hj : d.w j c = 0
    · have hr : ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) = 0 := by
        have h1 := eq_ratio_smul_of_mem_graded hd he he0 (hd.w_mem j c)
        have h2 : ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) • d.w (d.jc c) c = 0 := by
          rw [← h1]; exact hj
        exact (smul_eq_zero.mp h2).resolve_right he0
      rw [hr, hj, hd.nrm_zero, map_zero, norm_zero, zero_mul]
    · rw [← hd.nrm_smul c P _ he he0 (hint_ratio_ne hd he he0 (hd.w_mem j c) hj),
        ← eq_ratio_smul_of_mem_graded hd he he0 (hd.w_mem j c)]
  have hsum : ∑ j, d.nrm c d.wL (d.w j c) P ^ 2 = d.nrm c d.wL (d.w (d.jc c) c) P ^ 2 *
      ∑ j, ‖P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [key j]; ring
  have hU : ‖d.hintU c P‖ = Real.sqrt (∑ j, ‖P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))‖ ^ 2) := by
    simp [hintU, EuclideanSpace.norm_eq]
  have hUne : ‖d.hintU c P‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro h0
    have h1 := congrArg (fun x => x (d.jc c)) h0
    exact hint_ratio_ne hd he he0 he he0 (by simpa [hintU] using h1)
  have hpos := hd.nrm_pos c P he he0
  rw [be, hsum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hpos.le, ← hU, Real.log_mul hpos.ne' hUne]

theorem hint_bdd (sg : K →+* ℂ) (c : ι) {G : WT} {f : ∀ c, A c}
    (hb : BddAbove (Set.range fun p : (Σ c, PT (Ω := Ω c) sg) => d.nrm p.1 G (f p.1) p.2)) :
    ∃ B, ∀ P ∈ PT (Ω := Ω c) sg, d.nrm c G (f c) P ≤ B := by
  obtain ⟨B, hB⟩ := hb
  exact ⟨B, fun P hP => hB ⟨⟨c, ⟨P, hP⟩⟩, rfl⟩⟩

theorem hint_log_le (hd : d.AxH 𝒜) {c : ι} {G : WT} {f : A c} (hf : f ∈ 𝒜 c G) (hf0 : f ≠ 0)
    {sg : K →+* ℂ} {B : ℝ} (hB : ∀ P ∈ PT (Ω := Ω c) sg, d.nrm c G f P ≤ B) :
    ∀ P ∈ PT (Ω := Ω c) sg, Real.log (d.nrm c G f P) ≤ Real.log B := fun P hP => Real.log_le_log (hd.nrm_pos c P hf hf0) (hB P hP)

theorem hint_thp_ne (hd : d.AxH 𝒜) (c : ι) : ∃ k, d.thp k c ≠ 0 := by
  by_contra hall
  push_neg at hall
  obtain ⟨e, he, -, h3⟩ := hd.a4
  obtain ⟨q, hq, p, hp⟩ := h3 1
  apply hq c
  have h4 := hp c
  rw [Pi.one_apply, mul_one] at h4
  rw [h4]
  refine Finset.sum_eq_zero fun k _ => ?_
  have hr : ratio (Ω := Ω c) (d.thp (hd.sel k) c) (e c) = 0 := by
    rw [hall]
    have h1 := eq_ratio_smul_of_mem_graded hd (he c).1 (he c).2 (Submodule.zero_mem _)
    exact (smul_eq_zero.mp h1.symm).resolve_right (he c).2
  rw [hr, map_zero, mul_zero]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem hint_chain (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (c : ι) (sg : K →+* ℂ) :
    d.HintIS c sg (fun P => Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P)) ∧
    d.HintIS c sg (fun P => Real.log (d.nrm c d.wL (d.w (d.jc c) c) P)) ∧
    d.HintIS c sg (fun P => Real.log (d.nrm c ((2 : ℕ) • d.G1) (d.ta1 c) P)) ∧
    (∃ e, e ∈ 𝒜 c d.wF ∧ e ≠ 0 ∧ d.HintIS c sg (fun P => Real.log (d.nrm c d.wF e P))) ∧
    d.HintIS c sg (fun P => Real.log (d.nrm c d.G2 (d.ta2 c) P)) := by
  haveI := hd.graded c
  obtain ⟨Bw, hBw⟩ := d.hint_bdd sg c (f := d.w (d.jc c)) (hd.bdd sg d.wL _ (Or.inl
    ⟨by rw [hd.WW_span]; exact Submodule.subset_span ⟨_, rfl⟩, rfl⟩))
  obtain ⟨Be, hBe⟩ := d.hint_bdd sg c
    (hd.bdd sg (d.n1 • d.wde) d.et (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  obtain ⟨Bt, hBt⟩ := d.hint_bdd sg c
    (hd.bdd sg ((2 : ℕ) • d.G1) d.ta1 (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
  obtain ⟨B2, hB2⟩ := d.hint_bdd sg c
    (hd.bdd sg d.G2 d.ta2 (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))
  obtain ⟨k, hk⟩ := d.hint_thp_ne hd c
  obtain ⟨Bh, hBh⟩ := d.hint_bdd sg c (f := d.thp k) (hd.bdd sg d.wF _ (Or.inr (Or.inl
    ⟨by rw [hd.Thp_span]; exact Submodule.subset_span ⟨k, rfl⟩, rfl⟩)))
  have hwm := hd.w_mem (d.jc c) c
  have hw0 := hd.w_base c
  have hem := hd.et_mem c
  have he0 := hd.et_ne c
  have htm := hd.firstSectionMem c
  have ht0 := hd.firstSectionNeZero c
  have h2m := hd.secondSectionMem c
  have h20 := hd.secondSectionNeZero c
  have hhm := hd.thp_mem k c
  have hn1 : 0 < d.n1 := Nat.mul_pos hd.i_ge hd.g_zero_ge_ask_sum
  have hi : (1 : ℝ) ≤ d.i := by exact_mod_cast hd.i_ge
  have hn1r : (d.n1 : ℝ) = d.i * d.g0 := by simp [Data.n1]
  have hn1r1 : (1 : ℝ) ≤ d.n1 := by exact_mod_cast hn1
  have hκ : (d.n1 : ℝ) * (d.cc / d.i) = d.g0 * d.cc := by
    rw [hn1r]; field_simp
  have hq : 1 ≤ 2 - 2 * d.cc * d.g0 := by linarith [hd.ccg0]
  have IU : d.HintIS c sg (fun P => Real.log ‖d.hintU c P‖) := d.hint_intU hd h c sg

  obtain ⟨ht1m, ht10, ht1l⟩ := d.hint_pow hd htm ht0 d.n1 hn1
  obtain ⟨he2m, he20, he2l⟩ := d.hint_pow hd hem he0 2 two_pos
  obtain ⟨hwpm, hwp0, hwpl⟩ := d.hint_pow hd hwm hw0 (2 * d.n1) (by omega)
  have hW1 : d.n1 • ((2 : ℕ) • d.G1) + (2 : ℕ) • (d.n1 • d.wde) = (2 * d.n1) • d.wL := by
    simp only [Data.G1, smul_sub, smul_smul, mul_comm d.n1 2]; abel
  have hf1m : d.ta1 c ^ d.n1 * d.et c ^ 2 ∈ 𝒜 c ((2 * d.n1) • d.wL) := by
    rw [← hW1]; exact SetLike.mul_mem_graded ht1m he2m
  have hf10 := hd.mul_ne_zero c ht1m he2m ht10 he20
  have Ir1 : d.HintIS c sg (fun P => Real.log ‖P (ratio (Ω := Ω c) (d.ta1 c ^ d.n1 * d.et c ^ 2)
      (d.w (d.jc c) c ^ (2 * d.n1)))‖) :=
    d.hint_intNorm hd h c sg _ (hint_ratio_ne hd hwpm hwp0 hf1m hf10)
  have E1 : ∀ P, (d.n1 : ℝ) * Real.log (d.nrm c ((2 : ℕ) • d.G1) (d.ta1 c) P) +
      2 * Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P) =
      Real.log ‖P (ratio (Ω := Ω c) (d.ta1 c ^ d.n1 * d.et c ^ 2)
        (d.w (d.jc c) c ^ (2 * d.n1)))‖ + 2 * d.n1 * Real.log (d.nrm c d.wL (d.w (d.jc c) c) P) := by
    intro P
    have h1 := d.hint_log_mul hd ht1m he2m ht10 he20 P
    rw [hW1, ht1l, he2l] at h1
    have h2 := d.hint_log_line hd hwpm hwp0 hf1m hf10 P
    rw [hwpl] at h2
    push_cast at h1 h2
    linarith
  have I2 : ∀ P, -(Real.log (d.nrm c d.wL (d.w (d.jc c) c) P) + Real.log ‖d.hintU c P‖) ≤
      d.tableLineDegreeFive * d.DF + d.cc / d.i * (-Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P)) +
        d.cc * d.tableLineDegreeTwo := by
    intro P; rw [← d.hint_log_be hd c P]; exact hI2be c P

  have Iet : d.HintIS c sg (fun P => Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P)) := by
    refine d.hintIS_bounds hd h (d.hint_meas hd c sg hem he0)
      (d.hintIS_lin hd h Ir1 IU (1 / (2 - 2 * d.cc * d.g0)) (-(2 * d.n1) / (2 - 2 * d.cc * d.g0))
        (-(d.n1 * Real.log Bt + 2 * d.n1 * (d.tableLineDegreeFive * d.DF + d.cc * d.tableLineDegreeTwo)) /
          (2 - 2 * d.cc * d.g0))) (fun P hP => ?_) _ (d.hint_log_le hd hem he0 hBe)
    have e1 := E1 P
    have lt := d.hint_log_le hd htm ht0 hBt P hP
    have lt2 := mul_le_mul_of_nonneg_left lt (by positivity : (0 : ℝ) ≤ d.n1)
    have ib2 := mul_le_mul_of_nonneg_left (I2 P) (by positivity : (0 : ℝ) ≤ 2 * d.n1)
    have hκ' : (d.n1 : ℝ) * (d.cc / d.i) * Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P) =
        d.g0 * d.cc * Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P) := by rw [hκ]
    have hqp : (0 : ℝ) < 2 - 2 * d.cc * d.g0 := by linarith
    rw [← sub_nonneg]
    have : ∀ x y z : ℝ, 1 / (2 - 2 * d.cc * d.g0) * x + -(2 * d.n1) / (2 - 2 * d.cc * d.g0) * y +
        -z / (2 - 2 * d.cc * d.g0) = (x - 2 * d.n1 * y - z) / (2 - 2 * d.cc * d.g0) := by
      intro x y z; ring
    rw [this, sub_nonneg, div_le_iff₀ hqp]
    nlinarith

  have Iw : d.HintIS c sg (fun P => Real.log (d.nrm c d.wL (d.w (d.jc c) c) P)) := by
    refine d.hintIS_bounds hd h (d.hint_meas hd c sg hwm hw0)
      (d.hintIS_lin hd h Iet IU (d.cc / d.i) (-1) (-(d.tableLineDegreeFive * d.DF + d.cc * d.tableLineDegreeTwo)))
      (fun P _ => ?_) _ (d.hint_log_le hd hwm hw0 hBw)
    have := I2 P
    linarith

  have It1 : d.HintIS c sg (fun P => Real.log (d.nrm c ((2 : ℕ) • d.G1) (d.ta1 c) P)) := by
    refine d.hintIS_bounds hd h (d.hint_meas hd c sg htm ht0)
      (d.hintIS_lin hd h Ir1 Iw (1 / d.n1) 2 (-(2 * Real.log Be) / d.n1)) (fun P hP => ?_) _
      (d.hint_log_le hd htm ht0 hBt)
    have e1 := E1 P
    have le := d.hint_log_le hd hem he0 hBe P hP
    have hnp : (0 : ℝ) < d.n1 := by linarith
    have : ∀ x y : ℝ, 1 / (d.n1 : ℝ) * x + 2 * y + -(2 * Real.log Be) / d.n1 =
        (x + 2 * d.n1 * y - 2 * Real.log Be) / d.n1 := by
      intro x y; field_simp; ring
    rw [this, div_le_iff₀ hnp]
    nlinarith

  obtain ⟨hwqm, hwq0, hwql⟩ := d.hint_pow hd hwm hw0 (d.D + 4) (by omega)
  have hW2 : d.wF + d.G2 = (d.D + 4) • d.wL := by rw [Data.G2]; abel
  have hf2m : d.thp k c * d.ta2 c ∈ 𝒜 c ((d.D + 4) • d.wL) := by
    rw [← hW2]; exact SetLike.mul_mem_graded hhm h2m
  have hf20 := hd.mul_ne_zero c hhm h2m hk h20
  have Ir2 : d.HintIS c sg (fun P => Real.log ‖P (ratio (Ω := Ω c) (d.thp k c * d.ta2 c)
      (d.w (d.jc c) c ^ (d.D + 4)))‖) :=
    d.hint_intNorm hd h c sg _ (hint_ratio_ne hd hwqm hwq0 hf2m hf20)
  have E2 : ∀ P, Real.log (d.nrm c d.wF (d.thp k c) P) + Real.log (d.nrm c d.G2 (d.ta2 c) P) =
      Real.log ‖P (ratio (Ω := Ω c) (d.thp k c * d.ta2 c) (d.w (d.jc c) c ^ (d.D + 4)))‖ +
        ((d.D + 4 : ℕ) : ℝ) * Real.log (d.nrm c d.wL (d.w (d.jc c) c) P) := by
    intro P
    have h1 := d.hint_log_mul hd hhm h2m hk h20 P
    rw [hW2] at h1
    have h2 := d.hint_log_line hd hwqm hwq0 hf2m hf20 P
    rw [hwql] at h2
    linarith
  refine ⟨Iet, Iw, It1, ⟨d.thp k c, hhm, hk, ?_⟩, ?_⟩
  · refine d.hintIS_bounds hd h (d.hint_meas hd c sg hhm hk)
      (d.hintIS_lin hd h Ir2 Iw 1 ((d.D + 4 : ℕ) : ℝ) (-Real.log B2)) (fun P hP => ?_) _
      (d.hint_log_le hd hhm hk hBh)
    have e2 := E2 P
    have l2 := d.hint_log_le hd h2m h20 hB2 P hP
    linarith
  · refine d.hintIS_bounds hd h (d.hint_meas hd c sg h2m h20)
      (d.hintIS_lin hd h Ir2 Iw 1 ((d.D + 4 : ℕ) : ℝ) (-Real.log Bh)) (fun P hP => ?_) _
      (d.hint_log_le hd h2m h20 hB2)
    have e2 := E2 P
    have l2 := d.hint_log_le hd hhm hk hBh P hP
    linarith

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

private theorem hintIS_log_nrm_of_mem_graded (hd : d.AxH 𝒜) (h : d.S1) {c : ι} {sg : K →+* ℂ} {G : WT}
    {f e : A c} (he : e ∈ 𝒜 c G) (he0 : e ≠ 0) (hf : f ∈ 𝒜 c G) (hf0 : f ≠ 0)
    (hI : d.HintIS c sg (fun P => Real.log (d.nrm c G e P))) :
    d.HintIS c sg (fun P => Real.log (d.nrm c G f P)) := by
  have h1 := d.hint_intNorm hd h c sg (ratio (Ω := Ω c) f e) (d.hint_ratio_ne hd he he0 hf hf0)
  have h2 := d.hintIS_lin hd h (φ₁ := fun P => Real.log ‖P (ratio (Ω := Ω c) f e)‖) h1 hI 1 1 0
  refine d.hintIS_congr hd h (ψ := fun P => Real.log (d.nrm c G f P)) h2 ?_
  intro P _
  try dsimp only
  rw [d.hint_log_line hd he he0 hf hf0 P]
  ring

theorem int_Nsg (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (c : ι) (sg : K →+* ℂ) :
    (∀ (G : WT) (f : A c), G ∈ ({d.wL, d.n1 • d.wde, (2 : ℕ) • d.G1, d.wF, d.G2} : Set WT) →
      f ∈ 𝒜 c G → f ≠ 0 →
      MeasureTheory.Integrable (fun z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) =>
        ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)),
          Real.log (d.nrm c G f P)) (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1))) ∧
    (∀ f : A c, f ∈ 𝒜 c d.wL → f ≠ 0 →
      MeasureTheory.Integrable (fun z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) =>
        ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)),
          Real.log (d.nrm c d.wL f P / d.be c P)) (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1))) := by
  obtain ⟨h_et, h_w, h_ta1, ⟨e, he, he0, h_e⟩, h_ta2⟩ := d.hint_chain hd h hI2be c sg
  have hL : ∀ f : A c, f ∈ 𝒜 c d.wL → f ≠ 0 →
      d.HintIS c sg (fun P => Real.log (d.nrm c d.wL f P)) :=
    fun f hf hf0 => hintIS_log_nrm_of_mem_graded d hd h (hd.w_mem (d.jc c) c) (hd.w_base c) hf hf0 h_w
  refine ⟨fun G f hG hf hf0 => ?_, fun f hf hf0 => ?_⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hG
    rcases hG with rfl | rfl | rfl | rfl | rfl
    · exact hL f hf hf0
    · exact hintIS_log_nrm_of_mem_graded d hd h (hd.et_mem c) (hd.et_ne c) hf hf0 h_et
    · exact hintIS_log_nrm_of_mem_graded d hd h (hd.firstSectionMem c) (hd.firstSectionNeZero c) hf hf0 h_ta1
    · exact hintIS_log_nrm_of_mem_graded d hd h he he0 hf hf0 h_e
    · exact hintIS_log_nrm_of_mem_graded d hd h (hd.secondSectionMem c) (hd.secondSectionNeZero c) hf hf0 h_ta2
  · have h3 := d.hintIS_lin hd h (hL f hf hf0) h_w 1 (-1) 0
    have h4 := d.hintIS_lin hd h (φ₂ := fun P => Real.log ‖d.hintU c P‖) h3
      (d.hint_intU hd h c sg) 1 (-1) 0
    refine d.hintIS_congr hd h (ψ := fun P => Real.log (d.nrm c d.wL f P / d.be c P)) h4 ?_
    intro P _
    try dsimp only
    have hpos := hd.nrm_pos c P hf hf0
    have hw := hd.nrm_pos c P (hd.w_mem (d.jc c) c) (hd.w_base c)
    have hU := d.hint_one_le_U hd c P
    have hbe : d.be c P ≠ 0 := by
      rw [d.hint_be_eq hd c P]
      exact (mul_pos hw (lt_of_lt_of_le one_pos hU)).ne'
    rw [Real.log_div hpos.ne' hbe, d.hint_log_be hd c P]
    ring

end Data

end ReciprocityTheory.ChartRestriction.G.T0
