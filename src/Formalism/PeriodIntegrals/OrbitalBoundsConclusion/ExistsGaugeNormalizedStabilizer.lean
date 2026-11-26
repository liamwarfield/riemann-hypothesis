module

public import Mathlib

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.ExistsGaugeMeasureForEachRank
noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.ExistsGaugeMeasureForEachRank

def UH {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) : Set (Matrix ι ι ℂ) :=
  {g | gᴴ * H * g = H}

def eI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) := ⟨a.val, by omega⟩

def esI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) := ⟨2 * r + k - a.val, by omega⟩

def Hpk (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun i j =>
  if i.val < r ∧ i.val + j.val = 2 * r + k then 1
  else if j.val < r ∧ i.val + j.val = 2 * r + k then 1
  else if r ≤ i.val ∧ i.val ≤ r + k ∧ i = j then (if i.val = r + k then -1 else 1)
  else 0

def bvec {m : ℕ} (i : Fin m) : Fin m → ℂ := Pi.single i 1

abbrev Mt (k r : ℕ) := Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ

def lmulM {k r : ℕ} (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (x : Mt k r) : Mt k r :=
  a * Matrix.of x

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

abbrev GV (k r : ℕ) : Set (Mat k r) := UH (Hpk k r)

def UWb (k r : ℕ) : Set (Mat k r) :=
  {g | g ∈ GV k r ∧ ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)}

def IsHaarOn {k r : ℕ} (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
    (μ : Measure (Mt k r)) : Prop :=
  SigmaFinite μ ∧ μ ≠ 0 ∧ μ {x | Matrix.of x ∉ S} = 0 ∧
    ∀ s ∈ S, μ.map (lmulM s) = μ

def realifyFun {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) : Fin m × Fin m × Bool → ℝ :=
  fun p => if p.2.2 then (X p.1 p.2.1).im else (X p.1 p.2.1).re

def unrealify {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => ⟨x (i, j, false), x (i, j, true)⟩

def lieOf {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : Set (Matrix (Fin m) (Fin m) ℂ) :=
  {X | ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ S}

def lieE {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : Submodule ℝ (EuclideanSpace ℝ (Fin m × Fin m × Bool)) :=
  Submodule.span ℝ ((fun X => (WithLp.equiv 2 _).symm (realifyFun X)) '' lieOf S)

variable {k r : ℕ}

def expBall (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (ρ : ℝ) : Set (Mt k r) :=
  (fun x : lieE S =>
      fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j) '' Metric.ball 0 ρ

def IsGaugeOn (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (μ : Measure (Mt k r)) : Prop :=
  IsHaarOn S μ ∧
    Tendsto (fun ρ : ℝ => (μ (expBall S ρ)).toReal / (volume (Metric.ball (0 : lieE S) ρ)).toReal)
      (𝓝[>] 0) (𝓝 1)

def ExistsGaugeMeasureForEachRank : Prop := ∀ r : ℕ, ∃ μ : Measure (Mt 0 r), IsGaugeOn (UWb 0 r) μ

end PI.ExistsGaugeMeasureForEachRank
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CircleGaugeAction.ContinuousLmulM
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CircleGaugeAction.DglApplyOff
noncomputable section

open Matrix

namespace PI.ExistsGaugeMeasureForEachRank.W

variable {r : ℕ}

def cI (r : ℕ) : Fin (2 * r + 0 + 1) := ⟨r, by omega⟩

def dgl (r : ℕ) (u : ℂ) : Mat 0 r := diagonal (fun i => if i = cI r then u else 1)

lemma dgl_apply (u : ℂ) (i j : Fin (2 * r + 0 + 1)) :
    dgl r u i j = if i = j then (if i = cI r then u else 1) else 0 := by
  unfold dgl
  rw [Matrix.diagonal_apply]

lemma dgl_apply_off (u : ℂ) (i j : Fin (2 * r + 0 + 1)) (h : ¬ (i = cI r ∧ j = cI r)) :
    dgl r u i j = (1 : Mat 0 r) i j := by
  rw [dgl_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    have hi : i ≠ cI r := fun hi => h ⟨hi, hi⟩
    simp [hi]
  · simp [hij]

lemma rev_eq_c_iff (p : Fin (2 * r + 0 + 1)) : Fin.rev p = cI r ↔ p = cI r := by
  rw [Fin.ext_iff, Fin.ext_iff, Fin.val_rev]
  simp only [cI]
  have := p.isLt
  omega

lemma Hpk_apply (p q : Fin (2 * r + 0 + 1)) :
    Hpk 0 r p q = if q = Fin.rev p then (if p = cI r then -1 else 1) else 0 := by
  have hp := p.isLt
  have hq := q.isLt
  simp only [Hpk, Fin.ext_iff, Fin.val_rev, cI]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma dgl_mem {u : ℂ} (hu : (starRingEnd ℂ) u * u = 1) : dgl r u ∈ UWb 0 r := by
  refine ⟨?_, fun a => ⟨?_, ?_⟩⟩
  · show (dgl r u)ᴴ * Hpk 0 r * dgl r u = Hpk 0 r
    ext p q
    simp only [dgl, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, Matrix.mul_diagonal, Pi.star_apply]
    rw [Hpk_apply]
    by_cases hq : q = Fin.rev p
    · subst hq
      by_cases hp : p = cI r
      · subst hp
        have hc : Fin.rev (cI r) = cI r := (rev_eq_c_iff _).2 rfl
        simp only [hc, if_true]
        show star u * -1 * u = -1
        rw [show star u = (starRingEnd ℂ) u from rfl]
        linear_combination -hu
      · have hc : Fin.rev p ≠ cI r := fun h => hp ((rev_eq_c_iff p).1 h)
        simp [hp, hc]
    · simp [hq]
  · have hne : eI 0 r a ≠ cI r := by
      intro h
      have := congrArg Fin.val h
      simp [eI, cI] at this
      omega
    simp only [bvec, dgl, Matrix.diagonal_mulVec_single, if_neg hne, one_mul]
  · have hne : esI 0 r a ≠ cI r := by
      intro h
      have := congrArg Fin.val h
      simp [esI, cI] at this
      omega
    simp only [bvec, dgl, Matrix.diagonal_mulVec_single, if_neg hne, one_mul]

lemma col_fix {g : Mat 0 r} (hg : g ∈ UWb 0 r) (j : Fin (2 * r + 0 + 1)) (hj : j ≠ cI r)
    (i : Fin (2 * r + 0 + 1)) : g i j = if i = j then 1 else 0 := by
  have hjl := j.isLt
  have hcol : g *ᵥ bvec j = bvec j := by
    rcases lt_or_gt_of_ne (show j.val ≠ r from fun h => hj (Fin.ext h)) with h | h
    · have := (hg.2 ⟨j.val, h⟩).1
      have e : eI 0 r ⟨j.val, h⟩ = j := Fin.ext rfl
      rwa [e] at this
    · have := (hg.2 ⟨2 * r - j.val, by omega⟩).2
      have e : esI 0 r ⟨2 * r - j.val, by omega⟩ = j := Fin.ext (by simp [esI]; omega)
      rwa [e] at this
  have := congrFun hcol i
  rw [bvec, Matrix.mulVec_single_one, Pi.single_apply] at this
  simpa [Matrix.col] using this

lemma conjT_mul_H {g : Mat 0 r} (hg : g ∈ UWb 0 r) (p : Fin (2 * r + 0 + 1)) (hp : p ≠ cI r)
    (k : Fin (2 * r + 0 + 1)) : (gᴴ * Hpk 0 r) p k = Hpk 0 r p k := by
  simp [Matrix.mul_apply, col_fix hg p hp]

lemma col_c {g : Mat 0 r} (hg : g ∈ UWb 0 r) (q : Fin (2 * r + 0 + 1)) (hq : q ≠ cI r) :
    g q (cI r) = 0 := by
  have hp : Fin.rev q ≠ cI r := fun h => hq ((rev_eq_c_iff q).1 h)
  have hU : gᴴ * Hpk 0 r * g = Hpk 0 r := hg.1
  have h1 := congrFun (congrFun hU (Fin.rev q)) (cI r)
  rw [Matrix.mul_apply] at h1
  simp only [conjT_mul_H hg _ hp] at h1
  simp [Hpk_apply, Fin.rev_rev, hp, Ne.symm hq] at h1
  exact h1

lemma eq_dgl {g : Mat 0 r} (hg : g ∈ UWb 0 r) : g = dgl r (g (cI r) (cI r)) := by
  ext i j
  rw [dgl_apply]
  by_cases hj : j = cI r
  · subst hj
    by_cases hi : i = cI r
    · subst hi
      simp
    · rw [col_c hg i hi]
      simp [hi]
  · rw [col_fix hg j hj i]
    by_cases hij : i = j
    · subst hij
      simp [hj]
    · simp [hij]

lemma dgl_norm {u : ℂ} (h : dgl r u ∈ UWb 0 r) : (starRingEnd ℂ) u * u = 1 := by
  have hU : (dgl r u)ᴴ * Hpk 0 r * dgl r u = Hpk 0 r := h.1
  have h1 := congrFun (congrFun hU (cI r)) (cI r)
  have hc : Fin.rev (cI r) = cI r := (rev_eq_c_iff (cI r)).2 rfl
  simp only [dgl, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Pi.star_apply, if_true] at h1
  rw [Hpk_apply] at h1
  simp only [hc, if_true] at h1
  show (starRingEnd ℂ) u * u = 1
  rw [show (starRingEnd ℂ) u = star u from rfl]
  linear_combination -h1

theorem mem_UWb_iff (g : Mat 0 r) :
    g ∈ UWb 0 r ↔ ∃ u : ℂ, (starRingEnd ℂ) u * u = 1 ∧ g = dgl r u := by
  constructor
  · intro hg
    have e := eq_dgl hg
    exact ⟨g (cI r) (cI r), dgl_norm (e ▸ hg), e⟩
  · rintro ⟨u, hu, rfl⟩
    exact dgl_mem hu

lemma conj_mul_iff (u : ℂ) : (starRingEnd ℂ) u * u = 1 ↔ ‖u‖ = 1 := by
  rw [Complex.conj_mul']
  norm_cast
  exact pow_eq_one_iff_of_nonneg (norm_nonneg u) two_ne_zero

lemma dgl_mul (u v : ℂ) : dgl r u * dgl r v = dgl r (u * v) := by
  simp only [dgl, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

end PI.ExistsGaugeMeasureForEachRank.W
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CircleGaugeAction.OfRealCoordsSmulCenterCoord
noncomputable section

open Matrix Filter Topology

namespace PI.ExistsGaugeMeasureForEachRank.W

variable {r : ℕ}

def dz (r : ℕ) (z : ℂ) : Mat 0 r := diagonal (Pi.single (cI r) z)

lemma exp_dz (z : ℂ) : NormedSpace.exp (dz r z) = dgl r (Complex.exp z) := by
  rw [dz, Matrix.exp_diagonal, dgl]
  congr 1
  funext i
  rw [Pi.coe_exp]
  by_cases h : i = cI r
  · subst h
    simp [← Complex.exp_eq_exp_ℂ]
  · simp [h]

lemma smul_dz (t z : ℂ) : t • dz r z = dz r (t * z) := by
  rw [dz, dz, ← Matrix.diagonal_smul, ← Pi.single_smul', smul_eq_mul]

lemma dz_mem_lie (s : ℝ) : dz r ((s : ℂ) * Complex.I) ∈ lieOf (UWb 0 r) := by
  intro t
  rw [smul_dz, exp_dz]
  apply dgl_mem
  rw [conj_mul_iff, Complex.norm_exp]
  simp

set_option backward.isDefEq.respectTransparency false in
open scoped Norms.Operator in
lemma entry_zero {X : Mat 0 r} (hX : X ∈ lieOf (UWb 0 r)) (i j : Fin (2 * r + 0 + 1))
    (hij : ¬ (i = cI r ∧ j = cI r)) : X i j = 0 := by
  letI : NormedRing (Mat 0 r) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat 0 r) := Matrix.linftyOpNormedAlgebra
  have hconst : ∀ t : ℝ, (NormedSpace.exp (t • X)) i j = (1 : Mat 0 r) i j := by
    intro t
    have hm := hX t
    rw [Complex.coe_smul] at hm
    rw [eq_dgl hm, dgl_apply_off _ _ _ hij]
  let L : Mat 0 r →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  have hd := (L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_exp_smul_const X (0 : ℝ)))
  have hfun : (L ∘ fun t : ℝ => NormedSpace.exp (t • X)) = fun _ => (1 : Mat 0 r) i j :=
    funext hconst
  rw [hfun] at hd
  have h0 := hd.unique (hasDerivAt_const (0 : ℝ) ((1 : Mat 0 r) i j))
  simpa [L] using h0

lemma eq_dz_of_lie {X : Mat 0 r} (hX : X ∈ lieOf (UWb 0 r)) : X = dz r (X (cI r) (cI r)) := by
  ext i j
  by_cases h : i = cI r ∧ j = cI r
  · obtain ⟨rfl, rfl⟩ := h
    simp [dz]
  · rw [entry_zero hX i j h, dz, diagonal_apply]
    split_ifs with hij
    · subst hij
      have hi : i ≠ cI r := fun hi => h ⟨hi, hi⟩
      simp [hi]
    · rfl

theorem lieOf_iff (X : Mat 0 r) :
    X ∈ lieOf (UWb 0 r) ↔ ∃ s : ℝ, X = dz r ((s : ℂ) * Complex.I) := by
  constructor
  · intro hX
    have hX' := eq_dz_of_lie hX
    set x := X (cI r) (cI r)
    have h1 := hX 1
    rw [hX', Complex.ofReal_one, one_smul, exp_dz] at h1
    have hn := (conj_mul_iff _).1 (dgl_norm h1)
    rw [Complex.norm_exp, Real.exp_eq_one_iff] at hn
    refine ⟨x.im, hX'.trans ?_⟩
    congr 1
    apply Complex.ext <;> simp [hn]
  · rintro ⟨s, rfl⟩
    exact dz_mem_lie s

def v0 (r : ℕ) : EuclideanSpace ℝ (Fin (2 * r + 0 + 1) × Fin (2 * r + 0 + 1) × Bool) :=
  EuclideanSpace.single (cI r, cI r, true) 1

lemma norm_v0_eq_one : ‖v0 r‖ = 1 := by
  simp [v0]

lemma v0_ne : v0 r ≠ 0 := by
  intro h
  have := norm_v0_eq_one (r := r)
  rw [h, norm_zero] at this
  exact zero_ne_one this

lemma realify_dz (s : ℝ) :
    (WithLp.equiv 2 _).symm (realifyFun (dz r ((s : ℂ) * Complex.I))) = s • v0 r := by
  ext ⟨i, j, b⟩
  simp only [WithLp.equiv_symm_apply, realifyFun, v0, dz, diagonal_apply, PiLp.smul_apply,
    PiLp.single_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i = cI r
    · subst hi
      cases b <;> simp
    · cases b <;> simp [hi]
  · cases b <;> simp [hij] <;> intro hi hj <;> exact absurd (hi.trans hj.symm) hij

lemma ofRealCoords_smul_centerCoord (s : ℝ) : unrealify (s • v0 r) = dz r ((s : ℂ) * Complex.I) := by
  ext i j
  apply Complex.ext
  · simp only [unrealify, v0, dz, diagonal_apply, PiLp.smul_apply, PiLp.single_apply,
      smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      by_cases hi : i = cI r
      · subst hi
        simp
      · simp [hi]
    · simp [hij]
  · simp only [unrealify, v0, dz, diagonal_apply, PiLp.smul_apply, PiLp.single_apply,
      smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      by_cases hi : i = cI r
      · subst hi
        simp
      · simp [hi]
    · simp [hij]
      intro hi hj
      exact absurd (hi.trans hj.symm) hij

theorem lieE_eq : lieE (UWb 0 r) = Submodule.span ℝ {v0 r} := by
  apply le_antisymm
  · rw [lieE, Submodule.span_le]
    rintro _ ⟨X, hX, rfl⟩
    obtain ⟨s, rfl⟩ := (lieOf_iff X).1 hX
    beta_reduce
    rw [realify_dz]
    exact Submodule.smul_mem _ s (Submodule.subset_span rfl)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    apply Submodule.subset_span
    refine ⟨dz r ((1 : ℝ) * Complex.I), dz_mem_lie 1, ?_⟩
    beta_reduce
    rw [realify_dz, one_smul]

end PI.ExistsGaugeMeasureForEachRank.W
end
end

noncomputable section

open Matrix MeasureTheory Filter Topology Set Real
open scoped ENNReal

namespace PI.ExistsGaugeMeasureForEachRank.W

variable {r : ℕ}

instance fact_two_pi : Fact (0 < 2 * π) := ⟨by positivity⟩

def Gm (r : ℕ) (θ : AddCircle (2 * π)) : Mt 0 r :=
  fun i j => dgl r ((AddCircle.toCircle θ : Circle) : ℂ) i j

lemma toCircle_coe (s : ℝ) :
    ((AddCircle.toCircle (s : AddCircle (2 * π)) : Circle) : ℂ) = Complex.exp (s * Complex.I) := by
  rw [AddCircle.toCircle_apply_mk, div_self (ne_of_gt fact_two_pi.out), one_mul, Circle.coe_exp]

lemma continuous_Gm : Continuous (Gm r) := by
  have hc : Continuous fun θ : AddCircle (2 * π) => ((AddCircle.toCircle θ : Circle) : ℂ) :=
    continuous_subtype_val.comp AddCircle.continuous_toCircle
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Gm, dgl_apply]
  split_ifs
  · exact hc
  · exact continuous_const
  · exact continuous_const

lemma Gm_injective : Function.Injective (Gm r) := by
  intro a b h
  have := congrFun (congrFun h (cI r)) (cI r)
  simp only [Gm, dgl_apply] at this
  exact AddCircle.injective_toCircle (ne_of_gt fact_two_pi.out) (Circle.ext this)

lemma me_Gm : MeasurableEmbedding (Gm r) :=
  (continuous_Gm.isClosedEmbedding Gm_injective).measurableEmbedding

lemma Gm_mem (θ : AddCircle (2 * π)) : Matrix.of (Gm r θ) ∈ UWb 0 r := by
  show dgl r _ ∈ UWb 0 r
  exact dgl_mem ((conj_mul_iff _).2 (Circle.norm_coe _))

lemma continuous_lmulM (a : Mat 0 r) : Continuous (lmulM (k := 0) (r := r) a) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  change Continuous (fun x : Mt 0 r => ∑ l, a i l * x l j)
  refine continuous_finsetSum _ fun l _ => continuous_const.mul ?_
  have h : Continuous (fun x : Mt 0 r => x l) := continuous_apply l
  exact (continuous_apply j).comp h

lemma Gm_add (a b : AddCircle (2 * π)) :
    Gm r (a + b) = lmulM (dgl r ((AddCircle.toCircle a : Circle) : ℂ)) (Gm r b) := by
  have : lmulM (dgl r ((AddCircle.toCircle a : Circle) : ℂ)) (Gm r b) =
      dgl r ((AddCircle.toCircle a : Circle) : ℂ) * dgl r ((AddCircle.toCircle b : Circle) : ℂ) := rfl
  have h2 : ((AddCircle.toCircle (a + b) : Circle) : ℂ) =
      ((AddCircle.toCircle a : Circle) : ℂ) * ((AddCircle.toCircle b : Circle) : ℂ) := by
    rw [AddCircle.toCircle_add, Circle.coe_mul]
  rw [this, dgl_mul]
  unfold Gm
  rw [h2]

def μG (r : ℕ) : Measure (Mt 0 r) := Measure.map (Gm r) volume

lemma map_lmul (s : Mat 0 r) (hs : s ∈ UWb 0 r) : (μG r).map (lmulM s) = μG r := by
  obtain ⟨u, hu, rfl⟩ := (mem_UWb_iff s).1 hs
  rw [conj_mul_iff] at hu
  have hα : ((AddCircle.toCircle ((Complex.arg u : ℝ) : AddCircle (2 * π)) : Circle) : ℂ) = u := by
    rw [toCircle_coe]
    have := Complex.norm_mul_exp_arg_mul_I u
    rw [hu] at this
    simpa using this
  unfold μG
  rw [Measure.map_map (continuous_lmulM _).measurable continuous_Gm.measurable]
  have hcomp : lmulM (dgl r u) ∘ Gm r =
      Gm r ∘ (fun θ => ((Complex.arg u : ℝ) : AddCircle (2 * π)) + θ) := by
    funext θ
    simp only [Function.comp_apply]
    rw [Gm_add, hα]
  rw [hcomp, ← Measure.map_map continuous_Gm.measurable (measurable_const_add _),
    map_add_left_eq_self]

lemma isHaar : IsHaarOn (UWb 0 r) (μG r) := by
  refine ⟨?_, ?_, ?_, fun s hs => map_lmul s hs⟩
  · unfold μG; infer_instance
  · unfold μG
    rw [Ne, Measure.map_eq_zero_iff continuous_Gm.measurable.aemeasurable]
    intro h
    have h1 := AddCircle.measure_univ (2 * π)
    rw [h, Measure.coe_zero, Pi.zero_apply, eq_comm, ENNReal.ofReal_eq_zero] at h1
    linarith [Real.pi_pos]
  · unfold μG
    rw [me_Gm.map_apply]
    have : Gm r ⁻¹' {x | Matrix.of x ∉ UWb 0 r} = ∅ := by
      ext θ
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact Gm_mem θ
    rw [this, measure_empty]

lemma expBall_eq (ρ : ℝ) :
    expBall (UWb 0 r) ρ = Gm r '' (((↑) : ℝ → AddCircle (2 * π)) '' Ioo (-ρ) ρ) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x.1 ∈ Submodule.span ℝ {v0 r} := by
      rw [← lieE_eq]; exact x.2
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.1 hx'
    have hn : ‖x.1‖ = |s| := by
      rw [← hs, norm_smul, norm_v0_eq_one, mul_one, Real.norm_eq_abs]
    have hlt : |s| < ρ := by
      rw [← hn]; exact mem_ball_zero_iff.1 hx
    refine ⟨(s : AddCircle (2 * π)), ⟨s, abs_lt.1 hlt, rfl⟩, ?_⟩
    show Gm r s = fun i j => NormedSpace.exp (unrealify x.1) i j
    rw [← hs, ofRealCoords_smul_centerCoord, exp_dz]
    unfold Gm
    rw [toCircle_coe]
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    have hmem : s • v0 r ∈ lieE (UWb 0 r) := by
      rw [lieE_eq]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    refine ⟨⟨s • v0 r, hmem⟩, ?_, ?_⟩
    · rw [mem_ball_zero_iff]
      show ‖s • v0 r‖ < ρ
      rw [norm_smul, norm_v0_eq_one, mul_one, Real.norm_eq_abs, abs_lt]
      exact hs
    · show (fun i j => NormedSpace.exp (unrealify (s • v0 r)) i j) = Gm r s
      rw [ofRealCoords_smul_centerCoord, exp_dz]
      unfold Gm
      rw [toCircle_coe]

lemma vol_arc {ρ : ℝ} (hρ : ρ ≤ π) :
    volume (((↑) : ℝ → AddCircle (2 * π)) '' Ioo (-ρ) ρ) = ENNReal.ofReal (2 * ρ) := by
  have hopen : IsOpen (((↑) : ℝ → AddCircle (2 * π)) '' Ioo (-ρ) ρ) :=
    QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  rw [AddCircle.add_projection_respects_measure (2 * π) (-π) hopen.measurableSet]
  have hsub : Ioo (-ρ) ρ ⊆ Ioc (-π) (-π + 2 * π) := by
    intro θ hθ; constructor <;> linarith [hθ.1, hθ.2]
  have : ((↑) : ℝ → AddCircle (2 * π)) ⁻¹' (((↑) : ℝ → AddCircle (2 * π)) '' Ioo (-ρ) ρ) ∩
      Ioc (-π) (-π + 2 * π) = Ioo (-ρ) ρ := by
    ext θ
    constructor
    · rintro ⟨⟨θ', h1, he⟩, h3⟩
      rw [AddCircle.coe_eq_coe_iff_of_mem_Ioc (hsub h1) h3] at he
      exact he ▸ h1
    · intro h
      exact ⟨⟨θ, h, rfl⟩, hsub h⟩
  rw [this, Real.volume_Ioo]
  congr 1; ring

lemma finrank_lie : Module.finrank ℝ (lieE (UWb 0 r)) = 1 := by
  rw [lieE_eq]; exact finrank_span_singleton v0_ne

lemma vol_ball {ρ : ℝ} (h0 : 0 ≤ ρ) :
    volume (Metric.ball (0 : lieE (UWb 0 r)) ρ) = ENNReal.ofReal (2 * ρ) := by
  have : Nontrivial (lieE (UWb 0 r)) := Module.nontrivial_of_finrank_eq_succ finrank_lie
  rw [InnerProductSpace.volume_ball, finrank_lie]
  simp only [pow_one, Nat.cast_one]
  have hg : Real.Gamma (1 / 2 + 1) = √π / 2 := by
    rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]; ring
  have hs : √π / (√π / 2) = 2 := by
    have : √π ≠ 0 := Real.sqrt_ne_zero'.2 Real.pi_pos
    field_simp
  rw [hg, hs, ← ENNReal.ofReal_mul h0, mul_comm]

theorem gauge (r : ℕ) : IsGaugeOn (UWb 0 r) (μG r) := by
  refine ⟨isHaar, ?_⟩
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Ioo_mem_nhdsGT Real.pi_pos] with ρ hρ
  rw [μG, me_Gm.map_apply, expBall_eq, Gm_injective.preimage_image, vol_arc hρ.2.le,
    vol_ball hρ.1.le, div_self]
  rw [ENNReal.toReal_ofReal (by linarith [hρ.1])]
  linarith [hρ.1]

end PI.ExistsGaugeMeasureForEachRank.W
end
end

theorem exists_gaugeNormalizedStabilizer : PI.ExistsGaugeMeasureForEachRank.ExistsGaugeMeasureForEachRank := fun r => ⟨PI.ExistsGaugeMeasureForEachRank.W.μG r, PI.ExistsGaugeMeasureForEachRank.W.gauge r⟩
