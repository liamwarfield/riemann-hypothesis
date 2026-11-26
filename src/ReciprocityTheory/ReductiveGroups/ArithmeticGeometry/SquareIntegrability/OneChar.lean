module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PrjMemOfSpan
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ActOmegaExpand
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ExistsMinNorm
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.EmbComb
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.NormProjectionSq
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

private lemma Hf_im_IR_lemma {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)}
    (hI : ∀ x ∈ I, ∀ y ∈ I, (Hf x y).im = 0) {x y : Vsp dim} (hx : x ∈ IR I) (hy : y ∈ IR I) :
    (Hf x y).im = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy => exact hI x hx y hy
    | zero => simp [Hf]
    | add y z _ _ h1 h2 =>
      have e : Hf x (y + z) = Hf x y + Hf x z := by
        simp only [Hf, PiLp.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
      rw [e, Complex.add_im, h1, h2, add_zero]
    | smul r y _ h =>
      have e : Hf x (r • y) = (r : ℂ) * Hf x y := by
        unfold Hf
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [Complex.conj_ofReal]
        ring
      simp [e, h]
  | zero => simp [Hf]
  | add a b _ _ h1 h2 =>
    have e : Hf (a + b) y = Hf a y + Hf b y := by
      simp only [Hf, PiLp.add_apply, add_mul, Finset.sum_add_distrib]
    rw [e, Complex.add_im, h1, h2, add_zero]
  | smul r a _ h =>
    have e : Hf (r • a) y = (r : ℂ) * Hf a y := by
      unfold Hf
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp
      ring
    simp [e, h]

lemma norm_projection_sq [IsCMField E] {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)}
    (hI : ∀ x ∈ I, ∀ y ∈ I, (Hf x y).im = 0) (σ : E →+* ℂ) (u : Vsp dim)
    (h1 : Mc σ 1 u ∈ IR I) (hi : Mc σ Complex.I u ∈ IR I) :
    ‖Mc σ 1 u‖ ^ 2 = 2 * ‖prj σ u‖ ^ 2 := by
  classical
  have hσ : ComplexEmbedding.conjugate σ ≠ σ := fun h =>
    (InfinitePlace.isComplex_mk_iff.1 (IsTotallyComplex.isComplex (InfinitePlace.mk σ)))
      (ComplexEmbedding.isReal_iff.2 h)
  have hσ' : σ ≠ ComplexEmbedding.conjugate σ := fun h => hσ h.symm
  set S1 : ℝ := ∑ i : Idx dim, if i.1 = σ then ‖u i‖ ^ 2 else 0 with hS1
  set S2 : ℝ := ∑ i : Idx dim, if i.1 = ComplexEmbedding.conjugate σ then ‖u i‖ ^ 2 else 0 with hS2
  have e1 : ‖Mc σ 1 u‖ ^ 2 = S1 + S2 := by
    rw [EuclideanSpace.norm_sq_eq, hS1, hS2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases eq_or_ne i.1 σ with h1 | h1
    · simp [Mc_apply, h1, hσ']
    · by_cases h2 : i.1 = ComplexEmbedding.conjugate σ
      · simp [Mc_apply, h1, h2, hσ]
      · simp [Mc_apply, h1, h2]
  have e2 : ‖prj σ u‖ ^ 2 = S1 := by
    rw [EuclideanSpace.norm_sq_eq, hS1]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h1 : i.1 = σ <;> simp [prj_apply, h1]
  have e3 : (Hf (Mc σ 1 u) (Mc σ Complex.I u)).im = S2 - S1 := by
    rw [Hf, Complex.im_sum, hS1, hS2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases eq_or_ne i.1 σ with h1 | h1
    · simp [Mc_apply, h1, hσ', Complex.mul_im, Complex.sq_norm, Complex.normSq_apply] <;> ring
    · by_cases h2 : i.1 = ComplexEmbedding.conjugate σ
      · simp [Mc_apply, h1, h2, hσ, Complex.mul_im, Complex.sq_norm, Complex.normSq_apply] <;> ring
      · simp [Mc_apply, h1, h2]
  have e4 := Hf_im_IR_lemma hI h1 hi
  linarith

lemma orth_prj [IsCMField E] {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)}
    (hI : ∀ x ∈ I, ∀ y ∈ I, (Hf x y).im = 0) (σ : E →+* ℂ) {t y : Vsp dim} (ht : t ∈ IR I)
    (hy : ∀ c, Mc σ c y ∈ IR I) (horth : ∀ c, inner ℝ t (Mc σ c y) = 0) :
    Hf (prj σ t) (prj σ y) = 0 := by
  classical
  have hσ : ComplexEmbedding.conjugate σ ≠ σ := fun h =>
    (InfinitePlace.isComplex_mk_iff.1 (IsTotallyComplex.isComplex (InfinitePlace.mk σ)))
      (ComplexEmbedding.isReal_iff.2 h)
  have hσ' : σ ≠ ComplexEmbedding.conjugate σ := fun h => hσ h.symm
  have hre : ∀ a : Vsp dim, inner ℝ t a = (Hf t a).re := by
    intro a
    rw [PiLp.inner_apply, Hf, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Complex.inner, Complex.mul_re]
    ring
  have key : ∀ c : ℂ, Hf t (Mc σ c y) = (starRingEnd ℂ) c * Hf (prj σ t) (prj σ y) +
      c * Hf (prj (ComplexEmbedding.conjugate σ) t) (prj (ComplexEmbedding.conjugate σ) y) := by
    intro c
    rw [Hf, Hf, Hf, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases eq_or_ne i.1 σ with h1 | h1
    · simp [Mc_apply, prj_apply, h1, hσ'] <;> ring
    · by_cases h2 : i.1 = ComplexEmbedding.conjugate σ
      · simp [Mc_apply, prj_apply, h1, h2, hσ] <;> ring
      · simp [Mc_apply, prj_apply, h1, h2]
  have hz : ∀ c : ℂ, Hf t (Mc σ c y) = 0 := fun c =>
    Complex.ext (by rw [← hre]; simpa using horth c) (by simpa using Hf_im_IR_lemma hI ht (hy c))
  have e1 := (key 1).symm.trans (hz 1)
  have e2 := (key Complex.I).symm.trans (hz Complex.I)
  rw [map_one] at e1
  rw [Complex.conj_I] at e2
  linear_combination (1 / 2 : ℂ) * e1 + (Complex.I / 2) * e2 +
    ((Hf (prj σ t) (prj σ y) - Hf (prj (ComplexEmbedding.conjugate σ) t) (prj (ComplexEmbedding.conjugate σ) y)) / 2) *
      Complex.I_sq

abbrev conjO [IsCMField E] (α : 𝓞 E) : 𝓞 E := IsCMField.ringOfIntegersComplexConj E α

lemma emb_conjO [IsCMField E] (α : 𝓞 E) (τ : E →+* ℂ) :
    τ ((conjO α : 𝓞 E) : E) = (starRingEnd ℂ) (τ (α : E)) := by
  simp [conjO, NumberField.IsCMField.coe_ringOfIntegersComplexConj,
    NumberField.IsCMField.complexEmbedding_complexConj]

lemma act_apply {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (v : Vsp dim) (i : Idx dim) :
    act α v i = i.1 (α : E) * v i := rfl

def actL {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) : Vsp dim →ₗ[ℂ] Vsp dim where
  toFun := act α
  map_add' v w := by ext i; simp only [act_apply, PiLp.add_apply]; ring
  map_smul' c v := by ext i; simp only [act_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

lemma Hf_act [IsCMField E] {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (x a : Vsp dim) :
    Hf (act α x) a = Hf x (act (conjO α) a) := by
  unfold Hf
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [act, emb_conjO]
  ring

lemma inner_act [IsCMField E] {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (u a : Vsp dim) :
    inner ℝ (act α u) a = inner ℝ u (act (conjO α) a) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [act, emb_conjO, Complex.inner, Complex.mul_re, Complex.mul_im]
  ring

lemma act_mem_IR {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)}
    (hs : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I) (α : 𝓞 E) {a : Vsp dim} (ha : a ∈ IR I) :
    act α a ∈ IR I := by
  have key : Submodule.span ℝ (I : Set (Vsp dim)) ≤ (IR I).comap ((actL α).restrictScalars ℝ) := by
    rw [Submodule.span_le]
    intro x hx
    exact Submodule.subset_span (hs α x hx)
  exact key ha

lemma isU_act [IsCMField E] {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)}
    (hs : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I) (α : 𝓞 E) {x u : Vsp dim} (h : IsU I x u) :
    IsU I (act α x) (act α u) := by
  exact ⟨act_mem_IR hs α h.1, fun a ha => by
    rw [inner_act, h.2 _ (act_mem_IR hs _ ha), Hf_act]⟩

lemma norm_act_le {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (B : ℝ) (hB : ∀ τ : E →+* ℂ, ‖τ (α : E)‖ ≤ B)
    (v : Vsp dim) : ‖act α v‖ ≤ B * ‖v‖ := by
  by_cases hv : v = 0
  · subst hv
    rw [show act α (0 : Vsp dim) = 0 from (actL α).map_zero]
    simp
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (by ext i; simpa using h i)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB i.1)
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_sq hB0, ← Real.sqrt_mul (sq_nonneg B)]
  apply Real.sqrt_le_sqrt
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  simp only [act, PiLp.toLp_apply, norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hB j.1) 2) (sq_nonneg _)

def Xg {dim : (E →+* ℂ) → ℕ} (L I : Submodule ℤ (Vsp dim)) : AddSubgroup (Vsp dim) where
  carrier := {u | ∃ x ∈ L, IsU I x u}
  add_mem' := by
    rintro u v ⟨x, hx, hu⟩ ⟨y, hy, hv⟩; exact ⟨x + y, L.add_mem hx hy, isU_add hu hv⟩
  zero_mem' := ⟨0, L.zero_mem, isU_zero I⟩
  neg_mem' := by rintro u ⟨x, hx, hu⟩; exact ⟨-x, L.neg_mem hx, isU_neg hu⟩

lemma Xg_act [IsCMField E] {dim : (E →+* ℂ) → ℕ} {L I : Submodule ℤ (Vsp dim)}
    (hL : ∀ (α : 𝓞 E) x, x ∈ L → act α x ∈ L) (hs : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I)
    (α : 𝓞 E) {u : Vsp dim} (hu : u ∈ Xg L I) : act α u ∈ Xg L I := by
  obtain ⟨x, hx, h⟩ := hu
  exact ⟨act α x, hL α x hx, isU_act hs α h⟩

lemma Xg_IR {dim : (E →+* ℂ) → ℕ} {L I : Submodule ℤ (Vsp dim)} {u : Vsp dim}
    (hu : u ∈ Xg L I) : u ∈ IR I := by
  obtain ⟨x, -, h⟩ := hu
  exact h.1

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
end

namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

open NumberField.InfinitePlace Classical in
lemma emb_comb [IsCMField E] (σ : E →+* ℂ) (c : ℂ) :
    ∃ r : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℝ, ∀ τ : E →+* ℂ,
      ∑ i, (r i : ℂ) * τ (RingOfIntegers.basis E i : E) =
        if τ = σ then c else if τ = ComplexEmbedding.conjugate σ then (starRingEnd ℂ) c else 0 := by
  classical
  have hne := ne_conj σ
  have hcx : ∀ τ : E →+* ℂ, (mk τ).IsComplex := fun τ => IsTotallyComplex.isComplex _
  let wc : {w : InfinitePlace E // w.IsComplex} := ⟨mk σ, hcx σ⟩
  let c' : ℂ := if (mk σ).embedding = σ then c else (starRingEnd ℂ) c
  let y : mixedEmbedding.mixedSpace E := (0, Pi.single wc c')
  let B := mixedEmbedding.latticeBasis E
  refine ⟨fun i => B.repr y i, fun τ => ?_⟩
  have hsum := B.sum_repr y

  have hcoord : ∑ i, (B.repr y i : ℂ) * (mk τ).embedding (RingOfIntegers.basis E i : E) =
      y.2 ⟨mk τ, hcx τ⟩ := by
    conv_rhs => rw [← hsum]
    rw [Prod.snd_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [B, Prod.smul_snd, Pi.smul_apply, mixedEmbedding.latticeBasis_apply,
      mixedEmbedding.mixedEmbedding_apply_isComplex, integralBasis_apply, Complex.real_smul]
  have hy : y.2 ⟨mk τ, hcx τ⟩ = if mk τ = mk σ then c' else 0 := by
    simp only [y]
    by_cases h : mk τ = mk σ
    · rw [if_pos h]
      have : (⟨mk τ, hcx τ⟩ : {w : InfinitePlace E // w.IsComplex}) = wc := Subtype.ext h
      rw [this, Pi.single_eq_same]
    · rw [if_neg h, Pi.single_eq_of_ne]
      intro h'; exact h (congrArg Subtype.val h')
  have hemb := embedding_mk_eq τ

  have hval : ∑ i, (B.repr y i : ℂ) * τ (RingOfIntegers.basis E i : E) =
      if (mk τ).embedding = τ then (if mk τ = mk σ then c' else 0)
      else (starRingEnd ℂ) (if mk τ = mk σ then c' else 0) := by
    rcases hemb with h | h
    · rw [if_pos h, ← hy, ← hcoord, h]
    · by_cases h' : (mk τ).embedding = τ
      · rw [if_pos h', ← hy, ← hcoord, h']
      · rw [if_neg h', ← hy, ← hcoord, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [h, map_mul, Complex.conj_ofReal, ComplexEmbedding.conjugate_coe_eq]
        simp
  rw [hval]
  by_cases hτ : τ = σ
  · subst hτ
    simp only [if_true, c']
    split_ifs with h1 <;> simp
  · by_cases hτ' : τ = ComplexEmbedding.conjugate σ
    · subst hτ'
      have hm : mk (ComplexEmbedding.conjugate σ) = mk σ := mk_conjugate_eq σ
      simp only [if_neg hτ, if_true, hm, c']
      rcases embedding_mk_eq σ with h | h
      · have : (mk σ).embedding ≠ ComplexEmbedding.conjugate σ := by rw [h]; exact hne.symm
        simp [h, hm, this, hne, hne.symm]
      · simp [h, hm, hne, hne.symm]
    · have hm : mk τ ≠ mk σ := by
        intro h; rcases mk_eq_iff.mp h with h | h
        · exact hτ h
        · exact hτ' (by rw [← h]; exact (ComplexEmbedding.involutive_conjugate (K := E) τ).symm)
      simp [hτ, hτ', hm]


open Classical in
lemma Mc_comb [IsCMField E] {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (c : ℂ) :
    ∃ r : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℝ, ∀ v : Vsp dim,
      Mc σ c v = ∑ i, r i • act (RingOfIntegers.basis E i) v := by
  classical
  obtain ⟨r, hr⟩ := emb_comb σ c
  refine ⟨r, fun v => ?_⟩
  ext j
  rw [Mc_apply, WithLp.ofLp_sum, Finset.sum_apply]
  have := hr j.1
  simp only [PiLp.smul_apply, act_apply, Complex.real_smul]
  rw [show (∑ i, (r i : ℂ) * (j.1 (RingOfIntegers.basis E i : E) * v j)) =
    (∑ i, (r i : ℂ) * j.1 (RingOfIntegers.basis E i : E)) * v j by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring, this]
  split_ifs <;> simp

lemma Mc_mem [IsCMField E] {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (S : Submodule ℝ (Vsp dim))
    (hS : ∀ (α : 𝓞 E) v, v ∈ S → act α v ∈ S) (c : ℂ) {v : Vsp dim} (hv : v ∈ S) :
    Mc σ c v ∈ S := by
  obtain ⟨r, hr⟩ := Mc_comb (dim := dim) σ c
  rw [hr]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hS _ _ hv)

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
end

namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section

namespace ChA

lemma finite_sep {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (S : Set V) (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ ‖x - y‖) (R : ℝ) :
    {x | x ∈ S ∧ ‖x‖ ≤ R}.Finite := by
  classical
  have hcpt : IsCompact (Metric.closedBall (0 : V) R) := isCompact_closedBall 0 R
  obtain ⟨t, htfin, hcov⟩ :=
    (Metric.totallyBounded_iff.mp hcpt.totallyBounded) (1 / 2) (by norm_num)
  have hT : ∀ x ∈ {x | x ∈ S ∧ ‖x‖ ≤ R}, ∃ y ∈ t, dist x y < 1 / 2 := by
    intro x hx
    have hx' : x ∈ Metric.closedBall (0 : V) R := by
      rw [mem_closedBall_zero_iff]; exact hx.2
    have := hcov hx'
    simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at this
    exact this
  choose! f hf hfx using hT
  refine Set.Finite.of_finite_image (f := f) (htfin.subset ?_) ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact hf x hx
  · intro x hx y hy hxy
    by_contra hne
    have hsep := hS x hx.1 y hy.1 hne
    have h1 := hfx x hx
    have h2 := hfx y hy
    rw [hxy] at h1
    have hlt : dist x y < 1 := by
      calc dist x y ≤ dist x (f y) + dist y (f y) := dist_triangle_right _ _ _
        _ < 1 / 2 + 1 / 2 := add_lt_add h1 h2
        _ = 1 := by norm_num
    rw [dist_eq_norm] at hlt
    linarith

lemma sep_of_group {V : Type} [NormedAddCommGroup V] (G : AddSubgroup V)
    (hG : ∀ g ∈ G, g ≠ 0 → 1 ≤ ‖g‖) (S : Set V) (hS : S ⊆ G) :
    ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ ‖x - y‖ := by
  intro x hx y hy hne
  exact hG (x - y) (G.sub_mem (hS hx) (hS hy)) (sub_ne_zero.mpr hne)

lemma exists_closest {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (G : AddSubgroup V) (hG : ∀ g ∈ G, g ≠ 0 → 1 ≤ ‖g‖) (p : V) :
    ∃ w ∈ G, ∀ w' ∈ G, ‖p - w‖ ≤ ‖p - w'‖ := by
  classical
  have hsep := sep_of_group G hG (G : Set V) subset_rfl
  have hfin : {x | x ∈ (G : Set V) ∧ ‖x‖ ≤ 2 * ‖p‖}.Finite := finite_sep _ hsep _
  have hne : ({x | x ∈ (G : Set V) ∧ ‖x‖ ≤ 2 * ‖p‖} : Set V).Nonempty :=
    ⟨0, G.zero_mem, by simp⟩
  obtain ⟨w, hw, hmin⟩ := Set.exists_min_image _ (fun w => ‖p - w‖) hfin hne
  refine ⟨w, hw.1, fun w' hw' => ?_⟩
  by_cases h : ‖w'‖ ≤ 2 * ‖p‖
  · exact hmin w' ⟨hw', h⟩
  · push Not at h
    have h0 := hmin 0 ⟨G.zero_mem, by simp⟩
    simp only [sub_zero] at h0
    have h3 : ‖w'‖ - ‖p‖ ≤ ‖p - w'‖ := by
      rw [norm_sub_rev]; exact norm_sub_norm_le w' p
    linarith

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
end

namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

lemma act_omega_expand {dim : (E →+* ℂ) → ℕ} (ω : Fin (Module.finrank ℚ E) → 𝓞 E)
    (hω : LinearIndependent ℚ (fun j => (ω j : E))) (α : 𝓞 E) (y : Vsp dim) :
    act α y ∈ Submodule.span ℝ (Set.range fun j => act (ω j) y) := by
  classical
  have hsp : Submodule.span ℚ (Set.range fun j => (ω j : E)) = ⊤ :=
    by
      first
      | exact hω.span_eq_top_of_card_eq_finrank' (Fintype.card_fin _)
      | (haveI : Nonempty (Fin (Module.finrank ℚ E)) := ⟨⟨0, Module.finrank_pos⟩⟩
         exact hω.span_eq_top_of_card_eq_finrank (Fintype.card_fin _))
  have hα : (α : E) ∈ Submodule.span ℚ (Set.range fun j => (ω j : E)) := by
    rw [hsp]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ : ∃ c : Fin (Module.finrank ℚ E) → ℚ, ∑ j, c j • (ω j : E) = α := by
    first
    | exact (Submodule.mem_span_range_iff_exists_fun ℚ).1 hα
    | exact Submodule.mem_span_range_iff_exists_fun.1 hα
  have key : act α y = ∑ j, ((c j : ℝ)) • act (ω j) y := by
    ext i
    simp only [act, ← hc]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, Rat.smul_def, map_mul, map_ratCast, Finset.sum_mul, Complex.real_smul, mul_assoc]
  rw [key]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

lemma rank_bound {dim : (E →+* ℂ) → ℕ} (L I : Submodule ℤ (Vsp dim))
    (hsep : ∀ g ∈ Xg L I, g ≠ 0 → 1 ≤ ‖g‖)
    (hact : ∀ (α : 𝓞 E) u, u ∈ Xg L I → act α u ∈ Xg L I)
    (ω : Fin (Module.finrank ℚ E) → 𝓞 E) (hω : LinearIndependent ℚ (fun j => (ω j : E)))
    (σ : E →+* ℂ) (b : Set (Vsp dim)) [Fintype b] (hb : b ⊆ prj σ '' (Xg L I))
    (hli : LinearIndependent ℂ (fun s : b => (s : Vsp dim))) :
    Module.finrank ℚ E * Fintype.card b ≤ Module.finrank ℝ (IR I) := by
  classical
  have hpre : ∀ s : b, ∃ u, u ∈ Xg L I ∧ prj σ u = (s : Vsp dim) := by
    intro s
    obtain ⟨u, hu, h⟩ := hb s.2
    exact ⟨u, hu, h⟩
  choose u hu hus using hpre
  let v : Fin (Module.finrank ℚ E) × b → Vsp dim := fun p => act (ω p.1) (u p.2)
  have hvX : ∀ p, v p ∈ Xg L I := fun p => hact _ _ (hu p.2)
  have hvIR : ∀ p, v p ∈ IR I := by
    intro p
    have h : ∃ x ∈ L, IsU I x (v p) := hvX p
    obtain ⟨x, _, hx⟩ := h
    exact hx.1
  have hprj : ∀ (α : 𝓞 E) (w : Vsp dim), prj σ (act α w) = σ (α : E) • prj σ w := by
    intro α w
    ext i
    by_cases h : i.1 = σ
    · simp [prj, act_apply, h]
    · simp [prj, h]

  have hZ : ∀ m : Fin (Module.finrank ℚ E) × b → ℤ, ∑ p, m p • v p = 0 → ∀ p, m p = 0 := by
    intro m hm
    have h1 : ∑ s : b, (∑ j, ((m (j, s) : ℂ) * σ (ω j : E))) • (s : Vsp dim) = 0 := by
      have := congrArg (prj σ) hm
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_zero] at this
      rw [← this, Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      show _ = prj σ (m (j, s) • act (ω j) (u s))
      rw [map_zsmul, hprj, hus, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
    rintro ⟨j, s⟩
    have h2 := Fintype.linearIndependent_iff.mp hli
      (fun s => ∑ j, ((m (j, s) : ℂ) * σ (ω j : E))) h1 s
    have h3 : σ (∑ j, ((m (j, s) : E)) * (ω j : E)) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]; simpa [map_mul, map_intCast] using h2
    have h4 : ∑ j, ((m (j, s) : ℚ)) • (ω j : E) = 0 := by
      have h5 := (map_eq_zero_iff σ σ.injective).mp h3
      simpa [Rat.smul_def] using h5
    have h6 := Fintype.linearIndependent_iff.mp hω (fun j => (m (j, s) : ℚ)) h4 j
    exact_mod_cast h6

  have hR : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc p
    by_contra hcp
    let y : ℕ → Vsp dim := fun k => -(∑ q, ⌊(k : ℝ) * c q⌋ • v q)
    have hyX : ∀ k, y k ∈ Xg L I := fun k =>
      neg_mem (sum_mem fun q _ => zsmul_mem (hvX q) _)
    have hyeq : ∀ k : ℕ, y k = ∑ q, Int.fract ((k : ℝ) * c q) • v q := by
      intro k
      have h0 : ∑ q, ((k : ℝ) * c q) • v q = 0 := by
        simp_rw [mul_smul]
        rw [← Finset.smul_sum, hc, smul_zero]
      simp only [y, Int.fract, sub_smul, Finset.sum_sub_distrib, h0, zero_sub]
      congr 1
      refine Finset.sum_congr rfl fun q _ => ?_
      exact (Int.cast_smul_eq_zsmul ℝ _ _).symm
    have hyn : ∀ k, ‖y k‖ ≤ ∑ q, ‖v q‖ := by
      intro k
      rw [hyeq]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one _).le
    have hfin : {x | x ∈ (Xg L I : Set (Vsp dim)) ∧ ‖x‖ ≤ ∑ q, ‖v q‖}.Finite :=
      finite_sep _ (sep_of_group (Xg L I) hsep _ subset_rfl) _
    let g : ℕ → (Fin (Module.finrank ℚ E) × b → ℤ) := fun k q => ⌊(k : ℝ) * c q⌋
    let Φ : (Fin (Module.finrank ℚ E) × b → ℤ) → Vsp dim := fun m => -(∑ q, m q • v q)
    have hΦ : Function.Injective Φ := by
      intro m m' h
      have h' : ∑ q, m q • v q = ∑ q, m' q • v q := neg_inj.mp h
      have h'' : ∑ q, (m q - m' q) • v q = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, h', sub_self]
      funext q
      exact sub_eq_zero.mp (hZ _ h'' q)
    have hrg : (Set.range g).Finite := by
      refine Set.Finite.of_finite_image ?_ hΦ.injOn
      refine hfin.subset ?_
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨hyX k, hyn k⟩
    have hrp : (Set.range fun k : ℕ => ⌊(k : ℝ) * c p⌋).Finite :=
      (hrg.image (fun m => m p)).subset (by rintro _ ⟨k, rfl⟩; exact ⟨g k, ⟨k, rfl⟩, rfl⟩)
    obtain ⟨B, hB⟩ := hrp.bddAbove
    obtain ⟨B', hB'⟩ := hrp.bddBelow
    have hcpos : 0 < |c p| := abs_pos.mpr hcp
    obtain ⟨k, hk⟩ := exists_nat_gt ((|(B : ℝ)| + |(B' : ℝ)| + 2) / |c p|)
    have hkc : |(B : ℝ)| + |(B' : ℝ)| + 2 < (k : ℝ) * |c p| := by
      rwa [div_lt_iff₀ hcpos] at hk
    have hup : ⌊(k : ℝ) * c p⌋ ≤ B := hB ⟨k, rfl⟩
    have hlo : B' ≤ ⌊(k : ℝ) * c p⌋ := hB' ⟨k, rfl⟩
    have h1 : (k : ℝ) * c p - 1 < (⌊(k : ℝ) * c p⌋ : ℝ) := Int.sub_one_lt_floor _
    have h2 : (⌊(k : ℝ) * c p⌋ : ℝ) ≤ (k : ℝ) * c p := Int.floor_le _
    have hup' : (⌊(k : ℝ) * c p⌋ : ℝ) ≤ B := by exact_mod_cast hup
    have hlo' : (B' : ℝ) ≤ ⌊(k : ℝ) * c p⌋ := by exact_mod_cast hlo
    have hB0 := abs_nonneg (B : ℝ)
    have hB'0 := abs_nonneg (B' : ℝ)
    rcases lt_or_gt_of_ne hcp with hneg | hpos
    · rw [abs_of_neg hneg, mul_neg] at hkc
      have := neg_abs_le (B' : ℝ)
      linarith
    · rw [abs_of_pos hpos] at hkc
      have := le_abs_self (B : ℝ)
      linarith
  have hw : LinearIndependent ℝ (fun p => (⟨v p, hvIR p⟩ : IR I)) :=
    LinearIndependent.of_comp (IR I).subtype hR
  have := hw.fintype_card_le_finrank
  simpa [Fintype.card_prod, Fintype.card_fin] using this

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
end

namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

def Zs {dim : (E →+* ℂ) → ℕ} (L I : Submodule ℤ (Vsp dim)) (μ : ℝ) : Submodule ℝ (Vsp dim) :=
  Submodule.span ℝ {x | ∃ α : 𝓞 E, ∃ y ∈ Xg L I, ‖y‖ ≤ μ ∧ x = act α y}

lemma Zs_mono {dim : (E →+* ℂ) → ℕ} (L I : Submodule ℤ (Vsp dim)) {μ μ' : ℝ} (h : μ ≤ μ') :
    Zs L I μ ≤ Zs L I μ' := Submodule.span_mono fun _ ⟨α, y, hy, hyμ, hx⟩ => ⟨α, y, hy, hyμ.trans h, hx⟩

lemma Zs_self {dim : (E →+* ℂ) → ℕ} (L I : Submodule ℤ (Vsp dim)) {μ : ℝ} {y : Vsp dim}
    (hy : y ∈ Xg L I) (hμ : ‖y‖ ≤ μ) : y ∈ Zs L I μ := by
  refine Submodule.subset_span ⟨1, y, hy, hμ, ?_⟩
  ext i
  simp [act]

private lemma act_add_lemma {dim : (E →+* ℂ) → ℕ} (β : 𝓞 E) (x y : Vsp dim) :
    act β (x + y) = act β x + act β y := by
  ext i
  first | (simp [act]; done) | (simp [act]; ring)

private lemma act_smul_lemma_2 {dim : (E →+* ℂ) → ℕ} (β : 𝓞 E) (r : ℝ) (x : Vsp dim) :
    act β (r • x) = r • act β x := by
  ext i
  first | (simp [act]; done) | (simp [act]; ring)

private lemma act_zero_lemma_4 {dim : (E →+* ℂ) → ℕ} (β : 𝓞 E) : act β (0 : Vsp dim) = 0 := by
  ext i
  simp [act]

private lemma act_mul_lemma_5 {dim : (E →+* ℂ) → ℕ} (β α : 𝓞 E) (y : Vsp dim) :
    act β (act α y) = act (β * α) y := by
  ext i
  first | (simp [act]; done) | (simp [act]; ring)

private lemma act_span_lemma_3 {dim : (E →+* ℂ) → ℕ} (S : Set (Vsp dim)) (β : 𝓞 E)
    (hS : ∀ y ∈ S, act β y ∈ Submodule.span ℝ S) {a : Vsp dim}
    (ha : a ∈ Submodule.span ℝ S) : act β a ∈ Submodule.span ℝ S := by
  induction ha using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => rw [act_zero_lemma_4]; exact zero_mem _
  | add x y _ _ hx hy => rw [act_add_lemma]; exact add_mem hx hy
  | smul r x _ hx => rw [act_smul_lemma_2]; exact Submodule.smul_mem _ r hx

lemma Zs_act {dim : (E →+* ℂ) → ℕ} (L I : Submodule ℤ (Vsp dim)) (μ : ℝ) (β : 𝓞 E)
    {x : Vsp dim} (hx : x ∈ Zs L I μ) : act β x ∈ Zs L I μ := by
  refine act_span_lemma_3 _ β ?_ hx
  rintro _ ⟨α, y, hy, hyμ, rfl⟩
  exact Submodule.subset_span ⟨β * α, y, hy, hyμ, act_mul_lemma_5 β α y⟩

lemma Zs_IR {dim : (E →+* ℂ) → ℕ} {L I : Submodule ℤ (Vsp dim)}
    (hIs : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I) (μ : ℝ) : Zs L I μ ≤ IR I := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨α, y, hy, -, rfl⟩
  obtain ⟨x, -, hu⟩ : ∃ x ∈ L, IsU I x y := hy
  exact act_span_lemma_3 _ α (fun z hz => Submodule.subset_span (hIs α z hz)) hu.1

lemma prj_rsmul {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (r : ℝ) (x : Vsp dim) :
    prj σ (r • x) = r • prj σ x := by
  simp only [prj]
  exact LinearMap.map_smul_of_tower _ r x

private lemma prj_add_lemma_6 {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (x y : Vsp dim) :
    prj σ (x + y) = prj σ x + prj σ y := by
  simp only [prj]
  exact map_add _ x y

private lemma prj_zero_lemma_7 {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) : prj σ (0 : Vsp dim) = 0 := by
  simp only [prj]
  exact map_zero _

lemma prj_mem_of_span {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (W : Submodule ℂ (Vsp dim))
    (S : Set (Vsp dim)) (hS : ∀ y ∈ S, prj σ y ∈ W) {a : Vsp dim}
    (ha : a ∈ Submodule.span ℝ S) : prj σ a ∈ W := by
  induction ha using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => rw [prj_zero_lemma_7]; exact zero_mem _
  | add x y _ _ hx hy => rw [prj_add_lemma_6]; exact add_mem hx hy
  | smul r x _ hx => rw [prj_rsmul]; exact W.smul_of_tower_mem r hx

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
end

namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

set_option maxHeartbeats 1000000 in
lemma one_char [IsCMField E] (hNP : Ext.NearestPlane) {dim : (E →+* ℂ) → ℕ}
    (L I : Submodule ℤ (Vsp dim))
    (hLs : ∀ (α : 𝓞 E) x, x ∈ L → act α x ∈ L) (hIs : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I)
    (hiso : ∀ x ∈ I, ∀ y ∈ I, (Hf x y).im = 0) (hsep : ∀ g ∈ Xg L I, g ≠ 0 → 1 ≤ ‖g‖)
    (ω : Fin (Module.finrank ℚ E) → 𝓞 E) (hω : LinearIndependent ℚ (fun j => (ω j : E)))
    (B : ℝ) (hωB : ∀ j (τ : E →+* ℂ), ‖τ (ω j : E)‖ ≤ B)
    (D : ℕ) (hD : Module.finrank ℝ (IR I) ≤ D) (σ : E →+* ℂ) (W : Submodule ℂ (Vsp dim))
    (k : ℕ) (χ : ℕ → Vsp dim) (hχX : ∀ j < k, χ j ∈ Xg L I) (hχW : ∀ j < k, prj σ (χ j) ∈ W)
    (hWχ : W ≤ Submodule.span ℂ ((fun i => prj σ (χ i)) '' Set.Iio k))
    (hflag : ∀ j < k, ∃ μ, χ j ∈ Zs L I μ ∧ ∀ y ∈ Xg L I, prj σ y ∉ W → μ ≤ ‖y‖)
    (v : Vsp dim) (hvX : v ∈ Xg L I) (hvW : prj σ v ∉ W)
    (hvmin : ∀ y ∈ Xg L I, prj σ y ∉ W → ‖v‖ ≤ ‖y‖) (T : ℝ) (hT : 0 < T) :
    ∃ t χ' : Vsp dim, (∀ w ∈ W, inner ℂ w (prj σ t) = 0) ∧ ‖prj σ t‖ = T ∧
      ‖t‖ ^ 2 = 2 * T ^ 2 ∧ χ' ∈ Xg L I ∧ χ' ∈ Zs L I ‖v‖ ∧
      ‖χ' - t‖ ^ 2 ≤ D * (B * ‖v‖) ^ 2 / 4 ∧
      ∀ u ∈ Xg L I, |2 * inner ℝ χ' u| ≤ ‖u‖ ^ 2 ∨ ‖v‖ ≤ ‖u‖ := by
  classical

  have hMc1 : ∀ (c : ℂ) (x : Vsp dim), Mc σ 1 (Mc σ c x) = Mc σ c x := by
    intro c x
    ext i
    simp only [Mc, LinearMap.coe_mk, AddHom.coe_mk]
    split_ifs <;> simp
  have hprj1 : ∀ x : Vsp dim, prj σ (Mc σ 1 x) = prj σ x := by
    intro x; rw [prj_Mc, one_smul]
  have hZact : ∀ (α : 𝓞 E) x, x ∈ Zs L I ‖v‖ → act α x ∈ Zs L I ‖v‖ :=
    fun α x hx => Zs_act L I _ α hx
  have hZMc : ∀ (c : ℂ) {x : Vsp dim}, x ∈ Zs L I ‖v‖ → Mc σ c x ∈ Zs L I ‖v‖ :=
    fun c x hx => Mc_mem σ (Zs L I ‖v‖) hZact c hx
  have hvZ : v ∈ Zs L I ‖v‖ := Zs_self L I hvX le_rfl
  have hχZ : ∀ j < k, χ j ∈ Zs L I ‖v‖ := by
    intro j hj
    obtain ⟨μ, hμ, hμle⟩ := hflag j hj
    exact Zs_mono L I (hμle v hvX hvW) hμ
  have hshort : ∀ u ∈ Xg L I, ‖u‖ < ‖v‖ → prj σ u ∈ W := by
    intro u hu huv
    by_contra h
    exact absurd (hvmin u hu h) (not_le.mpr huv)

  obtain ⟨U, hU⟩ : ∃ U : Submodule ℝ (Vsp dim), U = Submodule.span ℝ
      {x | ∃ c : ℂ, ∃ y ∈ Zs L I ‖v‖, prj σ y ∈ W ∧ x = Mc σ c y} := ⟨_, rfl⟩
  have hUgen : ∀ (c : ℂ) y, y ∈ Zs L I ‖v‖ → prj σ y ∈ W → Mc σ c y ∈ U := by
    intro c y hy hyW
    rw [hU]; exact Submodule.subset_span ⟨c, y, hy, hyW, rfl⟩
  have hUZ : U ≤ Zs L I ‖v‖ := by
    rw [hU]
    refine Submodule.span_le.mpr ?_
    rintro x ⟨c, y, hy, -, rfl⟩
    exact hZMc c hy
  have hUprj : ∀ x ∈ U, prj σ x ∈ W := by
    intro x hx
    rw [hU] at hx
    refine prj_mem_of_span σ W _ ?_ hx
    rintro y ⟨c, y', -, hy', rfl⟩
    rw [prj_Mc]; exact W.smul_mem c hy'
  have hUMc : ∀ x ∈ U, Mc σ 1 x ∈ U := by
    intro x hx
    rw [hU] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨c, y', hy', hy'W, rfl⟩ := hy
      rw [hMc1]; exact hUgen c y' hy' hy'W
    | zero => rw [map_zero]; exact U.zero_mem
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact U.add_mem ha hb
    | smul r a _ ha => rw [LinearMap.map_smul_of_tower]; exact U.smul_mem r ha

  haveI : CompleteSpace U := FiniteDimensional.complete ℝ U
  obtain ⟨y₀, hy₀U, z, hzU, hxyz⟩ := U.exists_add_mem_mem_orthogonal (Mc σ 1 v)
  have hz : z = Mc σ 1 v - y₀ := by rw [hxyz]; abel
  have hzZ : z ∈ Zs L I ‖v‖ := by
    rw [hz]; exact Submodule.sub_mem _ (hZMc 1 hvZ) (hUZ hy₀U)
  have hzperp : ∀ u ∈ U, inner ℝ (Mc σ 1 z) u = 0 := by
    intro u hu
    rw [real_inner_Mc, map_one]
    exact Submodule.inner_left_of_mem_orthogonal (hUMc u hu) hzU
  have hprjt₀ : prj σ (Mc σ 1 z) = prj σ v - prj σ y₀ := by
    rw [hprj1, hz, map_sub, hprj1]
  have hp0 : prj σ (Mc σ 1 z) ≠ 0 := by
    intro h0
    apply hvW
    have h' : prj σ v = prj σ y₀ := by rw [← sub_eq_zero, ← hprjt₀, h0]
    rw [h']; exact hUprj y₀ hy₀U
  have hWorth : ∀ w ∈ W, inner ℂ w (prj σ (Mc σ 1 z)) = 0 := by
    have hsub : W ≤ (Submodule.span ℂ {prj σ (Mc σ 1 z)})ᗮ := by
      refine hWχ.trans (Submodule.span_le.mpr ?_)
      rintro _ ⟨j, hj, rfl⟩
      have hj' : j < k := hj
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left]
      have hH := orth_prj hiso σ (Zs_IR hIs _ (hZMc 1 hzZ))
        (fun c => Zs_IR hIs _ (hZMc c (hχZ j hj')))
        (fun c => hzperp _ (hUgen c _ (hχZ j hj') (hχW j hj')))
      have key : inner ℂ (prj σ (χ j)) (prj σ (Mc σ 1 z)) =
          Hf (prj σ (Mc σ 1 z)) (prj σ (χ j)) := by
        simp only [Hf, PiLp.inner_apply, RCLike.inner_apply]
      rw [key]; exact hH
    intro w hw
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp (hsub hw)

  have hpn : 0 < ‖prj σ (Mc σ 1 z)‖ := norm_pos_iff.mpr hp0
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = T / ‖prj σ (Mc σ 1 z)‖ := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact div_pos hT hpn
  obtain ⟨t, ht⟩ : ∃ t : Vsp dim, t = r • Mc σ 1 z := ⟨_, rfl⟩
  have htZ : t ∈ Zs L I ‖v‖ := by rw [ht]; exact Submodule.smul_mem _ r (hZMc 1 hzZ)
  have hprjt : prj σ t = r • prj σ (Mc σ 1 z) := by rw [ht, prj_rsmul]
  have hnT : ‖prj σ t‖ = T := by
    rw [hprjt, norm_smul, Real.norm_of_nonneg hr0.le, hr, div_mul_cancel₀ _ hpn.ne']
  have hWt : ∀ w ∈ W, inner ℂ w (prj σ t) = 0 := by
    intro w hw
    rw [hprjt, ← Complex.coe_smul, inner_smul_right, hWorth w hw, mul_zero]
  have hMt : Mc σ 1 t = t := by rw [ht, LinearMap.map_smul_of_tower, hMc1]
  have htn : ‖t‖ ^ 2 = 2 * T ^ 2 := by
    have h := norm_projection_sq hiso σ t (by rw [hMt]; exact Zs_IR hIs _ htZ)
      (Zs_IR hIs _ (hZMc Complex.I htZ))
    rw [hMt, hnT] at h; exact h
  have htorth : ∀ u ∈ Xg L I, ‖u‖ < ‖v‖ → inner ℝ t u = 0 := by
    intro u hu huv
    rw [ht, real_inner_smul_left, real_inner_Mc, map_one,
      Submodule.inner_left_of_mem_orthogonal
        (hUgen 1 u (Zs_self L I hu huv.le) (hshort u hu huv)) hzU, mul_zero]

  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : AddSubgroup (Vsp dim), Λ = Xg L I ⊓ (Zs L I ‖v‖).toAddSubgroup :=
    ⟨_, rfl⟩
  have hΛ : ∀ g, g ∈ Λ ↔ g ∈ Xg L I ∧ g ∈ Zs L I ‖v‖ := by
    intro g; rw [hΛdef, AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup]
  obtain ⟨χ', hχ'Λ, hclose⟩ :=
    exists_closest Λ (fun g hg hg0 => hsep g ((hΛ g).1 hg).1 hg0) t

  obtain ⟨S', hS'⟩ : ∃ S' : Set (Vsp dim),
      S' = {x | ∃ j, ∃ y ∈ Xg L I, ‖y‖ ≤ ‖v‖ ∧ x = act (ω j) y} := ⟨_, rfl⟩
  have hS'Λ : ∀ x ∈ S', x ∈ Λ := by
    intro x hx
    rw [hS'] at hx
    obtain ⟨j, y, hy, hyv, rfl⟩ := hx
    exact (hΛ _).2 ⟨Xg_act hLs hIs (ω j) hy, Zs_act L I _ (ω j) (Zs_self L I hy hyv)⟩
  have hS'norm : ∀ x ∈ S', ‖x‖ ≤ B * ‖v‖ := by
    intro x hx
    rw [hS'] at hx
    obtain ⟨j, y, hy, hyv, rfl⟩ := hx
    have hB : 0 ≤ B := (norm_nonneg _).trans (hωB j σ)
    exact (norm_act_le (ω j) B (hωB j) y).trans (mul_le_mul_of_nonneg_left hyv hB)
  have hZS' : Zs L I ‖v‖ ≤ Submodule.span ℝ S' := by
    unfold Zs
    refine Submodule.span_le.mpr ?_
    rintro x ⟨α, y, hy, hyv, rfl⟩
    refine Submodule.span_mono ?_ (act_omega_expand ω hω α y)
    rintro _ ⟨j, rfl⟩
    rw [hS']
    exact ⟨j, y, hy, hyv, rfl⟩
  obtain ⟨b, hbS', hbspan, hbli⟩ := exists_linearIndependent ℝ S'
  have hli : LinearIndependent ℝ (fun x : b => (x : Vsp dim)) := hbli
  haveI : Finite b := hli.finite
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin b
  obtain ⟨vv, hvvdef⟩ : ∃ vv : Fin n → Vsp dim, vv = fun i => ((e.symm i : b) : Vsp dim) :=
    ⟨_, rfl⟩
  have hvv : LinearIndependent ℝ vv := by
    rw [hvvdef]; exact hli.comp e.symm e.symm.injective
  have hvvS' : ∀ i, vv i ∈ S' := fun i => by rw [hvvdef]; exact hbS' (e.symm i).2
  have hrange : Set.range vv = b := by
    ext x; constructor
    · rintro ⟨i, rfl⟩; rw [hvvdef]; exact (e.symm i).2
    · intro hx; exact ⟨e ⟨x, hx⟩, by rw [hvvdef]; simp⟩
  have htspan : t ∈ Submodule.span ℝ (Set.range vv) := by
    rw [hrange, hbspan]; exact hZS' htZ
  obtain ⟨c, hc⟩ := hNP (Vsp dim) n vv hvv t htspan
  have hnD : (n : ℝ) ≤ D := by
    have h1 : Module.finrank ℝ (Submodule.span ℝ (Set.range vv)) = n := by
      rw [finrank_span_eq_card hvv, Fintype.card_fin]
    have h2 : Submodule.span ℝ (Set.range vv) ≤ IR I := by
      rw [hrange, hbspan]
      exact Submodule.span_le.mpr fun x hx => Zs_IR hIs _ ((hΛ x).1 (hS'Λ x hx)).2
    have h3 : n ≤ D := by rw [← h1]; exact (Submodule.finrank_mono h2).trans hD
    exact_mod_cast h3
  have hgΛ : (∑ i, (c i : ℝ) • vv i) ∈ Λ := by
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    rw [Int.cast_smul_eq_zsmul]
    exact AddSubgroup.zsmul_mem _ (hS'Λ _ (hvvS' i)) _
  have hsum : ∑ i, ‖vv i‖ ^ 2 ≤ n * (B * ‖v‖) ^ 2 := by
    calc ∑ i, ‖vv i‖ ^ 2 ≤ ∑ _i : Fin n, (B * ‖v‖) ^ 2 :=
          Finset.sum_le_sum fun i _ => by gcongr; exact hS'norm _ (hvvS' i)
      _ = n * (B * ‖v‖) ^ 2 := by simp
  have hbound : ‖χ' - t‖ ^ 2 ≤ D * (B * ‖v‖) ^ 2 / 4 := by
    have h1 : ‖t - χ'‖ ≤ ‖t - ∑ i, (c i : ℝ) • vv i‖ := hclose _ hgΛ
    have h2 : ‖t - χ'‖ ^ 2 ≤ ‖t - ∑ i, (c i : ℝ) • vv i‖ ^ 2 := by gcongr
    have h3 : (n : ℝ) * (B * ‖v‖) ^ 2 ≤ D * (B * ‖v‖) ^ 2 :=
      mul_le_mul_of_nonneg_right hnD (sq_nonneg _)
    rw [norm_sub_rev]
    linarith

  have hlast : ∀ u ∈ Xg L I, |2 * inner ℝ χ' u| ≤ ‖u‖ ^ 2 ∨ ‖v‖ ≤ ‖u‖ := by
    intro u hu
    by_cases huv : ‖v‖ ≤ ‖u‖
    · exact Or.inr huv
    left
    push_neg at huv
    have huΛ : u ∈ Λ := (hΛ u).2 ⟨hu, Zs_self L I hu huv.le⟩
    have h1 := hclose (χ' + u) (Λ.add_mem hχ'Λ huΛ)
    have h2 := hclose (χ' - u) (Λ.sub_mem hχ'Λ huΛ)
    have e1 : t - (χ' + u) = (t - χ') - u := by abel
    have e2 : t - (χ' - u) = (t - χ') + u := by abel
    rw [e1] at h1
    rw [e2] at h2
    have s1 : ‖t - χ'‖ ^ 2 ≤ ‖(t - χ') - u‖ ^ 2 := by gcongr
    have s2 : ‖t - χ'‖ ^ 2 ≤ ‖(t - χ') + u‖ ^ 2 := by gcongr
    rw [norm_sub_sq_real (t - χ') u] at s1
    rw [norm_add_sq_real (t - χ') u] at s2
    have hi : inner ℝ (t - χ') u = - inner ℝ χ' u := by
      rw [inner_sub_left, htorth u hu huv, zero_sub]
    rw [hi] at s1 s2
    rw [abs_le]; constructor <;> linarith
  exact ⟨t, χ', hWt, hnT, htn, ((hΛ χ').1 hχ'Λ).1, ((hΛ χ').1 hχ'Λ).2, hbound, hlast⟩

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
