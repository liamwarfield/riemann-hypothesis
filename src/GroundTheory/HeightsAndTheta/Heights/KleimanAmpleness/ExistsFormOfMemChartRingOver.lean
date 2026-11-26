module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PBundlePair
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsSumEqOneOfMulEqOne

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsFormOfMemChartRingOver
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

section Forms

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [Fintype K] in
theorem RowSub.isMultiHomog_mul {f g : MRingOver S ι} {a b : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a)
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g b) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]


omit [Fintype K] in
theorem RowSub.isMultiHomog_C (r : S) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (C r : MRingOver S ι) 0 := by
  classical
  intro m hm k
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hm
  split_ifs at hm with h
  · subst h; simp
  · exact absurd rfl hm


omit [Fintype K] in
theorem RowSub.isMultiHomog_X [DecidableEq K] (k : K) (i : ι k) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (X ⟨k, i⟩ : MRingOver S ι) (Pi.single k 1) := by
  classical
  intro m hm k'
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_X'] at hm
  split_ifs at hm with h
  · subst h
    by_cases hk : k' = k
    · subst hk
      simp [Finsupp.single_apply]
    · have : ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ := fun j e => hk (congrArg Sigma.fst e).symm
      simp [hk]
  · exact absurd rfl hm


omit [Fintype K] in
theorem RowSub.isMultiHomog_pow {f : MRingOver S ι} {a : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) (n : ℕ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f ^ n) (n • a) := by
  induction n with
  | zero => simpa using RowSub.isMultiHomog_C (ι := ι) (1 : S)
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact RowSub.isMultiHomog_mul ih hf


omit [Fintype K] in
theorem RowSub.isMultiHomog_prod {β : Type} (s : Finset β) (f : β → MRingOver S ι) (a : β → K → ℕ)
    (h : ∀ b ∈ s, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f b) (a b)) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (∏ b ∈ s, f b) (∑ b ∈ s, a b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using RowSub.isMultiHomog_C (ι := ι) (1 : S)
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.sum_insert hb]
    exact RowSub.isMultiHomog_mul (h b (Finset.mem_insert_self b s))
      (ih fun b' hb' => h b' (Finset.mem_insert_of_mem hb'))

theorem RowSub.isMultiHomog_coordProd (c : ∀ k, ι k) (d : K → ℕ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRingOver S ι) ^ d k) d := by
  classical
  have h := RowSub.isMultiHomog_prod (S := S) (ι := ι) Finset.univ (fun k => (X ⟨k, c k⟩ : MRingOver S ι) ^ d k)
    (fun k => d k • Pi.single k 1) fun k _ => RowSub.isMultiHomog_pow (RowSub.isMultiHomog_X k (c k)) _
  have e : (∑ k, d k • (Pi.single k 1 : K → ℕ)) = d := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  rwa [e] at h

variable {Ω : Type} [Field Ω] [Algebra S Ω]

theorem RowSub.exists_form_of_mem_chartRingOver (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {z : Ω} (hz : z ∈ ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.chartRingOver S y c) :
    ∃ (m : K → ℕ) (h : MRingOver S ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog h m ∧ z = aeval y h / ∏ k, y ⟨k, c k⟩ ^ m k := by
  classical
  have hP : ∀ m : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ m k) ≠ 0 := fun m =>
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have hPadd : ∀ m m' : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ (m + m') k) =
      (∏ k, y ⟨k, c k⟩ ^ m k) * ∏ k, y ⟨k, c k⟩ ^ m' k := fun m m' => by
    simp [pow_add, Finset.prod_mul_distrib]
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    refine ⟨Pi.single p.1 1, X p, RowSub.isMultiHomog_X p.1 p.2, ?_⟩
    rw [aeval_X]
    rw [Finset.prod_eq_single p.1 (fun k _ hk => by simp [hk]) (by simp)]
    simp
  | algebraMap r =>
    exact ⟨0, C r, RowSub.isMultiHomog_C r, by simp⟩
  | add x x' _ _ ih ih' =>
    obtain ⟨m, h, hh, rfl⟩ := ih
    obtain ⟨m', h', hh', rfl⟩ := ih'
    refine ⟨m + m', h * ∏ k, (X ⟨k, c k⟩ : MRingOver S ι) ^ m' k + h' * ∏ k, (X ⟨k, c k⟩ : MRingOver S ι) ^ m k,
      ?_, ?_⟩
    · have h1 := RowSub.isMultiHomog_mul hh (RowSub.isMultiHomog_coordProd (S := S) c m')
      have h2 := RowSub.isMultiHomog_mul hh' (RowSub.isMultiHomog_coordProd (S := S) c m)
      rw [add_comm m' m] at h2
      intro d hd k
      rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with hd | hd
      · exact h1 d hd k
      · exact h2 d hd k
    · rw [hPadd, div_add_div _ _ (hP m) (hP m')]
      simp only [map_add (f := _), map_mul, map_prod, map_pow, aeval_X]
      ring
  | mul x x' _ _ ih ih' =>
    obtain ⟨m, h, hh, rfl⟩ := ih
    obtain ⟨m', h', hh', rfl⟩ := ih'
    exact ⟨m + m', h * h', RowSub.isMultiHomog_mul hh hh', by rw [hPadd, map_mul, div_mul_div_comm]⟩

end Forms

theorem RowSub.proof : RowSub.Statement := by
  intro S _ K _ _ ι _ _ Ω _ _ y k₀ N e γ J I hne hI t ht
  obtain ⟨n, hn⟩ := ht
  choose c hc using hne
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => hI k (c k) (hc k)
  set δ : K → ℤ := γ + ((n * J.1.card : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ with hδ
  have h1 := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hn c) hyc
  rw [Submodule.mem_comap, LinearMap.mulRight_apply, Subalgebra.mem_toSubmodule] at h1
  obtain ⟨m, h, hh, heq⟩ := RowSub.exists_form_of_mem_chartRingOver y c hyc h1

  set p : K → ℕ := fun k => (-δ k).toNat with hp
  set q : K → ℕ := fun k => (δ k + p k).toNat with hq
  have hpk : ∀ k, -δ k ≤ (p k : ℤ) := fun k => Int.self_le_toNat _
  have hqk : ∀ k, (q k : ℤ) = δ k + p k := fun k => Int.toNat_of_nonneg (by have := hpk k; omega)

  set T : MRingOver S ι := (∏ j ∈ J.1, (X ⟨k₀, e.symm j⟩ : MRingOver S ι)) ^ n *
    ∏ k, (X ⟨k, c k⟩ : MRingOver S ι) ^ (m k + p k) with hT
  set G : MRingOver S ι := h * ∏ k, (X ⟨k, c k⟩ : MRingOver S ι) ^ q k with hG
  set a : K → ℕ := n • (∑ j ∈ J.1, (Pi.single k₀ 1 : K → ℕ)) + (m + p) with ha
  have hTa : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog T a := by
    refine RowSub.isMultiHomog_mul (RowSub.isMultiHomog_pow (RowSub.isMultiHomog_prod _ _ _ fun j _ =>
      RowSub.isMultiHomog_X k₀ (e.symm j)) n) ?_
    exact RowSub.isMultiHomog_coordProd c (m + p)
  have hak : ∀ k, γ k + (a k : ℤ) = δ k + p k + m k := by
    intro k
    simp only [ha, hδ, Pi.add_apply, Pi.smul_apply, Finset.sum_const, smul_eq_mul,
      IndefiniteRowSideFullHecke.Kleiman2.baseDeg]
    by_cases hk : k = k₀
    · subst hk; simp; ring
    · simp [hk]; ring
  have hGa : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog G (fun k => (γ k + a k).toNat) := by
    have e' : (fun k => (γ k + (a k : ℤ)).toNat) = m + q := by
      funext k
      rw [hak k, Pi.add_apply]
      have := hqk k
      have := hpk k
      omega
    rw [e']
    exact RowSub.isMultiHomog_mul hh (RowSub.isMultiHomog_coordProd c q)
  have hXmem : ∀ k (i : ι k), i ∈ baseCell k₀ e J.1 I k →
      (X ⟨k, i⟩ : MRingOver S ι) ∈ ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.cellMon S (baseCell k₀ e J.1 I) :=
    fun k i hi => Submonoid.subset_closure ⟨k, i, hi, rfl⟩
  have hTmem : T ∈ ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.cellMon S (baseCell k₀ e J.1 I) := by
    refine mul_mem (pow_mem (prod_mem fun j hj => hXmem k₀ (e.symm j) ?_) n)
      (prod_mem fun k _ => pow_mem (hXmem k (c k) ?_) _)
    · unfold baseCell
      rw [Function.update_self]
      exact Finset.mem_union_right _ (Finset.mem_map_of_mem _ hj)
    · unfold baseCell
      by_cases hk : k = k₀
      · subst hk; rw [Function.update_self]; exact Finset.mem_union_left _ (hc k)
      · rw [Function.update_of_ne hk]; exact hc k
  have hmeet : CellMeets y (baseCell k₀ e J.1 I) := by
    intro k i hi
    unfold baseCell at hi
    by_cases hk : k = k₀
    · subst hk
      rw [Function.update_self, Finset.mem_union] at hi
      rcases hi with hi | hi
      · exact hI k i hi
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
        exact (Kleiman.mem_support _).mp (J.2.2 hj)
    · rw [Function.update_of_ne hk] at hi; exact hI k i hi

  have hx : Kleiman.xProd J ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j hj => (Kleiman.mem_support _).mp (J.2.2 hj)
  have hPm : (∏ k, y ⟨k, c k⟩ ^ m k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hyc k)
  have hPp : (∏ k, y ⟨k, c k⟩ ^ (m k + p k)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hyc k)
  have hTv : aeval y T = Kleiman.xProd J ^ n * ∏ k, y ⟨k, c k⟩ ^ (m k + p k) := by
    simp only [hT, map_mul, map_prod, map_pow, aeval_X]
    rfl
  have hGv : aeval y G = aeval y h * ∏ k, y ⟨k, c k⟩ ^ q k := by
    simp only [hG, map_mul, map_prod, map_pow, aeval_X]
  have hH : aeval y h = Kleiman.xProd J ^ n * t * (∏ k, y ⟨k, c k⟩ ^ (-δ k)) * ∏ k, y ⟨k, c k⟩ ^ m k := by
    rw [eq_div_iff hPm] at heq
    exact heq.symm
  have e1 : (∏ k, y ⟨k, c k⟩ ^ (m k + p k)) = (∏ k, y ⟨k, c k⟩ ^ m k) * ∏ k, y ⟨k, c k⟩ ^ p k := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => pow_add _ _ _
  have e2 : (∏ k, y ⟨k, c k⟩ ^ (-δ k)) * ∏ k, y ⟨k, c k⟩ ^ q k = ∏ k, y ⟨k, c k⟩ ^ p k := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hyc k), hqk k]
    congr 1
    ring
  have hval : t = aeval y G / aeval y T := by
    rw [hTv, hGv, eq_div_iff (mul_ne_zero (pow_ne_zero _ hx) hPp), hH, e1]
    linear_combination (-(Kleiman.xProd J ^ n * t * ∏ k, y ⟨k, c k⟩ ^ m k)) * e2
  show t ∈ cellSec S y γ (baseCell k₀ e J.1 I)
  unfold cellSec
  rw [if_pos hmeet]
  exact Submodule.subset_span ⟨G, T, a, hTmem, hTa, fun k => by rw [hak k]; have := hpk k; have := hqk k; omega,
    hGa, hval⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsFormDivOfMemChartRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver chartRingOver)

noncomputable section

theorem exists_form_div_of_mem_chartRing {k : Type} [Field k] {N : ℕ} {Ω : Type} [Field Ω] [Algebra k Ω]
    {x : Fin (N + 1) → Ω} {i : Fin (N + 1)} (hi : x i ≠ 0) {a : Ω}
    (ha : a ∈ Kleiman.chartRing k x (Kleiman.singleChart hi)) :
    ∃ (e : ℕ) (f : Kleiman.Poly k N), f.IsHomogeneous e ∧ a = aeval x f / x i ^ e := by
  obtain ⟨f, t, e, ht, hf, hte, rfl⟩ := ha
  have ht' : t ∈ Submonoid.closure {(X i : Kleiman.Poly k N)} := by
    have : ((fun l => (X l : Kleiman.Poly k N)) '' ((({i} : Finset (Fin (N + 1))) : Set (Fin (N + 1))))) =
        {X i} := by simp
    rw [← this]; exact ht
  obtain ⟨p, rfl⟩ := Submonoid.mem_closure_singleton.mp ht'
  have hpe : e = p := hte.inj_right (isHomogeneous_X_pow i p) (by
    rw [X_pow_eq_monomial, Ne, monomial_eq_zero]; exact one_ne_zero)
  subst hpe
  exact ⟨e, f, hf, by rw [map_pow, aeval_X]⟩

theorem exists_common_form_div {k : Type} [Field k] {N : ℕ} {Ω : Type} [Field Ω] [Algebra k Ω]
    {x : Fin (N + 1) → Ω} {ι : Type} [Fintype ι] {i : Fin (N + 1)} (hi : x i ≠ 0) (a : ι → Ω)
    (ha : ∀ t, a t ∈ Kleiman.chartRing k x (Kleiman.singleChart hi)) :
    ∃ (D : ℕ) (E : ι → Kleiman.Poly k N), (∀ t, (E t).IsHomogeneous D) ∧
      ∀ t, a t = aeval x (E t) / x i ^ D := by
  classical
  choose e f hf hfa using fun t => exists_form_div_of_mem_chartRing hi (ha t)
  have hle : ∀ t, e t ≤ ∑ t, e t := fun t =>
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
  refine ⟨∑ t, e t, fun t => f t * X i ^ (∑ t, e t - e t), fun t => ?_, fun t => ?_⟩
  · have h := (hf t).mul (isHomogeneous_X_pow i (∑ t, e t - e t))
    rwa [Nat.add_sub_cancel' (hle t)] at h
  · have hD : x i ^ (∑ t, e t) = x i ^ e t * x i ^ (∑ t, e t - e t) := by
      rw [← pow_add, Nat.add_sub_cancel' (hle t)]
    rw [hfa t, map_mul, map_pow, aeval_X, hD, mul_div_mul_right _ _ (pow_ne_zero _ hi)]

theorem mConeMapOver_rename_base {k : Type} [Field k] {N : ℕ} {Ω : Type} [Field Ω] [Algebra k Ω]
    (x : Fin (N + 1) → Ω) {m : ℕ} (s : Fin m → Ω) {F : Kleiman.Poly k N} {D : ℕ} (hF : F.IsHomogeneous D) :
    mConeMapOver k (graphVec x s) (rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) F) =
      C (aeval x F) * X baseBlock ^ D := by
  have h := congrArg (fun φ => φ F) (mConeMapOver_graph_comp_base (S := k) x s)
  simp only [AlgHom.comp_apply] at h
  rw [h, Kleiman.cone_eq, Kleiman.coneGen_of_isHomogeneous x hF]
  simp only [AlgHom.restrictScalars_apply, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
    MvPolynomial.algebraMap_eq]

theorem mConeMapOver_X' {k : Type} [Field k] {N : ℕ} {Ω : Type} [Field Ω] [Algebra k Ω] {m : ℕ}
    (y : (Σ c, graphIdx N m c) → Ω) (v : Σ c, graphIdx N m c) :
    mConeMapOver k y (X v) = C (y v) * X v.1 := by
  simp [mConeMapOver]

theorem SectionRatio.full : SectionRatio.Statement := by
  intro k _ N Ω _ _ x Q n m s hx hgen W hW hle j b hYj
  have hmem : ∀ P, mConeMapOver k (graphVec x s) P = 0 → P ∈ W := fun P hP => hle (RingHom.mem_ker.mpr hP)
  obtain ⟨i, hXi⟩ : ∃ i : Fin (N + 1), (X ⟨baseBlock, i⟩ : NumbersDVR.MRing (graphIdx N m) k) ∉ W :=
    hW.relevant baseBlock
  have hi : x i ≠ 0 := fun h0 => hXi (hmem _ (by
    rw [mConeMapOver_X', show graphVec x s ⟨baseBlock, i⟩ = 0 from h0, map_zero, zero_mul]))
  obtain ⟨w, hw, hsum⟩ := exists_graph_inverse Q n s hgen hi
  have hw' : ∀ p : Fin m × Fin m,
      x i ^ (-n) * s p.1 * w p.2 ∈ Kleiman.chartRing k x (Kleiman.singleChart hi) := fun p => by
    rw [← chartRingOver_oneBlock x (fun _ => i) hi]; exact hw p.1 p.2
  obtain ⟨D, E, hE, hEq⟩ := exists_common_form_div hi _ hw'
  have hval : ∀ a c, aeval x (E (a, c)) = x i ^ D * (x i ^ (-n) * s a * w c) := fun a c => by
    have h := hEq (a, c)
    dsimp only at h
    rw [h]; field_simp
  obtain ⟨b0, hb0⟩ : ∃ b0, rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (E (j, b0)) ∉ W := by
    by_contra h
    push Not at h
    have key : ∑ c, aeval x (E (j, c)) * s c = x i ^ D * s j := by
      simp only [hval]
      calc ∑ c, x i ^ D * (x i ^ (-n) * s j * w c) * s c
          = x i ^ D * s j * ∑ c, x i ^ (-n) * s c * w c := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
        _ = x i ^ D * s j := by rw [hsum, mul_one]
    have hrel : ∑ c, rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (E (j, c)) *
          X ⟨Sum.inr (), c⟩ -
        rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (X i ^ D) *
          X ⟨Sum.inr (), j⟩ ∈ W := by
      apply hmem
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, map_mul, mConeMapOver_rename_base x s (isHomogeneous_X_pow i D), mConeMapOver_X']
      have hc : ∀ c, mConeMapOver k (graphVec x s)
          (rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (E (j, c)) *
            X ⟨Sum.inr (), c⟩) = C (aeval x (E (j, c)) * s c) * (X baseBlock ^ D * X (Sum.inr ())) := fun c => by
        rw [map_mul, mConeMapOver_rename_base x s (hE _), mConeMapOver_X', graphVec_inr, map_mul]
        ring
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_congr rfl fun c _ => hc c, ← Finset.sum_mul, ← map_sum, key, graphVec_inr]
      simp only [map_pow, aeval_X, map_mul]
      ring
    have hsumW : ∑ c, rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (E (j, c)) *
        X ⟨Sum.inr (), c⟩ ∈ W := W.sum_mem fun c _ => W.mul_mem_right _ (h c)
    have hXY := W.sub_mem hsumW hrel
    rw [sub_sub_cancel, map_pow, rename_X] at hXY
    rcases hW.isPrime.mem_or_mem hXY with h1 | h1
    · exact hXi (hW.isPrime.mem_of_pow_mem _ h1)
    · exact hYj h1
  refine ⟨D, E (b, b0), E (j, b0), hE _, hE _, hb0, hmem _ ?_⟩
  rw [map_sub, map_mul, map_mul, mConeMapOver_rename_base x s (hE _), mConeMapOver_rename_base x s (hE _),
    mConeMapOver_X', mConeMapOver_X', graphVec_inr, graphVec_inr, hval, hval]
  dsimp only
  simp only [map_mul]
  ring

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SgnSingleton
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

namespace CechContract

section Comb

variable {n : ℕ} {M : Type*} [AddCommGroup M]

theorem sgn_insert {J : Finset (Fin n)} {a : Fin n} (ha : a ∉ J) (j : Fin n) :
    Kleiman.Cech.sgn (insert a J) j = if a < j then -Kleiman.Cech.sgn J j else Kleiman.Cech.sgn J j := by
  unfold Kleiman.Cech.sgn
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp [ha]), pow_succ]; ring
  · rfl

theorem sgn_mul_self (J : Finset (Fin n)) (j : Fin n) : Kleiman.Cech.sgn J j * Kleiman.Cech.sgn J j = 1 := by
  unfold Kleiman.Cech.sgn
  rw [← mul_pow]; norm_num

theorem sgn_singleton (j : Fin n) : Kleiman.Cech.sgn {j} j = 1 := by
  rw [Kleiman.Cech.sgn, Finset.filter_singleton, if_neg (lt_irrefl j)]; simp

def cD (f : Finset (Fin n) → M) (J : Finset (Fin n)) : M :=
  ∑ j ∈ J, Kleiman.Cech.sgn J j • f (J.erase j)

def cH (j₀ : Fin n) (f : Finset (Fin n) → M) (J : Finset (Fin n)) : M :=
  if j₀ ∈ J then 0 else Kleiman.Cech.sgn (insert j₀ J) j₀ • f (insert j₀ J)

theorem cD_cH_add (j₀ : Fin n) (f : Finset (Fin n) → M) (J : Finset (Fin n)) :
    cD (cH j₀ f) J + cH j₀ (cD f) J = f J := by
  by_cases h₀ : j₀ ∈ J
  · have hH : cH j₀ (cD f) J = 0 := if_pos h₀
    have hrest : ∑ j ∈ J.erase j₀, Kleiman.Cech.sgn J j • cH j₀ f (J.erase j) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      obtain ⟨hj, -⟩ := Finset.mem_erase.mp hj
      rw [cH, if_pos (Finset.mem_erase.mpr ⟨Ne.symm hj, h₀⟩), smul_zero]
    rw [hH, add_zero, cD, ← Finset.add_sum_erase J _ h₀, hrest, add_zero, cH,
      if_neg (Finset.notMem_erase j₀ J), Finset.insert_erase h₀, smul_smul, sgn_mul_self, one_smul]
  · have hsum : ∑ j ∈ J, Kleiman.Cech.sgn J j • cH j₀ f (J.erase j) +
        ∑ j ∈ J, Kleiman.Cech.sgn (insert j₀ J) j₀ • Kleiman.Cech.sgn (insert j₀ J) j •
          f ((insert j₀ J).erase j) = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj₀ : j ≠ j₀ := fun h => h₀ (h ▸ hj)
      have hn : j₀ ∉ J.erase j := fun h => h₀ (Finset.mem_of_mem_erase h)
      have e : insert j₀ (J.erase j) = (insert j₀ J).erase j := (Finset.erase_insert_of_ne (Ne.symm hj₀)).symm
      have s1 : Kleiman.Cech.sgn ((insert j₀ J).erase j) j₀ = Kleiman.Cech.sgn (J.erase j) j₀ := by
        rw [← e, sgn_insert hn, if_neg (lt_irrefl _)]
      have s2 : Kleiman.Cech.sgn (insert j₀ J) j₀ = Kleiman.Cech.sgn J j₀ := by
        rw [sgn_insert h₀, if_neg (lt_irrefl _)]
      have s3 := sgn_insert h₀ j
      have s4 : Kleiman.Cech.sgn J j₀ =
          if j < j₀ then -Kleiman.Cech.sgn (J.erase j) j₀ else Kleiman.Cech.sgn (J.erase j) j₀ := by
        conv_lhs => rw [← Finset.insert_erase hj]
        exact sgn_insert (Finset.notMem_erase j J) j₀
      have hc : Kleiman.Cech.sgn J j * Kleiman.Cech.sgn ((insert j₀ J).erase j) j₀ +
          Kleiman.Cech.sgn (insert j₀ J) j₀ * Kleiman.Cech.sgn (insert j₀ J) j = 0 := by
        rw [s1, s2, s3, s4]
        rcases lt_or_gt_of_ne hj₀ with h | h
        · rw [if_neg (lt_asymm h), if_pos h]; ring
        · rw [if_pos h, if_neg (lt_asymm h)]; ring
      rw [cH, if_neg hn, e, smul_smul, smul_smul, ← add_smul, hc, zero_smul]
    have hH : cH j₀ (cD f) J = Kleiman.Cech.sgn (insert j₀ J) j₀ • cD f (insert j₀ J) := if_neg h₀
    rw [hH]
    unfold cD
    rw [Finset.sum_insert h₀, Finset.erase_insert h₀, smul_add, smul_smul, sgn_mul_self, one_smul,
      Finset.smul_sum, add_left_comm, hsum, add_zero]

end Comb

section CechSide

variable (S : Type) [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}


open Classical in
noncomputable def extZ {p : ℕ} (s : Kleiman.Cech.Cochain (fun _ : Kleiman.Chart x => Ω) p)
    (K : Finset (Fin (N + 1))) : Ω :=
  if h : K.Nonempty ∧ K ⊆ Kleiman.support x ∧ K.card = p + 1 then s ⟨⟨K, h.1, h.2.1⟩, h.2.2⟩ else 0

theorem extZ_idx {p : ℕ} (s : Kleiman.Cech.Cochain (fun _ : Kleiman.Chart x => Ω) p)
    (I : Kleiman.Cech.Idx (Kleiman.support x) p) : extZ s I.1.1 = s I := by
  rw [extZ, dite_eq_left ⟨I.1.2.1, I.1.2.2, I.2⟩]

theorem d_eq {p : ℕ} (t : Kleiman.Cech.Cochain (fun _ : Kleiman.Chart x => Ω) p) (g : Finset (Fin (N + 1)) → Ω)
    (hg : ∀ I, t I = g I.1.1) (J : Kleiman.Cech.Idx (Kleiman.support x) (p + 1)) :
    Kleiman.Cech.d (fun _ : Kleiman.Chart x => Ω) (omegaRes S x) p t J = cD g J.1.1 := by
  rw [Kleiman.Cech.d_apply, cD,
    ← Finset.sum_coe_sort J.1.1 (fun j => Kleiman.Cech.sgn J.1.1 j • g (J.1.1.erase j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  show _ • t (Kleiman.Cech.face J j) = _ • g (Kleiman.Cech.face J j).1.1
  rw [hg]

def insIdx {j₀ : Fin (N + 1)} (hj₀ : j₀ ∈ Kleiman.support x) {p : ℕ} (I : Kleiman.Cech.Idx (Kleiman.support x) p)
    (h : j₀ ∉ I.1.1) : Kleiman.Cech.Idx (Kleiman.support x) (p + 1) :=
  ⟨⟨insert j₀ I.1.1, Finset.insert_nonempty _ _, Finset.insert_subset hj₀ I.1.2.2⟩, by
    rw [Finset.card_insert_of_notMem h, I.2]⟩

theorem cH_cD_extZ {j₀ : Fin (N + 1)} (hj₀ : j₀ ∈ Kleiman.support x) {p : ℕ}
    (s : Kleiman.Cech.Cochain (fun _ : Kleiman.Chart x => Ω) p)
    (hds : Kleiman.Cech.d (fun _ : Kleiman.Chart x => Ω) (omegaRes S x) p s = 0)
    (I : Kleiman.Cech.Idx (Kleiman.support x) p) : cH j₀ (cD (extZ s)) I.1.1 = 0 := by
  unfold cH
  split_ifs with h
  · rfl
  · have h1 := d_eq S s (extZ s) (fun I => (extZ_idx s I).symm) (insIdx hj₀ I h)
    rw [hds] at h1
    change _ • cD (extZ s) (insIdx hj₀ I h).1.1 = 0
    rw [← h1, Pi.zero_apply, smul_zero]

end CechSide

theorem proof : Statement := by
  intro S _ Ω _ _ N x G J₀ hcard hmono hadd
  obtain ⟨j₀, hJ₀⟩ := Finset.card_eq_one.mp hcard
  have hj₀U : j₀ ∈ Kleiman.support x := J₀.2.2 (hJ₀ ▸ Finset.mem_singleton_self j₀)
  have hG : ∀ J J' : Kleiman.Chart x, J'.1 = insert j₀ J.1 → G J' = G J := fun J J' h =>
    hadd J J' (by rw [h, hJ₀, Finset.insert_eq])
  refine ⟨fun J => ?_, fun s hs hds => ?_, fun p s hs hds => ?_⟩
  · let J' : Kleiman.Chart x := ⟨insert j₀ J.1, Finset.insert_nonempty _ _, Finset.insert_subset hj₀U J.2.2⟩
    rw [← hG J J' rfl]
    exact hmono J₀ J' (by
      rw [hJ₀]; exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))
  · refine ⟨s ⟨J₀, hcard⟩, (hs ⟨J₀, hcard⟩ (Set.mem_univ _) :), fun J => ?_⟩
    have eb : extZ s {j₀} = s ⟨J₀, hcard⟩ :=
      (congrArg (extZ s) hJ₀).symm.trans (extZ_idx s ⟨J₀, hcard⟩)
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp J.2
    have e1 : cD (cH j₀ (extZ s)) J.1.1 = extZ s {j₀} := by
      rw [hj, cD, Finset.sum_singleton, Finset.erase_singleton, sgn_singleton, one_smul, cH,
        if_neg (Finset.notMem_empty _), insert_empty_eq, sgn_singleton, one_smul]
    rw [← extZ_idx s J, ← cD_cH_add j₀ (extZ s) J.1.1, cH_cD_extZ S hj₀U s hds J, add_zero, e1, eb]
  · refine ⟨fun I => cH j₀ (extZ s) I.1.1, fun I _ => ?_, ?_⟩
    · show cH j₀ (extZ s) I.1.1 ∈ G I.1
      unfold cH
      split_ifs with h
      · exact zero_mem _
      · have hK : s (insIdx hj₀U I h) ∈ G (insIdx hj₀U I h).1 := hs _ (Set.mem_univ _)
        rw [← extZ_idx s (insIdx hj₀U I h), hG I.1 (insIdx hj₀U I h).1 rfl] at hK
        exact zsmul_mem hK _
    · funext J
      rw [d_eq S _ (cH j₀ (extZ s)) (fun _ => rfl)]
      have := cD_cH_add j₀ (extZ s) J.1.1
      rw [cH_cD_extZ S hj₀U s hds J, add_zero, extZ_idx] at this
      exact this

end CechContract

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellMeetsPt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH

namespace CellZeroConst

variable {K : Type} [Fintype K] {ι : K → Type}

def pt (c : ∀ k, ι k) : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0 :=
  ⟨fun k => {c k}, fun _ => Finset.singleton_nonempty _, by simp⟩

theorem exists_pt (c : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0) : ∃ d : ∀ k, ι k, c = pt d := by
  have h1 : ∀ k, (c.1 k).card = 1 := by
    intro k
    have hk : (c.1 k).card - 1 = 0 := (Finset.sum_eq_zero_iff.mp c.2.2) k (Finset.mem_univ _)
    have := (c.2.1 k).card_pos
    omega
  choose d hd using fun k => Finset.card_eq_one.mp (h1 k)
  exact ⟨d, Subtype.ext (funext hd)⟩

theorem cellMeets_pt {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) :
    CellMeets y (pt c).1 ↔ ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  simp [CellMeets, pt]

variable [LinearOrder K] [∀ k, LinearOrder (ι k)]

theorem edge (S : Type) [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)
    (s : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0 → Ω) (hs : cellD S y 0 s = 0) (d : ∀ k, ι k) (k : K)
    {i i' : ι k} (hii : i < i') (hd : ∀ l, l ≠ k → y ⟨l, d l⟩ ≠ 0) (hi : y ⟨k, i⟩ ≠ 0)
    (hi' : y ⟨k, i'⟩ ≠ 0) :
    s (pt (Function.update d k i)) = s (pt (Function.update d k i')) := by
  classical
  have hne : i ≠ i' := hii.ne
  obtain ⟨J, hJk, hJl⟩ : ∃ J : ∀ l, Finset (ι l), J k = {i, i'} ∧ ∀ l, l ≠ k → J l = {d l} :=
    ⟨Function.update (fun l => {d l}) k {i, i'}, by simp, fun l hl => by simp [hl]⟩
  have hJ1 : (∀ l, (J l).Nonempty) ∧ ∑ l, ((J l).card - 1) = 0 + 1 := by
    refine ⟨fun l => ?_, ?_⟩
    · by_cases hl : l = k
      · subst hl; simp [hJk]
      · simp [hJl l hl]
    · rw [Finset.sum_eq_single k (fun l _ hl => by simp [hJl l hl]) (by simp)]
      simp [hJk, Finset.card_pair hne]
  have hm : CellMeets y J := by
    intro l j hj
    by_cases hl : l = k
    · subst hl
      rw [hJk] at hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl <;> assumption
    · rw [hJl l hl, Finset.mem_singleton] at hj
      subst hj
      exact hd l hl

  have hface : ∀ a b : ι k, J k = {a, b} → a ≠ b →
      Function.update J k ((J k).erase a) = (pt (Function.update d k b)).1 := by
    intro a b hab habn
    funext l
    by_cases hl : l = k
    · subst hl
      simp [pt, hab, habn]
    · simp [pt, hl, hJl l hl]
  have hfa := hface i i' hJk hne
  have hfb := hface i' i (by rw [hJk, Finset.pair_comm]) hne.symm
  have hlow : ∑ l ∈ Finset.univ.filter (· < k), ((J l).card - 1) = 0 :=
    Finset.sum_eq_zero fun l hl => by
      rw [hJl l (ne_of_lt (Finset.mem_filter.mp hl).2)]
      simp
  have hsa : faceSign J k i = 1 := by
    unfold faceSign
    rw [hlow, hJk]
    simp [Finset.filter_insert, Finset.filter_singleton, not_lt_of_gt hii]
  have hsb : faceSign J k i' = -1 := by
    unfold faceSign
    rw [hlow, hJk]
    simp [Finset.filter_insert, Finset.filter_singleton, hii]
  have h0 : cellD S y 0 s ⟨J, hJ1⟩ = 0 := by rw [hs]; rfl
  unfold cellD at h0
  erw [LinearMap.pi_apply] at h0
  erw [if_pos (show CellMeets y J from hm)] at h0
  rw [LinearMap.sum_apply, Finset.sum_eq_single k] at h0
  rotate_left
  · intro l _ hl
    rw [LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [dite_eq_right]
    · rfl
    rintro ⟨hn, -⟩
    have h2 := hn l
    rw [Function.update_self] at h2
    change j ∈ J l at hj
    rw [hJl l hl, Finset.mem_singleton] at hj
    subst hj
    change ((J l).erase (d l)).Nonempty at h2
    rw [hJl l hl] at h2
    simp at h2
  · simp
  rw [LinearMap.sum_apply, Finset.sum_eq_add i i' hne] at h0
  rotate_left
  · intro j hj hj2
    change j ∈ J k at hj
    rw [hJk] at hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact absurd rfl hj2.1
    · exact absurd rfl hj2.2
  · intro h; exact absurd (show i ∈ J k by rw [hJk]; simp) h
  · intro h; exact absurd (show i' ∈ J k by rw [hJk]; simp) h
  rw [dite_eq_left (hfa ▸ (pt (Function.update d k i')).2), dite_eq_left (hfb ▸ (pt (Function.update d k i)).2)] at h0
  simp only [LinearMap.smul_apply] at h0
  erw [LinearMap.proj_apply, LinearMap.proj_apply] at h0
  have e1 : ∀ h, s ⟨Function.update J k ((J k).erase i), h⟩ = s (pt (Function.update d k i')) :=
    fun _ => congrArg s (Subtype.ext hfa)
  have e2 : ∀ h, s ⟨Function.update J k ((J k).erase i'), h⟩ = s (pt (Function.update d k i)) :=
    fun _ => congrArg s (Subtype.ext hfb)
  rw [hsa, hsb, e1, e2, one_smul, neg_smul, one_smul] at h0
  linear_combination -h0

theorem step (S : Type) [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)
    (s : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0 → Ω) (hs : cellD S y 0 s = 0) (d : ∀ k, ι k)
    (hd : ∀ l, y ⟨l, d l⟩ ≠ 0) (k : K) (j : ι k) (hj : y ⟨k, j⟩ ≠ 0) :
    s (pt d) = s (pt (Function.update d k j)) := by
  classical
  have hdl : ∀ l, l ≠ k → y ⟨l, d l⟩ ≠ 0 := fun l _ => hd l
  rcases lt_trichotomy (d k) j with h | h | h
  · have := edge S y s hs d k h hdl (hd k) hj
    rwa [Function.update_eq_self] at this
  · rw [← h, Function.update_eq_self]
  · have := edge S y s hs d k h hdl hj (hd k)
    rw [Function.update_eq_self] at this
    exact this.symm

theorem chain (S : Type) [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)
    (s : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0 → Ω) (hs : cellD S y 0 s = 0) (d d' : ∀ k, ι k)
    (hd : ∀ l, y ⟨l, d l⟩ ≠ 0) (hd' : ∀ l, y ⟨l, d' l⟩ ≠ 0) :
    s (pt d) = s (pt d') := by
  classical
  have key : ∀ T : Finset K, s (pt d) = s (pt (fun l => if l ∈ T then d' l else d l)) := by
    intro T
    refine Finset.induction_on T ?_ ?_
    · simp
    · intro a T ha ih
      rw [ih]
      have hmeet : ∀ l, y ⟨l, (fun l => if l ∈ T then d' l else d l) l⟩ ≠ 0 := fun l => by
        dsimp only
        split_ifs
        · exact hd' l
        · exact hd l
      rw [step S y s hs _ hmeet a (d' a) (hd' a)]
      congr 2
      funext l
      by_cases hl : l = a
      · subst hl
        simp
      · simp [hl]
  simpa using key Finset.univ

end CellZeroConst

theorem CellZeroConst.proof : CellZeroConst.Statement := by
  intro S _ K _ _ ι _ _ Ω _ _ y s hs c c' hc hc'
  obtain ⟨d, rfl⟩ := CellZeroConst.exists_pt c
  obtain ⟨d', rfl⟩ := CellZeroConst.exists_pt c'
  rw [CellZeroConst.cellMeets_pt] at hc hc'
  exact CellZeroConst.chain S y s hs d d' hc hc'

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
