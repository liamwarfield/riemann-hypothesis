module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieAxes

@[expose] public section

section -- merged from Formalism.LocalToGlobal.CharacterGerms.ValNonnegLeadingCoeffOfMemTySet
section -- merged from Formalism.LocalToGlobal.CharacterGerms.ConstMemTypeSetOfNonneg
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

section TyS

variable {l : ℕ} (hl : 2 ≤ l)

include hl

theorem coeff_tyS_pow (a : ℕ → C) (s : ℕ) : PowerSeries.coeff (l ^ s) (tyS l a) = a s := by
  unfold tyS
  rw [PowerSeries.coeff_mk]
  have hinj : ∀ t, l ^ t = l ^ s ↔ t = s := fun t => (Nat.pow_right_injective hl).eq_iff
  simp only [hinj]
  rw [Finset.sum_ite_eq', if_pos]
  have hs : s < l ^ s := Nat.lt_pow_self (by omega)
  exact Finset.mem_range.2 (by omega)

omit hl in
theorem coeff_tyS_of_ne (a : ℕ → C) (m : ℕ) (hm : ∀ s, l ^ s ≠ m) : PowerSeries.coeff m (tyS l a) = 0 := by
  unfold tyS
  rw [PowerSeries.coeff_mk]
  exact Finset.sum_eq_zero fun s _ => if_neg (hm s)

theorem tyS_eq (a : ℕ → C) (f : PowerSeries C) (h1 : ∀ s, PowerSeries.coeff (l ^ s) f = a s)
    (h2 : ∀ m, (∀ s, l ^ s ≠ m) → PowerSeries.coeff m f = 0) : tyS l a = f := by
  ext m
  by_cases h : ∃ s, l ^ s = m
  · obtain ⟨s, rfl⟩ := h
    rw [coeff_tyS_pow hl, h1]
  · push_neg at h
    rw [coeff_tyS_of_ne a m h, h2 m h]

omit hl in
theorem tyS_zero : tyS l (fun _ => (0 : C)) = 0 := by
  ext m
  unfold tyS
  simp

end TyS

section Repar

theorem van_univ {τ : Type} {f : MvPowerSeries τ C} (h : MvPowerSeries.constantCoeff f = 0) :
    Van Set.univ f := by
  intro ν hν
  have hν0 : ν = 0 := by
    ext w
    by_contra hw
    exact hν w (Finsupp.mem_support_iff.2 hw) (Set.mem_univ w)
  subst hν0
  simpa using h

theorem constantCoeff_subst_zero {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) {f : MvPowerSeries σ C}
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Finsupp.prod, map_prod]
  simp only [map_pow, ha]
  by_cases hd : d = 0
  · subst hd
    simp [hf]
  · obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    have h0 : (∏ x ∈ d.support, (0 : C) ^ d x) = 0 :=
      Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hs) (zero_pow hs)
    rw [h0, smul_zero]

theorem alongCv_repar {σ : Type} [Finite σ] {γ : σ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) {τ : PowerSeries C} (hτ : PowerSeries.constantCoeff τ = 0)
    (f : MvPowerSeries σ C) :
    alongCv (fun i => PowerSeries.subst τ (γ i)) f = PowerSeries.subst τ (alongCv γ f) := by
  unfold alongCv
  have hγs : MvPowerSeries.HasSubst γ := MvPowerSeries.hasSubst_of_constantCoeff_zero hγ
  have hτs : MvPowerSeries.HasSubst (fun _ : Unit => τ) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hτ)
  exact (MvPowerSeries.subst_comp_subst_apply hγs hτs f).symm

theorem alongCv_zero {σ : Type} [Finite σ] {f : MvPowerSeries σ C} (hf : MvPowerSeries.constantCoeff f = 0) :
    alongCv (fun _ : σ => (0 : PowerSeries C)) f = 0 := by
  unfold alongCv
  have ha : MvPowerSeries.HasSubst (fun _ : σ => (0 : PowerSeries C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => map_zero _)
  refine MvPowerSeries.ext fun e => ?_
  rw [MvPowerSeries.coeff_subst ha, map_zero]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  by_cases hd : d = 0
  · subst hd
    simp [hf]
  · obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    have h0 : (d.prod fun _ e => (0 : PowerSeries C) ^ e) = 0 :=
      Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hs) (zero_pow hs)
    simp only [h0, map_zero, smul_zero]

end Repar

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

private theorem ge_zero_lemma (V : VF C) : V.Ge 0 (0 : C) := by
  change ((0 : ℝ) : WithTop ℝ) ≤ V.v 0
  rw [AddValuation.map_zero]
  exact le_top

private theorem ge_mul_lemma_2 (V : VF C) {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) : V.Ge 0 (a * b) := by
  change ((0 : ℝ) : WithTop ℝ) ≤ V.v (a * b)
  rw [AddValuation.map_mul]
  have h := add_le_add (show ((0 : ℝ) : WithTop ℝ) ≤ V.v a from ha) (show ((0 : ℝ) : WithTop ℝ) ≤ V.v b from hb)
  simpa using h

private theorem ge_zero_pow' (V : VF C) {a : C} (ha : V.Ge 0 a) (n : ℕ) : V.Ge 0 (a ^ n) := by
  induction n with
  | zero =>
    change ((0 : ℝ) : WithTop ℝ) ≤ V.v (a ^ 0)
    rw [pow_zero, AddValuation.map_one]
    simp
  | succ n ih =>
    rw [pow_succ]
    exact ge_mul_lemma_2 V ih ha

theorem TySet_repar {V : VF C} {g : Fin 2} (τ : PowerSeries C) (hτ : PowerSeries.constantCoeff τ = 0)
    (hint : ∀ f : PowerSeries C, (∀ n, V.Ge 0 (PowerSeries.coeff n f)) →
      ∀ n, V.Ge 0 (PowerSeries.coeff n (PowerSeries.subst τ f)))
    {x x' : ℕ → I g ⊕ JJ I g → C} (hx : x ∈ X.TySet V g)
    (hxx : ∀ n, tyS V.l (fun s => x' s n) = PowerSeries.subst τ (tyS V.l fun s => x s n)) :
    x' ∈ X.TySet V g := by
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := hx
  have hτs : PowerSeries.HasSubst τ := PowerSeries.HasSubst.of_constantCoeff_zero' hτ
  have hs : ∀ f : PowerSeries C, PowerSeries.subst τ f = PowerSeries.substAlgHom hτs f := fun f => by
    rw [PowerSeries.coe_substAlgHom]
  have hγ0 : ∀ j, PowerSeries.constantCoeff (γ j) = 0 := fun j => (hγ j).1
  refine ⟨fun i => PowerSeries.subst τ (γ i), fun q => PowerSeries.subst τ (lam q), ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨constantCoeff_subst_zero (a := fun _ : Unit => τ) (fun _ => hτ) (hγ i).1, hint _ (hγ i).2⟩
  · intro q
    exact ⟨constantCoeff_subst_zero (a := fun _ : Unit => τ) (fun _ => hτ) (hlam q).1, hint _ (hlam q).2⟩
  · intro i
    rw [alongCv_repar hγ0 hτ, h1 i]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hxx, hs, map_sum, map_smul]
  · intro q
    rw [hxx, h2 q, alongCv_repar hγ0 hτ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hxx, hs, map_add (f := _), map_sub, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs <;> simp

private theorem coeff_subst_smul_X (c : C) (f : PowerSeries C) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.subst (c • (PowerSeries.X : PowerSeries C)) f) = c ^ n * PowerSeries.coeff n f := by
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [PowerSeries.smul_eq_C_mul])),
    finsum_eq_single _ n]
  · rw [smul_pow, PowerSeries.coeff_smul, PowerSeries.coeff_X_pow_self, smul_eq_mul]
    ring
  · intro d hd
    rw [smul_pow, PowerSeries.coeff_smul, PowerSeries.coeff_X_pow, if_neg (Ne.symm hd), smul_zero, smul_zero]

theorem teich_mem (V : VF C) (g : Fin 2) (c : C) (hc : V.Ge 0 c) (x : ℕ → I g ⊕ JJ I g → C)
    (hx : x ∈ X.TySet V g) : teich V.l c x ∈ X.TySet V g := by
  have hl := V.l_prime.two_le
  refine X.TySet_repar (c • PowerSeries.X) (by simp [PowerSeries.smul_eq_C_mul]) (fun f hf n => ?_) hx (fun m => ?_)
  · rw [coeff_subst_smul_X]
    exact ge_mul_lemma_2 V (ge_zero_pow' V hc n) (hf n)
  · refine tyS_eq hl _ _ (fun s => ?_) (fun k hk => ?_)
    · rw [coeff_subst_smul_X, coeff_tyS_pow hl]
      rfl
    · rw [coeff_subst_smul_X, coeff_tyS_of_ne _ _ hk, mul_zero]

end RawChart

theorem coeff_subst_X_pow {l : ℕ} (hl : 0 < l) (f : PowerSeries C) (q : ℕ) :
    PowerSeries.coeff (l * q) (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) f) = PowerSeries.coeff q f := by
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hl.ne'])), finsum_eq_single _ q]
  · rw [← pow_mul, PowerSeries.coeff_X_pow_self, smul_eq_mul, mul_one]
  · intro d hd
    rw [← pow_mul, PowerSeries.coeff_X_pow, if_neg, smul_zero]
    intro h
    exact hd (Nat.eq_of_mul_eq_mul_left hl h).symm

theorem coeff_subst_X_pow_of_not_dvd {l : ℕ} (hl : 0 < l) (f : PowerSeries C) (m : ℕ) (hm : ¬ l ∣ m) :
    PowerSeries.coeff m (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) f) = 0 := by
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hl.ne']))]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  rw [← pow_mul, PowerSeries.coeff_X_pow, if_neg, smul_zero]
  rintro rfl
  exact hm (dvd_mul_right l d)

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

theorem V_mem (V : VF C) (g : Fin 2) (x : ℕ → I g ⊕ JJ I g → C) (hx : x ∈ X.TySet V g) :
    Vpow 1 x ∈ X.TySet V g := by
  have hl := V.l_prime.two_le
  have hl0 : 0 < V.l := by omega
  refine X.TySet_repar (PowerSeries.X ^ V.l) (by simp [hl0.ne']) (fun f hf m => ?_) hx (fun m => ?_)
  · by_cases hd : V.l ∣ m
    · obtain ⟨q, rfl⟩ := hd
      rw [coeff_subst_X_pow hl0]
      exact hf q
    · rw [coeff_subst_X_pow_of_not_dvd hl0 _ _ hd]
      exact ge_zero_lemma V
  · refine tyS_eq hl _ _ (fun s => ?_) (fun k hk => ?_)
    · cases s with
      | zero =>
        rw [pow_zero, coeff_subst_X_pow_of_not_dvd hl0 _ _ V.l_prime.not_dvd_one]
        simp [Vpow]
      | succ s =>
        rw [pow_succ', coeff_subst_X_pow hl0, coeff_tyS_pow hl]
        simp [Vpow]
    · by_cases hd : V.l ∣ k
      · obtain ⟨q, rfl⟩ := hd
        rw [coeff_subst_X_pow hl0, coeff_tyS_of_ne _ _ (fun s hs => hk (s + 1) (by rw [pow_succ', hs]))]
      · rw [coeff_subst_X_pow_of_not_dvd hl0 _ _ hd]

theorem constantCoeff_sg (hh : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 0) → MvPowerSeries.coeff e X.h = 0)
    (v : κ → C) : MvPowerSeries.constantCoeff (X.sg v) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  change -∑ i, v i * MvPowerSeries.coeff ((0 : κ →₀ ℕ).mapDomain (fun x : κ => ((0 : Fin 2), x)) +
    Finsupp.single ((1 : Fin 2), i) 1) X.h = 0
  simp only [Finsupp.mapDomain_zero, zero_add]
  rw [Finset.sum_eq_zero, neg_zero]
  intro i _
  rw [hh _ ?_, mul_zero]
  intro s hs
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hs
  rw [hs]
  simp

theorem const_mem_type_set_of_nonneg (hlg : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hh : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 0) → MvPowerSeries.coeff e X.h = 0)
    (V : VF C) (g : Fin 2) (ζ : JJ I g → C) (hζ : ∀ q, V.Ge 0 (ζ q)) :
    const0 (Sum.elim 0 ζ) ∈ X.TySet V g := by
  have hl := V.l_prime.two_le
  have hinl : ∀ c : I g, tyS V.l (fun s => const0 (Sum.elim 0 ζ) s (Sum.inl c : I g ⊕ JJ I g)) = 0 := by
    intro c
    rw [show (fun s => const0 (Sum.elim 0 ζ) s (Sum.inl c : I g ⊕ JJ I g)) = fun _ => (0 : C) by
      funext s
      simp [const0]]
    exact tyS_zero
  have hinr : ∀ q : JJ I g, tyS V.l (fun s => const0 (Sum.elim 0 ζ) s (Sum.inr q : I g ⊕ JJ I g)) =
      ζ q • PowerSeries.X := by
    intro q
    refine tyS_eq hl _ _ (fun s => ?_) (fun m hm => ?_)
    · cases s with
      | zero => simp [const0]
      | succ s =>
        have h1 : 1 < V.l ^ (s + 1) :=
          calc 1 < V.l := by omega
            _ = V.l ^ 1 := (pow_one _).symm
            _ ≤ V.l ^ (s + 1) := Nat.pow_le_pow_right (by omega) (by omega)
        have hl1 : V.l ≠ 1 := by omega
        simp [const0, PowerSeries.coeff_X, h1.ne', hl1]
    · have hm1 : m ≠ 1 := fun h => hm 0 (by simp [h])
      simp [PowerSeries.coeff_X, hm1]
  refine ⟨fun _ => 0, fun q => ζ q • PowerSeries.X, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨map_zero _, fun n => by simpa using ge_zero_lemma V⟩
  · intro q
    refine ⟨by simp, fun n => ?_⟩
    rw [PowerSeries.coeff_smul, PowerSeries.coeff_X]
    split_ifs
    · simpa using hζ q
    · simpa using ge_zero_lemma V
  · intro i
    rw [alongCv_zero (hlg i)]
    simp [hinl]
  · intro q
    rw [hinr, alongCv_zero (X.constantCoeff_sg hh _)]
    simp [hinl]

theorem zero_mem (hlg : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hh : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 0) → MvPowerSeries.coeff e X.h = 0)
    (V : VF C) (g : Fin 2) : (0 : ℕ → I g ⊕ JJ I g → C) ∈ X.TySet V g := by
  refine ⟨fun _ => 0, fun _ => 0, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨map_zero _, fun n => by simpa using ge_zero_lemma V⟩
  · intro q
    exact ⟨map_zero _, fun n => by simpa using ge_zero_lemma V⟩
  · intro i
    rw [alongCv_zero (hlg i)]
    simp [tyS_zero]
  · intro q
    rw [alongCv_zero (X.constantCoeff_sg hh _)]
    simp [tyS_zero]

end RawChart

end Formalism.L2.FormalSeriesBounds
end
end

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

theorem finsupp_deg_one {σ : Type} (e : σ →₀ ℕ) (h : e.degree = 1) : ∃ i, e = Finsupp.single i 1 := by
  classical
  have hdeg : ∑ j ∈ e.support, e j = 1 := h
  have hne : e.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he, Finset.sum_empty] at hdeg
    exact absurd hdeg (by norm_num)
  obtain ⟨i, hi⟩ := hne
  have hle : ∀ j ∈ e.support, e j ≤ 1 := fun j hj =>
    hdeg ▸ Finset.single_le_sum (f := fun k => e k) (fun _ _ => Nat.zero_le _) hj
  have hei : e i = 1 := by
    have h1 := hle i hi
    have h2 := Finsupp.mem_support_iff.mp hi
    omega
  refine ⟨i, ?_⟩
  ext j
  by_cases hj : j = i
  · subst hj
    simp [hei]
  · rw [Finsupp.single_apply, if_neg (Ne.symm hj)]
    by_contra hc
    have hjs : j ∈ e.support := Finsupp.mem_support_iff.mpr hc
    have h2 : e i + e j ≤ ∑ k ∈ e.support, e k := by
      rw [← Finset.sum_pair (f := fun k => e k) (Ne.symm hj)]
      apply Finset.sum_le_sum_of_subset
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hi
      · exact hjs
    omega

theorem coeff_alongCv_low {σ : Type} [Fintype σ] {γ : σ → PowerSeries C} {n : ℕ} (hn : 1 ≤ n)
    (hγ : ∀ i, ∀ m < n, PowerSeries.coeff m (γ i) = 0) {f : MvPowerSeries σ C}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    PowerSeries.coeff n (alongCv γ f) =
      ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) f * PowerSeries.coeff n (γ i) := by
  have hγ0 : ∀ i, MvPowerSeries.constantCoeff (γ i) = 0 := fun i => by
    have := hγ i 0 (by omega)
    rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
  unfold alongCv
  show MvPowerSeries.coeff (Finsupp.single () n) _ = _
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hγ0),
    finsum_eq_sum_of_support_subset (s := Finset.univ.image fun i : σ => Finsupp.single i 1)]
  · rw [Finset.sum_image (fun a _ b _ h => Finsupp.single_left_injective one_ne_zero h)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hp : (Finsupp.single i 1 : σ →₀ ℕ).prod (fun s e => γ s ^ e) = γ i := by
      rw [Finsupp.prod_single_index (h := fun s e => γ s ^ e) (pow_zero _), pow_one]
    show MvPowerSeries.coeff (Finsupp.single i 1) f •
      MvPowerSeries.coeff (Finsupp.single () n) ((Finsupp.single i 1 : σ →₀ ℕ).prod fun s e => γ s ^ e) = _
    rw [hp, smul_eq_mul]
    rfl
  · intro e he
    rw [Function.mem_support] at he
    rw [Finset.coe_image, Set.mem_image]
    by_contra hc
    apply he
    have hdeg : e.degree ≠ 1 := fun h => by
      obtain ⟨i, hi⟩ := finsupp_deg_one e h
      exact hc ⟨i, by simp, hi.symm⟩
    by_cases h0 : e.degree = 0
    · rw [Finsupp.degree_eq_zero_iff] at h0
      rw [h0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
    · have h2 : 2 ≤ e.degree := by omega
      have hdvd : (PowerSeries.X : PowerSeries C) ^ (n * e.degree) ∣ e.prod fun s m => γ s ^ m := by
        unfold Finsupp.prod
        rw [Finsupp.degree_apply, pow_mul, ← Finset.prod_pow_eq_pow_sum]
        apply Finset.prod_dvd_prod_of_dvd
        intro i _
        exact pow_dvd_pow_of_dvd (PowerSeries.X_pow_dvd_iff.2 (hγ i)) _
      have hz : PowerSeries.coeff n (e.prod fun s m => γ s ^ m) = 0 :=
        PowerSeries.X_pow_dvd_iff.1 hdvd n (by nlinarith)
      show MvPowerSeries.coeff e f • PowerSeries.coeff n (e.prod fun s m => γ s ^ m) = 0
      rw [hz, smul_zero]

theorem coeff_tyS_lt {l : ℕ} (hl : 2 ≤ l) (a : ℕ → C) (s : ℕ) (ha : ∀ i < s, a i = 0) (m : ℕ) (hm : m < l ^ s) :
    PowerSeries.coeff m (tyS l a) = 0 := by
  simp only [tyS, PowerSeries.coeff_mk]
  apply Finset.sum_eq_zero
  intro t _
  split_ifs with ht
  · apply ha
    by_contra hc
    push_neg at hc
    have : l ^ s ≤ l ^ t := Nat.pow_le_pow_right (by omega) hc
    omega
  · rfl

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

theorem val_nonneg_leading_coeff_of_mem_tySet (V : VF C) (g : Fin 2)
    (hlin : ∀ i (μ : κ →₀ ℕ), μ.degree ≤ 1 →
      MvPowerSeries.coeff μ (X.lg i) = MvPowerSeries.coeff μ (MvPowerSeries.X i : MvPowerSeries κ C))
    (hh : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 0) → MvPowerSeries.coeff e X.h = 0)
    (hsat : ∃ w : κ → I g → C, (∀ x c, V.Ge 0 (w x c)) ∧
      ∀ c c' : I g, ∑ x, X.u g c x * w x c' = if c = c' then 1 else 0)
    (hmis : ∀ (c : I g) (q : JJ I g), X.ty g c ≠ X.ty (1 - g) q → V.Ge 0 (X.sg1 (X.u g c) (X.u (1 - g) q)))
    (x : ℕ → I g ⊕ JJ I g → C) (hx : x ∈ X.TySet V g) (s : ℕ) (h0 : ∀ i < s, x i = 0) (n : I g ⊕ JJ I g) :
    V.Ge 0 (x s n) := by
  have hl2 := V.l_prime.two_le
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := hx
  obtain ⟨w, hw, huw⟩ := hsat
  have hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0 := fun i => by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hlin i 0 (by simp),
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_X]
  have hlg1 : ∀ i j, MvPowerSeries.coeff (Finsupp.single j 1) (X.lg i) = if j = i then 1 else 0 := fun i j => by
    rw [hlin i _ (by rw [Finsupp.degree_single]), MvPowerSeries.coeff_X]
    by_cases hji : j = i
    · rw [hji, if_pos rfl, if_pos rfl]
    · rw [if_neg hji, if_neg]
      intro h
      exact hji (Finsupp.single_left_injective one_ne_zero h)
  have hpos : 1 ≤ V.l ^ s := Nat.one_le_pow _ _ (by omega)
  have hlow : ∀ (m : ℕ) (hm1 : 1 ≤ m), (∀ i, ∀ m' < m, PowerSeries.coeff m' (γ i) = 0) → ∀ i,
      PowerSeries.coeff m (γ i) = ∑ c : I g, X.u g c i * PowerSeries.coeff m (tyS V.l fun s => x s (Sum.inl c)) := by
    intro m hm1 hm i
    have e1 := coeff_alongCv_low hm1 hm (hlg0 i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h1 i, map_sum] at e1
    simp only [hlg1, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      PowerSeries.coeff_smul, smul_eq_mul] at e1
    exact e1.symm
  have hord : ∀ m, m < V.l ^ s → ∀ i, PowerSeries.coeff m (γ i) = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm i
      by_cases hm0 : m = 0
      · rw [hm0, PowerSeries.coeff_zero_eq_constantCoeff_apply]
        exact (hγ i).1
      · rw [hlow m (by omega) (fun i m' hm' => ih m' hm' (by omega) i) i]
        apply Finset.sum_eq_zero
        intro c _
        rw [coeff_tyS_lt hl2 _ s (fun i hi => by rw [h0 i hi]; rfl) m hm, mul_zero]
  have hord' : ∀ i, ∀ m < V.l ^ s, PowerSeries.coeff m (γ i) = 0 := fun i m hm => hord m hm i
  have hlead : ∀ i, PowerSeries.coeff (V.l ^ s) (γ i) = ∑ c : I g, X.u g c i * x s (Sum.inl c) := by
    intro i
    rw [hlow _ hpos hord' i]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [coeff_tyS_pow hl2]
  have hinl : ∀ c', x s (Sum.inl c') = ∑ i, PowerSeries.coeff (V.l ^ s) (γ i) * w i c' := by
    intro c'
    simp only [hlead, Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ c : I g, ∑ i, X.u g c i * x s (Sum.inl c) * w i c' = (if c = c' then 1 else 0) * x s (Sum.inl c) := by
      intro c
      rw [← huw c c', Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => by ring
    simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hinlInt : ∀ c', V.Ge 0 (x s (Sum.inl c')) := by
    intro c'
    rw [hinl c']
    exact VF.Ge.sum fun i _ => ((hγ i).2 _).mul_int (hw i c')
  cases n with
  | inl c' => exact hinlInt c'
  | inr q =>
    have e2 := congrArg (PowerSeries.coeff (V.l ^ s)) (h2 q)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [coeff_tyS_pow hl2, map_add (f := _), map_sub, coeff_alongCv_low hpos hord' (X.constantCoeff_sg hh _), map_sum] at e2
    have e3 : ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) (X.sg (X.u (1 - g) q)) * PowerSeries.coeff (V.l ^ s) (γ i) =
        ∑ c : I g, X.sg1 (X.u g c) (X.u (1 - g) q) * x s (Sum.inl c) := by
      simp only [hlead, sg1, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => by ring
    have e4 : ∀ c : I g, PowerSeries.coeff (V.l ^ s) (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => x s (Sum.inl c)) else 0) =
        if X.ty g c = X.ty (1 - g) q then X.sg1 (X.u g c) (X.u (1 - g) q) * x s (Sum.inl c) else 0 := by
      intro c
      split_ifs
      · rw [PowerSeries.coeff_smul, coeff_tyS_pow hl2, smul_eq_mul]
      · rw [map_zero]
    simp only [e4] at e2
    rw [e3, sub_add, ← Finset.sum_sub_distrib] at e2
    rw [e2]
    refine ((hlam q).2 _).sub (VF.Ge.sum fun c _ => ?_)
    split_ifs with hc
    · rw [sub_self]
      exact VF.Ge.zero 0
    · rw [sub_zero]
      exact (hmis c q hc).mul_int (hinlInt c)

end RawChart

end Formalism.L2.FormalSeriesBounds
end
end

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

theorem tyS_add {l : ℕ} (hl : 2 ≤ l) (a b : ℕ → C) : tyS l (fun s => a s + b s) = tyS l a + tyS l b := by
  ext n
  simp only [tyS, PowerSeries.coeff_mk, map_add (f := _), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> simp

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

def AddCvSt (V : VF C) : Prop :=
  ∀ γ γ' : κ → PowerSeries C, IsCv V γ → IsCv V γ' →
    ∃ γ'' : κ → PowerSeries C, IsCv V γ'' ∧
      (∀ i, alongCv γ'' (X.lg i) = alongCv γ (X.lg i) + alongCv γ' (X.lg i)) ∧
      ∀ v : κ → C, (∀ i, V.Ge 0 (v i)) →
        PowerSeries.constantCoeff (alongCv γ'' (X.sg v) - alongCv γ (X.sg v) - alongCv γ' (X.sg v)) = 0 ∧
        ∀ n, V.Ge 0 (PowerSeries.coeff n (alongCv γ'' (X.sg v) - alongCv γ (X.sg v) - alongCv γ' (X.sg v)))

theorem add_mem (V : VF C) (g : Fin 2) (hA : X.AddCvSt V) (hu : ∀ g c i, V.Ge 0 (X.u g c i))
    (x y : ℕ → I g ⊕ JJ I g → C) (hx : x ∈ X.TySet V g) (hy : y ∈ X.TySet V g) : x + y ∈ X.TySet V g := by
  have hl2 := V.l_prime.two_le
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := hx
  obtain ⟨γ', lam', hγ', hlam', h1', h2'⟩ := hy
  obtain ⟨γ'', hγ'', hL, hS⟩ := hA γ γ' hγ hγ'
  have hty : ∀ n, tyS V.l (fun s => (x + y) s n) = tyS V.l (fun s => x s n) + tyS V.l (fun s => y s n) :=
    fun n => tyS_add hl2 _ _
  refine ⟨γ'', fun q => lam q + lam' q + (alongCv γ'' (X.sg (X.u (1 - g) q)) - alongCv γ (X.sg (X.u (1 - g) q)) -
    alongCv γ' (X.sg (X.u (1 - g) q))), hγ'', ?_, ?_, ?_⟩
  · intro q
    obtain ⟨c0, cI⟩ := hS (X.u (1 - g) q) (hu (1 - g) q)
    refine ⟨?_, fun n => ?_⟩
    · rw [map_add (f := _), map_add (f := _), (hlam q).1, (hlam' q).1, c0]
      simp
    · rw [map_add (f := _), map_add (f := _)]
      exact (((hlam q).2 n).add ((hlam' q).2 n)).add (cI n)
  · intro i
    rw [hL i, h1 i, h1' i, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hty, smul_add]
  · intro q
    have hs : ∀ c : I g, (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => (x + y) s (Sum.inl c)) else 0) =
        (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => x s (Sum.inl c)) else 0) +
        (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => y s (Sum.inl c)) else 0) := by
      intro c
      rw [hty]
      split_ifs
      · rw [smul_add]
      · rw [add_zero]
    simp only [hs]
    rw [Finset.sum_add_distrib, hty, h2 q, h2' q]
    abel

private theorem powerSeries_rescale_smul (a c : C) (f : PowerSeries C) :
    PowerSeries.rescale a (c • f) = c • PowerSeries.rescale a f := by
  ext n
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_smul, smul_eq_mul]
  ring

private theorem alongCv_rescale_eq_rescale_alongCv {σ : Type} [Finite σ] {γ : σ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (a : C) (f : MvPowerSeries σ C) :
    alongCv (fun i => PowerSeries.rescale a (γ i)) f = PowerSeries.rescale a (alongCv γ f) := by
  simp only [PowerSeries.rescale_eq_subst]
  exact alongCv_repar hγ (by simp) f

private theorem tyS_neg_eq_rescale_neg_one_of_odd {l : ℕ} (hl : Odd l) (a : ℕ → C) :
    tyS l (fun s => -a s) = PowerSeries.rescale (-1) (tyS l a) := by
  ext n
  simp only [tyS, PowerSeries.coeff_mk, PowerSeries.coeff_rescale, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs with h
  · rw [← h, (hl.pow).neg_one_pow]
    ring
  · ring

private theorem isCv_rescale_neg_one (V : VF C) {σ : Type} {γ : σ → PowerSeries C} (h : IsCv V γ) :
    IsCv V (fun i => PowerSeries.rescale (-1 : C) (γ i)) := by
  intro i
  show PowerSeries.constantCoeff (PowerSeries.rescale (-1 : C) (γ i)) = 0 ∧
    ∀ n, V.Ge 0 (PowerSeries.coeff n (PowerSeries.rescale (-1 : C) (γ i)))
  refine ⟨?_, fun n => ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (h i).1
  · have h2 := (h i).2 n
    rw [PowerSeries.coeff_rescale]
    rcases neg_one_pow_eq_or C n with e | e
    · rw [e, one_mul]
      exact h2
    · rw [e, neg_one_mul]
      unfold VF.Ge at h2 ⊢
      rw [V.v.map_neg]
      exact h2

theorem neg_mem (V : VF C) (g : Fin 2) (hodd : V.l ≠ 2) (x : ℕ → I g ⊕ JJ I g → C) (hx : x ∈ X.TySet V g) :
    -x ∈ X.TySet V g := by
  have hl : Odd V.l := V.l_prime.odd_of_ne_two hodd
  unfold RawChart.TySet at hx ⊢
  obtain ⟨γ, lam, hγ, hlam, hlg, hq⟩ := hx
  have hγ0 : ∀ i, PowerSeries.constantCoeff (γ i) = 0 := fun i => (hγ i).1
  rw [Set.mem_setOf_eq]
  refine ⟨fun i => PowerSeries.rescale (-1 : C) (γ i), fun q => PowerSeries.rescale (-1 : C) (lam q),
    isCv_rescale_neg_one V hγ, isCv_rescale_neg_one V hlam, ?_, ?_⟩
  · intro i
    simp only [Pi.neg_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [alongCv_rescale_eq_rescale_alongCv hγ0, hlg i, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [tyS_neg_eq_rescale_neg_one_of_odd hl, powerSeries_rescale_smul]
  · intro q
    simp only [Pi.neg_apply]
    rw [tyS_neg_eq_rescale_neg_one_of_odd hl, hq q, alongCv_rescale_eq_rescale_alongCv hγ0]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [tyS_neg_eq_rescale_neg_one_of_odd hl, map_add (f := _), map_sub, map_sum, apply_ite ⇑(PowerSeries.rescale (-1 : C)), map_zero,
      powerSeries_rescale_smul]

theorem sum_mem (V : VF C) (g : Fin 2) (h0 : (0 : ℕ → I g ⊕ JJ I g → C) ∈ X.TySet V g)
    (hadd : ∀ x y, x ∈ X.TySet V g → y ∈ X.TySet V g → x + y ∈ X.TySet V g) {ι : Type} (s : Finset ι)
    (f : ι → ℕ → I g ⊕ JJ I g → C) (hf : ∀ i ∈ s, f i ∈ X.TySet V g) : ∑ i ∈ s, f i ∈ X.TySet V g := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.sum_empty]
    exact h0
  · intro a s ha ih hf
    rw [Finset.sum_insert ha]
    exact hadd _ _ (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end RawChart

end Formalism.L2.FormalSeriesBounds
