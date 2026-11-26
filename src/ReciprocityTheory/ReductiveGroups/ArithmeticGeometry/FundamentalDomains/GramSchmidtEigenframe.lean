module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ExistsUnitaryBasisSameFlag

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MmatUnitary
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PerpSpanRight
namespace ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
  (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)

def hL (v : Fin r → ℂ) : (Fin r → ℂ) →ₗ[ℂ] ℂ where
  toFun u := hermC τ G u v
  map_add' u u' := hermC_add_left τ G u u' v
  map_smul' c u := by simp [hermC_smul_left]

theorem perp_span {s : Set (Fin r → ℂ)} {v : Fin r → ℂ} (h : ∀ y ∈ s, hermC τ G y v = 0) :
    ∀ y ∈ Submodule.span ℂ s, hermC τ G y v = 0 := by
  intro y hy
  have hle : Submodule.span ℂ s ≤ LinearMap.ker (hL τ G v) :=
    Submodule.span_le.mpr (fun z hz => LinearMap.mem_ker.mpr (h z hz))
  exact LinearMap.mem_ker.mp (hle hy)

theorem perp_span_right (hG : ∀ a b, cc (G a b) = G b a) {s : Set (Fin r → ℂ)} {v : Fin r → ℂ}
    (h : ∀ y ∈ s, hermC τ G v y = 0) : ∀ y ∈ Submodule.span ℂ s, hermC τ G v y = 0 := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp [hermC]
  | add x y _ _ hx hy =>
    have e : hermC τ G v (x + y) = hermC τ G v x + hermC τ G v y := by
      simp only [hermC, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
    rw [e, hx, hy, add_zero]
  | smul c x _ hx =>
    have e : hermC τ G v (c • x) = conj c * hermC τ G v x := by
      simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      ring
    rw [e, hx, mul_zero]

theorem coef_of_mem {n : ℕ} (Y : Fin n → Fin r → ℂ) (S : Set (Fin n)) {v : Fin r → ℂ}
    (hv : v ∈ Submodule.span ℂ (Y '' S)) :
    ∃ w : Fin n → ℂ, (∀ j, j ∉ S → w j = 0) ∧ v = ∑ j, w j • Y j := by
  classical
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    refine ⟨Pi.single j 1, fun i hi => ?_, ?_⟩
    · have hij : i ≠ j := fun e => hi (e ▸ hj)
      simp [Pi.single_apply, hij]
    · simp [Pi.single_apply]
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨w, hw, rfl⟩ := hx
    obtain ⟨w', hw', rfl⟩ := hy
    refine ⟨w + w', fun i hi => by simp [hw i hi, hw' i hi], ?_⟩
    simp [add_smul, Finset.sum_add_distrib]
  | smul c x _ hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    refine ⟨c • w, fun i hi => by simp [hw i hi], ?_⟩
    simp [Finset.smul_sum, smul_smul]

theorem sum_mem_of {n : ℕ} (Y : Fin n → Fin r → ℂ) (S : Set (Fin n)) (w : Fin n → ℂ)
    (hw : ∀ j, j ∉ S → w j = 0) : ∑ j, w j • Y j ∈ Submodule.span ℂ (Y '' S) := by
  refine Submodule.sum_mem _ (fun j _ => ?_)
  by_cases hj : j ∈ S
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  · rw [hw j hj, zero_smul]
    exact Submodule.zero_mem _

variable (hG : ∀ a b, cc (G a b) = G b a)
include hG

theorem hC_self_im (v : Fin r → ℂ) : (hermC τ G v v).im = 0 := by
  have hτ : ∀ a b, conj (τ (G a b)) = τ (G b a) := by
    intro a b
    rw [← hG a b]
    first
    | exact (NumberField.IsCMField.complexEmbedding_complexConj τ (G a b)).symm
    | exact (IsCMField.complexEmbedding_complexConj τ (G a b)).symm
    | (simp only [cc]; exact (NumberField.IsCMField.complexEmbedding_complexConj τ (G a b)).symm)
    | (simp [cc])
  have hc : conj (hermC τ G v v) = hermC τ G v v := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hermC, map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [hτ]
    ring
  exact Complex.conj_eq_iff_im.mp hc

theorem gs_exists {n : ℕ} (p : ℕ) (Y : Fin n → Fin r → ℂ) (hind : LinearIndependent ℂ Y)
    (horth : ∀ j k : Fin n, (j : ℕ) < p → p ≤ (k : ℕ) → hermC τ G (Y j) (Y k) = 0)
    (hpos : ∀ w : Fin n → ℂ, (∀ j : Fin n, p ≤ (j : ℕ) → w j = 0) → w ≠ 0 →
      0 < (hermC τ G (∑ j, w j • Y j) (∑ j, w j • Y j)).re)
    (hneg : ∀ w : Fin n → ℂ, (∀ j : Fin n, (j : ℕ) < p → w j = 0) → w ≠ 0 →
      (hermC τ G (∑ j, w j • Y j) (∑ j, w j • Y j)).re < 0) :
    ∃ g : Fin n → Fin r → ℂ,
      (∀ c a : Fin n, hermC τ G (g c) (g a) =
        if c = a then (if (c : ℕ) < p then 1 else -1) else 0) ∧
      (∀ c : Fin n, (c : ℕ) < p → g c ∈ Submodule.span ℂ (Y '' {j | (j : ℕ) < p})) ∧
      (∀ c : Fin n, g c ∈ Submodule.span ℂ (Set.range Y)) ∧
      (∀ j : Fin n, ∃ β : Fin n → ℂ, (∀ c : Fin n, ¬((c : ℕ) < p ↔ (j : ℕ) < p) → β c = 0) ∧
        Y j = ∑ c, β c • g c) := by
  classical
  obtain ⟨ε, hε⟩ : ∃ ε : Fin n → ℂ, ε = fun c : Fin n => (if (c : ℕ) < p then 1 else -1 : ℂ) :=
    ⟨fun c : Fin n => (if (c : ℕ) < p then 1 else -1 : ℂ), rfl⟩
  have hτ : ∀ a b, conj (τ (G a b)) = τ (G b a) := by
    intro a b
    rw [← hG a b]
    first
    | exact (NumberField.IsCMField.complexEmbedding_complexConj τ (G a b)).symm
    | exact (IsCMField.complexEmbedding_complexConj τ (G a b)).symm
    | (simp only [cc]; exact (NumberField.IsCMField.complexEmbedding_complexConj τ (G a b)).symm)
    | (simp [cc])
  have csym : ∀ u w, conj (hermC τ G u w) = hermC τ G w u := by
    intro u w
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hermC, map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [hτ]
    ring
  have smulL : ∀ (c : ℂ) u w, hermC τ G (c • u) w = c * hermC τ G u w := fun c u w =>
    map_smul (hL τ G w) c u
  have subL : ∀ u u' w, hermC τ G (u - u') w = hermC τ G u w - hermC τ G u' w := fun u u' w =>
    map_sub (hL τ G w) u u'
  have sumL : ∀ (s : Finset (Fin n)) (f : Fin n → Fin r → ℂ) w,
      hermC τ G (∑ a ∈ s, f a) w = ∑ a ∈ s, hermC τ G (f a) w := fun s f w =>
    map_sum (hL τ G w) f s
  have smulR : ∀ (c : ℂ) u w, hermC τ G u (c • w) = conj c * hermC τ G u w := by
    intro c u w
    rw [← csym, smulL, map_mul, csym]

  have cross : ∀ a c : Fin n, ¬((a : ℕ) < p ↔ (c : ℕ) < p) →
      ∀ u ∈ Submodule.span ℂ (Y '' {j | ((j : ℕ) < p ↔ (a : ℕ) < p)}),
      ∀ w ∈ Submodule.span ℂ (Y '' {j | ((j : ℕ) < p ↔ (c : ℕ) < p)}), hermC τ G u w = 0 := by
    intro a c hac u hu w hw
    refine perp_span τ G ?_ u hu
    rintro _ ⟨j, hj, rfl⟩
    refine perp_span_right τ G hG ?_ w hw
    rintro _ ⟨k, hk, rfl⟩
    simp only [Set.mem_setOf_eq] at hj hk
    by_cases hjp : (j : ℕ) < p
    · have hkp : p ≤ (k : ℕ) := by
        by_contra hkp
        exact hac ⟨fun _ => hk.mp (not_le.mp hkp), fun _ => hj.mp hjp⟩
      exact horth j k hjp hkp
    · have hkp : (k : ℕ) < p := by
        by_contra hkp
        exact hac ⟨fun ha => absurd (hj.mpr ha) hjp, fun hc => absurd (hk.mpr hc) hkp⟩
      rw [← csym, horth k j hkp (not_lt.mp hjp), map_zero]

  have step : ∀ m : ℕ, m ≤ n → ∃ g : Fin n → Fin r → ℂ,
      (∀ c a : Fin n, (c : ℕ) < m → (a : ℕ) < m → hermC τ G (g c) (g a) = if c = a then ε c else 0) ∧
      (∀ c : Fin n, (c : ℕ) < m →
        g c ∈ Submodule.span ℂ (Y '' {j | (j : ℕ) ≤ c ∧ ((j : ℕ) < p ↔ (c : ℕ) < p)})) ∧
      (∀ j : Fin n, (j : ℕ) < m →
        Y j ∈ Submodule.span ℂ (g '' {c | (c : ℕ) ≤ j ∧ ((c : ℕ) < p ↔ (j : ℕ) < p)})) := by
    intro m
    induction m with
    | zero => exact fun _ => ⟨0, fun c _ h => absurd h (Nat.not_lt_zero _),
        fun c h => absurd h (Nat.not_lt_zero _), fun j h => absurd h (Nat.not_lt_zero _)⟩
    | succ m ih =>
      intro hmn
      obtain ⟨g, horg, hspg, hspY⟩ := ih (Nat.le_of_succ_le hmn)
      set c₀ : Fin n := ⟨m, hmn⟩ with hc₀
      set T : Finset (Fin n) := Finset.univ.filter (fun a : Fin n => (a : ℕ) < m) with hT
      set v : Fin r → ℂ := Y c₀ - ∑ a ∈ T, (ε a * hermC τ G (Y c₀) (g a)) • g a with hv
      have hεsq : ∀ a, ε a * ε a = 1 := by
        intro a
        rw [hε]
        dsimp only
        split_ifs <;> norm_num
      have hvg : ∀ a ∈ T, hermC τ G v (g a) = 0 := by
        intro a ha
        have ham : (a : ℕ) < m := (Finset.mem_filter.mp ha).2
        rw [hv, subL, sumL]
        have : ∀ b ∈ T, hermC τ G ((ε b * hermC τ G (Y c₀) (g b)) • g b) (g a) =
            if b = a then hermC τ G (Y c₀) (g a) else 0 := by
          intro b hb
          rw [smulL, horg b a (Finset.mem_filter.mp hb).2 ham]
          split_ifs with hba
          · rw [hba, mul_comm (ε a), mul_assoc, hεsq, mul_one]
          · rw [mul_zero]
        rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' T a, if_pos ha, sub_self]

      set S₀ : Set (Fin n) := {j | (j : ℕ) ≤ c₀ ∧ ((j : ℕ) < p ↔ (c₀ : ℕ) < p)} with hS₀
      have hgS : ∀ a ∈ T, ((a : ℕ) < p ↔ (c₀ : ℕ) < p) → g a ∈ Submodule.span ℂ (Y '' S₀) := by
        intro a ha hblk
        have ham : (a : ℕ) < m := (Finset.mem_filter.mp ha).2
        refine Submodule.span_mono (Set.image_mono ?_) (hspg a ham)
        rintro j ⟨hj1, hj2⟩
        exact ⟨le_trans hj1 (le_of_lt ham), hj2.trans hblk⟩
      have hcoef0 : ∀ a ∈ T, ¬((a : ℕ) < p ↔ (c₀ : ℕ) < p) → hermC τ G (Y c₀) (g a) = 0 := by
        intro a ha hblk
        have ham : (a : ℕ) < m := (Finset.mem_filter.mp ha).2
        refine cross c₀ a (fun h => hblk h.symm) (Y c₀) (Submodule.subset_span ⟨c₀, Iff.rfl, rfl⟩)
          (g a) (Submodule.span_mono (Set.image_mono ?_) (hspg a ham))
        rintro j ⟨_, hj2⟩
        exact hj2
      have hvS : v ∈ Submodule.span ℂ (Y '' S₀) := by
        rw [hv]
        refine Submodule.sub_mem _ (Submodule.subset_span ⟨c₀, ⟨le_refl _, Iff.rfl⟩, rfl⟩) ?_
        refine Submodule.sum_mem _ (fun a ha => ?_)
        by_cases hblk : ((a : ℕ) < p ↔ (c₀ : ℕ) < p)
        · exact Submodule.smul_mem _ _ (hgS a ha hblk)
        · rw [hcoef0 a ha hblk, mul_zero, zero_smul]
          exact Submodule.zero_mem _
      have hv0 : v ≠ 0 := by
        intro hv0
        have hY : Y c₀ = ∑ a ∈ T, (ε a * hermC τ G (Y c₀) (g a)) • g a := by
          rw [hv] at hv0
          exact sub_eq_zero.mp hv0
        have hin : Y c₀ ∈ Submodule.span ℂ (Y '' {j | (j : ℕ) < m}) := by
          rw [hY]
          refine Submodule.sum_mem _ (fun a ha => Submodule.smul_mem _ _ ?_)
          have ham : (a : ℕ) < m := (Finset.mem_filter.mp ha).2
          refine Submodule.span_mono (Set.image_mono ?_) (hspg a ham)
          rintro j ⟨hj1, _⟩
          exact lt_of_le_of_lt hj1 ham
        have hnot : c₀ ∉ {j : Fin n | (j : ℕ) < m} := by
          simp [hc₀]
        first
        | exact hind.not_mem_span_image hnot hin
        | exact hind.notMem_span_image hnot hin

      have hsign : 0 < (ε c₀ * hermC τ G v v).re := by
        obtain ⟨w, hw, hvw⟩ := coef_of_mem Y S₀ hvS
        have hw0 : w ≠ 0 := by
          rintro rfl
          apply hv0
          rw [hvw]
          simp
        rw [hε]
        dsimp only
        by_cases hcp : (c₀ : ℕ) < p
        · rw [if_pos hcp, one_mul, hvw]
          refine hpos w (fun j hj => hw j ?_) hw0
          rintro ⟨_, hj2⟩
          exact absurd (hj2.mpr hcp) (not_lt.mpr hj)
        · rw [if_neg hcp, hvw]
          have := hneg w (fun j hj => hw j ?_) hw0
          · simp only [neg_mul, one_mul, Complex.neg_re]
            linarith
          · rintro ⟨_, hj2⟩
            exact hcp (hj2.mp hj)
      set t : ℝ := (ε c₀ * hermC τ G v v).re with ht
      have hvv : hermC τ G v v = ε c₀ * (t : ℂ) := by
        have hεc : ε c₀ = 1 ∨ ε c₀ = -1 := by
          rw [hε]
          dsimp only
          split_ifs
          · exact Or.inl rfl
          · exact Or.inr rfl
        have him := hC_self_im τ G hG v
        apply Complex.ext
        · rcases hεc with h | h <;> simp [ht, h]
        · rcases hεc with h | h <;> simp [ht, h, him]
      set s : ℂ := (((Real.sqrt t)⁻¹ : ℝ) : ℂ) with hs
      have hss : s * (conj s * (ε c₀ * (t : ℂ))) = ε c₀ := by
        have hr : ((Real.sqrt t)⁻¹ * ((Real.sqrt t)⁻¹ * t) : ℝ) = 1 := by
          rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt hsign.le, inv_mul_cancel₀ hsign.ne']
        rw [hs, Complex.conj_ofReal]
        have hc : ((Real.sqrt t)⁻¹ : ℂ) * (((Real.sqrt t)⁻¹ : ℂ) * (t : ℂ)) = 1 := by
          exact_mod_cast hr
        calc ((((Real.sqrt t)⁻¹ : ℝ)) : ℂ) * ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) * (ε c₀ * (t : ℂ)))
            = ε c₀ * (((Real.sqrt t)⁻¹ : ℂ) * (((Real.sqrt t)⁻¹ : ℂ) * (t : ℂ))) := by
              push_cast
              ring
          _ = ε c₀ := by rw [hc, mul_one]

      refine ⟨Function.update g c₀ (s • v), ?_, ?_, ?_⟩
      · have hlt : ∀ c : Fin n, (c : ℕ) < m + 1 → c ≠ c₀ → (c : ℕ) < m := by
          intro c hc hne
          have : (c : ℕ) ≠ m := fun h => hne (Fin.ext h)
          omega
        have hTm : ∀ c : Fin n, (c : ℕ) < m → c ∈ T := fun c hc => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
        intro c a hc ha
        by_cases hc0 : c = c₀ <;> by_cases ha0 : a = c₀
        · subst hc0
          subst ha0
          rw [Function.update_self, smulL, smulR, hvv, hss, if_pos rfl]
        · subst hc0
          rw [Function.update_self, Function.update_of_ne ha0, smulL,
            hvg a (hTm a (hlt a ha ha0)), mul_zero, if_neg (Ne.symm ha0)]
        · subst ha0
          rw [Function.update_self, Function.update_of_ne hc0, smulR, ← csym,
            hvg c (hTm c (hlt c hc hc0)), map_zero, mul_zero, if_neg hc0]
        · rw [Function.update_of_ne hc0, Function.update_of_ne ha0]
          exact horg c a (hlt c hc hc0) (hlt a ha ha0)
      · intro c hc
        by_cases hc0 : c = c₀
        · subst hc0
          rw [Function.update_self]
          exact Submodule.smul_mem _ _ hvS
        · rw [Function.update_of_ne hc0]
          have : (c : ℕ) ≠ m := fun h => hc0 (Fin.ext h)
          exact hspg c (by omega)
      · intro j hj
        by_cases hj0 : j = c₀
        · subst hj0
          have hY : Y c₀ = s⁻¹ • (s • v) + ∑ a ∈ T, (ε a * hermC τ G (Y c₀) (g a)) • g a := by
            have hs0 : s ≠ 0 := by
              rw [hs]
              exact_mod_cast (inv_pos.mpr (Real.sqrt_pos.mpr hsign)).ne'
            rw [smul_smul, inv_mul_cancel₀ hs0, one_smul, hv, sub_add_cancel]
          rw [hY]
          refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span
            ⟨c₀, ⟨le_refl _, Iff.rfl⟩, Function.update_self _ _ _⟩)) ?_
          refine Submodule.sum_mem _ (fun a ha => ?_)
          have ham : (a : ℕ) < m := (Finset.mem_filter.mp ha).2
          have hac : a ≠ c₀ := fun h => by rw [h] at ham; exact lt_irrefl _ ham
          by_cases hblk : ((a : ℕ) < p ↔ (c₀ : ℕ) < p)
          · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ⟨le_of_lt ham, hblk⟩, ?_⟩)
            exact Function.update_of_ne hac _ _
          · rw [hcoef0 a ha hblk, mul_zero, zero_smul]
            exact Submodule.zero_mem _
        · have hjm : (j : ℕ) < m := by
            have : (j : ℕ) ≠ m := fun h => hj0 (Fin.ext h)
            omega
          refine Submodule.span_mono ?_ (hspY j hjm)
          rintro _ ⟨c, hc, rfl⟩
          refine ⟨c, hc, ?_⟩
          have hcc : c ≠ c₀ := by
            intro h
            rw [h] at hc
            exact absurd (lt_of_le_of_lt hc.1 hjm) (lt_irrefl _)
          exact Function.update_of_ne hcc _ _
  obtain ⟨g, horg, hspg, hspY⟩ := step n le_rfl
  refine ⟨g, fun c a => ?_, fun c hc => ?_, fun c => ?_, fun j => ?_⟩
  · rw [horg c a c.isLt a.isLt, hε]
  · refine Submodule.span_mono (Set.image_mono ?_) (hspg c c.isLt)
    rintro j ⟨_, hj2⟩
    exact hj2.mpr hc
  · refine Submodule.span_mono (Set.image_subset_range _ _) (hspg c c.isLt)
  · obtain ⟨β, hβ, hYβ⟩ := coef_of_mem g _ (hspY j j.isLt)
    refine ⟨β, fun c hc => hβ c ?_, hYβ⟩
    rintro ⟨_, h2⟩
    exact hc h2

end

end ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary
end

namespace ReciprocityTheory.ChartRestriction.G.FD.EigenframeMatrices

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramSchmidtSelfImaginary
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
  (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {n : ℕ} (p : ℕ) (f g : Fin n → Fin r → ℂ)

def eps (k : Fin n) : ℂ := if (k : ℕ) < p then 1 else -1

def Mmat : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => (if a = b then 1 else 0) +
    ∑ k, (eps p k * (g k - f k) a) * ∑ m, τ (G b m) * conj (f k m)

theorem eps_sq (k : Fin n) : eps p k * eps p k = 1 := by
  unfold eps
  split_ifs <;> norm_num

theorem Mmat_mulVec (v : Fin r → ℂ) :
    Mmat τ G p f g *ᵥ v = v + ∑ k, (eps p k * hermC τ G v (f k)) • (g k - f k) := by
  ext a
  simp only [Matrix.mulVec, dotProduct, Mmat, Matrix.of_apply, add_mul, Finset.sum_add_distrib, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.add_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, hermC, Pi.sub_apply]
  congr 1
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun m _ => ?_
  ring

private lemma hermC_add_left' (u u' v : Fin r → ℂ) :
    hermC τ G (u + u') v = hermC τ G u v + hermC τ G u' v := by
  unfold hermC
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma hermC_add_right_fundamental_domains' (u v v' : Fin r → ℂ) :
    hermC τ G u (v + v') = hermC τ G u v + hermC τ G u v' := by
  unfold hermC
  simp only [Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

private lemma hermC_sum_smul_left {m : ℕ} (c : Fin m → ℂ) (q : Fin m → Fin r → ℂ) (v : Fin r → ℂ) :
    hermC τ G (∑ k, c k • q k) v = ∑ k, c k * hermC τ G (q k) v := by
  unfold hermC
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  calc _ = ∑ a, ∑ k, ∑ b, c k * q k a * τ (G a b) * conj (v b) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ k, ∑ a, ∑ b, c k * q k a * τ (G a b) * conj (v b) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => ?_
        ring

private lemma hermC_sum_smul_right {m : ℕ} (u : Fin r → ℂ) (d : Fin m → ℂ) (q : Fin m → Fin r → ℂ) :
    hermC τ G u (∑ l, d l • q l) = ∑ l, conj (d l) * hermC τ G u (q l) := by
  unfold hermC
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]
  calc _ = ∑ a, ∑ l, ∑ b, u a * τ (G a b) * (conj (d l) * conj (q l b)) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ l, ∑ a, ∑ b, u a * τ (G a b) * (conj (d l) * conj (q l b)) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => ?_
        ring

theorem expand (q : Fin n → Fin r → ℂ) (x y : Fin r → ℂ) (c d : Fin n → ℂ)
    (hx : ∀ l, hermC τ G x (q l) = 0) (hy : ∀ k, hermC τ G (q k) y = 0) :
    hermC τ G (x + ∑ k, c k • q k) (y + ∑ l, d l • q l) =
      hermC τ G x y + ∑ k, ∑ l, c k * conj (d l) * hermC τ G (q k) (q l) := by
  rw [hermC_add_left', hermC_add_right_fundamental_domains', hermC_add_right_fundamental_domains']
  simp only [hermC_sum_smul_right, hermC_sum_smul_left, hx, hy, mul_zero, Finset.sum_const_zero, add_zero,
    Finset.mul_sum]
  rw [zero_add, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

variable (hG : ∀ a b, cc (G a b) = G b a)
  (hf : ∀ k l, hermC τ G (f k) (f l) = if k = l then (if (k : ℕ) < p then 1 else -1) else 0)
include hG hf

theorem hf_eps (k l : Fin n) : hermC τ G (f k) (f l) = if k = l then eps p k else 0 := by
  rw [hf]
  rfl

theorem Mmat_f (l : Fin n) : Mmat τ G p f g *ᵥ f l = g l := by
  rw [Mmat_mulVec]
  simp only [hf_eps τ G p f hG hf, mul_ite, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, eps_sq, one_smul]
  abel

theorem Mmat_fix (v : Fin r → ℂ) (hv : ∀ k, hermC τ G v (f k) = 0) : Mmat τ G p f g *ᵥ v = v := by
  rw [Mmat_mulVec]
  simp [hv]

theorem Mmat_comb (β : Fin n → ℂ) : Mmat τ G p f g *ᵥ (∑ c, β c • f c) = ∑ c, β c • g c := by
  rw [Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.mulVec_smul, Mmat_f τ G p f g hG hf]

private lemma hermC_eq_conj_hermC_swap (u v : Fin r → ℂ) : hermC τ G u v = conj (hermC τ G v u) := by
  unfold hermC
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hG i j]
  simp only [cc, IsCMField.complexEmbedding_complexConj]
  ring

theorem Mmat_unitary (hgf : ∀ k, g k ∈ Submodule.span ℂ (Set.range f))
    (hg : ∀ k l, hermC τ G (g k) (g l) = if k = l then (if (k : ℕ) < p then 1 else -1) else 0)
    (v w : Fin r → ℂ) :
    hermC τ G (Mmat τ G p f g *ᵥ v) (Mmat τ G p f g *ᵥ w) = hermC τ G v w := by
  have hconj : ∀ u u', hermC τ G u u' = conj (hermC τ G u' u) := hermC_eq_conj_hermC_swap τ G p f hG hf
  have hdec : ∀ u : Fin r → ℂ, ∃ (x : Fin r → ℂ) (cu : Fin n → ℂ),
      u = x + ∑ k, cu k • f k ∧ ∀ l, hermC τ G x (f l) = 0 := by
    intro u
    refine ⟨u + ∑ k, (-(eps p k * hermC τ G u (f k))) • f k, fun k => eps p k * hermC τ G u (f k), ?_,
      fun l => ?_⟩
    · simp only [neg_smul, Finset.sum_neg_distrib]
      abel
    · rw [hermC_add_left', hermC_sum_smul_left]
      simp only [hf_eps τ G p f hG hf, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      linear_combination (-hermC τ G u (f l)) * eps_sq p l
  have hperp : ∀ x : Fin r → ℂ, (∀ l, hermC τ G x (f l) = 0) → ∀ k, hermC τ G x (g k) = 0 := by
    intro x hx k
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℂ)).mp (hgf k)
    rw [← ha, hermC_sum_smul_right]
    simp [hx]
  obtain ⟨xv, cv, hv, hxv⟩ := hdec v
  obtain ⟨xw, cw, hw, hxw⟩ := hdec w
  have hMv : Mmat τ G p f g *ᵥ v = xv + ∑ k, cv k • g k := by
    rw [hv, Matrix.mulVec_add, Mmat_fix τ G p f g hG hf xv hxv, Mmat_comb τ G p f g hG hf]
  have hMw : Mmat τ G p f g *ᵥ w = xw + ∑ k, cw k • g k := by
    rw [hw, Matrix.mulVec_add, Mmat_fix τ G p f g hG hf xw hxw, Mmat_comb τ G p f g hG hf]
  rw [hMv, hMw, hv, hw]
  rw [expand τ G g xv xw cv cw (hperp xv hxv) (fun k => by rw [hconj, hperp xw hxw k, map_zero]),
    expand τ G f xv xw cv cw hxv (fun k => by rw [hconj, hxw k, map_zero])]
  simp only [hg, hf]

theorem Mmat_span (hgf : ∀ k, g k ∈ Submodule.span ℂ (Set.range f)) (v : Fin r → ℂ)
    (hv : v ∈ Submodule.span ℂ (Set.range f)) :
    Mmat τ G p f g *ᵥ v ∈ Submodule.span ℂ (Set.range f) := by
  rw [Mmat_mulVec]
  exact Submodule.add_mem _ hv (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
    (Submodule.sub_mem _ (hgf k) (Submodule.subset_span ⟨k, rfl⟩)))

end

end ReciprocityTheory.ChartRestriction.G.FD.EigenframeMatrices
end

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Matrix
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

private theorem hermC_sub_left_eq_sub {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (u u' v : Fin r → ℂ) : hermC τ G (u - u') v = hermC τ G u v - hermC τ G u' v :=
  map_sub (AddMonoidHom.mk' (fun x => hermC τ G x v) (fun a b => hermC_add_left τ G a b v)) u u'

private theorem hermC_finset_sum_left' {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    {ι : Type} (s : Finset ι) (u : ι → Fin r → ℂ) (v : Fin r → ℂ) :
    hermC τ G (∑ i ∈ s, u i) v = ∑ i ∈ s, hermC τ G (u i) v :=
  map_sum (AddMonoidHom.mk' (fun x => hermC τ G x v) (fun a b => hermC_add_left τ G a b v)) u s

private theorem hermC_finset_sum_right_of_conj_symm {r : ℕ} (τ : E →+* ℂ) {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, cc (G a b) = G b a) {ι : Type} (s : Finset ι) (u : Fin r → ℂ)
    (v : ι → Fin r → ℂ) : hermC τ G u (∑ i ∈ s, v i) = ∑ i ∈ s, hermC τ G u (v i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hermC_conj τ hG _ u, hermC_finset_sum_left', map_sum]
  exact Finset.sum_congr rfl (fun i _ => hermC_conj τ hG _ _)

private theorem hermC_sub_right_of_conj_symm {r : ℕ} (τ : E →+* ℂ) {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, cc (G a b) = G b a) (u v v' : Fin r → ℂ) :
    hermC τ G u (v - v') = hermC τ G u v - hermC τ G u v' := by
  rw [← hermC_conj τ hG _ u, hermC_sub_left_eq_sub, map_sub, hermC_conj τ hG, hermC_conj τ hG]

private theorem ppos_self_adjoint_hermC {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ)
    (w v : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.ppos x τ w) v = hermC τ.1 X.Gm w (X.ppos x τ v) := by
  have hH : (X.gramPos x τ).IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Data.gramPos, Matrix.submatrix_apply, gram,
      Matrix.of_apply]
    rw [← starRingEnd_apply]
    exact hermC_conj _ X.Gm_herm _ _
  have hM := hH.inv
  simp only [Data.ppos]
  rw [hermC_finset_sum_left', hermC_finset_sum_right_of_conj_symm _ X.Gm_herm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermC_smul_left, hermC_smul_right, Finset.sum_mul, map_sum, map_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [hermC_conj _ X.Gm_herm, starRingEnd_apply, hM.apply]
  ring

private theorem hermC_ppos_eq_zero_of_hermC_eq_zero_of_Jt {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ)
    (w v : Fin r → ℂ) (h0 : hermC τ.1 X.Gm w v = 0) (hJ : hermC τ.1 X.Gm w (X.Jt x τ v) = 0) :
    hermC τ.1 X.Gm w (X.ppos x τ v) = 0 := by
  simp only [Data.Jt] at hJ
  rw [hermC_smul_right, hermC_sub_right_of_conj_symm _ X.Gm_herm, hermC_smul_right, h0] at hJ
  simpa using hJ

theorem gramSchmidt_eigenframe (r : ℕ) (X : DataX E r) (ξ : Fin r → E) (z0 : Frame X.Ψ r)
    (f Y : X.Ψ → Fin (r - 2) → Fin r → ℂ) (hξ : X.IsIso ξ) (hz : z0 ∈ X.dom) (hf : X.UBasis z0 ξ f)
    (hYind : ∀ τ, LinearIndependent ℂ (Y τ))
    (hYU : ∀ τ j, Y τ j ∈ Submodule.span ℂ (Set.range (f τ)))
    (hYorth : ∀ τ (j k : Fin (r - 2)), (j : ℕ) < X.p0 - 1 → X.p0 - 1 ≤ (k : ℕ) →
      hermC τ.1 X.Gm (Y τ j) (Y τ k) = 0)
    (hYpos : ∀ τ (w : Fin (r - 2) → ℂ), (∀ j : Fin (r - 2), X.p0 - 1 ≤ (j : ℕ) → w j = 0) → w ≠ 0 →
      0 < (hermC τ.1 X.Gm (∑ j, w j • Y τ j) (∑ j, w j • Y τ j)).re)
    (hYneg : ∀ τ (w : Fin (r - 2) → ℂ), (∀ j : Fin (r - 2), (j : ℕ) < X.p0 - 1 → w j = 0) → w ≠ 0 →
      (hermC τ.1 X.Gm (∑ j, w j • Y τ j) (∑ j, w j • Y τ j)).re < 0) :
    ∃ h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ, X.IsUnitaryC h1 ∧
      (∀ s t : X.Ψ → ℂ, X.applyV h1 (X.lineV ξ s + X.Jz z0 (X.lineV ξ t)) =
        X.lineV ξ s + X.Jz z0 (X.lineV ξ t)) ∧
      (∀ u ∈ X.Uz z0 ξ, X.applyV h1 u ∈ X.Uz z0 ξ) ∧
      (∀ τ (v : Fin r → ℂ), v ∈ Submodule.span ℂ (f τ '' {k | (k : ℕ) < X.p0 - 1}) →
        (h1 τ) *ᵥ v ∈ Submodule.span ℂ (Y τ '' {j | (j : ℕ) < X.p0 - 1})) ∧
      (∀ τ (j : Fin (r - 2)), ∃ u : Fin r → ℂ,
        u ∈ Submodule.span ℂ (f τ '' {k | ((k : ℕ) < X.p0 - 1 ↔ (j : ℕ) < X.p0 - 1)}) ∧ (h1 τ) *ᵥ u = Y τ j) := by
  have hgs := fun τ : X.Ψ => GramSchmidtSelfImaginary.gs_exists (τ := τ.1) (G := X.Gm) (p := X.p0 - 1) (Y := Y τ)
    (hind := hYind τ) (horth := hYorth τ) (hpos := hYpos τ) (hneg := hYneg τ) X.Gm_herm
  choose g hg1 hg2 hg3 hg4 using hgs
  have hgf : ∀ τ k, g τ k ∈ Submodule.span ℂ (Set.range (f τ)) := by
    intro τ k
    have hsub : Submodule.span ℂ (Set.range (Y τ)) ≤ Submodule.span ℂ (Set.range (f τ)) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hYU τ j
    exact hsub (hg3 τ k)
  have e0 : ∀ τ : X.Ψ, ∀ k, hermC τ.1 X.Gm (Data.emb τ.1 ξ) (f τ k) = 0 := fun τ k => by
    rw [← hermC_conj τ.1 X.Gm_herm, ((hf τ).1 k).1, map_zero]
  have eP : ∀ τ : X.Ψ, ∀ k, hermC τ.1 X.Gm (Data.emb τ.1 ξ) (X.ppos z0 τ (f τ k)) = 0 := fun τ k => by
    refine hermC_ppos_eq_zero_of_hermC_eq_zero_of_Jt X.toData z0 τ _ _ (e0 τ k) ?_
    rw [(hf τ).2.1 k, hermC_smul_right, e0 τ k, mul_zero]
  have hspan : ∀ τ : X.Ψ, ∀ y ∈ Submodule.span ℂ (Set.range (f τ)),
      hermC τ.1 X.Gm y (Data.emb τ.1 ξ) = 0 ∧ hermC τ.1 X.Gm y (X.ppos z0 τ (Data.emb τ.1 ξ)) = 0 := by
    intro τ y hy
    refine ⟨GramSchmidtSelfImaginary.perp_span (τ := τ.1) (G := X.Gm) ?_ y hy,
      GramSchmidtSelfImaginary.perp_span (τ := τ.1) (G := X.Gm) ?_ y hy⟩
    · rintro _ ⟨k, rfl⟩
      exact ((hf τ).1 k).1
    · rintro _ ⟨k, rfl⟩
      rw [← ppos_self_adjoint_hermC, ← hermC_conj τ.1 X.Gm_herm, eP τ k, map_zero]
  have hJspan : ∀ τ : X.Ψ, ∀ y ∈ Submodule.span ℂ (Set.range (f τ)),
      hermC τ.1 X.Gm (I • ((2 : ℂ) • X.ppos z0 τ y - y)) (Data.emb τ.1 ξ) = 0 := by
    intro τ y hy
    rw [hermC_smul_left, hermC_sub_left_eq_sub, hermC_smul_left, ppos_self_adjoint_hermC, (hspan τ y hy).1,
      (hspan τ y hy).2]
    simp
  refine ⟨fun τ => EigenframeMatrices.Mmat (τ := τ.1) (G := X.Gm) (p := X.p0 - 1) (f := f τ) (g := g τ),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro τ u w
    exact EigenframeMatrices.Mmat_unitary (τ := τ.1) (G := X.Gm) (p := X.p0 - 1) (f := f τ) (g := g τ) (hG := X.Gm_herm)
      (hf := (hf τ).2.2.1)
      (hgf τ) (hg1 τ) u w
  · intro s t
    funext τ
    simp only [Data.applyV]
    refine EigenframeMatrices.Mmat_fix (τ := τ.1) (G := X.Gm) (p := X.p0 - 1) (f := f τ) (g := g τ) (hG := X.Gm_herm)
      (hf := (hf τ).2.2.1) _
      (fun k => ?_)
    simp only [Pi.add_apply, Data.lineV, Data.Jz]
    simp only [hermC_add_left, hermC_smul_left, hermC_sub_left_eq_sub, ppos_self_adjoint_hermC, e0, eP,
      mul_zero, sub_zero, add_zero, zero_add]
  · intro u hu
    obtain ⟨hu1, hu2⟩ := hu
    have hmem : ∀ τ : X.Ψ, EigenframeMatrices.Mmat (τ := τ.1) (G := X.Gm) (p := X.p0 - 1) (f := f τ)
        (g := g τ) *ᵥ u τ ∈ Submodule.span ℂ (Set.range (f τ)) := fun τ =>
      EigenframeMatrices.Mmat_span (τ := τ.1) (G := X.Gm) (p := X.p0 - 1) (f := f τ) (g := g τ) (hG := X.Gm_herm)
      (hf := (hf τ).2.2.1) (hgf τ)
        (u τ) ((hf τ).2.2.2.2 (u τ) (hu1 τ) (hu2 τ))
    exact And.intro (fun τ => (hspan τ _ (hmem τ)).1) (fun τ => hJspan τ _ (hmem τ))
  · intro τ v hv
    have hle : Submodule.span ℂ (f τ '' {k | (k : ℕ) < X.p0 - 1}) ≤
        (Submodule.span ℂ (Y τ '' {j | (j : ℕ) < X.p0 - 1})).comap
          (Matrix.mulVecLin (EigenframeMatrices.Mmat (τ := τ.1) (G := X.Gm) (p := X.p0 - 1) (f := f τ)
            (g := g τ))) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, hk, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply,
        EigenframeMatrices.Mmat_f (τ := τ.1) (G := X.Gm) (p := X.p0 - 1) (f := f τ) (g := g τ) (hG := X.Gm_herm)
      (hf := (hf τ).2.2.1)]
      exact hg2 τ k hk
    have hv' := hle hv
    rwa [Submodule.mem_comap, Matrix.mulVecLin_apply] at hv'
  · intro τ j
    obtain ⟨β, hβ, hYj⟩ := hg4 τ j
    refine ⟨∑ c, β c • f τ c, GramSchmidtSelfImaginary.sum_mem_of (f τ) _ β hβ, ?_⟩
    show EigenframeMatrices.Mmat (τ := τ.1) (G := X.Gm) (p := X.p0 - 1) (f := f τ) (g := g τ) *ᵥ
      (∑ c, β c • f τ c) = Y τ j
    rw [EigenframeMatrices.Mmat_comb (τ := τ.1) (G := X.Gm) (p := X.p0 - 1) (f := f τ) (g := g τ) (hG := X.Gm_herm)
      (hf := (hf τ).2.2.1), hYj]

end

end ReciprocityTheory.ChartRestriction.G.FD
