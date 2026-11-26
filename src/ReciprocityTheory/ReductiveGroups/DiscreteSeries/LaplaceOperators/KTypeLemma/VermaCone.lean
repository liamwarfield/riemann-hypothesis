module

public import Lemmata.SmulListSum.SmulListSum
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.ConeNorm

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.VermaConeC
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.VermaConeB
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.VermaConeA
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

section Core

variable {n : ℕ} {U : Type*} [AddCommGroup U] [Module ℂ U]

theorem vc_le_genSub (T : Fin n → Fin n → Module.End ℂ U) (S : Submodule ℂ U) : S ≤ genSub T S := by
  unfold genSub
  exact le_sInf fun X hX => hX.1

theorem vc_genSub_stable (T : Fin n → Fin n → Module.End ℂ U) (S : Submodule ℂ U) (a b : Fin n) {v : U}
    (hv : v ∈ genSub T S) : T a b v ∈ genSub T S := by
  unfold genSub at hv ⊢
  rw [Submodule.mem_sInf] at hv ⊢
  intro X hX
  exact hX.2 a b v (hv X hX)

theorem vc_genSub_le (T : Fin n → Fin n → Module.End ℂ U) (S X : Submodule ℂ U) (hSX : S ≤ X)
    (hX : ∀ a b, ∀ v ∈ X, T a b v ∈ X) : genSub T S ≤ X := by
  unfold genSub
  exact sInf_le ⟨hSX, hX⟩

def vcGood (T : Fin n → Fin n → Module.End ℂ U) (P : (Fin n → ℝ) → Prop) : Set U :=
  {w | ∃ ν, P ν ∧ ∀ a, T a a w = ((ν a : ℝ) : ℂ) • w}

theorem vcGood_smul (T : Fin n → Fin n → Module.End ℂ U) (P : (Fin n → ℝ) → Prop) {w : U}
    (hw : w ∈ vcGood T P) (c : ℂ) : c • w ∈ vcGood T P := by
  simp only [vcGood, Set.mem_setOf_eq] at hw ⊢
  obtain ⟨ν, hP, hν⟩ := hw
  refine ⟨ν, hP, fun a => ?_⟩
  rw [map_smul, hν a, smul_comm]

theorem vc_exists_list {G : Set U} (hs : ∀ w ∈ G, ∀ c : ℂ, c • w ∈ G) {y : U}
    (hy : y ∈ Submodule.span ℂ G) : ∃ l : List U, (∀ w ∈ l, w ∈ G) ∧ y = l.sum := by
  first | exact Bl.SmulListSum.goal1 .. | (apply Bl.SmulListSum.goal1 <;> assumption) | (intros; apply Bl.SmulListSum.goal1 <;> assumption)

theorem vc_eq_zero_of_list (T : Fin n → Fin n → Module.End ℂ U) (P : (Fin n → ℝ) → Prop)
    {μ : Fin n → ℝ} (hμ : ¬ P μ) :
    ∀ (N : ℕ) (l : List U), l.length = N → (∀ w ∈ l, w ∈ vcGood T P) → ∀ x : U,
      (∀ a, T a a x = ((μ a : ℝ) : ℂ) • x) → x = l.sum → x = 0 := by
  intro N
  induction N with
  | zero =>
    intro l hl _ x _ hxl
    cases l with
    | nil => simpa using hxl
    | cons w l' => simp at hl
  | succ N ih =>
    intro l hl hg x hx hxl
    cases l with
    | nil => simp at hl
    | cons w l' =>
      have hl' : l'.length = N := by simpa using hl
      have hw0 := hg w (by simp)
      simp only [vcGood, Set.mem_setOf_eq] at hw0
      obtain ⟨ν, hPν, hν⟩ := hw0
      have hne : ν ≠ μ := fun h => hμ (h ▸ hPν)
      obtain ⟨a, ha⟩ := Function.ne_iff.mp hne
      have hc0 : ((μ a : ℝ) : ℂ) - ((ν a : ℝ) : ℂ) ≠ 0 :=
        sub_ne_zero.mpr (by exact_mod_cast ha.symm)
      obtain ⟨D, hD⟩ : ∃ D : Module.End ℂ U, ∀ u, D u = T a a u - ((ν a : ℝ) : ℂ) • u :=
        ⟨T a a - ((ν a : ℝ) : ℂ) • 1, fun u => by simp⟩
      have h1 : D x = (((μ a : ℝ) : ℂ) - ((ν a : ℝ) : ℂ)) • x := by
        rw [hD, hx a, sub_smul]
      have h2 : D w = 0 := by rw [hD, hν a, sub_self]
      have h3 : D x = (l'.map D).sum := by
        rw [hxl, List.sum_cons, map_add (f := _), h2, zero_add, map_list_sum]
      have hgood : ∀ u ∈ l'.map D, u ∈ vcGood T P := by
        intro u hu
        obtain ⟨u0, hu0, rfl⟩ := List.mem_map.mp hu
        have hg0 := hg u0 (by simp [hu0])
        simp only [vcGood, Set.mem_setOf_eq] at hg0 ⊢
        obtain ⟨ν', hP', hν'⟩ := hg0
        refine ⟨ν', hP', fun b => ?_⟩
        rw [hD, hν' a, ← sub_smul, map_smul, hν' b, smul_comm]
      have hwt : ∀ b, T b b ((((μ a : ℝ) : ℂ) - ((ν a : ℝ) : ℂ)) • x)
          = ((μ b : ℝ) : ℂ) • ((((μ a : ℝ) : ℂ) - ((ν a : ℝ) : ℂ)) • x) := by
        intro b
        rw [map_smul, hx b, smul_comm]
      have hz := ih (l'.map D) (by simpa using hl') hgood _ hwt (by rw [← h1, h3])
      exact (smul_eq_zero.mp hz).resolve_left hc0

theorem vc_eq_zero_of_mem_span (T : Fin n → Fin n → Module.End ℂ U) (P : (Fin n → ℝ) → Prop)
    {μ : Fin n → ℝ} (hμ : ¬ P μ) {x : U} (hx : ∀ a, T a a x = ((μ a : ℝ) : ℂ) • x)
    (hxs : x ∈ Submodule.span ℂ (vcGood T P)) : x = 0 := by
  obtain ⟨l, hl, e⟩ := vc_exists_list (fun w hw c => vcGood_smul T P hw c) hxs
  exact vc_eq_zero_of_list T P hμ l.length l rfl hl x hx e

def vcMon (T : Fin n → Fin n → Module.End ℂ U) (v : U) : ℕ → Set U
  | 0 => {v}
  | k + 1 => {y | ∃ a b, a < b ∧ ∃ x ∈ vcMon T v k, y = T a b x}

def vcMonAll (T : Fin n → Fin n → Module.End ℂ U) (v : U) : Set U := ⋃ k, vcMon T v k

def vcHt (β : Fin n → ℝ) : ℝ := ∑ a : Fin n, -((a : ℕ) : ℝ) * β a

theorem vcHt_add (β γ : Fin n → ℝ) : vcHt (β + γ) = vcHt β + vcHt γ := by
  simp only [vcHt, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem vcHt_zero : vcHt (0 : Fin n → ℝ) = 0 := by
  simp [vcHt]

theorem vcHt_root {c d : Fin n} (h : c < d) : 1 ≤ vcHt (root c d) := by
  have h1 : ∀ e : Fin n, ∑ a : Fin n, -((a : ℕ) : ℝ) * (Pi.single e (1 : ℝ) : Fin n → ℝ) a
      = -((e : ℕ) : ℝ) := by
    intro e
    rw [Fintype.sum_eq_single e (fun a ha => by simp [Pi.single_apply, ha])]
    simp
  have key : vcHt (root c d) = ((d : ℕ) : ℝ) - ((c : ℕ) : ℝ) := by
    simp only [vcHt, root, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, h1]
    ring
  rw [key]
  have h' : (c : ℕ) + 1 ≤ (d : ℕ) := h
  have h'' : ((c : ℕ) : ℝ) + 1 ≤ ((d : ℕ) : ℝ) := by exact_mod_cast h'
  linarith

theorem vc_inRootCone_zero' : InRootCone (0 : Fin n → ℝ) := by
  unfold InRootCone
  exact ⟨fun _ _ => 0, by simp⟩

theorem vc_inRootCone_add_root {β : Fin n → ℝ} (hβ : InRootCone β) {c d : Fin n} (h : c < d) :
    InRootCone (β + root c d) := by
  unfold InRootCone at hβ ⊢
  obtain ⟨m, hm⟩ := hβ
  refine ⟨fun a b => m a b + if a = c ∧ b = d then 1 else 0, ?_⟩
  have hsplit : ∀ a b : Fin n,
      (if a < b then (((m a b + if a = c ∧ b = d then 1 else 0 : ℕ)) : ℝ) • root a b else 0)
        = (if a < b then (m a b : ℝ) • root a b else 0)
          + (if a = c ∧ b = d then root c d else 0) := by
    intro a b
    by_cases hab : a = c ∧ b = d
    · obtain ⟨rfl, rfl⟩ := hab
      simp [h, add_smul]
    · rw [if_neg hab, if_neg hab]
      simp
  have hind : (∑ a : Fin n, ∑ b : Fin n, (if a = c ∧ b = d then root c d else 0)) = root c d := by
    rw [Finset.sum_eq_single c (fun a _ ha => by simp [ha]) (by simp)]
    rw [Finset.sum_eq_single d (fun b _ hb => by simp [hb]) (by simp)]
    simp
  rw [hm]
  simp only [hsplit, Finset.sum_add_distrib, hind]

theorem vcMon_weight (T : Fin n → Fin n → Module.End ℂ U) (hT : IsGlRep T) {v : U}
    {base : Fin n → ℝ} (hv : ∀ a, T a a v = ((base a : ℝ) : ℂ) • v) :
    ∀ k, ∀ w ∈ vcMon T v k, ∃ ν : Fin n → ℝ, (∀ a, T a a w = ((ν a : ℝ) : ℂ) • w) ∧
      InRootCone (ν - base) ∧ (k : ℝ) ≤ vcHt (ν - base) := by
  have hz : ∀ w, w ∈ vcMon T v 0 → w = v := fun w hw => hw
  have hs : ∀ k w, w ∈ vcMon T v (k + 1) → ∃ a b, a < b ∧ ∃ x ∈ vcMon T v k, w = T a b x :=
    fun k w hw => hw
  intro k
  induction k with
  | zero =>
    intro w hw
    rw [hz w hw]
    refine ⟨base, hv, ?_, ?_⟩
    · rw [sub_self]
      exact vc_inRootCone_zero'
    · rw [sub_self, vcHt_zero]
      simp
  | succ k ih =>
    intro w hw
    obtain ⟨a, b, hab', x, hx, rfl⟩ := hs k w hw
    obtain ⟨ν, hxν, hcone, hht⟩ := ih x hx
    have hab : a ≠ b := ne_of_lt hab'
    have hw : ∀ c, T c c (T a b x) = (((ν + root a b) c : ℝ) : ℂ) • T a b x := by
      intro c
      have hc := LinearMap.congr_fun (hT c c a b) x
      have e : (T c c * T a b - T a b * T c c) x = T c c (T a b x) - T a b (T c c x) := by
        first
          | rfl
          | simp [LinearMap.sub_apply, Module.End.mul_apply]
          | simp [LinearMap.sub_apply, LinearMap.mul_apply]
      rw [e, hxν c, map_smul] at hc
      simp only [root, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
      by_cases h1 : c = a
      · have h2 : ¬ b = c := by
          rw [h1]
          exact fun h => hab h.symm
        rw [if_pos h1, if_neg h2, sub_zero] at hc
        rw [h1] at hc ⊢
        rw [if_pos rfl, if_neg hab, sub_zero, Complex.ofReal_add, Complex.ofReal_one, add_smul,
          one_smul]
        rw [sub_eq_iff_eq_add] at hc
        rw [hc, add_comm]
      · by_cases h3 : c = b
        · have h2 : b = c := h3.symm
          rw [if_neg h1, if_pos h2, zero_sub] at hc
          rw [h3] at hc ⊢
          rw [if_neg (Ne.symm hab), if_pos rfl, zero_sub, ← sub_eq_add_neg, Complex.ofReal_sub,
            Complex.ofReal_one, sub_smul, one_smul]
          rw [LinearMap.neg_apply, sub_eq_iff_eq_add] at hc
          rw [hc, neg_add_eq_sub]
        · have h2 : ¬ b = c := fun h => h3 h.symm
          rw [if_neg h1, if_neg h2, sub_zero, LinearMap.zero_apply, sub_eq_zero] at hc
          rw [if_neg h1, if_neg h3, sub_zero, add_zero, hc]
    have e : ν + root a b - base = (ν - base) + root a b := by abel
    refine ⟨ν + root a b, hw, ?_, ?_⟩
    · rw [e]
      exact vc_inRootCone_add_root hcone hab'
    · rw [e, vcHt_add]
      have := vcHt_root hab'
      push_cast
      linarith

theorem vc_sup_stable {G : Set U} {F : Submodule ℂ U} (X : Module.End ℂ U)
    (hG : ∀ w ∈ G, X w ∈ Submodule.span ℂ G ⊔ F) (hF : ∀ x ∈ F, X x ∈ F) :
    ∀ x ∈ Submodule.span ℂ G ⊔ F, X x ∈ Submodule.span ℂ G ⊔ F := by
  intro x hx
  have h : Submodule.span ℂ G ⊔ F ≤ (Submodule.span ℂ G ⊔ F).comap X := by
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      intro w hw
      exact hG w hw
    · intro y hy
      exact Submodule.mem_sup_right (hF y hy)
  exact h hx

theorem vc_genSub_le_mon (T : Fin n → Fin n → Module.End ℂ U) (hT : IsGlRep T) (v : U)
    (F : Submodule ℂ U) (hF : ∀ a b, ∀ x ∈ F, T a b x ∈ F) (hlow : ∀ a b, b < a → T a b v ∈ F)
    (hdiag : ∀ a, ∃ c : ℂ, T a a v = c • v) :
    genSub T (Submodule.span ℂ {v}) ≤ Submodule.span ℂ (vcMonAll T v) ⊔ F := by
  have hz : ∀ w, w ∈ vcMon T v 0 → w = v := fun w hw => hw
  have hv0 : v ∈ vcMon T v 0 := by
    show v ∈ ({v} : Set U)
    exact Set.mem_singleton v
  have hs : ∀ k w, w ∈ vcMon T v (k + 1) → ∃ a b, a < b ∧ ∃ x ∈ vcMon T v k, w = T a b x :=
    fun k w hw => hw
  have hn : ∀ k a b, a < b → ∀ x ∈ vcMon T v k, T a b x ∈ vcMon T v (k + 1) := by
    intro k a b hab x hx
    show ∃ a' b', a' < b' ∧ ∃ y ∈ vcMon T v k, T a b x = T a' b' y
    exact ⟨a, b, hab, x, hx, rfl⟩
  have hmon : ∀ k, ∀ w ∈ vcMon T v k, w ∈ Submodule.span ℂ (vcMonAll T v) ⊔ F := by
    intro k w hw
    refine Submodule.mem_sup_left (Submodule.subset_span ?_)
    show w ∈ ⋃ k, vcMon T v k
    exact Set.mem_iUnion.mpr ⟨k, hw⟩
  have hup : ∀ c d, c < d → ∀ y ∈ Submodule.span ℂ (vcMonAll T v) ⊔ F,
      T c d y ∈ Submodule.span ℂ (vcMonAll T v) ⊔ F := by
    intro c d hcd
    refine vc_sup_stable (T c d) ?_ (hF c d)
    intro w hw
    obtain ⟨k, hk⟩ : ∃ k, w ∈ vcMon T v k := by simpa [vcMonAll] using hw
    exact hmon (k + 1) _ (hn k c d hcd w hk)
  have hstab : ∀ k, ∀ a b, ∀ w ∈ vcMon T v k,
      T a b w ∈ Submodule.span ℂ (vcMonAll T v) ⊔ F := by
    intro k
    induction k with
    | zero =>
      intro a b w hw
      rw [hz w hw]
      rcases lt_trichotomy a b with h | h | h
      · exact hmon 1 _ (hn 0 a b h v hv0)
      · rw [h]
        obtain ⟨c, hc⟩ := hdiag b
        rw [hc]
        exact Submodule.smul_mem _ c (hmon 0 v hv0)
      · exact Submodule.mem_sup_right (hlow a b h)
    | succ k ih =>
      intro a b w hw
      obtain ⟨c, d, hcd, x, hx, rfl⟩ := hs k w hw
      have hc := LinearMap.congr_fun (hT a b c d) x
      have e : (T a b * T c d - T c d * T a b) x = T a b (T c d x) - T c d (T a b x) := by
        first
          | rfl
          | simp [LinearMap.sub_apply, Module.End.mul_apply]
          | simp [LinearMap.sub_apply, LinearMap.mul_apply]
      rw [e, sub_eq_iff_eq_add] at hc
      rw [hc]
      refine Submodule.add_mem _ ?_ (hup c d hcd _ (ih a b x hx))
      rw [LinearMap.sub_apply]
      refine Submodule.sub_mem _ ?_ ?_
      · split_ifs
        · exact ih a d x hx
        · rw [LinearMap.zero_apply]
          exact Submodule.zero_mem _
      · split_ifs
        · exact ih c b x hx
        · rw [LinearMap.zero_apply]
          exact Submodule.zero_mem _
  refine vc_genSub_le T (Submodule.span ℂ {v}) _ ?_ ?_
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hmon 0 v hv0
  · intro a b y hy
    refine vc_sup_stable (T a b) ?_ (hF a b) y hy
    intro w hw
    obtain ⟨k, hk⟩ : ∃ k, w ∈ vcMon T v k := by simpa [vcMonAll] using hw
    exact hstab k a b w hk

def vcIter (A : Module.End ℂ U) (θ : ℕ → ℂ) (k0 : ℕ) : ℕ → Module.End ℂ U
  | 0 => 1
  | i + 1 => (A - θ (k0 + i) • 1) * vcIter A θ k0 i

theorem vcIter_maps (A : Module.End ℂ U) (θ : ℕ → ℂ) (F : ℕ → Submodule ℂ U)
    (hstep : ∀ k, ∀ x ∈ F k, A x - θ k • x ∈ F (k + 1)) (k0 : ℕ) :
    ∀ i, ∀ x ∈ F k0, vcIter A θ k0 i x ∈ F (k0 + i) := by
  intro i x hx
  induction i with
  | zero => simpa [vcIter] using hx
  | succ i ih =>
    simpa only [vcIter, mul_apply_eq_comp, LinearMap.sub_apply, LinearMap.smul_apply,
      one_apply_eq_self, Nat.add_assoc] using hstep (k0 + i) _ ih

theorem vcIter_eig (A : Module.End ℂ U) (θ : ℕ → ℂ) (k0 : ℕ) {x : U} {t : ℂ} (hx : A x = t • x) :
    ∀ i, vcIter A θ k0 i x = (∏ i' ∈ range i, (t - θ (k0 + i'))) • x
  | 0 => by simp [vcIter]
  | i + 1 => by
    rw [vcIter, Module.End.mul_apply, vcIter_eig A θ k0 hx i, Finset.prod_range_succ]
    simp only [map_smul, LinearMap.sub_apply, hx, LinearMap.smul_apply, Module.End.one_apply]
    rw [← sub_smul, smul_smul, mul_comm]

theorem vcIter_comm (A : Module.End ℂ U) (θ : ℕ → ℂ) (k0 : ℕ) {X : Module.End ℂ U} (hX : Commute A X) :
    ∀ i, Commute (vcIter A θ k0 i) X
  | 0 => Commute.one_left X
  | i + 1 => ((hX.sub_left ((Commute.one_left X).smul_left _)).mul_left (vcIter_comm A θ k0 hX i))

end Core

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

section Core2

variable {n : ℕ} {U : Type*} [AddCommGroup U] [Module ℂ U]

theorem vc_cone_core (T : Fin n → Fin n → Module.End ℂ U) (hT : IsGlRep T) (A : Module.End ℂ U)
    (hA : ∀ a b, Commute A (T a b)) (F : ℕ → Submodule ℂ U) (θ : ℕ → ℂ)
    (hF : ∀ k a b, ∀ x ∈ F k, T a b x ∈ F k)
    (hstep : ∀ k, ∀ x ∈ F k, A x - θ k • x ∈ F (k + 1))
    (m j : ℕ) (h0 : F 0 = ⊤) (hm : F m = ⊥) (hj : j < m) (hθ : ∀ k < m, k ≠ j → θ k ≠ θ j)
    (v : U) (base : Fin n → ℝ) (hFj : F j ≤ genSub T (Submodule.span ℂ {v}) ⊔ F (j + 1))
    (hlow : ∀ a b, b < a → T a b v ∈ F (j + 1)) (hdiag : ∀ a, T a a v = ((base a : ℝ) : ℂ) • v) :
    (∀ (μ : Fin n → ℝ) (x : U), A x = θ j • x → x ≠ 0 → (∀ a, T a a x = ((μ a : ℝ) : ℂ) • x) →
        InRootCone (μ - base)) ∧
    ∀ x₁ x₂ : U, A x₁ = θ j • x₁ → A x₂ = θ j • x₂ →
      (∀ a, T a a x₁ = ((base a : ℝ) : ℂ) • x₁) → (∀ a, T a a x₂ = ((base a : ℝ) : ℂ) • x₂) →
      ∃ c₁ c₂ : ℂ, (c₁ ≠ 0 ∨ c₂ ≠ 0) ∧ c₁ • x₁ + c₂ • x₂ = 0 := by
  have hiter_maps : ∀ k₀ i x, x ∈ F k₀ → vcIter A θ k₀ i x ∈ F (k₀ + i) := by
    intro k₀ i
    induction i with
    | zero =>
        intro x hx
        simpa [vcIter] using hx
    | succ i ih =>
        intro x hx
        have h := hstep (k₀ + i) _ (ih x hx)
        simpa [vcIter, Module.End.mul_apply, LinearMap.sub_apply, add_assoc] using h
  set post := vcIter A θ (j + 1) (m - j - 1) with hpost
  set c' : ℂ := ∏ i ∈ range (m - j - 1), (θ j - θ (j + 1 + i)) with hc'
  have hc'0 : c' ≠ 0 := by
    rw [hc', Finset.prod_ne_zero_iff]
    intro i hi
    rw [Finset.mem_range] at hi
    exact sub_ne_zero.mpr (hθ (j + 1 + i) (by omega) (by omega)).symm
  have hpostT : ∀ a b, Commute post (T a b) := fun a b => vcIter_comm A θ _ (hA a b) _
  have hred : ∀ x, A x = θ j • x → ∃ y ∈ Submodule.span ℂ (vcMonAll T v), post y = c' • x := by
    intro x hx
    have hxj : x ∈ F j := by
      have h1 := hiter_maps 0 j x (by rw [h0]; exact Submodule.mem_top)
      rw [vcIter_eig A θ 0 hx j, Nat.zero_add] at h1
      have hc : (∏ i' ∈ range j, (θ j - θ (0 + i'))) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro i hi
        rw [Finset.mem_range] at hi
        exact sub_ne_zero.mpr (hθ (0 + i) (by omega) (by omega)).symm
      have := (F j).smul_mem (∏ i' ∈ range j, (θ j - θ (0 + i')))⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    have hx2 : x ∈ Submodule.span ℂ (vcMonAll T v) ⊔ F (j + 1) := by
      have h3 := vc_genSub_le_mon T hT v (F (j + 1)) (hF (j + 1)) hlow (fun a => ⟨_, hdiag a⟩)
      exact (sup_le h3 le_sup_right) (hFj hxj)
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx2
    refine ⟨y, hy, ?_⟩
    have hpz : post z = 0 := by
      have := hiter_maps (j + 1) (m - j - 1) z hz
      rw [show j + 1 + (m - j - 1) = m by omega, hm] at this
      exact (Submodule.mem_bot ℂ).mp this
    have hpx : post x = c' • x := vcIter_eig A θ (j + 1) hx _
    rw [← hpx, ← hyz, map_add (f := _), hpz, add_zero]
  have hpostGood : ∀ (P : (Fin n → ℝ) → Prop) (w : U), w ∈ vcGood T P → post w ∈ vcGood T P := by
    intro P w ⟨ν, hP, hν⟩
    refine ⟨ν, hP, fun a => ?_⟩
    rw [← Module.End.mul_apply, ← (hpostT a a).eq, Module.End.mul_apply, hν a, map_smul]
  have hspanGood : ∀ (P : (Fin n → ℝ) → Prop) (G : Set U), G ⊆ vcGood T P →
      ∀ y ∈ Submodule.span ℂ G, post y ∈ Submodule.span ℂ (vcGood T P) := by
    intro P G hG y hy
    have : Submodule.span ℂ G ≤ (Submodule.span ℂ (vcGood T P)).comap post :=
      Submodule.span_le.mpr (fun w hw => Submodule.subset_span (hpostGood P w (hG hw)))
    exact this hy
  refine ⟨?_, ?_⟩
  · intro μ x hx hx0 hμ
    by_contra hcone
    obtain ⟨y, hy, hyx⟩ := hred x hx
    have hmon : vcMonAll T v ⊆ vcGood T (fun ν => InRootCone (ν - base)) := by
      intro w hw
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hw
      obtain ⟨ν, hν, hc, _⟩ := vcMon_weight T hT hdiag k w hk
      exact ⟨ν, hc, hν⟩
    have hs := hspanGood _ _ hmon y hy
    rw [hyx] at hs
    have hz := vc_eq_zero_of_mem_span T (fun ν => InRootCone (ν - base)) hcone
      (x := c' • x) (fun a => by rw [map_smul, hμ a, smul_comm]) hs
    exact hx0 ((smul_eq_zero.mp hz).resolve_left hc'0)
  · have hpv : ∀ a, T a a (post v) = ((base a : ℝ) : ℂ) • post v := by
      intro a
      rw [← Module.End.mul_apply, ← (hpostT a a).eq, Module.End.mul_apply, hdiag a, map_smul]
    have hvert : ∀ x, A x = θ j • x → (∀ a, T a a x = ((base a : ℝ) : ℂ) • x) →
        ∃ β : ℂ, x = β • post v := by
      intro x hx hxw
      obtain ⟨y, hy, hyx⟩ := hred x hx
      have hmon : vcMonAll T v ⊆
          (Submodule.span ℂ {v} ⊔ Submodule.span ℂ (vcGood T (fun ν => ν ≠ base)) : Submodule ℂ U) := by
        intro w hw
        obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hw
        rcases k with _ | k
        · have hwv : w = v := hk
          subst hwv
          exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self w)
        · obtain ⟨ν, hν, _, hht⟩ := vcMon_weight T hT hdiag (k + 1) w hk
          refine Submodule.mem_sup_right (Submodule.subset_span ⟨ν, ?_, hν⟩)
          intro hνb
          rw [hνb, sub_self, vcHt_zero] at hht
          push_cast at hht
          linarith
      have hy2 := (Submodule.span_le.mpr hmon) hy
      obtain ⟨y1, hy1, r, hr, hyr⟩ := Submodule.mem_sup.mp hy2
      obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.mp hy1
      have hpr := hspanGood (fun ν => ν ≠ base) _ (Set.Subset.refl _) r hr
      have hd : c' • x - α • post v = post r := by
        rw [← hyx, ← hyr, map_add (f := _), map_smul]
        abel
      have hdw : ∀ a, T a a (c' • x - α • post v) = ((base a : ℝ) : ℂ) • (c' • x - α • post v) := by
        intro a
        rw [map_sub, map_smul, map_smul, hxw a, hpv a, smul_sub, smul_comm c', smul_comm α]
      have hd0 := vc_eq_zero_of_mem_span T (fun ν => ν ≠ base) (μ := base) (by simp) hdw
        (by rw [hd]; exact hpr)
      refine ⟨c'⁻¹ * α, ?_⟩
      rw [sub_eq_zero] at hd0
      rw [mul_smul, ← hd0, smul_smul, inv_mul_cancel₀ hc'0, one_smul]
    intro x₁ x₂ h1 h2 hw1 hw2
    obtain ⟨β₁, rfl⟩ := hvert x₁ h1 hw1
    obtain ⟨β₂, rfl⟩ := hvert x₂ h2 hw2
    by_cases hb : β₁ = 0
    · exact ⟨1, 0, Or.inl one_ne_zero, by simp [hb]⟩
    · refine ⟨β₂, -β₁, Or.inr (neg_ne_zero.mpr hb), ?_⟩
      rw [smul_smul, smul_smul, mul_comm β₂ β₁, neg_mul, neg_smul, add_neg_cancel]

def vcFlag (T : Fin n → Fin n → Module.End ℂ U) (g : Fin n → U) (r : Fin n → ℕ) (k : ℕ) : Submodule ℂ U :=
  genSub T (Submodule.span ℂ (g '' {t | k ≤ r t}))

variable (T : Fin n → Fin n → Module.End ℂ U) (g : Fin n → U) (r : Fin n → ℕ)

theorem vcFlag_stable (k : ℕ) (a b : Fin n) : ∀ x ∈ vcFlag T g r k, T a b x ∈ vcFlag T g r k :=
  fun _ hx => vc_genSub_stable T _ a b hx

theorem vcFlag_gen {t : Fin n} {k : ℕ} (h : k ≤ r t) : g t ∈ vcFlag T g r k :=
  vc_le_genSub T _ (Submodule.subset_span ⟨t, h, rfl⟩)

theorem vcFlag_anti {k l : ℕ} (h : k ≤ l) : vcFlag T g r l ≤ vcFlag T g r k :=
  vc_genSub_le T _ _ (Submodule.span_le.mpr (by
    rintro _ ⟨t, ht, rfl⟩
    exact vcFlag_gen T g r (le_trans h ht))) (vcFlag_stable T g r k)

theorem vcFlag_eq_bot {m : ℕ} (hm : ∀ t, r t < m) : vcFlag T g r m = ⊥ := by
  refine le_bot_iff.mp (vc_genSub_le T _ ⊥ ?_ (fun a b v hv => by
    rw [(Submodule.mem_bot ℂ).mp hv, map_zero]; exact Submodule.zero_mem _))
  rw [Submodule.span_le]
  rintro _ ⟨t, ht, rfl⟩
  exact absurd ht (not_le.mpr (hm t))

theorem vcFlag_step (A : Module.End ℂ U) (hA : ∀ a b, Commute A (T a b)) (θ : ℕ → ℂ)
    (hgen : ∀ t, A (g t) - θ (r t) • g t ∈ vcFlag T g r (r t + 1)) :
    ∀ k, ∀ x ∈ vcFlag T g r k, A x - θ k • x ∈ vcFlag T g r (k + 1) := by
  have hAst : ∀ k, ∀ x ∈ vcFlag T g r k, A x ∈ vcFlag T g r k := by
    intro k
    let S : Submodule ℂ U := vcFlag T g r k ⊓ (vcFlag T g r k).comap A
    have hle : vcFlag T g r k ≤ S := by
      refine vc_genSub_le T _ S ?_ ?_
      · rw [Submodule.span_le]
        rintro _ ⟨t, ht, rfl⟩
        refine ⟨vcFlag_gen T g r ht, ?_⟩
        show A (g t) ∈ vcFlag T g r k
        have h1 := vcFlag_anti T g r (show k ≤ r t + 1 by simp at ht; omega) (hgen t)
        have h2 := (vcFlag T g r k).smul_mem (θ (r t)) (vcFlag_gen T g r ht)
        simpa using (vcFlag T g r k).add_mem h1 h2
      · intro a b x hx
        refine ⟨vcFlag_stable T g r k a b x hx.1, ?_⟩
        show A (T a b x) ∈ vcFlag T g r k
        rw [← Module.End.mul_apply, (hA a b).eq, Module.End.mul_apply]
        exact vcFlag_stable T g r k a b _ hx.2
    exact fun x hx => (hle hx).2
  intro k
  let S : Submodule ℂ U := vcFlag T g r k ⊓ (vcFlag T g r (k + 1)).comap (A - θ k • 1)
  have hle : vcFlag T g r k ≤ S := by
    refine vc_genSub_le T _ S ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨t, ht, rfl⟩
      refine ⟨vcFlag_gen T g r ht, ?_⟩
      show (A - θ k • 1) (g t) ∈ vcFlag T g r (k + 1)
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      have ht' : k ≤ r t := ht
      rcases eq_or_lt_of_le ht' with h | h
      · rw [h]; exact hgen t
      · have hg : g t ∈ vcFlag T g r (k + 1) := vcFlag_gen T g r h
        exact Submodule.sub_mem _ (hAst (k + 1) _ hg) (Submodule.smul_mem _ _ hg)
    · intro a b x hx
      refine ⟨vcFlag_stable T g r k a b x hx.1, ?_⟩
      show (A - θ k • 1) (T a b x) ∈ vcFlag T g r (k + 1)
      have hc : Commute (A - θ k • 1) (T a b) := (hA a b).sub_left ((Commute.one_left _).smul_left _)
      rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply]
      exact vcFlag_stable T g r (k + 1) a b _ hx.2
  intro x hx
  have := (hle hx).2
  simpa using this

theorem vcFlag_top_le {j : ℕ} {s : Fin n} (hr : Function.Injective r) (hj : r s = j) :
    vcFlag T g r j ≤ genSub T (Submodule.span ℂ {g s}) ⊔ vcFlag T g r (j + 1) := by
  refine vc_genSub_le T _ _ ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨t, ht, rfl⟩
    have ht' : j ≤ r t := ht
    rcases eq_or_lt_of_le ht' with h | h
    · have hts : t = s := hr (by omega)
      subst hts
      exact Submodule.mem_sup_left (vc_le_genSub T _ (Submodule.mem_span_singleton_self _))
    · exact Submodule.mem_sup_right (vcFlag_gen T g r h)
  · intro a b x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (vc_genSub_stable T _ a b hy) (vcFlag_stable T g r _ a b z hz)

end Core2

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

section Inst

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem vc_tensV_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (m : M) :
    tensV E a b (Pi.single c m) = Pi.single c (E a b m) + (if b = c then Pi.single a m else 0) := by
  ext d
  simp only [tensV, prj, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Pi.add_apply]
  by_cases hdc : d = c <;> by_cases hda : d = a <;> by_cases hbc : b = c <;>
    simp_all

theorem vc_tensVd_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (m : M) :
    tensVd E a b (Pi.single c m) = Pi.single c (E a b m) - (if a = c then Pi.single b m else 0) := by
  ext d
  simp only [tensVd, prj, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Pi.sub_apply]
  by_cases hdc : d = c <;> by_cases hdb : d = b <;> by_cases hac : a = c <;>
    simp_all

theorem vc_tensV_apply (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensV E a b f c = E a b (f c) + (if c = a then f b else 0) := by
  by_cases h : c = a <;> simp [tensV, prj, h]

theorem vc_tensVd_apply (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensVd E a b f c = E a b (f c) - (if c = b then f a else 0) := by
  by_cases h : c = b <;> simp [tensVd, prj, h]

theorem vc_eeV_single (E : Fin n → Fin n → Module.End ℂ M) (t e : Fin n) (m : M) :
    eeV E (Pi.single t m) e = E t e m := by
  simp [eeV, prj, Pi.single_apply, apply_ite]

theorem vc_eeVd_single (E : Fin n → Fin n → Module.End ℂ M) (t e : Fin n) (m : M) :
    eeVd E (Pi.single t m) e = -E e t m := by
  simp [eeVd, prj, Pi.single_apply, apply_ite]

theorem vc_commV (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) (a b : Fin n) :
    Commute (eeV E) (tensV E a b) := by
  obtain ⟨hT, -, hcas, -⟩ := tens_statement n M E hE
  have key : ∀ g : Fin n → M, (2 : ℂ) • eeV E g =
      casimir (tensV E) g - (fun c => casimir E (g c)) - (n : ℂ) • g := by
    intro g
    rw [hcas g]
    abel
  have hpi : ∀ g : Fin n → M,
      (fun c => casimir E (tensV E a b g c)) = tensV E a b (fun c => casimir E (g c)) := by
    intro g
    funext c
    rw [vc_tensV_apply, vc_tensV_apply, map_add (f := _)]
    congr 1
    · rw [← Module.End.mul_apply, casimir_comm hE, Module.End.mul_apply]
    · split_ifs <;> simp
  show eeV E * tensV E a b = tensV E a b * eeV E
  refine LinearMap.ext fun g => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply]
  have h2 : (2 : ℂ) • eeV E (tensV E a b g) = (2 : ℂ) • tensV E a b (eeV E g) := by
    rw [← map_smul (tensV E a b) (2 : ℂ) (eeV E g), key, key, map_sub, map_sub, map_smul, ← hpi,
      ← Module.End.mul_apply (casimir (tensV E)), casimir_comm hT a b, Module.End.mul_apply]
  exact smul_right_injective (Fin n → M) two_ne_zero h2

theorem vc_commVd (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) (a b : Fin n) :
    Commute (eeVd E) (tensVd E a b) := by
  obtain ⟨-, hT, -, hcas⟩ := tens_statement n M E hE
  have key : ∀ g : Fin n → M, (2 : ℂ) • eeVd E g =
      casimir (tensVd E) g - (fun c => casimir E (g c)) - (n : ℂ) • g := by
    intro g
    rw [hcas g]
    abel
  have hpi : ∀ g : Fin n → M,
      (fun c => casimir E (tensVd E a b g c)) = tensVd E a b (fun c => casimir E (g c)) := by
    intro g
    funext c
    rw [vc_tensVd_apply, vc_tensVd_apply, map_sub]
    congr 1
    · rw [← Module.End.mul_apply, casimir_comm hE, Module.End.mul_apply]
    · split_ifs <;> simp
  show eeVd E * tensVd E a b = tensVd E a b * eeVd E
  refine LinearMap.ext fun g => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply]
  have h2 : (2 : ℂ) • eeVd E (tensVd E a b g) = (2 : ℂ) • tensVd E a b (eeVd E g) := by
    rw [← map_smul (tensVd E a b) (2 : ℂ) (eeVd E g), key, key, map_sub, map_sub, map_smul, ← hpi,
      ← Module.End.mul_apply (casimir (tensVd E)), casimir_comm hT a b, Module.End.mul_apply]
  exact smul_right_injective (Fin n → M) two_ne_zero h2

theorem vc_gen_top (E : Fin n → Fin n → Module.End ℂ M) (φ : M)
    (hgen : genSub E (Submodule.span ℂ {φ}) = ⊤) (T : Fin n → Fin n → Module.End ℂ (Fin n → M))
    (hT : ∀ a b c m, Pi.single c (E a b m) - T a b (Pi.single c m) ∈
        Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)))
    (G : Submodule ℂ (Fin n → M)) (hG : ∀ a b, ∀ x ∈ G, T a b x ∈ G)
    (hφ : ∀ c, (Pi.single c φ : Fin n → M) ∈ G) : G = ⊤ := by
  let S : Submodule ℂ M :=
    { carrier := {m | ∀ c, (Pi.single c m : Fin n → M) ∈ G}
      add_mem' := by
        intro x y hx hy c
        rw [Pi.single_add]
        exact G.add_mem (hx c) (hy c)
      zero_mem' := by
        intro c
        rw [Pi.single_zero]
        exact G.zero_mem
      smul_mem' := by
        intro r x hx c
        rw [Pi.single_smul']
        exact G.smul_mem r (hx c) }
  have hSS : ∀ a b, ∀ m ∈ S, E a b m ∈ S := by
    intro a b m hm c
    have h1 : Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)) ≤ G :=
      Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact hm x)
    have h2 := G.add_mem (h1 (hT a b c m)) (hG a b _ (hm c))
    simpa using h2
  have hle := vc_genSub_le E _ S (by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hφ) hSS
  rw [hgen] at hle
  refine eq_top_iff.mpr fun f _ => ?_
  rw [← Finset.univ_sum_single f]
  exact G.sum_mem fun c _ => hle Submodule.mem_top c

end Inst

section Inst2

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem vc_genV (E : Fin n → Fin n → Module.End ℂ M) (lam : Fin n → ℝ) (φ : M)
    (hlow : ∀ a b, b < a → E a b φ = 0) (hd : ∀ a, E a a φ = ((lam a + rho n a : ℝ) : ℂ) • φ) (t : Fin n) :
    eeV E (Pi.single t φ : Fin n → M) - ((thV lam t : ℝ) : ℂ) • (Pi.single t φ : Fin n → M) =
      ∑ d ∈ univ.filter (fun d => t < d), tensV E t d (Pi.single d φ) := by
  funext e
  rw [Pi.sub_apply, vc_eeV_single, Finset.sum_apply]
  simp only [vc_tensV_single, Pi.add_apply, if_true, Pi.smul_apply, Pi.single_apply]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_const]
  rcases lt_trichotomy e t with h | rfl | h
  · simp [h.ne, hlow t e h, not_lt.mpr h.le]
  · have hc : (univ.filter fun d : Fin n => e < d).card = n - 1 - e := by
      rw [filter_lt_eq_Ioi, Fin.card_Ioi]
    simp only [if_true, lt_irrefl, Finset.mem_filter, Finset.mem_univ, true_and, if_false, zero_add, hc, hd]
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← sub_smul]
    congr 1
    have he : 1 + (e : ℕ) ≤ n := by have := e.isLt; omega
    rw [Nat.sub_sub, Nat.cast_sub he]
    simp only [rho, thV]
    push_cast
    ring
  · simp [h.ne', h]

theorem vc_genVd (E : Fin n → Fin n → Module.End ℂ M) (lam : Fin n → ℝ) (φ : M)
    (hlow : ∀ a b, b < a → E a b φ = 0) (hd : ∀ a, E a a φ = ((lam a + rho n a : ℝ) : ℂ) • φ) (t : Fin n) :
    eeVd E (Pi.single t φ : Fin n → M) - ((thVd lam t : ℝ) : ℂ) • (Pi.single t φ : Fin n → M) =
      -∑ d ∈ univ.filter (fun d => d < t), tensVd E d t (Pi.single d φ) := by
  funext e
  rw [Pi.sub_apply, vc_eeVd_single, Pi.neg_apply, Finset.sum_apply]
  simp only [vc_tensVd_single, Pi.sub_apply, if_true, Pi.smul_apply, Pi.single_apply]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_const]
  rcases lt_trichotomy e t with h | rfl | h
  · simp [h.ne, h]
  · have hc : (univ.filter fun d : Fin n => d < e).card = e := by
      rw [filter_gt_eq_Iio, Fin.card_Iio]
    simp only [if_true, lt_irrefl, Finset.mem_filter, Finset.mem_univ, true_and, if_false, zero_sub, hc, hd,
      neg_neg]
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← neg_smul, ← sub_smul]
    congr 1
    simp only [rho, thVd]
    push_cast
    ring
  · simp [h.ne', hlow e t h, not_lt.mpr h.le]

end Inst2

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

section Inst3

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

def vcSgl (φ : M) : Fin n → Fin n → M := fun t => Pi.single t φ

def vcRV (n : ℕ) : Fin n → ℕ := fun t => (t : ℕ)

def vcRVd (n : ℕ) : Fin n → ℕ := fun t => (Fin.rev t : ℕ)

def vcThV (lam : Fin n → ℝ) : ℕ → ℂ := fun k => if h : k < n then ((thV lam ⟨k, h⟩ : ℝ) : ℂ) else 0

def vcThVd (lam : Fin n → ℝ) : ℕ → ℂ :=
  fun k => if h : k < n then ((thVd lam (Fin.rev ⟨k, h⟩) : ℝ) : ℂ) else 0

theorem vcThV_rV (lam : Fin n → ℝ) (t : Fin n) : vcThV lam (vcRV n t) = ((thV lam t : ℝ) : ℂ) := by
  simp [vcThV, vcRV, t.isLt]

theorem vcThVd_rVd (lam : Fin n → ℝ) (t : Fin n) : vcThVd lam (vcRVd n t) = ((thVd lam t : ℝ) : ℂ) := by
  unfold vcThVd vcRVd
  rw [dite_eq_left (Fin.rev t).isLt]
  simp only [Fin.eta, Fin.rev_rev]

theorem vcThV_ne (lam : Fin n → ℝ) (hanti : StrictAnti lam) (s : Fin n) :
    ∀ k < n, k ≠ vcRV n s → vcThV lam k ≠ vcThV lam (vcRV n s) := by
  intro k hk hks heq
  rw [vcThV_rV, show vcThV lam k = ((thV lam ⟨k, hk⟩ : ℝ) : ℂ) by simp [vcThV, hk]] at heq
  have h1 : thV lam ⟨k, hk⟩ = thV lam s := by exact_mod_cast heq
  have h2 : lam ⟨k, hk⟩ = lam s := by unfold thV at h1; linarith
  exact hks (congrArg Fin.val (hanti.injective h2))

theorem vcThVd_ne (lam : Fin n → ℝ) (hanti : StrictAnti lam) (s : Fin n) :
    ∀ k < n, k ≠ vcRVd n s → vcThVd lam k ≠ vcThVd lam (vcRVd n s) := by
  intro k hk hks heq
  rw [vcThVd_rVd, show vcThVd lam k = ((thVd lam (Fin.rev ⟨k, hk⟩) : ℝ) : ℂ) by simp [vcThVd, hk]] at heq
  have h1 : thVd lam (Fin.rev ⟨k, hk⟩) = thVd lam s := by exact_mod_cast heq
  have h2 : lam (Fin.rev ⟨k, hk⟩) = lam s := by unfold thVd at h1; linarith
  have h3 := hanti.injective h2
  apply hks
  rw [← h3]
  simp [vcRVd]

theorem vc_xs {A : Module.End ℂ (Fin n → M)} {S : Submodule ℂ M} {θ : ℝ} {f : Fin n → M}
    (hf : f ∈ Xs A S θ) : A f = ((θ : ℝ) : ℂ) • f := by
  have h := (Submodule.mem_inf.mp hf).2
  rw [LinearMap.mem_ker] at h
  simpa [sub_eq_zero] using h

end Inst3

theorem verma_cone (n : ℕ) : VermaConeStatement n := by
  intro M _ _ E lam φ s hE hlow hd hgen hanti
  obtain ⟨hTV, hTVd, -, -⟩ := tens_statement n M E hE
  refine ⟨?_, ?_⟩
  · have hgenV : ∀ t, eeV E (vcSgl φ t) - vcThV lam (vcRV n t) • vcSgl φ t ∈
        vcFlag (tensV E) (vcSgl φ) (vcRV n) (vcRV n t + 1) := by
      intro t
      rw [vcThV_rV]
      show eeV E (Pi.single t φ : Fin n → M) - ((thV lam t : ℝ) : ℂ) • (Pi.single t φ : Fin n → M) ∈ _
      rw [vc_genV E lam φ hlow hd t]
      refine Submodule.sum_mem _ fun d hd' => vcFlag_stable _ _ _ _ _ _ _ (vcFlag_gen _ _ _ ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd'
      exact hd'
    have h0 : vcFlag (tensV E) (vcSgl φ) (vcRV n) 0 = ⊤ := by
      refine vc_gen_top E φ hgen (tensV E) ?_ _ (vcFlag_stable _ _ _ 0)
        (fun c => vcFlag_gen (tensV E) (vcSgl φ) (vcRV n) (Nat.zero_le _))
      intro a b c m
      rw [vc_tensV_single]
      split_ifs
      · have hx : (Pi.single a m : Fin n → M) ∈
            Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)) :=
          Submodule.subset_span ⟨a, rfl⟩
        simpa using Submodule.neg_mem _ hx
      · simp
    have hlowV : ∀ a b, b < a → tensV E a b (vcSgl φ s) ∈ vcFlag (tensV E) (vcSgl φ) (vcRV n) (vcRV n s + 1) := by
      intro a b hab
      show tensV E a b (Pi.single s φ) ∈ _
      rw [vc_tensV_single, hlow a b hab, Pi.single_zero, zero_add]
      split_ifs with hbs
      · subst hbs
        exact vcFlag_gen _ _ _ hab
      · exact Submodule.zero_mem _
    have hdiagV : ∀ a, tensV E a a (vcSgl φ s) = (((lam + rho n + Pi.single s 1 : Fin n → ℝ) a : ℝ) : ℂ) • vcSgl φ s := by
      intro a
      show tensV E a a (Pi.single s φ) = _ • (Pi.single s φ : Fin n → M)
      rw [vc_tensV_single, hd a, Pi.single_smul']
      by_cases has : a = s
      · subst has
        simp [add_smul]
      · simp [has, Pi.single_apply]
    have hrinj : Function.Injective (vcRV n) := fun a b h => Fin.ext h
    obtain ⟨h1, h2⟩ := vc_cone_core (tensV E) hTV (eeV E) (vc_commV E hE) (vcFlag (tensV E) (vcSgl φ) (vcRV n))
      (vcThV lam) (vcFlag_stable _ _ _) (vcFlag_step _ _ _ (eeV E) (vc_commV E hE) (vcThV lam) hgenV) n
      (vcRV n s) h0 (vcFlag_eq_bot _ _ _ (fun t => t.isLt)) s.isLt (vcThV_ne lam hanti s) (vcSgl φ s)
      (lam + rho n + Pi.single s 1) (vcFlag_top_le _ _ _ hrinj rfl) hlowV hdiagV
    refine ⟨fun μ f hf hf0 hμ => h1 μ f (by rw [vcThV_rV]; exact vc_xs hf) hf0 hμ, ?_⟩
    intro f₁ f₂ hf₁ hf₂ hw₁ hw₂
    exact h2 f₁ f₂ (by rw [vcThV_rV]; exact vc_xs hf₁) (by rw [vcThV_rV]; exact vc_xs hf₂) hw₁ hw₂
  · have hgenVd : ∀ t, eeVd E (vcSgl φ t) - vcThVd lam (vcRVd n t) • vcSgl φ t ∈
        vcFlag (tensVd E) (vcSgl φ) (vcRVd n) (vcRVd n t + 1) := by
      intro t
      rw [vcThVd_rVd]
      show eeVd E (Pi.single t φ : Fin n → M) - ((thVd lam t : ℝ) : ℂ) • (Pi.single t φ : Fin n → M) ∈ _
      rw [vc_genVd E lam φ hlow hd t]
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun d hd' =>
        vcFlag_stable _ _ _ _ _ _ _ (vcFlag_gen _ _ _ ?_))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd'
      have := Fin.lt_def.mp hd'
      simp only [vcRVd, Fin.val_rev]
      omega
    have h0 : vcFlag (tensVd E) (vcSgl φ) (vcRVd n) 0 = ⊤ := by
      refine vc_gen_top E φ hgen (tensVd E) ?_ _ (vcFlag_stable _ _ _ 0)
        (fun c => vcFlag_gen (tensVd E) (vcSgl φ) (vcRVd n) (Nat.zero_le _))
      intro a b c m
      rw [vc_tensVd_single]
      split_ifs
      · have hx : (Pi.single b m : Fin n → M) ∈
            Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)) :=
          Submodule.subset_span ⟨b, rfl⟩
        simpa using hx
      · simp
    have hlowVd : ∀ a b, b < a → tensVd E a b (vcSgl φ s) ∈
        vcFlag (tensVd E) (vcSgl φ) (vcRVd n) (vcRVd n s + 1) := by
      intro a b hab
      show tensVd E a b (Pi.single s φ) ∈ _
      rw [vc_tensVd_single, hlow a b hab, Pi.single_zero, zero_sub]
      split_ifs with has
      · subst has
        refine Submodule.neg_mem _ (vcFlag_gen _ _ _ ?_)
        have := Fin.lt_def.mp hab
        simp only [vcRVd, Fin.val_rev]
        omega
      · simp
    have hdiagVd : ∀ a, tensVd E a a (vcSgl φ s) =
        (((lam + rho n - Pi.single s 1 : Fin n → ℝ) a : ℝ) : ℂ) • vcSgl φ s := by
      intro a
      show tensVd E a a (Pi.single s φ) = _ • (Pi.single s φ : Fin n → M)
      rw [vc_tensVd_single, hd a, Pi.single_smul']
      by_cases has : a = s
      · subst has
        simp [add_smul, sub_smul]
      · simp [has, Pi.single_apply]
    have hrinj : Function.Injective (vcRVd n) := fun a b h => Fin.rev_injective (Fin.ext h)
    obtain ⟨h1, h2⟩ := vc_cone_core (tensVd E) hTVd (eeVd E) (vc_commVd E hE)
      (vcFlag (tensVd E) (vcSgl φ) (vcRVd n)) (vcThVd lam) (vcFlag_stable _ _ _)
      (vcFlag_step _ _ _ (eeVd E) (vc_commVd E hE) (vcThVd lam) hgenVd) n
      (vcRVd n s) h0 (vcFlag_eq_bot _ _ _ (fun t => (Fin.rev t).isLt)) (Fin.rev s).isLt
      (vcThVd_ne lam hanti s) (vcSgl φ s)
      (lam + rho n - Pi.single s 1) (vcFlag_top_le _ _ _ hrinj rfl) hlowVd hdiagVd
    refine ⟨fun μ f hf hf0 hμ => h1 μ f (by rw [vcThVd_rVd]; exact vc_xs hf) hf0 hμ, ?_⟩
    intro f₁ f₂ hf₁ hf₂ hw₁ hw₂
    exact h2 f₁ f₂ (by rw [vcThVd_rVd]; exact vc_xs hf₁) (by rw [vcThVd_rVd]; exact vc_xs hf₂) hw₁ hw₂

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
