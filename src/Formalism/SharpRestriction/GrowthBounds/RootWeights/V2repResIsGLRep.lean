module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.ContravariantIsotypicOrthogonal

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.V2repExistsHwv
section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.HighestWeightModuleBounds
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem v2rep_mem_weightSp (E : GLOps n K V) (mu : Fin n → ℤ) (x : V) :
    x ∈ weightSp E mu ↔ ∀ a, E a a x = (mu a : K) • x := by
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero]

theorem v2rep_comm (E : GLOps n K V) (hR : SatisfiesGLRelations E) (a b c d : Fin n) (x : V) :
    E a b (E c d x) = E c d (E a b x) + ((if b = c then E a d x else 0) - (if d = a then E c b x else 0)) := by
  have h := congrArg (fun f : Module.End K V => f x) (hR a b c d)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [sub_eq_iff_eq_add'] at h
  rw [h]
  congr 1
  split_ifs <;> simp

theorem v2rep_shift (E : GLOps n K V) (hR : SatisfiesGLRelations E) (a b : Fin n) (ν : Fin n → ℤ) (x : V)
    (hx : x ∈ weightSp E ν) : E a b x ∈ weightSp E (ν + rootW a b) := by
  rw [v2rep_mem_weightSp] at hx ⊢
  intro c
  rw [v2rep_comm E hR c c a b x, hx c, map_smul]
  by_cases hca : c = a <;> by_cases hcb : c = b
  · subst hca; subst hcb
    simp [rootW]
  · subst hca
    simp [rootW, hcb, Ne.symm hcb]
    module
  · subst hcb
    simp [rootW, hca]
    module
  · simp [rootW, hca, hcb, Ne.symm hcb]

def cyclicLevelSubmodule (E : GLOps n K V) (v : V) : ℕ → Submodule K V
  | 0 => Submodule.span K {v}
  | k + 1 => cyclicLevelSubmodule E v k ⊔ ⨆ ab : Fin n × Fin n, ⨆ (_ : ab.2 < ab.1), (cyclicLevelSubmodule E v k).map (E ab.1 ab.2)

theorem v2rep_Y_le (E : GLOps n K V) (v : V) (k : ℕ) : cyclicLevelSubmodule E v k ≤ cyclicLevelSubmodule E v (k + 1) := by
  exact le_sup_left

theorem v2rep_Y_low (E : GLOps n K V) (v : V) (k : ℕ) (a b : Fin n) (h : b < a) (x : V) (hx : x ∈ cyclicLevelSubmodule E v k) :
    E a b x ∈ cyclicLevelSubmodule E v (k + 1) := by
  show E a b x ∈ cyclicLevelSubmodule E v k ⊔ _
  refine Submodule.mem_sup_right ?_
  refine Submodule.mem_iSup_of_mem (a, b) ?_
  refine Submodule.mem_iSup_of_mem h ?_
  exact Submodule.mem_map_of_mem hx

theorem v2rep_Y_up (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (v : V) (hv : IsHWV E mu v) (k : ℕ) :
    ∀ c d : Fin n, c ≤ d → ∀ x ∈ cyclicLevelSubmodule E v k, E c d x ∈ cyclicLevelSubmodule E v k := by
  induction k with
  | zero =>
    intro c d hcd x hx
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    rcases hcd.lt_or_eq with hlt | heq
    · rw [hv.2.2 c d hlt]
      exact Submodule.zero_mem _
    · subst heq
      rw [(v2rep_mem_weightSp E mu v).1 hv.2.1 c]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  | succ k ih =>
    have hany : ∀ p q : Fin n, ∀ y ∈ cyclicLevelSubmodule E v k, E p q y ∈ cyclicLevelSubmodule E v (k + 1) := by
      intro p q y hy
      rcases lt_or_ge q p with hqp | hpq
      · exact v2rep_Y_low E v k p q hqp y hy
      · exact v2rep_Y_le E v k (ih p q hpq y hy)
    intro c d hcd
    suffices hs : cyclicLevelSubmodule E v (k + 1) ≤ (cyclicLevelSubmodule E v (k + 1)).comap (E c d) from fun x hx => hs hx
    refine sup_le (fun y hy => v2rep_Y_le E v k (ih c d hcd y hy)) ?_
    refine iSup_le fun ab => iSup_le fun hab => ?_
    rw [Submodule.map_le_iff_le_comap]
    intro y hy
    rw [Submodule.mem_comap, Submodule.mem_comap, v2rep_comm E hR c d ab.1 ab.2 y]
    refine Submodule.add_mem _ (v2rep_Y_low E v k ab.1 ab.2 hab _ (ih c d hcd y hy)) ?_
    refine Submodule.sub_mem _ ?_ ?_
    · split_ifs
      · exact hany c ab.2 y hy
      · exact Submodule.zero_mem _
    · split_ifs
      · exact hany ab.1 d y hy
      · exact Submodule.zero_mem _

theorem v2rep_Y_all (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (v : V) (hv : IsHWV E mu v) (k : ℕ)
    (a b : Fin n) (y : V) (hy : y ∈ cyclicLevelSubmodule E v k) : E a b y ∈ cyclicLevelSubmodule E v (k + 1) := by
  rcases lt_or_ge b a with hba | hab
  · exact v2rep_Y_low E v k a b hba y hy
  · exact v2rep_Y_le E v k (v2rep_Y_up E hR mu v hv k a b hab y hy)

theorem v2rep_Umon_Y (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (v : V) (hv : IsHWV E mu v)
    (u : Module.End K V) (hu : u ∈ Umon E) : ∀ k, ∀ x ∈ cyclicLevelSubmodule E v k, ∃ k', u x ∈ cyclicLevelSubmodule E v k' := by
  induction hu using Submonoid.closure_induction with
  | mem u hu =>
    obtain ⟨ab, rfl⟩ := hu
    intro k x hx
    exact ⟨k + 1, v2rep_Y_all E hR mu v hv k ab.1 ab.2 x hx⟩
  | one =>
    intro k x hx
    exact ⟨k, hx⟩
  | mul u₁ u₂ _ _ h₁ h₂ =>
    intro k x hx
    obtain ⟨k₂, hk₂⟩ := h₂ k x hx
    obtain ⟨k₁, hk₁⟩ := h₁ k₂ _ hk₂
    exact ⟨k₁, hk₁⟩

def dominantWeightSubmodule [NeZero n] (E : GLOps n K V) (mu : Fin n → ℤ) : Submodule K V :=
  ⨆ ν ∈ {ν : Fin n → ℤ | mu (lastIdx n) ≤ ν (lastIdx n) ∧ ν 0 ≤ mu 0}, weightSp E ν

theorem v2rep_Good_low [NeZero n] (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (a b : Fin n) (h : b < a) :
    dominantWeightSubmodule E mu ≤ (dominantWeightSubmodule E mu).comap (E a b) := by
  refine iSup₂_le fun ν hν => ?_
  intro x hx
  rw [Submodule.mem_comap]
  have hs := v2rep_shift E hR a b ν x hx
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0] at h
    exact absurd h (Fin.not_lt_zero b)
  have hbl : b ≠ lastIdx n := by
    intro hb
    have : (a : ℕ) ≤ n - 1 := Nat.le_sub_one_of_lt a.2
    have h2 : (b : ℕ) < a := h
    rw [hb] at h2
    simp [lastIdx] at h2
    omega
  refine (le_iSup₂ (f := fun ν (_ : ν ∈ {ν : Fin n → ℤ | mu (lastIdx n) ≤ ν (lastIdx n) ∧ ν 0 ≤ mu 0}) =>
    weightSp E ν) (ν + rootW a b) ?_) hs
  obtain ⟨h1, h2⟩ := hν
  refine ⟨?_, ?_⟩
  · simp only [Pi.add_apply, rootW, Pi.sub_apply, Pi.single_apply, Ne.symm hbl, if_false, sub_zero]
    split_ifs <;> omega
  · simp only [Pi.add_apply, rootW, Pi.sub_apply, Pi.single_apply, Ne.symm ha0, if_false, zero_sub]
    split_ifs <;> omega

theorem v2rep_Y_Good [NeZero n] (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (v : V) (hv : IsHWV E mu v)
    (k : ℕ) : cyclicLevelSubmodule E v k ≤ dominantWeightSubmodule E mu := by
  induction k with
  | zero =>
    refine (Submodule.span_singleton_le_iff_mem _ _).2 ?_
    exact (le_iSup₂ (f := fun ν (_ : ν ∈ {ν : Fin n → ℤ | mu (lastIdx n) ≤ ν (lastIdx n) ∧ ν 0 ≤ mu 0}) =>
      weightSp E ν) mu ⟨le_rfl, le_rfl⟩) hv.2.1
  | succ k ih =>
    refine sup_le ih (iSup_le fun ab => iSup_le fun hab => ?_)
    rw [Submodule.map_le_iff_le_comap]
    exact ih.trans (v2rep_Good_low E hR mu ab.1 ab.2 hab)

theorem highest_weight_module_bounds : HighestWeightModuleWeightBounds := by
  intro K V _ _ _ _ n _ E hR mu v hv u hu
  obtain ⟨k, hk⟩ := v2rep_Umon_Y E hR mu v hv u hu 0 v (Submodule.mem_span_singleton_self v)
  exact v2rep_Y_Good E hR mu v hv k hk

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem v2rep_comp_mem [CharZero K] (E : GLOps n K V) (Z : Submodule K V) (hZ : ∀ a, ∀ x ∈ Z, E a a x ∈ Z)
    (s : Finset (Fin n → ℤ)) : ∀ g : (Fin n → ℤ) → V, (∀ ν ∈ s, g ν ∈ weightSp E ν) → ∑ ν ∈ s, g ν ∈ Z →
      ∀ ν ∈ s, g ν ∈ Z := by
  induction s using Finset.strongInduction with
  | H s ih =>
  intro g hg hsum μ hμ
  by_cases hs : ∃ ν ∈ s, ν ≠ μ
  · obtain ⟨ν, hν, hne⟩ := hs
    obtain ⟨a, ha⟩ : ∃ a, μ a ≠ ν a := by
      by_contra h
      push_neg at h
      exact hne (funext h).symm
    let g' : (Fin n → ℤ) → V := fun ρ => (((ρ a - ν a : ℤ) : K)) • g ρ
    have hZ' : (E a a - (ν a : K) • (1 : Module.End K V)) (∑ ρ ∈ s, g ρ) ∈ Z := by
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      exact Z.sub_mem (hZ a _ hsum) (Z.smul_mem _ hsum)
    have heq : (E a a - (ν a : K) • (1 : Module.End K V)) (∑ ρ ∈ s, g ρ) = ∑ ρ ∈ s.erase ν, g' ρ := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, ← Finset.sum_erase_add _ _ hν]
      have h0 : (E a a - (ν a : K) • (1 : Module.End K V)) (g ν) = 0 := by
        have := (v2rep_mem_weightSp E ν (g ν)).mp (hg ν hν) a
        rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, this, sub_self]
      rw [h0, add_zero]
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      have := (v2rep_mem_weightSp E ρ (g ρ)).mp (hg ρ (Finset.mem_of_mem_erase hρ)) a
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, this, ← sub_smul]
      simp only [g', Int.cast_sub]
    have hg' : ∀ ρ ∈ s.erase ν, g' ρ ∈ weightSp E ρ := fun ρ hρ =>
      (weightSp E ρ).smul_mem _ (hg ρ (Finset.mem_of_mem_erase hρ))
    have hIH := ih (s.erase ν) (Finset.erase_ssubset hν) g' hg' (heq ▸ hZ') μ
      (Finset.mem_erase.mpr ⟨hne.symm, hμ⟩)
    have hc : (((μ a - ν a : ℤ)) : K) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr ha
    have := Z.smul_mem (((μ a - ν a : ℤ) : K))⁻¹ hIH
    simp only [g'] at this
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  · push_neg at hs
    have : ∑ ν ∈ s, g ν = g μ :=
      Finset.sum_eq_single_of_mem μ hμ (fun ν hν hne => absurd (hs ν hν) hne)
    rw [this] at hsum
    exact hsum

theorem v2rep_graded [CharZero K] (E : GLOps n K V) (Z : Submodule K V) (hZ : ∀ a, ∀ x ∈ Z, E a a x ∈ Z)
    (x : V) (hx : x ∈ Z) (hw : x ∈ ⨆ ν, weightSp E ν) : x ∈ ⨆ ν, weightSp E ν ⊓ Z := by
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hw
  have hsum : ∑ ν ∈ f.support, f ν ∈ Z := by simpa [Finsupp.sum] using hx
  have key := v2rep_comp_mem E Z hZ f.support f (fun ν _ => hf ν) hsum
  show ∑ ν ∈ f.support, f ν ∈ _
  exact Submodule.sum_mem _ fun ν hν => Submodule.mem_iSup_of_mem ν ⟨hf ν, key ν hν⟩

def weightHeight' (ν : Fin n → ℤ) : ℤ := -∑ a : Fin n, (a.val : ℤ) * ν a

theorem v2rep_ht_root (ν : Fin n → ℤ) (a b : Fin n) (h : a < b) : weightHeight' ν < weightHeight' (ν + rootW a b) := by
  have hab : ((a : ℕ) : ℤ) < ((b : ℕ) : ℤ) := by exact_mod_cast h
  simp only [weightHeight', rootW, Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  linarith

def heightOperator' (E : GLOps n K V) : Module.End K V := -∑ a : Fin n, ((a.val : ℤ) : K) • E a a

theorem v2rep_H_apply (E : GLOps n K V) (ν : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E ν) :
    heightOperator' E x = ((weightHeight' ν : ℤ) : K) • x := by
  rw [v2rep_mem_weightSp] at hx
  have h1 : heightOperator' E x = -∑ a : Fin n, (((a.val : ℤ) : K) * (ν a : K)) • x := by
    simp only [heightOperator', LinearMap.neg_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      hx, smul_smul]
  rw [h1, ← Finset.sum_smul, ← neg_smul]
  congr 1
  simp only [weightHeight']
  push_cast
  rfl

theorem v2rep_exists_hwv [CharZero K] (E : GLOps n K V) (hR : SatisfiesGLRelations E) (Z : Submodule K V)
    [FiniteDimensional K Z] (hZ : IsStableUnderOperators E Z) (hw : Z ≤ ⨆ ν, weightSp E ν) (hne : Z ≠ ⊥) :
    ∃ mu v, v ∈ Z ∧ IsHWV E mu v := by
  have hHZ : ∀ x ∈ Z, heightOperator' E x ∈ Z := by
    intro x hx
    simp only [heightOperator', LinearMap.neg_apply, LinearMap.sum_apply, LinearMap.smul_apply]
    exact Z.neg_mem (Z.sum_mem fun a _ => Z.smul_mem _ (hZ a a x hx))
  let HZ : Module.End K Z := (heightOperator' E).restrict hHZ
  let S : Set ℤ := {h | ∃ ν v, v ∈ Z ∧ v ≠ 0 ∧ v ∈ weightSp E ν ∧ weightHeight' ν = h}
  have hSeig : ∀ h ∈ S, HZ.HasEigenvalue (h : K) := by
    rintro h ⟨ν, v, hvZ, hv0, hvw, rfl⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨v, hvZ⟩) ?_
    rw [Module.End.hasEigenvector_iff]
    refine ⟨Module.End.mem_eigenspace_iff.mpr (Subtype.ext ?_), fun h0 => hv0 (congrArg Subtype.val h0)⟩
    exact v2rep_H_apply E ν v hvw
  have hSfin : S.Finite :=
    ((Module.End.finite_hasEigenvalue HZ).preimage (Int.cast_injective (α := K)).injOn).subset
      fun h hh => hSeig h hh
  obtain ⟨x, hxZ, hx0⟩ := (Submodule.ne_bot_iff Z).mp hne
  have hgr := v2rep_graded E Z (fun a x hx => hZ a a x hx) x hxZ (hw hxZ)
  obtain ⟨ν0, hν0⟩ : ∃ ν, weightSp E ν ⊓ Z ≠ ⊥ := by
    by_contra hc
    push_neg at hc
    simp [hc] at hgr
    exact hx0 hgr
  obtain ⟨v0, hv0m, hv00⟩ := (Submodule.ne_bot_iff _).mp hν0
  have hSne : S.Nonempty := ⟨_, ν0, v0, hv0m.2, hv00, hv0m.1, rfl⟩
  have hTne : hSfin.toFinset.Nonempty := (Set.Finite.toFinset_nonempty hSfin).mpr hSne
  obtain ⟨ν, v, hvZ, hv0, hvw, hht⟩ := (hSfin.mem_toFinset).mp (hSfin.toFinset.max'_mem hTne)
  refine ⟨ν, v, hvZ, hv0, hvw, fun a b hab => ?_⟩
  by_contra hne'
  have hmem : weightHeight' (ν + rootW a b) ∈ S :=
    ⟨ν + rootW a b, E a b v, hZ a b v hvZ, hne', v2rep_shift E hR a b ν v hvw, rfl⟩
  have h1 := hSfin.toFinset.le_max' _ ((hSfin.mem_toFinset).mpr hmem)
  have h2 := v2rep_ht_root ν a b hab
  omega

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem v2rep_Umon_stable (E : GLOps n K V) (W : Submodule K V) (hW : IsStableUnderOperators E W) (u : Module.End K V)
    (hu : u ∈ Umon E) : ∀ x ∈ W, u x ∈ W := by
  induction hu using Submonoid.closure_induction with
  | mem u hu => obtain ⟨⟨a, b⟩, rfl⟩ := hu; exact hW a b
  | one => intro x hx; exact hx
  | mul u v _ _ hu hv => intro x hx; exact hu _ (hv x hx)

theorem v2rep_isoIn_stable (E : GLOps n K V) (W : Submodule K V) (mu : Fin n → ℤ) :
    IsStableUnderOperators E (isotypicPartIn E W mu) := by
  intro a b x hx
  unfold isotypicPartIn at hx ⊢
  have h : Submodule.span K {x | ∃ u ∈ Umon E, ∃ v ∈ W, IsHWV E mu v ∧ x = u v} ≤
      (Submodule.span K {x | ∃ u ∈ Umon E, ∃ v ∈ W, IsHWV E mu v ∧ x = u v}).comap (E a b) := by
    rw [Submodule.span_le]
    rintro y ⟨u, hu, v, hv, hhw, rfl⟩
    exact Submodule.subset_span
      ⟨E a b * u, (Umon E).mul_mem (Submonoid.subset_closure ⟨(a, b), rfl⟩) hu, v, hv, hhw, rfl⟩
  exact h hx

theorem v2rep_iSup_stable (E : GLOps n K V) {ι : Sort*} (p : ι → Submodule K V) (hp : ∀ i, IsStableUnderOperators E (p i)) :
    IsStableUnderOperators E (⨆ i, p i) := by
  intro a b x hx
  exact Submodule.iSup_induction (motive := fun y => E a b y ∈ ⨆ i, p i) p hx
    (fun i y hy => Submodule.mem_iSup_of_mem i (hp i a b y hy))
    (by rw [map_zero]; exact zero_mem _)
    (fun y z hy hz => by rw [map_add]; exact add_mem hy hz)

def restrictToStableSubmodule (E : GLOps n K V) (W : Submodule K V) (hW : IsStableUnderOperators E W) : GLOps n K W :=
  fun a b => (E a b).restrict (hW a b)

theorem v2rep_res_apply (E : GLOps n K V) (W : Submodule K V) (hW : IsStableUnderOperators E W) (a b : Fin n) (x : W) :
    ((restrictToStableSubmodule E W hW a b x : W) : V) = E a b x := rfl

theorem v2rep_res_weightSp (E : GLOps n K V) (W : Submodule K V) (hW : IsStableUnderOperators E W) (mu : Fin n → ℤ) :
    weightSp (restrictToStableSubmodule E W hW) mu = (weightSp E mu).comap W.subtype := by
  ext x
  simp only [weightSp, Submodule.mem_comap, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, Submodule.subtype_apply]
  refine forall_congr' fun a => ?_
  rw [← Submodule.coe_eq_zero, Submodule.coe_sub, Submodule.coe_smul, v2rep_res_apply]
  simp

theorem v2rep_res_isGLRep [CharZero K] (E : GLOps n K V) (hR : SatisfiesGLRelations E) (W : Submodule K V)
    [FiniteDimensional K W] (hW : IsStableUnderOperators E W) (hw : W ≤ ⨆ ν, weightSp E ν) : IsGLRep (restrictToStableSubmodule E W hW) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b c d
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have h := v2rep_comm E hR a b c d (x : V)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, v2rep_res_apply]
    rw [h, add_sub_cancel_left]
    congr 1
    · split_ifs <;> simp [v2rep_res_apply]
    · split_ifs <;> simp [v2rep_res_apply]
  · intro x
    exact ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ _ _ => Submodule.mem_top⟩
  · rw [eq_top_iff]
    intro y _
    have h1 := v2rep_graded E W (fun a => hW a a) y y.2 (hw y.2)
    have h2 : (⨆ ν, weightSp E ν ⊓ W) = (⨆ ν, weightSp (restrictToStableSubmodule E W hW) ν).map W.subtype := by
      rw [Submodule.map_iSup]
      refine iSup_congr fun ν => ?_
      rw [v2rep_res_weightSp, Submodule.map_comap_subtype, inf_comm]
    rw [h2] at h1
    obtain ⟨y', hy', hyy⟩ := Submodule.mem_map.1 h1
    have : y' = y := Subtype.ext hyy
    rwa [this] at hy'

theorem stable_subspace_complete_reducibility (D : Formalism.BasicNotions.D7) (h2 : adm2 D) : StableSubspaceCompleteReducibility := by
  intro K V _ _ _ _ n E hR W hfd hW hw
  have := hfd
  set W' : Submodule K V := ⨆ mu, isotypicPartIn E W mu with hW'
  have hW'st : IsStableUnderOperators E W' := v2rep_iSup_stable E _ fun mu => v2rep_isoIn_stable E W mu
  obtain ⟨P2, hcompl, hP2⟩ := h2 K W n (restrictToStableSubmodule E W hW) (v2rep_res_isGLRep E hR W hW hw)
    (W'.comap W.subtype) (fun a b x hx => hW'st a b x hx)
  have hbot : P2 = ⊥ := by
    by_contra hne
    let Z : Submodule K V := P2.map W.subtype
    have hZW : Z ≤ W := by
      rintro _ ⟨y, _, rfl⟩
      exact y.2
    have : FiniteDimensional K Z := Submodule.finiteDimensional_of_le hZW
    have hZst : IsStableUnderOperators E Z := by
      rintro a b _ ⟨y, hy, rfl⟩
      exact ⟨restrictToStableSubmodule E W hW a b y, hP2 a b y hy, rfl⟩
    have hZne : Z ≠ ⊥ := by
      intro h
      obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      have h5 : (y : V) ∈ Z := ⟨y, hy, rfl⟩
      rw [h] at h5
      exact hy0 (Subtype.ext h5)
    obtain ⟨mu, v, hvZ, hhw⟩ := v2rep_exists_hwv E hR Z hZst (hZW.trans hw) hZne
    obtain ⟨y, hy, rfl⟩ := hvZ
    have h1 : (y : V) ∈ W' :=
      Submodule.mem_iSup_of_mem mu (Submodule.subset_span ⟨1, Submonoid.one_mem _, y, y.2, hhw, rfl⟩)
    have h3 : y ∈ (W'.comap W.subtype) ⊓ P2 := ⟨h1, hy⟩
    rw [hcompl.inf_eq_bot] at h3
    have h4 : y = 0 := h3
    exact hhw.1 (by rw [h4]; rfl)
  have htop : W'.comap W.subtype = ⊤ := by
    have := hcompl.sup_eq_top
    rwa [hbot, sup_bot_eq] at this
  intro x hx
  have : (⟨x, hx⟩ : W) ∈ W'.comap W.subtype := by rw [htop]; exact Submodule.mem_top
  exact this

end Formalism.MainNotions.G.GLWeightTheory
