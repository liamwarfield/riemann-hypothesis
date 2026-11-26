module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.KhwLowKSubRootEqZero

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.ConeNorm
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

theorem cone_norm_dot_root {n : ℕ} (l : Fin n → ℝ) (a b : Fin n) (c : ℝ) :
    ∑ i, l i * (c • root a b) i = c * (l a - l b) := by
  unfold root
  simp [Pi.single_apply, mul_sub, Finset.sum_sub_distrib]
  try ring

theorem cone_norm_dot_nonneg {n : ℕ} (l β : Fin n → ℝ) (hl : Antitone l) (hβ : InRootCone β) :
    0 ≤ dot l β := by
  unfold dot
  obtain ⟨m, rfl⟩ := hβ
  have hsw : ∑ i, l i * (∑ a, ∑ b, if a < b then (m a b : ℝ) • root a b else 0) i
      = ∑ a, ∑ b, ∑ i, l i * ((if a < b then (m a b : ℝ) • root a b else 0) i) := by
    simp only [Finset.sum_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
  rw [hsw]
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  split_ifs with hab
  · rw [cone_norm_dot_root]
    exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (hl hab.le))
  · simp

theorem cone_norm_eq_zero {n : ℕ} (β : Fin n → ℝ) (h : nsq β ≤ 0) : β = 0 := by
  unfold nsq dot at h
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ β i * β i := fun i _ => mul_self_nonneg _
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp (le_antisymm h (Finset.sum_nonneg hnn))
  funext i
  exact mul_self_eq_zero.mp (h0 i (Finset.mem_univ _))

theorem cone_norm (n : ℕ) : ConeNormStatement n := by
  intro lam β hl hβ h
  apply cone_norm_eq_zero
  have hd := cone_norm_dot_nonneg lam β hl hβ
  have hexp : nsq (lam + β) = nsq lam + 2 * dot lam β + nsq β := by
    unfold nsq dot
    simp only [Pi.add_apply]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  linarith

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.CasimirTensVd
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS Finset

namespace TensK

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem tensV_apply' (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensV E a b f c = E a b (f c) + (if c = a then f b else 0) := by
  by_cases h : c = a <;> simp [tensV, prj, h]

theorem tensVd_apply' (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensVd E a b f c = E a b (f c) - (if c = b then f a else 0) := by
  by_cases h : c = b <;> simp [tensVd, prj, h]

theorem eeV_apply' (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (d : Fin n) :
    eeV E f d = ∑ c, E c d (f c) := by
  simp [eeV, prj, LinearMap.sum_apply]

theorem eeVd_apply' (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (d : Fin n) :
    eeVd E f d = -∑ c, E d c (f c) := by
  simp [eeVd, prj, LinearMap.sum_apply]

theorem casimir_apply' (E : Fin n → Fin n → Module.End ℂ M) (x : M) :
    casimir E x = ∑ a, ∑ b, E a b (E b a x) := by
  simp [casimir, LinearMap.sum_apply, Module.End.mul_apply]

theorem isGlRep_tensV (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) : IsGlRep (tensV E) := by
  intro a b c d
  refine LinearMap.ext fun f => funext fun e => ?_
  have key := LinearMap.congr_fun (hE a b c d) (f e)
  have key' : E a b (E c d (f e)) = E c d (E a b (f e)) +
      ((if b = c then E a d (f e) else 0) - (if d = a then E c b (f e) else 0)) := by
    by_cases h3 : b = c <;> by_cases h4 : d = a <;>
      simp only [h3, h4, if_true, if_false, LinearMap.sub_apply, Module.End.mul_apply,
        LinearMap.zero_apply] at key ⊢ <;> rw [← key] <;> abel
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply,
    tensV_apply', map_add, apply_ite (E a b), apply_ite (E c d), map_zero, key']
  by_cases h3 : b = c <;> by_cases h4 : d = a <;>
    simp only [h3, h4, if_true, if_false, LinearMap.zero_apply, Pi.zero_apply, tensV_apply'] <;>
    split_ifs <;> subst_vars <;> (try simp) <;> first | exact absurd rfl h4 | exact absurd rfl h3 | abel

theorem isGlRep_tensVd (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) : IsGlRep (tensVd E) := by
  intro a b c d
  refine LinearMap.ext fun f => funext fun e => ?_
  have key := LinearMap.congr_fun (hE a b c d) (f e)
  have key' : E a b (E c d (f e)) = E c d (E a b (f e)) +
      ((if b = c then E a d (f e) else 0) - (if d = a then E c b (f e) else 0)) := by
    by_cases h3 : b = c <;> by_cases h4 : d = a <;>
      simp only [h3, h4, if_true, if_false, LinearMap.sub_apply, Module.End.mul_apply,
        LinearMap.zero_apply] at key ⊢ <;> rw [← key] <;> abel
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply,
    tensVd_apply', map_sub, apply_ite (E a b), apply_ite (E c d), map_zero, key']
  by_cases h3 : b = c <;> by_cases h4 : d = a <;>
    simp only [h3, h4, if_true, if_false, LinearMap.zero_apply, Pi.zero_apply, tensVd_apply'] <;>
    split_ifs <;> subst_vars <;> (try simp) <;> first | exact absurd rfl h4 | exact absurd rfl h3 | abel

theorem casimir_tensV' (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) :
    casimir (tensV E) f = (fun c => casimir E (f c)) + (n : ℂ) • f + (2 : ℂ) • eeV E f := by
  funext e
  simp only [casimir_apply', Finset.sum_apply, tensV_apply', map_add (f := _), apply_ite (E _ _), map_zero,
    Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply, eeV_apply', if_true, ite_add_zero]
  simp [Finset.sum_ite_eq, Finset.sum_ite_irrel, two_smul]
  rw [Nat.cast_smul_eq_nsmul]
  abel

theorem casimir_tensVd' (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) :
    casimir (tensVd E) f = (fun c => casimir E (f c)) + (n : ℂ) • f + (2 : ℂ) • eeVd E f := by
  funext e
  simp only [casimir_apply', Finset.sum_apply, tensVd_apply', map_sub, apply_ite (E _ _), map_zero,
    Finset.sum_sub_distrib, Pi.add_apply, Pi.smul_apply, eeVd_apply', if_true]
  simp [Finset.sum_ite_eq, Finset.sum_ite_irrel, two_smul]
  rw [Nat.cast_smul_eq_nsmul]
  abel

end TensK

theorem tens_statement (n : ℕ) : TensStatement n := by
  intro M _ _ E hE
  exact ⟨TensK.isGlRep_tensV E hE, TensK.isGlRep_tensVd E hE, TensK.casimir_tensV' E, TensK.casimir_tensVd' E⟩

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.SingleSmulFin
noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

section GeneratorMatrix

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

private lemma le_genSub_self (E : Fin n → Fin n → Module.End ℂ M) (S : Submodule ℂ M) : S ≤ genSub E S := by
  exact le_sInf fun T hT => hT.1

private lemma genSub_stable (E : Fin n → Fin n → Module.End ℂ M) (S : Submodule ℂ M) (a b : Fin n) {v : M}
    (hv : v ∈ genSub E S) : E a b v ∈ genSub E S := by
  exact Submodule.mem_sInf.2 fun T hT => hT.2 a b v (Submodule.mem_sInf.1 hv T hT)

private lemma genSub_le_of (E : Fin n → Fin n → Module.End ℂ M) (S T : Submodule ℂ M) (hST : S ≤ T)
    (hT : ∀ a b, ∀ v ∈ T, E a b v ∈ T) : genSub E S ≤ T := by
  exact sInf_le ⟨hST, hT⟩

private lemma single_smul_fin (c : Fin n) (r : ℂ) (x : M) :
    (Pi.single c (r • x) : Fin n → M) = r • Pi.single c x := by
  funext j
  by_cases h : j = c
  · subst h
    simp
  · simp [h]

private lemma gen_generic (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M)
    (T : Fin n → Fin n → Module.End ℂ (Fin n → M))
    (hT : ∀ a b c m, Pi.single c (E a b m) - T a b (Pi.single c m) ∈
        Submodule.span ℂ (Set.range fun x : Fin n => (Pi.single x m : Fin n → M)))
    (f : Fin n → M) (hf : ∀ c, f c ∈ genSub E V) :
    f ∈ genSub T (Submodule.pi Set.univ fun _ => V) := by
  classical
  let G := genSub T (Submodule.pi Set.univ fun _ => V)
  let S : Submodule ℂ M :=
    { carrier := {m | ∀ x, (Pi.single x m : Fin n → M) ∈ G}
      add_mem' := fun {m m'} hm hm' x => by rw [Pi.single_add]; exact G.add_mem (hm x) (hm' x)
      zero_mem' := fun x => by rw [Pi.single_zero]; exact G.zero_mem
      smul_mem' := fun r m hm x => by rw [single_smul_fin]; exact G.smul_mem r (hm x) }
  have hVS : V ≤ S := fun v hv x => le_genSub_self T _ (Submodule.mem_pi.2 fun j _ => by
    by_cases h : j = x
    · subst h
      simpa using hv
    · simp [h])
  have hSS : ∀ a b, ∀ m ∈ S, E a b m ∈ S := by
    intro a b m hm x
    have h2 : Submodule.span ℂ (Set.range fun y : Fin n => (Pi.single y m : Fin n → M)) ≤ G :=
      Submodule.span_le.2 (by rintro _ ⟨y, rfl⟩; exact hm y)
    have h3 := G.add_mem (h2 (hT a b x m)) (genSub_stable T _ a b (hm x))
    simpa using h3
  have hle := genSub_le_of E V S hVS hSS
  rw [← Finset.univ_sum_single f]
  exact G.sum_mem fun c _ => hle (hf c) c

private lemma tensV_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (m : M) :
    tensV E a b (Pi.single c m) = Pi.single c (E a b m) + (if b = c then Pi.single a m else 0) := by
  funext c'
  simp only [tensV, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.comp_apply, prj, LinearMap.proj_apply,
    Pi.add_apply]
  by_cases h2 : c' = a <;> by_cases h1 : c' = c <;> by_cases h3 : b = c <;>
    simp_all [Pi.single_apply, ite_apply]

private lemma tensVd_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (m : M) :
    tensVd E a b (Pi.single c m) = Pi.single c (E a b m) - (if a = c then Pi.single b m else 0) := by
  funext c'
  simp only [tensVd, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply, prj, LinearMap.proj_apply,
    Pi.sub_apply]
  by_cases h2 : c' = b <;> by_cases h1 : c' = c <;> by_cases h3 : a = c <;>
    simp_all [Pi.single_apply, ite_apply]

end GeneratorMatrix

theorem gen_statement (n : ℕ) : GenStatement n := by
  intro ε M _ _ E V _ _
  refine ⟨fun f hf => gen_generic E V (tensV E) (fun a b c m => ?_) f hf,
    fun f hf => gen_generic E V (tensVd E) (fun a b c m => ?_) f hf⟩
  · rw [tensV_single, sub_add_cancel_left]
    split_ifs
    · exact neg_mem (Submodule.subset_span ⟨a, rfl⟩)
    · simp
  · rw [tensVd_single, sub_sub_cancel]
    split_ifs
    · exact Submodule.subset_span ⟨b, rfl⟩
    · exact zero_mem _

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end
