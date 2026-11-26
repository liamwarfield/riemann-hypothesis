module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SelfDualMap
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanExists
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LeviActionCommutesWithTotalBoundary
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.JacquetBasis

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LevelWeightSumBound
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LevelWeightSumBound
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

namespace GlobalTheory.CompanionTheory.RgCOBlock.ClusterBound

theorem card_first_le {n : ℕ} (A : Finset (Pos n)) (c : Fin n) :
    (A.filter fun i => i.1.1 = c).card ≤ n := by
  have h : (A.filter fun i => i.1.1 = c).card ≤ (univ : Finset (Fin n)).card :=
    Finset.card_le_card_of_injOn (fun i => i.1.2) (fun _ _ => mem_univ _) (by
      intro x hx y hy hxy
      have h1 := (mem_filter.1 (mem_coe.1 hx)).2
      have h2 := (mem_filter.1 (mem_coe.1 hy)).2
      exact Subtype.ext (Prod.ext (h1.trans h2.symm) hxy))
  simpa using h

theorem card_second_le {n : ℕ} (A : Finset (Pos n)) (c : Fin n) :
    (A.filter fun i => i.1.2 = c).card ≤ n := by
  have h : (A.filter fun i => i.1.2 = c).card ≤ (univ : Finset (Fin n)).card :=
    Finset.card_le_card_of_injOn (fun i => i.1.1) (fun _ _ => mem_univ _) (by
      intro x hx y hy hxy
      have h1 := (mem_filter.1 (mem_coe.1 hx)).2
      have h2 := (mem_filter.1 (mem_coe.1 hy)).2
      exact Subtype.ext (Prod.ext hxy (h1.trans h2.symm)))
  simpa using h

theorem abs_wt_le {n : ℕ} (A : Finset (Pos n)) (c : Fin n) : |wt A c| ≤ n := by
  have h1 : (((A.filter fun i => i.1.1 = c).card : ℕ) : ℝ) ≤ n := by
    exact_mod_cast card_first_le A c
  have h2 : (((A.filter fun i => i.1.2 = c).card : ℕ) : ℝ) ≤ n := by
    exact_mod_cast card_second_le A c
  have h3 : (0 : ℝ) ≤ ((A.filter fun i => i.1.1 = c).card : ℕ) := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ ((A.filter fun i => i.1.2 = c).card : ℕ) := Nat.cast_nonneg _
  unfold wt
  rw [abs_le]
  constructor <;> linarith

theorem abs_two_rhoC_le {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    |(2 : ℝ) * PI.UpqRep.rhoC ε a| ≤ n := by
  have h1 : (((univ.filter fun b => a < b ∧ ε b = ε a).card : ℕ) : ℝ) ≤ n := by
    exact_mod_cast (card_le_univ _).trans_eq (Fintype.card_fin n)
  have h2 : (((univ.filter fun b => b < a ∧ ε b = ε a).card : ℕ) : ℝ) ≤ n := by
    exact_mod_cast (card_le_univ _).trans_eq (Fintype.card_fin n)
  have h3 : (0 : ℝ) ≤ ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℕ) := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℕ) := Nat.cast_nonneg _
  unfold PI.UpqRep.rhoC
  rw [abs_le]
  constructor <;> linarith

theorem abs_modExp_le {M N : ℕ} (d : Fin M → ℕ) (h : ∑ j, d j = N) (i : Fin M) :
    |modExp (fun j => Fin (d j)) i| ≤ (N : ℤ) := by
  have hN : ∑ j, (d j : ℤ) = N := by exact_mod_cast h
  have key : ∀ p : Fin M → Prop, ∀ [DecidablePred p],
      (0 : ℤ) ≤ ∑ b with p b, (d b : ℤ) ∧ ∑ b with p b, (d b : ℤ) ≤ N := fun p _ =>
    ⟨sum_nonneg fun _ _ => Int.natCast_nonneg _, hN ▸ sum_le_sum_of_subset_of_nonneg
      (filter_subset _ _) fun _ _ _ => Int.natCast_nonneg _⟩
  obtain ⟨a1, a2⟩ := key (fun b => i < b)
  obtain ⟨b1, b2⟩ := key (fun b => b < i)
  simp only [modExp, Fintype.card_fin]
  rw [abs_le]
  constructor <;> linarith

end GlobalTheory.CompanionTheory.RgCOBlock.ClusterBound

namespace GlobalTheory.CompanionTheory.RgCOBlock

theorem norm_cluster_sum_le (n M : ℕ) (ε : Fin n → Bool) (lev : Fin n → ℕ) (i : Fin M) (h : ∑ j, sz lev M j = n) :
    ‖∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)), ((wt (omU ε lev) a - (2 : ℝ) * PI.UpqRep.rhoC ε a : ℝ) : ℂ) -
      ((sz lev M i : ℂ) * ((modExp (fun j => Fin (sz lev M j)) i : ℂ) / 2))‖ ≤ 3 * (n : ℝ) ^ 2 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hsz : ((sz lev M i : ℕ) : ℝ) ≤ n := by
    have : sz lev M i ≤ n := (card_le_univ _).trans_eq (Fintype.card_fin n)
    exact_mod_cast this
  have hsz0 : (0 : ℝ) ≤ ((sz lev M i : ℕ) : ℝ) := Nat.cast_nonneg _
  have hm : ((|modExp (fun j => Fin (sz lev M j)) i| : ℤ) : ℝ) ≤ n := by
    exact_mod_cast ClusterBound.abs_modExp_le (sz lev M) h i
  have hm0 : (0 : ℝ) ≤ ((|modExp (fun j => Fin (sz lev M j)) i| : ℤ) : ℝ) := by
    exact_mod_cast abs_nonneg _
  have hterm : ∀ a ∈ univ.filter (fun a => lev a = (i : ℕ)),
      ‖((wt (omU ε lev) a - (2 : ℝ) * PI.UpqRep.rhoC ε a : ℝ) : ℂ)‖ ≤ 2 * (n : ℝ) := by
    intro a _
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h1 := ClusterBound.abs_wt_le (omU ε lev) a
    have h2 := ClusterBound.abs_two_rhoC_le ε a
    have h3 := abs_sub (wt (omU ε lev) a) ((2 : ℝ) * PI.UpqRep.rhoC ε a)
    linarith
  have hsum : ‖∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)),
      ((wt (omU ε lev) a - (2 : ℝ) * PI.UpqRep.rhoC ε a : ℝ) : ℂ)‖ ≤
      ((sz lev M i : ℕ) : ℝ) * (2 * (n : ℝ)) := by
    refine (norm_sum_le_of_le _ hterm).trans_eq ?_
    rw [sum_const, nsmul_eq_mul]
    rfl
  have hmod : ‖(sz lev M i : ℂ) * ((modExp (fun j => Fin (sz lev M j)) i : ℂ) / 2)‖ =
      ((sz lev M i : ℕ) : ℝ) * (((|modExp (fun j => Fin (sz lev M j)) i| : ℤ) : ℝ) / 2) := by
    rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_intCast]
    simp
  refine (norm_sub_le _ _).trans ?_
  rw [hmod]
  have e1 : ((sz lev M i : ℕ) : ℝ) * (2 * (n : ℝ)) ≤ (n : ℝ) * (2 * n) :=
    mul_le_mul_of_nonneg_right hsz (by positivity)
  have e2 : ((sz lev M i : ℕ) : ℝ) * (((|modExp (fun j => Fin (sz lev M j)) i| : ℤ) : ℝ) / 2) ≤
      (n : ℝ) * ((n : ℝ) / 2) :=
    mul_le_mul hsz (by linarith) (by linarith) hn
  nlinarith [sq_nonneg (n : ℝ)]

end GlobalTheory.CompanionTheory.RgCOBlock
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LevelWeightSumBoundStatement
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_weight_sum_bound : ∀ (n M : ℕ) (ε : Fin n → Bool) (lev : Fin n → ℕ) (i : Fin M) (h : ∑ j, sz lev M j = n),
    ‖∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)), ((wt (omU ε lev) a - (2 : ℝ) * PI.UpqRep.rhoC ε a : ℝ) : ℂ) -
      ((sz lev M i : ℂ) * ((modExp (fun j => Fin (sz lev M j)) i : ℂ) / 2))‖ ≤ 3 * (n : ℝ) ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.RgCOBlock.norm_cluster_sum_le | exact GlobalTheory.CompanionTheory.RgCOBlock.norm_cluster_sum_le | (intros; apply GlobalTheory.CompanionTheory.RgCOBlock.norm_cluster_sum_le <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HighestWeightClassBoundaryAndWeight
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HighestWeightClassBoundaryAndWeight
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

noncomputable section

namespace GlobalTheory.CompanionTheory.RgCOBlock.TopU

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem ann_app (i : Pos n) (x : Cn n V) (B : Finset (Pos n)) :
    ann i x B = if i ∈ B then 0 else CompanionTheory.D.LK.sg i B • x (insert i B) := rfl

theorem cre_app (i : Pos n) (x : Cn n V) (B : Finset (Pos n)) :
    cre i x B = if i ∈ B then CompanionTheory.D.LK.sg i B • x (B.erase i) else 0 := rfl

theorem sg_erase (i : Pos n) (B : Finset (Pos n)) : CompanionTheory.D.LK.sg i (B.erase i) = CompanionTheory.D.LK.sg i B := by
  unfold CompanionTheory.D.LK.sg
  congr 2
  ext j
  simp only [mem_filter, mem_erase]
  constructor
  · exact fun h => ⟨h.1.2, h.2⟩
  · exact fun h => ⟨⟨fun e => by subst e; exact lt_irrefl _ h.2, h.1⟩, h.2⟩

theorem sg_sq (i : Pos n) (B : Finset (Pos n)) : CompanionTheory.D.LK.sg i B * CompanionTheory.D.LK.sg i B = 1 := by
  unfold CompanionTheory.D.LK.sg; rw [← pow_add, ← two_mul, pow_mul]; simp

theorem cre_ann (i : Pos n) (x : Cn n V) (B : Finset (Pos n)) :
    cre i (ann i x) B = if i ∈ B then x B else 0 := by
  rw [cre_app]
  split_ifs with h
  · rw [ann_app, if_neg (notMem_erase i B), insert_erase h, sg_erase, smul_smul, sg_sq, one_smul]
  · rfl

theorem adC_self (a : Fin n) (i k : Pos n) :
    adC a a i k = if k = i then ((if i.1.1 = a then 1 else 0) - (if i.1.2 = a then 1 else 0) : ℂ) else 0 := by
  unfold adC
  have e1 : (a = i.1.1 ∧ k.1 = (a, i.1.2)) ↔ (k = i ∧ i.1.1 = a) := by
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨Subtype.ext (h2.trans (Prod.ext h1 rfl)), h1.symm⟩
    · rintro ⟨rfl, h⟩; exact ⟨h.symm, Prod.ext h rfl⟩
  have e2 : (i.1.2 = a ∧ k.1 = (i.1.1, a)) ↔ (k = i ∧ i.1.2 = a) := by
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨Subtype.ext (h2.trans (Prod.ext rfl h1.symm)), h1⟩
    · rintro ⟨rfl, h⟩; exact ⟨h, Prod.ext rfl h⟩
  simp only [e1, e2]
  by_cases hk : k = i <;> simp [hk]

theorem adL_self_apply (a : Fin n) (x : Cn n V) (B : Finset (Pos n)) :
    adL a a x B = ∑ i : Pos n, (((if i.1.1 = a then 1 else 0) - (if i.1.2 = a then 1 else 0) : ℂ)) •
      cre i (ann i x) B := by
  simp only [adL, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, Module.End.mul_apply,
    adC_self]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk; simp [hk]
  · simp

theorem top_cycle_weight : ∀ (n : ℕ) (ε : Fin n → Bool) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (γ : Fin n → ℝ) (u : V), Monotone lev → KHighest ε E γ u →
    bd (allT n) E (Pi.single (omU ε lev) u) = 0 ∧
    ∀ a, lF E a a (Pi.single (omU ε lev) u) = (((γ a + wt (omU ε lev) a : ℝ)) : ℂ) • (Pi.single (omU ε lev) u : Cn n V) := by
  intro n ε lev V _ _ E γ u _ hu
  have memA : ∀ i : Pos n, i ∈ omU ε lev ↔ ε i.1.1 = ε i.1.2 ∧ lev i.1.1 < lev i.1.2 := fun i => by simp [omU]
  refine ⟨?_, fun a => ?_⟩
  · funext B
    rw [CompanionTheory.D.LK.bd_apply, Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero, Pi.zero_apply]
    · refine fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
      split_ifs with ht
      · by_contra h
        obtain ⟨h1, -, -, h4⟩ := CompanionTheory.D.LK.tri_ne h
        have e : insert i (insert j (B.erase k)) = omU ε lev := by
          by_contra h'; exact h4 (Pi.single_eq_of_ne h' _)
        have ci := (memA i).1 (e ▸ mem_insert_self _ _)
        have cj := (memA j).1 (e ▸ mem_insert_of_mem (mem_insert_self _ _))
        obtain ⟨-, -, t1, t2, t3⟩ := ht
        have ck : k ∈ omU ε lev := (memA k).2
          ⟨by rw [t2, t3, ci.1, t1]; exact cj.1,
           by rw [t2, t3]; exact (ci.2.trans_eq (congrArg lev t1)).trans cj.2⟩
        rw [← e] at ck
        have pi := i.2
        have pj := j.2
        rcases mem_insert.1 ck with h | h
        · subst h; rw [← t1, t3] at pj; exact lt_irrefl _ pj
        · rcases mem_insert.1 h with h | h
          · subst h; rw [← t2, t1] at pi; exact lt_irrefl _ pi
          · exact notMem_erase _ _ h
      · rfl
    · intro i _
      rw [if_pos rfl, ann_app]
      split_ifs with hi
      · exact map_zero _
      · by_cases e : insert i B = omU ε lev
        · have hiA := (memA i).1 (e ▸ mem_insert_self i B)
          rw [e, Pi.single_eq_same, map_smul, hu.2 _ _ i.2 hiA.1, smul_zero]
        · rw [Pi.single_eq_of_ne e, smul_zero, map_zero]
  · funext B
    show E a a ((Pi.single (omU ε lev) u : Cn n V) B) + adL a a (Pi.single (omU ε lev) u) B = _
    rw [adL_self_apply]
    simp only [cre_ann]
    by_cases e : B = omU ε lev
    · subst e
      rw [Pi.single_eq_same, hu.1 a, Pi.smul_apply, Pi.single_eq_same]
      have hs : ∀ i : Pos n, ((if i.1.1 = a then 1 else 0) - (if i.1.2 = a then 1 else 0) : ℂ) •
          (if i ∈ omU ε lev then u else 0) =
          (if i ∈ omU ε lev then ((if i.1.1 = a then 1 else 0) - (if i.1.2 = a then 1 else 0) : ℂ) else 0) • u := by
        intro i; split_ifs <;> simp
      rw [Finset.sum_congr rfl fun i _ => hs i, ← Finset.sum_smul, ← add_smul]
      congr 1
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, univ_inter, Finset.sum_sub_distrib, Finset.sum_boole,
        Finset.sum_boole]
      simp only [wt]
      push_cast
      ring
    · simp [Pi.single_eq_of_ne e]

end GlobalTheory.CompanionTheory.RgCOBlock.TopU
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HighestWeightClassBoundaryAndWeightStatement
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highest_weight_class_boundary_and_weight : ∀ (n : ℕ) (ε : Fin n → Bool) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (γ : Fin n → ℝ) (u : V), Monotone lev → KHighest ε E γ u →
    bd (allT n) E (Pi.single (omU ε lev) u) = 0 ∧
    ∀ a, lF E a a (Pi.single (omU ε lev) u) = (((γ a + wt (omU ε lev) a : ℝ)) : ℂ) • (Pi.single (omU ε lev) u : Cn n V) := by
  first | exact @GlobalTheory.CompanionTheory.RgCOBlock.TopU.top_cycle_weight | exact GlobalTheory.CompanionTheory.RgCOBlock.TopU.top_cycle_weight | (intros; apply GlobalTheory.CompanionTheory.RgCOBlock.TopU.top_cycle_weight <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FiniteTypeAlgebraCommonEigencharacter
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FiniteTypeAlgebraCommonEigencharacter
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

namespace GlobalTheory.CompanionTheory.RgCOBlock

theorem exists_character_of_smul_ne_zero :
    ∀ (R : Type) [CommRing R] [Algebra ℂ R] [Algebra.FiniteType ℂ R] (W : Type) [AddCommGroup W]
      [Module ℂ W] [Module R W] [IsScalarTower ℂ R W] (t : W), t ≠ 0 →
      ∃ φ : R →ₐ[ℂ] ℂ, ∀ (r : R) (c : ℂ), r • t = c • t → φ r = c := by
  intro R _ _ _ W _ _ _ _ t ht
  let J : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R W t)
  have hmemJ : ∀ x : R, x ∈ J ↔ x • t = 0 := fun x => by
    simp [J, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
  have hJ : J ≠ ⊤ := by
    intro h
    have h1 : (1 : R) ∈ J := h ▸ Submodule.mem_top
    exact ht (by simpa using (hmemJ 1).1 h1)
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJ
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType ℂ (R ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ m) (Ideal.Quotient.mkₐ_surjective ℂ m)
  haveI : Module.Finite ℂ (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (R ⧸ m)
  have bij : Function.Bijective (algebraMap ℂ (R ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : ℂ ≃ₐ[ℂ] R ⧸ m := AlgEquiv.ofBijective (Algebra.ofId ℂ (R ⧸ m)) bij
  refine ⟨(e.symm : (R ⧸ m) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ m), fun r c h => ?_⟩
  have hmem : r - algebraMap ℂ R c ∈ J := by
    rw [hmemJ, sub_smul, algebraMap_smul, h, sub_self]
  have hq : Ideal.Quotient.mkₐ ℂ m r = algebraMap ℂ (R ⧸ m) c := by
    have h0 : Ideal.Quotient.mk m (r - algebraMap ℂ R c) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (hJm hmem)
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  have he : e c = algebraMap ℂ (R ⧸ m) c := rfl
  show e.symm (Ideal.Quotient.mkₐ ℂ m r) = c
  rw [hq, ← he, AlgEquiv.symm_apply_apply]

end GlobalTheory.CompanionTheory.RgCOBlock
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FiniteTypeAlgebraCommonEigencharacterStatement
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_type_algebra_common_eigencharacter : ∀ (R : Type) [CommRing R] [Algebra ℂ R] [Algebra.FiniteType ℂ R] (W : Type) [AddCommGroup W] [Module ℂ W] [Module R W] [IsScalarTower ℂ R W] (t : W), t ≠ 0 → ∃ φ : R →ₐ[ℂ] ℂ, ∀ (r : R) (c : ℂ), r • t = c • t → φ r = c := by
  first | exact @GlobalTheory.CompanionTheory.RgCOBlock.exists_character_of_smul_ne_zero | exact GlobalTheory.CompanionTheory.RgCOBlock.exists_character_of_smul_ne_zero | (intros; apply GlobalTheory.CompanionTheory.RgCOBlock.exists_character_of_smul_ne_zero <;> assumption)
end
end

noncomputable section

namespace GlobalTheory.CompanionTheory.RgCOBlock

open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

theorem sub_char {W : Type} [AddCommGroup W] [Module ℂ W] (R : Subalgebra ℂ (Module.End ℂ W))
    (hc : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x) (hfg : R.FG) (t : W) (ht : t ≠ 0) :
    ∃ f : Module.End ℂ W → ℂ, f 1 = 1 ∧ (∀ x ∈ R, ∀ y ∈ R, f (x + y) = f x + f y ∧ f (x * y) = f x * f y) ∧
      (∀ x ∈ R, ∀ c : ℂ, f (c • x) = c * f x) ∧ ∀ x ∈ R, ∀ c : ℂ, x t = c • t → f x = c := by
  classical
  letI cr : CommRing R := { (inferInstance : Ring R) with
    mul_comm := fun x y => Subtype.ext (hc x x.2 y y.2) }
  haveI : Algebra.FiniteType ℂ R := (Subalgebra.fg_iff_finiteType R).1 hfg
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.finite_type_algebra_common_eigencharacter R W t ht
  refine ⟨fun x => if h : x ∈ R then φ ⟨x, h⟩ else 0, ?_, ?_, ?_, ?_⟩
  · simp only [R.one_mem, dite_eq_left]
    exact map_one φ
  · intro x hx y hy
    simp only [hx, hy, R.add_mem hx hy, R.mul_mem hx hy, dite_eq_left]
    exact ⟨map_add φ ⟨x, hx⟩ ⟨y, hy⟩, map_mul φ ⟨x, hx⟩ ⟨y, hy⟩⟩
  · intro x hx c
    simp only [hx, R.smul_mem hx c, dite_eq_left]
    exact map_smul φ c ⟨x, hx⟩
  · intro x hx c e
    simp only [hx, dite_eq_left]
    exact hφ ⟨x, hx⟩ c e

theorem L_core : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (t : W) (M : ℕ) (d : Fin M → ℕ)
    (B : ∀ i, Fin (d i) → Fin (d i) → Module.End ℂ W) (s : Fin M → ℂ) (n : ℕ) (χ : Fin n → ℂ) (τ : Fin M → ℂ),
    t ≠ 0 → (∀ i, GlRel (B i)) → (∀ i j, i ≠ j → ∀ p q r v, Commute (B i p q) (B j r v)) →
    (∀ Y : ℂ, (List.ofFn fun i => qdet (B i) (Y + s i)).prod = Formalism.QuantumDeterminants.capP χ Y • (1 : Module.End ℂ W)) →
    (∀ i, (∑ p, B i p p) t = τ i • t) →
    ∃ P : Fin M → ℂ[X], (∀ i, (P i).Monic ∧ (P i).natDegree = d i ∧
        (P i).nextCoeff = τ i - (d i : ℂ) * ((d i : ℂ) - 1) / 2) ∧
      ∀ Y : ℂ, ∏ i, (P i).eval (Y + s i) = Formalism.QuantumDeterminants.capP χ Y := by
  classical
  intro W _ _ t M d B s n χ τ ht hGl hCm hcap htr
  obtain ⟨c, c1, c2, c3, c4⟩ := GlobalTheory.T.quantum_determinant_coefficients_expansion W M d B hGl hCm
  let S : Finset (Module.End ℂ W) := univ.biUnion fun i => (range (d i + 1)).image (c i)
  have hS : ∀ x ∈ (S : Set (Module.End ℂ W)), ∃ i j, x = c i j := fun x hx => by
    obtain ⟨i, -, hi⟩ := mem_biUnion.1 (Finset.mem_coe.1 hx)
    obtain ⟨j, -, rfl⟩ := mem_image.1 hi
    exact ⟨i, j, rfl⟩
  have hmemS : ∀ i j, j ≤ d i → c i j ∈ Algebra.adjoin ℂ (S : Set (Module.End ℂ W)) := fun i j hj =>
    Algebra.subset_adjoin (Finset.mem_coe.2 (mem_biUnion.2 ⟨i, mem_univ _,
      mem_image.2 ⟨j, mem_range.2 (Nat.lt_succ_of_le hj), rfl⟩⟩))
  set R := Algebra.adjoin ℂ (S : Set (Module.End ℂ W)) with hR
  have hcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := by
    letI := Algebra.isMulCommutative_adjoin ℂ (s := (S : Set (Module.End ℂ W))) (fun a ha b hb _ => by
      obtain ⟨i, j, rfl⟩ := hS a ha
      obtain ⟨k, l, rfl⟩ := hS b hb
      exact c4 i k j l)
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : R) ⟨y, hy⟩)
  obtain ⟨f, f1, f2, f3, f4⟩ := sub_char R hcomm ⟨S, rfl⟩ t ht
  have fsum : ∀ (A : Finset ℕ) (g : ℕ → Module.End ℂ W), (∀ j ∈ A, g j ∈ R) → (∑ j ∈ A, g j) ∈ R ∧
      f (∑ j ∈ A, g j) = ∑ j ∈ A, f (g j) := by
    intro A g
    induction A using Finset.induction_on with
    | empty =>
      intro _
      have h0 := (f3 1 R.one_mem 0)
      simp only [zero_smul, zero_mul] at h0
      rw [sum_empty, sum_empty]; exact ⟨R.zero_mem, h0⟩
    | insert a A ha ih =>
      intro hg
      obtain ⟨i1, i2⟩ := ih fun j hj => hg j (mem_insert_of_mem hj)
      rw [sum_insert ha, sum_insert ha]
      refine ⟨R.add_mem (hg a (mem_insert_self _ _)) i1, ?_⟩
      rw [(f2 _ (hg a (mem_insert_self _ _)) _ i1).1, i2]
  let a : Fin M → ℕ → ℂ := fun i j => f (c i j)
  let P : Fin M → ℂ[X] := fun i => X ^ d i + ∑ j ∈ range (d i), C (a i j) * X ^ j
  have hdeg : ∀ i, (∑ j ∈ range (d i), C (a i j) * X ^ j : ℂ[X]).degree < (d i : WithBot ℕ) := fun i => by
    rw [degree_lt_iff_coeff_zero]
    intro m hm
    simp only [finsetSum_coeff, coeff_C_mul, coeff_X_pow]
    refine Finset.sum_eq_zero fun j hj => ?_
    have : m ≠ j := by have := Finset.mem_range.1 hj; omega
    simp [this]
  have hmon : ∀ i, (P i).Monic := fun i => monic_X_pow_add (hdeg i)
  have hnd : ∀ i, (P i).natDegree = d i := fun i => by
    have : (P i).degree = (d i : WithBot ℕ) := by
      simp only [P]
      rw [degree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact hdeg i), degree_X_pow]
    exact natDegree_eq_of_degree_eq_some this
  have hval : ∀ i (u : ℂ), qdet (B i) u ∈ R ∧ f (qdet (B i) u) = (P i).eval u := fun i u => by
    have hg : ∀ j ∈ range (d i + 1), u ^ j • c i j ∈ R := fun j hj =>
      R.smul_mem (hmemS i j (Nat.lt_succ_iff.1 (mem_range.1 hj))) _
    obtain ⟨m1, m2⟩ := fsum (range (d i + 1)) (fun j => u ^ j • c i j) hg
    rw [c2 i u]
    refine ⟨m1, ?_⟩
    rw [m2, sum_range_succ]
    simp only [P, eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C]
    rw [add_comm]
    congr 1
    · rw [f3 _ (hmemS i _ le_rfl), c1, f1, mul_one]
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [f3 _ (hmemS i j (Finset.mem_range.1 hj).le), mul_comm]
  have hlist : ∀ l : List (Module.End ℂ W), (∀ x ∈ l, x ∈ R) → l.prod ∈ R ∧ f l.prod = (l.map f).prod := by
    intro l
    induction l with
    | nil => intro _; exact ⟨by simpa using R.one_mem, by simpa using f1⟩
    | cons x l ih =>
      intro h
      obtain ⟨i1, i2⟩ := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
      have hx := h x List.mem_cons_self
      rw [List.prod_cons, List.map_cons, List.prod_cons]
      exact ⟨R.mul_mem hx i1, by rw [(f2 _ hx _ i1).2, i2]⟩
  refine ⟨P, fun i => ⟨hmon i, hnd i, ?_⟩, fun Y => ?_⟩
  · by_cases hd : d i = 0
    · have h0 : (∑ p, B i p p) = 0 := by
        refine Finset.sum_eq_zero fun p _ => ?_
        exact absurd p.2 (by omega)
      have : τ i = 0 := by
        have := htr i
        rw [h0, LinearMap.zero_apply] at this
        exact (smul_eq_zero.1 this.symm).resolve_right ht
      have hn0 : (P i).nextCoeff = 0 := by
        rw [Polynomial.nextCoeff, if_pos ((hnd i).trans hd)]
      rw [hn0, this, hd]
      simp
    · have h1 : 1 ≤ d i := Nat.one_le_iff_ne_zero.2 hd
      rw [nextCoeff_of_natDegree_pos (by rw [hnd i]; omega), hnd i]
      have hco : (P i).coeff (d i - 1) = a i (d i - 1) := by
        simp only [P, coeff_add, coeff_X_pow, finsetSum_coeff, coeff_C_mul]
        rw [if_neg (by omega), zero_add, Finset.sum_eq_single (d i - 1)]
        · simp
        · intro b _ hb; simp [Ne.symm hb]
        · intro h; exact absurd (mem_range.2 (by omega)) h
      rw [hco]
      refine f4 _ (hmemS i _ (by omega)) _ ?_
      rw [c3 i h1, LinearMap.sub_apply, htr i, LinearMap.smul_apply, Module.End.one_apply, sub_smul]
  · have e := hlist (List.ofFn fun i => qdet (B i) (Y + s i)) (fun x hx => by
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
      exact (hval i _).1)
    rw [hcap Y] at e
    have e2 : f (Formalism.QuantumDeterminants.capP χ Y • (1 : Module.End ℂ W)) = Formalism.QuantumDeterminants.capP χ Y := by
      rw [f3 _ R.one_mem, f1, mul_one]
    rw [e2, List.map_ofFn, List.prod_ofFn] at e
    rw [e.2]
    exact Finset.prod_congr rfl fun i _ => by simp only [Function.comp]; exact (hval i _).2.symm

theorem L_lF : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), Monotone lev → GlRel E →
    ∀ (x : Cn n V), SuppIn (inU lev) x →
      (∀ p q, lev p = lev q → SuppIn (inU lev) (lF E p q x) ∧
        (∀ j, Deg j x → Deg j (lF E p q x)) ∧ lF E p q (bd (allT n) E x) = bd (allT n) E (lF E p q x)) ∧
      ∀ p q r v, lev p = lev q → lev r = lev v →
        lF E p q (lF E r v x) - lF E r v (lF E p q x) =
          (if q = r then lF E p v x else 0) - (if v = p then lF E r q x else 0) := by
  intro n lev V _ _ E hm hE x hx
  refine ⟨fun p q hpq => ?_, fun p q r v h1 h2 => GlobalTheory.T.levi_action_is_gl_representation n lev V E hm hE x hx p q r v h1 h2⟩
  obtain ⟨a, b⟩ := GlobalTheory.T.levi_action_preserves_support_degree n lev V E hm x hx p q hpq
  exact ⟨a, b, GlobalTheory.T.levi_action_commutes_with_total_boundary n lev V E hm hE x hx p q hpq⟩

theorem coBlock : InjU → GenCOU → COBlock := by
  intro hI hG n
  refine ⟨3 * (n : ℝ) ^ 2, ?_⟩
  intro ε γ lev V _ _ E hE χ hgap hKU hLF hMin hSC ⟨u, hu0, hu⟩
  have hmono : Monotone lev := hgap.2.1
  obtain ⟨M, hM⟩ : ∃ M, ∀ a, lev a < M :=
    ⟨univ.sup lev + 1, fun a => Nat.lt_succ_of_le (Finset.le_sup (f := lev) (mem_univ a))⟩
  have h : ∑ i, sz lev M i = n := GlobalTheory.T.sum_of_level_sizes_eq n M lev hM
  obtain ⟨hlev, hsum⟩ := GlobalTheory.T.standard_blocks_level_sum n M lev h hmono hM
  set s := stdBlocks (sz lev M) h with hs
  have hinj : ∀ (i : Fin M) (p q : Fin (sz lev M i)), s ⟨i, p⟩ = s ⟨i, q⟩ ↔ p = q := fun i p q => by
    rw [s.injective.eq_iff]; simp
  set dg := (omU ε lev).card with hdg
  set Z := cyc lev E dg with hZ
  set B := bdy lev E dg with hB
  have hZs : ∀ k, ∀ z ∈ Z, lL lev E k z ∈ Z := by
    rintro ⟨p, q⟩ z ⟨h1, h2, h3⟩
    by_cases hpq : lev p = lev q
    · obtain ⟨g1, g2, g3⟩ := (L_lF n lev V E hmono hE z h1).1 p q hpq
      simp only [lL, if_pos hpq]
      exact ⟨g1, g2 _ h2, by rw [← g3, h3, map_zero]⟩
    · simp only [lL, if_neg hpq]
      exact Z.zero_mem
  have hBs : ∀ k, ∀ z ∈ B, lL lev E k z ∈ B := by
    rintro ⟨p, q⟩ _ ⟨w, h1, h2, rfl⟩
    by_cases hpq : lev p = lev q
    · obtain ⟨g1, g2, g3⟩ := (L_lF n lev V E hmono hE w h1).1 p q hpq
      simp only [lL, if_pos hpq]
      exact ⟨_, g1, g2 _ h2, g3.symm⟩
    · simp only [lL, if_neg hpq]
      exact B.zero_mem
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.free_algebra_action_on_subquotient (Cn n V) (Fin n × Fin n) (lL lev E) Z B hZs hBs
  have hlift : FreeAlgebra.lift ℂ (lL lev E) = evLc lev E := rfl
  rw [hlift] at hρ
  have hzero : ∀ y, (∀ z : Z, evLc lev E y (z : Cn n V) = 0) → ρ y = 0 := fun y hy => by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun z => ?_)
    obtain ⟨hz, e⟩ := hρ y z
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.zero_apply]
    rw [e]
    have : (⟨evLc lev E y (z : Cn n V), hz⟩ : Z) = 0 := Subtype.ext (hy z)
    rw [this]; rfl
  have hev : ∀ p q, lev p = lev q → ∀ x : Cn n V, evLc lev E (lt p q) x = lF E p q x := fun p q hpq x => by
    simp [evLc, lt, hpq]
  let Xq : ∀ i : Fin M, Fin (sz lev M i) → Fin (sz lev M i) → Module.End ℂ (Z ⧸ B.comap Z.subtype) :=
    fun i p q => ρ (lt (s ⟨i, p⟩) (s ⟨i, q⟩))
  have hsame : ∀ (i j : Fin M) (p : Fin (sz lev M i)) (q : Fin (sz lev M j)), lev (s ⟨i, p⟩) = lev (s ⟨j, q⟩) ↔ i = j :=
    fun i j p q => by rw [hlev, hlev]; exact Fin.val_inj
  have hGl : ∀ i, GlRel (Xq i) := fun i p q r v => by
    have e := hzero (lt (s ⟨i, p⟩) (s ⟨i, q⟩) * lt (s ⟨i, r⟩) (s ⟨i, v⟩) - lt (s ⟨i, r⟩) (s ⟨i, v⟩) * lt (s ⟨i, p⟩) (s ⟨i, q⟩)
      - ((if q = r then lt (s ⟨i, p⟩) (s ⟨i, v⟩) else 0) - (if v = p then lt (s ⟨i, r⟩) (s ⟨i, q⟩) else 0))) (fun z => by
        have g := (L_lF n lev V E hmono hE z z.2.1).2 (s ⟨i, p⟩) (s ⟨i, q⟩) (s ⟨i, r⟩) (s ⟨i, v⟩) ((hsame _ _ _ _).2 rfl) ((hsame _ _ _ _).2 rfl)
        simp only [hinj] at g
        have hll : ∀ (a b : Fin (sz lev M i)), lev (s ⟨i, a⟩) = lev (s ⟨i, b⟩) := fun a b => (hsame _ _ _ _).2 rfl
        by_cases c1 : q = r <;> by_cases c2 : v = p <;>
          simp only [c1, c2, if_true, if_false, map_sub, map_mul, map_zero, LinearMap.sub_apply, Module.End.mul_apply, hev _ _ (hll _ _), LinearMap.zero_apply] at g ⊢ <;>
          simp [g])
    simp only [map_sub, map_mul] at e
    rw [sub_eq_zero] at e
    simp only [Xq]
    rw [e]
    split_ifs <;> simp
  have hCm : ∀ i j, i ≠ j → ∀ p q r v, Commute (Xq i p q) (Xq j r v) := fun i j hij p q r v => by
    have e := hzero (lt (s ⟨i, p⟩) (s ⟨i, q⟩) * lt (s ⟨j, r⟩) (s ⟨j, v⟩) - lt (s ⟨j, r⟩) (s ⟨j, v⟩) * lt (s ⟨i, p⟩) (s ⟨i, q⟩)) (fun z => by
        have g := (L_lF n lev V E hmono hE z z.2.1).2 (s ⟨i, p⟩) (s ⟨i, q⟩) (s ⟨j, r⟩) (s ⟨j, v⟩) ((hsame _ _ _ _).2 rfl) ((hsame _ _ _ _).2 rfl)
        have n1 : s ⟨i, q⟩ ≠ s ⟨j, r⟩ := fun e => hij ((hsame _ _ q r).1 (by rw [e]))
        have n2 : s ⟨j, v⟩ ≠ s ⟨i, p⟩ := fun e => hij ((hsame _ _ p v).1 (by rw [e]))
        rw [if_neg n1, if_neg n2, sub_zero] at g
        simp only [map_sub, map_mul, LinearMap.sub_apply, Module.End.mul_apply, hev _ _ ((hsame _ _ _ _).2 rfl)]
        exact g)
    simp only [map_sub, map_mul] at e
    exact sub_eq_zero.1 e
  have hcap : ∀ Y : ℂ, (List.ofFn fun i => qdet (Xq i) (Y + shift (sz lev M) i)).prod = Formalism.QuantumDeterminants.capP χ Y • (1 : Module.End ℂ (Z ⧸ B.comap Z.subtype)) := fun Y => by
    have e1 : (List.ofFn fun i => qdet (Xq i) (Y + shift (sz lev M) i)).prod = ρ (fb (sz lev M) h Y) := by
      unfold fb
      rw [map_list_prod, List.map_ofFn]
      congr 2
      funext i
      simpa [Function.comp_def, Xq, hs] using (map_qdet ρ _ (Y + shift (sz lev M) i)).symm
    rw [e1]
    refine Submodule.linearMap_qext _ (LinearMap.ext fun z => ?_)
    obtain ⟨hz, e⟩ := hρ (fb (sz lev M) h Y) z
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [e, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    obtain ⟨w, w1, w2, w3⟩ := hG n lev (fa n Y) (fb (sz lev M) h Y) hmono
      (fun V _ _ E hE => GlobalTheory.T.center_action_commutes_levi_difference n M lev (sz lev M) h Y hmono hlev V E hE) V E hE dg z z.2.1 z.2.2.1 z.2.2.2
    have hq : ev E (fa n Y) = Formalism.QuantumDeterminants.capP χ Y • (1 : Module.End ℂ V) := by
      unfold fa
      rw [map_qdet]
      have := hSC Y
      simp only [ev, lt, FreeAlgebra.lift_ι_apply]
      exact this
    rw [hq] at w3
    refine ⟨-w, ?_, ?_, ?_⟩
    · intro A hA i hi; exact w1 A (fun e => hA (by simp [e])) i hi
    · intro A hA; exact w2 A (fun e => hA (by simp [e]))
    · rw [map_neg, ← w3]
      ext A
      simp
  set t : Cn n V := Pi.single (omU ε lev) u with ht
  obtain ⟨tc, tw⟩ := GlobalTheory.T.highest_weight_class_boundary_and_weight n ε lev V E γ u hmono hu
  have tsup : SuppIn (inU lev) t := by
    intro A hA i hi
    have : A = omU ε lev := by
      by_contra hne
      exact hA (by simp [ht, Pi.single_apply, hne])
    subst this
    exact (mem_filter.1 hi).2.2
  have tdeg : Deg dg t := by
    intro A hA
    have : A = omU ε lev := by
      by_contra hne
      exact hA (by simp [ht, Pi.single_apply, hne])
    rw [this]
  let tZ : Z := ⟨t, tsup, tdeg, tc⟩
  let tb : Z ⧸ B.comap Z.subtype := Submodule.Quotient.mk tZ
  have htb : tb ≠ 0 := by
    intro e
    rw [Submodule.Quotient.mk_eq_zero] at e
    obtain ⟨y, y1, y2, y3⟩ := e
    exact hu0 (hI n ε γ lev V E hgap hE hKU hLF hMin u y hu y1 y2 y3)
  let τ : Fin M → ℂ := fun i => ∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)), (((γ a + wt (omU ε lev) a : ℝ)) : ℂ)
  have htr : ∀ i, (∑ p, Xq i p p) tb = τ i • tb := fun i => by
    simp only [LinearMap.sum_apply, τ, ← hsum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun p _ => ?_
    obtain ⟨hz, e⟩ := hρ (lt (s ⟨i, p⟩) (s ⟨i, p⟩)) tZ
    simp only [Xq, tb]
    rw [e, ← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (by simpa [tZ, hev _ _ rfl] using tw (s ⟨i, p⟩))
  obtain ⟨P, hP, hPe⟩ := L_core _ tb M (sz lev M) Xq (shift (sz lev M)) n χ τ htb hGl hCm hcap htr
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.capelli_polynomial_permutation_match n M lev χ P (shift (sz lev M)) hM (fun i => ⟨(hP i).1, (hP i).2.1⟩) hPe
  refine ⟨σ, fun c => ?_⟩
  by_cases hc : c < M
  · have e := hσ ⟨c, hc⟩
    have hb := GlobalTheory.T.level_weight_sum_bound n M ε lev ⟨c, hc⟩ h
    simp only at e hb
    rw [e, (hP _).2.2]
    refine le_of_eq_of_le ?_ hb
    congr 1
    simp only [τ, shift, xv, sz, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    push_cast
    ring
  · have : ∀ a, lev a ≠ c := fun a e => hc (e ▸ hM a)
    simp only [this, Finset.filter_false, Finset.sum_empty, sub_zero, norm_zero]
    positivity

end GlobalTheory.CompanionTheory.RgCOBlock
