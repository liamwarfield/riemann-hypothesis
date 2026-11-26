module

public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MemFiltOfWords

@[expose] public section

section -- merged from CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.KoszulDifferentialAnticommutator
open Finset

noncomputable section

namespace CompanionTheory.D.LK

open Car
open Formalism.REAL hiding KRel
open CompanionTheory.D.DSIC (KRel)

variable {n : ℕ} {ε : Fin n → Bool}

def tc (ε : Fin n → Bool) (i j k : Pos n) : ℂ := if Tri ε i j k then 1 else 0

def cc (ε : Fin n → Bool) (i : Pos n) : ℂ := if cpt ε i then 1 else 0

theorem tri_uniq {i j k k' : Pos n} (h : Tri ε i j k) (h' : Tri ε i j k') : k = k' :=
  Subtype.ext (Prod.ext (h.2.2.2.1.trans h'.2.2.2.1.symm) (h.2.2.2.2.trans h'.2.2.2.2.symm))

theorem sum_tc {M : Type} [AddCommGroup M] [Module ℂ M] (i j : Pos n) (f : Pos n → M) :
    ∑ k, tc ε i j k • f k = if h : cpt ε i ∧ cpt ε j ∧ i.1.2 = j.1.1 then
      f ⟨(i.1.1, j.1.2), i.2.trans (h.2.2 ▸ j.2)⟩ else 0 := by
  split_ifs with h
  · have ht : Tri ε i j ⟨(i.1.1, j.1.2), i.2.trans (h.2.2 ▸ j.2)⟩ := ⟨h.1, h.2.1, h.2.2, rfl, rfl⟩
    rw [Finset.sum_eq_single _ (fun k _ hk => by rw [tc, if_neg fun h' => hk (tri_uniq h' ht), zero_smul]) (by simp),
      tc, if_pos ht, one_smul]
  · exact Finset.sum_eq_zero fun k _ => by rw [tc, if_neg fun h' => h ⟨h'.1, h'.2.1, h'.2.2.1⟩, zero_smul]

theorem tc_assoc (p q r k : Pos n) : ∑ i, tc ε p q i * tc ε i r k = ∑ j, tc ε q r j * tc ε p j k := by
  have h1 := sum_tc (ε := ε) p q (fun i => tc ε i r k)
  have h2 := sum_tc (ε := ε) q r (fun j => tc ε p j k)
  simp only [smul_eq_mul] at h1 h2
  rw [h1, h2]
  obtain ⟨⟨a, b⟩, _⟩ := p
  obtain ⟨⟨b', c⟩, _⟩ := q
  obtain ⟨⟨c', d⟩, _⟩ := r
  simp only [tc, Tri, cpt]
  by_cases hb : b = b'
  · subst hb
    by_cases hc : c = c'
    · subst hc
      simp only [dite_eq_ite]
      cases ε a <;> cases ε b <;> cases ε c <;> cases ε d <;> simp
    · simp [hc]
  · simp [hb]

section Ring

variable {R : Type} [Ring R] [Algebra ℂ R] (E : Fin n → Fin n → R) (an cr : Pos n → R)

theorem self_neg {x : R} (h : x = -x) : x = 0 := by
  have : (2 : ℂ) • x = 0 := by rw [two_smul]; exact add_eq_zero_iff_eq_neg.2 h
  rw [← one_smul ℂ x, ← inv_mul_cancel₀ (two_ne_zero' ℂ), mul_smul, this, smul_zero]

theorem koszul_differential_sq (hE : KRel ε E) (h1 : ∀ a b i, Commute (E a b) (an i)) (haa : ∀ i j, an i * an j + an j * an i = 0) :
    (∑ i, cc ε i • (E i.1.1 i.1.2 * an i)) * (∑ i, cc ε i • (E i.1.1 i.1.2 * an i)) =
      ∑ i, ∑ j, ∑ k, tc ε i j k • (E k.1.1 k.1.2 * (an i * an j)) := by
  set T : Pos n → Pos n → R := fun i j => ∑ k, tc ε i j k • (E k.1.1 k.1.2 * (an i * an j)) with hT
  set U : Pos n → Pos n → R := fun i j => (cc ε i * cc ε j) • (E i.1.1 i.1.2 * E j.1.1 j.1.2 * (an i * an j)) with hU
  have e : (∑ i, cc ε i • (E i.1.1 i.1.2 * an i)) * (∑ i, cc ε i • (E i.1.1 i.1.2 * an i)) = ∑ i, ∑ j, U i j := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm, hU, mul_assoc, ← mul_assoc (an i), ← (h1 _ _ i).eq]
    simp only [mul_assoc]
  have key : ∀ i j, U i j + U j i = T i j + T j i := by
    intro i j
    have ha : an j * an i = -(an i * an j) := eq_neg_of_add_eq_zero_right (haa i j)
    simp only [hT, hU, sum_tc (f := fun k => E k.1.1 k.1.2 * (an i * an j)),
      sum_tc (f := fun k => E k.1.1 k.1.2 * (an j * an i))]
    rw [ha]
    by_cases ci : cpt ε i
    swap
    · simp [cc, ci]
    by_cases cj : cpt ε j
    swap
    · simp [cc, cj]
    have := hE i.1.1 i.1.2 j.1.1 j.1.2 ci cj
    simp only [cc, eq_true ci, eq_true cj, if_true, true_and, mul_one, one_smul, mul_neg, ← sub_eq_add_neg, ← sub_mul, this]
    split_ifs <;> simp [sub_mul, sub_eq_add_neg, add_mul]
  rw [e, ← sub_eq_zero]
  apply self_neg
  rw [eq_neg_iff_add_eq_zero]
  have s1 : ∑ i, ∑ j, U i j = ∑ i, ∑ j, U j i := Finset.sum_comm
  have s2 : ∑ i, ∑ j, T i j = ∑ i, ∑ j, T j i := Finset.sum_comm
  have s3 : ∑ i, ∑ j, U i j + ∑ i, ∑ j, U j i = ∑ i, ∑ j, T i j + ∑ i, ∑ j, T j i := by
    simp only [← Finset.sum_add_distrib, key]
  rw [← s1, ← s2] at s3
  change (∑ i, ∑ j, U i j - ∑ i, ∑ j, T i j) + (∑ i, ∑ j, U i j - ∑ i, ∑ j, T i j) = 0
  rw [sub_add_sub_comm, s3, sub_self]

theorem comm_aa (haa : ∀ i j, an i * an j + an j * an i = 0) (l i j : Pos n) : an j * an i * an l = an l * (an j * an i) := by
  have h : ∀ i j, an i * an j = -(an j * an i) := fun i j => eq_neg_of_add_eq_zero_left (haa i j)
  rw [mul_assoc, h i l, mul_neg, ← mul_assoc, h j l, neg_mul, neg_neg, mul_assoc]

theorem koszul_differential_anticommutator (h1 : ∀ a b i, Commute (E a b) (an i)) (h2 : ∀ a b i, Commute (E a b) (cr i))
    (haa : ∀ i j, an i * an j + an j * an i = 0) (hac : ∀ i j, an i * cr j + cr j * an i = if i = j then 1 else 0) :
    (∑ i, cc ε i • (E i.1.1 i.1.2 * an i)) * (∑ i, ∑ j, ∑ k, tc ε i j k • (cr k * an j * an i)) +
      (∑ i, ∑ j, ∑ k, tc ε i j k • (cr k * an j * an i)) * (∑ i, cc ε i • (E i.1.1 i.1.2 * an i)) =
      -∑ i, ∑ j, ∑ k, tc ε i j k • (E k.1.1 k.1.2 * (an i * an j)) := by
  simp only [Finset.mul_sum (s := univ) (f := fun i => ∑ j, ∑ k, tc ε i j k • (cr k * an j * an i)),
    Finset.sum_mul (s := univ) (f := fun i => ∑ j, ∑ k, tc ε i j k • (cr k * an j * an i)),
    ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, ← smul_add, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  have e : ∀ l : Pos n, cc ε l • (E l.1.1 l.1.2 * an l) * (cr k * an j * an i) +
      cr k * an j * an i * cc ε l • (E l.1.1 l.1.2 * an l) =
      if l = k then cc ε l • (E l.1.1 l.1.2 * (an j * an i)) else 0 := by
    intro l
    have c1 : cr k * an j * an i * (E l.1.1 l.1.2 * an l) = E l.1.1 l.1.2 * (cr k * an l * (an j * an i)) := by
      rw [← mul_assoc, ← (((h2 _ _ k).mul_right (h1 _ _ j)).mul_right (h1 _ _ i)).eq, mul_assoc, mul_assoc (cr k),
        mul_assoc (cr k), comm_aa an haa, mul_assoc (cr k)]
    have c2 : E l.1.1 l.1.2 * an l * (cr k * an j * an i) = E l.1.1 l.1.2 * (an l * cr k * (an j * an i)) := by
      simp only [mul_assoc]
    rw [smul_mul_assoc, mul_smul_comm, ← smul_add, c1, c2, ← mul_add, ← add_mul, hac]
    split_ifs <;> simp
  simp only [e, Finset.sum_ite_eq', mem_univ, if_true]
  rw [eq_neg_of_add_eq_zero_left (haa j i), tc]
  split_ifs with h
  · simp [cc, h.cptk]
  · simp

theorem beta_sq (haa : ∀ i j, an i * an j + an j * an i = 0) (hcc : ∀ i j, cr i * cr j + cr j * cr i = 0)
    (hac : ∀ i j, an i * cr j + cr j * an i = if i = j then 1 else 0) :
    (∑ i, ∑ j, ∑ k, tc ε i j k • (cr k * an j * an i)) * (∑ i, ∑ j, ∑ k, tc ε i j k • (cr k * an j * an i)) = 0 := by
  let t : Pos n × Pos n × Pos n → ℂ := fun p => tc ε p.1 p.2.1 p.2.2
  have e : (∑ i, ∑ j, ∑ k, tc ε i j k • (cr k * an j * an i)) =
      ∑ p : Pos n × Pos n × Pos n, t p • (cr p.2.2 * an p.2.1 * an p.1) := by
    simp only [Fintype.sum_prod_type, t]
  have ex : ∀ i j k i' j' k' : Pos n, cr k * an j * an i * (cr k' * an j' * an i') =
      (if i = k' then cr k * (an j * (an j' * an i')) else 0) - (if j = k' then cr k * (an j' * an i' * an i) else 0) +
        cr k * cr k' * ((an j * an i) * (an j' * an i')) := by
    intro i j k i' j' k'
    have a1 := eq_sub_of_add_eq (hac i k')
    have a2 := eq_sub_of_add_eq (hac j k')
    calc _ = cr k * (an j * (an i * cr k')) * (an j' * an i') := by simp only [mul_assoc]
      _ = cr k * (an j * (if i = k' then 1 else 0) - (an j * cr k') * an i) * (an j' * an i') := by
          rw [a1, mul_sub, mul_assoc (an j)]
      _ = _ := by
          rw [a2, comm_aa an haa i i' j']
          split_ifs <;> noncomm_ring
  rw [e, Finset.sum_mul_sum]
  simp only [smul_mul_smul_comm, ex, smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h3 : ∑ p : Pos n × Pos n × Pos n, ∑ q : Pos n × Pos n × Pos n,
      (t p * t q) • (cr p.2.2 * cr q.2.2 * ((an p.2.1 * an p.1) * (an q.2.1 * an q.1))) = 0 := by
    apply self_neg
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [mul_comm (t q), eq_neg_of_add_eq_zero_left (hcc q.2.2 p.2.2), neg_mul, smul_neg, ← mul_assoc (an q.2.1 * an q.1),
      comm_aa an haa, mul_assoc (an p.2.1), comm_aa an haa, ← mul_assoc (an p.2.1)]
  rw [h3, add_zero, sub_eq_zero]
  have L : ∑ p : Pos n × Pos n × Pos n, ∑ q : Pos n × Pos n × Pos n,
      (t p * t q) • (if p.1 = q.2.2 then cr p.2.2 * (an p.2.1 * (an q.2.1 * an q.1)) else 0) =
      ∑ p, ∑ q, ∑ r, ∑ k, (∑ i, tc ε p q i * tc ε i r k) • (cr k * (an r * an q * an p)) := by
    simp only [Fintype.sum_prod_type, t, smul_ite, smul_zero, Finset.sum_ite_eq, mem_univ, if_true, Finset.sum_smul]
    symm
    calc _ = ∑ p, ∑ q, ∑ i, ∑ r, ∑ k, (tc ε p q i * tc ε i r k) • (cr k * (an r * an q * an p)) := by
          refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
          exact (Finset.sum_congr rfl fun r _ => Finset.sum_comm).trans Finset.sum_comm
      _ = ∑ x : Pos n × Pos n, ∑ y : Pos n × Pos n × Pos n,
            (tc ε x.1 x.2 y.1 * tc ε y.1 y.2.1 y.2.2) • (cr y.2.2 * (an y.2.1 * an x.2 * an x.1)) := by
          simp only [Fintype.sum_prod_type]
      _ = _ := by
          rw [Finset.sum_comm]
          simp only [Fintype.sum_prod_type, mul_comm (tc ε _ _ _) (tc ε _ _ _), mul_assoc]
  have R' : ∑ p : Pos n × Pos n × Pos n, ∑ q : Pos n × Pos n × Pos n,
      (t p * t q) • (if p.2.1 = q.2.2 then cr p.2.2 * (an q.2.1 * an q.1 * an p.1) else 0) =
      ∑ p, ∑ q, ∑ r, ∑ k, (∑ j, tc ε q r j * tc ε p j k) • (cr k * (an r * an q * an p)) := by
    simp only [Fintype.sum_prod_type, t, smul_ite, smul_zero, Finset.sum_ite_eq, mem_univ, if_true, Finset.sum_smul]
    refine Finset.sum_congr rfl fun p _ => ?_
    calc _ = ∑ x : Pos n × Pos n, ∑ y : Pos n × Pos n,
            (tc ε p x.1 x.2 * tc ε y.1 y.2 x.1) • (cr x.2 * (an y.2 * an y.1 * an p)) := by
          simp only [Fintype.sum_prod_type]
      _ = _ := by
          rw [Finset.sum_comm]
          simp only [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.sum_comm]
          simp only [mul_comm (tc ε p _ _)]
  rw [L, R']
  simp only [tc_assoc]

end Ring

theorem koszul_differential_sq_zero : BdSq := by
  intro n ε V _ _ E hE
  have e : bd ε E = (∑ i, cc ε i • ((lift n (E i.1.1 i.1.2) : Module.End ℂ (Cn n V)) * ann i)) +
      ∑ i, ∑ j, ∑ k, tc ε i j k • (cre k * ann j * ann i : Module.End ℂ (Cn n V)) := by
    simp only [bd, cc, tc, ite_smul, one_smul, zero_smul]
  have hL : KRel ε fun a b => (lift n (E a b) : Module.End ℂ (Cn n V)) := by
    intro a b c d h1 h2
    refine LinearMap.ext fun x => funext fun A => ?_
    have := LinearMap.congr_fun (hE a b c d h1 h2) (x A)
    split_ifs at this ⊢ <;> simpa using this
  have h1 : ∀ a b i, Commute (lift n (E a b) : Module.End ℂ (Cn n V)) (ann i) :=
    fun a b i => LinearMap.ext fun y => lift_ann _ _ y
  have h2 : ∀ a b i, Commute (lift n (E a b) : Module.End ℂ (Cn n V)) (cre i) :=
    fun a b i => LinearMap.ext fun y => lift_cre _ _ y
  rw [e, add_mul, mul_add, mul_add, koszul_differential_sq _ ann hL h1 ann_ann, beta_sq ann cre ann_ann cre_cre ann_cre, add_zero,
    add_assoc, koszul_differential_anticommutator _ ann cre h1 h2 ann_ann ann_cre, add_neg_cancel]

end CompanionTheory.D.LK
end
end

section -- merged from CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.CreAnnApply
open Finset

noncomputable section

namespace CompanionTheory.D.LK

open Car
open Formalism.REAL hiding KRel
open GlobalTheory.CompanionTheory.DSICKoszul (homotopy_ring filt mem_filt_succ euler_filt)
open CompanionTheory.D.DSIC (KRel)

variable {n : ℕ} {Z : Type} [AddCommGroup Z] [Module ℂ Z]

theorem ann_mem {Q : Submodule ℂ Z} {x : Cn n Z} (h : ∀ A, x A ∈ Q) (i : Pos n) (A : Finset (Pos n)) :
    ann i x A ∈ Q := by
  rw [ann_apply]; split_ifs
  · exact Q.zero_mem
  · exact Q.smul_mem _ (h _)

theorem cre_mem {Q : Submodule ℂ Z} {x : Cn n Z} (h : ∀ A, x A ∈ Q) (i : Pos n) (A : Finset (Pos n)) :
    cre i x A ∈ Q := by
  rw [cre_apply]; split_ifs
  · exact Q.smul_mem _ (h _)
  · exact Q.zero_mem

theorem cre_ann_apply (i : Pos n) (x : Cn n Z) (A : Finset (Pos n)) :
    cre i (ann i x) A = if i ∈ A then x A else 0 := by
  by_cases h : i ∈ A
  · simp [cre_apply, ann_apply, h, sg_erase i h, tw_self, smul_smul, sg_mul_self, insert_erase h]
  · simp [cre_apply, h]

theorem acycAbs_of (hS : BdSq) : AcycAbs := by
  intro n ε Z _ _ E a d Fil hE hF B j x hx hcyc
  let I := {i : Pos n // cpt ε i}
  let H : Module.End ℂ (Cn n Z) := ∑ i : I, (lift n (d i.1) : Module.End ℂ (Cn n Z)) * cre i.1
  let Da : Module.End ℂ (Cn n Z) := ∑ i : I, (lift n (a i.1) : Module.End ℂ (Cn n Z)) * ann i.1
  let N : Module.End ℂ Z := ∑ i : I, a i.1 * d i.1
  let G : ℕ → Submodule ℂ Z := fun k => Nat.casesOn k ⊥ Fil
  have hda : ∀ i j : I, d i.1 * a j.1 - a j.1 * d i.1 = if i = j then 1 else 0 := fun i j => by
    rw [hF.da i.1 j.1 i.2]; simp only [Subtype.ext_iff (a1 := i)]
  have hdG : ∀ i k, ∀ z ∈ G (k + 1), d i z ∈ G k := fun i k z hz => by
    cases k with
    | zero => exact hF.d_zero i z hz
    | succ k => exact hF.d_mem i k z hz
  have hNG : ∀ k, ∀ z ∈ G k, N z ∈ G k := fun k z hz => by
    cases k with
    | zero => obtain rfl : z = 0 := hz; simp
    | succ k =>
      rw [LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun i _ => ?_
      cases k with
      | zero => rw [Module.End.mul_apply, hF.d_zero _ z hz, map_zero]; exact Submodule.zero_mem _
      | succ k => exact hF.a_mem _ k _ (hF.d_mem _ k z hz)
  have hrG : ∀ i k, ∀ z ∈ G k, E i.1.1 i.1.2 z - a i z ∈ G k := fun i k z hz => by
    cases k with
    | zero => obtain rfl : z = 0 := hz; simp
    | succ k => exact hF.r_mem i k z hz
  have hGf : ∀ k, G k ≤ filt (fun i : I => d i.1) k := fun k => by
    induction k with
    | zero => exact bot_le
    | succ k ih => exact fun z hz => (mem_filt_succ _ _ _).2 fun i => ih (hdG _ k z hz)
  have hGm : ∀ k, G k ≤ G (k + 1) := fun k => by
    cases k with
    | zero => exact bot_le
    | succ k => exact hF.mono (Nat.le_succ k)
  have hH : ∀ (y : Cn n Z) A, H y A = ∑ i : I, d i.1 (cre i.1 y A) := fun y A => by
    simp only [H, LinearMap.sum_apply, Finset.sum_apply]; rfl
  have hHG : ∀ k (y : Cn n Z), (∀ A, y A ∈ G (k + 1)) → ∀ A, H y A ∈ G k := fun k y hy A => by
    rw [hH]; exact Submodule.sum_mem _ fun i _ => hdG _ k _ (cre_mem hy _ _)
  have hρ : ∀ k (y : Cn n Z), (∀ A, y A ∈ G k) → ∀ A, (bd ε E y - Da y) A ∈ G k := fun k y hy A => by
    have e : Da y A = ∑ i : Pos n, if cpt ε i then a i (ann i y A) else 0 := by
      rw [← Finset.sum_filter, Finset.sum_subtype (p := cpt ε) _ (by simp)]
      simp only [Da, LinearMap.sum_apply, Finset.sum_apply]; rfl
    rw [Pi.sub_apply, bd_apply, e, add_sub_right_comm, ← Finset.sum_sub_distrib]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => ?_) (Submodule.sum_mem _ fun i _ =>
      Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun k _ => ?_)
    · split_ifs
      · exact hrG i _ _ (ann_mem hy _ _)
      · simp
    · split_ifs
      · exact cre_mem (ann_mem (ann_mem hy _) _) _ _
      · exact Submodule.zero_mem _
  have hom : Da * H + H * Da =
      ∑ i : I, (lift n (a i.1) : Module.End ℂ (Cn n Z)) * lift n (d i.1) + ∑ i : I, cre i.1 * ann i.1 := by
    refine homotopy_ring (fun i : I => (lift n (a i.1) : Module.End ℂ (Cn n Z))) (fun i => lift n (d i.1))
      (fun i => ann i.1) (fun i => cre i.1) (fun i j => LinearMap.ext fun y => (lift_ann _ _ y).symm)
      (fun i j => LinearMap.ext fun y => (lift_cre _ _ y).symm) (fun i j => ?_) (fun i j => ?_)
    · refine LinearMap.ext fun y => funext fun A => ?_
      have e := congrArg (fun T : Module.End ℂ Z => T (y A)) (hda i j)
      by_cases h : i = j
      · simpa [h] using e
      · simpa [h] using e
    · rw [ann_cre]; simp only [Subtype.ext_iff (a1 := i)]
  have hHs : ∀ y : Cn n Z, Sup ε B (j + 1) y → Sup ε B (j + 2) (H y) := fun y hy A hA => by
    rw [hH] at hA
    obtain ⟨i, -, hi⟩ := exists_ne_zero_of_sum_ne_zero hA
    obtain ⟨h1, h2⟩ := cre_ne (fun h => hi (by rw [h, map_zero]) : cre i.1 y A ≠ 0)
    obtain ⟨e1, e2⟩ := hy _ h2
    rw [filter_erase_of_not (not_not.2 i.2)] at e1
    rw [filter_erase] at e2
    have := card_erase_add_one (mem_filter.2 ⟨h1, i.2⟩ : i.1 ∈ A.filter (cpt ε))
    exact ⟨e1, by omega⟩
  have hΔ : ∀ y : Cn n Z, Sup ε B (j + 1) y → bd ε E y = 0 → ∀ A, bd ε E (H y) A =
      N (y A) + ((j + 1 : ℕ) : ℂ) • y A + ((bd ε E (H y) - Da (H y)) A + H (bd ε E y - Da y) A) := by
    intro y hy hc A
    have e := congrArg (fun T : Module.End ℂ (Cn n Z) => T y A) hom
    simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, LinearMap.sum_apply, Finset.sum_apply,
      cre_ann_apply, lift_apply] at e
    have e2 : (∑ i : I, if i.1 ∈ A then y A else 0) = ((j + 1 : ℕ) : ℂ) • y A := by
      by_cases h : y A = 0
      · simp [h]
      · rw [← (hy A h).2, ← Finset.sum_subtype (univ.filter (cpt ε)) (p := cpt ε) (by simp)
          (fun i => if i ∈ A then y A else 0), ← Finset.sum_filter, Finset.sum_const, Nat.cast_smul_eq_nsmul]
        congr 2
        ext i; simp [and_comm]
    have e3 : N (y A) = ∑ i : I, a i.1 (d i.1 (y A)) := by simp only [N, LinearMap.sum_apply]; rfl
    rw [e3, ← e2, ← e, hc, zero_sub, map_neg, Pi.sub_apply, Pi.neg_apply]
    abel
  have main : ∀ k (y : Cn n Z), (∀ A, y A ∈ G k) → Sup ε B (j + 1) y → bd ε E y = 0 →
      ∃ t : Cn n Z, Sup ε B (j + 2) t ∧ bd ε E t = y := by
    intro k
    induction k with
    | zero => exact fun y hy _ _ => ⟨0, fun _ h => absurd rfl h, by rw [map_zero]; exact (funext hy).symm⟩
    | succ k ihk =>
      have inner : ∀ m (y : Cn n Z), (∀ A, y A ∈ G (k + 1)) → (∀ A, y A ∈ filt (fun i : I => d i.1) m ⊔ G k) →
          Sup ε B (j + 1) y → bd ε E y = 0 → ∃ t : Cn n Z, Sup ε B (j + 2) t ∧ bd ε E t = y := by
        intro m
        induction m with
        | zero => exact fun y _ hy => ihk y fun A => by simpa [filt] using hy A
        | succ m ih =>
          intro y hy1 hy2 hs hc
          have hne : ((m : ℂ) + (j + 1 : ℕ)) ≠ 0 := by exact_mod_cast (by omega : m + (j + 1) ≠ 0)
          have hL : ∀ A, (bd ε E (H y) - Da (H y)) A + H (bd ε E y - Da y) A ∈ G k := fun A =>
            Submodule.add_mem _ (hρ k _ (hHG k y hy1) A) (hHG k _ (hρ (k + 1) y hy1) A)
          have hw : ∀ A, (bd ε E (H y) - ((m : ℂ) + (j + 1 : ℕ)) • y) A =
              (N (y A) - (m : ℂ) • y A) + ((bd ε E (H y) - Da (H y)) A + H (bd ε E y - Da y) A) := fun A => by
            rw [Pi.sub_apply, hΔ y hs hc A, Pi.smul_apply, add_smul]
            abel
          obtain ⟨t, ht, hbt⟩ := ih (bd ε E (H y) - ((m : ℂ) + (j + 1 : ℕ)) • y)
            (fun A => by
              rw [hw]
              exact Submodule.add_mem _ (Submodule.sub_mem _ (hNG (k + 1) _ (hy1 A)) (Submodule.smul_mem _ _ (hy1 A)))
                (hGm k (hL A)))
            (fun A => by
              rw [hw]
              obtain ⟨u, hu, g, hg, e⟩ := Submodule.mem_sup.1 (hy2 A)
              refine Submodule.add_mem _ ?_ (Submodule.mem_sup_right (hL A))
              rw [← e, map_add (f := _), smul_add, add_sub_add_comm]
              exact Submodule.add_mem_sup (euler_filt (fun i : I => a i.1) _ (fun i j => hF.d_comm _ _) hda m u hu)
                (Submodule.sub_mem _ (hNG _ _ hg) (Submodule.smul_mem _ _ hg)))
            (fun A hA => by
              by_cases h : y A = 0
              · have := sup_bd E (hHs y hs) (A := A) fun h' => hA (by simp [h, h'])
                exact ⟨this.1, by omega⟩
              · exact hs A h)
            (by
              rw [map_sub, map_smul, hc, smul_zero, sub_zero]
              exact LinearMap.congr_fun (hS n ε Z E hE) _)
          refine ⟨((m : ℂ) + (j + 1 : ℕ))⁻¹ • (H y - t), fun A hA => ?_, ?_⟩
          · by_cases h : t A = 0
            · exact hHs y hs A fun h' => hA (by simp [h, h'])
            · exact ht A h
          · rw [map_smul, map_sub, hbt, sub_sub_cancel, smul_smul, inv_mul_cancel₀ hne, one_smul]
      exact fun y hy => inner (k + 1) y hy fun A => Submodule.mem_sup_left (hGf _ (hy A))
  choose f hf using hF.exh
  exact main ((univ.sup fun A => f (x A)) + 1) x
    (fun A => hF.mono (Finset.le_sup (f := fun A => f (x A)) (mem_univ A)) (hf _)) hx hcyc

end CompanionTheory.D.LK
end
end

section -- merged from CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialCommutesWeightOperator
open Finset

noncomputable section

namespace CompanionTheory.D.LK

open Car
open Formalism.REAL hiding KRel
open CompanionTheory.D.DSIC (KRel)

variable {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def al (i : Pos n) (c : Fin n) : ℝ := (if i.1.1 = c then 1 else 0) - (if i.1.2 = c then 1 else 0)

theorem wt_insert {i : Pos n} {A : Finset (Pos n)} (h : i ∉ A) (c : Fin n) : wt (insert i A) c = wt A c + al i c := by
  simp only [wt, al, filter_insert]
  have h1 : ∀ p : Pos n → Prop, ∀ [DecidablePred p], i ∉ A.filter p := fun p _ hh => h (mem_filter.1 hh).1
  split_ifs <;> (try simp only [card_insert_of_notMem (h1 _)]) <;> push_cast <;> ring

theorem Ft_apply (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (c : Fin n) (x : Cn n V)
    (A : Finset (Pos n)) : Ft ε E c x A = E c c (x A) + (wt (A.filter (cpt ε)) c : ℂ) • x A := rfl

theorem Ft_ann {ε : Fin n → Bool} (E : Fin n → Fin n → Module.End ℂ V) (c : Fin n) {i : Pos n} (hi : cpt ε i)
    (x : Cn n V) : Ft ε E c (ann i x) = ann i (Ft ε E c x) - (al i c : ℂ) • ann i x := by
  funext A
  simp only [Ft_apply, ann_apply, Pi.sub_apply, Pi.smul_apply]
  by_cases h : i ∈ A
  · simp [h]
  · rw [if_neg h, if_neg h, filter_insert, if_pos hi, wt_insert (fun hh => h (mem_filter.1 hh).1), map_smul]
    push_cast
    module

theorem Ft_cre {ε : Fin n → Bool} (E : Fin n → Fin n → Module.End ℂ V) (c : Fin n) {i : Pos n} (hi : cpt ε i)
    (x : Cn n V) : Ft ε E c (cre i x) = cre i (Ft ε E c x) + (al i c : ℂ) • cre i x := by
  funext A
  simp only [Ft_apply, cre_apply, Pi.add_apply, Pi.smul_apply]
  by_cases h : i ∈ A
  · have e : A.filter (cpt ε) = insert i ((A.erase i).filter (cpt ε)) := by
      conv_lhs => rw [← insert_erase h, filter_insert, if_pos hi]
    rw [if_pos h, if_pos h, e, wt_insert (fun hh => notMem_erase i A (mem_filter.1 hh).1), map_smul]
    push_cast
    module
  · simp [h]

theorem differential_commutes_weight_operator : ∀ (n : ℕ) (ε₀ ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), (∀ a b, ε a = ε b → ε₀ a = ε₀ b) → KRel ε E →
    ∀ c, Commute (Ft ε₀ E c) (bd ε E) := by
  intro n ε₀ ε V _ _ E h0 hE c
  refine Commute.add_right (Commute.sum_right _ _ _ fun i _ => ?_) (Commute.sum_right _ _ _ fun i _ =>
    Commute.sum_right _ _ _ fun j _ => Commute.sum_right _ _ _ fun k _ => ?_)
  · split_ifs with hi
    · refine LinearMap.ext fun x => ?_
      have e : ∀ y : Cn n V, Ft ε₀ E c (lift n (E i.1.1 i.1.2) y) =
          lift n (E i.1.1 i.1.2) (Ft ε₀ E c y) + (al i c : ℂ) • lift n (E i.1.1 i.1.2) y := by
        intro y
        funext A
        have := congrArg (fun T : Module.End ℂ V => T (y A)) (hE c c i.1.1 i.1.2 rfl hi)
        simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
        simp only [Ft_apply, lift_apply, Pi.add_apply, Pi.smul_apply, map_add (f := _), map_smul, sub_eq_iff_eq_add.1 this, al]
        have hne := i.2.ne
        by_cases h1 : c = i.1.1
        · subst h1; simp [hne.symm]; module
        · by_cases h2 : i.1.2 = c
          · subst h2; simp [hne, hne.symm]; module
          · simp [h1, h2, Ne.symm h1]
      simp only [Module.End.mul_apply]
      rw [e, Ft_ann E c (h0 _ _ hi), map_sub, map_smul, sub_add_cancel]
    · exact Commute.zero_right _
  · split_ifs with ht
    · refine LinearMap.ext fun x => ?_
      have hk := Tri.cptk (ε := ε) ht
      simp only [Module.End.mul_apply]
      rw [Ft_cre E c (h0 _ _ hk), Ft_ann E c (h0 _ _ ht.2.1), Ft_ann E c (h0 _ _ ht.1)]
      have : (al k c : ℂ) = al i c + al j c := by
        rw [← Complex.ofReal_add]; simp only [al, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2]; congr 1; ring
      simp only [map_sub, map_smul, this]
      module
    · exact Commute.zero_right _

theorem free_inter {ι : Type} (φ : V →ₗ[ℂ] W) (S : ι → Module.End ℂ V) (T : ι → Module.End ℂ W)
    (h : ∀ i x, φ (S i x) = T i (φ x)) (a : FreeAlgebra ℂ ι) :
    ∀ x, φ (FreeAlgebra.lift ℂ S a x) = FreeAlgebra.lift ℂ T a (φ x) := by
  induction a using FreeAlgebra.induction with
  | grade0 r => intro x; simp [Module.algebraMap_end_apply]
  | grade1 c => intro x; simp [h]
  | mul a b ha hb => intro x; simp only [map_mul, Module.End.mul_apply, ha, hb]
  | add a b ha hb => intro x; simp only [map_add (f := _), LinearMap.add_apply, ha, hb]

theorem evK_inter {ε : Fin n → Bool} (φ : V →ₗ[ℂ] W) (E : Fin n → Fin n → Module.End ℂ V)
    (F : Fin n → Fin n → Module.End ℂ W) (h : ∀ a b x, φ (E a b x) = F a b (φ x)) (a : FreeAlgebra ℂ (Fin n × Fin n))
    (x : V) : φ (evK ε E a x) = evK ε F a (φ x) :=
  free_inter φ _ _ (fun p x => by split_ifs <;> simp [h]) a x

theorem evd_Ft_apply (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (b : FreeAlgebra ℂ (Fin n))
    (x : Cn n V) (A : Finset (Pos n)) :
    evd (Ft ε E) b x A = evd (fun c => E c c + (wt (A.filter (cpt ε)) c : ℂ) • 1) b (x A) :=
  free_inter (LinearMap.proj (R := ℂ) (φ := fun _ => V) A) _ _ (fun _ _ => rfl) b x

theorem lift_evd {ε : Fin n → Bool} (φ : V →ₗ[ℂ] W) (E : Fin n → Fin n → Module.End ℂ V)
    (F : Fin n → Fin n → Module.End ℂ W) (h : ∀ a b x, φ (E a b x) = F a b (φ x)) (b : FreeAlgebra ℂ (Fin n))
    (x : Cn n V) : lift n φ (evd (Ft ε E) b x) = evd (Ft ε F) b (lift n φ x) :=
  free_inter (lift n φ) _ _ (fun c y => by funext A; simp [Ft_apply, h]) b x

theorem sup_of_supp {ε : Fin n → Bool} {B : Finset (Pos n)} {j : ℕ} {x : Cn n V} {y : Cn n W} (hx : Sup ε B j x)
    (h : ∀ A, x A = 0 → y A = 0) : Sup ε B j y := fun A hA => hx A fun h0 => hA (h A h0)

theorem Sup.sub {ε : Fin n → Bool} {B : Finset (Pos n)} {j : ℕ} {x y : Cn n V} (hx : Sup ε B j x) (hy : Sup ε B j y) :
    Sup ε B j (x - y) := fun A hA => by
  by_cases h : x A = 0
  · exact hy A fun h' => hA (by simp [h, h'])
  · exact hx A h

theorem genCO_of (hS : BdSq) (hC : Cover2) : GenCO := by
  intro n ε₀ ε a b h0 hab V _ _ E hE B j
  induction j generalizing V with
  | zero =>
    intro x hx _ _
    obtain ⟨w, hw⟩ := (hab V E hE).2 (x B)
    have hxB : ∀ A, A ≠ B → x A = 0 := fun A hA => by
      by_contra h
      obtain ⟨e1, e2⟩ := hx A h
      refine hA (e1 ▸ (filter_true_of_mem fun i hi hc => ?_).symm)
      exact notMem_empty i (card_eq_zero.1 e2 ▸ mem_filter.2 ⟨hi, hc⟩)
    by_cases hB : x B = 0
    · have : x = 0 := funext fun A => by
        by_cases h : A = B
        · rw [h, hB]; rfl
        · exact hxB A h
      subst this
      exact ⟨0, fun A hA => absurd rfl hA, by simp⟩
    have hBn : ∀ i ∈ B, ¬cpt ε₀ i := fun i hi => (mem_filter.1 ((hx B hB).1.symm ▸ hi :)).2
    have hBc : B.filter (cpt ε₀) = ∅ := filter_false_of_mem hBn
    let w' : Cn n V := fun A => ∑ i : Pos n, if cpt ε₀ i ∧ A = insert i B then sg i B • w i else 0
    have hw' : Sup ε₀ B (0 + 1) w' := by
      intro A hA
      obtain ⟨i, -, hi⟩ := exists_ne_zero_of_sum_ne_zero hA
      obtain ⟨h1, rfl⟩ : cpt ε₀ i ∧ A = insert i B := by by_contra h; exact hi (if_neg h)
      rw [filter_insert, if_neg (not_not.2 h1), filter_true_of_mem hBn, filter_insert, if_pos h1, hBc]
      simp
    refine ⟨w', hw', funext fun A => ?_⟩
    by_cases hA : A = B
    · subst hA
      rw [Pi.sub_apply, lift_apply, evd_Ft_apply, hBc]
      have e : (fun c => E c c + (wt (∅ : Finset (Pos n)) c : ℂ) • (1 : Module.End ℂ V)) = fun c => E c c := by
        funext c; simp [wt]
      rw [e, hw, bd_apply, Finset.sum_eq_zero (s := univ) (f := fun i => ∑ j : Pos n, ∑ k : Pos n,
        if Tri ε₀ i j k then cre k (ann j (ann i w')) A else 0), add_zero]
      · refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs with hi
        · have hiA : i ∉ A := fun h => hBn i h hi
          rw [ann_apply, if_neg hiA]
          congr 1
          simp only [w']
          rw [Finset.sum_eq_single i, if_pos ⟨hi, rfl⟩, smul_smul, sg_mul_self, one_smul]
          · intro k _ hk
            refine if_neg fun h => ?_
            rcases mem_insert.1 (h.2 ▸ mem_insert_self i A) with h' | h'
            · exact hk h'.symm
            · exact hiA h'
          · simp
        · rfl
      · refine fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
        split_ifs with ht
        · by_contra h
          exact hBn k (tri_ne h).1 ht.cptk
        · rfl
    · rw [Pi.sub_apply, lift_apply, evd_Ft_apply, hxB A hA, map_zero, map_zero, sub_zero]
      by_contra h
      obtain ⟨e1, e2⟩ := sup_bd E hw' (Ne.symm h)
      refine hA (e1 ▸ (filter_true_of_mem fun i hi hc => ?_).symm)
      exact notMem_empty i (card_eq_zero.1 (by omega : (A.filter (cpt ε₀)).card = 0) ▸ mem_filter.2 ⟨hi, hc⟩)
  | succ j ih =>
    intro x hx hr hbx
    obtain ⟨Y, _, _, EY, π, hY, hs, hπ, hac⟩ := hC n ε₀ V E hE
    have hK : ∀ a b, ∀ y ∈ LinearMap.ker π, EY a b y ∈ LinearMap.ker π := by
      intro a b y hy
      rw [LinearMap.mem_ker] at hy ⊢
      rw [hπ, hy, map_zero]
    let EK : Fin n → Fin n → Module.End ℂ (LinearMap.ker π) := fun a b => (EY a b).restrict (hK a b)
    have hι : ∀ a b y, (LinearMap.ker π).subtype (EK a b y) = EY a b ((LinearMap.ker π).subtype y) :=
      fun _ _ _ => rfl
    have hEK : KRel ε₀ EK := by
      intro a b c d h1 h2
      ext y
      have := LinearMap.congr_fun (hY a b c d h1 h2) (y : Y)
      split_ifs at this ⊢ <;> simpa [EK] using this
    classical
    let x' : Cn n Y := fun A => if x A = 0 then 0 else (hs (x A)).choose
    have hz : ∀ A, x A = 0 → x' A = 0 := fun A h => if_pos h
    have hx' : Sup ε₀ B (j + 1) x' := sup_of_supp hx hz
    have hr' : Ref ε₀ ε x' := fun A hA => hr A fun h => hA (hz A h)
    have hπx : lift n π x' = x := by
      funext A
      by_cases hA : x A = 0
      · simp [x', hA]
      · simp only [lift_apply, x', if_neg hA]
        exact (hs (x A)).choose_spec
    have hy : ∀ A, bd ε₀ EY x' A ∈ LinearMap.ker π := by
      intro A
      have := congrFun (lift_bd (ε := ε₀) π EY E (fun i _ => hπ _ _) x') A
      rw [hπx, hbx] at this
      exact this
    obtain ⟨s1, -, s3, -⟩ := differential_bounded_support n ε₀ Y EY
    obtain ⟨-, -, s3', -⟩ := differential_bounded_support n ε Y EY
    let y : Cn n (LinearMap.ker π) := fun A => ⟨_, hy A⟩
    have hιy : lift n (LinearMap.ker π).subtype y = bd ε₀ EY x' := rfl
    have hyd : Sup ε₀ B j y := sup_of_supp (s1 B j x' hx') fun A hA => Subtype.ext hA
    have hyr : Ref ε₀ ε y := fun A hA =>
      (s3' ε₀ x' h0 hr').2 A fun h => hA (Subtype.ext (by rw [← (s3' ε₀ x' h0 hr').1] at h; exact h))
    have hyb : bd ε₀ EK y = 0 := by
      have := lift_bd (ε := ε₀) _ EK EY (fun i _ => hι _ _) y
      rw [hιy, show bd ε₀ EY (bd ε₀ EY x') = 0 from LinearMap.congr_fun (hS n ε₀ Y EY hY) x'] at this
      funext A
      exact Subtype.ext (congrFun this A)
    obtain ⟨w, hw, hDw⟩ := ih _ EK hEK y hyd hyr hyb
    have hpush := congrArg (lift n (LinearMap.ker π).subtype) hDw
    have hl : ∀ {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (φ : V →ₗ[ℂ] W)
        (E : Fin n → Fin n → Module.End ℂ V) (F : Fin n → Fin n → Module.End ℂ W),
        (∀ a b x, φ (E a b x) = F a b (φ x)) → ∀ z : Cn n V,
        lift n φ (lift n (evK ε₀ E a) z) = lift n (evK ε₀ F a) (lift n φ z) :=
      fun φ E F h z => funext fun A => evK_inter φ E F h a _
    rw [map_sub, hl _ EK EY hι, lift_evd _ EK EY hι, lift_bd (ε := ε₀) _ EK EY (fun i _ => hι _ _), hιy] at hpush
    have c1 : bd ε₀ EY (lift n (evK ε₀ EY a) x') = lift n (evK ε₀ EY a) (bd ε₀ EY x') := by
      rw [(s3' ε₀ x' h0 hr').1, (s3' ε₀ _ h0 fun A hA => hr' A fun h => hA (by simp [h])).1]
      exact (lift_bd _ EY EY (fun i hi z => (LinearMap.congr_fun ((hab Y EY hY).1 i hi).eq z).symm) x').symm
    have c2 : bd ε₀ EY (evd (Ft ε₀ EY) b x') = evd (Ft ε₀ EY) b (bd ε₀ EY x') :=
      free_inter (bd ε₀ EY) _ _
        (fun c z => (LinearMap.congr_fun (differential_commutes_weight_operator n ε₀ ε₀ Y EY (fun _ _ h => h) hY c).eq z).symm) b x'
    obtain ⟨t, ht, hbt⟩ := hac B j
      (lift n (evK ε₀ EY a) x' - evd (Ft ε₀ EY) b x' - lift n (LinearMap.ker π).subtype w)
      (((sup_of_supp hx' fun A h => by simp [h]).sub
        (sup_of_supp hx' fun A h => by rw [evd_Ft_apply, h, map_zero])).sub (sup_of_supp hw fun A h => by simp [h]))
      (by rw [map_sub, map_sub, c1, c2, hpush, sub_self])
    refine ⟨lift n π t, sup_of_supp ht fun A h => by simp [h], ?_⟩
    have h2 : lift n π (lift n (LinearMap.ker π).subtype w) = 0 := by
      funext A
      exact (w A).2
    rw [← lift_bd π EY E (fun i _ => hπ _ _), hbt, map_sub, map_sub, h2, hl π EY E hπ, lift_evd π EY E hπ, hπx,
      sub_zero]

end CompanionTheory.D.LK
end
end
