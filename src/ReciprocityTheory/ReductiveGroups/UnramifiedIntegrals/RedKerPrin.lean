module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedHalf
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ExistsFinitePartOneIdeleSplitCongruenceQuotient
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedKerPoly
section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedSeries
section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedVeluFun
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

theorem velu_pair (L : PeriodPair) (z P : ℂ) (hz : z ∉ L.lattice) (hP : P ∉ L.lattice)
    (hp : z + P ∉ L.lattice) (hm : z - P ∉ L.lattice) :
    (L.weierstrassP (z + P) - L.weierstrassP P) + (L.weierstrassP (z + -P) - L.weierstrassP (-P))
      = fW L.g₂ L.g₃ (L.weierstrassP P) / (L.weierstrassP z - L.weierstrassP P) ^ 2
        + fW' L.g₂ (L.weierstrassP P) / (2 * (L.weierstrassP z - L.weierstrassP P)) := by
  have hne := Formalism.L2.Th1.E.AddThm.P_sub_ne L z P hz hP hp hm
  have hP' : -P ∉ L.lattice := fun h => hP (by simpa using L.lattice.neg_mem h)
  have h1 := Formalism.L2.Th1.E.AddThm.P_add L z P hz hP hp hm
  have h2 := Formalism.L2.Th1.E.AddThm.P_add L z (-P) hz hP' (by simpa [sub_eq_add_neg] using hm)
    (by simpa using hp)
  rw [L.weierstrassP_neg, L.derivWeierstrassP_neg] at h2
  have hY := L.derivWeierstrassP_sq z hz
  have hy := L.derivWeierstrassP_sq P hP
  rw [L.weierstrassP_neg, h1, h2]
  unfold fW fW'
  generalize L.weierstrassP z = X at *
  generalize L.weierstrassP P = x at *
  generalize L.derivWeierstrassP z = Y at *
  generalize L.derivWeierstrassP P = y at *
  field_simp
  linear_combination 4 * hY + 4 * hy

theorem velu_fun (L : PeriodPair) (α : ℂ) (T : Finset ℂ) (hα : α ≠ 0) (hs : MulStable L α)
    (hT : IsHalfReps L α T) (z : ℂ) (hz : α * z ∉ L.lattice) :
    α ^ 2 * L.weierstrassP (α * z) = veluFun L.g₂ L.g₃ (xsOf L T) (L.weierstrassP z) := by
  obtain ⟨hK, hdisj⟩ := hT.kerReps
  have hzL : z ∉ L.lattice := fun h => hz (hs z h)
  rw [isogenyP L α _ hα hs hK z hz, Finset.sum_union hdisj,
    Finset.sum_image (by intro a _ b _ h; exact neg_injective h)]
  simp only [veluFun, xsOf]
  rw [Finset.sum_image (by intro a ha b hb h; exact hT.injOn ha hb h)]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun P hP => ?_
  obtain ⟨hαP, h2P⟩ := hT.1 P hP

  have hPL : P ∉ L.lattice := fun h => h2P (by rw [two_mul]; exact L.lattice.add_mem h h)

  have hp : z + P ∉ L.lattice := fun h => hz (by
    have := L.lattice.sub_mem (hs _ h) hαP
    rwa [mul_add, add_sub_cancel_right] at this)
  have hm : z - P ∉ L.lattice := fun h => hz (by
    have := L.lattice.add_mem (hs _ h) hαP
    rwa [mul_sub, sub_add_cancel] at this)
  exact velu_pair L z P hzL hPL hp hm

end ReciprocityTheory.ChartRestriction.L1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedVeluAlg
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial

namespace ReciprocityTheory.ChartRestriction.L1

variable {K : Type} [Field K] [CharZero K] [DecidableEq K] (g2 g3 : K) (xs : Finset K)

theorem rootPoly_monic : (rootPoly xs).Monic := by
  unfold rootPoly
  exact monic_prod_of_monic _ _ (fun x _ => monic_X_sub_C x)

theorem rootPoly_natDegree : (rootPoly xs).natDegree = xs.card := by
  unfold rootPoly
  rw [natDegree_prod_of_monic _ _ (fun x _ => monic_X_sub_C x)]
  simp

theorem rootPoly_eval (t : K) : (rootPoly xs).eval t = ∏ x ∈ xs, (t - x) := by
  unfold rootPoly
  rw [eval_prod]
  simp

theorem rootPoly_eval_ne {t : K} (ht : t ∉ xs) : (rootPoly xs).eval t ≠ 0 := by
  rw [rootPoly_eval, Finset.prod_ne_zero_iff]
  intro x hx h
  rw [sub_eq_zero] at h
  exact ht (h ▸ hx)

theorem rootPoly_eval_mem {t : K} (ht : t ∈ xs) : (rootPoly xs).eval t = 0 := by
  rw [rootPoly_eval]
  exact Finset.prod_eq_zero ht (sub_self t)

theorem rootPoly_erase {x : K} (hx : x ∈ xs) :
    rootPoly xs = (X - C x) * rootPoly (xs.erase x) := by
  unfold rootPoly
  exact (Finset.mul_prod_erase xs (fun y => (X - C y : K[X])) hx).symm

theorem veluNum_eval' (t : K) :
    (veluNum g2 g3 xs).eval t = t * (rootPoly xs).eval t ^ 2
      + ∑ x ∈ xs, (fW g2 g3 x + fW' g2 x / 2 * (t - x)) * (rootPoly (xs.erase x)).eval t ^ 2 := by
  unfold veluNum
  simp [eval_finsetSum]

theorem veluNum_eval {t : K} (ht : t ∉ xs) :
    (veluNum g2 g3 xs).eval t = veluFun g2 g3 xs t * (rootPoly xs).eval t ^ 2 := by
  rw [veluNum_eval']
  unfold veluFun
  rw [add_mul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl (fun x hx => ?_)
  have hne : t - x ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    exact ht (h ▸ hx)
  rw [rootPoly_erase xs hx]
  simp only [eval_mul, eval_sub, eval_X, eval_C]
  field_simp

theorem veluNum_natDegree_le : (veluNum g2 g3 xs).natDegree ≤ 2 * xs.card + 1 := by
  unfold veluNum
  refine natDegree_add_le_of_degree_le ?_ ?_
  · refine natDegree_mul_le.trans ?_
    have h1 := natDegree_pow_le (p := rootPoly xs) (n := 2)
    rw [rootPoly_natDegree] at h1
    rw [natDegree_X]
    omega
  · refine natDegree_sum_le_of_forall_le _ _ (fun x hx => ?_)
    refine natDegree_mul_le.trans ?_
    have h1 := natDegree_pow_le (p := rootPoly (xs.erase x)) (n := 2)
    rw [rootPoly_natDegree] at h1
    have h2 : (xs.erase x).card ≤ xs.card := Finset.card_erase_le
    have h3 : (C (fW g2 g3 x) + C (fW' g2 x / 2) * (X - C x) : K[X]).natDegree ≤ 1 := by
      refine natDegree_add_le_of_degree_le (by simp) ?_
      refine natDegree_mul_le.trans ?_
      simp
    omega

theorem veluNum_eval_mem {x : K} (hx : x ∈ xs) :
    (veluNum g2 g3 xs).eval x = fW g2 g3 x * (rootPoly (xs.erase x)).eval x ^ 2 := by
  rw [veluNum_eval', rootPoly_eval_mem xs hx, Finset.sum_eq_single_of_mem x hx]
  · simp
  · intro y _ hy
    rw [rootPoly_eval_mem (xs.erase y) (Finset.mem_erase.2 ⟨hy.symm, hx⟩)]
    simp

theorem veluNum_coprime (h : ∀ x ∈ xs, fW g2 g3 x ≠ 0) :
    IsCoprime (veluNum g2 g3 xs) (rootPoly xs ^ 2) := by
  refine IsCoprime.pow_right ?_
  unfold rootPoly
  refine IsCoprime.prod_right (fun x hx => ?_)
  refine IsCoprime.symm ?_
  rw [(irreducible_X_sub_C x).coprime_iff_not_dvd, dvd_iff_isRoot, IsRoot.def,
    veluNum_eval_mem g2 g3 xs hx]
  exact mul_ne_zero (h x hx) (pow_ne_zero 2 (rootPoly_eval_ne _ (Finset.notMem_erase x xs)))

end ReciprocityTheory.ChartRestriction.L1
end
end

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial

namespace ReciprocityTheory.ChartRestriction.L1

def HasT (f : ℂ → ℂ) (s : PowerSeries ℂ) : Prop := AnalyticAt ℂ f 0 ∧ taylor0 f = s

theorem HasT.add {f g : ℂ → ℂ} {s t : PowerSeries ℂ} (hf : HasT f s) (hg : HasT g t) :
    HasT (fun z => f z + g z) (s + t) :=
  ⟨hf.1.add hg.1, by rw [(taylorRing.1 f g hf.1 hg.1).1, hf.2, hg.2]⟩

theorem HasT.mul {f g : ℂ → ℂ} {s t : PowerSeries ℂ} (hf : HasT f s) (hg : HasT g t) :
    HasT (fun z => f z * g z) (s * t) :=
  ⟨hf.1.mul hg.1, by rw [(taylorRing.1 f g hf.1 hg.1).2, hf.2, hg.2]⟩

theorem hasT_const (c : ℂ) : HasT (fun _ => c) (PowerSeries.C c) :=
  ⟨analyticAt_const, taylorRing.2.1 c⟩

theorem hasT_id : HasT (fun z => z) PowerSeries.X := ⟨analyticAt_id, taylorRing.2.2.1⟩

theorem HasT.pow {f : ℂ → ℂ} {s : PowerSeries ℂ} (hf : HasT f s) (n : ℕ) :
    HasT (fun z => f z ^ n) (s ^ n) := by
  induction n with
  | zero => simpa using hasT_const 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem hasT_sum {ι : Type} (S : Finset ι) (f : ι → ℂ → ℂ) (s : ι → PowerSeries ℂ)
    (h : ∀ i ∈ S, HasT (f i) (s i)) : HasT (fun z => ∑ i ∈ S, f i z) (∑ i ∈ S, s i) := by
  induction S using Finset.induction_on with
  | empty => simpa using hasT_const 0
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a S)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem HasT.rescale {f : ℂ → ℂ} {s : PowerSeries ℂ} (hf : HasT f s) (a : ℂ) :
    HasT (fun z => f (a * z)) (PowerSeries.rescale a s) := by
  refine ⟨?_, by rw [taylorDeriv.2.1 f a hf.1, hf.2]⟩
  refine AnalyticAt.fun_comp (f := fun z : ℂ => a * z) (g := f) ?_ (analyticAt_const.mul analyticAt_id)
  simpa using hf.1

def uFun (L : PeriodPair) (z : ℂ) : ℂ := 1 + z ^ 2 * L.weierstrassPExcept 0 z

theorem hasT_uFun (L : PeriodPair) : HasT (uFun L) (wpNum L.g₂ L.g₃) := by
  have h : HasT (L.weierstrassPExcept 0) (pOf L.g₂ L.g₃) :=
    ⟨L.analyticAt_weierstrassPExcept 0, pOfLattice L⟩
  rw [(wpNumDen ℂ L.g₂ L.g₃).1]
  have h3 := (hasT_const 1).add ((hasT_id.pow 2).mul h)
  rw [map_one] at h3
  exact h3

theorem uFun_eq (L : PeriodPair) {z : ℂ} (hz : z ≠ 0) : uFun L z = z ^ 2 * L.weierstrassP z := by
  have h := L.weierstrassPExcept_add 0 z
  simp only [ZeroMemClass.coe_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, div_zero] at h
  rw [← h, uFun]
  field_simp
  ring

def homF (u : ℂ → ℂ) (m : ℕ) (Q : ℂ[X]) (z : ℂ) : ℂ :=
  ∑ i ∈ Finset.range (m + 1), Q.coeff i * u z ^ i * z ^ (2 * (m - i))

theorem hasT_homF {u : ℂ → ℂ} {U : PowerSeries ℂ} (hu : HasT u U) (m : ℕ) (Q : ℂ[X]) :
    HasT (homF u m Q) (homS U m Q) :=
  hasT_sum _ _ _ fun i _ => ((hasT_const (Q.coeff i)).mul (hu.pow i)).mul (hasT_id.pow _)

theorem homF_eq {u : ℂ → ℂ} {m : ℕ} {Q : ℂ[X]} (hQ : Q.natDegree ≤ m) {z t : ℂ}
    (h : u z = z ^ 2 * t) : homF u m Q z = z ^ (2 * m) * Q.eval t := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hQ), Finset.mul_sum, homF]
  refine Finset.sum_congr rfl fun i hi => ?_
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
  rw [h, Nat.add_sub_cancel_left]
  ring

theorem eventually_notMem (L : PeriodPair) {α : ℂ} (hα : α ≠ 0) :
    ∀ᶠ z in nhdsWithin (0 : ℂ) {0}ᶜ, z ≠ 0 ∧ α * z ∉ L.lattice := by
  have h1 : Filter.Tendsto (fun z : ℂ => α * z) (nhds 0) (nhds 0) := by
    have : ContinuousAt (fun z : ℂ => α * z) 0 := by fun_prop
    simpa [ContinuousAt] using this
  have h2 := h1 (L.compl_lattice_sdiff_singleton_mem_nhds 0)
  rw [eventually_nhdsWithin_iff]
  filter_upwards [h2] with z hz hz0
  refine ⟨hz0, fun hm => hz ⟨hm, ?_⟩⟩
  simpa [hα] using hz0

theorem xs_notMem (L : PeriodPair) {α : ℂ} {T : Finset ℂ} (hs : MulStable L α)
    (hT : IsHalfReps L α T) {z : ℂ} (hz : α * z ∉ L.lattice) : L.weierstrassP z ∉ xsOf L T := by
  intro hm
  obtain ⟨P, hP, hPz⟩ := Finset.mem_image.1 hm
  have hz' : z ∉ L.lattice := fun h => hz (hs z h)
  have hP' : P ∉ L.lattice := fun h => (hT.1 P hP).2 (by
    rw [two_mul]; exact L.lattice.add_mem h h)
  have hαP := (hT.1 P hP).1
  rcases (pInjective L z P hz' hP').1 hPz.symm with h | h
  · apply hz
    have : α * z = α * (z - P) + α * P := by ring
    rw [this]; exact L.lattice.add_mem (hs _ h) hαP
  · apply hz
    have : α * z = α * (z + P) - α * P := by ring
    rw [this]; exact L.lattice.sub_mem (hs _ h) hαP

theorem velu_series (L : PeriodPair) (α : ℂ) (T : Finset ℂ) (hα : α ≠ 0) (hs : MulStable L α)
    (hT : IsHalfReps L α T) :
    PowerSeries.rescale α (wpNum L.g₂ L.g₃)
        * homS (wpNum L.g₂ L.g₃) (2 * (xsOf L T).card) (rootPoly (xsOf L T) ^ 2)
      = homS (wpNum L.g₂ L.g₃) (2 * (xsOf L T).card + 1) (veluNum L.g₂ L.g₃ (xsOf L T)) := by
  have hu := hasT_uFun L
  have h1 := (hu.rescale α).mul (hasT_homF hu (2 * (xsOf L T).card) (rootPoly (xsOf L T) ^ 2))
  have h2 := hasT_homF hu (2 * (xsOf L T).card + 1) (veluNum L.g₂ L.g₃ (xsOf L T))
  rw [← h1.2, ← h2.2]
  refine taylorRing.2.2.2 _ _ ((h1.1.frequently_eq_iff_eventually_eq h2.1).1 ?_)
  refine Filter.Eventually.frequently ?_
  filter_upwards [eventually_notMem L hα] with z hz
  obtain ⟨hz0, hzα⟩ := hz
  have hx := xs_notMem L hs hT hzα
  have hd : (rootPoly (xsOf L T) ^ 2).natDegree ≤ 2 * (xsOf L T).card := by
    rw [(rootPoly_monic (xsOf L T)).natDegree_pow, rootPoly_natDegree]
  rw [homF_eq hd (uFun_eq L hz0), homF_eq (veluNum_natDegree_le _ _ _) (uFun_eq L hz0),
    uFun_eq L (mul_ne_zero hα hz0), veluNum_eval _ _ _ hx, ← velu_fun L α T hα hs hT z hzα,
    Polynomial.eval_pow]
  ring

end ReciprocityTheory.ChartRestriction.L1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedProj
section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedProjA
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial

namespace ReciprocityTheory.ChartRestriction.L1

variable {K : Type} [Field K] (U : PowerSeries K)

theorem homS_add (m : ℕ) (P Q : K[X]) : homS U m (P + Q) = homS U m P + homS U m Q := by
  simp only [homS, coeff_add, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem homS_sub (m : ℕ) (P Q : K[X]) : homS U m (P - Q) = homS U m P - homS U m Q := by
  simp only [homS, coeff_sub, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem homS_zero (m : ℕ) : homS U m (0 : K[X]) = 0 := by
  simp [homS]

theorem homS_sum {ι : Type} (s : Finset ι) (m : ℕ) (f : ι → K[X]) :
    homS U m (∑ i ∈ s, f i) = ∑ i ∈ s, homS U m (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [homS_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, homS_add, ih]

theorem homS_monomial (m i : ℕ) (hi : i ≤ m) (a : K) :
    homS U m (monomial i a) = PowerSeries.C a * U ^ i * PowerSeries.X ^ (2 * (m - i)) := by
  unfold homS
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    rw [coeff_monomial_of_ne a hb]
    simp
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hi)) h

theorem homS_mul (m n : ℕ) (P Q : K[X]) (hP : P.natDegree ≤ m) (hQ : Q.natDegree ≤ n) :
    homS U (m + n) (P * Q) = homS U m P * homS U n Q := by
  have eP : P = ∑ i ∈ Finset.range (m + 1), monomial i (P.coeff i) :=
    P.as_sum_range' (m + 1) (Nat.lt_succ_of_le hP)
  have eQ : Q = ∑ j ∈ Finset.range (n + 1), monomial j (Q.coeff j) :=
    Q.as_sum_range' (n + 1) (Nat.lt_succ_of_le hQ)
  have e : P * Q = ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
      monomial (i + j) (P.coeff i * Q.coeff j) := by
    conv_lhs => rw [eP, eQ]
    rw [Finset.sum_mul_sum]
    simp only [monomial_mul_monomial]
  rw [e, homS_sum]
  simp only [homS_sum]
  unfold homS
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hj' : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have := homS_monomial U (m + n) (i + j) (by omega) (P.coeff i * Q.coeff j)
  unfold homS at this
  rw [this]
  have h2 : 2 * (m + n - (i + j)) = 2 * (m - i) + 2 * (n - j) := by omega
  rw [h2, pow_add, pow_add, map_mul]
  ring

theorem homS_eq_zero (hU : PowerSeries.constantCoeff U = 1) (m : ℕ) (P : K[X]) (hP : P.natDegree ≤ m)
    (h : homS U m P = 0) : P = 0 := by
  have h1 : PowerSeries.coeff (2 * (m - P.natDegree)) (homS U m P) = P.leadingCoeff := by
    unfold homS
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_eq_single P.natDegree]
    · rw [PowerSeries.coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply,
        map_mul, map_pow, hU]
      simp
    · intro b hb hne
      have hb' : b ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hb)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [PowerSeries.coeff_mul_X_pow', if_neg (by omega)]
      · rw [coeff_eq_zero_of_natDegree_lt hgt]
        simp
    · intro hh
      exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hP)) hh
  rw [h, map_zero] at h1
  exact leadingCoeff_eq_zero.1 h1.symm

end ReciprocityTheory.ChartRestriction.L1
end
end

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial

namespace ReciprocityTheory.ChartRestriction.L1

section Proj

variable {E : Type} [Field E]

def serMap (ψ : E →+ E) (S : PowerSeries E) : PowerSeries E :=
  PowerSeries.mk fun n => ψ (PowerSeries.coeff n S)

def polMap (ψ : E →+ E) (m : ℕ) (Q : E[X]) : E[X] :=
  ∑ i ∈ Finset.range (m + 1), monomial i (ψ (Q.coeff i))

theorem coeff_serMap (ψ : E →+ E) (S : PowerSeries E) (n : ℕ) :
    PowerSeries.coeff n (serMap ψ S) = ψ (PowerSeries.coeff n S) := by
  simp [serMap]

theorem serMap_sum (ψ : E →+ E) {ι : Type} (s : Finset ι) (f : ι → PowerSeries E) :
    serMap ψ (∑ i ∈ s, f i) = ∑ i ∈ s, serMap ψ (f i) := by
  ext n
  set_option synthInstance.maxHeartbeats 100000 in
    simp [coeff_serMap, map_sum]

theorem coeff_polMap (ψ : E →+ E) (m : ℕ) (Q : E[X]) (i : ℕ) :
    (polMap ψ m Q).coeff i = if i ≤ m then ψ (Q.coeff i) else 0 := by
  simp only [polMap, finsetSum_coeff, coeff_monomial_apply]
  rw [Finset.sum_ite_eq' (Finset.range (m + 1)) i]
  simp

theorem natDegree_polMap_le (ψ : E →+ E) (m : ℕ) (Q : E[X]) : (polMap ψ m Q).natDegree ≤ m := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro i hi
  rw [coeff_polMap, if_neg (by omega)]

variable (k : Subfield E)

theorem coeff_mem_mul {S T : PowerSeries E} (hS : ∀ n, PowerSeries.coeff n S ∈ k)
    (hT : ∀ n, PowerSeries.coeff n T ∈ k) : ∀ n, PowerSeries.coeff n (S * T) ∈ k := by
  intro n
  rw [PowerSeries.coeff_mul]
  exact sum_mem fun p _ => mul_mem (hS _) (hT _)

theorem coeff_mem_one : ∀ n, PowerSeries.coeff n (1 : PowerSeries E) ∈ k := by
  intro n
  rw [PowerSeries.coeff_one]
  split_ifs
  · exact one_mem k
  · exact zero_mem k

theorem coeff_mem_pow {S : PowerSeries E} (hS : ∀ n, PowerSeries.coeff n S ∈ k) (i : ℕ) :
    ∀ n, PowerSeries.coeff n (S ^ i) ∈ k := by
  induction i with
  | zero => simpa using coeff_mem_one k
  | succ i ih => rw [pow_succ]; exact coeff_mem_mul k ih hS

theorem coeff_mem_X : ∀ n, PowerSeries.coeff n (PowerSeries.X : PowerSeries E) ∈ k := by
  intro n
  rw [PowerSeries.coeff_X]
  split_ifs
  · exact one_mem k
  · exact zero_mem k

variable {k}

theorem serMap_mul (ψ : E →+ E) (hψ : ∀ c ∈ k, ∀ x, ψ (c * x) = c * ψ x) {W : PowerSeries E}
    (hW : ∀ n, PowerSeries.coeff n W ∈ k) (S : PowerSeries E) :
    serMap ψ (W * S) = W * serMap ψ S := by
  ext n
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coeff_serMap, PowerSeries.coeff_mul, PowerSeries.coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hψ _ (hW _), coeff_serMap]

theorem serMap_C (ψ : E →+ E) (q : E) : serMap ψ (PowerSeries.C q) = PowerSeries.C (ψ q) := by
  ext n
  rw [coeff_serMap, PowerSeries.coeff_C, PowerSeries.coeff_C]
  split_ifs
  · rfl
  · exact map_zero ψ

theorem serMap_homS (ψ : E →+ E) (hψ : ∀ c ∈ k, ∀ x, ψ (c * x) = c * ψ x) {U : PowerSeries E}
    (hU : ∀ n, PowerSeries.coeff n U ∈ k) (m : ℕ) (Q : E[X]) :
    serMap ψ (homS U m Q) = homS U m (polMap ψ m Q) := by
  unfold homS
  rw [serMap_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hW : ∀ n, PowerSeries.coeff n (U ^ i * PowerSeries.X ^ (2 * (m - i))) ∈ k :=
    coeff_mem_mul k (coeff_mem_pow k hU i) (coeff_mem_pow k (coeff_mem_X k) _)
  rw [coeff_polMap, if_pos hi', mul_assoc, mul_assoc, mul_comm (PowerSeries.C (Q.coeff i)),
    serMap_mul ψ hψ hW, serMap_C, mul_comm]

theorem exists_proj (k : Subfield E) : ∃ ψ : E →+ E, (∀ c ∈ k, ∀ x, ψ (c * x) = c * ψ x) ∧
    (∀ x, ψ x ∈ k) ∧ ψ 1 = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap k E)
    (LinearMap.ker_eq_bot.mpr (algebraMap k E).injective)
  refine ⟨(k.subtype : k →+ E).comp g.toAddMonoidHom, ?_, ?_, ?_⟩
  · intro c hc x
    have := g.map_smul (⟨c, hc⟩ : k) x
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe]
    have h2 : (⟨c, hc⟩ : k) • x = c * x := rfl
    rw [← h2, this]
    rfl
  · intro x
    exact (g x).2
  · have := LinearMap.congr_fun hg 1
    simp only [LinearMap.comp_apply, Algebra.linearMap_apply, map_one, LinearMap.id_apply] at this
    simp [this]

end Proj

theorem proj_trick {E : Type} [Field E] (k : Subfield E) (U V : PowerSeries E)
    (hU : ∀ n, PowerSeries.coeff n U ∈ k) (hV : ∀ n, PowerSeries.coeff n V ∈ k)
    (hU0 : PowerSeries.constantCoeff U = 1) (A B : E[X]) (N : ℕ) (hA : A.natDegree ≤ N + 1)
    (hB : B.Monic) (hBd : B.natDegree = N) (hc : IsCoprime A B)
    (h : V * homS U N B = homS U (N + 1) A) : ∀ i, B.coeff i ∈ k := by
  obtain ⟨ψ, hψ, hψk, hψ1⟩ := exists_proj k
  set A' := polMap ψ (N + 1) A with hA'
  set B' := polMap ψ N B with hB'
  have hA'd : A'.natDegree ≤ N + 1 := natDegree_polMap_le ψ _ A
  have hB'd : B'.natDegree ≤ N := natDegree_polMap_le ψ _ B
  have h' : V * homS U N B' = homS U (N + 1) A' := by
    rw [hA', hB', ← serMap_homS ψ hψ hU, ← serMap_homS ψ hψ hU, ← serMap_mul ψ hψ hV, h]
  have hBN : B'.coeff N = 1 := by
    rw [hB', coeff_polMap, if_pos le_rfl, ← hBd, hB.coeff_natDegree, hψ1]
  have hB'deg : B'.natDegree = N := by
    refine le_antisymm hB'd (le_natDegree_of_ne_zero ?_)
    rw [hBN]; exact one_ne_zero
  have hB'm : B'.Monic := by
    rw [Monic, leadingCoeff, hB'deg, hBN]
  have hcross : A * B' = A' * B := by
    have h0 : homS U (N + 1 + N) (A * B' - A' * B) = 0 := by
      rw [homS_sub, homS_mul U _ _ _ _ hA hB'd, homS_mul U _ _ _ _ hA'd hBd.le, ← h, ← h']
      ring
    have hdeg : (A * B' - A' * B).natDegree ≤ N + 1 + N := by
      refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact natDegree_mul_le.trans (add_le_add hA hB'd)
      · exact natDegree_mul_le.trans (add_le_add hA'd hBd.le)
    exact sub_eq_zero.mp (homS_eq_zero U hU0 _ _ hdeg h0)
  have hdvd : B ∣ B' := by
    refine hc.symm.dvd_of_dvd_mul_left ?_
    rw [hcross]
    exact dvd_mul_left _ _
  have heq : B = B' :=
    (eq_of_monic_of_dvd_of_natDegree_le hB hB'm hdvd (by rw [hB'deg, hBd])).symm
  intro i
  rw [heq, hB', coeff_polMap]
  split_ifs
  · exact hψk _
  · exact zero_mem k

end ReciprocityTheory.ChartRestriction.L1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedSqrt
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial

namespace ReciprocityTheory.ChartRestriction.L1

theorem sqrt_poly {E : Type} [Field E] [CharZero E] (k : Subfield E) (h : E[X]) (hm : h.Monic)
    (hk : ∀ i, (h ^ 2).coeff i ∈ k) : ∀ i, h.coeff i ∈ k := by
  have key : ∀ m i : ℕ, h.natDegree ≤ i + m → h.coeff i ∈ k := by
    intro m
    induction m with
    | zero =>
      intro i hi
      rcases Nat.eq_or_lt_of_le (by simpa using hi : h.natDegree ≤ i) with h1 | h1
      · rw [← h1, hm.coeff_natDegree]; exact k.one_mem
      · rw [coeff_eq_zero_of_natDegree_lt h1]; exact k.zero_mem
    | succ m ih =>
      intro i hi
      by_cases h0 : h.natDegree ≤ i + m
      · exact ih i h0
      have hin : i < h.natDegree := by omega
      set n := h.natDegree with hn
      have hmem : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal (i + n),
          h.coeff x.1 * h.coeff x.2 - (if x = (i, n) then h.coeff i else 0)
            - (if x = (n, i) then h.coeff i else 0) ∈ k := by
        rintro ⟨a, b⟩ hx
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        simp only at hx
        by_cases ha : a = i
        · have hb : b = n := by omega
          subst ha; subst hb
          have hne : ¬ ((a, h.natDegree) = (h.natDegree, a)) := by
            intro he
            have := (Prod.mk.injEq _ _ _ _ ▸ he : a = h.natDegree ∧ h.natDegree = a).1
            omega
          rw [if_pos rfl, if_neg hne, hm.coeff_natDegree]
          simp [k.zero_mem]
        by_cases ha' : a = n
        · have hb : b = i := by omega
          subst hb
          rw [ha']
          have hne : ¬ ((n, b) = (b, n)) := by
            intro he
            have := (Prod.mk.injEq _ _ _ _ ▸ he : n = b ∧ b = n).1
            omega
          rw [if_neg hne, if_pos rfl, hn, hm.coeff_natDegree]
          simp [k.zero_mem]
        have hne1 : ¬ ((a, b) = (i, n)) := fun he => ha (congrArg Prod.fst he)
        have hne2 : ¬ ((a, b) = (n, i)) := fun he => ha' (congrArg Prod.fst he)
        rw [if_neg hne1, if_neg hne2, sub_zero, sub_zero]
        rcases lt_or_gt_of_ne ha with h1 | h1
        · have : n < b := by omega
          show h.coeff a * h.coeff b ∈ k
          rw [coeff_eq_zero_of_natDegree_lt this, mul_zero]; exact k.zero_mem
        · rcases lt_or_gt_of_ne ha' with h2 | h2
          · exact k.mul_mem (ih a (by omega)) (ih b (by omega))
          · show h.coeff a * h.coeff b ∈ k
            rw [coeff_eq_zero_of_natDegree_lt h2, zero_mul]; exact k.zero_mem
      have hsum := k.sum_mem hmem
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← coeff_mul, ← pow_two,
        Finset.sum_ite_eq', Finset.sum_ite_eq',
        if_pos (by simp),
        if_pos (by simp [add_comm])] at hsum
      have h2 : (2 : E) * h.coeff i ∈ k := by
        have := k.sub_mem (hk (i + n)) hsum
        have e : (h ^ 2).coeff (i + n) - ((h ^ 2).coeff (i + n) - h.coeff i - h.coeff i)
            = 2 * h.coeff i := by ring
        rwa [e] at this
      have h2k : (2 : E) ∈ k := by
        have := k.add_mem k.one_mem k.one_mem
        rwa [one_add_one_eq_two] at this
      have := k.mul_mem (k.inv_mem h2k) h2
      rwa [← mul_assoc, inv_mul_cancel₀ (two_ne_zero), one_mul] at this
  intro i
  exact key h.natDegree i (by omega)

end ReciprocityTheory.ChartRestriction.L1
end
end

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial

namespace ReciprocityTheory.ChartRestriction.L1

theorem wpNum_coeff_mem (k : Subfield ℂ) {g2 g3 : ℂ} (h2 : g2 ∈ k) (h3 : g3 ∈ k) (n : ℕ) :
    PowerSeries.coeff n (wpNum g2 g3) ∈ k := by
  have h := (seriesMap k ℂ k.subtype ⟨g2, h2⟩ ⟨g3, h3⟩ 0 0).1
  have h' : wpNum g2 g3 = PowerSeries.map k.subtype (wpNum (⟨g2, h2⟩ : k) ⟨g3, h3⟩) := h.symm
  rw [h', PowerSeries.coeff_map]
  exact (PowerSeries.coeff n (wpNum (⟨g2, h2⟩ : k) ⟨g3, h3⟩)).2

theorem kerPoly_mem (L : PeriodPair) (α : ℂ) (T : Finset ℂ) (hα : α ≠ 0) (hs : MulStable L α)
    (hT : IsHalfReps L α T) (k : Subfield ℂ) (h2 : L.g₂ ∈ k) (h3 : L.g₃ ∈ k) (hk : α ∈ k) :
    ∀ i, (rootPoly (xsOf L T)).coeff i ∈ k := by
  apply sqrt_poly k _ (rootPoly_monic _)
  refine proj_trick k (wpNum L.g₂ L.g₃) (PowerSeries.rescale α (wpNum L.g₂ L.g₃))
    (wpNum_coeff_mem k h2 h3) ?_ ?_ (veluNum L.g₂ L.g₃ (xsOf L T)) (rootPoly (xsOf L T) ^ 2)
    (2 * (xsOf L T).card) (veluNum_natDegree_le _ _ _) ((rootPoly_monic _).pow 2) ?_
    (veluNum_coprime _ _ _ fun x hx => hT.fW_ne hx) (velu_series L α T hα hs hT)
  · intro n
    rw [PowerSeries.coeff_rescale]
    exact k.mul_mem (k.pow_mem hk n) (wpNum_coeff_mem k h2 h3 n)
  · simp [wpNum]
  · rw [(rootPoly_monic _).natDegree_pow, rootPoly_natDegree]

theorem prod_mem_of_rootPoly {E : Type} [Field E] (k : Subfield E) (xs : Finset E)
    (h : ∀ i, (rootPoly xs).coeff i ∈ k) : ∏ x ∈ xs, x ∈ k := by
  have h0 : (rootPoly xs).coeff 0 = (-1) ^ xs.card * ∏ x ∈ xs, x := by
    rw [Polynomial.coeff_zero_eq_eval_zero, rootPoly, Polynomial.eval_prod]
    simp only [eval_sub, eval_X, eval_C, zero_sub]
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun x _ => (neg_one_mul x).symm
  have h1 : ∏ x ∈ xs, x = (-1) ^ xs.card * (rootPoly xs).coeff 0 := by
    rw [h0, ← mul_assoc, ← mul_pow]
    simp
  rw [h1]
  exact k.mul_mem (k.pow_mem (k.neg_mem k.one_mem) _) (h 0)

end ReciprocityTheory.ChartRestriction.L1
end
end

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

theorem sqD_eq (d r : ℕ) :
    (r : ℂ) + redSqD d = (((r : ℤ) - 1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * omegaK d := by
  unfold redSqD
  push_cast
  ring

theorem sqD_normSq (d r : ℕ) : Complex.normSq ((r : ℂ) + redSqD d) = ((r ^ 2 + d : ℕ) : ℝ) := by
  unfold redSqD omegaK
  have h : (r : ℂ) + (2 * ((1 + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2) - 1)
      = ⟨(r : ℝ), Real.sqrt d⟩ := by
    apply Complex.ext <;> simp <;> ring
  rw [h, Complex.normSq_mk, Real.mul_self_sqrt (Nat.cast_nonneg d)]
  push_cast
  ring

theorem sqD_mulStable (d : ℕ) (L : PeriodPair) (hCM : HasCMBy d L) (r : ℕ) : MulStable L ((r : ℂ) + redSqD d) := by
  rw [sqD_eq]
  exact (hasCMByStable d L hCM _ _).1

theorem kerProdAt_of_norm (d : ℕ) (L : PeriodPair) (hCM : HasCMBy d L) (l e r : ℕ) (hodd : Odd (r ^ 2 + d))
    (hl : ¬ l ∣ r ^ 2 + d) (he : ¬ e ∣ r ^ 2 + d) (he' : ¬ e ∣ (r ^ 2 + d - 1) / 2) :
    KerProdAt d L l e := by
  have hN := sqD_normSq d r
  have hs := sqD_mulStable d L hCM r
  have hα : (r : ℂ) + redSqD d ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hN
    have h1 : r ^ 2 + d = 0 := by exact_mod_cast hN.symm
    rw [h1] at hodd
    exact absurd hodd (by decide)
  obtain ⟨T, hT⟩ := halfReps_exist L _ hα hs _ hN hodd
  have hcard : 2 * T.card + 1 = r ^ 2 + d := by
    have h1 := hT.card hα hs
    rw [hN] at h1
    exact_mod_cast h1
  have hcard' : T.card = (r ^ 2 + d - 1) / 2 := by omega
  refine ⟨r ^ 2 + d, T, hl, he, by rw [hcard']; exact he', ?_, ?_⟩
  · intro z hz
    exact ⟨hT.notMem hz, ker_norm hs hN (hT.1 z hz).1⟩
  · intro k h2 h3 hk
    have hαk : (r : ℂ) + redSqD d ∈ k := by
      unfold redSqD
      exact k.add_mem (natCast_mem k r)
        (k.sub_mem (k.mul_mem (by exact_mod_cast natCast_mem k 2) hk) k.one_mem)
    have h4 := prod_mem_of_rootPoly k (xsOf L T) (kerPoly_mem L _ T hα hs hT k h2 h3 hαk)
    unfold xsOf at h4
    rwa [Finset.prod_image (fun a ha b hb hab => hT.injOn ha hb hab)] at h4

theorem kerProd_prin (d : ℕ) (L : PeriodPair) (hd4 : d % 4 = 3) (hCM : HasCMBy d L) (l : ℕ) (hl : l.Prime)
    (h5 : 5 ≤ l) (hld : ¬ l ∣ d) (e : ℕ) (he : e = 2 ∨ e = 3 ∧ ¬ 3 ∣ d) : KerProdAt d L l e := by
  rcases he with rfl | ⟨rfl, h3⟩
  · refine kerProdAt_of_norm d L hCM l 2 0 ?_ ?_ ?_ ?_
    · rw [Nat.odd_iff]; omega
    · simpa using hld
    · omega
    · omega
  · have hmod : d % 3 = 1 ∨ d % 3 = 2 := by omega
    rcases hmod with h1 | h2
    · by_cases hl2 : l ∣ 2 ^ 2 + d
      · have hl4 : ¬ l ∣ 4 ^ 2 + d := by
          intro h
          have h12 : l ∣ 12 := by
            have := Nat.dvd_sub h hl2
            have e12 : 4 ^ 2 + d - (2 ^ 2 + d) = 12 := by omega
            rwa [e12] at this
          have hle : l ≤ 12 := Nat.le_of_dvd (by norm_num) h12
          interval_cases l <;> omega
        refine kerProdAt_of_norm d L hCM l 3 4 ?_ hl4 ?_ ?_
        · rw [Nat.odd_iff]; omega
        · omega
        · omega
      · refine kerProdAt_of_norm d L hCM l 3 2 ?_ hl2 ?_ ?_
        · rw [Nat.odd_iff]; omega
        · omega
        · omega
    · refine kerProdAt_of_norm d L hCM l 3 0 ?_ ?_ ?_ ?_
      · rw [Nat.odd_iff]; omega
      · simpa using hld
      · omega
      · omega

end ReciprocityTheory.ChartRestriction.L1
