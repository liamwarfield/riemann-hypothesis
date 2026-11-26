module

public import Development.EtaleCohomology.DivisorCycles.CycSpecQzkPf

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalEig
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qp10.Mat :
    Type → ℕ → Type :=
    fun (C : Type) (N : ℕ) ↦ Matrix (Fin N) (Fin N) C

theorem UpperTheory.Reformulated.B.Qp10.aeval_eig :
    ∀ {C : Type} [inst : Field C] {N : ℕ} (y : UpperTheory.Reformulated.B.Qp10.Mat C N) (μ : C) (v : Fin N → C),
      Matrix.mulVec y v = μ • v →
        ∀ (Q : Polynomial C),
          Matrix.mulVec ((Polynomial.aeval y : Polynomial C → UpperTheory.Reformulated.B.Qp10.Mat C N) Q) v = Polynomial.eval μ Q • v := by
  intro C _ N y μ v h Q
  have hpow : ∀ n : ℕ, Matrix.mulVec (y ^ n) v = μ ^ n • v := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, Matrix.one_mulVec, one_smul]
    | succ n ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ']
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add (f := _), Matrix.add_mulVec, hp, hq, Polynomial.eval_add, add_smul]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.eval_monomial, ← Algebra.smul_def,
      Matrix.smul_mulVec, hpow, smul_smul]
end

section -- merged from Development.EtaleCohomology.DivisorCycles.FixScalOf
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div Polynomial
namespace LateralTheory.DivDb.ScalarFixedPointsUnderAeval
open LateralTheory.DivDb

variable {C : Type} [Field C] {N : ℕ}

theorem comm_aeval (y p : Mat C N) (h : Commute y p) (Q : C[X]) : Commute (aeval y Q) p := by
  induction Q using Polynomial.induction_on with
  | C a => simpa using Algebra.commute_algebraMap_left a p
  | add f g hf hg => simpa using hf.add_left hg
  | monomial k a _ =>
    simp only [map_mul, map_pow, aeval_C, aeval_X]
    exact (Algebra.commute_algebraMap_left a p).mul_left (h.pow_left _)

theorem aeval_eig (y : Mat C N) (μ : C) (v : Fin N → C) (hv : y *ᵥ v = μ • v) (Q : C[X]) :
    aeval y Q *ᵥ v = Q.eval μ • v :=
  _root_.UpperTheory.Reformulated.B.Qp10.aeval_eig y μ v hv Q

theorem same_fix {n : ℕ} (π : Equiv.Perm (Fin n)) (i a : Fin n) (hi : π i = i) (h : π.SameCycle i a) : a = i := by
  obtain ⟨z, hz⟩ := h
  rw [Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hi] at hz
  exact hz.symm

theorem kill {n : ℕ} (p : Fin n → Mat C N) (y : Mat C N) (π : Equiv.Perm (Fin n)) (l : Fin n → C) (hp : Sys p)
    (hd : Disj y π p)
    (hv : ∀ j, ∃ v : Fin N → C, v ≠ 0 ∧ y *ᵥ v = l j • v ∧ ∀ k, ¬ π.SameCycle j k → p k *ᵥ v = 0)
    (i : Fin n) (hi : π i = i) (hyi : Commute y (p i)) (S : Finset (Fin n)) (hS : i ∉ S) :
    ∀ w : Fin N → C, p i *ᵥ w = w → aeval y (∏ j ∈ S, (X - Polynomial.C (l j))) *ᵥ w = 0 → w = 0 := by
  induction S using Finset.induction_on with
  | empty => intro w _ h; simpa using h
  | insert a s ha ih =>
    intro w hw h
    have hai : a ≠ i := fun h' => hS (h' ▸ Finset.mem_insert_self a s)
    have his : i ∉ s := fun h' => hS (Finset.mem_insert_of_mem h')
    rw [Finset.prod_insert ha, map_mul, ← mulVec_mulVec] at h
    by_cases h0 : aeval y (∏ j ∈ s, (X - Polynomial.C (l j))) *ᵥ w = 0
    · exact ih his w hw h0
    exfalso
    set w' := aeval y (∏ j ∈ s, (X - Polynomial.C (l j))) *ᵥ w with hw'
    have heig : y *ᵥ w' = l a • w' := by
      simp only [map_sub, aeval_X, aeval_C, sub_mulVec, Algebra.algebraMap_eq_smul_one, smul_mulVec,
        one_mulVec, sub_eq_zero] at h
      exact h
    have hc := comm_aeval y (p i) hyi (∏ j ∈ s, (X - Polynomial.C (l j)))
    have hcond : ∀ k, ¬ π.SameCycle i k → p k *ᵥ w' = 0 := by
      intro k hk
      have hki : k ≠ i := fun h' => hk (h' ▸ Equiv.Perm.SameCycle.refl π i)
      rw [hw', ← hw, mulVec_mulVec, mulVec_mulVec, mul_assoc, hc.eq, ← mul_assoc, hp.1.ortho hki, zero_mul, zero_mulVec]
    obtain ⟨v, hv0, hyv, hvc⟩ := hv a
    exact hd i a (fun h' => hai (same_fix π i a hi h')) (l a) w' v h0 hv0 heig hyv hcond hvc

theorem FixScal_of : LateralTheory.DivDb.CycleCountPf.FixScal := by
  intro C _ _ _ N n p y π l hp hyp hdeg hd hl hv i hi
  obtain ⟨q, hq0, hqd, hqy⟩ := hdeg
  have hroot : ∀ j, q.IsRoot (l j) := by
    intro j
    obtain ⟨v, hv0, hyv, -⟩ := hv j
    have := aeval_eig y (l j) v hyv q
    rw [hqy, zero_mulVec, eq_comm, smul_eq_zero] at this
    exact this.resolve_right hv0
  set s : Multiset C := Multiset.map l Finset.univ.val with hs
  have hnd : s.Nodup := Multiset.Nodup.map hl Finset.univ.nodup
  have hle : s ≤ q.roots := (Multiset.le_iff_subset hnd).2 (fun a ha => by
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 ha
    exact (mem_roots hq0).2 (hroot j))
  obtain ⟨r, hr⟩ := (Multiset.prod_X_sub_C_dvd_iff_le_roots hq0 s).2 hle
  set P := (s.map fun a => X - Polynomial.C a).prod with hPdef
  have hPm : P.Monic := monic_multiset_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)
  have hPd : P.natDegree = n := by
    rw [hPdef, natDegree_multiset_prod_X_sub_C_eq_card, hs, Multiset.card_map, Finset.card_val,
      Finset.card_univ, Fintype.card_fin]
  have hr0 : r ≠ 0 := by rintro rfl; exact hq0 (by rw [hr, mul_zero])
  have hrd : r.natDegree = 0 := by
    have := hPm.natDegree_mul' hr0
    rw [← hr, hPd] at this; omega
  have hc0 : r.coeff 0 ≠ 0 := by
    intro h; apply hr0; rw [eq_C_of_natDegree_eq_zero hrd, h, map_zero]
  have hPy : aeval y P = 0 := by
    rw [hr, eq_C_of_natDegree_eq_zero hrd, map_mul, aeval_C, Algebra.algebraMap_eq_smul_one, mul_smul_one,
      smul_eq_zero] at hqy
    exact hqy.resolve_left hc0
  have hPP : P = ∏ j, (X - Polynomial.C (l j)) := by
    rw [hPdef, hs, Multiset.map_map, Finset.prod_eq_multiset_prod]; rfl
  rw [hPP, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), mul_comm, map_mul] at hPy
  have hyi : Commute y (p i) := by have := hyp i; rw [hi] at this; exact this
  set M := aeval y (X - Polynomial.C (l i)) with hM
  have hMc : Commute M (p i) := comm_aeval y (p i) hyi _
  have hidem : p i * p i = p i := hp.1.idem i
  have hMp : M * p i = 0 := by
    rw [ext_iff_mulVec]
    intro u
    rw [zero_mulVec]
    apply kill p y π l hp hd hv i hi hyi (Finset.univ.erase i) (Finset.notMem_erase i _)
    · rw [mulVec_mulVec, ← mul_assoc, ← hMc.eq, mul_assoc, hidem]
    · rw [mulVec_mulVec, ← mul_assoc, hPy, zero_mul, zero_mulVec]
  refine ⟨l i, ?_⟩
  rw [hM, map_sub, aeval_X, aeval_C, sub_mul, sub_eq_zero, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
    one_mul] at hMp
  exact hMp

end LateralTheory.DivDb.ScalarFixedPointsUnderAeval
end

section -- merged from Development.EtaleCohomology.DivisorCycles.AlgStruct2
open Matrix
namespace LateralTheory.DivDb
namespace AlgStruct₂

variable {C : Type} [Field C] {N n : ℕ} {p : Fin n → Mat C N}

theorem pp (hp : Sys p) (i : Fin n) : p i * p i = p i := (hp.1.idem i).eq
theorem pp' (hp : Sys p) (i : Fin n) (X : Mat C N) : p i * (p i * X) = p i * X := by
  rw [← mul_assoc, pp hp]
theorem pq (hp : Sys p) {i j : Fin n} (h : i ≠ j) : p i * p j = 0 := hp.1.ortho h
theorem pq' (hp : Sys p) {i j : Fin n} (h : i ≠ j) (X : Mat C N) : p i * (p j * X) = 0 := by
  rw [← mul_assoc, pq hp h, zero_mul]

theorem corner_comm (hp : Sys p) (X : Mat C N) (i m : Fin n) :
    p i * X * p i * p m = p m * (p i * X * p i) := by
  by_cases h : m = i
  · rw [h]; simp only [mul_assoc, pp hp, pp' hp]
  · simp only [mul_assoc, pq hp (Ne.symm h), pq' hp h, mul_zero]

theorem decomp (hp : Sys p) (a b : Mat C N) (i k : Fin n) :
    p i * (a * b) * p k = ∑ j, p i * a * p j * (p j * b * p k) := by
  have h1 : a * b = a * (∑ j, p j) * b := by rw [hp.1.complete, mul_one]
  rw [h1]; simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [mul_assoc, pp' hp]

theorem expand (hp : Sys p) (Y : Mat C N) : Y = ∑ i, ∑ j, p i * Y * p j := by
  have h : Y = (∑ i, p i) * Y * (∑ j, p j) := by rw [hp.1.complete, one_mul, mul_one]
  conv_lhs => rw [h]
  rw [Finset.sum_mul, Finset.sum_mul]
  simp only [Finset.mul_sum]

def S (p : Fin n → Mat C N) (g : Submodule C (Mat C N)) : Set (Mat C N) :=
  {a | (∀ i j, i ≠ j → p i * a * p j ∈ g) ∧ ∀ i, ∃ c : C, p i * a * p i = c • p i}

variable {g : Submodule C (Mat C N)}

theorem S_add {a b : Mat C N} (ha : a ∈ S p g) (hb : b ∈ S p g) : a + b ∈ S p g := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · rw [mul_add, add_mul]; exact g.add_mem (ha.1 i j h) (hb.1 i j h)
  · obtain ⟨c, hc⟩ := ha.2 i; obtain ⟨c', hc'⟩ := hb.2 i
    exact ⟨c + c', by rw [mul_add, add_mul, hc, hc', add_smul]⟩

theorem S_alg (hp : Sys p) (r : C) : algebraMap C (Mat C N) r ∈ S p g := by
  refine ⟨fun i j h => ?_, fun i => ⟨r, ?_⟩⟩
  · rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc, pq hp h, smul_zero]
    exact g.zero_mem
  · rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc, pp hp]

theorem S_mul (hp : Sys p) (hbr : ∀ Y ∈ g, ∀ Z ∈ g, Y * Z - Z * Y ∈ g)
    (hdiag : ∀ Y ∈ g, (∀ i, Y * p i = p i * Y) → ∀ i, ∃ c : C, Y * p i = c • p i)
    {a b : Mat C N} (ha : a ∈ S p g) (hb : b ∈ S p g) : a * b ∈ S p g := by
  refine ⟨fun i k hik => ?_, fun i => ?_⟩
  · rw [decomp hp]
    refine g.sum_mem fun j _ => ?_
    by_cases hji : j = i
    · rw [hji]; obtain ⟨c, hc⟩ := ha.2 i
      have e : p i * (p i * b * p k) = p i * b * p k := by simp only [mul_assoc, pp' hp]
      rw [hc, smul_mul_assoc, e]; exact g.smul_mem _ (hb.1 _ _ hik)
    by_cases hjk : j = k
    · rw [hjk]; obtain ⟨c, hc⟩ := hb.2 k
      have e : p i * a * p k * p k = p i * a * p k := by simp only [mul_assoc, pp hp]
      rw [hc, mul_smul_comm, e]; exact g.smul_mem _ (ha.1 _ _ hik)
    have h := hbr _ (ha.1 i j (Ne.symm hji)) _ (hb.1 j k hjk)
    have z : p j * b * p k * (p i * a * p j) = 0 := by
      simp only [mul_assoc, pq' hp (Ne.symm hik), mul_zero]
    rwa [z, sub_zero] at h
  · have key : ∀ j, ∃ c : C, p i * a * p j * (p j * b * p i) = c • p i := by
      intro j
      by_cases hji : j = i
      · rw [hji]; obtain ⟨c, hc⟩ := ha.2 i; obtain ⟨c', hc'⟩ := hb.2 i
        exact ⟨c * c', by rw [hc, hc', smul_mul_assoc, mul_smul_comm, pp hp, smul_smul]⟩
      have hZ := hbr _ (ha.1 i j (Ne.symm hji)) _ (hb.1 j i hji)
      have e1 : p i * a * p j * (p j * b * p i) = p i * (a * p j * (p j * b)) * p i := by
        simp only [mul_assoc]
      have e2 : p j * b * p i * (p i * a * p j) = p j * (b * p i * (p i * a)) * p j := by
        simp only [mul_assoc]
      rw [e1, e2] at hZ
      have hc : ∀ m, (p i * (a * p j * (p j * b)) * p i - p j * (b * p i * (p i * a)) * p j) * p m =
          p m * (p i * (a * p j * (p j * b)) * p i - p j * (b * p i * (p i * a)) * p j) := by
        intro m; rw [sub_mul, mul_sub, corner_comm hp, corner_comm hp]
      obtain ⟨c, hcZ⟩ := hdiag _ hZ hc i
      refine ⟨c, ?_⟩
      rw [e1, ← hcZ, sub_mul]
      have f1 : p i * (a * p j * (p j * b)) * p i * p i = p i * (a * p j * (p j * b)) * p i := by
        simp only [mul_assoc, pp hp]
      have f2 : p j * (b * p i * (p i * a)) * p j * p i = 0 := by
        simp only [mul_assoc, pq hp hji, mul_zero]
      rw [f1, f2, sub_zero]
    choose f hf using key
    exact ⟨∑ j, f j, by rw [decomp hp, Finset.sum_smul]; exact Finset.sum_congr rfl fun j _ => hf j⟩

theorem S_of_mem (hp : Sys p) (hoff : ∀ Y ∈ g, ∀ i j, i ≠ j → p i * Y * p j ∈ g)
    (hdiag : ∀ Y ∈ g, (∀ i, Y * p i = p i * Y) → ∀ i, ∃ c : C, Y * p i = c • p i)
    {Y : Mat C N} (hY : Y ∈ g) : Y ∈ S p g := by
  refine ⟨hoff Y hY, fun i => ?_⟩
  set D := ∑ k, p k * Y * p k with hDdef
  have hsplit : Y = D + ∑ k, ∑ j ∈ Finset.univ.erase k, p k * Y * p j := by
    conv_lhs => rw [expand hp Y]
    rw [hDdef, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => (Finset.add_sum_erase _ _ (Finset.mem_univ k)).symm
  have hD : D ∈ g := by
    have : D = Y - ∑ k, ∑ j ∈ Finset.univ.erase k, p k * Y * p j := by
      rw [eq_sub_iff_add_eq, ← hsplit]
    rw [this]
    refine g.sub_mem hY (g.sum_mem fun k _ => g.sum_mem fun j hj => hoff Y hY k j ?_)
    exact Ne.symm (Finset.ne_of_mem_erase hj)
  have hcomm : ∀ m, D * p m = p m * D := by
    intro m; rw [hDdef, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => corner_comm hp Y k m
  obtain ⟨c, hc⟩ := hdiag D hD hcomm i
  refine ⟨c, ?_⟩
  rw [← hc, hDdef, Finset.sum_mul, Finset.sum_eq_single i]
  · simp only [mul_assoc, pp hp]
  · intro k _ hki; simp only [mul_assoc, pq hp hki, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

def Sa (hp : Sys p) (hbr : ∀ Y ∈ g, ∀ Z ∈ g, Y * Z - Z * Y ∈ g)
    (hdiag : ∀ Y ∈ g, (∀ i, Y * p i = p i * Y) → ∀ i, ∃ c : C, Y * p i = c • p i) :
    Subalgebra C (Mat C N) where
  carrier := S p g
  mul_mem' := S_mul hp hbr hdiag
  add_mem' := S_add
  algebraMap_mem' := S_alg hp

theorem AlgStruct_of : AlgStruct := by
  intro C _ N n p g hp hbr hoff hdiag a ha
  have hle : Algebra.adjoin C (g : Set (Mat C N)) ≤ Sa hp hbr hdiag :=
    Algebra.adjoin_le fun Y hY => S_of_mem hp hoff hdiag hY
  exact hle ha

end AlgStruct₂
end LateralTheory.DivDb
end

section -- merged from Development.EtaleCohomology.DivisorCycles.ProjPf
open Matrix Polynomial PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.ProjPf

variable {C : Type} [Field C] {N n : ℕ}

theorem root_minpoly (X : LateralTheory.DivDb.Mat C N) (c : C) (h : X.charpoly.IsRoot c) :
    (minpoly C X).IsRoot c := by
  have h1 : Module.End.HasEigenvalue (Matrix.toLin' X) c :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2 (by rw [Matrix.charpoly_toLin']; exact h)
  rw [← Matrix.minpoly_toLin']
  exact Module.End.hasEigenvalue_iff_isRoot.1 h1

theorem prod_dvd (e : Fin n → C) (he : Function.Injective e) (f : C[X]) (hf : ∀ k, f.eval (e k) = 0) :
    (∏ k, (X - Polynomial.C (e k))) ∣ f := by
  apply Finset.prod_dvd_of_coprime
  · exact fun a _ b _ hab => Polynomial.pairwise_coprime_X_sub_C he hab
  · intro k _; exact Polynomial.dvd_iff_isRoot.2 (hf k)

theorem minpoly_eq (X : LateralTheory.DivDb.Mat C N) (e : Fin n → C) (he : Function.Injective e)
    (hD : LateralTheory.DivDb.Deg n X) (hr : ∀ i, X.charpoly.IsRoot (e i)) :
    minpoly C X = ∏ k, (Polynomial.X - Polynomial.C (e k)) := by
  obtain ⟨q, hq0, hqd, hq⟩ := hD
  have hint : IsIntegral C X := Matrix.isIntegral X
  have hmon : (minpoly C X).Monic := minpoly.monic hint
  have hdvd : (∏ k, (Polynomial.X - Polynomial.C (e k))) ∣ minpoly C X :=
    prod_dvd e he _ (fun k => root_minpoly X _ (hr k))
  have hPm : (∏ k, (Polynomial.X - Polynomial.C (e k))).Monic :=
    monic_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)
  have hdeg : (minpoly C X).natDegree ≤ n := by
    have := Polynomial.natDegree_le_of_dvd (minpoly.dvd C X hq) hq0
    omega
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le hPm hmon hdvd
  rw [natDegree_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  exact hdeg

theorem evb (e : Fin n → C) (he : Function.Injective e) (i k : Fin n) :
    (Lagrange.basis Finset.univ e i).eval (e k) = if k = i then 1 else 0 := by
  split_ifs with h
  · subst h; exact Lagrange.eval_basis_self he.injOn (Finset.mem_univ _)
  · exact Lagrange.eval_basis_of_ne (Ne.symm h) (Finset.mem_univ _)

theorem vanish (X : LateralTheory.DivDb.Mat C N) (e : Fin n → C) (he : Function.Injective e)
    (hD : LateralTheory.DivDb.Deg n X) (hr : ∀ i, X.charpoly.IsRoot (e i)) (f : C[X])
    (hf : ∀ k, f.eval (e k) = 0) : aeval X f = 0 := by
  rw [← minpoly.dvd_iff, minpoly_eq X e he hD hr]
  exact prod_dvd e he f hf

end LateralTheory.DivDb.ProjPf

namespace LateralTheory.DivDb
open LateralTheory.DivDb.ProjPf

theorem Proj_of : Proj := by
  intro C _ N n X e he hD hr
  classical
  set b : Fin n → C[X] := fun i => Lagrange.basis Finset.univ e i with hb
  have V := vanish X e he hD hr
  refine ⟨fun i => aeval X (b i), ⟨⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩, fun i => ?_⟩, ?_, fun i => ?_⟩
  · show aeval X (b i) * aeval X (b i) = aeval X (b i)
    rw [← sub_eq_zero, ← map_mul, ← map_sub]
    apply V; intro k
    simp only [hb, eval_sub, eval_mul, evb e he]
    split_ifs <;> simp
  · show aeval X (b i) * aeval X (b j) = 0
    rw [← map_mul]
    apply V; intro k
    simp only [hb, eval_mul, evb e he]
    split_ifs with h1 h2 <;> simp_all
  · show ∑ i, aeval X (b i) = 1
    have h : aeval X (∑ i, b i - 1) = 0 := by
      apply V; intro k
      simp only [hb, eval_sub, eval_finsetSum, evb e he, eval_one]
      simp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_one, map_sum, sub_eq_zero] at h
    exact h
  · intro h0
    have h1 : minpoly C X ∣ b i := (minpoly.dvd_iff).2 h0
    rw [minpoly_eq X e he hD hr] at h1
    have hne : b i ≠ 0 := Lagrange.basis_ne_zero he.injOn (Finset.mem_univ _)
    have h2 := Polynomial.natDegree_le_of_dvd h1 hne
    rw [natDegree_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)] at h2
    have h3 : (b i).natDegree = n - 1 := by
      simp only [hb]
      rw [Lagrange.natDegree_basis he.injOn (Finset.mem_univ _)]
      simp
    simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one] at h2
    have := i.pos
    omega
  · have : aeval X (Polynomial.X - ∑ i, Polynomial.C (e i) * b i) = 0 := by
      apply V; intro k
      simp only [hb, eval_sub, eval_X, eval_finsetSum, eval_mul, eval_C, evb e he]
      simp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, aeval_X, map_sum, sub_eq_zero] at this
    refine this.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [map_mul, aeval_C, Algebra.smul_def]
  · exact Polynomial.aeval_mem_adjoin_singleton C _

end LateralTheory.DivDb
end

section -- merged from Development.EtaleCohomology.DivisorCycles.DiagScalar2
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.DiagScalar₂
open LateralTheory.DivDb

variable {C : Type} [Field C] {N n : ℕ}

theorem mul_p (p : Fin n → Mat C N) (hp : Sys p) (e : Fin n → C) (j : Fin n) :
    (∑ i, e i • p i) * p j = e j • p j := by
  rw [Finset.sum_mul, Finset.sum_eq_single j]
  · rw [smul_mul_assoc, (hp.1.idem j).eq]
  · intro b _ hb; rw [smul_mul_assoc, hp.1.ortho hb, smul_zero]
  · simp

theorem p_mul (p : Fin n → Mat C N) (hp : Sys p) (e : Fin n → C) (j : Fin n) :
    p j * (∑ i, e i • p i) = e j • p j := by
  rw [Finset.mul_sum, Finset.sum_eq_single j]
  · rw [mul_smul_comm, (hp.1.idem j).eq]
  · intro b _ hb; rw [mul_smul_comm, hp.1.ortho (Ne.symm hb), smul_zero]
  · simp

theorem vec_of (p : Fin n → Mat C N) (hp : Sys p) (i : Fin n) (v : Fin N → C)
    (hv : ∀ k, k ≠ i → p k *ᵥ v = 0) : p i *ᵥ v = v := by
  have h1 : (∑ k, p k) *ᵥ v = v := by rw [hp.1.complete]; simp
  rw [Matrix.sum_mulVec, Finset.sum_eq_single i] at h1
  · exact h1
  · intro b _ hb; exact hv b hb
  · simp

theorem X_vec (p : Fin n → Mat C N) (hp : Sys p) (e : Fin n → C) (i : Fin n) (v : Fin N → C)
    (hv : ∀ k, k ≠ i → p k *ᵥ v = 0) : (∑ k, e k • p k) *ᵥ v = e i • v := by
  have h := vec_of p hp i v hv
  conv_lhs => rw [← h]
  rw [Matrix.mulVec_mulVec, mul_p p hp e i, Matrix.smul_mulVec, h]

theorem root_of_eig (Y : Mat C N) (μ : C) (v : Fin N → C) (hv : v ≠ 0) (h : Y *ᵥ v = μ • v) :
    Y.charpoly.IsRoot μ := by
  rw [Polynomial.IsRoot, Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec, h, Matrix.scalar_apply]
  ext k; simp [Matrix.mulVec_diagonal]

theorem deg_shift (x : Mat C N) (c : C) (h : Deg n x) : Deg n (x + algebraMap C (Mat C N) c) := by
  obtain ⟨q, hq, hd, ha⟩ := h
  refine ⟨Polynomial.taylor (-c) q, ?_, ?_, ?_⟩
  · rwa [Ne, Polynomial.taylor_eq_zero]
  · rwa [Polynomial.natDegree_taylor]
  · rw [Polynomial.taylor_apply, Polynomial.aeval_comp]
    simp [ha]

theorem alg_vec (c : C) (v : Fin N → C) : (algebraMap C (Mat C N) c) *ᵥ v = c • v := by
  rw [Matrix.algebraMap_eq_diagonal]; ext k; simp [Matrix.mulVec_diagonal]

end LateralTheory.DivDb.DiagScalar₂

namespace LateralTheory.DivDb
open DiagScalar₂ in
theorem DiagScalar_of (hC : CycleCount) : DiagScalar := by
  intro C _ _ _ N n p e Y hp he hY hD i
  classical
  have : Infinite C := Infinite.of_injective _ Nat.cast_injective
  set X := ∑ i, e i • p i with hX
  set R := Y.charpoly.roots.toFinset with hR
  set B : Finset C := insert 0 ((R ×ˢ R ×ˢ (Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n))).image
    (fun t => (e t.2.2.2 - e t.2.2.1) / (t.1 - t.2.1))) with hB
  obtain ⟨s, hs⟩ := Infinite.exists_notMem_finset B
  have hs0 : s ≠ 0 := fun h => hs (h ▸ Finset.mem_insert_self _ _)
  set M := s • Y + X with hM
  obtain ⟨c', hc'⟩ := Infinite.exists_notMem_finset ((-M).charpoly.roots.toFinset)
  set y := M + algebraMap C (Mat C N) c' with hy
  have hunit : IsUnit y := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro h0; apply hc'
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero, Polynomial.IsRoot,
      Matrix.eval_charpoly]
    convert h0 using 2
    rw [hy, Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply, sub_neg_eq_add, add_comm]; rfl
  have hcomm : ∀ j, y * p j = p ((1 : Equiv.Perm (Fin n)) j) * y := by
    intro j
    rw [Equiv.Perm.one_apply, hy, hM, add_mul, add_mul, mul_add, mul_add, smul_mul_assoc, mul_smul_comm, hY j,
      hX, mul_p p hp e j, p_mul p hp e j, Algebra.commutes]
  have hdeg : Deg n y := deg_shift _ c' (hD s)
  have key : ∀ (i : Fin n) (l : C) (v : Fin N → C), v ≠ 0 → y *ᵥ v = l • v →
      (∀ k, ¬ i = k → p k *ᵥ v = 0) → ∃ μ ∈ R, s * μ + e i = l - c' := by
    intro i l v hv hyv hpv
    have hXv := X_vec p hp e i v (fun k hk => hpv k (Ne.symm hk))
    have h1 : y *ᵥ v = s • (Y *ᵥ v) + e i • v + c' • v := by
      rw [hy, hM, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, hX, hXv, alg_vec]
    rw [h1] at hyv
    have h2 : s • (Y *ᵥ v) = (l - c' - e i) • v := by rw [sub_smul, sub_smul, ← hyv]; abel
    refine ⟨s⁻¹ * (l - c' - e i), ?_, by field_simp; ring⟩
    rw [hR, Multiset.mem_toFinset, Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero]
    apply root_of_eig Y _ v hv
    rw [mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  have hdisj : Disj y 1 p := by
    intro i j hij l v w hv hw hyv hyw hpv hpw
    simp only [Equiv.Perm.sameCycle_one] at hij hpv hpw
    obtain ⟨μ, hμ, h1⟩ := key i l v hv hyv hpv
    obtain ⟨μ', hμ', h2⟩ := key j l w hw hyw hpw
    have hne : e i ≠ e j := he.ne hij
    have hμμ : μ - μ' ≠ 0 := by
      intro h; apply hne
      have : μ = μ' := sub_eq_zero.mp h
      subst this; linear_combination h1 - h2
    apply hs
    apply Finset.mem_insert_of_mem
    rw [Finset.mem_image]
    refine ⟨(μ, μ', i, j), by simp [hμ, hμ'], ?_⟩
    show (e j - e i) / (μ - μ') = s
    rw [div_eq_iff hμμ]; linear_combination h2 - h1
  obtain ⟨_, hfix⟩ := hC C N n p y 1 hp hunit hcomm hdeg hdisj
  obtain ⟨c, hc⟩ := hfix i rfl
  refine ⟨s⁻¹ * (c - e i - c'), ?_⟩
  have h4 : y * p i = s • (Y * p i) + e i • p i + c' • p i := by
    rw [hy, hM, add_mul, add_mul, smul_mul_assoc, hX, mul_p p hp e i, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      one_mul]
  rw [h4] at hc
  have h3 : s • (Y * p i) = (c - e i - c') • p i := by rw [sub_smul, sub_smul, ← hc]; abel
  rw [mul_smul, ← h3, smul_smul, inv_mul_cancel₀ hs0, one_smul]

end LateralTheory.DivDb
end

section -- merged from Development.EtaleCohomology.DivisorCycles.GradePf
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div Polynomial
namespace LateralTheory.DivDb.GradePf

section
variable {C : Type} [Field C] {N n : ℕ}

noncomputable def adX (X : Mat C N) : Module.End C (Mat C N) :=
  LinearMap.mulLeft C X - LinearMap.mulRight C X

lemma adX_apply (X Y : Mat C N) : adX X Y = X * Y - Y * X := by
  simp [adX]

lemma pow_mem (f : Module.End C (Mat C N)) (g : Submodule C (Mat C N))
    (hf : ∀ Y ∈ g, f Y ∈ g) (k : ℕ) : ∀ Y ∈ g, (f ^ k) Y ∈ g := by
  induction k with
  | zero => intro Y hY; simpa using hY
  | succ k ih => intro Y hY; rw [pow_succ', Module.End.mul_apply]; exact hf _ (ih Y hY)

lemma aeval_mem (f : Module.End C (Mat C N)) (g : Submodule C (Mat C N))
    (hf : ∀ Y ∈ g, f Y ∈ g) (q : C[X]) : ∀ Y ∈ g, aeval f q Y ∈ g := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    intro Y hY; simp only [map_add (f := _), LinearMap.add_apply]; exact g.add_mem (hp Y hY) (hq Y hY)
  | monomial k a =>
    intro Y hY
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact g.smul_mem _ (pow_mem f g hf k Y hY)

lemma pow_eig (f : Module.End C (Mat C N)) (Z : Mat C N) (c : C) (h : f Z = c • Z) (k : ℕ) :
    (f ^ k) Z = c ^ k • Z := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, h, smul_smul, pow_succ]

lemma aeval_eig (f : Module.End C (Mat C N)) (Z : Mat C N) (c : C) (h : f Z = c • Z) (q : C[X]) :
    aeval f q Z = q.eval c • Z := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, hp, hq, eval_add, add_smul]
  | monomial k a =>
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, pow_eig f Z c h, smul_smul,
      eval_monomial]

lemma lac_key [CharZero C] {e : Fin n → C} (hL : IsLac e) {i j k l : Fin n} (hij : i ≠ j)
    (h : e i - e j = e k - e l) : k = i ∧ l = j := by
  have inj := isLac_inj hL
  have h' : e i + e l = e k + e j := by linear_combination h
  by_contra hne
  have hki : k ≠ i := by
    intro hk; rw [hk] at h'
    exact hne ⟨hk, inj (by linear_combination h')⟩
  have hlj : l ≠ j := by
    intro hl; rw [hl] at h'
    exact hne ⟨(inj (by linear_combination h')).symm, hl⟩
  have hkl : k ≠ l := by
    intro hk; rw [hk] at h; exact hij (inj (by linear_combination h))
  by_cases hil : i = l
  · subst hil
    by_cases hkj : k = j
    · subst hkj
      exact hki (inj (mul_left_cancel₀ (two_ne_zero (α := C)) (by linear_combination -h')))
    · have := hL {i} {k, j} (by simp) (by simp)
        (by simp [Finset.disjoint_left]; exact ⟨hki.symm, hij⟩)
      apply this
      rw [Finset.card_pair hkj, Finset.sum_pair hkj]; simp; linear_combination h'
  · by_cases hkj : k = j
    · subst hkj
      have := hL {i, l} {k} (by simp) (by simp)
        (by simp [Finset.disjoint_left]; exact ⟨hij, hlj⟩)
      apply this
      rw [Finset.card_pair hil, Finset.sum_pair hil]; simp; linear_combination h'
    · have := hL {i, l} {k, j} (by simp) (by simp)
        (by simp [Finset.disjoint_left]; exact ⟨⟨hki.symm, hij⟩, hkl.symm, hlj⟩)
      apply this
      rw [Finset.card_pair hil, Finset.sum_pair hil, Finset.card_pair hkj, Finset.sum_pair hkj]
      rw [h']
end

end LateralTheory.DivDb.GradePf

namespace LateralTheory.DivDb
open LateralTheory.DivDb.GradePf

theorem Grade_of : Grade := by
  intro C _ _ N n p e g hS hL hg Y hY i j hij
  set X := ∑ i, e i • p i with hXdef
  have hco := hS.1
  have hid : ∀ k, p k * p k = p k := fun k => hco.idem k
  have hor : ∀ k l, k ≠ l → p k * p l = 0 := fun k l h => hco.ortho h
  have hsum : ∑ k, p k = 1 := hco.complete
  have hXp : ∀ k, X * p k = e k • p k := by
    intro k; rw [hXdef, Finset.sum_mul]; simp only [smul_mul_assoc]
    rw [Finset.sum_eq_single k]
    · rw [hid]
    · intro b _ hb; rw [hor b k hb, smul_zero]
    · simp
  have hpX : ∀ k, p k * X = e k • p k := by
    intro k; rw [hXdef, Finset.mul_sum]; simp only [mul_smul_comm]
    rw [Finset.sum_eq_single k]
    · rw [hid]
    · intro b _ hb; rw [hor k b (Ne.symm hb), smul_zero]
    · simp
  have hdec : Y = ∑ kl : Fin n × Fin n, p kl.1 * Y * p kl.2 := by
    have : (∑ k, p k) * Y * (∑ l, p l) = ∑ kl : Fin n × Fin n, p kl.1 * Y * p kl.2 := by
      rw [Finset.sum_mul, Finset.sum_mul, Fintype.sum_prod_type]; simp_rw [Finset.mul_sum]
    rw [← this, hsum, one_mul, mul_one]
  have heig : ∀ kl : Fin n × Fin n, adX X (p kl.1 * Y * p kl.2) = (e kl.1 - e kl.2) • (p kl.1 * Y * p kl.2) := by
    intro kl
    rw [adX_apply, ← mul_assoc, ← mul_assoc, hXp, mul_assoc (p kl.1 * Y), hpX]
    simp [sub_smul, smul_mul_assoc, mul_smul_comm]
  have hstab : ∀ Z ∈ g, adX X Z ∈ g := fun Z hZ => by rw [adX_apply]; exact hg Z hZ
  let q : C[X] := ∏ kl ∈ (Finset.univ : Finset (Fin n × Fin n)).erase (i, j), (Polynomial.X - Polynomial.C (e kl.1 - e kl.2))
  have hq : aeval (adX X) q Y = q.eval (e i - e j) • (p i * Y * p j) := by
    conv_lhs => rw [hdec]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp_rw [aeval_eig (adX X) _ _ (heig _)]
    rw [Finset.sum_eq_single (i, j)]
    · intro b _ hb
      have : q.eval (e b.1 - e b.2) = 0 := by
        simp only [q, eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hb, Finset.mem_univ _⟩) (by simp)
      rw [this, zero_smul]
    · simp
  have hq0 : q.eval (e i - e j) ≠ 0 := by
    simp only [q, eval_prod]
    rw [Finset.prod_ne_zero_iff]
    intro kl hkl
    simp only [eval_sub, eval_X, eval_C]
    intro h0
    have := lac_key hL hij (sub_eq_zero.mp h0)
    exact (Finset.mem_erase.mp hkl).1 (Prod.ext this.1 this.2)
  have hm := g.smul_mem (q.eval (e i - e j))⁻¹ (aeval_mem (adX X) g hstab q Y hY)
  rwa [hq, smul_smul, inv_mul_cancel₀ hq0, one_smul] at hm

end LateralTheory.DivDb
end

section -- merged from Development.EtaleCohomology.DivisorCycles.CoeMulInv
open Matrix

namespace LateralTheory.DivDb.EnvStab₂
open LateralTheory.DivDb

variable {Γ C : Type} [Group Γ] [Field C] {N : ℕ}

theorem ev_X (x : Mat C N) (q : Fin N × Fin N) : ev x (MvPolynomial.X q) = x q.1 q.2 := by
  simp [ev]

theorem mem_img (ρ : Γ →* GL (Fin N) C) (h : Γ) : ((ρ h : GL (Fin N) C) : Mat C N) ∈ (img ρ ⊤ : Set (Mat C N)) := by
  simp only [img, SetLike.mem_coe, Submonoid.mem_map]
  exact ⟨h, by simp, rfl⟩

theorem img_cases (ρ : Γ →* GL (Fin N) C) {x : Mat C N} (hx : x ∈ (img ρ ⊤ : Set (Mat C N))) :
    ∃ h : Γ, ((ρ h : GL (Fin N) C) : Mat C N) = x := by
  simp only [img, SetLike.mem_coe, Submonoid.mem_map] at hx
  obtain ⟨h, _, rfl⟩ := hx
  exact ⟨h, rfl⟩

theorem coe_mul_inv (ρ : Γ →* GL (Fin N) C) (g : Γ) :
    ((ρ g : GL (Fin N) C) : Mat C N) * ((ρ g⁻¹ : GL (Fin N) C) : Mat C N) = 1 := by
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem coe_inv_mul (ρ : Γ →* GL (Fin N) C) (g : Γ) :
    ((ρ g⁻¹ : GL (Fin N) C) : Mat C N) * ((ρ g : GL (Fin N) C) : Mat C N) = 1 := by
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

def conjL (G G' : Mat C N) : Mat C N →ₗ[C] Mat C N where
  toFun x := G * x * G'
  map_add' x y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c x := by simp

theorem lie_conj (hC : Chain) (ρ : Γ →* GL (Fin N) C) (g : Γ) (Y : Mat C N) (hY : Y ∈ lie ρ) :
    ((ρ g : GL (Fin N) C) : Mat C N) * Y * ((ρ g⁻¹ : GL (Fin N) C) : Mat C N) ∈ lie ρ := by
  intro f hf
  obtain ⟨f', hev, hd⟩ := hC C N N (conjL (ρ g : Mat C N) (ρ g⁻¹ : Mat C N)) f
  have hf' : f' ∈ Van (img ρ ⊤ : Set (Mat C N)) := by
    intro x hx
    obtain ⟨h, rfl⟩ := img_cases ρ hx
    rw [hev]
    apply hf
    have : conjL (C := C) (N := N) (ρ g : Mat C N) (ρ g⁻¹ : Mat C N) (ρ h : Mat C N)
        = ((ρ (g * h * g⁻¹) : GL (Fin N) C) : Mat C N) := by
      simp [conjL, map_mul, Units.val_mul]
    rw [this]; exact mem_img ρ _
  have h1 : conjL (C := C) (N := N) (ρ g : Mat C N) (ρ g⁻¹ : Mat C N) 1 = 1 := by
    simp only [conjL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_one]; exact coe_mul_inv ρ g
  have := hd 1 Y
  rw [h1] at this
  show dAt f 1 (conjL (C := C) (N := N) (ρ g : Mat C N) (ρ g⁻¹ : Mat C N) Y) = 0
  rw [← this]
  exact hY f' hf'

theorem normd (hC : Chain) (ρ : Γ →* GL (Fin N) C) : Normd ρ (env ρ) := by
  intro g a ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin (lie_conj hC ρ g x hx)
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, coe_mul_inv]
    exact Subalgebra.smul_mem _ (Subalgebra.one_mem _) r
  | add x y _ _ hx hy =>
    rw [Matrix.mul_add, Matrix.add_mul]; exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy =>
    have : ((ρ g : GL (Fin N) C) : Mat C N) * (x * y) * ((ρ g⁻¹ : GL (Fin N) C) : Mat C N)
        = (((ρ g : GL (Fin N) C) : Mat C N) * x * ((ρ g⁻¹ : GL (Fin N) C) : Mat C N)) *
          (((ρ g : GL (Fin N) C) : Mat C N) * y * ((ρ g⁻¹ : GL (Fin N) C) : Mat C N)) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc ((ρ g⁻¹ : GL (Fin N) C) : Mat C N), coe_inv_mul, Matrix.one_mul]
    rw [this]; exact Subalgebra.mul_mem _ hx hy

def lamL (ℓ : Module.Dual C (Fin N → C)) (v : Fin N → C) : Mat C N →ₗ[C] Mat C 1 where
  toFun x := Matrix.of fun _ _ => ℓ (x *ᵥ v)
  map_add' x y := by ext; simp [Matrix.add_mulVec]
  map_smul' c x := by ext; simp [Matrix.smul_mulVec]

theorem lie_keeps (hC : Chain) (ρ : Γ →* GL (Fin N) C) (W : Submodule C (Fin N → C))
    (hW : ∀ g, ∀ v ∈ W, ((ρ g : GL (Fin N) C) : Mat C N) *ᵥ v ∈ W) (Y : Mat C N) (hY : Y ∈ lie ρ)
    (v : Fin N → C) (hv : v ∈ W) : Y *ᵥ v ∈ W := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro ℓ hℓ
  rw [Submodule.mem_dualAnnihilator] at hℓ
  obtain ⟨f', hev, hd⟩ := hC C N 1 (lamL ℓ v) (MvPolynomial.X (0, 0))
  have hf' : f' ∈ Van (img ρ ⊤ : Set (Mat C N)) := by
    intro x hx
    obtain ⟨h, rfl⟩ := img_cases ρ hx
    rw [hev, ev_X]
    simp only [lamL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
    exact hℓ _ (hW h v hv)
  have h0 := hY f' hf'
  rw [hd] at h0
  simpa [dAt, lamL, ev, MvPolynomial.pderiv_X, Fintype.sum_unique, Pi.single_apply, Prod.ext_iff, Fin.fin_one_eq_zero] using h0

theorem keeps (hC : Chain) (ρ : Γ →* GL (Fin N) C) : Keeps ρ (env ρ) := by
  intro W hW a ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact fun v hv => lie_keeps hC ρ W hW x hx v hv
  | algebraMap r =>
    intro v hv
    rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact W.smul_mem r hv
  | add x y _ _ hx hy =>
    intro v hv; rw [Matrix.add_mulVec]; exact W.add_mem (hx v hv) (hy v hv)
  | mul x y _ _ hx hy =>
    intro v hv; rw [← Matrix.mulVec_mulVec]; exact hx _ (hy v hv)

end LateralTheory.DivDb.EnvStab₂

namespace LateralTheory.DivDb

theorem EnvStab_of (hC : Chain) : EnvStab := fun _ _ _ _ _ ρ =>
  ⟨EnvStab₂.normd hC ρ, EnvStab₂.keeps hC ρ⟩

end LateralTheory.DivDb
end

section -- merged from Development.EtaleCohomology.DivisorCycles.StructPf
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.StructPf
open LateralTheory.DivDb

theorem deg_img {Γ C : Type} [Group Γ] [Field C] {N n : ℕ} (ρ : Γ →* GL (Fin N) C)
    (h : ∀ g, Deg n (ρ g : Mat C N)) : ∀ x ∈ (img ρ ⊤ : Submonoid (Mat C N)), Deg n x := by
  intro x hx
  obtain ⟨g, -, rfl⟩ := Submonoid.mem_map.mp hx
  exact h g

theorem Struct_of (hTanDeg : TanDeg) (hProj : Proj) (hTanLie : TanLie) (hGrade : Grade)
    (hDiag : DiagScalar) (hAlg : AlgStruct) (hEnv : EnvStab) (hSemis : Semis) : Struct := by
  intro Γ C _ _ _ _ N n ρ X e hSS hdeg hX hLac hroots

  have hdegL : ∀ Y ∈ lie ρ, Deg n Y := (hTanDeg C N n (img ρ ⊤) (deg_img ρ hdeg)).2
  have hinj : Function.Injective e := isLac_inj hLac

  obtain ⟨p, hSys, hXeq, hadj⟩ := hProj C N n X e hinj (hdegL X hX) hroots
  have hbr : ∀ Y ∈ lie ρ, ∀ Z ∈ lie ρ, Y * Z - Z * Y ∈ lie ρ := hTanLie C N (img ρ ⊤)

  have hoff : ∀ Y ∈ lie ρ, ∀ i j, i ≠ j → p i * Y * p j ∈ lie ρ :=
    hGrade C N n p e (lie ρ) hSys hLac (fun Y hY => by rw [← hXeq]; exact hbr X hX Y hY)

  have hdiag : ∀ Y ∈ lie ρ, (∀ i, Y * p i = p i * Y) → ∀ i, ∃ c : C, Y * p i = c • p i :=
    fun Y hY hc => hDiag C N n p e Y hSys hinj hc (fun s => by
      rw [← hXeq]; exact hdegL _ ((lie ρ).add_mem ((lie ρ).smul_mem s hY) hX))
  have hA := hAlg C N n p (lie ρ) hSys hbr hoff hdiag
  obtain ⟨hNormd, hKeeps⟩ := hEnv Γ C N ρ
  refine ⟨p, hSys, by rw [← hXeq]; exact hX, ⟨fun i => ?_, fun a ha i => (hA a ha).2 i⟩,
    hSemis Γ C N ρ (env ρ) hSS hNormd hKeeps, hNormd, hKeeps, fun a ha i j hij => (hA a ha).1 i j hij⟩
  exact Algebra.adjoin_mono (Set.singleton_subset_iff.mpr hX) (hadj i)

end LateralTheory.DivDb.StructPf
end

section -- merged from Development.EtaleCohomology.DivisorCycles.TanLiePf
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.TanLiePf
open LateralTheory.DivDb

theorem DX_X {C : Type} [Field C] {N : ℕ} (Y : Mat C N) (p : Fin N × Fin N) :
    DX Y (MvPolynomial.X p) = ∑ k, MvPolynomial.C (Y p.1 k) * MvPolynomial.X (k, p.2) := by
  simp [DX, MvPolynomial.mkDerivation_X]

theorem DX_comm {C : Type} [Field C] {N : ℕ} (Y Z : Mat C N) :
    ⁅DX Y, DX Z⁆ = DX (Z * Y - Y * Z) := by
  apply MvPolynomial.derivation_ext
  intro p
  rw [Derivation.commutator_apply, DX_X, DX_X, DX_X]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, MvPolynomial.C_mul', map_smul, DX_X, Finset.smul_sum, smul_smul]
  simp only [Matrix.sub_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib]
  simp only [sub_smul, Finset.sum_smul, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  rw [Derivation.map_smul, Derivation.map_smul, DX_X, DX_X]
  simp only [MvPolynomial.C_mul', Finset.smul_sum, smul_smul, ← Finset.sum_sub_distrib]

end LateralTheory.DivDb.TanLiePf

namespace LateralTheory.DivDb
open LateralTheory.DivDb.TanLiePf

theorem TanLie_of (hF : TanField) : TanLie := by
  intro C _ N S Y hY Z hZ
  have hY' := (hF C N S Y).1 hY
  have hZ' := (hF C N S Z).1 hZ
  have h : Z * Y - Y * Z ∈ Tan (S : Set (Mat C N)) := by
    rw [hF C N S]
    intro f hf
    rw [← DX_comm, Derivation.commutator_apply]
    intro x hx
    have h1 := hY' _ (hZ' f hf) x hx
    have h2 := hZ' _ (hY' f hf) x hx
    simp only [ev, map_sub] at h1 h2 ⊢
    rw [h1, h2, sub_zero]
  have := (Tan (S : Set (Mat C N))).neg_mem h
  simpa using this

end LateralTheory.DivDb
end

namespace LateralTheory.Fin.Struct
theorem etale_divisibility_chain_of_key : LateralTheory.DivDb.Chain := by
  apply LateralTheory.DivDb.Chain_of
theorem etale_tangent_field_extension_of_key : LateralTheory.DivDb.TanField := by
  apply LateralTheory.DivDb.TangentFieldExtension.TanField_of <;> first | exact etale_divisibility_chain_of_key
theorem etale_exponent_vanishing_of_key : LateralTheory.DivDb.ExpVan := by
  apply LateralTheory.DivDb.ExpVan_of <;> first | exact etale_tangent_field_extension_of_key
theorem etale_degree_polynomial_bound : LateralTheory.DivDb.DegPoly := by
  apply LateralTheory.DivDb.DegPoly₂.DegPoly_of
theorem etale_tangent_degree_bound_of_key : LateralTheory.DivDb.TanDeg := by
  apply LateralTheory.DivDb.TangentDegree.TanDeg_of <;> first | exact etale_exponent_vanishing_of_key | exact etale_degree_polynomial_bound
theorem etale_projection_system_of_structure : LateralTheory.DivDb.Proj := by
  apply LateralTheory.DivDb.Proj_of
theorem etale_tangent_lie_algebra_of_structure : LateralTheory.DivDb.TanLie := by
  apply LateralTheory.DivDb.TanLie_of <;> first | exact etale_tangent_field_extension_of_key
theorem etale_cyclic_grading_of_structure : LateralTheory.DivDb.Grade := by
  apply LateralTheory.DivDb.Grade_of
theorem etale_cycle_spectrum_of_structure : LateralTheory.DivDb.CycleCountPf.CycSpec := by
  apply LateralTheory.DivDb.CycSpec_qzkPf.CycSpec_of
theorem etale_fixed_cycle_scalar_of_structure : LateralTheory.DivDb.CycleCountPf.FixScal := by
  apply LateralTheory.DivDb.ScalarFixedPointsUnderAeval.FixScal_of
theorem etale_cycle_count_eigenvalues_of_key : LateralTheory.DivDb.CycleCount := by
  apply LateralTheory.DivDb.CycleCountPf.CycleCount_of <;> first | exact etale_cycle_spectrum_of_structure | exact etale_fixed_cycle_scalar_of_structure
theorem etale_diagonal_scalar_of_structure : LateralTheory.DivDb.DiagScalar := by
  apply LateralTheory.DivDb.DiagScalar_of <;> first | exact etale_cycle_count_eigenvalues_of_key
theorem etale_algebra_decomposition_of_structure : LateralTheory.DivDb.AlgStruct := by
  apply LateralTheory.DivDb.AlgStruct₂.AlgStruct_of
theorem etale_envelope_stabilizer_of_structure : LateralTheory.DivDb.EnvStab := by
  apply LateralTheory.DivDb.EnvStab_of <;> first | exact etale_divisibility_chain_of_key
theorem etale_semisimplicity_instance : LateralTheory.DivDb.Semis := by
  apply LateralTheory.DivDb.SemisPf.Semis_of
theorem etale_algebra_structure_theorem_of_components : LateralTheory.DivDb.Struct := by
  apply LateralTheory.DivDb.StructPf.Struct_of <;> first | exact etale_tangent_degree_bound_of_key | exact etale_projection_system_of_structure | exact etale_tangent_lie_algebra_of_structure | exact etale_cyclic_grading_of_structure | exact etale_diagonal_scalar_of_structure | exact etale_algebra_decomposition_of_structure | exact etale_envelope_stabilizer_of_structure | exact etale_semisimplicity_instance
theorem intersectionNumber_baseChange : LateralTheory.DivDb.Struct := etale_algebra_structure_theorem_of_components
end LateralTheory.Fin.Struct
