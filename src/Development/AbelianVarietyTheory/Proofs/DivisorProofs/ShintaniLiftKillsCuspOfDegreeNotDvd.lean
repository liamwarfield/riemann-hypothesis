module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVirtualCharacterShintaniPsiLiftStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedVirtualCharacterNormOneSupportStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHopfIdealKerIdealOfBialgHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiSumEqCharSumAgainstCuspForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftCuspidalVanishing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFunctionCharpolyPairProdRootSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GreenFunctionCharacterSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonResolutionPotentialComparison
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem torusPair_pow_eq_one_iff {F : Type} [Field F] [Finite F] (n : ℕ) (α : AlgebraicClosure F) (h0 : α ≠ 0) :
    α ^ (Nat.card F ^ n - 1) = 1 ↔ (minpoly F α).natDegree ∣ n := by
  have hi : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  rw [(minpoly.irreducible hi).natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X, minpoly.dvd_iff]
  have hq : 0 < Nat.card F ^ n := pow_pos Nat.card_pos _
  simp only [map_sub, map_pow, aeval_X, sub_eq_zero]
  obtain ⟨k, hk⟩ : ∃ k, Nat.card F ^ n = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hq).symm⟩
  rw [hk, Nat.add_sub_cancel, pow_succ]
  constructor
  · intro h; rw [h, one_mul]
  · intro h; exact mul_right_cancel₀ h0 (h.trans (one_mul α).symm)

theorem torusPair_finite_monic {F : Type} [Field F] [Finite F] (n : ℕ) :
    {P : F[X] | P.Monic ∧ P.natDegree = n ∧ P.coeff 0 ≠ 0}.Finite := by
  have : Finite (Polynomial.degreeLT F (n + 1)) := Finite.of_equiv _ (degreeLTEquiv F (n + 1)).symm.toEquiv
  have h : (Polynomial.degreeLT F (n + 1) : Set F[X]).Finite := Set.toFinite _
  refine h.subset fun P hP => ?_
  simp only [SetLike.mem_coe, mem_degreeLT]
  exact (degree_le_of_natDegree_le hP.2.1.le).trans_lt (by exact_mod_cast Nat.lt_succ_self n)

theorem torusPair_finite_torus {F : Type} [Field F] [Finite F] (n : ℕ) (hn : 0 < n) :
    {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}.Finite := by
  have hq : 1 < Nat.card F ^ n := Nat.one_lt_pow hn.ne' Finite.one_lt_card
  refine (Polynomial.nthRootsFinset (Nat.card F ^ n - 1) (1 : AlgebraicClosure F)).finite_toSet.subset
    fun α hα => ?_
  exact Finset.mem_coe.2 ((Polynomial.mem_nthRootsFinset (by omega) _).2 hα)

theorem torusPair_mangoldt_pow {F : Type} [Field F] (s : F[X] → ℂ) (f : F[X]) (hf : f.Monic)
    (hirr : Irreducible f) (r : ℕ) (hr : 0 < r) : mangoldt s (f ^ r) = s f := by
  have hset : {g : F[X] | g.Monic ∧ Irreducible g ∧ ∃ r' : ℕ, 0 < r' ∧ f ^ r = g ^ r'} = {f} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hg, hgi, r', hr', he⟩
      have h1 : g ∣ f ^ r := he ▸ dvd_pow_self g hr'.ne'
      have h2 : g ∣ f := hgi.prime.dvd_of_dvd_pow h1
      exact eq_of_monic_of_associated hg hf (hgi.associated_of_dvd hirr h2)
    · rintro rfl
      exact ⟨hf, hirr, r, hr, rfl⟩
  rw [mangoldt, hset, finsum_mem_singleton]

theorem torusPair_mangoldt_sum (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (n k : ℕ)
    (S : F[X] → ℂ) (hn : 0 < n) :
    ∑ᶠ P ∈ {P : F[X] | P.Monic ∧ P.natDegree = n ∧ P.coeff 0 ≠ 0}, mangoldt (rootSum θ k) P * star (S P) =
      ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1},
        θ α ^ k * star (S (minpoly F α ^ (n / (minpoly F α).natDegree))) := by
  have hq : 1 < Nat.card F ^ n := Nat.one_lt_pow hn.ne' Finite.one_lt_card
  have hi : ∀ α : AlgebraicClosure F, IsIntegral F α := fun α => Algebra.IsIntegral.isIntegral α
  have hne : ∀ α : AlgebraicClosure F, α ^ (Nat.card F ^ n - 1) = 1 → α ≠ 0 := by
    rintro α h rfl
    rw [zero_pow (by omega)] at h
    exact zero_ne_one h
  rw [finsum_mem_eq_finite_toFinset_sum _ (torusPair_finite_monic n),
    finsum_mem_eq_finite_toFinset_sum _ (torusPair_finite_torus n hn),
    ← Finset.sum_fiberwise_of_maps_to (s := (torusPair_finite_torus (F := F) n hn).toFinset)
      (t := (torusPair_finite_monic (F := F) n).toFinset)
      (g := fun α => minpoly F α ^ (n / (minpoly F α).natDegree))]
  swap
  · intro α hα
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hα ⊢
    have hm := minpoly.monic (hi α)
    refine ⟨hm.pow _, ?_, ?_⟩
    · rw [hm.natDegree_pow, Nat.div_mul_cancel ((torusPair_pow_eq_one_iff n α (hne α hα)).1 hα)]
    · rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero]
      exact pow_ne_zero _ (minpoly.coeff_zero_ne_zero (hi α) (hne α hα))
  refine Finset.sum_congr rfl fun P hP => ?_
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hP
  obtain ⟨hP, hd, h0⟩ := hP
  by_cases hex : ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ P = f ^ m
  swap
  · have hempty : {f : F[X] | f.Monic ∧ Irreducible f ∧ ∃ m : ℕ, 0 < m ∧ P = f ^ m} = ∅ := by
      ext f
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hf, hirr, m, hm, rfl⟩
      exact hex ⟨f, m, hf, hirr, hm, rfl⟩
    rw [mangoldt, hempty, finsum_mem_empty, zero_mul]
    refine (Finset.sum_eq_zero fun α hα => ?_).symm
    exfalso
    obtain ⟨hα1, hα2⟩ := Finset.mem_filter.1 hα
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hα1
    have hdv := (torusPair_pow_eq_one_iff n α (hne α hα1)).1 hα1
    exact hex ⟨minpoly F α, n / (minpoly F α).natDegree, minpoly.monic (hi α), minpoly.irreducible (hi α),
      Nat.div_pos (Nat.le_of_dvd hn hdv) (minpoly.natDegree_pos (hi α)), hα2.symm⟩
  obtain ⟨f, m, hf, hirr, hm, rfl⟩ := hex
  rw [hf.natDegree_pow] at hd
  have hdiv : n / f.natDegree = m := by
    rw [← hd, Nat.mul_div_cancel _ hirr.natDegree_pos]
  have hmp : ∀ α : AlgebraicClosure F, aeval α f = 0 → minpoly F α = f := fun α h =>
    (minpoly.eq_of_irreducible_of_monic hirr h hf).symm
  have hfib : Finset.filter (fun α : AlgebraicClosure F => minpoly F α ^ (n / (minpoly F α).natDegree) = f ^ m)
      (torusPair_finite_torus (F := F) n hn).toFinset = (f.map (algebraMap F (AlgebraicClosure F))).roots.toFinset := by
    ext α
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Multiset.mem_toFinset]
    rw [mem_roots (hf.map _).ne_zero, IsRoot.def, eval_map_algebraMap]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : n / (minpoly F α).natDegree ≠ 0 :=
        (Nat.div_pos (Nat.le_of_dvd hn ((torusPair_pow_eq_one_iff n α (hne α h1)).1 h1))
          (minpoly.natDegree_pos (hi α))).ne'
      have h4 := congrArg (aeval α) h2
      rw [map_pow, map_pow, minpoly.aeval, zero_pow h3] at h4
      exact pow_eq_zero_iff hm.ne' |>.1 h4.symm
    · intro h
      have hα : α ≠ 0 := by
        rintro rfl
        apply h0
        rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero]
        rw [aeval_def, eval₂_at_zero, map_eq_zero] at h
        rw [h, zero_pow hm.ne']
      rw [torusPair_pow_eq_one_iff n α hα, hmp α h, hdiv]
      exact ⟨Dvd.intro_left _ hd, rfl⟩
  have hsep : f.Separable := PerfectField.separable_of_irreducible hirr
  have hnd : (f.map (algebraMap F (AlgebraicClosure F))).roots.Nodup := nodup_roots hsep.map
  rw [hfib, torusPair_mangoldt_pow _ f hf hirr m hm, rootSum,
    ← Multiset.dedup_eq_self.2 hnd, ← Multiset.toFinset_val, ← Finset.sum_eq_multiset_sum,
    Finset.val_toFinset, Finset.sum_mul]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [Multiset.mem_toFinset, mem_roots (hf.map _).ne_zero, IsRoot.def, eval_map_algebraMap] at hα
  rw [hmp α hα, hdiv]

theorem torusPair_finsum_GL_eq_ipGL (F : Type) [Field F] [Finite F] (m : ℕ) (s S : F[X] → ℂ) :
    ∑ᶠ x : GL (Fin m) F, psiG s m x * star (chG S m x) =
      ipGL (psi s (Fin m → F)) (fun g => S (LinearMap.charpoly g)) := by
  have h : ∀ x : GL (Fin m) F, psiG s m x * star (chG S m x) =
      (fun g => psi s (Fin m → F) g * star (S (LinearMap.charpoly g)))
        (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F)) := by
    intro x; simp [psiG, chG, Matrix.charpoly_toLin']
  rw [finsum_congr h, ipGL, ← finsum_mem_univ]
  apply finsum_mem_eq_of_bijOn (fun x : GL (Fin m) F => Matrix.toLin' (x : Matrix (Fin m) (Fin m) F))
  · refine ⟨fun x _ => ?_, fun x _ y _ hxy => ?_, fun g hg => ?_⟩
    · have := x.isUnit.map (Matrix.toLinAlgEquiv' (R := F) (n := Fin m))
      simpa using this
    · exact Units.ext (Matrix.toLin'.injective hxy)
    · have hu : IsUnit (LinearMap.toMatrix' g) := by
        have := (show IsUnit g from hg).map (LinearMap.toMatrixAlgEquiv' (R := F) (n := Fin m))
        simpa using this
      exact ⟨hu.unit, Set.mem_univ _, by simp⟩
  · intro x _; rfl

theorem psiG_rootSum_pair_chG_eq_sum_torus : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (m k : ℕ) (S : F[X] → ℂ), 0 < m → ((Nat.card F : ℂ) ^ m - 1) * ∑ᶠ x, psiG (rootSum θ k) m x * star (chG S m x) =
      (Nat.card (GL (Fin m) F) : ℂ) * ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ m - 1) = 1},
        θ α ^ k * star (S (minpoly F α ^ (m / (minpoly F α).natDegree))) := by
  intro F _ _ θ m k S hm
  have hadd := (rootSum_isAdditive_and_pow_X_sub_one F θ k).1
  have hq1 : 1 < Nat.card F ^ m := Nat.one_lt_pow hm.ne' Finite.one_lt_card
  have hq : (Nat.card F : ℂ) ^ m - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast hq1.ne'
  rw [torusPair_finsum_GL_eq_ipGL, ipGL_charpoly_eq_finsum_mass, Module.finrank_fin_fun,
    ← torusPair_mangoldt_sum F θ m k S hm]
  have hterm : ∀ P ∈ {P : F[X] | P.Monic ∧ P.natDegree = m ∧ P.coeff 0 ≠ 0},
      mass (psi (rootSum θ k) (Fin m → F)) P * star (S P) =
        (Nat.card (GL (Fin m) F) : ℂ) * (mangoldt (rootSum θ k) P * star (S P)) / ((Nat.card F : ℂ) ^ m - 1) := by
    intro P hP
    obtain ⟨hPm, hPd, -⟩ := hP
    rw [mass_psi_eq_glCard_mul_mangoldt_div F (Fin m → F) (rootSum θ k) hadd P hPm (by simpa using hPd), hPd,
      glCard]
    ring
  rw [finsum_mem_congr rfl hterm, finsum_mem_eq_finite_toFinset_sum _ (torusPair_finite_monic m),
    finsum_mem_eq_finite_toFinset_sum _ (torusPair_finite_monic m), ← Finset.sum_div, ← Finset.mul_sum,
    mul_div_cancel₀ _ hq]

end GlobalTheory.Shin
end

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.green_function_character_sum : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (m k : ℕ) (S : F[X] → ℂ), 0 < m → ((Nat.card F : ℂ) ^ m - 1) * ∑ᶠ x, psiG (rootSum θ k) m x * star (chG S m x) = (Nat.card (GL (Fin m) F) : ℂ) * ∑ᶠ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ m - 1) = 1}, θ α ^ k * star (S (minpoly F α ^ (m / (minpoly F α).natDegree))) := by
  first | (exact @GlobalTheory.Shin.psiG_rootSum_pair_chG_eq_sum_torus) | (exact GlobalTheory.Shin.psiG_rootSum_pair_chG_eq_sum_torus) | (intros; apply GlobalTheory.Shin.psiG_rootSum_pair_chG_eq_sum_torus  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSumMinpolyPowEqSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSumMinpolyPowEqSum
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem rootSum_minpoly_pow_eq_sum : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (m l : ℕ)
    (α : AlgebraicClosure F), 0 < m → α ^ (Nat.card F ^ m - 1) = 1 →
    rootSum θ l (minpoly F α ^ (m / (minpoly F α).natDegree)) =
      ∑ a ∈ Finset.range m, θ α ^ (l * Nat.card F ^ a) := by
  intro F _ _ θ m l α hm hα
  rw [((GlobalTheory.CuspGL.torus_minpoly F θ m hm α hα).2.2 l)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_pow, ← pow_mul, mul_comm]

end GlobalTheory.Shin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSumMinpolyPowEqSumStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootSum_minpoly_pow_eq_sum_range : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (m l : ℕ) (α : AlgebraicClosure F), 0 < m → α ^ (Nat.card F ^ m - 1) = 1 → rootSum θ l (minpoly F α ^ (m / (minpoly F α).natDegree)) = ∑ a ∈ Finset.range m, θ α ^ (l * Nat.card F ^ a) := by
  first | (exact @GlobalTheory.Shin.rootSum_minpoly_pow_eq_sum) | (exact GlobalTheory.Shin.rootSum_minpoly_pow_eq_sum) | (intros; apply GlobalTheory.Shin.rootSum_minpoly_pow_eq_sum  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFunctionCharpolyPairProdRootSum
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem psiG_rootSum_pair_prod_rootSum : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ (m k l : ℕ) (e : Fin l → ℕ), 0 < m → ∑ᶠ x, psiG (rootSum θ k) m x * star (chG (fun P => ∏ j, rootSum θ (e j) P) m x) = (Nat.card (GL (Fin m) F) : ℂ) * ((Finset.univ.filter fun a : Fin l → Fin m => k ≡ ∑ j, e j * Nat.card F ^ (a j : ℕ) [MOD Nat.card F ^ m - 1]).card : ℂ) := by
  intro F _ _ θ hθ m k l e hm
  set q := Nat.card F with hq
  have hq1 : 1 < q := Finite.one_lt_card
  have hqm : 1 < q ^ m := Nat.one_lt_pow hm.ne' hq1
  set N := q ^ m - 1 with hN
  have hN0 : 0 < N := by omega
  have hcast : ((q : ℂ) ^ m - 1) = ((N : ℕ) : ℂ) := by
    rw [hN, Nat.cast_sub hqm.le]; push_cast; ring
  have hNne : ((N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
  have htor := GlobalTheory.T.green_function_character_sum F θ m k (fun P => ∏ j, rootSum θ (e j) P) hm
  have horth := (GlobalTheory.CuspGL.torus_orthogonality F θ hθ m hm).2
  set T := {α : AlgebraicClosure F | α ^ N = 1} with hT
  have hTfin : T.Finite := by
    apply (Polynomial.nthRoots N (1 : AlgebraicClosure F)).toFinset.finite_toSet.subset
    intro α hα
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    exact (Polynomial.mem_nthRoots hN0).2 hα
  have key : ∀ α ∈ T, θ α ^ k * star (∏ j, rootSum θ (e j) (minpoly F α ^ (m / (minpoly F α).natDegree)))
      = ∑ a : Fin l → Fin m, θ α ^ k * star (θ α ^ (∑ j, e j * q ^ (a j : ℕ))) := by
    intro α hα
    have hr : ∀ j, rootSum θ (e j) (minpoly F α ^ (m / (minpoly F α).natDegree)) = ∑ a : Fin m, θ α ^ (e j * q ^ (a : ℕ)) :=
      fun j => (GlobalTheory.T.rootSum_minpoly_pow_eq_sum_range F θ m (e j) α hm hα).trans (Finset.sum_range (fun a => θ α ^ (e j * q ^ a)))
    simp_rw [hr]
    rw [← Finset.mul_sum, ← star_sum, Finset.prod_univ_sum]
    simp only [Fintype.piFinset_univ, Finset.prod_pow_eq_pow_sum]
  have hsum : ∑ᶠ α ∈ T, θ α ^ k * star (∏ j, rootSum θ (e j) (minpoly F α ^ (m / (minpoly F α).natDegree)))
      = ∑ a : Fin l → Fin m, ∑ᶠ α ∈ T, θ α ^ k * star (θ α ^ (∑ j, e j * q ^ (a j : ℕ))) := by
    rw [finsum_mem_congr rfl key, finsum_mem_eq_finite_toFinset_sum _ hTfin, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [finsum_mem_eq_finite_toFinset_sum _ hTfin]
  rw [hsum] at htor
  simp_rw [horth] at htor
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, hcast] at htor
  apply mul_left_cancel₀ hNne
  rw [htor]
  ring

end GlobalTheory.Shin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveFunctionCharpolyPairProdRootSumStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveFunctionCharpoly_pair_prod_rootSum : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ (m k l : ℕ) (e : Fin l → ℕ), 0 < m → ∑ᶠ x, psiG (rootSum θ k) m x * star (chG (fun P => ∏ j, rootSum θ (e j) P) m x) = (Nat.card (GL (Fin m) F) : ℂ) * ((Finset.univ.filter fun a : Fin l → Fin m => k ≡ ∑ j, e j * Nat.card F ^ (a j : ℕ) [MOD Nat.card F ^ m - 1]).card : ℂ) := by
  first | (exact @GlobalTheory.Shin.psiG_rootSum_pair_prod_rootSum) | (exact GlobalTheory.Shin.psiG_rootSum_pair_prod_rootSum) | (intros; apply GlobalTheory.Shin.psiG_rootSum_pair_prod_rootSum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLFiniteFieldEqOfModEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLFiniteFieldEqOfModEq
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem pow_card_pow_sub_one_of_root (F : Type) [Field F] [Finite F] (f : F[X]) (hf : f.Monic)
    (hi : Irreducible f) (m : ℕ) (hd : f.natDegree ∣ m) (α : AlgebraicClosure F)
    (hα : α ∈ (f.map (algebraMap F (AlgebraicClosure F))).roots) (h0 : α ≠ 0) :
    α ^ (Nat.card F ^ m - 1) = 1 := by
  have hf0 : f.map (algebraMap F (AlgebraicClosure F)) ≠ 0 := Polynomial.map_ne_zero hi.ne_zero
  have hr : aeval α f = 0 := by
    have := (mem_roots hf0).1 hα
    rwa [IsRoot, eval_map_algebraMap] at this
  have hmin : f = minpoly F α := minpoly.eq_of_irreducible_of_monic hi hr hf
  have hx : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  have hfix : α ^ Nat.card F ^ m = α := by
    have h1 := ((minpoly.irreducible hx).natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X (n := m)).1
      (by rw [← hmin]; exact hd)
    rw [minpoly.dvd_iff] at h1
    simpa [sub_eq_zero] using h1
  have hpos : 1 ≤ Nat.card F ^ m := Nat.one_le_pow _ _ Nat.card_pos
  have : α ^ (Nat.card F ^ m - 1) * α = 1 * α := by
    rw [← pow_succ, Nat.sub_add_cancel hpos, hfix, one_mul]
  exact mul_right_cancel₀ h0 this

theorem pow_eq_pow_of_modEq' {M : Type} [Monoid M] (α : M) (N a b : ℕ) (h : α ^ N = 1)
    (hab : a ≡ b [MOD N]) : α ^ a = α ^ b := by
  rw [← Nat.div_add_mod a N, ← Nat.div_add_mod b N, pow_add, pow_add, pow_mul, pow_mul, h, one_pow,
    one_pow, hab]

end GlobalTheory.Shin

namespace GlobalTheory.Shin

theorem rootSum_eq_of_modEq (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (f : F[X])
    (hf : f.Monic) (hi : Irreducible f) (hc : f.coeff 0 ≠ 0) (m k k' a : ℕ) (hd : f.natDegree ∣ m)
    (hk : k' ≡ k * Nat.card F ^ a [MOD Nat.card F ^ m - 1]) :
    rootSum θ k' f = rootSum θ k f := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F (ringChar F)
  have hq : ringChar F ^ ((n : ℕ) * a) = Nat.card F ^ a := by
    rw [Nat.card_eq_fintype_card, hn, pow_mul]
  have hgal := GlobalTheory.T.rootSum_map_frobenius_pow_eq_rootSum_mul F θ (RingHom.id F) ((n : ℕ) * a) (fun x => by
    rw [hq, Nat.card_eq_fintype_card, FiniteField.pow_card_pow]; rfl) k f
  rw [Polynomial.map_id, hq] at hgal
  rw [hgal]
  unfold rootSum
  congr 1
  refine Multiset.map_congr rfl fun α hα => ?_
  have hf0 : f.map (algebraMap F (AlgebraicClosure F)) ≠ 0 := Polynomial.map_ne_zero hi.ne_zero
  have h0 : α ≠ 0 := by
    rintro rfl
    have h := (mem_roots hf0).1 hα
    rw [IsRoot, ← coeff_zero_eq_eval_zero, coeff_map] at h
    exact hc ((algebraMap F (AlgebraicClosure F)).injective (by rw [h, map_zero]))
  rw [← map_pow, ← map_pow,
    pow_eq_pow_of_modEq' α _ _ _ (pow_card_pow_sub_one_of_root F f hf hi m hd α hα h0) hk]

end GlobalTheory.Shin

namespace GlobalTheory.Shin

theorem cusp_eq_of_modEq : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ),
    (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) →
    ∀ m k k' a : ℕ, 0 < m → k' ≡ k * Nat.card F ^ a [MOD Nat.card F ^ m - 1] →
      cusp θ m k' = cusp θ m k := by
  intro F _ _ θ _ m k k' a _ hk
  funext x
  unfold cusp psiG
  congr 1
  set V := Fin m → F
  set g : Module.End F V := Matrix.toLin' (x : Matrix (Fin m) (Fin m) F)
  have hV : Finite V := Module.finite_of_finite F
  have hE : Finite (Module.End F V) := Finite.of_injective _ DFunLike.coe_injective
  have hs := (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F θ k).1
  have hs' := (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F θ k').1
  let φ : Module.End F V → ℂ := fun h => psi (rootSum θ k') V h - psi (rootSum θ k) V h
  have hc : IsClassFn φ := by
    intro e h
    simp only [φ, GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj]
  have hp : GlobalTheory.CuspGL.IsPrimitive φ := by
    intro A hA hA' g' hg'
    have e1 := GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse F V _ hs' A hA hA' g' hg'
    have e2 := GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse F V _ hs A hA hA' g' hg'
    have := finsum_mem_lin_comb_of_finite (nilRad A) 1 1 (fun h => psi (rootSum θ k') V (g' + h))
      (fun h => psi (rootSum θ k) V (g' + h))
    simp only [one_mul] at this
    simp only [φ]
    rw [this, e1, e2, sub_zero]
  have hP : (LinearMap.charpoly g).Monic := LinearMap.charpoly_monic g
  have hdeg : (LinearMap.charpoly g).natDegree = Module.finrank F V := LinearMap.charpoly_natDegree g
  have hdegm : (LinearMap.charpoly g).natDegree = m := by rw [hdeg, Module.finrank_fin_fun]
  have hc0 : (LinearMap.charpoly g).coeff 0 ≠ 0 := by
    intro h0
    have hdet := LinearMap.det_eq_sign_charpoly_coeff g
    rw [h0, mul_zero, LinearMap.det_toLin'] at hdet
    exact ((Matrix.isUnit_iff_isUnit_det _).1 x.isUnit).ne_zero hdet
  have hmang : mangoldt (rootSum θ k') (LinearMap.charpoly g) =
      mangoldt (rootSum θ k) (LinearMap.charpoly g) := by
    unfold mangoldt
    refine finsum_mem_congr rfl fun f hf => ?_
    obtain ⟨hfm, hfi, r, hr, hfr⟩ := hf
    refine rootSum_eq_of_modEq F θ f hfm hfi ?_ m k k' a ?_ hk
    · intro h
      apply hc0
      rw [hfr, coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero, h, zero_pow hr.ne']
    · refine ⟨r, ?_⟩
      rw [← hdegm, hfr, natDegree_pow, mul_comm]
  have hmass : mass φ (LinearMap.charpoly g) = 0 := by
    have := finsum_mem_lin_comb_of_finite {h : Module.End F V | LinearMap.charpoly h = LinearMap.charpoly g}
      1 1 (psi (rootSum θ k') V) (psi (rootSum θ k) V)
    simp only [one_mul] at this
    unfold mass
    simp only [φ]
    rw [this]
    have m1 := GlobalTheory.T.endomorphismMass_mobiusInverse_monic_eq F V _ hs' _ hP hdeg
    have m2 := GlobalTheory.T.endomorphismMass_mobiusInverse_monic_eq F V _ hs _ hP hdeg
    unfold mass at m1 m2
    rw [m1, m2, hmang, sub_self]
  exact sub_eq_zero.1 (GlobalTheory.T.primitiveEndClassFunction_zero_of_charpoly_mass_zero F V φ hc hp g hmass)

end GlobalTheory.Shin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLFiniteFieldEqOfModEqStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidalCharacterGLFiniteField_eq_of_modEq : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ m k k' a : ℕ, 0 < m → k' ≡ k * Nat.card F ^ a [MOD Nat.card F ^ m - 1] → cusp θ m k' = cusp θ m k := by
  first | (exact @GlobalTheory.Shin.cusp_eq_of_modEq) | (exact GlobalTheory.Shin.cusp_eq_of_modEq) | (intros; apply GlobalTheory.Shin.cusp_eq_of_modEq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardExponentTuplesModEqOneOfPrimeNotDvd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardExponentTuplesModEqOneOfPrimeNotDvd
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.ExpCount

theorem eq_zero_of_modEq (q l m k c : ℕ) (hq : 2 ≤ q) (hl : l.Prime) (hm : 0 < m) (hlm : ¬ l ∣ m)
    (hreg : Reg q m k) (hc : c < l * m) (hlc : l ∣ c)
    (h : k * (∑ i ∈ Finset.range l, q ^ (m * i)) * q ^ c ≡ k * ∑ i ∈ Finset.range l, q ^ (m * i)
      [MOD q ^ (l * m) - 1]) : c = 0 := by
  set S : ℕ := ∑ i ∈ Finset.range l, q ^ (m * i) with hS
  have hSpos : 0 < S := Finset.sum_pos (fun i _ => by positivity) ⟨0, Finset.mem_range.2 hl.pos⟩
  have hgeom : ((q ^ (l * m) - 1 : ℕ) : ℤ) = ((q : ℤ) ^ m - 1) * (S : ℤ) := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), hS]
    push_cast
    have e : ∑ i ∈ Finset.range l, (q : ℤ) ^ (m * i) = ∑ i ∈ Finset.range l, ((q : ℤ) ^ m) ^ i :=
      Finset.sum_congr rfl fun i _ => by rw [pow_mul]
    rw [e, mul_comm ((q : ℤ) ^ m - 1), geom_sum_mul, ← pow_mul, mul_comm m l]
  have h1 := Nat.modEq_iff_dvd.1 h
  rw [hgeom] at h1
  push_cast at h1
  have h2 : ((q : ℤ) ^ m - 1) ∣ (k : ℤ) - k * (q : ℤ) ^ c := by
    have h1' : ((q : ℤ) ^ m - 1) * S ∣ ((k : ℤ) - k * (q : ℤ) ^ c) * S := by
      convert h1 using 1; ring
    exact (mul_dvd_mul_iff_right (by exact_mod_cast hSpos.ne')).1 h1'
  have h3 : ((q : ℤ) ^ m - 1) ∣ (k : ℤ) - k * (q : ℤ) ^ (c % m) := by
    have hc' : (q : ℤ) ^ c = ((q : ℤ) ^ m) ^ (c / m) * (q : ℤ) ^ (c % m) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    have e : (k : ℤ) - k * (q : ℤ) ^ (c % m) = ((k : ℤ) - k * (q : ℤ) ^ c)
        + k * (q : ℤ) ^ (c % m) * (((q : ℤ) ^ m) ^ (c / m) - 1 ^ (c / m)) := by
      rw [hc']; ring
    rw [e]
    exact dvd_add h2 (Dvd.dvd.mul_left (sub_dvd_pow_sub_pow _ _ _) _)
  have hmc : m ∣ c := by
    by_contra hne
    have hd : 0 < c % m := Nat.pos_of_ne_zero (fun h0 => hne (Nat.dvd_of_mod_eq_zero h0))
    apply hreg (c % m) hd (Nat.mod_lt c hm)
    apply Nat.modEq_iff_dvd.2
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
    push_cast
    exact h3
  have hcop : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd hl).2 hlm
  exact Nat.eq_zero_of_dvd_of_lt (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hlc hmc) hc

theorem pow_val_add_natCast {M N : ℕ} [NeZero N] (Q : ZMod M) (hQ : Q ^ N = 1) (x : ZMod N) (n : ℕ) :
    Q ^ (x + (n : ZMod N)).val = Q ^ x.val * Q ^ n := by
  rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (x.val + n) N, pow_add, pow_mul, hQ, one_pow, mul_one]

theorem fixed_eq (l' m : ℕ) (hl : (l' + 1).Prime) (hlm : ¬ (l' + 1) ∣ m)
    (h : ZMod (l' + 1) → ZMod ((l' + 1) * m)) (hfix : ∀ r, h (r - m) + m = h r) (r : ZMod (l' + 1)) :
    h r = h 0 + (((r * (m : ZMod (l' + 1))⁻¹).val * m : ℕ) : ZMod ((l' + 1) * m)) := by
  haveI : Fact (l' + 1).Prime := ⟨hl⟩
  have hm0 : (m : ZMod (l' + 1)) ≠ 0 := fun h0 => hlm ((ZMod.natCast_eq_zero_iff _ _).1 h0)
  have hind : ∀ n : ℕ, h ((n : ZMod (l' + 1)) * m) = h 0 + ((n * m : ℕ) : ZMod ((l' + 1) * m)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hf := hfix (((n + 1 : ℕ) : ZMod (l' + 1)) * m)
      rw [← hf]
      have e : ((n + 1 : ℕ) : ZMod (l' + 1)) * m - m = (n : ZMod (l' + 1)) * m := by push_cast; ring
      rw [e, ih]; push_cast; ring
  have hr : r = (((r * (m : ZMod (l' + 1))⁻¹).val : ℕ) : ZMod (l' + 1)) * m := by
    rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hm0, mul_one]
  conv_lhs => rw [hr]
  exact hind _

theorem fixed_sum (M l' m : ℕ) (Q : ZMod M) (hl : (l' + 1).Prime) (hlm : ¬ (l' + 1) ∣ m) (hm : 0 < m)
    (hQ : Q ^ ((l' + 1) * m) = 1)
    (h : ZMod (l' + 1) → ZMod ((l' + 1) * m)) (hfix : ∀ r, h (r - m) + m = h r) :
    ∑ r, Q ^ (h r).val = Q ^ (h 0).val * ∑ i ∈ Finset.range (l' + 1), Q ^ (m * i) := by
  haveI : Fact (l' + 1).Prime := ⟨hl⟩
  haveI : NeZero ((l' + 1) * m) := ⟨by positivity⟩
  have hm0 : (m : ZMod (l' + 1)) ≠ 0 := fun h0 => hlm ((ZMod.natCast_eq_zero_iff _ _).1 h0)
  rw [Finset.sum_congr rfl (fun r _ => by rw [fixed_eq l' m hl hlm h hfix r, pow_val_add_natCast Q hQ]),
    ← Finset.mul_sum]
  congr 1
  have e1 : ∑ r : ZMod (l' + 1), Q ^ ((r * (m : ZMod (l' + 1))⁻¹).val * m)
      = ∑ s : ZMod (l' + 1), Q ^ (s.val * m) :=
    Equiv.sum_comp (Equiv.mulRight₀ ((m : ZMod (l' + 1))⁻¹) (inv_ne_zero hm0)) (fun s : ZMod (l' + 1) => Q ^ (s.val * m))
  rw [e1, ← Fin.sum_univ_eq_sum_range (fun i => Q ^ (m * i)) (l' + 1)]
  exact Finset.sum_congr rfl fun s _ => by rw [mul_comm]; rfl

end GlobalTheory.ExpCount

namespace GlobalTheory.ExpCount

theorem card_eq (q l' m k : ℕ) (hm : 0 < m) :
    (Finset.univ.filter fun a : Fin (l' + 1) → Fin m => k * ∑ i ∈ Finset.range (l' + 1), q ^ (m * i) ≡
      ∑ j : Fin (l' + 1), k * q ^ (j : ℕ) * (q ^ (l' + 1)) ^ (a j : ℕ) [MOD (q ^ (l' + 1)) ^ m - 1]).card =
    Nat.card {g : ZMod (l' + 1) → ZMod ((l' + 1) * m) //
      (∀ r, ZMod.castHom (dvd_mul_right (l' + 1) m) (ZMod (l' + 1)) (g r) = r) ∧
      ((k * ∑ i ∈ Finset.range (l' + 1), q ^ (m * i) : ℕ) : ZMod (q ^ ((l' + 1) * m) - 1)) =
        ∑ r, (k : ZMod (q ^ ((l' + 1) * m) - 1)) * (q : ZMod (q ^ ((l' + 1) * m) - 1)) ^ (g r).val} := by
  haveI : NeZero ((l' + 1) * m) := ⟨by positivity⟩
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  let ef : Fin (l' + 1) ≃ ZMod (l' + 1) := Equiv.refl _
  have hef : ∀ r : ZMod (l' + 1), ((ef.symm r : Fin (l' + 1)) : ℕ) = r.val := fun r => rfl
  have hef' : ∀ j : Fin (l' + 1), (ef j).val = (j : ℕ) := fun j => rfl
  have hb : ∀ (j : ℕ) (x : ℕ), j < l' + 1 → x < m → j + (l' + 1) * x < (l' + 1) * m := by
    intro j x hj hx
    calc j + (l' + 1) * x < (l' + 1) + (l' + 1) * x := by omega
      _ = (l' + 1) * (x + 1) := by ring
      _ ≤ (l' + 1) * m := Nat.mul_le_mul_left _ hx
  have hkey : ∀ (g : ZMod (l' + 1) → ZMod ((l' + 1) * m)),
      (∀ r, ZMod.castHom (dvd_mul_right (l' + 1) m) (ZMod (l' + 1)) (g r) = r) →
      ∀ r : ZMod (l' + 1), r.val + (l' + 1) * ((g r).val / (l' + 1)) = (g r).val := by
    intro g hg r
    have h := hg r
    rw [ZMod.castHom_apply, ← ZMod.natCast_val] at h
    have h2 := congrArg ZMod.val h
    rw [ZMod.val_natCast] at h2
    rw [← h2, Nat.mod_add_div]
  have hmod : (q ^ (l' + 1)) ^ m - 1 = q ^ ((l' + 1) * m) - 1 := by rw [← pow_mul]
  refine Nat.card_congr
    { toFun := fun a => ⟨fun r => ((r.val + (l' + 1) * (a.1 (ef.symm r)).val : ℕ) : ZMod ((l' + 1) * m)), ?_, ?_⟩
      invFun := fun g => ⟨fun j => ⟨(g.1 (ef j)).val / (l' + 1),
        (Nat.div_lt_iff_lt_mul (Nat.succ_pos l')).2 (lt_of_lt_of_eq (ZMod.val_lt _) (mul_comm _ _))⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro r
    rw [map_natCast, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero, ZMod.natCast_zmod_val]
  · rcases a with ⟨a, ha⟩
    rw [hmod] at ha
    have h := (ZMod.natCast_eq_natCast_iff _ _ _).2 ha
    have hv : ∀ r : ZMod (l' + 1), (((r.val + (l' + 1) * (a (ef.symm r)).val : ℕ) : ZMod ((l' + 1) * m))).val
        = r.val + (l' + 1) * (a (ef.symm r)).val := fun r =>
      ZMod.val_cast_of_lt (hb _ _ (ZMod.val_lt r) (a (ef.symm r)).isLt)
    simp only [hv]
    rw [h]; push_cast
    rw [← Equiv.sum_comp ef.symm (fun j : Fin (l' + 1) => (k : ZMod (q ^ ((l' + 1) * m) - 1)) *
      (q : ZMod (q ^ ((l' + 1) * m) - 1)) ^ (j : ℕ) * ((q : ZMod (q ^ ((l' + 1) * m) - 1)) ^ (l' + 1)) ^ (a j : ℕ))]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [pow_add (q : ZMod (q ^ ((l' + 1) * m) - 1)) r.val, hef, mul_assoc, ← pow_mul]
  · rcases g with ⟨g, hg1, hg2⟩
    apply (ZMod.natCast_eq_natCast_iff _ _ _).1
    show ((k * ∑ i ∈ Finset.range (l' + 1), q ^ (m * i) : ℕ) : ZMod ((q ^ (l' + 1)) ^ m - 1)) =
      ((∑ j : Fin (l' + 1), k * q ^ (j : ℕ) * (q ^ (l' + 1)) ^ ((g (ef j)).val / (l' + 1)) : ℕ) : ZMod ((q ^ (l' + 1)) ^ m - 1))
    rw [hmod, hg2]; push_cast
    rw [← Equiv.sum_comp ef (fun r : ZMod (l' + 1) => (k : ZMod (q ^ ((l' + 1) * m) - 1)) *
      (q : ZMod (q ^ ((l' + 1) * m) - 1)) ^ (g r).val)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← pow_mul, mul_assoc, ← pow_add, ← hef' j, hkey g hg1 (ef j)]
  · intro a
    apply Subtype.ext; funext j; apply Fin.ext
    show ((((ef j).val + (l' + 1) * (a.1 (ef.symm (ef j))).val : ℕ) : ZMod ((l' + 1) * m))).val / (l' + 1)
      = (a.1 j).val
    rw [Equiv.symm_apply_apply, ZMod.val_cast_of_lt (hb _ _ (ZMod.val_lt _) (a.1 j).isLt),
      Nat.add_mul_div_left _ _ (Nat.succ_pos l'), Nat.div_eq_of_lt (ZMod.val_lt _), zero_add]
  · intro g
    apply Subtype.ext; funext r
    show ((r.val + (l' + 1) * ((g.1 (ef (ef.symm r))).val / (l' + 1)) : ℕ) : ZMod ((l' + 1) * m)) = g.1 r
    rw [Equiv.apply_symm_apply, hkey g.1 g.2.1 r, ZMod.natCast_zmod_val]

end GlobalTheory.ExpCount

namespace GlobalTheory.ExpCount

theorem count_one_mod : ∀ q l m k : ℕ, 2 ≤ q → l.Prime → 0 < m → ¬ l ∣ m → Reg q m k →
    (Finset.univ.filter fun a : Fin l → Fin m => k * ∑ i ∈ Finset.range l, q ^ (m * i) ≡
      ∑ j : Fin l, k * q ^ (j : ℕ) * (q ^ l) ^ (a j : ℕ) [MOD (q ^ l) ^ m - 1]).card ≡ 1 [MOD l] := by
  intro q l m k hq hl hm hlm hreg
  obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by have := hl.one_lt; omega⟩
  rw [card_eq q l' m k hm]
  haveI : Fact (l' + 1).Prime := ⟨hl⟩
  haveI : NeZero ((l' + 1) * m) := ⟨by positivity⟩
  have hm0 : (m : ZMod (l' + 1)) ≠ 0 := fun h0 => hlm ((ZMod.natCast_eq_zero_iff _ _).1 h0)
  have hQ : (q : ZMod (q ^ ((l' + 1) * m) - 1)) ^ ((l' + 1) * m) = 1 := by
    have h0 : ((q ^ ((l' + 1) * m) - 1 : ℕ) : ZMod (q ^ ((l' + 1) * m) - 1)) = 0 := ZMod.natCast_self _
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega))] at h0
    push_cast at h0
    exact sub_eq_zero.1 h0
  generalize hMdef : q ^ ((l' + 1) * m) - 1 = M at hQ ⊢
  have hSQ : (q : ZMod M) ^ m * ∑ i ∈ Finset.range (l' + 1), (q : ZMod M) ^ (m * i)
      = ∑ i ∈ Finset.range (l' + 1), (q : ZMod M) ^ (m * i) := by
    have h1 := Finset.sum_range_succ' (fun i => (q : ZMod M) ^ (m * i)) (l' + 1)
    have h2 := Finset.sum_range_succ (fun i => (q : ZMod M) ^ (m * i)) (l' + 1)
    beta_reduce at h1 h2
    have h3 : (q : ZMod M) ^ (m * (l' + 1)) = (q : ZMod M) ^ (m * 0) := by
      rw [mul_comm m, hQ, mul_zero, pow_zero]
    rw [h3] at h2
    rw [Finset.mul_sum]
    have h4 : ∀ i ∈ Finset.range (l' + 1),
        (q : ZMod M) ^ m * (q : ZMod M) ^ (m * i) = (q : ZMod M) ^ (m * (i + 1)) := fun i _ => by
      rw [← pow_add]; congr 1; ring
    rw [Finset.sum_congr rfl h4]
    exact add_right_cancel (h1.symm.trans h2)
  let P : (ZMod (l' + 1) → ZMod ((l' + 1) * m)) → Prop := fun g =>
    (∀ r, ZMod.castHom (dvd_mul_right (l' + 1) m) (ZMod (l' + 1)) (g r) = r) ∧
      ((k * ∑ i ∈ Finset.range (l' + 1), q ^ (m * i) : ℕ) : ZMod M) = ∑ r, (k : ZMod M) * (q : ZMod M) ^ (g r).val
  have hpres : ∀ g, P g → P (fun r => g (r - m) + m) := by
    intro g hg
    refine ⟨fun r => ?_, ?_⟩
    · rw [map_add (f := _), hg.1, map_natCast]; ring
    · have e : ∑ r, (k : ZMod M) * (q : ZMod M) ^ (g (r - m) + m).val
          = ∑ r, (k : ZMod M) * (q : ZMod M) ^ (g r + m).val :=
        Equiv.sum_comp (Equiv.subRight (m : ZMod (l' + 1))) (fun r => (k : ZMod M) * (q : ZMod M) ^ (g r + m).val)
      show _ = ∑ r, (k : ZMod M) * (q : ZMod M) ^ (g (r - m) + m).val
      rw [e]
      calc ((k * ∑ i ∈ Finset.range (l' + 1), q ^ (m * i) : ℕ) : ZMod M)
          = (q : ZMod M) ^ m * ((k * ∑ i ∈ Finset.range (l' + 1), q ^ (m * i) : ℕ) : ZMod M) := by
            push_cast; rw [mul_left_comm, hSQ]
        _ = (q : ZMod M) ^ m * ∑ r, (k : ZMod M) * (q : ZMod M) ^ (g r).val := by rw [hg.2]
        _ = ∑ r, (k : ZMod M) * (q : ZMod M) ^ (g r + m).val := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [pow_val_add_natCast _ hQ]; ring
  let X := {g : ZMod (l' + 1) → ZMod ((l' + 1) * m) // P g}
  let σ : Function.End X := fun g => ⟨fun r => g.1 (r - m) + m, hpres g.1 g.2⟩
  have hpow : ∀ n : ℕ, ∀ g : X, ((σ ^ n) g).1 =
      fun r => g.1 (r - (n : ZMod (l' + 1)) * m) + ((n * m : ℕ) : ZMod ((l' + 1) * m)) := by
    intro n
    induction n with
    | zero => intro g; funext r; rw [pow_zero]; show g.1 r = _; simp
    | succ n ih =>
      intro g; funext r
      rw [pow_succ]
      show ((σ ^ n) (σ g)).1 r = _
      rw [ih]
      show g.1 (r - (n : ZMod (l' + 1)) * m - m) + m + ((n * m : ℕ) : ZMod ((l' + 1) * m)) = _
      rw [add_assoc]
      congr 1
      · congr 1; push_cast; ring_nf
      · push_cast; ring
  have hσ : σ ^ (l' + 1) ^ 1 = 1 := by
    rw [pow_one]
    refine funext fun g => Subtype.ext ?_
    rw [hpow]
    funext r
    show _ = g.1 r
    rw [ZMod.natCast_self, ZMod.natCast_self, zero_mul, sub_zero, add_zero]
  have hcard := Equiv.Perm.card_fixedPoints_modEq (p := l' + 1) (n := 1) hσ
  let gs : ZMod (l' + 1) → ZMod ((l' + 1) * m) :=
    fun r => (((r * (m : ZMod (l' + 1))⁻¹).val * m : ℕ) : ZMod ((l' + 1) * m))
  have hgs_fix : ∀ r, gs (r - m) + m = gs r := by
    intro r
    show ((((r - m) * (m : ZMod (l' + 1))⁻¹).val * m : ℕ) : ZMod ((l' + 1) * m)) + m
      = (((r * (m : ZMod (l' + 1))⁻¹).val * m : ℕ) : ZMod ((l' + 1) * m))
    have e : (r - m) * (m : ZMod (l' + 1))⁻¹ = r * (m : ZMod (l' + 1))⁻¹ - 1 := by
      rw [sub_mul, mul_inv_cancel₀ hm0]
    rw [e]
    have h1 : (r * (m : ZMod (l' + 1))⁻¹ - 1).val + 1 ≡ (r * (m : ZMod (l' + 1))⁻¹).val [MOD l' + 1] := by
      rw [← ZMod.natCast_eq_natCast_iff]; push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]; ring
    have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).2 (Nat.ModEq.mul_right' m h1)
    rw [← h2]; push_cast; ring
  have hgs0 : gs 0 = 0 := by simp [gs]
  have hgsP : P gs := by
    refine ⟨fun r => ?_, ?_⟩
    · show ZMod.castHom _ (ZMod (l' + 1)) (((r * (m : ZMod (l' + 1))⁻¹).val * m : ℕ) : ZMod ((l' + 1) * m)) = r
      rw [map_natCast]; push_cast
      rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hm0, mul_one]
    · show _ = ∑ r, (k : ZMod M) * (q : ZMod M) ^ (gs r).val
      rw [← Finset.mul_sum, fixed_sum M l' m _ hl hlm hm hQ gs hgs_fix, hgs0, ZMod.val_zero, pow_zero, one_mul]
      push_cast; rfl
  have huniq : ∀ g, P g → (∀ r, g (r - m) + m = g r) → g = gs := by
    intro g hg hfix
    have hs := fixed_sum M l' m (q : ZMod M) hl hlm hm hQ g hfix
    have hlc : l' + 1 ∣ (g 0).val := by
      have h := hg.1 0
      rw [ZMod.castHom_apply, ← ZMod.natCast_val] at h
      exact (ZMod.natCast_eq_zero_iff _ _).1 h
    have hmodeq : k * (∑ i ∈ Finset.range (l' + 1), q ^ (m * i)) * q ^ (g 0).val
        ≡ k * ∑ i ∈ Finset.range (l' + 1), q ^ (m * i) [MOD q ^ ((l' + 1) * m) - 1] := by
      rw [hMdef, ← ZMod.natCast_eq_natCast_iff]
      have h2 := hg.2
      rw [← Finset.mul_sum, hs] at h2
      push_cast at h2 ⊢
      linear_combination h2.symm
    have hc := eq_zero_of_modEq q (l' + 1) m k (g 0).val hq hl hm hlm hreg (ZMod.val_lt _) hlc hmodeq
    have h0 : g 0 = 0 := (ZMod.val_eq_zero _).1 hc
    funext r
    rw [fixed_eq l' m hl hlm g hfix r, h0, zero_add]
  have hfp : Fintype.card (Function.fixedPoints σ) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨⟨gs, hgsP⟩, ?_⟩, ?_⟩
    · show σ ⟨gs, hgsP⟩ = ⟨gs, hgsP⟩
      exact Subtype.ext (funext hgs_fix)
    · rintro ⟨⟨g, hg⟩, hfx⟩
      have hfx' : σ ⟨g, hg⟩ = ⟨g, hg⟩ := hfx
      have hfix : ∀ r, g (r - m) + m = g r := fun r => congrFun (congrArg Subtype.val hfx') r
      exact Subtype.ext (Subtype.ext (huniq g hg hfix))
  change Nat.card X ≡ 1 [MOD l' + 1]
  rw [Nat.card_eq_fintype_card]
  exact hcard.trans (by rw [hfp])

end GlobalTheory.ExpCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardExponentTuplesModEqOneOfPrimeNotDvdStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_exponent_tuples_modEq_one_of_prime_not_dvd : ∀ q l m k : ℕ, 2 ≤ q → l.Prime → 0 < m → ¬ l ∣ m → Reg q m k → (Finset.univ.filter fun a : Fin l → Fin m => k * ∑ i ∈ Finset.range l, q ^ (m * i) ≡ ∑ j : Fin l, k * q ^ (j : ℕ) * (q ^ l) ^ (a j : ℕ) [MOD (q ^ l) ^ m - 1]).card ≡ 1 [MOD l] := by
  first | (exact @GlobalTheory.ExpCount.count_one_mod) | (exact GlobalTheory.ExpCount.count_one_mod) | (intros; apply GlobalTheory.ExpCount.count_one_mod  <;> assumption)
end
end

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem shLift_cusp_kills_of_not_dvd : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ n k : ℕ, 0 < n → ¬ Module.finrank F F' ∣ n → Reg (Nat.card F) n k → Kills (shLift s (cusp (pullθ ι θ) n k)) (cusp θ n (k * ∑ i ∈ Finset.range (Module.finrank F F'), Nat.card F ^ (n * i))) := by
  intro F F' _ _ _ _ s hl hs ι θ hθ n k hn hnd hreg
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  haveI := Fintype.ofFinite F
  haveI := Fintype.ofFinite F'
  haveI : Fact (Module.finrank F F').Prime := ⟨hl⟩
  set l := Module.finrank F F' with hl_def
  set q := Nat.card F with hq_def
  have hq2 : 2 ≤ q := Finite.one_lt_card
  have hcard' : Nat.card F' = q ^ l := by
    rw [hq_def, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F)]
  set K := k * ∑ i ∈ Finset.range l, q ^ (n * i) with hK_def
  obtain ⟨hregK, a, ha⟩ := GlobalTheory.T.regular_pair_lift_to_prime_power_field q l n k hq2 hl hn hnd hreg
  have hregK' : Reg (Nat.card F') n K := by rw [hcard']; exact hregK
  obtain ⟨hYchar, -⟩ := GlobalTheory.T.cuspidalCharacterGL_isCharacter_norm_one_of_regular F' θ hθ n K hn hregK'
  have hYs : ∀ g, cusp θ n K (galAct F F' n s g) = cusp θ n K g := by
    intro g
    obtain ⟨⟨i, hi⟩, hi'⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F F').2 s
    simp only at hi'
    obtain ⟨r, hp, hr⟩ := FiniteField.card F (ringChar F)
    have hchar : ringChar F' = ringChar F := (Algebra.ringChar_eq F F').symm
    have hsx : ∀ x, s.toRingEquiv x = x ^ (ringChar F' ^ ((r : ℕ) * i)) := by
      intro x
      change s x = _
      rw [← hi', AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, hr, hchar, pow_mul]
    have h1 := GlobalTheory.T.cuspidalCharacterGLFiniteField_frobenius_pow F' θ s.toRingEquiv ((r : ℕ) * i) hsx n K g
    have hpq : ringChar F' ^ ((r : ℕ) * i) = q ^ i := by
      rw [hchar, pow_mul, ← hr, hq_def, Nat.card_eq_fintype_card]
    rw [hpq] at h1
    have hpow : ∀ j, K * q ^ j ≡ K * Nat.card F' ^ (a * j) [MOD Nat.card F' ^ n - 1] := by
      intro j
      induction j with
      | zero => simp only [pow_zero, mul_zero, mul_one]; exact Nat.ModEq.refl _
      | succ j ih =>
        have e1 : K * q ^ (j + 1) = (K * q ^ j) * q := by ring
        have e2 : K * Nat.card F' ^ (a * (j + 1)) = (K * (q ^ l) ^ a) * Nat.card F' ^ (a * j) := by
          rw [hcard']; ring
        rw [e1, e2]
        calc K * q ^ j * q ≡ K * Nat.card F' ^ (a * j) * q [MOD Nat.card F' ^ n - 1] := ih.mul_right _
          _ = (K * q) * Nat.card F' ^ (a * j) := by ring
          _ ≡ (K * (q ^ l) ^ a) * Nat.card F' ^ (a * j) [MOD Nat.card F' ^ n - 1] := by
            apply Nat.ModEq.mul_right
            rw [hcard']; exact ha
    have h2 := GlobalTheory.T.cuspidalCharacterGLFiniteField_eq_of_modEq F' θ hθ n K (K * q ^ i) (a * i) hn (hpow i)
    rw [galAct_apply]
    exact h1.trans (congrFun h2 g)
  obtain ⟨X0, hX0, hX0a, hX0b⟩ := GlobalTheory.T.exists_virtualCharacter_shintani_psi_lift F F' s hl hs ι θ hθ k n
  set c : ℂ := (-1) ^ (n - 1) with hc_def
  have hc2 : c * c = 1 := by rw [hc_def, ← mul_pow]; simp
  have hcstar : star c = c := by rw [hc_def]; simp
  set X : GHat F F' n → ℂ := fun x => c * X0 x with hX_def
  have hX : X ∈ Virt ℂ ℂ (GHat F F' n) := by
    have e : X = ((-1 : ℤ) ^ (n - 1)) • X0 := by
      funext x
      simp only [hX_def, Pi.smul_apply, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, hc_def]
    rw [e]
    exact AddSubgroup.zsmul_mem _ hX0 _
  have hfun : (fun δ => X (inl δ * inr s)) = shLift s (cusp (pullθ ι θ) n k) := by
    funext δ
    simp only [hX_def, hX0b]
    by_cases h : ∃ γ, IsNorm s δ γ <;> simp [shLift, cusp, h, hc_def]
  have hcl : IsCl (cusp (pullθ ι θ) n k) := by
    intro x y
    have := ((GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction F (RingHom.id F) 0 0 n (fun _ => 0) (fun _ => 0)).2.2 (rootSum (pullθ ι θ) k)).1 x y
    simp only [cusp]
    rw [this]
  have hinj : Function.Injective ι := ι.toRingHom.injective
  have hθ' : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → pullθ ι θ x = pullθ ι θ y → x = y := by
    intro x y hx hy h
    apply hinj
    refine hθ _ _ ?_ ?_ h
    · exact fun h0 => hx (hinj (h0.trans (map_zero ι).symm))
    · exact fun h0 => hy (hinj (h0.trans (map_zero ι).symm))
  obtain ⟨-, hnormF⟩ := GlobalTheory.T.cuspidalCharacterGL_isCharacter_norm_one_of_regular F (pullθ ι θ) hθ' n k hn hreg
  have hΓ : Nat.card (F' ≃ₐ[F] F') = l := IsGalois.card_aut_eq_finrank F F'
  have htop : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s := fun t => by
    rw [zpowers_eq_top_of_prime_card hΓ hs]; trivial
  have hiso := GlobalTheory.T.shintaniLiftClassFunction_isometry F F' s htop n _ _ hcl hcl
  rw [hnormF] at hiso
  have hnorm : ∑ᶠ g, X (inl g * inr s) * star (X (inl g * inr s)) = (Nat.card (GL (Fin n) F') : ℂ) := by
    have e : ∀ g, X (inl g * inr s) * star (X (inl g * inr s)) =
        shLift s (cusp (pullθ ι θ) n k) g * star (shLift s (cusp (pullθ ι θ) n k) g) := fun g => by
      rw [← congrFun hfun g]
    rw [finsum_congr e]
    have hpos : (Nat.card (GL (Fin n) F) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    apply mul_left_cancel₀ hpos
    rw [hiso, mul_comm]
  set S : F'[X] → ℂ := fun P => ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F')) with hS_def
  have hS1 : S 1 = 0 := by
    simp only [hS_def, Polynomial.map_one]
    apply Finset.prod_eq_zero (Finset.mem_univ 1)
    simp [rootSum]
  have hSprod : S = fun P => ∏ j : Fin l, rootSum θ (k * q ^ (j : ℕ)) P := by
    funext P
    simp only [hS_def]
    rw [GlobalTheory.T.prod_rootPowerSum_map_galois_eq F F' θ k P, Fin.prod_univ_eq_prod_range (fun j => rootSum θ (k * q ^ j) P) l]
  have hprim := GlobalTheory.T.psi_sum_eq_char_sum_against_cusp_form F' θ S n K hS1
  have hprod := GlobalTheory.T.primitiveFunctionCharpoly_pair_prod_rootSum F' θ hθ n K l (fun j => k * q ^ (j : ℕ)) hn
  rw [hcard'] at hprod
  set cnt := (Finset.univ.filter fun a : Fin l → Fin n =>
    K ≡ ∑ j : Fin l, k * q ^ (j : ℕ) * (q ^ l) ^ (a j : ℕ) [MOD (q ^ l) ^ n - 1]).card with hcnt_def
  have hcnt : cnt ≡ 1 [MOD l] := GlobalTheory.T.card_exponent_tuples_modEq_one_of_prime_not_dvd q l n k hq2 hl hn hnd hreg
  have hz : ∑ᶠ g, X (inl g) * star (cusp θ n K g) = ((cnt : ℤ) : ℂ) * (Nat.card (GL (Fin n) F') : ℂ) := by
    simp only [finsum_eq_sum_of_fintype] at hprim hprod ⊢
    have e1 : ∀ g, X (inl g) * star (cusp θ n K g) = c * (psiG S n g * star (cusp θ n K g)) := fun g => by
      simp only [hX_def, hX0a]; ring
    rw [Finset.sum_congr rfl (fun g _ => e1 g), ← Finset.mul_sum, hprim]
    have e2 : ∀ g, chG S n g * star (cusp θ n K g) = star (cusp θ n K g * star (chG S n g)) := fun g => by
      rw [star_mul, star_star, mul_comm]
    rw [Finset.sum_congr rfl (fun g _ => e2 g), ← star_sum]
    have e3 : ∀ g, cusp θ n K g * star (chG S n g) = c * (psiG (rootSum θ K) n g * star (chG S n g)) :=
      fun g => by simp only [cusp, hc_def]; ring
    rw [Finset.sum_congr rfl (fun g _ => e3 g), ← Finset.mul_sum, hSprod, hprod, star_mul', hcstar, ← mul_assoc, hc2,
      one_mul, star_mul', star_natCast, star_natCast]
    push_cast
    ring
  have hndvd : ¬ ((Nat.card (F' ≃ₐ[F] F') : ℤ) ∣ (cnt : ℤ)) := by
    rw [hΓ, Int.natCast_dvd_natCast]
    intro h
    have h1 : cnt % l = 1 % l := hcnt
    rw [(Nat.dvd_iff_mod_eq_zero).1 h, Nat.mod_eq_of_lt hl.one_lt] at h1
    exact zero_ne_one h1
  have key := GlobalTheory.T.twisted_virtualCharacter_norm_one_support (GL (Fin n) F') (F' ≃ₐ[F] F') (galAct F F' n) s (hΓ ▸ hl) hs X hX hnorm (cusp θ n K)
    hYchar hYs (cnt : ℤ) hz hndvd
  rw [hfun] at key
  exact key

end GlobalTheory.Shin
end

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shintani_lift_kills_cusp_of_degree_not_dvd : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (Module.finrank F F').Prime → s ≠ 1 → ∀ (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F') (θ : AlgebraicClosure F' →* ℂ), (∀ x y : AlgebraicClosure F', x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ n k : ℕ, 0 < n → ¬ Module.finrank F F' ∣ n → Reg (Nat.card F) n k → Kills (shLift s (cusp (pullθ ι θ) n k)) (cusp θ n (k * ∑ i ∈ Finset.range (Module.finrank F F'), Nat.card F ^ (n * i))) := by
  first | (exact @GlobalTheory.Shin.shLift_cusp_kills_of_not_dvd) | (exact GlobalTheory.Shin.shLift_cusp_kills_of_not_dvd) | (intros; apply GlobalTheory.Shin.shLift_cusp_kills_of_not_dvd  <;> assumption)
