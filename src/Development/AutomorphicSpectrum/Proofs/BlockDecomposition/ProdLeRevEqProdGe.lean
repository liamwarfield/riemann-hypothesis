module

public import Mathlib

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdLeRevEqProdGe
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdLeRevEqProdGe
namespace GlobalTheory.CompanionTheory.FinReversal

theorem prod_filter_le_rev {M : Type*} [CommMonoid M] (h : ℕ) (f : Fin h → M) (j : Fin h) :
    ∏ a ∈ Finset.univ.filter (fun a => a ≤ j), f (Fin.rev a)
      = ∏ i ∈ Finset.univ.filter (fun i => Fin.rev j ≤ i), f i := by
  refine Finset.prod_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact Fin.rev_le_rev.mpr ha
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [← Fin.rev_le_rev, Fin.rev_rev]
    exact ha
  · intro a _
    exact Fin.rev_rev a
  · intro a _
    exact Fin.rev_rev a
  · intro a _
    rfl

end GlobalTheory.CompanionTheory.FinReversal
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdLeRevEqProdGeStatement
alias GlobalTheory.T.prod_le_rev_eq_prod_ge := GlobalTheory.CompanionTheory.FinReversal.prod_filter_le_rev
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultisetAntitoneEnumeration
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultisetAntitoneEnumeration
namespace GlobalTheory.CompanionTheory.Multiset

theorem exists_antitone_listing {α : Type*} (m : Multiset α) (f : α → ℝ) (P : α → α → Prop)
    (hP : ∀ a b, P a b → f a < f b) :
    ∃ (h : ℕ) (Δ : Fin h → α), Finset.univ.val.map Δ = m ∧ Antitone (f ∘ Δ) ∧
      ∀ i j, i < j → ¬ P (Δ i) (Δ j) := by
  classical
  obtain ⟨l, rfl⟩ := Quot.exists_rep m
  let r : α → α → Prop := fun a b => f b ≤ f a
  haveI : DecidableRel r := fun _ _ => Classical.dec _
  haveI : Std.Total r := ⟨fun a b => le_total (f b) (f a)⟩
  haveI : IsTrans α r := ⟨fun a b c h1 h2 => le_trans h2 h1⟩
  let l' := l.insertionSort r
  have hperm : l'.Perm l := List.perm_insertionSort r l
  have hsort : l'.Pairwise r := List.pairwise_insertionSort r l
  have hlt : ∀ i j : Fin l'.length, i < j → f (l'.get j) ≤ f (l'.get i) := by
    intro i j hij
    exact (List.pairwise_iff_get.mp hsort) i j hij
  refine ⟨l'.length, l'.get, ?_, ?_, ?_⟩
  · have h1 : (Finset.univ : Finset (Fin l'.length)).val.map l'.get = ((List.ofFn l'.get : List α) : Multiset α) := by
      rw [Fin.univ_val_map]
    rw [h1, List.ofFn_get]
    exact Quot.sound hperm
  · intro i j hij
    rcases hij.lt_or_eq with h | h
    · exact hlt i j h
    · subst h; exact le_rfl
  · intro i j hij hp
    exact absurd (hP _ _ hp) (not_lt.mpr (hlt i j hij))

end GlobalTheory.CompanionTheory.Multiset
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultisetAntitoneEnumerationStatement
alias GlobalTheory.T.multiset_antitone_enumeration := GlobalTheory.CompanionTheory.Multiset.exists_antitone_listing
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEvalEqProdOfNatDegreeEq
namespace GlobalTheory.CompanionTheory.AicSplit

open Polynomial

theorem exists_eval_eq_prod_of_natDegree_eq {B : Type} [CommRing B]
    (hB : ∀ p : Polynomial B, p.Monic → 0 < p.natDegree → ∃ a, p.eval a = 0) (d : ℕ) :
    ∀ P : Polynomial B, P.Monic → P.natDegree = d →
      ∃ b : Fin d → B, ∀ a : B, P.eval a = ∏ j, (a - b j) := by
  induction d with
  | zero =>
    intro P hP hd
    refine ⟨fun j => j.elim0, fun a => ?_⟩
    have hc : P.coeff 0 = 1 := by
      rw [← hd]
      exact hP
    rw [eq_C_of_natDegree_eq_zero hd, hc, C_1, eval_one, Fin.prod_univ_zero]
  | succ d ih =>
    intro P hP hd
    rcases subsingleton_or_nontrivial B with hs | hs
    · exfalso
      have h0 : P = 0 := Polynomial.ext fun n => Subsingleton.elim _ _
      rw [h0, natDegree_zero] at hd
      omega
    · obtain ⟨a0, ha0⟩ := hB P hP (by rw [hd]; exact Nat.succ_pos d)
      have hroot : (X - C a0) * (P /ₘ (X - C a0)) = P :=
        mul_divByMonic_eq_iff_isRoot.mpr ha0
      have hQ : (P /ₘ (X - C a0)).Monic :=
        Monic.of_mul_monic_left (monic_X_sub_C a0) (by rw [hroot]; exact hP)
      have hQd : (P /ₘ (X - C a0)).natDegree = d := by
        have h := (monic_X_sub_C a0).natDegree_mul hQ
        rw [hroot, hd, natDegree_X_sub_C] at h
        omega
      obtain ⟨b', hb'⟩ := ih _ hQ hQd
      refine ⟨(Fin.cons a0 b' : Fin (d + 1) → B), fun a => ?_⟩
      have hev : P.eval a = (a - a0) * (P /ₘ (X - C a0)).eval a := by
        conv_lhs => rw [← hroot]
        rw [eval_mul, eval_sub, eval_X, eval_C]
      rw [hev, hb' a, Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]

end GlobalTheory.CompanionTheory.AicSplit
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactSetFiniteCosetRepresentatives
open scoped Topology

namespace GlobalTheory.CompanionTheory.OpenSubgroupCosets

theorem exists_finset_unique_coset_reps :
    ∀ {E : Type} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
      (D : AddSubgroup E), IsOpen (D : Set E) → ∀ (R : Set E), IsCompact R →
      ∃ S : Finset E, (∀ s ∈ S, s ∈ R) ∧ ∀ x ∈ R, ∃! s, s ∈ S ∧ x - s ∈ D := by
  intro E _ _ _ D hD R hR
  classical
  obtain ⟨t, ht⟩ := hR.elim_finite_subcover (fun x : E => (fun y => y - x) ⁻¹' (D : Set E))
    (fun x => hD.preimage (continuous_sub_right x))
    (fun r _ => Set.mem_iUnion.2 ⟨r, by simp⟩)
  set π : E → E ⧸ D := QuotientAddGroup.mk with hπ
  have hfin : (π '' R).Finite := by
    apply (t.finite_toSet.image π).subset
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨x, hx, hrx⟩ : ∃ x ∈ t, r - x ∈ D := by simpa using ht hr
    refine ⟨x, hx, ?_⟩
    apply QuotientAddGroup.eq_iff_sub_mem.2
    rw [← neg_sub]
    exact D.neg_mem hrx
  have hrep : ∀ c ∈ π '' R, ∃ r, r ∈ R ∧ π r = c := by
    rintro _ ⟨r, hr, rfl⟩
    exact ⟨r, hr, rfl⟩
  choose! f hfR hfπ using hrep
  refine ⟨hfin.toFinset.image f, ?_, ?_⟩
  · intro s hs
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hs
    exact hfR c (hfin.mem_toFinset.1 hc)
  · intro x hx
    have hxc : π x ∈ π '' R := ⟨x, hx, rfl⟩
    refine ⟨f (π x), ⟨Finset.mem_image.2 ⟨π x, hfin.mem_toFinset.2 hxc, rfl⟩, ?_⟩, ?_⟩
    · exact QuotientAddGroup.eq_iff_sub_mem.1 (hfπ (π x) hxc).symm
    · rintro s ⟨hs, hxs⟩
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hs
      have hc' := hfin.mem_toFinset.1 hc
      have h1 : π x = c := by
        rw [← hfπ c hc']
        exact QuotientAddGroup.eq_iff_sub_mem.2 hxs
      rw [h1]

end GlobalTheory.CompanionTheory.OpenSubgroupCosets
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFgTmulEqZero
open TensorProduct

namespace GlobalTheory.CompanionTheory.EqCrit

theorem exists_fg_tmul_eq_zero {A : Type} [CommRing A] (B : Type) [CommRing B] [Algebra A B]
    {Q : Type} [AddCommGroup Q] [Module A Q] (z : Q) (h : (1 : B) ⊗ₜ[A] z = 0) :
    ∃ (Q' : Submodule A Q) (hz : z ∈ Q'), Q'.FG ∧ (⟨z, hz⟩ : Q') ⊗ₜ[A] (1 : B) = 0 := by
  classical
  have h' : z ⊗ₜ[A] (1 : B) = 0 := by
    have := congrArg (TensorProduct.comm A B Q) h
    rwa [TensorProduct.comm_tmul, map_zero] at this
  let N0 : {N : Submodule A Q // N.FG} := ⟨Submodule.span A {z}, Submodule.fg_span_singleton z⟩
  have hz0 : z ∈ (N0 : Submodule A Q) := Submodule.mem_span_singleton_self z
  have he : (Module.fgSystem.equiv A Q).symm z =
      Module.DirectLimit.of A {N : Submodule A Q // N.FG} (fun i => ↥(i : Submodule A Q))
        (Module.fgSystem A Q) N0 ⟨z, hz0⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    have := congrArg (fun f => f ⟨z, hz0⟩) (Module.fgSystem.equiv_comp_of (R := A) (M := Q) N0)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply] at this
    exact this.symm
  have h2 : (TensorProduct.directLimitLeft (Module.fgSystem A Q) B)
      ((LinearMap.rTensor B ((Module.fgSystem.equiv A Q).symm : Q →ₗ[A] _)) (z ⊗ₜ[A] (1 : B))) = 0 := by
    rw [h', map_zero, map_zero]
  rw [LinearMap.rTensor_tmul, LinearEquiv.coe_coe, he, TensorProduct.directLimitLeft_tmul_of] at h2
  haveI : DirectedSystem (fun i : {N : Submodule A Q // N.FG} => TensorProduct A (↥(i : Submodule A Q)) B)
      (fun i j h => ⇑(LinearMap.rTensor B (Module.fgSystem A Q i j h))) :=
    DirectedSystem.rTensor A B (f := fun ⦃i j⦄ h => Module.fgSystem A Q i j h) inferInstance
  obtain ⟨j, hij, hj⟩ := Module.DirectLimit.of.zero_exact h2
  refine ⟨(j : Submodule A Q), (show (N0 : Submodule A Q) ≤ j from hij) hz0, j.2, ?_⟩
  rw [LinearMap.rTensor_tmul] at hj
  exact hj

theorem exists_system {A : Type} [CommRing A] (B : Type) [CommRing B] [Algebra A B]
    {Q : Type} [AddCommGroup Q] [Module A Q] (z : Q) (h : (1 : B) ⊗ₜ[A] z = 0) :
    ∃ (m n : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A),
      (∃ y : Fin n → B, ∀ t, ∑ j, a t j • y j = algebraMap A B (c t)) ∧
      ∀ (B₁ : Type) [CommRing B₁] [Algebra A B₁],
        (∃ y : Fin n → B₁, ∀ t, ∑ j, a t j • y j = algebraMap A B₁ (c t)) →
          (1 : B₁) ⊗ₜ[A] z = 0 := by
  classical
  obtain ⟨Q', hz, hfg, hzero⟩ := exists_fg_tmul_eq_zero B z h
  haveI : Module.Finite A Q' := Module.Finite.iff_fg.mpr hfg
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' A Q'
  obtain ⟨w, hw⟩ := hπ ⟨z, hz⟩
  have hex := lTensor_exact B (LinearMap.exact_subtype_ker_map π) hπ
  have h1 : LinearMap.lTensor B π ((1 : B) ⊗ₜ[A] w) = 0 := by
    rw [LinearMap.lTensor_tmul, hw]
    have := congrArg (TensorProduct.comm A Q' B) hzero
    rwa [TensorProduct.comm_tmul, map_zero] at this
  obtain ⟨x, hx⟩ := (hex ((1 : B) ⊗ₜ[A] w)).mp h1
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset x
  let e := S.equivFin
  let b : Fin S.card → B := fun t => (e.symm t : B × LinearMap.ker π).1
  let kk : Fin S.card → LinearMap.ker π := fun t => (e.symm t : B × LinearMap.ker π).2
  have hxsum : x = ∑ t, b t ⊗ₜ[A] kk t := by
    rw [hS, ← Finset.sum_coe_sort, ← Equiv.sum_comp e.symm]
  have hx' : ∑ t, b t ⊗ₜ[A] (kk t : Fin n → A) = (1 : B) ⊗ₜ[A] w := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hx, hxsum, map_sum]
    simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply]
  refine ⟨n, S.card, fun s t => (kk t : Fin n → A) s, w, ⟨b, fun s => ?_⟩, ?_⟩
  · have hvec := congrFun (congrArg (TensorProduct.piScalarRight A B B (Fin n)) hx') s
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      Finset.sum_apply] at hvec
    rw [Algebra.algebraMap_eq_smul_one]
    exact hvec
  · intro B₁ _ _ hy
    obtain ⟨y, hy⟩ := hy
    have h2 : ∑ t, y t ⊗ₜ[A] (kk t : Fin n → A) = (1 : B₁) ⊗ₜ[A] w := by
      apply (TensorProduct.piScalarRight A B₁ B₁ (Fin n)).injective
      funext s
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
        Finset.sum_apply]
      rw [← Algebra.algebraMap_eq_smul_one]
      exact hy s
    have h3 := congrArg (LinearMap.lTensor B₁ (Q'.subtype ∘ₗ π)) h2
    have hk : ∀ t, π (kk t : Fin n → A) = 0 := fun t => LinearMap.mem_ker.mp (kk t).2
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.lTensor_tmul, LinearMap.comp_apply, hk, hw, map_zero,
      TensorProduct.tmul_zero, Finset.sum_const_zero, Submodule.subtype_apply] at h3
    exact h3.symm

end GlobalTheory.CompanionTheory.EqCrit
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPrincipalCongruence
open Matrix

namespace GlobalTheory.CompanionTheory.PrincipalCongruence

variable {k Γ : Type*} [Field k] [LinearOrderedCommGroupWithZero Γ]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem entry_mul_le (v : Valuation k Γ) {r s : Γ} (hs : s ≤ 1)
    {A B : Matrix n n k} (hA : ∀ i j, v (A i j) ≤ r) (hB : ∀ i j, v (B i j) ≤ s) (i j : n) :
    v ((A * B) i j) ≤ r := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le v fun l _ => ?_
  rw [map_mul]
  calc v (A i l) * v (B l j) ≤ r * s := mul_le_mul' (hA i l) (hB l j)
    _ ≤ r * 1 := mul_le_mul' le_rfl hs
    _ = r := mul_one r

theorem inv_entry_le_one (v : Valuation k Γ) {r : Γ} (hr : r < 1)
    {A B : Matrix n n k} (hBA : B * (1 + A) = 1) (hA : ∀ i j, v (A i j) ≤ r) (i j : n) :
    v (B i j) ≤ 1 := by
  haveI : Nonempty (n × n) := ⟨(i, j)⟩
  obtain ⟨⟨a, b⟩, hmax⟩ := Finite.exists_max (fun p : n × n => v (B p.1 p.2))
  have hM : ∀ i j, v (B i j) ≤ v (B a b) := fun i j => hmax (i, j)
  refine (hM i j).trans ?_
  by_contra hlt
  have hgt : 1 < v (B a b) := not_le.mp hlt
  have hpos : 0 < v (B a b) := zero_lt_one.trans hgt
  have hB : B = 1 - B * A := by
    have : B + B * A = 1 := by rw [← hBA, mul_add, mul_one]
    exact eq_sub_of_add_eq this
  have hprod : v ((B * A) a b) ≤ v (B a b) * r := by
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_le v fun l _ => ?_
    rw [map_mul]
    exact mul_le_mul' (hM a l) (hA l b)
  have hlt' : v (B a b) * r < v (B a b) := by
    calc v (B a b) * r < v (B a b) * 1 := by
          exact mul_lt_mul_of_pos_left hr hpos
      _ = v (B a b) := mul_one _
  have hone : v ((1 : Matrix n n k) a b) ≤ 1 := by
    by_cases h : a = b
    · rw [h, Matrix.one_apply_eq, map_one]
    · rw [Matrix.one_apply_ne h, map_zero]
      exact zero_le_one
  have hentry : B a b = (1 : Matrix n n k) a b - (B * A) a b := by
    conv_lhs => rw [hB]
    rfl
  have hle : v (B a b) ≤ max (v ((1 : Matrix n n k) a b)) (v ((B * A) a b)) := by
    rw [hentry]
    exact Valuation.map_sub v _ _
  rcases le_max_iff.mp hle with h | h
  · exact absurd (h.trans hone) (not_le.mpr hgt)
  · exact absurd (h.trans hprod) (not_le.mpr hlt')

def principalCongruence (v : Valuation k Γ) (r : Γ) (hr : r < 1) :
    Subgroup (GL n k) where
  carrier := {g | ∀ i j, v ((g : Matrix n n k) i j - (1 : Matrix n n k) i j) ≤ r}
  one_mem' := by
    intro i j
    simp
  mul_mem' := by
    intro g h hg hh i j
    have hg' : ∀ i j, v (((g : Matrix n n k) - 1) i j) ≤ r := hg
    have hh' : ∀ i j, v (((h : Matrix n n k) - 1) i j) ≤ r := hh
    have key : ((g * h : GL n k) : Matrix n n k) - 1 =
        ((g : Matrix n n k) - 1) * ((h : Matrix n n k) - 1) +
          (((g : Matrix n n k) - 1) + ((h : Matrix n n k) - 1)) := by
      rw [Units.val_mul]
      noncomm_ring
    have key' : ((g * h : GL n k) : Matrix n n k) i j - (1 : Matrix n n k) i j =
        (((g : Matrix n n k) - 1) * ((h : Matrix n n k) - 1)) i j +
          ((((g : Matrix n n k) - 1) i j) + (((h : Matrix n n k) - 1) i j)) := by
      rw [← Matrix.sub_apply, key]
      rfl
    rw [key']
    exact Valuation.map_add_le v (entry_mul_le v hr.le hg' hh' i j)
      (Valuation.map_add_le v (hg' i j) (hh' i j))
  inv_mem' := by
    intro g hg i j
    have hg' : ∀ i j, v (((g : Matrix n n k) - 1) i j) ≤ r := hg
    have hBA : ((g⁻¹ : GL n k) : Matrix n n k) * (1 + ((g : Matrix n n k) - 1)) = 1 := by
      rw [add_sub_cancel, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hint := inv_entry_le_one v hr hBA hg'
    have key : ((g⁻¹ : GL n k) : Matrix n n k) - 1 =
        -(((g⁻¹ : GL n k) : Matrix n n k) * ((g : Matrix n n k) - 1)) := by
      rw [mul_sub, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
      abel
    have key' : ((g⁻¹ : GL n k) : Matrix n n k) i j - (1 : Matrix n n k) i j =
        -((((g⁻¹ : GL n k) : Matrix n n k) * ((g : Matrix n n k) - 1)) i j) := by
      rw [← Matrix.sub_apply, key]
      rfl
    rw [key', Valuation.map_neg, Matrix.mul_apply]
    refine Valuation.map_sum_le v fun l _ => ?_
    rw [map_mul]
    calc v (((g⁻¹ : GL n k) : Matrix n n k) i l) * v (((g : Matrix n n k) - 1) l j)
        ≤ 1 * r := mul_le_mul' (hint i l) (hg' l j)
      _ = r := one_mul r

theorem exists_principalCongruence :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (N : ℕ) (t : k), t ≠ 0 → ValuativeRel.valuation k (t) < 1 →
      ∃ H : Subgroup (GL (Fin N) k), (H : Set (GL (Fin N) k)) =
        {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k
          ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
            ValuativeRel.valuation k (t)} := by
  intro k _ _ _ _ N t _ ht
  exact ⟨principalCongruence (ValuativeRel.valuation k) _ ht, rfl⟩

end GlobalTheory.CompanionTheory.PrincipalCongruence
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUdlOfIsUnit
namespace GlobalTheory.CompanionTheory.IwahoriUDL

open Matrix

variable {R : Type*} [CommRing R]

def ex (n : ℕ) : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv

theorem ex_inl {n : ℕ} (i : Fin n) : ex n (Sum.inl i) = i.castSucc := rfl

theorem ex_inr {n : ℕ} (k : Fin 1) : ex n (Sum.inr k) = Fin.last n := by
  have hk : k = 0 := Subsingleton.elim _ _
  subst hk
  ext
  simp [ex]

theorem one_ex {n : ℕ} (i j : Fin n ⊕ Fin 1) :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (ex n i) (ex n j) =
      fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 (1 : Matrix (Fin 1) (Fin 1) R) i j := by
  rw [fromBlocks_one]
  simp [Matrix.one_apply]

def IsUp (I : Ideal R) {n : ℕ} (u : Matrix (Fin n) (Fin n) R) : Prop :=
  (∀ i j, u i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I) ∧ (∀ i j, j < i → u i j = 0) ∧
    ∀ i, u i i = 1

def IsLo (I : Ideal R) {n : ℕ} (l : Matrix (Fin n) (Fin n) R) : Prop :=
  (∀ i j, l i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I) ∧ (∀ i j, i < j → l i j = 0) ∧
    ∀ i, l i i = 1

def IsDi (I : Ideal R) {n : ℕ} (d : Matrix (Fin n) (Fin n) R) : Prop :=
  (∀ i j, d i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I) ∧ ∀ i j, i ≠ j → d i j = 0

theorem up_step {I : Ideal R} {n : ℕ} {u : Matrix (Fin n) (Fin n) R} (hu : IsUp I u)
    {x : Matrix (Fin n) (Fin 1) R} (hx : ∀ i k, x i k ∈ I) :
    IsUp I ((fromBlocks u x 0 1).submatrix (ex n).symm (ex n).symm) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    obtain ⟨i, rfl⟩ := (ex n).surjective i
    obtain ⟨j, rfl⟩ := (ex n).surjective j
    rw [one_ex, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    · simpa using hu.1 i j
    · simpa using hx i j
    · simp
    · simp
  · intro i j hij
    obtain ⟨i, rfl⟩ := (ex n).surjective i
    obtain ⟨j, rfl⟩ := (ex n).surjective j
    rw [submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    · simp only [ex_inl, Fin.castSucc_lt_castSucc_iff] at hij
      simpa using hu.2.1 i j hij
    · simp only [ex_inl, ex_inr] at hij
      exact absurd hij (not_lt.mpr (Fin.le_last _))
    · simp
    · simp only [ex_inr, lt_self_iff_false] at hij
  · intro i
    obtain ⟨i, rfl⟩ := (ex n).surjective i
    rw [submatrix_apply, Equiv.symm_apply_apply]
    rcases i with i | i
    · simpa using hu.2.2 i
    · simp

theorem lo_step {I : Ideal R} {n : ℕ} {l : Matrix (Fin n) (Fin n) R} (hl : IsLo I l)
    {y : Matrix (Fin 1) (Fin n) R} (hy : ∀ k j, y k j ∈ I) :
    IsLo I ((fromBlocks l 0 y 1).submatrix (ex n).symm (ex n).symm) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    obtain ⟨i, rfl⟩ := (ex n).surjective i
    obtain ⟨j, rfl⟩ := (ex n).surjective j
    rw [one_ex, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    · simpa using hl.1 i j
    · simp
    · simpa using hy i j
    · simp
  · intro i j hij
    obtain ⟨i, rfl⟩ := (ex n).surjective i
    obtain ⟨j, rfl⟩ := (ex n).surjective j
    rw [submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    · simp only [ex_inl, Fin.castSucc_lt_castSucc_iff] at hij
      simpa using hl.2.1 i j hij
    · simp
    · simp only [ex_inl, ex_inr] at hij
      exact absurd hij (not_lt.mpr (Fin.le_last _))
    · simp only [ex_inr, lt_self_iff_false] at hij
  · intro i
    obtain ⟨i, rfl⟩ := (ex n).surjective i
    rw [submatrix_apply, Equiv.symm_apply_apply]
    rcases i with i | i
    · simpa using hl.2.2 i
    · simp

theorem di_step {I : Ideal R} {n : ℕ} {d : Matrix (Fin n) (Fin n) R} (hd : IsDi I d)
    {a : Matrix (Fin 1) (Fin 1) R} (ha : ∀ k k', a k k' - (1 : Matrix (Fin 1) (Fin 1) R) k k' ∈ I) :
    IsDi I ((fromBlocks d 0 0 a).submatrix (ex n).symm (ex n).symm) := by
  refine ⟨?_, ?_⟩
  · intro i j
    obtain ⟨i, rfl⟩ := (ex n).surjective i
    obtain ⟨j, rfl⟩ := (ex n).surjective j
    rw [one_ex, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    · simpa using hd.1 i j
    · simp
    · simp
    · simpa using ha i j
  · intro i j hij
    obtain ⟨i, rfl⟩ := (ex n).surjective i
    obtain ⟨j, rfl⟩ := (ex n).surjective j
    rw [submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    · have : i ≠ j := fun h => hij (by rw [h])
      simpa using hd.2 i j this
    · simp
    · simp
    · exact absurd (by rw [Subsingleton.elim i j]) hij

theorem fromBlocks_udl {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (c : Matrix (Fin n) (Fin 1) R)
    (r : Matrix (Fin 1) (Fin n) R) (a b : Matrix (Fin 1) (Fin 1) R) (hab : a * b = 1)
    (hba : b * a = 1) (u d l : Matrix (Fin n) (Fin n) R) (h : A - c * b * r = u * d * l) :
    fromBlocks A c r a =
      fromBlocks u (c * b) 0 1 * fromBlocks d 0 0 a * fromBlocks l 0 (b * r) 1 := by
  have h' : A = u * d * l + c * b * r := by rw [← h]; abel
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, Matrix.one_mul]
  rw [Matrix.mul_assoc c b a, hba, Matrix.mul_one, ← Matrix.mul_assoc a b r, hab, Matrix.one_mul]
  rw [h', Matrix.mul_assoc c b r]

theorem exists_udl_of_isUnit (I : Ideal R) (hI : ∀ x ∈ I, IsUnit (1 + x)) (n : ℕ) :
    ∀ g : Matrix (Fin n) (Fin n) R,
      (∀ i j, g i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I) →
        ∃ u d l : Matrix (Fin n) (Fin n) R, IsUp I u ∧ IsDi I d ∧ IsLo I l ∧ g = u * d * l := by
  induction n with
  | zero =>
    intro g _
    exact ⟨1, 1, 1, ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩,
      ⟨fun i => i.elim0, fun i => i.elim0⟩, ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩,
      Subsingleton.elim _ _⟩
  | succ n ih =>
    intro g hg
    set A : Matrix (Fin n) (Fin n) R := fun i j => g i.castSucc j.castSucc with hA
    set c : Matrix (Fin n) (Fin 1) R := fun i _ => g i.castSucc (Fin.last n) with hc
    set r : Matrix (Fin 1) (Fin n) R := fun _ j => g (Fin.last n) j.castSucc with hr
    set s : R := g (Fin.last n) (Fin.last n) with hs
    have hs1 : s - 1 ∈ I := by simpa [hs] using hg (Fin.last n) (Fin.last n)
    have hsu : IsUnit s := by simpa using hI _ hs1
    obtain ⟨t, hst⟩ := hsu.exists_right_inv
    have hts : t * s = 1 := by rw [mul_comm]; exact hst
    have hcI : ∀ i k, c i k ∈ I := fun i k => by
      have := hg i.castSucc (Fin.last n)
      rw [Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne, sub_zero] at this
      exact this
    have hrI : ∀ k j, r k j ∈ I := fun k j => by
      have := hg (Fin.last n) j.castSucc
      rw [Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne', sub_zero] at this
      exact this
    set a : Matrix (Fin 1) (Fin 1) R := fun _ _ => s with ha
    set b : Matrix (Fin 1) (Fin 1) R := fun _ _ => t with hb
    have hab : a * b = 1 := by
      ext i j
      rw [Subsingleton.elim i j, Matrix.mul_apply, Matrix.one_apply_eq]
      simp only [Finset.univ_unique, Finset.sum_singleton]
      exact hst
    have hba : b * a = 1 := by
      ext i j
      rw [Subsingleton.elim i j, Matrix.mul_apply, Matrix.one_apply_eq]
      simp only [Finset.univ_unique, Finset.sum_singleton]
      exact hts
    have hS : ∀ i j, (A - c * b * r) i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I := by
      intro i j
      have h1 : A i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I := by
        have := hg i.castSucc j.castSucc
        simpa [hA, Matrix.one_apply] using this
      have h2 : (c * b * r) i j ∈ I := by
        simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton]
        exact I.mul_mem_right _ (I.mul_mem_right _ (hcI i default))
      have h3 : (A - c * b * r) i j - (1 : Matrix (Fin n) (Fin n) R) i j =
          (A i j - (1 : Matrix (Fin n) (Fin n) R) i j) - (c * b * r) i j := by
        simp only [Matrix.sub_apply]
        ring
      rw [h3]
      exact I.sub_mem h1 h2
    obtain ⟨u, d, l, hu, hd, hl, hudl⟩ := ih _ hS
    have hcb : ∀ i k, (c * b) i k ∈ I := fun i k => by
      simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton]
      exact I.mul_mem_right _ (hcI i default)
    have hbr : ∀ k j, (b * r) k j ∈ I := fun k j => by
      simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton]
      exact I.mul_mem_left _ (hrI default j)
    have haI : ∀ k k', a k k' - (1 : Matrix (Fin 1) (Fin 1) R) k k' ∈ I := fun k k' => by
      simpa [ha, Matrix.one_apply, Subsingleton.elim k k'] using hs1
    refine ⟨_, _, _, up_step hu hcb, di_step hd haI, lo_step hl hbr, ?_⟩
    have hblock : g.submatrix (ex n) (ex n) = fromBlocks A c r a := by
      ext i j
      rcases i with i | i <;> rcases j with j | j
      · rw [submatrix_apply, ex_inl, ex_inl]; rfl
      · rw [submatrix_apply, ex_inl, ex_inr]; rfl
      · rw [submatrix_apply, ex_inr, ex_inl]; rfl
      · rw [submatrix_apply, ex_inr, ex_inr]; rfl
    have hg' : g = (fromBlocks A c r a).submatrix (ex n).symm (ex n).symm := by
      rw [← hblock]
      simp
    rw [hg', fromBlocks_udl A c r a b hab hba u d l hudl]
    simp only [Matrix.submatrix_mul_equiv]

theorem iwahori_udl : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (n : ℕ)
    (ϖ : R) (m : ℕ), Irreducible ϖ → 1 ≤ m → ∀ g : Matrix (Fin n) (Fin n) R,
    (∀ i j, g i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ Ideal.span {ϖ ^ m}) →
    ∃ (u d l : Matrix (Fin n) (Fin n) R),
      (∀ i j, u i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ Ideal.span {ϖ ^ m}) ∧
      (∀ i j, d i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ Ideal.span {ϖ ^ m}) ∧
      (∀ i j, l i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ Ideal.span {ϖ ^ m}) ∧
      (∀ i j, j < i → u i j = 0) ∧ (∀ i, u i i = 1) ∧ (∀ i j, i ≠ j → d i j = 0) ∧
      (∀ i j, i < j → l i j = 0) ∧ (∀ i, l i i = 1) ∧ g = u * d * l := by
  intro R _ _ _ n ϖ m hϖ hm g hg
  have hmem : ϖ ^ m ∈ IsLocalRing.maximalIdeal R :=
    Ideal.pow_mem_of_mem _ ((IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit) m (by omega)
  have hle : Ideal.span {ϖ ^ m} ≤ IsLocalRing.maximalIdeal R :=
    (Ideal.span_singleton_le_iff_mem _).mpr hmem
  have hI : ∀ x ∈ Ideal.span {ϖ ^ m}, IsUnit (1 + x) := by
    intro x hx
    by_contra hnu
    have h1 : 1 + x ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have h2 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
      simpa using Ideal.sub_mem _ h1 (hle hx)
    exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal R).ne_top h2
  obtain ⟨u, d, l, hu, hd, hl, h⟩ := exists_udl_of_isUnit _ hI n g hg
  exact ⟨u, d, l, hu.1, hd.1, hl.1, hu.2.1, hu.2.2, hd.2, hl.2.1, hl.2.2, h⟩

end GlobalTheory.CompanionTheory.IwahoriUDL
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SesquilinearEqZeroOfDiagZero
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SesquilinearEqZeroOfDiagZero
open Matrix

namespace GlobalTheory.CompanionTheory.Sesquilinear

theorem eq_zero_of_diag_eq_zero {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (h : ∀ v, B v v = 0) : B = 0 := by
  ext v w
  have h1 := h (v + w)
  have h2 := h (v + Complex.I • w)
  simp only [map_add (f := _), LinearMap.add_apply, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
    h v, h w, smul_eq_mul, zero_add, add_zero, Complex.conj_I, RingHom.id_apply,
    mul_zero] at h1 h2
  have h3 : B v w = B w v := by
    have : Complex.I * (B w v - B v w) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp this with h4 | h4
    · exact absurd h4 Complex.I_ne_zero
    · exact (sub_eq_zero.mp h4).symm
  have h5 : (2 : ℂ) * B v w = 0 := by linear_combination h1 + h3
  simpa using h5

end GlobalTheory.CompanionTheory.Sesquilinear
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SesquilinearEqZeroOfDiagZeroStatement
open Matrix
alias GlobalTheory.T.sesquilinear_eq_zero_of_diag_zero := GlobalTheory.CompanionTheory.Sesquilinear.eq_zero_of_diag_eq_zero
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGLLastBasisVecMulEq
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGLLastBasisVecMulEq
open Matrix
open scoped Topology

namespace GlobalTheory.CompanionTheory.RowSect

theorem exists_GL_last_row (k : Type) [Field k] (m : ℕ) (ξ : Fin (m + 1) → k) (hξ : ξ ≠ 0) :
    ∃ h : GL (Fin (m + 1)) k,
      (Pi.single (Fin.last m) 1 : Fin (m + 1) → k) ᵥ* (h : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ξ := by
  classical
  have hs : LinearIndepOn k id ({ξ} : Set (Fin (m + 1) → k)) := (linearIndepOn_singleton_iff k).2 hξ
  have hmem : ξ ∈ hs.extend (Set.subset_univ _) := Module.Basis.subset_extend hs (Set.mem_singleton ξ)
  have hcard : Fintype.card (hs.extend (Set.subset_univ _)) = m + 1 := by
    rw [← Module.finrank_eq_card_basis (Module.Basis.extend hs), Module.finrank_fin_fun]
  let e₀ := Fintype.equivFinOfCardEq hcard
  let e := e₀.trans (Equiv.swap (e₀ ⟨ξ, hmem⟩) (Fin.last m))
  have he : e.symm (Fin.last m) = ⟨ξ, hmem⟩ := by
    rw [Equiv.symm_apply_eq]
    simp [e]
  let b := (Module.Basis.extend hs).reindex e
  have hlast : b (Fin.last m) = ξ := by
    simp only [b, Module.Basis.reindex_apply, he, Module.Basis.extend_apply_self]
  have hu : IsUnit (Matrix.of fun i j => b i j) :=
    Matrix.linearIndependent_rows_iff_isUnit.1 b.linearIndependent
  refine ⟨hu.unit, ?_⟩
  rw [IsUnit.unit_spec, single_vecMul, one_smul]
  exact hlast

end GlobalTheory.CompanionTheory.RowSect
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGLLastBasisVecMulEqStatement
open Matrix
open scoped Topology
alias GlobalTheory.T.exists_GL_last_basis_vecMul_eq := GlobalTheory.CompanionTheory.RowSect.exists_GL_last_row
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetSumTranslateInvariant
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetSumTranslateInvariant
open Matrix

namespace GlobalTheory.CompanionTheory.Transversal

theorem sum_add_eq_sum_of_transversal : ∀ {X : Type} [AddCommGroup X] {M : Type} [AddCommMonoid M] {A H : AddSubgroup X}, H ≤ A → ∀ {T : Finset X}, (∀ t ∈ T, t ∈ A) → (∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H) → ∀ (F : X → M), (∀ a, ∀ h ∈ H, F (a + h) = F a) → ∀ {a : X}, a ∈ A → ∑ t ∈ T, F (t + a) = ∑ t ∈ T, F t := by
  intro X _ M _ A H hHA T hTA huniq F hF a ha
  classical
  have hex : ∀ t ∈ T, ∃ t', t' ∈ T ∧ (t + a) - t' ∈ H := fun t ht =>
    (huniq (t + a) (A.add_mem (hTA t ht) ha)).exists
  choose! g hgT hgH using hex
  have uniq : ∀ x ∈ A, ∀ t₁ t₂, t₁ ∈ T → x - t₁ ∈ H → t₂ ∈ T → x - t₂ ∈ H → t₁ = t₂ :=
    fun x hx t₁ t₂ h1 h1' h2 h2' => (huniq x hx).unique ⟨h1, h1'⟩ ⟨h2, h2'⟩
  refine Finset.sum_bij (fun t _ => g t) (fun t ht => hgT t ht) ?_ ?_ ?_
  · intro t₁ h₁ t₂ h₂ heq
    have hd : t₁ - t₂ ∈ H := by
      have h3 := H.sub_mem (hgH t₁ h₁) (hgH t₂ h₂)
      have e : t₁ + a - g t₁ - (t₂ + a - g t₂) = t₁ - t₂ := by rw [heq]; abel
      rwa [e] at h3
    exact uniq t₁ (hTA t₁ h₁) t₁ t₂ h₁ (by rw [sub_self]; exact H.zero_mem) h₂ hd
  · intro t' ht'
    obtain ⟨t, ⟨htT, htH⟩, -⟩ := huniq (t' - a) (A.sub_mem (hTA t' ht') ha)
    refine ⟨t, htT, ?_⟩
    have h1 : t + a - t' ∈ H := by
      have h3 := H.neg_mem htH
      have e : -(t' - a - t) = t + a - t' := by abel
      rwa [e] at h3
    exact uniq (t + a) (A.add_mem (hTA t htT) ha) (g t) t' (hgT t htT) (hgH t htT) ht' h1
  · intro t ht
    have h3 := hF (g t) _ (hgH t ht)
    have e : g t + (t + a - g t) = t + a := by abel
    rw [e] at h3
    exact h3

end GlobalTheory.CompanionTheory.Transversal
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetSumTranslateInvariantStatement
open Matrix
alias GlobalTheory.T.coset_sum_translate_invariant := GlobalTheory.CompanionTheory.Transversal.sum_add_eq_sum_of_transversal
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGLVecMulEqLastBasis
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGLVecMulEqLastBasis
open Matrix

namespace GlobalTheory.CompanionTheory.Matrixlemmas

theorem exists_GL_vecMul_eq_single_last {k : Type} [Field k] (n : ℕ) (ξ : Fin (n + 1) → k) (hξ : ξ ≠ 0) :
    ∃ g : GL (Fin (n + 1)) k,
      Matrix.vecMul ξ (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = Pi.single (Fin.last n) 1 := by
  classical
  obtain ⟨c, hc⟩ : ∃ c, ξ c ≠ 0 := by
    by_contra hcon
    exact hξ (funext fun i => by_contra fun hi => hcon ⟨i, hi⟩)
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap c (Fin.last n)
  let U : Matrix (Fin (n + 1)) (Fin (n + 1)) k :=
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateRow c ξ
  have hU : U.det = ξ c := by
    have hT : Uᵀ = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateCol c ξ := by
      simp only [U]
      rw [← Matrix.updateCol_transpose, Matrix.transpose_one]
    rw [← Matrix.det_transpose, hT, ← Matrix.cramer_apply, Matrix.cramer_one]
    rfl
  let h : Matrix (Fin (n + 1)) (Fin (n + 1)) k := U.submatrix σ id
  have hdet : IsUnit h.det := by
    have : h.det = Equiv.Perm.sign σ * U.det := Matrix.det_permute σ U
    rw [this, hU]
    refine IsUnit.mul ?_ (isUnit_iff_ne_zero.mpr hc)
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> simp [e]
  have hrow : Matrix.vecMul (Pi.single (Fin.last n) 1) h = ξ := by
    rw [Matrix.single_one_vecMul]
    funext j
    simp [h, U, σ]
  refine ⟨(Matrix.nonsingInvUnit h hdet)⁻¹, ?_⟩
  have hinv : h * (((Matrix.nonsingInvUnit h hdet)⁻¹ : GL (Fin (n + 1)) k) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) k) = 1 :=
    (Matrix.nonsingInvUnit h hdet).mul_inv
  conv_lhs => rw [← hrow]
  rw [Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one]

end GlobalTheory.CompanionTheory.Matrixlemmas
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGLVecMulEqLastBasisStatement
open Matrix
alias GlobalTheory.T.exists_GL_vecMul_eq_last_basis := GlobalTheory.CompanionTheory.Matrixlemmas.exists_GL_vecMul_eq_single_last
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteCosetRepresentatives
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteCosetRepresentatives
open Matrix

namespace GlobalTheory.CompanionTheory.OpenSubgroupTransversal

theorem finite_transversal {X : Type} [TopologicalSpace X] [AddCommGroup X]
    [IsTopologicalAddGroup X] (A H : AddSubgroup X) (hA : IsCompact (A : Set X))
    (hH : IsOpen (H : Set X)) (_hHA : H ≤ A) :
    ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H := by
  classical
  haveI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  have hopen : IsOpen ((H.addSubgroupOf A : AddSubgroup A) : Set A) :=
    hH.preimage continuous_subtype_val
  haveI : Finite (A ⧸ H.addSubgroupOf A) := AddSubgroup.quotient_finite_of_isOpen _ hopen
  haveI : Fintype (A ⧸ H.addSubgroupOf A) := Fintype.ofFinite _
  let rep : A ⧸ H.addSubgroupOf A → X := fun q => ((Quotient.out q : A) : X)
  refine ⟨Finset.univ.image rep, ?_, ?_⟩
  · intro t ht
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp ht
    exact (Quotient.out q).2
  · intro a ha
    have key : ∀ q : A ⧸ H.addSubgroupOf A,
        a - rep q ∈ H ↔ q = QuotientAddGroup.mk ⟨a, ha⟩ := by
      intro q
      conv_rhs => rw [← QuotientAddGroup.out_eq' q]
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, sub_eq_add_neg, add_comm]
      exact Iff.rfl
    refine ⟨rep (QuotientAddGroup.mk ⟨a, ha⟩),
      ⟨Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, (key _).mpr rfl⟩, ?_⟩
    rintro t ⟨ht, hat⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp ht
    rw [(key q).mp hat]

theorem main : ∀ {X : Type} [TopologicalSpace X] [AddCommGroup X] [IsTopologicalAddGroup X]
    (A H : AddSubgroup X), IsCompact (A : Set X) → IsOpen (H : Set X) → H ≤ A →
    ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H :=
  fun A H hA hH hHA => GlobalTheory.CompanionTheory.OpenSubgroupTransversal.finite_transversal A H hA hH hHA

end GlobalTheory.CompanionTheory.OpenSubgroupTransversal
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteCosetRepresentativesStatement
open Matrix
alias GlobalTheory.T.exists_finite_coset_representatives := GlobalTheory.CompanionTheory.OpenSubgroupTransversal.main
end
end
