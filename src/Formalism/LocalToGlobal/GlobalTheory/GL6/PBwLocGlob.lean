module

public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwDecomp
public import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.ExistsDenOfIsCompact

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGlob
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField Classical IsDedekindDomain

theorem bwG_span_dualSet {K : Type} [Field K] [NumberField K] {n : ℕ} (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K)
    (L : Submodule (𝓞 K) (Fin n → K)) :
    ((Submodule.span (𝓞 K) (dualSet σ J L) : Submodule (𝓞 K) (Fin n → K)) : Set (Fin n → K)) = dualSet σ J L := by
  apply le_antisymm
  · intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hy
    | zero =>
      intro x _
      refine ⟨0, ?_⟩
      simp [Formalism.UG.hform]
    | add y y' _ _ hy hy' =>
      intro x hx
      have e : Formalism.UG.hform σ J x (y + y') = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x y' := by
        simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      rw [e]
      exact add_mem (hy x hx) (hy' x hx)
    | smul r y _ hy =>
      intro x hx
      have e : Formalism.UG.hform σ J x (r • y) = algebraMap (𝓞 K) K r * Formalism.UG.hform σ J x y := by
        simp only [Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [e]
      exact mul_mem ⟨r, rfl⟩ (hy x hx)
  · exact Submodule.subset_span

variable (D : D7) (u : D.what₂.Word)

theorem bwG_Ld_coe (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    (Ld D u i hi c : Set (Fin (D.R.N i) → D.host.E)) =
      dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (clsCrd D u i hi c) :=
  bwG_span_dualSet _ _ _

theorem bwG_intSpan_smul (w : D.what₂.places.Pl) {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (r : D.what₂.LL)
    (hr : r ∈ intW D.what₂.places w) {Q : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ} (hQ : Q ∈ Formalism.L2.Forms.IntSpan D w lam) :
    D.what₂.embLL r • Q ∈ Formalism.L2.Forms.IntSpan D w lam := by
  induction hQ using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨s, f, hs, hf, rfl⟩ := hp
    exact AddSubgroup.subset_closure ⟨r * s, f, mul_mem hr hs, hf, by rw [map_mul, mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add p q _ _ hp hq => rw [smul_add]; exact add_mem hp hq
  | neg p _ hp => rw [smul_neg]; exact neg_mem hp

theorem bwG_int_mem (w : D.what₂.places.Pl) (k : 𝓞 D.what₂.LL) :
    algebraMap (𝓞 D.what₂.LL) D.what₂.LL k ∈ intW D.what₂.places w :=
  (D.val_nonneg_iff w _).2 ((D.plEq w).valuation_le_one k)

theorem bwG_inv_mem (w : D.what₂.places.Pl) {r : 𝓞 D.what₂.LL} (hr : r ∉ (D.plEq w).asIdeal) :
    (algebraMap (𝓞 D.what₂.LL) D.what₂.LL r)⁻¹ ∈ intW D.what₂.places w := by
  have hv : (D.plEq w).valuation D.what₂.LL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL r) = 1 :=
    ((D.plEq w).valuation_eq_one_iff_notMem).2 hr
  exact (D.val_nonneg_iff w _).2 (by rw [map_inv₀, hv, inv_one])

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end

section -- merged from Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLcInt
noncomputable section

open NumberField

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms

theorem bwL_descent (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (e : E)
    (he : Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.inclE (F := F) (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AF F) e ∈ Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.SS F E) :
    e ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨D, hD, hDe⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_den_of_incl F E
  set d : E := algebraMap F E (D : F) with hd
  have hd0 : d ≠ 0 := by
    rw [hd]; intro h
    exact hD (by exact_mod_cast (FaithfulSMul.algebraMap_injective F E) (h.trans (map_zero _).symm))
  have hpow : ∀ k : ℕ, d * e ^ k ∈ (algebraMap (𝓞 E) E).range := by
    intro k
    have := hDe (e ^ k) (by rw [map_pow]; exact Subring.pow_mem _ he k)
    rwa [Algebra.smul_def] at this
  let f : 𝓞 E →ₗ[ℤ] E := LinearMap.mulLeft ℤ d⁻¹ ∘ₗ (Algebra.linearMap (𝓞 E) E).restrictScalars ℤ
  have hS : (Algebra.adjoin ℤ ({e} : Set E)).toSubmodule ≤ LinearMap.range f := by
    intro x hx
    rw [Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval] at hx
    obtain ⟨p, rfl⟩ := hx
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_eq_sum_range]
    refine Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ ?_)
    obtain ⟨y, hy⟩ := hpow k
    exact ⟨y, by simp [f, hy, hd0]⟩
  have : IsNoetherian ℤ (LinearMap.range f) := by
    exact isNoetherian_of_surjective f.rangeRestrict (LinearMap.range_rangeRestrict f)
  have : IsNoetherian ℤ (Algebra.adjoin ℤ ({e} : Set E)).toSubmodule := isNoetherian_of_le hS
  have hint : IsIntegral ℤ e :=
    isIntegral_of_submodule_noetherian (Algebra.adjoin ℤ ({e} : Set E)) inferInstance e
      (Algebra.subset_adjoin (Set.mem_singleton e))
  exact ⟨⟨e, hint⟩, rfl⟩

variable (D : D7) (u : D.what₂.Word)


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem bwL_lcInt (Tt : FormsTied D u) : BwLcInt D u := by
  intro i hi c x hx
  apply Submodule.subset_span
  intro x' hx'
  have hglob : ∀ z ∈ clsCrd D u i hi c, z ∈ Formalism.UG.CS.globLat ((Tt.cls i hi).y c).1 (Tt.cls i hi).lev.Lb := by
    intro z hz
    exact ((Tt.cls i hi).y_lat c _).1 (Submodule.subset_span ⟨z, hz, rfl⟩)
  have hm : ∀ a ∈ (Tt.cls i hi).lev.Lb, ∀ b ∈ (Tt.cls i hi).lev.Lb,
      IsIntegral ℤ (((1 : ℤ) : D.host.E) * Formalism.UG.hform (sigD D : D.host.E →+* D.host.E) (gramN D i hi) a b) := by
    intro a ha b hb
    obtain ⟨r, hr⟩ := (Tt.cls i hi).lev.Lb_int b hb a ha
    rw [Int.cast_one, one_mul, ← hr]
    exact RingOfIntegers.isIntegral_coe r
  have h := Formalism.UG.P.csScale_glob (sigD D) (gramN D i hi) (Tt.cls i hi).lev.Lb 1 hm ((Tt.cls i hi).y c).1
    ((Tt.cls i hi).y c).2 (hglob x' hx') (hglob x hx)
  rw [Int.cast_one, one_mul] at h
  exact bwL_descent _ _ _ h

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
end
end
