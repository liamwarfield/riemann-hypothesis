module

public import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg

@[expose] public section

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.CurveCountA
namespace Formalism.L2.Pj.CurveCount

open MvPolynomial

theorem eval₂_mul_homog {R S σ : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) (c : S) (g : σ → S)
    {P : MvPolynomial σ R} {k : ℕ} (hP : P.IsHomogeneous k) :
    P.eval₂ f (fun i => c * g i) = c ^ k * P.eval₂ f g := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ i ∈ m.support, m i = k := by
    have h := hP (MvPolynomial.mem_support_iff.1 hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

theorem aeval_div_homog {K L σ : Type*} [Field K] [Field L] [Algebra K L] (g : σ → L) (c : L)
    {P : MvPolynomial σ K} {k : ℕ} (hP : P.IsHomogeneous k) :
    aeval (fun i => g i / c) P = c⁻¹ ^ k * aeval g P := by
  have h := eval₂_mul_homog (algebraMap K L) c⁻¹ g hP
  show MvPolynomial.eval₂ (algebraMap K L) (fun i => g i / c) P =
    c⁻¹ ^ k * MvPolynomial.eval₂ (algebraMap K L) g P
  rw [← h]
  congr 1
  funext i
  rw [div_eq_mul_inv, mul_comm]

theorem exists_indep_ratios {K κ : Type*} [Field K] [Field κ] [Algebra K κ] {N D : ℕ} (x : Fin N → κ) (a : Fin N)
    (hxa : x a ≠ 0) (t : Fin (D + 1) × Fin N → κ) (ht : AlgebraicIndependent K t)
    (hlin : ∀ i : Fin D, ∑ k, t (i.succ, k) * x k = 0) (hlin0 : ∑ k, t (0, k) * x k = 1) :
    ∃ s : Finset κ, s.card = D ∧ (↑s : Set κ) ⊆ Set.range (fun i => x i / x a) ∧
      AlgebraicIndepOn K id (↑s : Set κ) := by
  classical
  have : FaithfulSMul K κ := (faithfulSMul_iff_algebraMap_injective K κ).mpr (algebraMap K κ).injective
  set r : Fin N → κ := fun i => x i / x a with hr
  let t2 : Fin (D + 1) × ↥(Finset.univ.erase a) → κ := fun p => t (p.1, p.2.1)
  set T2 : Set κ := insert (x a)⁻¹ (Set.range t2) with hT2
  set S : Set κ := Set.range r ∪ T2 with hS
  have hc : ∀ i : Fin (D + 1), ∑ k, t (i, k) * x k = if i = 0 then 1 else 0 := by
    intro i
    cases i using Fin.cases with
    | zero => simpa using hlin0
    | succ i => simpa [Fin.succ_ne_zero] using hlin i
  have hrS : ∀ k, r k ∈ Algebra.adjoin K S := fun k => Algebra.subset_adjoin (Or.inl ⟨k, rfl⟩)
  have hzS : (x a)⁻¹ ∈ Algebra.adjoin K S := Algebra.subset_adjoin (Or.inr (Set.mem_insert _ _))
  have htS : ∀ i k, k ≠ a → t (i, k) ∈ Algebra.adjoin K S := fun i k hk =>
    Algebra.subset_adjoin (Or.inr (Set.mem_insert_of_mem _
      ⟨(i, ⟨k, Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩⟩), rfl⟩))
  have hmem : ∀ p, t p ∈ Algebra.adjoin K S := by
    rintro ⟨i, k⟩
    by_cases hk : k = a
    · rw [hk]
      have e : t (i, a) = (if i = 0 then 1 else 0) * (x a)⁻¹ - ∑ l ∈ Finset.univ.erase a, t (i, l) * r l := by
        have h := hc i
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)] at h
        rw [← h, add_mul, Finset.sum_mul, add_sub_assoc, ← Finset.sum_sub_distrib]
        simp only [hr, div_eq_mul_inv, mul_assoc, sub_self, Finset.sum_const_zero, add_zero,
          mul_inv_cancel₀ hxa, mul_one]
      rw [e]
      refine Subalgebra.sub_mem _ (Subalgebra.mul_mem _ ?_ hzS)
        (Subalgebra.sum_mem _ fun l hl => Subalgebra.mul_mem _ (htS i l (Finset.ne_of_mem_erase hl)) (hrS l))
      split_ifs
      · exact Subalgebra.one_mem _
      · exact Subalgebra.zero_mem _
    · exact htS i k hk
  let M := AlgebraicIndependent.matroid K κ
  have hI : M.Indep (Set.range t) := AlgebraicIndependent.matroid_indep_iff.mpr ht.to_subtype_range
  have hIS : Set.range t ⊆ M.closure S := by
    rintro _ ⟨p, rfl⟩
    rw [AlgebraicIndependent.matroid_closure_eq]
    exact isAlgebraic_algebraMap (⟨t p, hmem p⟩ : Algebra.adjoin K S)
  have h1 := hI.encard_le_eRk_of_subset hIS
  rw [M.eRk_closure_eq] at h1
  have h2 := M.eRk_union_le_eRk_add_eRk (Set.range r) T2
  have h3 : M.eRk T2 ≤ ((D + 1) * (N - 1) + 1 : ℕ) := by
    refine (M.eRk_le_encard T2).trans ((Set.encard_insert_le _ _).trans ?_)
    have h4 : (Set.range t2).encard ≤ ((D + 1) * (N - 1) : ℕ) := by
      rw [← Set.image_univ]
      refine (Set.encard_image_le _ _).trans ?_
      rw [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_add, Nat.cast_one]
    exact add_le_add h4 le_rfl
  have h5 : (((D + 1) * N : ℕ) : ℕ∞) ≤ (Set.range t).encard := by
    have := ht.injective.encard_range
    rw [ENat.card_eq_coe_fintype_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at this
    exact this.ge
  have hfin : M.eRk (Set.range r) ≠ ⊤ :=
    ne_top_of_le_ne_top (Set.finite_range r).encard_lt_top.ne (M.eRk_le_encard _)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  have hineq : (D + 1) * N ≤ n + ((D + 1) * (N - 1) + 1) := by
    have := h5.trans (h1.trans (h2.trans (add_le_add le_rfl h3)))
    rw [← hn, ← Nat.cast_add, Nat.cast_le] at this
    exact this
  have hN : (D + 1) * N = (D + 1) * (N - 1) + (D + 1) := by
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by have := a.2; omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have hDn : D ≤ n := by
    rw [hN] at hineq
    generalize (D + 1) * (N - 1) = X at hineq
    omega
  obtain ⟨B, hB⟩ := M.exists_isBasis (Set.range r) (Set.subset_univ _)
  have hDB : ((D : ℕ) : ℕ∞) ≤ B.encard := by
    rw [hB.encard_eq_eRk, ← hn]
    exact_mod_cast hDn
  obtain ⟨B', hB'sub, hB'card⟩ := Set.exists_subset_encard_eq hDB
  have hB'fin : B'.Finite := Set.finite_of_encard_eq_coe hB'card
  refine ⟨hB'fin.toFinset, ?_, ?_, ?_⟩
  · have := Set.encard_coe_eq_coe_finsetCard hB'fin.toFinset
    rw [Set.Finite.coe_toFinset, hB'card] at this
    exact_mod_cast this.symm
  · rw [Set.Finite.coe_toFinset]
    exact hB'sub.trans hB.subset
  · rw [Set.Finite.coe_toFinset]
    exact AlgebraicIndependent.matroid_indep_iff.mp (hB.indep.subset hB'sub)

theorem countCore {K κ Ω : Type*} [Field K] [Field κ] [Field Ω] [Algebra K κ] [Algebra K Ω] {N D : ℕ}
    (v : Fin N → Ω) (x : Fin N → κ) (a : Fin N) (hva : v a ≠ 0) (hxa : x a ≠ 0)
    (htr : Algebra.trdeg K (IntermediateField.adjoin K (Set.range fun i => v i / v a)) ≤ D)
    (htrans : ∀ Q : MvPolynomial (Fin N) K, aeval (fun i => v i / v a) Q = 0 → aeval (fun i => x i / x a) Q = 0)
    (t : Fin (D + 1) × Fin N → κ) (ht : AlgebraicIndependent K t)
    (hlin : ∀ i : Fin D, ∑ k, t (i.succ, k) * x k = 0) (hlin0 : ∑ k, t (0, k) * x k = 1)
    (P : MvPolynomial (Fin N) K) {k : ℕ} (hP : P.IsHomogeneous k) (hPv : aeval v P ≠ 0) :
    aeval x P ≠ 0 := by
  classical
  intro hxP
  set ρ : Fin N → Ω := fun i => v i / v a with hρ
  set σ : Fin N → κ := fun i => x i / x a with hσ
  have hα0 : aeval ρ P ≠ 0 := by
    rw [hρ, aeval_div_homog v (v a) hP]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hva)) hPv
  have hσP : aeval σ P = 0 := by
    rw [hσ, aeval_div_homog x (x a) hP, hxP, mul_zero]
  obtain ⟨s, hscard, hsub, hind⟩ := exists_indep_ratios (K := K) x a hxa t ht hlin hlin0
  have hf : ∀ e : s, ∃ i, σ i = (e : κ) := fun e => hsub e.2
  choose f hfe using hf
  have hy : AlgebraicIndependent K (fun e : s => (e : κ)) := hind
  have h3 : (σ ∘ f) = fun e : s => (e : κ) := funext hfe
  have huind : AlgebraicIndependent K (ρ ∘ f) := by
    rw [algebraicIndependent_iff]
    intro Q hQ
    have h1 : aeval ρ (rename f Q) = 0 := by rw [aeval_rename]; exact hQ
    have h2 := htrans (rename f Q) h1
    rw [aeval_rename, h3] at h2
    exact (algebraicIndependent_iff.mp hy) Q h2
  have hρA : ∀ i, ρ i ∈ IntermediateField.adjoin K (Set.range ρ) :=
    fun i => IntermediateField.subset_adjoin K _ ⟨i, rfl⟩
  let ρA : Fin N → IntermediateField.adjoin K (Set.range ρ) := fun i => ⟨ρ i, hρA i⟩
  have hvalρ : ∀ Q : MvPolynomial (Fin N) K,
      IntermediateField.val _ (aeval ρA Q) = aeval ρ Q := by
    intro Q
    induction Q using MvPolynomial.induction_on
    next c =>
      simp only [MvPolynomial.aeval_C, AlgHom.commutes]
    next p q hp hq =>
      rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
    next p i hp =>
      rw [map_mul, map_mul, map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
      rfl
  have hnot : ¬ AlgebraicIndependent K (fun o : Option s => o.elim (aeval ρ P) (ρ ∘ f)) := by
    intro hI
    let w : Option s → IntermediateField.adjoin K (Set.range ρ) :=
      fun o => o.elim (aeval ρA P) (fun e => ρA (f e))
    have hcomp : (IntermediateField.val _) ∘ w = fun o : Option s => o.elim (aeval ρ P) (ρ ∘ f) := by
      funext o
      cases o with
      | none => exact hvalρ P
      | some e => rfl
    have hw : AlgebraicIndependent K w := by
      apply AlgebraicIndependent.of_comp (IntermediateField.val _)
      rw [hcomp]
      exact hI
    have hcard := hw.lift_cardinalMk_le_trdeg.trans (Cardinal.lift_le.mpr htr)
    simp [Cardinal.mk_fintype, Fintype.card_option, hscard] at hcard
  have halg : IsAlgebraic (Algebra.adjoin K (Set.range (ρ ∘ f))) (aeval ρ P) := by
    by_contra hna
    exact hnot ((huind.option_iff_transcendental _).mpr hna)
  set α := aeval ρ P with hαdef
  have hex : ∃ n, ∃ p : Polynomial (Algebra.adjoin K (Set.range (ρ ∘ f))),
      p ≠ 0 ∧ Polynomial.aeval α p = 0 ∧ p.natDegree = n := by
    obtain ⟨p, hp0, hp⟩ := halg
    exact ⟨_, p, hp0, hp, rfl⟩
  obtain ⟨p, hp0, hpα, hpn⟩ := Nat.find_spec hex
  have hc0 : p.coeff 0 ≠ 0 := by
    intro hc
    have hdec : Polynomial.X * p.divX = p := by
      have h0 := Polynomial.X_mul_divX_add p
      rw [hc, map_zero, add_zero] at h0
      exact h0
    have hd0 : p.divX ≠ 0 := by
      intro h
      rw [h, mul_zero] at hdec
      exact hp0 hdec.symm
    have hdα : Polynomial.aeval α p.divX = 0 := by
      have h1 : Polynomial.aeval α p = α * Polynomial.aeval α p.divX := by
        conv_lhs => rw [← hdec]
        rw [map_mul, Polynomial.aeval_X]
      rw [hpα] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_left hα0
    have hdeg : p.divX.natDegree < p.natDegree := by
      rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
      have hn0 : p.natDegree ≠ 0 := by
        intro h0
        rw [Polynomial.eq_C_of_natDegree_eq_zero h0, hc, map_zero] at hp0
        exact hp0 rfl
      omega
    exact Nat.find_min hex (hpn ▸ hdeg) ⟨p.divX, hd0, hdα, rfl⟩
  have hQ : ∀ c : Algebra.adjoin K (Set.range (ρ ∘ f)), ∃ Q : MvPolynomial s K,
      aeval (ρ ∘ f) Q = (c : Ω) := by
    intro c
    have hc : (c : Ω) ∈ (MvPolynomial.aeval (R := K) (ρ ∘ f)).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval]
      exact c.2
    obtain ⟨Q, hQ⟩ := hc
    exact ⟨Q, hQ⟩
  choose Qc hQc using hQ
  have hT : aeval ρ (∑ j ∈ Finset.range (p.natDegree + 1), rename f (Qc (p.coeff j)) * P ^ j) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_mul, map_pow, aeval_rename, hQc]
    rw [← hpα, Polynomial.aeval_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def]
    rfl
  have hT2 := htrans _ hT
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_range_succ'] at hT2
  simp only [map_mul, map_pow, aeval_rename, hσP, ne_eq, Nat.add_eq_zero, one_ne_zero, and_false,
    not_false_eq_true, zero_pow, mul_zero, Finset.sum_const_zero, zero_add, pow_zero, mul_one] at hT2
  rw [h3] at hT2
  have h4 := (algebraicIndependent_iff.mp hy) _ hT2
  have h5 := hQc (p.coeff 0)
  rw [h4, map_zero] at h5
  apply hc0
  apply Subtype.ext
  simpa using h5.symm

end Formalism.L2.Pj.CurveCount
end

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor TensorProduct

namespace CurveLoc

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  (N : ℕ) {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

def fr0 (k : ℕ) (F : X.Forms) (hF : emb X la N F ∈ Vw X la N (addL (wt0 D j) wL k)) : ↥(Frac0 X la w) :=
  ⟨frac X la w k (emb X la N F),
    (Algebra.subset_adjoin (frac_mem_Hfr X la w hF) : frac X la w k (emb X la N F) ∈ Frac0 X la w)⟩

def constF : B.KO →+* ↥(Frac0 X la w) :=
  (algebraMap (Kp X la N) ↥(Frac0 X la w)).comp ((algebraMap (X.Kl la) (Kp X la N)).comp (algebraMap B.KO (X.Kl la)))

theorem emb_inc_mem (i : Fin N) : emb X la N (X.inc wL (w i)) ∈ Vw X la N (addL (wt0 D j) wL 1) := by
  rw [add_zero_weight_one_eq]
  exact emb_mem_Vw X la N wL (w i)

def xw (i : Fin N) : ↥(Frac0 X la w) := fr0 X la N w 1 (X.inc wL (w i)) (emb_inc_mem X la N w i)

def polX (Pw : MvPolynomial (Fin N) B.KO) : ↥(Frac0 X la w) := MvPolynomial.eval₂ (constF X la N w) (xw X la N w) Pw

def secOf (g : Fin N → B.Cusp j wL) : Rp X la N :=
  ∑ k, (@algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N (0, k))) • emb X la N (X.inc wL (g k))

theorem secOf_self : secOf X la N w = Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0 := rfl

theorem secOf_mem (g : Fin N → B.Cusp j wL) : secOf X la N g ∈ Vw X la N wL :=
  Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (emb_mem_Vw X la N wL (g k))

section One

variable {Ω : Type} [CommRing Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)

def psiZ : Ω →+* RZs X la N Ω gF w :=
  (algebraMap (RZ X la N Ω) (RZs X la N Ω gF w)).comp
    ((Algebra.TensorProduct.includeRight : (X.Kl la ⊗[B.KO] Ω) →ₐ[X.Kl la] RZ X la N Ω).toRingHom.comp
      (Algebra.TensorProduct.includeRight : Ω →ₐ[B.KO] X.Kl la ⊗[B.KO] Ω).toRingHom)

theorem psiZ_apply (ω : Ω) : psiZ X la N w gF ω =
    algebraMap (RZ X la N Ω) (RZs X la N Ω gF w) ((1 : Kp X la N) ⊗ₜ[X.Kl la] ((1 : X.Kl la) ⊗ₜ[B.KO] ω)) := rfl

theorem alg_rzMap_emb (F : X.Forms) :
    algebraMap (RZ X la N Ω) (RZs X la N Ω gF w) (rzMap X la N Ω gF (emb X la N F)) = psiZ X la N w gF (gF F) := by
  rw [rzMap_emb]
  rfl

def invS : RZs X la N Ω gF w := lwZ X la N Ω gF w (w0inv X la w)

theorem weight_zero_section_mul_inv :
    algebraMap (RZ X la N Ω) (RZs X la N Ω gF w) (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0)) * invS X la N w gF = 1 := by
  have h := congrArg (lwZ X la N Ω gF w) (section_mul_inverse_eq_one X la w)
  rw [map_mul, lwZ_alg, map_one] at h
  exact h

theorem phiZ_of_eq (x : ↥(Frac0 X la w)) (k : ℕ) (g : Rp X la N) (hx : (x : Lw X la w) = frac X la w k g) :
    phiZ X la N Ω gF w x =
      algebraMap (RZ X la N Ω) (RZs X la N Ω gF w) (rzMap X la N Ω gF g) * invS X la N w gF ^ k := by
  rw [phiZ_apply, hx, frac_apply, map_mul, map_pow, lwZ_alg]
  rfl

theorem phiZ_fraction_base (k : ℕ) (F : X.Forms) (hF : emb X la N F ∈ Vw X la N (addL (wt0 D j) wL k)) :
    phiZ X la N Ω gF w (fr0 X la N w k F hF) = psiZ X la N w gF (gF F) * invS X la N w gF ^ k := by
  rw [phiZ_of_eq X la N w gF _ k _ rfl, alg_rzMap_emb]

theorem phiZ_const (c : B.KO) :
    phiZ X la N Ω gF w (constF X la N w c) = psiZ X la N w gF (algebraMap B.KO Ω c) := by
  rw [constF, RingHom.comp_apply, (phiZ X la N Ω gF w).commutes, psiZ_apply,
    IsScalarTower.algebraMap_apply (Kp X la N) (RZ X la N Ω) (RZs X la N Ω gF w)]
  congr 1
  show (algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) c)) ⊗ₜ[X.Kl la] (1 : X.Kl la ⊗[B.KO] Ω) = _
  rw [Algebra.algebraMap_eq_smul_one (algebraMap B.KO (X.Kl la) c), TensorProduct.smul_tmul,
    Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
    Algebra.algebraMap_eq_smul_one c, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]

theorem phiZ_xw (i : Fin N) :
    phiZ X la N Ω gF w (xw X la N w i) = psiZ X la N w gF (gF (X.inc wL (w i))) * invS X la N w gF := by
  rw [xw, phiZ_fraction_base, pow_one]

theorem phiZ_polX {Pw : MvPolynomial (Fin N) B.KO} {k : ℕ} (hPw : Pw.IsHomogeneous k) :
    phiZ X la N Ω gF w (polX X la N w Pw) =
      invS X la N w gF ^ k * psiZ X la N w gF (MvPolynomial.aeval (fun i => gF (X.inc wL (w i))) Pw) := by
  have h := MvPolynomial.eval₂_comp_left (phiZ X la N Ω gF w).toRingHom (constF X la N w) (xw X la N w) Pw
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
  have hc : (phiZ X la N Ω gF w : ↥(Frac0 X la w) →+* RZs X la N Ω gF w).comp (constF X la N w) =
      (psiZ X la N w gF).comp (algebraMap B.KO Ω) := RingHom.ext fun c => phiZ_const X la N w gF c
  have hx : (⇑(phiZ X la N Ω gF w) ∘ xw X la N w) =
      fun i => invS X la N w gF * psiZ X la N w gF (gF (X.inc wL (w i))) := by
    funext i
    rw [Function.comp_apply, phiZ_xw, mul_comm]
  rw [polX, h, hc, hx, CurveCount.eval₂_mul_homog _ _ _ hPw, MvPolynomial.map_aeval]
  rfl

theorem rzMap_secOf (g g' : Fin N → B.Cusp j wL) (h : ∀ k, gF (X.inc wL (g k)) = gF (X.inc wL (g' k))) :
    rzMap X la N Ω gF (secOf X la N g) = rzMap X la N Ω gF (secOf X la N g') := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [secOf, map_sum, map_smul, rzMap_emb, h]

theorem rzMap_secOf_zero (g : Fin N → B.Cusp j wL) (h : ∀ k, gF (X.inc wL (g k)) = 0) :
    rzMap X la N Ω gF (secOf X la N g) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [secOf, map_sum, map_smul, rzMap_emb, h, TensorProduct.tmul_zero, smul_zero, Finset.sum_const_zero]

end One

section Fam

variable {ι : Type} (Ω : ι → Type) [∀ Z, CommRing (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)] (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)

theorem one_of_split
    (hsplit : ∀ (Z : ι) (k : Fin N), ∃ g : B.Cusp j wL, gF Z (X.inc wL g) = gF Z (X.inc wL (w k)) ∧
      ∀ Z', Z' ≠ Z → gF Z' (X.inc wL g) = 0)
    (𝔮 : Ideal ↥(Frac0 X la w)) (h𝔮 : 𝔮.IsPrime) (Z Z' : ι)
    (hZ : RingHom.ker (phiZ X la N (Ω Z) (gF Z) w) ≤ 𝔮) (hZ' : RingHom.ker (phiZ X la N (Ω Z') (gF Z') w) ≤ 𝔮) :
    Z = Z' := by
  by_contra hne
  choose g hg using hsplit Z
  have hmem : frac X la w 1 (secOf X la N g) ∈ Frac0 X la w :=
    Algebra.subset_adjoin (frac_mem_Hfr X la w (by rw [add_zero_weight_one_eq]; exact secOf_mem X la N g))
  have h1 : (⟨_, hmem⟩ : ↥(Frac0 X la w)) - 1 ∈ 𝔮 := hZ (by
    rw [RingHom.mem_ker, map_sub, map_one, phiZ_of_eq X la N w (gF Z) _ 1 _ rfl,
      rzMap_secOf X la N (gF Z) g w (fun k => (hg k).1), secOf_self, pow_one, weight_zero_section_mul_inv, sub_self])
  have h2 : (⟨_, hmem⟩ : ↥(Frac0 X la w)) ∈ 𝔮 := hZ' (by
    rw [RingHom.mem_ker, phiZ_of_eq X la N w (gF Z') _ 1 _ rfl, rzMap_secOf_zero X la N (gF Z') g (fun k => (hg k).2 Z' (Ne.symm hne)),
      map_zero, zero_mul])
  have h3 := 𝔮.sub_mem h2 h1
  rw [sub_sub_cancel] at h3
  exact h𝔮.ne_top ((Ideal.eq_top_iff_one _).2 h3)

end Fam

section Loc

variable {Ω : Type} [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)

def CountQAt : Prop :=
  ∀ 𝔮 : Ideal ↥(Frac0 X la w), 𝔮.IsPrime → Jid X la w ≤ 𝔮 → RingHom.ker (phiZ X la N Ω gF w) ≤ 𝔮 →
    ∀ (Pw : MvPolynomial (Fin N) B.KO) {k : ℕ}, Pw.IsHomogeneous k →
      MvPolynomial.aeval (fun i => gF (X.inc wL (w i))) Pw ≠ 0 → polX X la N w Pw ∉ 𝔮

def BirAt : Prop :=
  ∀ a : Ω, ∃ (k : ℕ) (g : B.Cusp j (wsmul k wL)) (Pw : MvPolynomial (Fin N) B.KO), Pw.IsHomogeneous k ∧
    MvPolynomial.aeval (fun i => gF (X.inc wL (w i))) Pw ≠ 0 ∧
    a * MvPolynomial.aeval (fun i => gF (X.inc wL (w i))) Pw = gF (X.inc (wsmul k wL) g)

def Den (p : ↥(Frac0 X la w)) : Prop :=
  ∀ 𝔮 : Ideal ↥(Frac0 X la w), 𝔮.IsPrime → Jid X la w ≤ 𝔮 → RingHom.ker (phiZ X la N Ω gF w) ≤ 𝔮 → p ∉ 𝔮

def Good (r : RZs X la N Ω gF w) : Prop :=
  ∃ a p : ↥(Frac0 X la w), Den X la N w gF p ∧ phiZ X la N Ω gF w p * r = phiZ X la N Ω gF w a

theorem den_one : Den X la N w gF 1 := fun _ h𝔮 _ _ h => h𝔮.ne_top ((Ideal.eq_top_iff_one _).2 h)

theorem den_mul {p p' : ↥(Frac0 X la w)} (hp : Den X la N w gF p) (hp' : Den X la N w gF p') :
    Den X la N w gF (p * p') := fun 𝔮 h𝔮 hJ hK h =>
  (h𝔮.mem_or_mem h).elim (hp 𝔮 h𝔮 hJ hK) (hp' 𝔮 h𝔮 hJ hK)

theorem good_phi (f : ↥(Frac0 X la w)) : Good X la N w gF (phiZ X la N Ω gF w f) :=
  ⟨f, 1, den_one X la N w gF, by rw [map_one, one_mul]⟩

theorem good_add {r s : RZs X la N Ω gF w} (hr : Good X la N w gF r) (hs : Good X la N w gF s) :
    Good X la N w gF (r + s) := by
  obtain ⟨a, p, hp, he⟩ := hr
  obtain ⟨a', p', hp', he'⟩ := hs
  refine ⟨p' * a + p * a', p * p', den_mul X la N w gF hp hp', ?_⟩
  rw [map_mul, map_add (f := _), map_mul, map_mul, ← he, ← he']
  ring

theorem good_mul {r s : RZs X la N Ω gF w} (hr : Good X la N w gF r) (hs : Good X la N w gF s) :
    Good X la N w gF (r * s) := by
  obtain ⟨a, p, hp, he⟩ := hr
  obtain ⟨a', p', hp', he'⟩ := hs
  refine ⟨a * a', p * p', den_mul X la N w gF hp hp', ?_⟩
  rw [map_mul, map_mul, ← he, ← he']
  ring

theorem good_pow {r : RZs X la N Ω gF w} (hr : Good X la N w gF r) (n : ℕ) : Good X la N w gF (r ^ n) := by
  induction n with
  | zero => rw [pow_zero]; simpa using good_phi X la N w gF 1
  | succ n ih => rw [pow_succ]; exact good_mul X la N w gF ih hr

theorem good_smul (c : Kp X la N) {r : RZs X la N Ω gF w} (hr : Good X la N w gF r) : Good X la N w gF (c • r) := by
  rw [Algebra.smul_def, ← (phiZ X la N Ω gF w).commutes c]
  exact good_mul X la N w gF (good_phi X la N w gF _) hr

theorem good_psi (hB : BirAt X N w gF) (hC : CountQAt X la N w gF) (ω : Ω) :
    Good X la N w gF (psiZ X la N w gF ω) := by
  obtain ⟨k, g, Pw, hPw, hne, he⟩ := hB ω
  have hG : emb X la N (X.inc (wsmul k wL) g) ∈ Vw X la N (addL (wt0 D j) wL k) := by
    rw [addL, zero_weight_add]
    exact emb_mem_Vw X la N _ g
  refine ⟨fr0 X la N w k _ hG, polX X la N w Pw, fun 𝔮 h𝔮 hJ hK => hC 𝔮 h𝔮 hJ hK Pw hPw hne, ?_⟩
  rw [phiZ_polX X la N w gF hPw, phiZ_fraction_base, ← he, map_mul]
  ring

theorem good_invS (hB : BirAt X N w gF) (hC : CountQAt X la N w gF) (k0 : Fin N)
    (hk0 : gF (X.inc wL (w k0)) ≠ 0) : Good X la N w gF (invS X la N w gF) := by
  have h1 : emb X la N (X.inc wL (w k0)) ∈ Vw X la N (addL (wt0 D j) wL 1) := by
    rw [add_zero_weight_one_eq]; exact emb_mem_Vw X la N wL (w k0)
  have e : invS X la N w gF =
      phiZ X la N Ω gF w (fr0 X la N w 1 _ h1) * psiZ X la N w gF (gF (X.inc wL (w k0)))⁻¹ := by
    rw [phiZ_fraction_base, pow_one, mul_right_comm, ← map_mul, mul_inv_cancel₀ hk0, map_one, one_mul]
  rw [e]
  exact good_mul X la N w gF (good_phi X la N w gF _) (good_psi X la N w gF hB hC _)

theorem tmul_eq (κ : Kp X la N) (l : X.Kl la) (ω : Ω) :
    (κ ⊗ₜ[X.Kl la] (l ⊗ₜ[B.KO] ω) : RZ X la N Ω) =
      (κ * algebraMap (X.Kl la) (Kp X la N) l) • ((1 : Kp X la N) ⊗ₜ[X.Kl la] ((1 : X.Kl la) ⊗ₜ[B.KO] ω)) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have h : (l ⊗ₜ[B.KO] ω : X.Kl la ⊗[B.KO] Ω) = l • ((1 : X.Kl la) ⊗ₜ[B.KO] ω) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm]

theorem loc_of_bir (hB : BirAt X N w gF) (hC : CountQAt X la N w gF) (r : RZs X la N Ω gF w) :
    ∃ a p : ↥(Frac0 X la w), (∀ 𝔮 : Ideal ↥(Frac0 X la w), 𝔮.IsPrime → Jid X la w ≤ 𝔮 →
      RingHom.ker (phiZ X la N Ω gF w) ≤ 𝔮 → p ∉ 𝔮) ∧ phiZ X la N Ω gF w p * r = phiZ X la N Ω gF w a := by
  by_cases hk : ∃ k, gF (X.inc wL (w k)) ≠ 0
  · obtain ⟨k0, hk0⟩ := hk
    have hRZ : ∀ x : RZ X la N Ω, Good X la N w gF (algebraMap (RZ X la N Ω) (RZs X la N Ω gF w) x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => rw [map_zero]; simpa using good_phi X la N w gF 0
      | tmul κ v =>
        induction v using TensorProduct.induction_on with
        | zero => rw [TensorProduct.tmul_zero, map_zero]; simpa using good_phi X la N w gF 0
        | tmul l ω =>
          rw [tmul_eq, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def]
          exact good_smul X la N w gF _ (good_psi X la N w gF hB hC ω)
        | add v₁ v₂ h₁ h₂ => rw [TensorProduct.tmul_add, map_add (f := _)]; exact good_add X la N w gF h₁ h₂
      | add x y hx hy => rw [map_add (f := _)]; exact good_add X la N w gF hx hy
    obtain ⟨⟨x, y⟩, hr⟩ :=
      IsLocalization.mk'_surjective (Submonoid.powers (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0))) r
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp y.2
    have e : r = algebraMap (RZ X la N Ω) (RZs X la N Ω gF w) x * invS X la N w gF ^ n := by
      rw [← hr]
      show IsLocalization.mk' (RZs X la N Ω gF w) x y = _
      rw [IsLocalization.mk'_eq_iff_eq_mul, ← hn, map_pow, mul_assoc, ← mul_pow, mul_comm (invS X la N w gF),
        weight_zero_section_mul_inv, one_pow, mul_one]
    rw [e]
    obtain ⟨a, p, hp, he⟩ :=
      good_mul X la N w gF (hRZ x) (good_pow X la N w gF (good_invS X la N w gF hB hC k0 hk0) n)
    exact ⟨a, p, hp, he⟩
  · push Not at hk
    have hz : rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0) = 0 := rzMap_secOf_zero X la N gF w hk
    have h2 : algebraMap (RZ X la N Ω) (RZs X la N Ω gF w) (rzMap X la N Ω gF (Formalism.MainNotions.Gaps.EtaleWeightGaps.sec X la w 0)) = 0 :=
      (congrArg (algebraMap (RZ X la N Ω) (RZs X la N Ω gF w)) hz).trans (map_zero _)
    have h0 : (1 : RZs X la N Ω gF w) = 0 := by
      rw [← weight_zero_section_mul_inv X la N w gF, h2, zero_mul]
    have := subsingleton_of_zero_eq_one h0.symm
    exact ⟨0, 1, den_one X la N w gF, Subsingleton.elim _ _⟩

end Loc

end CurveLoc

end Formalism.L2.Pj
