module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodE

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodG
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodC
namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

theorem succ_le_ringKrullDim_of_algebraicIndependent {σ : Type} [Finite σ]
    (P : Ideal (MvPolynomial σ ℤ)) (hP : P.IsPrime)
    (hH : P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥) {n : ℕ}
    (x : Fin n → MvPolynomial σ ℚ ⧸ qIdeal P) (hx : AlgebraicIndependent ℚ x) :
    ((n + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial σ ℤ ⧸ P) := by
  have hdom := isDomain_qQuot P hP hH
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg ℚ (MvPolynomial σ ℚ ⧸ qIdeal P)
  have hns : n ≤ s := by
    set S := Algebra.adjoin ℚ (Set.range (g ∘ X))
    have hmem : ∀ y, g y ∈ S := by
      intro y
      show g y ∈ Algebra.adjoin ℚ (Set.range (g ∘ X))
      rw [Algebra.adjoin_range_eq_range_aeval]
      refine ⟨y, ?_⟩
      show aeval (g ∘ X) y = g y
      rw [← MvPolynomial.aeval_unique g]
    let g' : MvPolynomial (Fin s) ℚ →+* S := g.toRingHom.codRestrict S.toSubsemiring hmem
    have hg' : (algebraMap S (MvPolynomial σ ℚ ⧸ qIdeal P)).comp g' = g.toRingHom := by
      ext y <;> rfl
    have halg : Algebra.IsAlgebraic S (MvPolynomial σ ℚ ⧸ qIdeal P) := by
      refine ⟨fun b => ?_⟩
      obtain ⟨p, hpm, hp⟩ := hint b
      refine IsIntegral.isAlgebraic ⟨p.map g', hpm.map g', ?_⟩
      rw [Polynomial.eval₂_map, hg']
      exact hp
    have h1 := hx.cardinalMk_le_trdeg
    have h2 := Algebra.IsAlgebraic.trdeg_le_cardinalMk ℚ (Set.range (g ∘ X))
    have h3 := Cardinal.mk_range_le (f := g ∘ X)
    have := h1.trans (h2.trans h3)
    simpa using this
  have hdim : (s : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial σ ℚ ⧸ qIdeal P) := by
    refine le_ringKrullDim_of_isIntegral g.toRingHom hint hinj s ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  letI := (ratHom P).toAlgebra
  haveI := ratHom_isLocalization P
  refine succ_le_ringKrullDim_of_isLocalization
    (Algebra.algebraMapSubmonoid (MvPolynomial σ ℤ ⧸ P) (nonZeroDivisors ℤ)) ?_ n
    (le_trans (by exact_mod_cast hns) hdim)
  intro p hp hdis
  refine exists_gt_of_comap_int_eq_bot (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective p hp ?_
  ext m
  simp only [Ideal.mem_comap, RingHom.coe_comp, Function.comp_apply, Submodule.mem_bot]
  constructor
  · intro hm
    by_contra hm0
    refine Set.disjoint_left.mp hdis ⟨m, mem_nonZeroDivisors_of_ne_zero hm0, rfl⟩ ?_
    simpa [eq_intCast] using hm
  · rintro rfl
    simp

end ReciprocityTheory.ChartRestriction.G.Geo
end

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def segQ (P : Ideal (MRing ι)) (i : (k : K) → ι k) : MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal P :=
  Ideal.Quotient.mk _ (segMon i)

private lemma rename_inl_aeval_mul_prod_X_inr_pow_eq_of_support {r : ℕ} {S : Type} [Fintype S] (c : S → ℕ)
    (H : MvPolynomial (Fin r ⊕ S) ℚ) (hc : ∀ m ∈ H.support, ∀ s, m (Sum.inr s) = c s) :
    rename Sum.inl (aeval (Sum.elim (X : Fin r → MvPolynomial (Fin r) ℚ) 1) H) *
      ∏ s, (X (Sum.inr s) : MvPolynomial (Fin r ⊕ S) ℚ) ^ c s = H := by
  classical
  conv_rhs => rw [H.as_sum]
  conv_lhs => rw [H.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type]
  simp only [map_mul, map_prod, map_pow, aeval_C, aeval_X, Sum.elim_inl, Sum.elim_inr,
    Pi.one_apply, one_pow, Finset.prod_const_one, mul_one, rename_C, rename_X, algebraMap_eq,
    hc m hm, mul_assoc]

private lemma aeval_sumElim_one_eq_aeval_aeval_sumElim_X_one {r : ℕ} {S : Type} {B : Type*} [CommRing B] [Algebra ℚ B]
    (a : Fin r → B) (H : MvPolynomial (Fin r ⊕ S) ℚ) :
    aeval (Sum.elim a 1) H = aeval a (aeval (Sum.elim (X : Fin r → MvPolynomial (Fin r) ℚ) 1) H) := by
  have hf : (fun i : Fin r ⊕ S => aeval a (Sum.elim (X : Fin r → MvPolynomial (Fin r) ℚ) 1 i)) =
      Sum.elim a (1 : S → B) := by
    funext i
    cases i <;> simp
  rw [← AlgHom.comp_apply, comp_aeval, hf]

theorem algebraicIndependent_sumElim (P : Ideal (MRing ι)) (hP : P.IsPrime) (hH : IsHorizontal P)
    (hhom : IsMultiHomogIdeal P) (k0 : K) (i0 : (k : K) → ι k)
    (hi0 : ∀ k, (X ⟨k, i0 k⟩ : MRing ι) ∉ P) {r : ℕ} (L : Fin r → ((k : K) → ι k) → ℚ)
    (hind : AlgebraicIndependent ℚ (forms (segQ P) L)) :
    AlgebraicIndependent ℚ (Sum.elim (forms (segQ P) L)
      (fun k' : {k // k ≠ k0} => Ideal.Quotient.mk (qIdeal P) (X ⟨k'.1, i0 k'.1⟩))) := by
  classical
  have : IsDomain (MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal P) := isDomain_qQuot P hP hH
  set b : {k // k ≠ k0} → MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal P :=
    fun k' => Ideal.Quotient.mk (qIdeal P) (X ⟨k'.1, i0 k'.1⟩) with hbdef
  let yt : Fin r ⊕ {k // k ≠ k0} → MvPolynomial (Σ k, ι k) ℚ :=
    Sum.elim (fun j => ∑ t, L j t • segMon t) (fun k' => X ⟨k'.1, i0 k'.1⟩)
  have hyt : (fun e => Ideal.Quotient.mkₐ ℚ (qIdeal P) (yt e)) = Sum.elim (forms (segQ P) L) b := by
    funext e
    cases e with
    | inl j => simp [yt, forms, segQ, map_sum, Ideal.Quotient.mkₐ_eq_mk]
    | inr k' => simp [yt, b, Ideal.Quotient.mkₐ_eq_mk]
  have hhomY : ∀ e, IsWeightedHomogeneous (blkWt (ι := ι)) (yt e) (sWt k0 r e) := by
    rintro (j | k')
    · have hmem : (∑ t, L j t • segMon t) ∈
          weightedHomogeneousSubmodule ℚ (blkWt (ι := ι)) oneK :=
        Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (segMon_isWeightedHomogeneous t)
      exact hmem
    · exact isWeightedHomogeneous_X ℚ (blkWt (ι := ι)) ⟨k'.1, i0 k'.1⟩
  have hb : ∀ k', b k' ≠ 0 := by
    intro k' h
    rw [hbdef, Ideal.Quotient.eq_zero_iff_mem] at h
    exact hi0 k'.1 (mem_of_qmap_mem_qIdeal P hP hH (by simpa using h))
  have hev : ∀ G, aeval (Sum.elim (forms (segQ P) L) b) G =
      Ideal.Quotient.mk (qIdeal P) (aeval (R := ℚ) yt G) := by
    intro G
    rw [← hyt, ← comp_aeval, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [algebraicIndependent_iff]
  intro H hH0
  have hmem : aeval (R := ℚ) yt H ∈ qIdeal P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hev]
    exact hH0
  have key : ∀ δ, weightedHomogeneousComponent (sWt k0 r) δ H = 0 := by
    intro δ
    have hHd : IsWeightedHomogeneous (sWt k0 r) (weightedHomogeneousComponent (sWt k0 r) δ H) δ :=
      weightedHomogeneousComponent_isWeightedHomogeneous _ _
    have hcomp := weightedHomogeneousComponent_mem_of_mem ℚ (blkWt (ι := ι))
      (qIdeal_isHomogeneous P hhom) hmem δ
    rw [component_aeval (sWt k0 r) yt hhomY H δ] at hcomp
    have h0 : aeval (Sum.elim (forms (segQ P) L) b) (weightedHomogeneousComponent (sWt k0 r) δ H) = 0 := by
      rw [hev, Ideal.Quotient.eq_zero_iff_mem]
      exact hcomp
    by_contra hne
    obtain ⟨n0, hn0⟩ := Finset.nonempty_of_ne_empty (mt MvPolynomial.support_eq_empty.mp hne)
    rw [aeval_sumElim_factor k0 hHd hn0] at h0
    have hprod : (∏ k', b k' ^ n0 (Sum.inr k')) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k' _ => pow_ne_zero _ (hb k')
    have h1 := (mul_eq_zero.mp h0).resolve_left hprod
    rw [aeval_sumElim_one_eq_aeval_aeval_sumElim_X_one] at h1
    have h2 := algebraicIndependent_iff.mp hind _ h1
    apply hne
    rw [← rename_inl_aeval_mul_prod_X_inr_pow_eq_of_support (fun s => n0 (Sum.inr s))
      (weightedHomogeneousComponent (sWt k0 r) δ H) ?_, h2, map_zero, zero_mul]
    intro m hm s
    exact inr_eq_of_weight_eq k0 ((hHd (mem_support_iff.mp hm)).trans
      (hHd (mem_support_iff.mp hn0)).symm) s
  ext n
  have := congrArg (AddMonoidAlgebra.coeff · n) (key (Finsupp.weight (sWt k0 r) n))
  rw [coeff_weightedHomogeneousComponent, if_pos rfl] at this
  simpa using this

theorem forms_not_algebraicIndependent (P : Ideal (MRing ι)) (e : ℕ) (hP : IsArithVar P (e + 1))
    {r : ℕ} (hr : e + 1 < r) (L : Fin r → ((k : K) → ι k) → ℚ) :
    ¬ AlgebraicIndependent ℚ (forms (segQ P) L) := by
  classical
  intro hind
  obtain ⟨hne, ⟨hprime, hhom, hrel⟩, hH, hdim⟩ := hP
  obtain ⟨k0⟩ := hne
  choose i0 hi0 using hrel
  have hall := algebraicIndependent_sumElim P hprime hH hhom k0 i0 hi0 L hind
  set n := Fintype.card (Fin r ⊕ {k // k ≠ k0})
  have hall' := hall.comp _ (Fintype.equivFin (Fin r ⊕ {k // k ≠ k0})).symm.injective
  have hle := succ_le_ringKrullDim_of_algebraicIndependent P hprime hH _ hall'
  rw [hdim] at hle
  have hle' : n + 1 ≤ e + 1 + Fintype.card K := by exact_mod_cast hle
  have hcard : n + 1 = r + Fintype.card K := by
    have h1 : Fintype.card {k // k ≠ k0} = Fintype.card K - 1 := by
      simp [Fintype.card_subtype_compl]
    have h2 : 0 < Fintype.card K := Fintype.card_pos_iff.mpr ⟨k0⟩
    simp only [n, Fintype.card_sum, Fintype.card_fin, h1]
    omega
  omega

end

end ReciprocityTheory.ChartRestriction.G.Geo
end

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

noncomputable section

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def scaleBlock (k0 : K) (c : ℂ) (z : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun p => (if p.1 = k0 then c else 1) * z p

theorem eval_scaleBlock (k0 : K) (c : ℂ) (z : (Σ k, ι k) → ℂ) (f : MRing ι) (a : K → ℕ)
    (hf : IsMultiHomog f a) :
    eval (scaleBlock k0 c z) (map (Int.castRingHom ℂ) f) =
      c ^ a k0 * eval z (map (Int.castRingHom ℂ) f) := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m ∈ f.support := MvPolynomial.support_map_subset _ _ hm
  have hdeg := hf m hm' k0
  simp only [scaleBlock, mul_pow, Finset.prod_mul_distrib]
  have hc : ∏ x : (Σ k, ι k), (if x.1 = k0 then c else 1) ^ m x = c ^ a k0 := by
    rw [Fintype.prod_sigma, Finset.prod_eq_single k0]
    · simp [hdeg, Finset.prod_pow_eq_pow_sum]
    · intro k _ hk
      simp [hk]
    · simp
  rw [hc]
  ring

theorem scaleBlock_mem_zeroLocus (P : Ideal (MRing ι)) (hP : IsMultiHomogIdeal P) (k0 : K) {c : ℂ} (hc : c ≠ 0)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : scaleBlock k0 c z ∈ mcPts P := by
  obtain ⟨S, hS, rfl⟩ := hP
  show (∀ k, ∃ i, scaleBlock k0 c z ⟨k, i⟩ ≠ 0) ∧
    ∀ f ∈ Ideal.span S, eval (scaleBlock k0 c z) (map (Int.castRingHom ℂ) f) = 0
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    refine ⟨i, ?_⟩
    simp only [scaleBlock]
    split_ifs <;> simp [hc, hi]
  · have hle : Ideal.span S ≤ RingHom.ker ((eval (scaleBlock k0 c z)).comp (map (Int.castRingHom ℂ))) := by
      rw [Ideal.span_le]
      intro s hs
      obtain ⟨a, ha⟩ := hS s hs
      simp only [SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply]
      rw [eval_scaleBlock k0 c z s a ha, hz.2 s (Ideal.subset_span hs), mul_zero]
    exact (RingHom.mem_ker).mp (hle hf)

def evQ (P : Ideal (MRing ι)) (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P) :
    MvPolynomial (Σ k, ι k) ℚ ⧸ qIdeal P →+* ℂ :=
  Ideal.Quotient.lift (qIdeal P) (eval₂Hom (algebraMap ℚ ℂ) z) fun a ha => by
    have hle : qIdeal P ≤ RingHom.ker (eval₂Hom (algebraMap ℚ ℂ) z) := by
      refine Ideal.map_le_iff_le_comap.mpr fun f hf => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker, coe_eval₂Hom, eval₂_map]
      have h := hz.2 f hf
      rw [eval_map] at h
      convert h using 2
      exact RingHom.ext_int _ _
    exact hle ha

theorem evQ_mk (P : Ideal (MRing ι)) (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P)
    (q : MvPolynomial (Σ k, ι k) ℚ) :
    evQ P z hz (Ideal.Quotient.mk _ q) = eval₂ (algebraMap ℚ ℂ) z q := rfl

theorem goodProjExists : GoodProjExistsStatement := by
  intro K _ ι _ P e hP
  classical
  obtain ⟨r, hr, L, hL⟩ := exists_linear_normalization (k := ℚ) (segQ P) (e + 1)
    (fun r L hr => forms_not_algebraicIndependent P e hP hr L)
  have hint : ∀ t, ∃ p : Polynomial (MvPolynomial (Fin r) ℚ), p.Monic ∧
      Polynomial.eval₂ (aeval (forms (segQ P) L)).toRingHom (segQ P t) p = 0 := hL
  choose p hpm hpe using hint
  let Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ) :=
    { toFun := fun w j => if h : j.val < r then ∑ t, algebraMap ℚ ℂ (L ⟨j.val, h⟩ t) * w t else 0
      map_add' := by
        intro w w'
        funext j
        simp only [Pi.add_apply]
        split_ifs <;> simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a w
        funext j
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        split_ifs <;> simp [Finset.mul_sum, mul_left_comm] }
  have hΨ : ∀ w (j : Fin r), Ψ w ⟨j.1, lt_of_lt_of_le j.2 hr⟩ = ∑ t, algebraMap ℚ ℂ (L j t) * w t := by
    intro w j
    simp only [Ψ, LinearMap.coe_mk, AddHom.coe_mk, dif_pos j.2, Fin.eta]
  have hA : ∀ z' (hz' : z' ∈ mcPts P), Ψ (segre z') = 0 →
      ∀ t, ((p t).map ((algebraMap ℚ ℂ).comp MvPolynomial.constantCoeff)).IsRoot (segre z' t) := by
    intro z' hz' h0 t
    have hφs : ∀ t', evQ P z' hz' (segQ P t') = segre z' t' := by
      intro t'
      show evQ P z' hz' (Ideal.Quotient.mk _ (segMon t')) = _
      rw [evQ_mk]
      simp [segMon, segre, eval₂_prod]
    have hφf : ∀ j, evQ P z' hz' (forms (segQ P) L j) = 0 := by
      intro j
      have h1 := congrFun h0 ⟨j.1, lt_of_lt_of_le j.2 hr⟩
      rw [hΨ] at h1
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [forms, map_sum, Algebra.smul_def, map_mul, RingHom.map_rat_algebraMap, hφs]
      simpa using h1
    have hcomp : (evQ P z' hz').comp (aeval (forms (segQ P) L)).toRingHom =
        (algebraMap ℚ ℂ).comp MvPolynomial.constantCoeff := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [RingHom.map_rat_algebraMap]
      · intro j
        simp [hφf]
    show Polynomial.eval (segre z' t) ((p t).map ((algebraMap ℚ ℂ).comp MvPolynomial.constantCoeff)) = 0
    rw [Polynomial.eval_map, ← hcomp, ← hφs, ← Polynomial.hom_eval₂, hpe t, map_zero]
  refine ⟨Ψ, fun z hz h0 => ?_⟩
  obtain ⟨k0⟩ := hP.1
  have hhom : IsMultiHomogIdeal P := hP.2.1.2.1
  choose t0 ht0 using hz.1
  have hs : segre z t0 ≠ 0 := by
    simp only [segre]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => ht0 k
  have hsegA : ∀ c : ℂ, segre (scaleBlock k0 c z) = c • segre z := by
    intro c
    funext t
    simp only [segre, scaleBlock, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_ite_eq' Finset.univ k0 (fun _ => c)]
    simp
  have hroot : ∀ n : ℕ, ((p t0).map ((algebraMap ℚ ℂ).comp MvPolynomial.constantCoeff)).IsRoot
      (((n : ℂ) + 1) * segre z t0) := by
    intro n
    have hcn : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    have hmem : scaleBlock k0 ((n : ℂ) + 1) z ∈ mcPts P := scaleBlock_mem_zeroLocus P hhom k0 hcn hz
    have h0' : Ψ (segre (scaleBlock k0 ((n : ℂ) + 1) z)) = 0 := by
      rw [hsegA, map_smul, h0, smul_zero]
    have h5 := hA (scaleBlock k0 ((n : ℂ) + 1) z) hmem h0' t0
    have h7 : segre (scaleBlock k0 ((n : ℂ) + 1) z) t0 = ((n : ℂ) + 1) * segre z t0 := by
      rw [hsegA, Pi.smul_apply, smul_eq_mul]
    rw [h7] at h5
    exact h5
  have hinf := Set.infinite_of_injective_forall_mem
    (s := {x | ((p t0).map ((algebraMap ℚ ℂ).comp MvPolynomial.constantCoeff)).IsRoot x})
    (f := fun n : ℕ => ((n : ℂ) + 1) * segre z t0)
    (by
      intro a b hab
      simp only at hab
      have h6 := mul_right_cancel₀ hs hab
      exact_mod_cast add_right_cancel h6) hroot
  exact hinf (Polynomial.finite_setOf_isRoot ((hpm t0).map _).ne_zero)

end

end ReciprocityTheory.ChartRestriction.G.Geo
