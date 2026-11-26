module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterPCProof
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeI

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeO
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory

def NormPolyStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (f : MRing ι) (a : K → ℕ),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → IsMultiHomog f a → f ∉ P →
    ∃ (c : MvPolynomial (Fin (e + 1)) ℂ) (m : ℕ), c ≠ 0 ∧ c.IsHomogeneous m ∧
      ∀ z ∈ mcPts P, eval z (map (Int.castRingHom ℂ) f) = 0 → eval (Ψ (segre z)) c = 0

theorem eval_smul_of_isHomogeneous {n : ℕ} {c : MvPolynomial (Fin n) ℂ} {m : ℕ}
    (hc : c.IsHomogeneous m) (t : ℂ) (v : Fin n → ℂ) :
    eval (fun i => t * v i) c = t ^ m * eval v c := by
  conv_lhs => rw [c.as_sum]
  conv_rhs => rw [c.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.mul_sum, eval_monomial]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = m := by
    have h1 := hc (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h1
  simp only [mul_pow, Finsupp.prod_mul]
  rw [show (d.prod fun _ e => t ^ e) = t ^ m by
    rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, hdeg]]
  ring

theorem exists_eval_cons_ne_zero {n : ℕ} {c : MvPolynomial (Fin (n + 1)) ℂ} {m : ℕ}
    (hc0 : c ≠ 0) (hc : c.IsHomogeneous m) : ∃ y : Fin n → ℂ, eval (Fin.cons 1 y) c ≠ 0 := by
  by_contra h
  push Not at h
  apply hc0
  have hX : (X 0 : MvPolynomial (Fin (n + 1)) ℂ) * c = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, eval_X, map_zero]
    by_cases hx : x 0 = 0
    · rw [hx, zero_mul]
    · have hxe : x = fun i => x 0 * (Fin.cons 1 (fun j => x j.succ / x 0) : Fin (n + 1) → ℂ) i := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp
        · rw [Fin.cons_succ, mul_div_left_comm, div_self hx, mul_one]
      have hx0 : eval x c = 0 := by
        rw [hxe, eval_smul_of_isHomogeneous hc (x 0) (Fin.cons 1 (fun j => x j.succ / x 0)), h,
          mul_zero]
      rw [hx0, mul_zero]
  rcases mul_eq_zero.mp hX with h0 | h0
  · exact absurd h0 (X_ne_zero 0)
  · exact h0

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}

private theorem volume_eval_eq_zero_lemma :
    ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℂ), p ≠ 0 → volume {y : Fin n → ℂ | eval y p = 0} = 0 := by
  intro n
  induction n with
  | zero =>
    intro p hp
    refine measure_mono_null (fun y hy => ?_) measure_empty
    exfalso
    apply hp
    apply MvPolynomial.funext
    intro x
    have hxy : x = y := Subsingleton.elim _ _
    subst hxy
    simpa using hy
  | succ n ih =>
    intro p hp
    have hq0 : finSuccEquiv ℂ n p ≠ 0 := by
      intro h
      apply hp
      apply (finSuccEquiv ℂ n).injective
      rw [h, map_zero]
    have hbad := ih _ (Polynomial.leadingCoeff_ne_zero.mpr hq0)
    let E := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0
    have hE : MeasurePreserving E (Measure.pi fun _ => (volume : Measure ℂ))
        ((volume : Measure ℂ).prod (Measure.pi fun _ : Fin n => (volume : Measure ℂ))) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure ℂ)) 0
    have hC : MeasurableSet {y : Fin (n + 1) → ℂ | eval y p = 0} :=
      (isClosed_eq (MvPolynomial.continuous_eval p) continuous_const).measurableSet
    have hT : MeasurableSet (E.symm ⁻¹' {y : Fin (n + 1) → ℂ | eval y p = 0}) :=
      E.symm.measurable hC
    have hS : {y : Fin (n + 1) → ℂ | eval y p = 0} =
        E ⁻¹' (E.symm ⁻¹' {y : Fin (n + 1) → ℂ | eval y p = 0}) := by
      ext x
      simp only [Set.mem_preimage, MeasurableEquiv.symm_apply_apply]
    show (Measure.pi fun _ => (volume : Measure ℂ)) _ = 0
    rw [hS, hE.measure_preimage_equiv, Measure.prod_apply_symm hT]
    have hae : ∀ᵐ s ∂(Measure.pi fun _ : Fin n => (volume : Measure ℂ)),
        eval s (finSuccEquiv ℂ n p).leadingCoeff ≠ 0 :=
      ae_iff.2 (by
        have hbad' : (Measure.pi fun _ : Fin n => (volume : Measure ℂ))
            {y | eval y (finSuccEquiv ℂ n p).leadingCoeff = 0} = 0 := hbad
        simpa using hbad')
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hae] with s hs
    have hmap : (finSuccEquiv ℂ n p).map (eval s) ≠ 0 := by
      intro h0
      apply hs
      have h1 := congrArg (fun (r : Polynomial ℂ) => r.coeff (finSuccEquiv ℂ n p).natDegree) h0
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h1
      exact h1
    refine Set.Finite.measure_zero
      ((((finSuccEquiv ℂ n p).map (eval s)).roots.toFinset.finite_toSet).subset ?_) _
    intro y hy
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hy
    have hcons : E.symm (y, s) = Fin.cons y s := by
      simp [E]
    rw [hcons, eval_eq_eval_mv_eval'] at hy
    simpa [Polynomial.mem_roots hmap] using hy

theorem projB_null_of (hN : NormPolyStatement)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (hJ : IsMultiHomogIdeal J) (hJP : ¬ J ≤ P) :
    volume {y : Fin e → ℂ | ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y} = 0 := by
  obtain ⟨S, hS, rfl⟩ := hJ
  obtain ⟨f, hfS, hfP⟩ : ∃ f ∈ S, f ∉ P := by
    by_contra h
    push Not at h
    exact hJP (Ideal.span_le.2 h)
  obtain ⟨a, ha⟩ := hS f hfS
  obtain ⟨c, m, hc0, hc, hz⟩ := hN K ι P e Ψ f a hP hΨ ha hfP
  have key : ∀ y : Fin e → ℂ,
      eval y (Polynomial.eval 1 (finSuccEquiv ℂ e c)) = eval (Fin.cons 1 y) c := by
    intro y
    rw [eval_eq_eval_mv_eval', Polynomial.eval_map, Polynomial.eval₂_at_one]
  have hp0 : Polynomial.eval 1 (finSuccEquiv ℂ e c) ≠ 0 := by
    obtain ⟨y, hy⟩ := exists_eval_cons_ne_zero hc0 hc
    intro h0
    apply hy
    rw [← key, h0, map_zero]
  refine measure_mono_null ?_ (volume_eval_eq_zero_lemma e _ hp0)
  rintro y ⟨z, hzP, hzJ, hzy⟩
  have hzJ' : (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧
      ∀ g ∈ Ideal.span S, eval z (map (Int.castRingHom ℂ) g) = 0 := hzJ
  show eval y (Polynomial.eval 1 (finSuccEquiv ℂ e c)) = 0
  rw [key, ← hzy]
  exact hz z hzP (hzJ'.2 f (Ideal.subset_span hfS))

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeQ
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeP
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}


set_option maxHeartbeats 1600000 in
theorem exists_monic_rel (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (P : Ideal (MRing ι)) (hPh : IsMultiHomogIdeal P) (hΨ : IsGoodProj P Ψ)
    (F : MvPolynomial ((k : K) → ι k) ℂ) :
    ∃ (n : ℕ) (c : ℕ → MvPolynomial (Fin (e + 1)) ℂ), c n = 1 ∧
      ∀ z ∈ mcPts P, ∑ i ∈ Finset.range (n + 1),
        eval (Ψ (segre z)) (c i) * eval (segre z) F ^ i = 0 := by
  classical
  have hrel := fun i => segre_rel hPh Ψ hΨ i
  choose r hr G hG hrelz using hrel
  let R := MvPolynomial (Fin (e + 1)) ℂ
  let Z := ↥(mcPts P)
  let φw : MvPolynomial ((k : K) → ι k) ℂ →+* (Z → ℂ) :=
    Pi.ringHom fun z : Z => MvPolynomial.eval (segre z.1)
  let φy : R →+* (Z → ℂ) := Pi.ringHom fun z : Z => MvPolynomial.eval (Ψ (segre z.1))
  letI : Algebra R (Z → ℂ) := φy.toAlgebra
  have hsmul : ∀ (c : R) (x : Z → ℂ), c • x = φy c * x := fun c x => Algebra.smul_def c x
  let T : Finset (((k : K) → ι k) →₀ ℕ) :=
    (Fintype.piFinset fun i => Finset.range (r i)).image Finsupp.equivFunOnFinite.symm
  have memT : ∀ s : ((k : K) → ι k) →₀ ℕ, (∀ i, s i < r i) → s ∈ T := fun s hs =>
    Finset.mem_image.2 ⟨⇑s, Fintype.mem_piFinset.2 fun i => Finset.mem_range.2 (hs i),
      Finsupp.equivFunOnFinite_symm_coe s⟩
  let N : Submodule R (Z → ℂ) :=
    Submodule.span R (↑(T.image fun s => φw (monomial s 1)) : Set (Z → ℂ))
  have hC : ∀ (a : ℂ) (x : Z → ℂ), x ∈ N → φw (C a) * x ∈ N := by
    intro a x hx
    have e1 : φw (C a) = φy (C a) := by
      funext z
      show MvPolynomial.eval (segre z.1) (C a) = MvPolynomial.eval (Ψ (segre z.1)) (C a)
      rw [eval_C, eval_C]
    rw [e1, ← hsmul]
    exact N.smul_mem _ hx
  have hY : ∀ (j : Fin (e + 1)) (x : Z → ℂ), x ∈ N → φy (X j) * x ∈ N := by
    intro j x hx
    rw [← hsmul]
    exact N.smul_mem _ hx
  have key : ∀ d, ∀ f : MvPolynomial ((k : K) → ι k) ℂ, f.totalDegree ≤ d → φw f ∈ N := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro f hf
      set_option synthInstance.maxHeartbeats 100000 in
        rw [f.as_sum, map_sum]
      refine N.sum_mem fun s hs => ?_
      rw [show monomial s (AddMonoidAlgebra.coeff f s) = C (AddMonoidAlgebra.coeff f s) * monomial s 1 by
        rw [C_mul_monomial, mul_one], map_mul]
      apply hC
      have hsdeg : (s.sum fun _ e => e) ≤ d := (le_totalDegree hs).trans hf
      by_cases hall : ∀ i, s i < r i
      · exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (memT s hall)))
      · push_neg at hall
        obtain ⟨i, hi⟩ := hall
        obtain ⟨s', hsplit⟩ : ∃ s', s = s' + Finsupp.single i (r i) :=
          ⟨s - Finsupp.single i (r i), (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 hi)).symm⟩
        have hdeg : (s.sum fun _ e => e) = (s'.sum fun _ e => e) + r i := by
          rw [hsplit, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
            Finsupp.sum_single_index rfl]
        have hXr : φw (X i ^ r i) = ∑ j, φy (X j) * φw (G i j) := by
          funext z
          rw [Finset.sum_apply]
          show MvPolynomial.eval (segre z.1) (X i ^ r i) =
            ∑ j, MvPolynomial.eval (Ψ (segre z.1)) (X j) * MvPolynomial.eval (segre z.1) (G i j)
          simp only [map_pow, eval_X]
          exact hrelz i z.1 z.2
        have hri := hr i
        rw [hsplit, monomial_add_single, map_mul, hXr, Finset.mul_sum]
        refine N.sum_mem fun j _ => ?_
        rw [mul_left_comm, ← map_mul φw]
        apply hY
        apply ih ((s.sum fun _ e => e) - 1) (by omega)
        calc (monomial s' 1 * G i j).totalDegree
            ≤ (monomial s' (1 : ℂ)).totalDegree + (G i j).totalDegree := totalDegree_mul _ _
          _ ≤ (s'.sum fun _ e => e) + (r i - 1) := by
            rw [totalDegree_monomial _ one_ne_zero]
            exact Nat.add_le_add_left (hG i j) _
          _ ≤ (s.sum fun _ e => e) - 1 := by omega
  have hFG : (Subalgebra.toSubmodule (Algebra.adjoin R (Set.range φw))).FG := by
    have e2 : Subalgebra.toSubmodule (Algebra.adjoin R (Set.range φw)) = N := by
      apply le_antisymm
      · rw [Algebra.adjoin_eq_span, Submodule.span_le]
        intro x hx
        let Mw : Submonoid (Z → ℂ) :=
          { carrier := Set.range φw
            mul_mem' := by
              rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
              exact ⟨a * b, map_mul _ _ _⟩
            one_mem' := ⟨1, map_one _⟩ }
        have hx' : x ∈ Mw := (Submonoid.closure_le.2 (fun y hy => hy)) hx
        obtain ⟨f, rfl⟩ := hx'
        exact key _ f le_rfl
      · rw [Submodule.span_le]
        intro x hx
        obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
        exact Algebra.subset_adjoin ⟨_, rfl⟩
    rw [e2]
    exact ⟨_, rfl⟩
  have hint : IsIntegral R (φw F) :=
    IsIntegral.of_mem_of_fg (Algebra.adjoin R (Set.range φw)) hFG (φw F)
      (Algebra.subset_adjoin ⟨F, rfl⟩)
  obtain ⟨p, hpm, hp⟩ := hint
  refine ⟨p.natDegree, p.coeff, hpm.coeff_natDegree, fun z hz => ?_⟩
  have h := congrFun hp ⟨z, hz⟩
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_apply] at h
  exact h

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

theorem eval_eq_zero_of_mul (hM : PCMinContractStatement) {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ} (hP : IsArithVar P (e + 1)) {u : MRing ι}
    (hu : u ∉ P) {H : MRingOver ℂ ι}
    (h : ∀ z ∈ mcPts P, eval z (map (Int.castRingHom ℂ) u) * eval z H = 0) :
    ∀ z ∈ mcPts P, eval z H = 0 := by
  classical
  have hPp : P.IsPrime := hP.2.1.1
  choose i hi using hP.2.1.2.2
  set m : MRing ι := ∏ k, X ⟨k, i k⟩ with hmdef
  have hm : m ∉ P := fun h' => by
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hPp)).mp h'
    exact hi k hk
  have hv : u * m ∉ P := fun h' => (hPp.mem_or_mem h').elim hu hm
  have hvan : map (Int.castRingHom ℂ) (u * m) * H ∈ (pC P).radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ),
      MvPolynomial.mem_vanishingIdeal_iff]
    intro x hx
    change eval x _ = 0
    rw [MvPolynomial.mem_zeroLocus_iff] at hx
    by_cases hb : ∀ k, x ⟨k, i k⟩ ≠ 0
    · have hxm : x ∈ mcPts P := by
        rw [mcPts_eq_pC]
        exact ⟨fun k => ⟨i k, hb k⟩, fun f hf => hx f hf⟩
      rw [map_mul, map_mul, map_mul, mul_right_comm, h x hxm, zero_mul]
    · push Not at hb
      obtain ⟨k, hk⟩ := hb
      have : eval x (map (Int.castRingHom ℂ) m) = 0 := by
        rw [hmdef, map_prod, map_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])
      rw [map_mul, map_mul, map_mul, this, mul_zero, zero_mul]
  have hHrad : H ∈ (pC P).radical := by
    rw [← Ideal.sInf_minimalPrimes]
    refine Submodule.mem_sInf.mpr fun Q hQ => ?_
    have hQp : Ideal.IsPrime Q := hQ.1.1
    have hle : (pC P).radical ≤ Q := (Ideal.IsPrime.radical_le_iff hQp).mpr hQ.1.2
    have hvQ : map (Int.castRingHom ℂ) (u * m) ∉ Q := fun h' => by
      apply hv
      rw [← hM K ι P e hP Q hQ]
      exact h'
    exact (hQp.mem_or_mem (hle hvan)).resolve_left hvQ
  intro z hz
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ),
    MvPolynomial.mem_vanishingIdeal_iff] at hHrad
  have := hHrad z (by
    rw [MvPolynomial.mem_zeroLocus_iff]
    intro p hp
    exact (by rw [mcPts_eq_pC] at hz; exact hz.2 p hp))
  exact this

theorem exists_homog_of_cone {n : ℕ} {c : MvPolynomial (Fin n) ℂ} (hc : c ≠ 0)
    {T : Set (Fin n → ℂ)} (hT : ∀ v ∈ T, ∀ t : ℂ, t ≠ 0 → (fun i => t * v i) ∈ T)
    (hcT : ∀ v ∈ T, eval v c = 0) :
    ∃ m, homogeneousComponent m c ≠ 0 ∧ (homogeneousComponent m c).IsHomogeneous m ∧
      ∀ v ∈ T, eval v (homogeneousComponent m c) = 0 := by
  have hscale : ∀ (m : ℕ) (t : ℂ) (v : Fin n → ℂ),
      eval (fun i => t * v i) (homogeneousComponent m c) = t ^ m * eval v (homogeneousComponent m c) := by
    intro m t v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [homogeneousComponent_apply, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.mem_filter] at hd
    have hdeg : ∑ i ∈ d.support, d i = m := by
      first
      | exact hd.2
      | (rw [← hd.2]; rfl)
      | simpa [Finsupp.degree] using hd.2
    simp only [eval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, hdeg]
    ring
  have hcomp : ∀ m, ∀ v ∈ T, eval v (homogeneousComponent m c) = 0 := by
    intro m v hv
    let Q : Polynomial ℂ := ∑ k ∈ Finset.range (c.totalDegree + 1),
      Polynomial.C (eval v (homogeneousComponent k c)) * Polynomial.X ^ k
    have hQ : ∀ t : ℂ, t ≠ 0 → Q.eval t = 0 := by
      intro t ht
      have h0 := hcT _ (hT v hv t ht)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← sum_homogeneousComponent c, map_sum] at h0
      simp only [Q, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      rw [← h0]
      exact Finset.sum_congr rfl fun k _ => by rw [hscale]; ring
    have hQ0 : Q = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      apply Set.Infinite.mono (s := {t : ℂ | t ≠ 0})
      · intro t ht
        exact hQ t ht
      · exact (Set.finite_singleton (0 : ℂ)).infinite_compl
    by_cases hm : m ≤ c.totalDegree
    · have h1 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p m) hQ0
      simpa [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
        (by omega : m < c.totalDegree + 1)] using h1
    · rw [homogeneousComponent_eq_zero m c (by omega), map_zero]
  obtain ⟨m, -, hm⟩ : ∃ m ∈ Finset.range (c.totalDegree + 1), homogeneousComponent m c ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hc
    rw [← sum_homogeneousComponent c]
    exact Finset.sum_eq_zero hcon
  exact ⟨m, hm, homogeneousComponent_isHomogeneous m c, fun v hv => hcomp m v hv⟩

theorem normPoly_of (hM : PCMinContractStatement) : NormPolyStatement := by
  intro K _ ι _ P e Ψ f a hP hΨ hf hfP
  classical
  have hPp : P.IsPrime := hP.2.1.1
  have hPh : IsMultiHomogIdeal P := hP.2.1.2.1
  obtain ⟨k1⟩ := hP.1
  choose i hi using hP.2.1.2.2
  set d := ∑ k, a k with hd
  set g : MRing ι := ∏ k, X ⟨k, i k⟩ ^ (d - a k) with hgdef
  set f' : MRing ι := f * g with hf'def
  have hgP : g ∉ P := fun h' => by
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hPp)).mp h'
    exact hi k (hPp.mem_of_pow_mem _ hk)
  have hf'P : f' ∉ P := fun h' => (hPp.mem_or_mem h').elim hfP hgP
  have hweight (β : (Σ k, ι k) →₀ ℕ) (k : K) :
      Finsupp.weight (blkW ι) β k = ∑ j, β ⟨k, j⟩ := by
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
    simp [blkW, Pi.single_apply]
  have hf'h : IsWeightedHomogeneous (blkW ι) (map (Int.castRingHom ℂ) f') (fun _ => d) := by
    have h1 : IsWeightedHomogeneous (blkW ι) (map (Int.castRingHom ℂ) f) a := by
      intro β hβ
      rw [coeff_map] at hβ
      have hmem : β ∈ f.support := mem_support_iff.mpr (fun h0 => hβ (by simp [h0]))
      funext k
      rw [hweight]
      exact hf β hmem k
    have h2 : IsWeightedHomogeneous (blkW ι) (map (Int.castRingHom ℂ) g)
        (∑ k, (d - a k) • blkW ι ⟨k, i k⟩) := by
      rw [hgdef, map_prod]
      refine IsWeightedHomogeneous.prod _ _ _ fun k _ => ?_
      rw [map_pow, map_X]
      exact (isWeightedHomogeneous_X ℂ _ _).pow _
    have hw : a + ∑ k, (d - a k) • blkW ι ⟨k, i k⟩ = fun _ => d := by
      funext k'
      have hle : a k' ≤ d := Finset.single_le_sum (fun k _ => Nat.zero_le (a k))
        (Finset.mem_univ k')
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, blkW, Pi.single_apply,
        smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      omega
    rw [hf'def, map_mul, ← hw]
    exact h1.mul h2
  let p := map (Int.castRingHom ℂ) f'
  have hmonomial (β : (Σ k, ι k) →₀ ℕ) :
      ∃ G : MvPolynomial ((k : K) → ι k) ℂ, β ∈ p.support →
        ∀ z : (Σ k, ι k) → ℂ, ∏ q, z q ^ β q = eval (segre z) G := by
    by_cases hβ : β ∈ p.support
    · have hw := hf'h (mem_support_iff.mp hβ)
      obtain ⟨G, -, hG⟩ := diag_prod d (fun q => β q) (fun k => by
        rw [← hweight]
        exact congrFun hw k)
      exact ⟨G, fun _ => hG⟩
    · exact ⟨0, fun h => (hβ h).elim⟩
  choose G hG using hmonomial
  let F : MvPolynomial ((k : K) → ι k) ℂ :=
    ∑ β ∈ p.support, C (AddMonoidAlgebra.coeff p β) * G β
  have hF : ∀ z, eval z (map (Int.castRingHom ℂ) f') = eval (segre z) F := by
    intro z
    change eval z p = eval (segre z) F
    dsimp only [F]
    rw [eval_eq', map_sum]
    refine Finset.sum_congr rfl fun β hβ => ?_
    rw [eval_mul, eval_C, hG β hβ z]
  obtain ⟨n, c, hcn, hrelF⟩ := exists_monic_rel Ψ P hPh hΨ F
  have hex : ∃ k, c k ≠ 0 := ⟨n, by rw [hcn]; exact one_ne_zero⟩
  set k0 := Nat.find hex with hk0def
  have hk0 : c k0 ≠ 0 := Nat.find_spec hex
  have hlt : ∀ j < k0, c j = 0 := fun j hj => by
    by_contra h
    exact Nat.find_min hex hj h
  have hk0n : k0 ≤ n := Nat.find_min' hex (by rw [hcn]; exact one_ne_zero)
  set S := (Finset.range (n + 1)).filter (fun j => k0 ≤ j) with hSdef
  let ψ (j : Fin (e + 1)) : MRingOver ℂ ι :=
    ∑ l : (k : K) → ι k, C (Ψ (fun l' => if l = l' then 1 else 0) j) * ∏ k, X ⟨k, l k⟩
  have hψ (z : (Σ k, ι k) → ℂ) : (fun j => eval z (ψ j)) = Ψ (segre z) := by
    have hs : segre z = ∑ l : (k : K) → ι k, segre z l •
        (fun l' => if l = l' then (1 : ℂ) else 0) := by
      funext l'
      simp [Finset.sum_apply]
    funext j
    dsimp only [ψ]
    simp only [map_sum, map_mul, eval_C, map_prod, eval_X]
    conv_rhs => rw [hs]
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    change _ * segre z l = _
    rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  set H : MRingOver ℂ ι := ∑ j ∈ S,
    bind₁ ψ (c j) * (map (Int.castRingHom ℂ) f') ^ (j - k0) with hHdef
  have hbind : ∀ (z : (Σ k, ι k) → ℂ) (q : MvPolynomial (Fin (e + 1)) ℂ),
      eval z (bind₁ ψ q) = eval (Ψ (segre z)) q := by
    intro z q
    rw [eval, eval₂Hom_bind₁]
    change eval (fun j => eval z (ψ j)) q = eval (Ψ (segre z)) q
    rw [hψ]
  have hevalH : ∀ z, eval z H = ∑ j ∈ S, eval (Ψ (segre z)) (c j) * eval (segre z) F ^ (j - k0) := by
    intro z
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hHdef, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow, hbind, hF]
  have hmul : ∀ z ∈ mcPts P, eval z (map (Int.castRingHom ℂ) (f' ^ k0)) * eval z H = 0 := by
    intro z hz
    rw [hevalH, map_pow, map_pow, hF, Finset.mul_sum, ← hrelF z hz]
    rw [hSdef, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : k0 ≤ j
    · rw [if_pos hj]
      rw [show j = k0 + (j - k0) from (Nat.add_sub_cancel' hj).symm]
      rw [Nat.add_sub_cancel_left, pow_add]
      ring
    · rw [if_neg hj, hlt j (not_le.mp hj), map_zero, zero_mul]
  have hH := eval_eq_zero_of_mul hM hP (u := f' ^ k0) (fun h' => hf'P (hPp.mem_of_pow_mem _ h'))
    hmul
  set T : Set (Fin (e + 1) → ℂ) :=
    {v | ∃ z ∈ mcPts P, eval z (map (Int.castRingHom ℂ) f) = 0 ∧ Ψ (segre z) = v} with hTdef
  have hcT : ∀ v ∈ T, eval v (c k0) = 0 := by
    rintro _ ⟨z, hz, hfz, rfl⟩
    have h0 := hH z hz
    have hF0 : eval (segre z) F = 0 := by
      rw [← hF, hf'def, map_mul, map_mul, hfz, zero_mul]
    rw [hevalH, hF0] at h0
    rw [Finset.sum_eq_single k0] at h0
    · simpa using h0
    · intro j hj hjk
      have : 0 < j - k0 := by
        have := (Finset.mem_filter.mp hj).2
        omega
      rw [zero_pow this.ne', mul_zero]
    · intro h
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), le_rfl⟩) h
  have hT : ∀ v ∈ T, ∀ t : ℂ, t ≠ 0 → (fun j => t * v j) ∈ T := by
    rintro _ ⟨z, hz, hfz, rfl⟩ t ht
    set cc : K → ℂ := Function.update (fun _ => (1 : ℂ)) k1 t with hccdef
    have hcc : ∀ k, cc k ≠ 0 := by
      intro k
      by_cases hk : k = k1
      · subst hk; simp [hccdef, ht]
      · simp [hccdef, Function.update_of_ne hk]
    have hpc : ∏ k, cc k = t := by
      simp [hccdef, Finset.prod_update_of_mem (Finset.mem_univ k1)]
    refine ⟨fun p => cc p.1 * z p, mcPts_smul hPh cc hcc hz, ?_, ?_⟩
    · rw [eval_smul_homog f a hf cc z, hfz, mul_zero]
    · rw [segre_smul, map_smul, hpc]
      rfl
  obtain ⟨m, hm0, hmh, hmT⟩ := exists_homog_of_cone hk0 hT hcT
  exact ⟨homogeneousComponent m (c k0), m, hm0, hmh, fun z hz hfz => hmT _ ⟨z, hz, hfz, rfl⟩⟩

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

section PushForward

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem pushForward_null [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (q : X → Fin e → ℂ) (S : Set X)
    (hS : ∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) = 0)
    (hq : ∀ x ∉ S, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)
    (hfin : ∀ y, (q ⁻¹' {y} \ S).Finite) (g : X → ℝ) (hg : MIntegrable A Φ g) :
    mInt A Φ g = ∫ y, ∑ᶠ x ∈ q ⁻¹' {y} \ S, g x * pushDens A Φ q x :=
  pushForward_null' A Φ hΦ q S hS hq hfin g hg

end PushForward

section Res

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}

theorem psi0_null (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩
      (R.A.chart j).symm ⁻¹' {x | Ψ (segre (R.lift x x)) 0 = 0}) = 0 :=
  volume_projection_zeroSet_null R Ψ hP hΨ j

theorem ram_null (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | Ψ (segre (R.lift x x)) 0 ≠ 0 ∧
      ∃ k, x ∈ (R.A.chart k).source ∧
        LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart k).symm) (R.A.chart k x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0}) = 0 :=
  ram_null' R Ψ hP hΨ j

theorem brBad_null (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' brBad R Ψ) = 0 := by
  have h3 : brBad R Ψ ⊆ {x | R.lift x x ∈ mcPts J} ∪ {x | Ψ (segre (R.lift x x)) 0 = 0} ∪
      {x | Ψ (segre (R.lift x x)) 0 ≠ 0 ∧ ∃ k, x ∈ (R.A.chart k).source ∧
        LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart k).symm) (R.A.chart k x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0} := by
    rintro x ((h | h) | ⟨k, hk, hn⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · by_cases h0 : Ψ (segre (R.lift x x)) 0 = 0
      · exact Or.inl (Or.inr h0)
      · refine Or.inr ⟨h0, k, hk, ?_⟩
        by_contra hd
        exact hn ⟨analyticAt_brQ R Ψ x k hk h0, hd⟩
  refine measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono h3)) ?_
  simp only [Set.preimage_union, Set.inter_union_distrib_left]
  exact measure_union_null (measure_union_null (R.null j) (psi0_null R Ψ hP hΨ j))
    (ram_null R Ψ hP hΨ j)

theorem potOf_isPotential (R : AnLogRes P J e) (L : HermLine ι) (hL : IsSmoothHerm L) :
    IsPotential R.A (potOf R L) :=
  isPotential_potOf R hL

theorem logAbsLocInt : LogAbsLocIntStatement := logAbsLocInt'

theorem brIntegrable (R : AnLogRes P J e) (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι)
    (hP : IsArithVar P (e + 1)) (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hs : IsSectionOn P A s) :
    MIntegrable R.A (fun j => potOf R (L j)) (fun x => logNorm A s (R.lift x x)) :=
  brIntegrable_of logAbsLocInt R L A s hL hA hs

theorem normPoly : NormPolyStatement := normPoly_of pcMinContract

theorem projB_null (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (hJ : IsMultiHomogIdeal J) (hJP : ¬ J ≤ P) :
    volume {y : Fin e → ℂ | ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y} = 0 :=
  projB_null_of normPoly Ψ hP hΨ hJ hJP

theorem brQ_image_null (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) :
    volume (brQ R Ψ '' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0})) = 0 :=
  brQ_image_null_of R Ψ (brBad_null R Ψ hP hΨ)

theorem brFibreSum_ae (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι)
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (hL : ∀ j, IsSmoothHerm (L j))
    (hA : IsSmoothHerm A) (hs : IsSectionOn P A s) :
    ∀ᵐ y, ∑ᶠ w ∈ fibre P Ψ y, sheetDensity P Ψ (pot L) (logNorm A s) y w =
      ∑ᶠ x ∈ brQ R Ψ ⁻¹' {y} \ brBad R Ψ,
        logNorm A s (R.lift x x) * pushDens R.A (fun j => potOf R (L j)) (brQ R Ψ) x := by
  have hN : volume ({y : Fin e → ℂ | ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y} ∪
      brQ R Ψ '' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0})) = 0 :=
    measure_union_null (projB_null Ψ hP hΨ R.homog R.nondeg) (brQ_image_null R Ψ hP hΨ)
  have hNae : ∀ᵐ y, y ∉ ({y : Fin e → ℂ | ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y} ∪
      brQ R Ψ '' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0})) :=
    ae_iff.mpr (by simpa only [not_not, Set.ofPred_mem_eq] using hN)
  filter_upwards [hNae, sheetIndep K ι P e Ψ L A s hP hΨ hL hA hs] with y hyN hind
  have hy1 : ¬ ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y := fun h => hyN (Or.inl h)
  have hfib : fibre P Ψ y = brW R Ψ '' (brQ R Ψ ⁻¹' {y} \ brBad R Ψ) := by
    ext w
    constructor
    · intro hw
      obtain ⟨x, -, hx0, hxq, rfl⟩ := exists_of_mem_fibre R Ψ hw hy1
      exact ⟨x, ⟨hxq, fun hbad => hyN (Or.inr ⟨x, ⟨hbad, hx0⟩, hxq⟩)⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      have := brW_mem_fibre R Ψ hP.1 hP.2.1.2.1 (projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2)
      rwa [show brQ R Ψ x = y from hx.1] at this
  rw [hfib, finsum_mem_image ((brW_injOn R Ψ).mono (by exact fun x hx => show _ ∧ _ from
    ⟨notMemB_of_notMem_brBad R Ψ hx.2, projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2⟩))]
  refine finsum_mem_congr rfl fun x hx => ?_
  obtain ⟨γ, hγ, hval⟩ := exists_sheet_brW R Ψ L A s hP hL hs x hx.2
  rw [show brQ R Ψ x = y from hx.1] at hγ hval
  unfold sheetDensity
  rw [dite_eq_left ⟨γ, hγ⟩]
  exact (hind _ _ _ (Exists.choose_spec (⟨γ, hγ⟩ : ∃ γ, IsSheet P Ψ y (brW R Ψ x) γ)) hγ).trans hval

end Res

end ReciprocityTheory.ChartRestriction.G.Geo
