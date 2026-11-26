module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinHomOfUniformizerFrameStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EnvRingExists
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemNonZeroDivisorsOfInvertibleSpanSingletonStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorRingHomEqOfSubMemStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismHomExtOfX
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismHomExtOfX
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.BK

theorem hom_ext_of_hf_X : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Obj l ↥(OL K))
    (g g' : Hom bk.prism C), BK.hf g X = BK.hf g' X → g = g' := by
  intro l _ K bk C g g' hX

  have hI : ∀ x : bk.S, BK.hf g x - BK.hf g' x ∈ C.I := by
    intro x
    have hr : Ideal.Quotient.mk bk.prism.I x = bk.prism.str (bk.str.symm (Ideal.Quotient.mk _ x)) :=
      (bk.str.apply_symm_apply _).symm
    have h1 := g.f_str _ x hr
    have h2 := g'.f_str _ x hr
    exact Ideal.Quotient.eq.1 (h1.trans h2.symm)
  have hH : IsHausdorff (JJ C) C.A := C.complete.toIsHausdorff

  have hCC : (BK.hf g).comp (PowerSeries.C (R := Wq l bk.a)) = (BK.hf g').comp PowerSeries.C :=
    GlobalTheory.T.wittVector_ringHom_eq_of_sub_mem' l (Fq l bk.a) C.A (JJ C) (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) hH _ _
      (fun w => Ideal.mem_sup_right (hI _))

  have hP : ∀ p : Polynomial (Wq l bk.a), BK.hf g (p : bk.S) = BK.hf g' (p : bk.S) := by
    have h := Polynomial.ringHom_ext (f := (BK.hf g).comp (Polynomial.coeToPowerSeries.ringHom))
      (g := (BK.hf g').comp Polynomial.coeToPowerSeries.ringHom)
      (fun a => by
        simp only [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C]
        exact RingHom.congr_fun hCC a)
      (by simp only [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]; exact hX)
    intro p
    exact RingHom.congr_fun h p

  have hXe : ∃ q : bk.S, (X : bk.S) ^ bk.Ep.natDegree = bk.E - (l : bk.S) * q := by
    have hd : Polynomial.C (l : Wq l bk.a) ∣ bk.Ep - Polynomial.X ^ bk.Ep.natDegree := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
      rcases lt_trichotomy i bk.Ep.natDegree with h | h | h
      · rw [if_neg h.ne, sub_zero]; exact bk.dvd_coeff i h
      · rw [if_pos h, h, bk.monic.coeff_natDegree, sub_self]; exact dvd_zero _
      · rw [if_neg h.ne', sub_zero, Polynomial.coeff_eq_zero_of_natDegree_lt h]; exact dvd_zero _
    obtain ⟨q, hq⟩ := hd
    refine ⟨(q : bk.S), ?_⟩
    have h := congrArg (fun p : Polynomial (Wq l bk.a) => (p : bk.S)) hq
    rw [Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_mul,
      Polynomial.coe_C, map_natCast] at h
    show _ = (bk.Ep : bk.S) - _
    linear_combination -h
  obtain ⟨q, hq⟩ := hXe
  have hgXe : BK.hf g X ^ bk.Ep.natDegree ∈ JJ C := by
    rw [← map_pow, hq, map_sub, map_mul, map_natCast]
    refine Ideal.sub_mem _ (Ideal.mem_sup_right (g.f_I _ (Ideal.mem_span_singleton_self _)))
      (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))

  have hsplit : ∀ (N : ℕ) (f : bk.S), ∃ (p : Polynomial (Wq l bk.a)) (h : bk.S), f = (p : bk.S) + X ^ N * h := by
    intro N f
    obtain ⟨h, hh⟩ := (PowerSeries.X_pow_dvd_iff (n := N)
      (φ := f - ((trunc N f : Polynomial (Wq l bk.a)) : bk.S))).2 (fun m hm => by
        rw [map_sub, Polynomial.coeff_coe, coeff_trunc, if_pos hm, sub_self])
    exact ⟨_, h, by rw [← hh]; ring⟩
  apply Hom.ext'
  refine RingHom.ext fun f => ?_
  change BK.hf g f = BK.hf g' f
  have key : ∀ n : ℕ, BK.hf g f - BK.hf g' f ∈ JJ C ^ n := by
    intro n
    obtain ⟨p, h, hh⟩ := hsplit (bk.Ep.natDegree * n) f
    have e : ∀ φ : bk.S →+* C.A, φ f = φ (p : bk.S) + φ X ^ (bk.Ep.natDegree * n) * φ h := fun φ => by
      have := congrArg φ hh
      rwa [map_add, map_mul, map_pow] at this
    have hm : BK.hf g X ^ (bk.Ep.natDegree * n) ∈ JJ C ^ n := by
      rw [pow_mul]; exact Ideal.pow_mem_pow hgXe n
    have e2 : BK.hf g f - BK.hf g' f = BK.hf g X ^ (bk.Ep.natDegree * n) * (BK.hf g h - BK.hf g' h) := by
      have hXN : BK.hf g' X ^ (bk.Ep.natDegree * n) = BK.hf g X ^ (bk.Ep.natDegree * n) := by rw [hX]
      linear_combination e (BK.hf g) - e (BK.hf g') + hP p - BK.hf g' h * hXN
    rw [e2]
    exact Ideal.mul_mem_right _ _ hm
  refine sub_eq_zero.1 (hH.haus _ fun n => ?_)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact key n

end GlobalTheory.BSP.BK
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismHomExtOfXStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_prism_hom_ext_of_X : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Obj l ↥(OL K)) (g g' : Hom bk.prism C), BK.hf g X = BK.hf g' X → g = g' := by
  first | exact @GlobalTheory.BSP.BK.hom_ext_of_hf_X | exact GlobalTheory.BSP.BK.hom_ext_of_hf_X | (intros; apply GlobalTheory.BSP.BK.hom_ext_of_hf_X <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDeltaOfPrismIdealEqSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDeltaOfPrismIdealEqSpan
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isUnit_δ_of_I_eq_span : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B : Obj l R) (d : B.A),
    B.I = Ideal.span {d} → IsUnit (B.D.δ d) := by
  intro l hl R _ B d hI
  by_contra hu
  obtain ⟨m, hm, hdm⟩ := Ideal.exists_le_maximal (Ideal.span {B.D.δ d})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hδd : B.D.δ d ∈ m := hdm (Ideal.mem_span_singleton_self _)
  have hJ : JJ B ≤ m := by
    have h1 : JJ B ≤ (⊥ : Ideal B.A).jacobson := @IsAdicComplete.le_jacobson_bot _ _ _ B.complete
    exact h1.trans (sInf_le ⟨bot_le, hm⟩)
  have hlm : (l : B.A) ∈ m := hJ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
  have hdm' : d ∈ m := hJ (Ideal.mem_sup_right (by rw [hI]; exact Ideal.mem_span_singleton_self _))
  have hmem := B.l_mem
  rw [hI, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton_sup] at hmem
  obtain ⟨a, y, hy, hle⟩ := hmem
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  have hl2 : 2 ≤ l := hl.out.two_le
  have hφ : B.D.φ d ∈ m ^ 2 := by
    rw [B.D.φ_eq]
    refine Ideal.add_mem _ ?_ ?_
    · have : d ^ l = d ^ 2 * d ^ (l - 2) := by rw [← pow_add]; congr 1; omega
      rw [this]; exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hdm' 2)
    · rw [pow_two]; exact Ideal.mul_mem_mul hlm hδd
  have hy2 : c * B.D.φ d ∈ m ^ (1 + 1) := Ideal.mul_mem_left _ _ hφ
  have hδy : B.D.δ (c * B.D.φ d) ∈ m := by
    simpa using GlobalTheory.T.delta_mem_ideal_pow_of_mem_pow_succ l B.A B.D m hlm 1 _ hy2
  have hδad : B.D.δ (a * d) ∈ m := by
    rw [B.D.δ_mul]
    refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
    · exact Ideal.mul_mem_left _ _ hδd
    · exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hdm' _ hl.out.pos)
    · exact Ideal.mul_mem_left _ _ hδd
  have hsum : ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : B.A) * (a * d) ^ k * (c * B.D.φ d) ^ (l - k) ∈ m :=
    Ideal.sum_mem _ fun k hk =>
      Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _
        (Ideal.pow_mem_of_mem _ (Ideal.mul_mem_left _ _ hdm') _ (Finset.mem_Ioo.1 hk).1))
  have hδl : B.D.δ (l : B.A) ∈ m := by
    rw [← hle, B.D.δ_add]
    exact Ideal.sub_mem _ (Ideal.add_mem _ hδad hδy) hsum
  exact (GlobalTheory.T.prime_not_mem_sq_and_delta_not_mem l B.A B.D m hm.ne_top hlm).2 hδl

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDeltaOfPrismIdealEqSpanStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_delta_of_prism_ideal_eq_span : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B : Obj l R) (d : B.A), B.I = Ideal.span {d} → IsUnit (B.D.δ d) := by
  first | exact @GlobalTheory.BSP.isUnit_δ_of_I_eq_span | exact GlobalTheory.BSP.isUnit_δ_of_I_eq_span | (intros; apply GlobalTheory.BSP.isUnit_δ_of_I_eq_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaRingHomUniqueOfAdicTopologicalBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaRingHomUniqueOfAdicTopologicalBasis
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem deltaHom_unique_of_base : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (Q : Type) [CommRing Q] (C : Type) [CommRing C] (DQ : Delta l Q) (DC : Delta l C) (J : Ideal A) (JC : Ideal C) (i : A →+* Q) (w : Q) (tb : TopBasis i J (Digits l)), (∀ α, tb.b α = α.1.prod fun k n => (DQ.δ^[k] w) ^ n) → IsHausdorff JC C → ∀ h h' : Q →+* C, IsδMap DQ DC h → IsδMap DQ DC h' → J.map (h.comp i) ≤ JC → h.comp i = h'.comp i → h w = h' w → h = h' := by
  intro l _ A _ Q _ C _ DQ DC J JC i w tb hb hH h h' hδ hδ' hJ hi hw
  have hit : ∀ (g : Q →+* C), IsδMap DQ DC g → ∀ k x, g (DQ.δ^[k] x) = DC.δ^[k] (g x) := by
    intro g hg k
    induction k with
    | zero => intro x; rfl
    | succ k ih => intro x; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hg, ih]
  have hbα : ∀ α, h (tb.b α) = h' (tb.b α) := by
    intro α
    simp only [hb, Finsupp.prod, map_prod, map_pow, hit h hδ, hit h' hδ', hw]
  ext x
  have key : ∀ n, h x - h' x ∈ JC ^ n := by
    intro n
    have hF : ∀ α, α ∉ (tb.fin x n).toFinset → tb.c α x ∈ J ^ n := by
      intro α hα
      by_contra hc
      exact hα ((tb.fin x n).mem_toFinset.2 hc)
    have hap := tb.approx x n _ hF
    have hs : h (∑ α ∈ (tb.fin x n).toFinset, i (tb.c α x) * tb.b α) =
        h' (∑ α ∈ (tb.fin x n).toFinset, i (tb.c α x) * tb.b α) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [← RingHom.comp_apply h i, hi, RingHom.comp_apply, hbα]
    have mem : ∀ g : Q →+* C, g.comp i = h.comp i →
        g (x - ∑ α ∈ (tb.fin x n).toFinset, i (tb.c α x) * tb.b α) ∈ JC ^ n := by
      intro g hg
      have hm := Ideal.mem_map_of_mem g hap
      rw [Ideal.map_map, hg, Ideal.map_pow] at hm
      exact Ideal.pow_right_mono hJ n hm
    have e : h x - h' x = h (x - ∑ α ∈ (tb.fin x n).toFinset, i (tb.c α x) * tb.b α) -
        h' (x - ∑ α ∈ (tb.fin x n).toFinset, i (tb.c α x) * tb.b α) := by
      rw [map_sub, map_sub, hs]; ring
    rw [e]
    exact sub_mem (mem h rfl) (mem h' hi.symm)
  rw [← sub_eq_zero]
  refine hH.haus _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact key n

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaRingHomUniqueOfAdicTopologicalBasisStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deltaRingHom_unique_of_adicTopologicalBasis : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (Q : Type) [CommRing Q] (C : Type) [CommRing C] (DQ : Delta l Q) (DC : Delta l C) (J : Ideal A) (JC : Ideal C) (i : A →+* Q) (w : Q) (tb : TopBasis i J (Digits l)), (∀ α, tb.b α = α.1.prod fun k n => (DQ.δ^[k] w) ^ n) → IsHausdorff JC C → ∀ h h' : Q →+* C, IsδMap DQ DC h → IsδMap DQ DC h' → J.map (h.comp i) ≤ JC → h.comp i = h'.comp i → h w = h' w → h = h' := by
  first | exact @GlobalTheory.BSP.deltaHom_unique_of_base | exact GlobalTheory.BSP.deltaHom_unique_of_base | (intros; apply GlobalTheory.BSP.deltaHom_unique_of_base <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RegularAndBoundedTorsionOfAdicTopologicalBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Imports
namespace GlobalTheory.PowerBound

theorem pow_le {A : Type} [CommRing A] (a d : A) (n : ℕ) :
    (Ideal.span {a} ⊔ Ideal.span {d}) ^ (n + 1) ≤
      Ideal.span {a ^ (n + 1)} ⊔ Ideal.span {d} * (Ideal.span {a} ⊔ Ideal.span {d}) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    set I := Ideal.span {a} ⊔ Ideal.span {d} with hI
    have haI : a ^ (n + 1) ∈ I ^ (n + 1) :=
      Ideal.pow_mem_pow (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a)) _
    calc I ^ (n + 1 + 1) = I * I ^ (n + 1) := pow_succ' I (n + 1)
      _ ≤ I * (Ideal.span {a ^ (n + 1)} ⊔ Ideal.span {d} * I ^ n) := Ideal.mul_mono_right ih
      _ = I * Ideal.span {a ^ (n + 1)} ⊔ Ideal.span {d} * (I * I ^ n) := by
          rw [Ideal.mul_sup, mul_left_comm]
      _ ≤ Ideal.span {a ^ (n + 1 + 1)} ⊔ Ideal.span {d} * I ^ (n + 1) := by
          apply sup_le
          · rw [hI, Ideal.sup_mul, Ideal.span_singleton_mul_span_singleton, ← pow_succ']
            apply sup_le_sup_left
            exact Ideal.mul_mono_right ((Ideal.span_singleton_le_iff_mem _).2 haI)
          · rw [← pow_succ']
            exact le_sup_right

theorem main : ∀ {A : Type} [inst : CommRing A] (a d : A) (n : ℕ) {x : A},
    x ∈ (Ideal.span {a} ⊔ Ideal.span {d}) ^ (n + (1 : ℕ)) →
      ∃ (u : A), ∃ w ∈ (Ideal.span {a} ⊔ Ideal.span {d}) ^ n, x = a ^ (n + (1 : ℕ)) * u + d * w := by
  intro A _ a d n x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (pow_le a d n hx)
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  obtain ⟨w, hw, rfl⟩ := Ideal.mem_span_singleton_mul.1 hz
  exact ⟨u, w, hw, by ring⟩

end GlobalTheory.PowerBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RegularAndBoundedTorsionOfAdicTopologicalBasis
namespace GlobalTheory.BSP

section TopFree

variable {A Q : Type} [CommRing A] [CommRing Q] {i : A →+* Q} {J : Ideal A} {ι : Type}

theorem TopBasis.eq_zero_of_forall_mem (B : TopBasis i J ι) {x : Q} (h : ∀ n : ℕ, x ∈ (J ^ n).map i) :
    x = 0 := by
  have := B.complete
  refine IsHausdorff.haus (I := J.map i) this.toIsHausdorff x fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.map_pow]
  exact h n

theorem TopBasis.eq_zero_of_coeff (B : TopBasis i J ι) {x : Q} (h : ∀ k, B.c k x = 0) : x = 0 :=
  B.eq_zero_of_forall_mem fun n => by
    simpa using B.approx x n ∅ fun k _ => by rw [h k]; exact zero_mem _

theorem TopBasis.exists_sum (B : TopBasis i J ι) (z : ι → A) (hz : ∀ n : ℕ, {k | z k ∉ J ^ n}.Finite) :
    ∃ y : Q, ∀ n : ℕ, (∑ k ∈ (hz n).toFinset, i (z k) * B.b k) - y ∈ (J ^ n).map i := by
  classical
  have hc := B.complete
  obtain ⟨y, hy⟩ := IsPrecomplete.prec (I := J.map i) hc.toIsPrecomplete
    (f := fun n => ∑ k ∈ (hz n).toFinset, i (z k) * B.b k) (fun {m n} hmn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.map_pow]
      have hsub : (hz m).toFinset ⊆ (hz n).toFinset := fun k hk => by
        simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hk ⊢
        exact fun h => hk (Ideal.pow_le_pow_right hmn h)
      rw [← Finset.sum_sdiff hsub, sub_add_cancel_right]
      refine neg_mem (Ideal.sum_mem _ fun k hk => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_))
      have := (Finset.mem_sdiff.1 hk).2
      simpa using this)
  refine ⟨y, fun n => ?_⟩
  have := hy n
  rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.map_pow] at this

theorem exists_eq_of_mem_pow_succ_pair (a d : A) (n : ℕ) {x : A}
    (hx : x ∈ (Ideal.span {a} ⊔ Ideal.span {d}) ^ (n + 1)) :
    ∃ u : A, ∃ w ∈ (Ideal.span {a} ⊔ Ideal.span {d}) ^ n, x = a ^ (n + 1) * u + d * w := by
  first
  | exact @_root_.GlobalTheory.PowerBound.main
  | exact _root_.GlobalTheory.PowerBound.main
  | (apply _root_.GlobalTheory.PowerBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerBound.main ..)

theorem mem_pow_of_mul_mem_pow_pair (a d : A) (N : ℕ) (hd : d ∈ nonZeroDivisors A)
    (hN : ∀ (x : A) (m : ℕ), a ^ m * x ∈ Ideal.span {d} → a ^ N * x ∈ Ideal.span {d}) (n : ℕ) {z : A}
    (hz : d * z ∈ (Ideal.span {a} ⊔ Ideal.span {d}) ^ (n + N + 1)) :
    z ∈ (Ideal.span {a} ⊔ Ideal.span {d}) ^ n := by
  have ha : a ∈ Ideal.span {a} ⊔ Ideal.span {d} := Ideal.mem_sup_left (Ideal.mem_span_singleton_self a)
  obtain ⟨u, w, hw, e⟩ := exists_eq_of_mem_pow_succ_pair a d (n + N) hz
  have h1 : a ^ (n + N + 1) * u ∈ Ideal.span {d} :=
    Ideal.mem_span_singleton'.2 ⟨z - w, by linear_combination e⟩
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 (hN u _ h1)
  have h2 : d * (z - (a ^ n * (a * v) + w)) = 0 := by
    linear_combination e - a ^ n * a * hv
  have h3 := (mem_nonZeroDivisors_iff.1 hd).1 _ h2
  rw [sub_eq_zero.1 h3]
  exact add_mem (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ha _))
    (Ideal.pow_le_pow_right (Nat.le_add_right n N) hw)

end TopFree

theorem TopBasis.regular_and_torsion_bounded (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (Q : Type) [CommRing Q]
    (i : A →+* Q) (d : A) (N : ℕ) (ι : Type) (hd : d ∈ nonZeroDivisors A)
    (hN : ∀ (x : A) (m : ℕ), (l : A) ^ m * x ∈ Ideal.span {d} → (l : A) ^ N * x ∈ Ideal.span {d})
    (B : TopBasis i (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ι) :
    i d ∈ nonZeroDivisors Q ∧
      ∀ (x : Q) (m : ℕ), (l : Q) ^ m * x ∈ Ideal.span {i d} → (l : Q) ^ N * x ∈ Ideal.span {i d} := by
  have hl : ∀ (m : ℕ) (k : ι) (x : Q), B.c k ((l : Q) ^ m * x) = (l : A) ^ m * B.c k x := fun m k x => by
    rw [← B.c_mul, map_pow, map_natCast]
  have hreg : ∀ x : Q, i d * x = 0 → x = 0 := fun x hx =>
    B.eq_zero_of_coeff fun k => (mem_nonZeroDivisors_iff.1 hd).1 _ (by rw [← B.c_mul, hx, map_zero])
  refine ⟨mem_nonZeroDivisors_iff.2 ⟨hreg, fun x hx => hreg x (by rwa [mul_comm])⟩, fun x m hx => ?_⟩
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hx
  have h1 : ∀ k, ∃ z : A, d * z = B.c k ((l : Q) ^ N * x) := fun k => by
    have : (l : A) ^ m * B.c k x ∈ Ideal.span {d} := by
      rw [← hl, ← hy, mul_comm, B.c_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self d)
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 (hN _ _ this)
    exact ⟨z, by rw [hl, ← hz, mul_comm]⟩
  choose z hz using h1
  have hfin : ∀ n : ℕ, {k | z k ∉ (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ^ n}.Finite := fun n =>
    (B.fin ((l : Q) ^ N * x) (n + N + 1)).subset fun k hk h =>
      hk (mem_pow_of_mul_mem_pow_pair _ d N hd hN n (by rwa [hz]))
  obtain ⟨w, hw⟩ := B.exists_sum z hfin
  have key : (l : Q) ^ N * x - i d * w = 0 := B.eq_zero_of_forall_mem fun n => by
    have h2 := B.approx ((l : Q) ^ N * x) n (hfin n).toFinset fun k hk => by
      rw [← hz]
      refine Ideal.mul_mem_left _ _ ?_
      simpa using hk
    have h3 := add_mem h2 (Ideal.mul_mem_left _ (i d) (hw n))
    convert h3 using 1
    simp only [← hz, map_mul, mul_sub, Finset.mul_sum, mul_assoc]
    ring
  rw [sub_eq_zero.1 key]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RegularAndBoundedTorsionOfAdicTopologicalBasisStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_and_bounded_torsion_of_adicTopologicalBasis : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (Q : Type) [CommRing Q] (i : A →+* Q) (d : A) (N : ℕ) (ι : Type), d ∈ nonZeroDivisors A → (∀ (x : A) (m : ℕ), (l : A) ^ m * x ∈ Ideal.span {d} → (l : A) ^ N * x ∈ Ideal.span {d}) → TopBasis i (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ι → i d ∈ nonZeroDivisors Q ∧ ∀ (x : Q) (m : ℕ), (l : Q) ^ m * x ∈ Ideal.span {i d} → (l : Q) ^ N * x ∈ Ideal.span {i d} := by
  first | exact @GlobalTheory.BSP.TopBasis.regular_and_torsion_bounded | exact GlobalTheory.BSP.TopBasis.regular_and_torsion_bounded | (intros; apply GlobalTheory.BSP.TopBasis.regular_and_torsion_bounded <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinHomImageXDeltaZeroLiftsUniformizerStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinHom_image_X_delta_zero_lifts_uniformizer :
    ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Obj l ↥(OL K))
      (g : Hom bk.prism C), C.D.δ (BK.hf (bk := bk) g X) = 0 ∧
      Ideal.Quotient.mk C.I (BK.hf (bk := bk) g X) = C.str (bk.str.symm (Ideal.Quotient.mk _ X)) := by
  intro l _ K bk C g
  have hδX : (deltaS l bk.a).δ (X : bk.S) = 0 := by
    have h := (deltaS l bk.a).φ_eq (X : bk.S)
    have hφ : (deltaS l bk.a).φ (X : bk.S) = X ^ l := frobS_X l bk.a
    rw [hφ] at h
    have hmul : (l : bk.S) * (deltaS l bk.a).δ X = 0 := by linear_combination -h
    exact (mul_eq_zero.1 hmul).resolve_left (l_ne_zero l bk.a)
  refine ⟨?_, ?_⟩
  · have h := g.f_δ (X : bk.S)
    change C.D.δ (g.f X) = 0
    rw [← h]
    change g.f ((deltaS l bk.a).δ X) = 0
    rw [hδX]
    exact g.f.map_zero
  · refine g.f_str (bk.str.symm (Ideal.Quotient.mk _ X)) X ?_
    change Ideal.Quotient.mk (Ideal.span {bk.E}) X = bk.str (bk.str.symm (Ideal.Quotient.mk _ X))
    rw [RingEquiv.apply_symm_apply]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyBreuilKisinPrismCoproduct
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.EnvCop

section
variable {l : ℕ}

theorem map_eq_span {A C : Type} [CommRing A] [CommRing C] (f : A →+* C) (I : Ideal A) (d : A)
    (hI : I = Ideal.span {d}) : I.map f = Ideal.span {f d} := by
  subst hI; rw [Ideal.map_span, Set.image_singleton]

theorem map_sup_le {A C : Type} [CommRing A] [CommRing C] (f : A →+* C) (I : Ideal A) (I' : Ideal C)
    (h : ∀ a ∈ I, f a ∈ I') : (Ideal.span {(l : A)} ⊔ I).map f ≤ Ideal.span {(l : C)} ⊔ I' := by
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast]
  exact sup_le_sup_left (Ideal.map_le_of_le_comap fun a ha => Ideal.mem_comap.2 (h a ha)) _

theorem eq_add_mul_of {R : Type} [CommRing R] {a b c v : R} (h : v * c = a - b) : a = b + c * v := by
  linear_combination -h

theorem map_span_mem {Q C : Type} [CommRing Q] [CommRing C] (h : Q →+* C) (q : Q) (I : Ideal C)
    (hq : h q ∈ I) : ∀ a ∈ Ideal.span {q}, h a ∈ I := by
  intro a ha
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  rw [map_mul]; exact Ideal.mul_mem_left _ _ hq

theorem quot_eq_of {Q C : Type} [CommRing Q] [CommRing C] (h : Q →+* C) (I : Ideal C) (a b : Q) (c : C)
    (hb : h b = c) (e : h (a - b) ∈ I) : Ideal.Quotient.mk I (h a) = Ideal.Quotient.mk I c := by
  subst hb; rw [map_sub] at e; exact Ideal.Quotient.eq.2 e

theorem eval_lin {Q C : Type} [CommRing Q] [CommRing C] (h : Q →+* C) (x P D w : Q) (p d v : C)
    (hx : x = P + D * w) (hP : h P = p) (hD : h D = d) (hw : h w = v) : h x = p + d * v := by
  subst hx hP hD hw; rw [map_add (f := _), map_mul]

theorem cancel_of {C : Type} [CommRing C] {p d a v : C} (hd : d ∈ nonZeroDivisors C)
    (h : p + d * a = p + d * v) : a = v := by
  have e : d * (a - v) = 0 := by rw [mul_sub]; exact sub_eq_zero.2 (add_left_cancel h)
  exact sub_eq_zero.1 (hd.1 _ e)

theorem fg_sup_span {A : Type} [CommRing A] (I : Ideal A) (d : A) (hI : I = Ideal.span {d}) :
    (Ideal.span {(l : A)} ⊔ I).FG := by
  subst hI; exact (Submodule.fg_span_singleton _).sup (Submodule.fg_span_singleton _)
end

theorem comp_hf_X {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {P P' : Obj l ↥(OL K)} (h' : Hom P P')
    (g0 : Hom bk.prism P) (g : Hom bk.prism P') (h2 : h'.comp g0 = g) : h'.f (BK.hf g0 X) = BK.hf g X := by
  subst h2; rfl

section

variable {l : ℕ}

theorem quot_bdd_of_mem {A : Type} [CommRing A] (q : A) (N : ℕ)
    (h : ∀ (x : A) (m : ℕ), (l : A) ^ m * x ∈ Ideal.span {q} → (l : A) ^ N * x ∈ Ideal.span {q}) :
    ∀ x : A ⧸ Ideal.span {q}, (∃ m : ℕ, (l : A ⧸ Ideal.span {q}) ^ m * x = 0) →
      (l : A ⧸ Ideal.span {q}) ^ N * x = 0 := by
  rintro x ⟨m, hm⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hm' : (l : A) ^ m * y ∈ Ideal.span {q} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow, map_natCast]; exact hm
  have h2 := h y m hm'
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow, map_natCast] at h2
  exact h2

theorem pow_mul_mem_of_pow_mul_mem {A : Type} [CommRing A] (I : Ideal A) (N : ℕ)
    (h : ∀ x : A ⧸ I, (∃ m : ℕ, (l : A ⧸ I) ^ m * x = 0) → (l : A ⧸ I) ^ N * x = 0) :
    ∀ (x : A) (m : ℕ), (l : A) ^ m * x ∈ I → (l : A) ^ N * x ∈ I := by
  intro x m hm
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow, map_natCast] at hm ⊢
  exact h _ ⟨m, hm⟩

theorem map_sup_span {A Q : Type} [CommRing A] [CommRing Q] (i : A →+* Q) (I : Ideal A) (d : A)
    (hI : I = Ideal.span {d}) :
    (Ideal.span {(l : A)} ⊔ I).map i = Ideal.span {(l : Q)} ⊔ Ideal.span {i d} := by
  subst hI
  rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_natCast]

theorem le_comap_span {A Q : Type} [CommRing A] [CommRing Q] (i : A →+* Q) (I : Ideal A) (d : A)
    (hI : I = Ideal.span {d}) : I ≤ (Ideal.span {i d}).comap i := by
  subst hI
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  rw [Ideal.mem_comap, map_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

end

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} {B : Obj l ↥(OL K)} {d p : B.A}

section
variable (hI : B.I = Ideal.span {d}) (En : EnvRing B.D (JJ B) d p)
include hI

theorem facts : ∃ N : ℕ, En.i d ∈ nonZeroDivisors En.Q ∧ ∀ (x : En.Q) (m : ℕ),
    (l : En.Q) ^ m * x ∈ Ideal.span {En.i d} → (l : En.Q) ^ N * x ∈ Ideal.span {En.i d} := by
  obtain ⟨N, hN⟩ := B.bdd
  have hnz : d ∈ nonZeroDivisors B.A := by
    have h := B.inv; rw [hI] at h; exact GlobalTheory.T.mem_nonZeroDivisors_of_invertible_span_singleton' _ d h
  have hb : ∀ (x : B.A) (m : ℕ), (l : B.A) ^ m * x ∈ Ideal.span {d} → (l : B.A) ^ N * x ∈ Ideal.span {d} := by
    rw [← hI]; exact pow_mul_mem_of_pow_mul_mem B.I N hN
  have tb : TopBasis En.i (Ideal.span {(l : B.A)} ⊔ Ideal.span {d}) (Digits l) := by
    rw [← hI]; exact En.tb
  exact ⟨N, GlobalTheory.T.regular_and_bounded_torsion_of_adicTopologicalBasis l B.A En.Q En.i d N (Digits l) hnz hb tb⟩

def strQ : ↥(OL K) →+* En.Q ⧸ Ideal.span {En.i d} :=
  (Ideal.quotientMap (Ideal.span {En.i d}) En.i (le_comap_span En.i B.I d hI)).comp B.str

theorem strQ_eq (r : ↥(OL K)) (b : B.A) (hb : Ideal.Quotient.mk B.I b = B.str r) :
    strQ hI En r = Ideal.Quotient.mk (Ideal.span {En.i d}) (En.i b) :=
  (congrArg (Ideal.quotientMap (Ideal.span {En.i d}) En.i (le_comap_span En.i B.I d hI)) hb).symm.trans
    Ideal.quotientMap_mk

abbrev obj : Obj l ↥(OL K) where
  A := En.Q
  D := En.DQ
  I := Ideal.span {En.i d}
  inv := invertible_span_singleton (facts hI En).choose_spec.1
  complete := by rw [← map_sup_span En.i B.I d hI]; exact En.tb.complete
  l_mem := En.DQ.l_mem_of_isUnit hl.out.pos (by rw [← En.i_δ d]; exact (GlobalTheory.T.isUnit_delta_of_prism_ideal_eq_span l _ B d hI).map En.i)
  bdd := ⟨(facts hI En).choose, quot_bdd_of_mem (En.i d) _ (facts hI En).choose_spec.2⟩
  str := strQ hI En

def inl : Hom B (obj hI En) where
  f := En.i
  f_δ := En.i_δ
  f_I a ha := le_comap_span En.i B.I d hI ha
  f_str r a h := Ideal.quotientMap_mk.symm.trans
    (congrArg (Ideal.quotientMap (Ideal.span {En.i d}) En.i (le_comap_span En.i B.I d hI)) h)

end

variable {bk : BK K} (En : EnvRing B.D (JJ B) d p)

theorem frame (hF : IsFrame bk B d p) : IsFrame bk (obj hF.1 En) (En.i d) (En.i p + En.i d * En.w) := by
  refine ⟨rfl, ?_⟩
  have e1 := congrArg (Ideal.quotientMap (Ideal.span {En.i d}) En.i (le_comap_span En.i B.I d hF.1)) hF.2
  have e2 : En.i p + En.i d * En.w - En.i p ∈ Ideal.span {En.i d} := by
    rw [add_sub_cancel_left]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  exact (Ideal.Quotient.eq.2 e2).trans (Ideal.quotientMap_mk.symm.trans e1)

theorem str_of (hI : B.I = Ideal.span {d}) {C : Obj l ↥(OL K)} (f : Hom B C) (h0 : En.Q →+* C.A)
    (h0a : ∀ a, h0 (En.i a) = f.f a) (hIQ : ∀ a ∈ Ideal.span {En.i d}, h0 a ∈ C.I) (r : ↥(OL K)) (a : En.Q)
    (ha : Ideal.Quotient.mk (Ideal.span {En.i d}) a = strQ hI En r) :
    Ideal.Quotient.mk C.I (h0 a) = C.str r := by
  have hsu : ∃ b : B.A, Ideal.Quotient.mk B.I b = B.str r := Ideal.Quotient.mk_surjective (B.str r)
  obtain ⟨b, hb⟩ := hsu
  have e1 : Ideal.Quotient.mk (Ideal.span {En.i d}) a = Ideal.Quotient.mk (Ideal.span {En.i d}) (En.i b) :=
    ha.trans (strQ_eq hI En r b hb)
  have hab : a - En.i b ∈ Ideal.span {En.i d} := Ideal.Quotient.eq.1 e1
  exact (quot_eq_of h0 C.I a (En.i b) (f.f b) (h0a b) (hIQ _ hab)).trans (f.f_str r b hb)

theorem I_of (hI : B.I = Ideal.span {d}) {C : Obj l ↥(OL K)} (f : Hom B C) (h0 : En.Q →+* C.A)
    (h0a : ∀ a, h0 (En.i a) = f.f a) : ∀ a ∈ Ideal.span {En.i d}, h0 a ∈ C.I :=
  map_span_mem h0 (En.i d) C.I ((congrArg (· ∈ C.I) (h0a d)).mpr
    (f.f_I d (by rw [hI]; exact Ideal.mem_span_singleton_self d)))

def lift (hI : B.I = Ideal.span {d}) {C : Obj l ↥(OL K)} (f : Hom B C) (h0 : En.Q →+* C.A)
    (h0δ : IsδMap En.DQ C.D h0) (h0a : ∀ a, h0 (En.i a) = f.f a) : Hom (obj hI En) C where
  f := h0
  f_δ := h0δ
  f_I := I_of En hI f h0 h0a
  f_str := str_of En hI f h0 h0a (I_of En hI f h0 h0a)


set_option maxHeartbeats 2000000 in
theorem univ (hF : IsFrame bk B d p) (g0 : Hom bk.prism (obj hF.1 En))
    (hg0 : BK.hf g0 X = En.i p + En.i d * En.w) (C : Obj l ↥(OL K)) (f : Hom B C)
    (g : Hom bk.prism C) : ∃! h : Hom (obj hF.1 En) C, h.comp (inl hF.1 En) = f ∧ h.comp g0 = g := by
  have hdI : d ∈ B.I := by rw [hF.1]; exact Ideal.mem_span_singleton_self d
  have hCI : C.I = Ideal.span {f.f d} :=
    (GlobalTheory.T.prism_hom_map_ideal_eq l _ B C f).symm.trans (map_eq_span f.f B.I d hF.1)
  have hnz : f.f d ∈ nonZeroDivisors C.A := by
    have h := C.inv; rw [hCI] at h; exact GlobalTheory.T.mem_nonZeroDivisors_of_invertible_span_singleton' _ _ h
  obtain ⟨hgδ, hgs⟩ := GlobalTheory.T.breuilKisinHom_image_X_delta_zero_lifts_uniformizer l K bk C g
  have hfp := f.f_str _ p hF.2
  have hmem : BK.hf g X - f.f p ∈ Ideal.span {f.f d} := by
    rw [← hCI]; exact Ideal.Quotient.eq.1 (hgs.trans hfp.symm)
  have hex : ∃ v', v' * f.f d = BK.hf g X - f.f p := Ideal.mem_span_singleton'.1 hmem
  obtain ⟨v', hv'⟩ := hex
  have hgX : BK.hf g X = f.f p + f.f d * v' := eq_add_mul_of hv'
  have hrel : C.D.δ (f.f p + f.f d * v') = 0 := (congrArg C.D.δ hgX).symm.trans hgδ
  have hJ : (JJ B).map f.f ≤ JJ C := map_sup_le f.f B.I C.I f.f_I
  have hlift : ∃ h : En.Q →+* C.A, IsδMap En.DQ C.D h ∧ h.comp En.i = f.f ∧ h En.w = v' :=
    En.lift C.A C.D (JJ C) C.complete f.f f.f_δ hJ v' hrel
  obtain ⟨h0, h0δ, h0i, h0w⟩ := hlift
  have h0a : ∀ a, h0 (En.i a) = f.f a := fun a => RingHom.congr_fun h0i a
  refine ⟨lift En hF.1 f h0 h0δ h0a, ⟨Hom.ext' h0i, GlobalTheory.T.breuilKisin_prism_hom_ext_of_X l K bk C _ _ ?_⟩, ?_⟩
  · exact (eval_lin h0 _ _ _ _ _ _ _ hg0 (h0a p) (h0a d) h0w).trans hgX.symm
  · rintro h' ⟨h1, h2⟩
    have e1 : h'.f.comp En.i = f.f := congrArg Hom.f h1
    have e1a : ∀ a, h'.f (En.i a) = f.f a := fun a => RingHom.congr_fun e1 a
    have e2 := comp_hf_X h' g0 g h2
    have e3 : h'.f En.w = v' :=
      cancel_of hnz ((eval_lin h'.f (BK.hf g0 X) (En.i p) (En.i d) En.w (f.f p) (f.f d) (h'.f En.w) hg0 (e1a p) (e1a d) rfl).symm.trans (e2.trans hgX))
    have hJ' : (JJ B).map (h'.f.comp En.i) ≤ JJ C := (congrArg (fun φ => (JJ B).map φ ≤ JJ C) e1).mpr hJ
    exact Hom.ext' (GlobalTheory.T.deltaRingHom_unique_of_adicTopologicalBasis l B.A En.Q C.A En.DQ C.D (JJ B) (JJ C) En.i En.w En.tb En.tb_b
      C.complete.toIsHausdorff h'.f h0 h'.f_δ h0δ hJ' (e1.trans h0i.symm) (e3.trans h0w.symm))

def env (hF : IsFrame bk B d p) : Env bk B d p :=
  have hex := GlobalTheory.T.exists_breuilKisinHom_of_uniformizerFrame l K bk (obj hF.1 En) (En.i d) (En.i p + En.i d * En.w) (frame En hF) En.rel
  { Q := obj hF.1 En
    inl := inl hF.1 En
    inr := hex.choose
    univ := univ En hF hex.choose hex.choose_spec
    w := En.w
    w_eq := hex.choose_spec
    I_eq := rfl
    tb := En.tb
    tb_b := En.tb_b }

end GlobalTheory.BSP.EnvCop


open GlobalTheory.BSP.EnvCop in
theorem GlobalTheory.BSP.nonempty_env : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K))
    (d p : B.A), IsFrame bk B d p → Nonempty (Env bk B d p) := by
  intro l _ K bk B d p hF
  have hd : d ∈ JJ B := Ideal.mem_sup_right (by rw [hF.1]; exact Ideal.mem_span_singleton_self d)
  have hEn : Nonempty (EnvRing B.D (JJ B) d p) :=
    GlobalTheory.T.nonempty_envRing l B.A B.D (JJ B) d p (fg_sup_span B.I d hF.1)
      (Ideal.mem_sup_left (Ideal.mem_span_singleton_self (l : B.A))) hd (GlobalTheory.T.isUnit_delta_of_prism_ideal_eq_span l _ B d hF.1) B.complete
  exact ⟨env hEn.some hF⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyBreuilKisinPrismCoproductStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_breuilKisinPrismCoproduct : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (d p : B.A), IsFrame bk B d p → Nonempty (Env bk B d p) := by
  first | exact @GlobalTheory.BSP.nonempty_env | exact GlobalTheory.BSP.nonempty_env | (intros; apply GlobalTheory.BSP.nonempty_env <;> assumption)
end
