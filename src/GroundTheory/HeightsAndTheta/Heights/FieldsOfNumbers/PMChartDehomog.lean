module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocQuot

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartDehomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem prod_pow_blockWeight {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {M : Type*}
    [CommMonoid M] (w : K → M) (e : (Σ k, ι k) →₀ ℕ) :
    ∏ k, w k ^ (Finsupp.weight (blockWeight ι) e k) = e.prod fun v n => w v.1 ^ n := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, ← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm, Finsupp.prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finset.prod_eq_single v.1]
  · simp [blockWeight]
  · intro k _ hk
    simp [blockWeight, Pi.single_eq_of_ne hk]
  · simp

theorem MChartDehomog.proof : MChartDehomog.Statement := by
  intro F _ K _ _ ι P _ u hu f b hf
  set L := FractionRing (MRing ι F ⧸ P)
  let φ : MRing ι F →+* L := (algebraMap (MRing ι F ⧸ P) L).comp (Ideal.Quotient.mk P)
  let w : K → L := fun k => φ (X ⟨k, u k⟩)
  have hw : ∀ k, w k ≠ 0 := fun k => by
    simp only [w, φ, RingHom.comp_apply, ne_eq, IsFractionRing.to_map_eq_zero_iff,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hu k
  have hD : φ (chartMonomial u b) = ∏ k, w k ^ b k := by
    simp [chartMonomial, w, map_prod, map_pow]
  have hC : ∀ c : F, φ (C c) = algebraMap F L c := fun c => by
    simp only [φ, RingHom.comp_apply]
    rw [← MvPolynomial.algebraMap_eq, ← Ideal.Quotient.mkₐ_eq_mk F, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]
  have hmono : ∀ e ∈ f.support, chartMap P u (monomial e (AddMonoidAlgebra.coeff f e)) * ∏ k, w k ^ b k =
      φ (monomial e (AddMonoidAlgebra.coeff f e)) := by
    intro e he
    have hwe : Finsupp.weight (blockWeight ι) e = b := hf (mem_support_iff.mp he)
    rw [← hwe, prod_pow_blockWeight, chartMap, aeval_monomial, mul_assoc, ← Finsupp.prod_mul,
      monomial_eq, map_mul, hC, Finsupp.prod, Finsupp.prod, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    change (φ (X v) / w v.1) ^ e v * w v.1 ^ e v = φ (X v ^ e v)
    rw [← mul_pow, div_mul_cancel₀ _ (hw v.1), map_pow]
  change chartMap P u f = φ f / φ (chartMonomial u b)
  rw [hD, eq_div_iff (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hw k))]
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl hmono

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type*} [Field F]


omit [DecidableEq K] in
theorem chartMonomial_add (u : ∀ k, ι k) (a c : K → ℕ) :
    (chartMonomial u (a + c) : MRing ι F) = chartMonomial u a * chartMonomial u c := by
  simp only [chartMonomial, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

theorem chartMonomial_isMultiHomog (u : ∀ k, ι k) (c : K → ℕ) :
    IsMultiHomog (chartMonomial u c : MRing ι F) c := by
  show IsWeightedHomogeneous (blockWeight ι) (∏ k, (X ⟨k, u k⟩ : MRing ι F) ^ c k) c
  have h := IsWeightedHomogeneous.prod (R := F) Finset.univ
    (fun k => (X ⟨k, u k⟩ : MRing ι F) ^ c k) (fun k => c k • blockWeight ι ⟨k, u k⟩)
    (w := blockWeight ι) (fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) ⟨k, u k⟩).pow (c k))
  convert h using 1
  funext j
  simp [blockWeight, Finset.sum_apply, Pi.single_apply]

theorem finsuppProd_chartVar (u : ∀ k, ι k) (e : (Σ k, ι k) →₀ ℕ) :
    (e.prod fun v n => (X ⟨v.1, u v.1⟩ : MRing ι F) ^ n) =
      chartMonomial u (Finsupp.weight (blockWeight ι) e) := by
  induction e using Finsupp.induction_linear with
  | zero => simp [chartMonomial]
  | add f g hf hg =>
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), hf, hg, map_add (f := _),
      chartMonomial_add]
  | single v n =>
    rw [Finsupp.prod_single_index (by simp), Finsupp.weight_single]
    simp only [chartMonomial]
    rw [Finset.prod_eq_single v.1]
    · simp [blockWeight]
    · intro k _ hk
      simp [blockWeight, hk]
    · simp

theorem chartMap_monomial_mul (P : Ideal (MRing ι F)) [P.IsPrime] (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) (e : (Σ k, ι k) →₀ ℕ) (c : F) :
    chartMap P u (monomial e c) *
        algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
          (Ideal.Quotient.mk P (chartMonomial u (Finsupp.weight (blockWeight ι) e))) =
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (monomial e c)) := by
  have hy : ∀ k, algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
      (Ideal.Quotient.mk P (X ⟨k, u k⟩)) ≠ 0 := fun k => by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact hu k
  rw [← finsuppProd_chartVar, chartMap, aeval_monomial, monomial_eq]
  simp only [map_mul, map_finsuppProd, map_pow]
  rw [mul_assoc, ← Finsupp.prod_mul]
  congr 1
  refine Finsupp.prod_congr fun v _ => ?_
  rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (hy v.1))]

theorem MChartHomog.proof : MChartHomog.Statement.{u} := by
  intro F _ K _ _ ι u p
  classical
  obtain ⟨b, hle⟩ : ∃ b : K → ℕ, ∀ e ∈ p.support, Finsupp.weight (blockWeight ι) e ≤ b :=
    ⟨fun k => p.support.sup fun e => Finsupp.weight (blockWeight ι) e k, fun e he k =>
      Finset.le_sup (f := fun e => Finsupp.weight (blockWeight ι) e k) he⟩
  refine ⟨b, ∑ e ∈ p.support,
    monomial e (AddMonoidAlgebra.coeff p e) * chartMonomial u (b - Finsupp.weight (blockWeight ι) e), ?_, ?_⟩
  · refine IsWeightedHomogeneous.sum _ _ _ fun e he => ?_
    have := (isWeightedHomogeneous_monomial (blockWeight ι) e (AddMonoidAlgebra.coeff p e) rfl).mul
      (chartMonomial_isMultiHomog (F := F) u (b - Finsupp.weight (blockWeight ι) e))
    rwa [add_tsub_cancel_of_le (hle e he)] at this
  · intro P _ hu
    have hY : ∀ c, algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
        (Ideal.Quotient.mk P (chartMonomial u c)) ≠ 0 := fun c => by
      simp only [chartMonomial, map_prod, map_pow]
      refine Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ ?_
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact hu k
    rw [eq_div_iff (hY b)]
    conv_lhs => rw [p.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul, map_sum, map_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    have key : (chartMonomial u b : MRing ι F) = chartMonomial u (Finsupp.weight (blockWeight ι) e) *
        chartMonomial u (b - Finsupp.weight (blockWeight ι) e) := by
      rw [← chartMonomial_add, add_tsub_cancel_of_le (hle e he)]
    rw [key, map_mul, map_mul, map_mul, map_mul, ← mul_assoc, chartMap_monomial_mul P u hu]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartLocDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

namespace MChartLocDim

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

theorem chartMonomial_isMultiHomog (u : ∀ k, ι k) (b : K → ℕ) :
    IsMultiHomog (chartMonomial (F := F) u b) b := by
  have h := IsWeightedHomogeneous.prod (R := F) (w := blockWeight ι) Finset.univ
    (fun k => (X ⟨k, u k⟩ : MRing ι F) ^ b k) (fun k => b k • blockWeight ι ⟨k, u k⟩)
    (fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) ⟨k, u k⟩).pow (b k))
  unfold IsMultiHomog chartMonomial
  convert h using 1
  funext j
  simp [blockWeight, Finset.sum_apply, Pi.single_apply]


omit [DecidableEq K] in
theorem chartMonomial_not_mem (Q : Ideal (MRing ι F)) [Q.IsPrime] (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ Q) (b : K → ℕ) : chartMonomial u b ∉ Q := by
  unfold chartMonomial
  rw [Ideal.IsPrime.prod_mem_iff]
  rintro ⟨k, -, hk⟩
  exact hu k (Ideal.IsPrime.mem_of_pow_mem inferInstance _ hk)


omit [Fintype K] [DecidableEq K] in
theorem algebraMap_mk_ne_zero (Q : Ideal (MRing ι F)) [Q.IsPrime] {g : MRing ι F} (hg : g ∉ Q) :
    algebraMap (MRing ι F ⧸ Q) (FractionRing (MRing ι F ⧸ Q)) (Ideal.Quotient.mk Q g) ≠ 0 := by
  rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  exact hg


omit [DecidableEq K] in
theorem mem_chartIdeal_iff (Q : Ideal (MRing ι F)) [Q.IsPrime] (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ Q) {p h : MRing ι F} {b : K → ℕ}
    (hp : chartMap Q u p = algebraMap (MRing ι F ⧸ Q) (FractionRing (MRing ι F ⧸ Q))
      (Ideal.Quotient.mk Q h) / algebraMap (MRing ι F ⧸ Q) _ (Ideal.Quotient.mk Q (chartMonomial u b))) :
    p ∈ chartIdeal Q u ↔ h ∈ Q := by
  rw [chartIdeal, RingHom.mem_ker, hp, div_eq_zero_iff,
    or_iff_left (algebraMap_mk_ne_zero Q (chartMonomial_not_mem Q u hu b)),
    IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]


omit [Fintype K] in
theorem chartMap_mem (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ W) (p : MRing ι F) : chartMap P u p ∈ degZeroLoc P {W} := by
  have hr : (chartMap P u).range ≤ degZeroLoc P {W} := by
    rw [chartMap, aeval_range, Algebra.adjoin_le_iff]
    rintro _ ⟨v, rfl⟩
    exact div_mem_degZeroLoc P {W} (isWeightedHomogeneous_X F (blockWeight ι) v)
      (isWeightedHomogeneous_X F (blockWeight ι) ⟨v.1, u v.1⟩)
      (fun h => hu v.1 (hPW h)) (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact hu v.1)
  exact hr ⟨p, rfl⟩

def toLoc (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ W) : (MRing ι F ⧸ chartIdeal P u) →+* degZeroLoc P {W} :=
  Ideal.Quotient.lift (chartIdeal P u)
    ((chartMap P u).toRingHom.codRestrict (degZeroLoc P {W}) (chartMap_mem P W hPW u hu))
    (fun _ ha => Subtype.ext (RingHom.mem_ker.mp ha))

end MChartLocDim


open MChartLocDim in
theorem MChartLocDim.proof (h₁ : DegZeroLocQuot.Statement.{u}) (h₂ : MChartDehomog.Statement.{u})
    (h₃ : MChartHomog.Statement.{u}) : MChartLocDim.Statement.{u} := by
  intro F _ K _ _ ι _ P W _ _ hPW u hu
  have huP : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P := fun k h => hu k (hPW h)
  have hle : chartIdeal P u ≤ chartIdeal W u := by
    intro p hp
    obtain ⟨b, h, -, hQ⟩ := h₃ F K ι u p
    exact (mem_chartIdeal_iff W u hu (hQ W hu)).2 (hPW ((mem_chartIdeal_iff P u huP (hQ P huP)).1 hp))
  set q := (chartIdeal W u).map (Ideal.Quotient.mk (chartIdeal P u))
  have : q.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hle)
  let _ := (toLoc P W hPW u hu).toAlgebra
  have hmap : ∀ p, ((algebraMap (MRing ι F ⧸ chartIdeal P u) (degZeroLoc P {W})
      (Ideal.Quotient.mk _ p) : degZeroLoc P {W}) : FractionRing (MRing ι F ⧸ P)) = chartMap P u p :=
    fun p => rfl
  have hmemq : ∀ p, Ideal.Quotient.mk (chartIdeal P u) p ∈ q ↔ p ∈ chartIdeal W u :=
    fun p => Ideal.mem_quotient_iff_mem hle
  have : IsLocalization.AtPrime (degZeroLoc P {W}) q := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨a, ha⟩
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
      have hpW : p ∉ chartIdeal W u := fun h => ha ((hmemq p).2 h)
      obtain ⟨b, h, hh, hQ⟩ := h₃ F K ι u p
      have hhW : h ∉ W := fun h' => hpW ((mem_chartIdeal_iff W u hu (hQ W hu)).2 h')
      have hinv := div_mem_degZeroLoc P {W} (chartMonomial_isMultiHomog u b) hh (fun h' => hhW (hPW h'))
        (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact hhW)
      refine IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext ?_)
      rw [Subalgebra.coe_mul, hmap, hQ P huP, Subalgebra.coe_one,
        div_mul_div_comm, mul_comm, div_self]
      exact mul_ne_zero (algebraMap_mk_ne_zero P (chartMonomial_not_mem P u huP b))
        (algebraMap_mk_ne_zero P (fun h' => hhW (hPW h')))
    · rintro ⟨x, hx⟩
      obtain ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩ := h₁ F K ι P {W}
        (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; infer_instance) x hx
      have hgW' : g ∉ W := hgW W rfl
      have hgq : Ideal.Quotient.mk (chartIdeal P u) g ∈ q.primeCompl := fun h' =>
        hgW' ((mem_chartIdeal_iff W u hu (h₂ F K ι W u hu g b hg)).1 ((hmemq g).1 h'))
      refine ⟨(Ideal.Quotient.mk _ f, ⟨_, hgq⟩), Subtype.ext ?_⟩
      rw [Subalgebra.coe_mul, hmap, hmap, h₂ F K ι P u huP g b hg, h₂ F K ι P u huP f b hf]
      have h1 := algebraMap_mk_ne_zero P (chartMonomial_not_mem P u huP b)
      have h2 := algebraMap_mk_ne_zero P hgP
      field_simp
    · intro a c hac
      refine ⟨1, ?_⟩
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨p', rfl⟩ := Ideal.Quotient.mk_surjective c
      have h := congrArg Subtype.val hac
      rw [hmap, hmap, ← sub_eq_zero, ← map_sub] at h
      rw [Submonoid.coe_one, one_mul, one_mul]
      exact Ideal.Quotient.eq.mpr (RingHom.mem_ker.mpr h)
  exact IsLocalization.AtPrime.ringKrullDim_eq_height q (degZeroLoc P {W})

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFunctionFieldFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

namespace FunctionFieldFinite

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

def chartGens (P : Ideal (MRing ι F)) [P.IsPrime] (u : ∀ k, ι k) :
    Set (FractionRing (MRing ι F ⧸ P)) :=
  Set.range fun v => algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (X v)) /
    algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P (X ⟨v.1, u v.1⟩))


omit [Fintype K] [DecidableEq K] in
theorem range_chartMap (P : Ideal (MRing ι F)) [P.IsPrime] (u : ∀ k, ι k) :
    (chartMap P u).range = Algebra.adjoin F (chartGens P u) :=
  aeval_range _

theorem homFracDegZero_eq (hD : MChartDehomog.Statement.{u}) (P : Ideal (MRing ι F)) [P.IsPrime]
    (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) :
    homFracDegZero P = IntermediateField.adjoin F (chartGens P u) := by
  apply le_antisymm
  · unfold homFracDegZero
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨b, f, g, hf, hg, -, rfl⟩
    have hm : algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
        (Ideal.Quotient.mk P (chartMonomial u b)) ≠ 0 := by
      rw [chartMonomial, map_prod, map_prod]
      refine Finset.prod_ne_zero_iff.mpr fun k _ => ?_
      rw [map_pow, map_pow]
      refine pow_ne_zero _ ?_
      rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
      exact hu k
    have hr : ∀ p, chartMap P u p ∈ IntermediateField.adjoin F (chartGens P u) := fun p =>
      IntermediateField.algebra_adjoin_le_adjoin F _ (by rw [← range_chartMap]; exact ⟨p, rfl⟩)
    have key := div_mem (hr f) (hr g)
    rwa [hD F K ι P u hu f b hf, hD F K ι P u hu g b hg, div_div_div_cancel_right₀ hm] at key
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨v, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨blockWeight ι v, X v, X ⟨v.1, u v.1⟩,
      isWeightedHomogeneous_X _ _ _, isWeightedHomogeneous_X _ _ _, hu v.1, rfl⟩


open IntermediateField.algebraAdjoinAdjoin in
theorem trdeg_homFracDegZero (hD : MChartDehomog.Statement.{u}) (hT : MChartTrdeg.Statement.{u})
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) [P.IsPrime] (hP : IsMultiHomogIdeal P)
    (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) :
    Algebra.trdeg F (homFracDegZero P) + Fintype.card K = Algebra.trdeg F (MRing ι F ⧸ P) := by
  haveI : Algebra.FiniteType F (Algebra.adjoin F (chartGens P u)) :=
    Algebra.FiniteType.adjoin_of_finite (Set.finite_range _)
  rw [← hT F K ι P hP u hu, homFracDegZero_eq hD P u hu,
    GroundTheory.Arith.Abelian.Jacobian.trdeg_eq_of_isFractionRing (k := F)
      (A := Algebra.adjoin F (chartGens P u)), ← range_chartMap]
  exact congrArg (· + _) (Ideal.quotientKerEquivRange (chartMap P u)).trdeg_eq.symm

theorem relDim_eq_trdeg (hD : MChartDehomog.Statement.{u}) (hT : MChartTrdeg.Statement.{u})
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) [P.IsPrime] (hP : IsMultiProjPrime P) :
    ∃ n : ℕ, Algebra.trdeg F (homFracDegZero P) = n ∧
      relDim P = (((n : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := by
  choose u hu using hP.relevant
  have h1 := trdeg_homFracDegZero hD hT P hP.multiHomog u hu
  obtain ⟨m, hdim, htr⟩ :=
    GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg (k := F) (A := MRing ι F ⧸ P)
  rw [htr] at h1
  have hlt : Algebra.trdeg F (homFracDegZero P) < Cardinal.aleph0 :=
    lt_of_le_of_lt (h1 ▸ self_le_add_right _ _) (Cardinal.natCast_lt_aleph0 (n := m))
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp hlt
  rw [hn] at h1
  have hnm : n + Fintype.card K = m := by exact_mod_cast h1
  refine ⟨n, hn, ?_⟩
  have hz : (((n + Fintype.card K : ℕ) : ℤ) - Fintype.card K : ℤ) = n := by push_cast; ring
  rw [relDim, hdim, ← hnm, ← hz]
  rfl

end FunctionFieldFinite


open FunctionFieldFinite in
theorem FunctionFieldFinite.proof (hD : MChartDehomog.Statement.{u})
    (hT : MChartTrdeg.Statement.{u}) : FunctionFieldFinite.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' hrel
  have := hP'.isPrime
  have hP := isMultiProjPrime_contractPrime j ι' hP'
  obtain ⟨n, hn, hrn⟩ := relDim_eq_trdeg hD hT (contractPrime j P') hP
  obtain ⟨n', hn', hrn'⟩ := relDim_eq_trdeg hD hT P' hP'
  have hnn : n = n' := by
    rw [hrel, hrn'] at hrn
    exact_mod_cast (WithTop.coe_injective (WithBot.coe_injective hrn)).symm
  set E := (homFracDegZero (contractPrime j P')).map (contractFracMap j P')
  set κ' := homFracDegZero P'
  have h : E ≤ κ' := map_homFracDegZero_le j ι' P'
  have hE : Algebra.trdeg F E = n :=
    (IntermediateField.equivMap _ (contractFracMap j P')).trdeg_eq.symm.trans hn
  let _ : Algebra E κ' := (IntermediateField.inclusion h).toAlgebra
  have : IsScalarTower F E κ' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FaithfulSMul E κ' :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IntermediateField.inclusion h).injective
  have : FaithfulSMul F E := (faithfulSMul_iff_algebraMap_injective F E).2 (algebraMap F E).injective
  have htow := trdeg_add_eq F E (A := κ')
  rw [hE, hn', ← hnn] at htow
  have hlt : Algebra.trdeg E κ' < Cardinal.aleph0 :=
    lt_of_le_of_lt (htow ▸ self_le_add_left _ _) (Cardinal.natCast_lt_aleph0 (n := n))
  obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.mp hlt
  rw [hm] at htow
  have hm0 : m = 0 := by
    have : n + m = n := by exact_mod_cast htow
    omega
  have : Algebra.IsAlgebraic E κ' := trdeg_eq_zero_iff.mp (by rw [hm, hm0]; rfl)
  let g : κ' →ₐ[E] FractionRing (MRing ι' F ⧸ P') :=
    { (κ'.val : κ' →+* FractionRing (MRing ι' F ⧸ P')) with commutes' := fun _ => rfl }
  choose u hu using hP'.relevant
  have hκ' : κ' = IntermediateField.adjoin F (chartGens P' u) := homFracDegZero_eq hD P' u hu
  have hint : ∀ x ∈ chartGens P' u, IsIntegral E x := by
    intro x hx
    have hx' : x ∈ κ' := hκ' ▸ IntermediateField.subset_adjoin F _ hx
    have hy : IsAlgebraic E (⟨x, hx'⟩ : κ') := Algebra.IsAlgebraic.isAlgebraic _
    exact IsIntegral.map g hy.isIntegral
  have : Finite (chartGens P' u) := (Set.finite_range _).to_subtype
  have := IntermediateField.finiteDimensional_adjoin hint
  show IntermediateField.relfinrank E κ' ≠ 0
  rw [IntermediateField.relfinrank_eq_finrank_of_le h]
  have hext : IntermediateField.extendScalars h = IntermediateField.adjoin E (chartGens P' u) := by
    rw [← IntermediateField.extendScalars_adjoin (h.trans hκ'.le)]
    exact IntermediateField.ext fun x =>
      show x ∈ κ' ↔ x ∈ IntermediateField.adjoin F (chartGens P' u) by rw [hκ']
  rw [hext]
  exact Module.finrank_pos.ne'

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PMChartTrdeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

namespace MChartTrdeg

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

theorem chartMonomial_isMultiHomog (u : ∀ k, ι k) (b : K → ℕ) :
    IsMultiHomog (chartMonomial (F := F) u b) b := by
  have h := IsWeightedHomogeneous.prod (R := F) (w := blockWeight ι) Finset.univ
    (fun k => (X ⟨k, u k⟩ : MRing ι F) ^ b k) (fun k => b k • blockWeight ι ⟨k, u k⟩)
    (fun k _ => (isWeightedHomogeneous_X F _ _).pow (b k))
  have hb : ∑ k, b k • blockWeight ι ⟨k, u k⟩ = b := by
    funext j
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  unfold IsMultiHomog chartMonomial
  rwa [hb] at h

variable (P : Ideal (MRing ι F)) [P.IsPrime]


omit [Fintype K] [DecidableEq K] [P.IsPrime] in
theorem map_eq_zero_iff (f : MRing ι F) :
    algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) = 0 ↔ f ∈ P := by
  rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]


omit [DecidableEq K] [P.IsPrime] in
theorem map_chartMonomial (u : ∀ k, ι k) (b : K → ℕ) :
    algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (chartMonomial u b)) =
      ∏ k, algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
        (Ideal.Quotient.mk P (X ⟨k, u k⟩)) ^ b k := by
  simp [chartMonomial, map_prod, map_pow]


omit [DecidableEq K] in
theorem map_chartMonomial_ne_zero (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P)
    (b : K → ℕ) :
    algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
      (Ideal.Quotient.mk P (chartMonomial u b)) ≠ 0 := by
  rw [map_chartMonomial]
  exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ fun h => hu k ((map_eq_zero_iff P _).1 h)

theorem algebraicIndependent (hH : MChartHomog.Statement.{u}) (hP : IsMultiHomogIdeal P)
    (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) :
    AlgebraicIndependent (chartMap P u).range (fun k => algebraMap (MRing ι F ⧸ P)
      (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (X ⟨k, u k⟩))) := by
  classical
  set L := FractionRing (MRing ι F ⧸ P)
  set φ : MRing ι F →+* L := (algebraMap (MRing ι F ⧸ P) L).comp (Ideal.Quotient.mk P) with hφ
  have hφapp : ∀ f, φ f = algebraMap (MRing ι F ⧸ P) L (Ideal.Quotient.mk P f) := fun _ => rfl
  rw [algebraicIndependent_iff]
  intro p hp

  have hq : ∀ m, ∃ q, chartMap P u q = ((p.coeff m : (chartMap P u).range) : L) := fun m => (p.coeff m).2
  choose q hq using hq
  choose b h hhom heq using fun m => hH F K ι u (q m)
  have hval : ∀ m, φ (h m) = ((p.coeff m : (chartMap P u).range) : L) * φ (chartMonomial u (b m)) := by
    intro m
    have := heq m P hu
    rw [hq m, eq_div_iff (map_chartMonomial_ne_zero P u hu _)] at this
    rw [hφapp, hφapp]
    exact this.symm
  set s := p.support
  set N : K → ℕ := ∑ m ∈ s, b m
  have hbN : ∀ m ∈ s, ∀ k, b m k ≤ N k := fun m hm =>
    Finset.single_le_sum (f := b) (fun _ _ _ => Nat.zero_le _) hm
  set c : (K →₀ ℕ) → K → ℕ := fun m => N - b m + ⇑m
  have hbc : ∀ m ∈ s, b m + c m = N + ⇑m := by
    intro m hm
    funext k
    have := hbN m hm k
    simp only [c, Pi.add_apply, Pi.sub_apply]
    omega

  set G := ∑ m ∈ s, h m * chartMonomial u (c m)
  have hG : G ∈ P := by
    rw [← map_eq_zero_iff, ← hφapp]
    have hp' := hp
    rw [aeval_def, eval₂_eq'] at hp'
    calc φ G = ∑ m ∈ s, φ (chartMonomial u N) * (algebraMap (chartMap P u).range L (p.coeff m) *
          ∏ k, algebraMap (MRing ι F ⧸ P) L (Ideal.Quotient.mk P (X ⟨k, u k⟩)) ^ m k) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [G, map_sum, map_mul, hval]
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [hφapp (chartMonomial u (b m)), hφapp (chartMonomial u (c m)), hφapp (chartMonomial u N),
            map_chartMonomial, map_chartMonomial, map_chartMonomial]
          have e : ∀ x : K → L, (∏ k, x k ^ b m k) * (∏ k, x k ^ c m k) =
              (∏ k, x k ^ N k) * ∏ k, x k ^ m k := by
            intro x
            rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
            refine Finset.prod_congr rfl fun k _ => ?_
            rw [← pow_add, ← pow_add]
            exact congrArg (x k ^ ·) (congrFun (hbc m hm) k)
          rw [mul_assoc, e, mul_left_comm]
          rfl
      _ = 0 := by rw [← Finset.mul_sum, hp', mul_zero]

  have hhomt : ∀ m ∈ s, IsMultiHomog (h m * chartMonomial u (c m)) (N + ⇑m) := by
    intro m hm
    unfold IsMultiHomog
    rw [← hbc m hm]
    exact IsWeightedHomogeneous.mul (hhom m) (chartMonomial_isMultiHomog u (c m))
  have hcomp : ∀ m ∈ s,
      weightedHomogeneousComponent (blockWeight ι) (N + ⇑m) G = h m * chartMonomial u (c m) := by
    intro m hm
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [G, map_sum]
    rw [Finset.sum_eq_single m]
    · exact IsWeightedHomogeneous.weightedHomogeneousComponent_same (hhomt m hm)
    · intro m' hm' hne
      exact IsWeightedHomogeneous.weightedHomogeneousComponent_ne (N + ⇑m) (hhomt m' hm')
        fun e => hne (DFunLike.coe_injective (add_left_cancel e)).symm
    · intro hms
      exact absurd hm hms

  have hzero : ∀ m ∈ s, p.coeff m = 0 := by
    intro m hm
    have hmem : h m * chartMonomial u (c m) ∈ P := hcomp m hm ▸ hP G hG (N + ⇑m)
    have hcm : chartMonomial u (c m) ∉ P := fun h' =>
      map_chartMonomial_ne_zero P u hu (c m) ((map_eq_zero_iff P _).2 h')
    have hh : h m ∈ P := (Ideal.IsPrime.mem_or_mem ‹_› hmem).resolve_right hcm
    have h2 := hval m
    rw [hφapp, (map_eq_zero_iff P _).2 hh, eq_comm, mul_eq_zero] at h2
    rcases h2 with h2 | h2
    · exact Subtype.ext h2
    · exact absurd h2 (map_chartMonomial_ne_zero P u hu (b m))
  ext m
  by_contra hne
  exact hne (by simpa using hzero m (mem_support_iff.2 (by simpa using hne)))


omit [Fintype K] [DecidableEq K] in
theorem isAlgebraic_adjoin (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) :
    Algebra.IsAlgebraic (Algebra.adjoin (chartMap P u).range (Set.range fun k =>
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (X ⟨k, u k⟩))))
      (FractionRing (MRing ι F ⧸ P)) := by
  set_option synthInstance.maxHeartbeats 200000 in
    set R := MRing ι F ⧸ P
    set L := FractionRing R
    set A₀ := (chartMap P u).range
    set S' := Algebra.adjoin A₀ (Set.range fun k => algebraMap R L (Ideal.Quotient.mk P (X ⟨k, u k⟩)))
    have hξS : ∀ v, algebraMap R L (Ideal.Quotient.mk P (X v)) ∈ S' := by
      intro v
      have hr : chartMap P u (X v) ∈ A₀ := AlgHom.mem_range_self _ _
      have hne : algebraMap R L (Ideal.Quotient.mk P (X ⟨v.1, u v.1⟩)) ≠ 0 :=
        fun h => hu v.1 ((map_eq_zero_iff P _).1 h)
      have e : algebraMap R L (Ideal.Quotient.mk P (X v)) =
          chartMap P u (X v) * algebraMap R L (Ideal.Quotient.mk P (X ⟨v.1, u v.1⟩)) := by
        simp only [chartMap, aeval_X]
        exact (div_mul_cancel₀ _ hne).symm
      rw [e]
      exact S'.mul_mem (S'.algebraMap_mem (⟨_, hr⟩ : A₀)) (Algebra.subset_adjoin ⟨v.1, rfl⟩)
    have hRS : ∀ r : R, algebraMap R L r ∈ S' := by
      intro r
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective r
      induction f using MvPolynomial.induction_on with
      | C c =>
        rw [show (Ideal.Quotient.mk P (C c) : R) = algebraMap F R c from rfl,
          ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply F A₀ L]
        exact S'.algebraMap_mem _
      | add f g hf hg => rw [map_add (f := _), map_add (f := _)]; exact S'.add_mem hf hg
      | mul_X f i hf => rw [map_mul, map_mul]; exact S'.mul_mem hf (hξS i)
    let _ : CommRing S' := Subalgebra.toCommRing S'
    refine ⟨fun x => ?_⟩
    obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := R) x
    have hd0 : algebraMap R L d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
    refine ⟨Polynomial.C (⟨_, hRS d⟩ : S') * Polynomial.X - Polynomial.C (⟨_, hRS a⟩ : S'),
      fun h => hd0 ?_, ?_⟩
    · have := congrArg (fun p : Polynomial S' => p.coeff 1) h
      simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, ↓reduceIte,
        one_ne_zero, Polynomial.coeff_zero] at this
      have h' := congrArg Subtype.val this
      simp only [Subalgebra.coe_zero, sub_zero] at h'
      exact h'
    · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
      show algebraMap R L d * (algebraMap R L a / algebraMap R L d) - algebraMap R L a = 0
      rw [mul_comm, div_mul_cancel₀ _ hd0, sub_self]

end MChartTrdeg

theorem MChartTrdeg.proof (hH : MChartHomog.Statement.{u}) : MChartTrdeg.Statement.{u} := by
  intro F _ K _ _ ι _ P _ hP u hu
  set R := MRing ι F ⧸ P
  set L := FractionRing R
  set A₀ := (chartMap P u).range
  have hb : IsTranscendenceBasis A₀ (fun k => algebraMap R L (Ideal.Quotient.mk P (X ⟨k, u k⟩))) :=
    (MChartTrdeg.algebraicIndependent P hH hP u hu).isTranscendenceBasis_iff_isAlgebraic.mpr
      (MChartTrdeg.isAlgebraic_adjoin P u hu)
  have h1 : Algebra.trdeg A₀ L = Fintype.card K := by
    simpa using hb.lift_cardinalMk_eq_trdeg.symm
  have : FaithfulSMul A₀ L :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  have : FaithfulSMul F A₀ :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap F A₀).injective
  rw [show Algebra.trdeg F (MRing ι F ⧸ chartIdeal P u) = Algebra.trdeg F A₀ from
      (Ideal.quotientKerEquivRange (chartMap P u)).trdeg_eq, ← h1, trdeg_add_eq F A₀ (A := L),
    GroundTheory.Arith.Abelian.Jacobian.trdeg_eq_of_isFractionRing (k := F) (A := R) L]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConePolyLocalization
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR IsLocalRing

noncomputable section

universe u


set_option maxHeartbeats 400000 in
theorem ConePolyLocalization.proof (h₀ : DegZeroLocLocal.Statement.{u}) (h₁ : ConeVarUnit.Statement.{u})
    (h₂ : ConeVarSurj.Statement.{u}) (h₃ : ConeVarInj.Statement.{u}) :
    ConePolyLocalization.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW v hv
  have := hP.isPrime
  have := hW.isPrime
  have hA : IsLocalRing (degZeroLoc P {W}) := h₀ F K ι P hP W hW hPW
  refine ⟨hA, ?_⟩
  let _ := (coneVarMap P W hPW v).toRingHom.toAlgebra
  have := isPrime_map_C_mvPolynomial K (maximalIdeal (degZeroLoc P {W}))
  have hQ : ∀ q : MvPolynomial K (degZeroLoc P {W}),
      q ∈ ((maximalIdeal (degZeroLoc P {W})).map
        (C : degZeroLoc P {W} →+* MvPolynomial K _)).primeCompl ↔ ∃ e, IsUnit (q.coeff e) := by
    intro q
    rw [Ideal.mem_primeCompl_iff, mem_map_C_iff]
    push Not
    simp only [mem_maximalIdeal, mem_nonunits_iff, not_not]
  refine (isLocalization_iff _ _).mpr ⟨fun y => ?_, fun z => ?_, fun {x y} hxy => ?_⟩
  · obtain ⟨e, he⟩ := (hQ y).mp y.2
    exact h₁ F K ι P hP W hW hPW v hv y e he
  · obtain ⟨p, q, e, he, hz⟩ := h₂ F K ι P hP W hW hPW v hv z
    exact ⟨⟨p, ⟨q, (hQ q).mpr ⟨e, he⟩⟩⟩, hz⟩
  · refine ⟨1, ?_⟩
    rw [h₃ F K ι P hP W hW hPW v hv hxy]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocUnits
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem DegZeroLocUnits.proof : DegZeroLocUnits.Statement.{u} := by
  intro F _ K _ _ ι _ P hP 𝒲 h𝒲ne h𝒲
  have := hP.isPrime
  have hne : ∀ g : MRing ι F, g ∉ P →
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P g) ≠ 0 :=
    fun g hg => by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact hg
  intro x hx
  constructor
  · rintro ⟨y, hy, hxy⟩ W hW
    exact ⟨y, degZeroLoc_anti P (Set.singleton_subset_iff.mpr hW) hy, hxy⟩
  · intro h
    obtain ⟨b, f, g, hf, hg, hgP, hgW, hx'⟩ :=
      DegZeroLocQuot.proof F K ι P 𝒲 (fun W hW => (h𝒲 W hW).1.isPrime) x hx
    by_cases hfW : ∃ W ∈ 𝒲, f ∈ W
    ·
      exfalso
      obtain ⟨W, hW, hfW⟩ := hfW
      have hWp : W.IsPrime := (h𝒲 W hW).1.isPrime
      obtain ⟨y, hy, hxy⟩ := h W hW
      obtain ⟨b', f', g', -, -, hg'P, hg'W, hy'⟩ := DegZeroLocQuot.proof F K ι P {W}
        (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact hWp) y hy
      rw [hx', hy', div_mul_div_comm,
        div_eq_one_iff_eq (mul_ne_zero (hne g hgP) (hne g' hg'P)), ← map_mul, ← map_mul,
        ← map_mul, ← map_mul] at hxy
      have h2 := Ideal.Quotient.eq.mp (IsFractionRing.injective _ _ hxy)
      have h3 : g * g' ∈ W := by
        have := W.sub_mem (W.mul_mem_right f' hfW) ((h𝒲 W hW).2 h2)
        rwa [sub_sub_cancel] at this
      rcases hWp.mem_or_mem h3 with h4 | h4
      exacts [hgW W hW h4, hg'W W (Set.mem_singleton W) h4]
    ·
      push Not at hfW
      obtain ⟨W₀, hW₀⟩ := h𝒲ne
      have hfP : f ∉ P := fun h' => hfW W₀ hW₀ ((h𝒲 W₀ hW₀).2 h')
      refine ⟨_, div_mem_degZeroLoc P 𝒲 hg hf hfP hfW, ?_⟩
      rw [hx', div_mul_div_comm, mul_comm (algebraMap _ _ _),
        div_self (mul_ne_zero (hne g hgP) (hne f hfP))]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocLocalize
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem DegZeroLocLocalize.proof : DegZeroLocLocalize.Statement.{u} := by
  intro F _ K _ _ ι _ P hP 𝒲 h𝒲 h𝒲P
  have := hP.isPrime
  intro W hW y hy
  have hWp := h𝒲P W hW
  have : W.IsPrime := hWp.1.isPrime
  obtain ⟨c, f, g, hf, hg, hgP, hgW, rfl⟩ :=
    DegZeroLocQuot.proof F K ι P {W} (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact this)
      y hy
  have hgW' : g ∉ W := hgW W rfl
  obtain ⟨e, h, hh, hce, hhS⟩ := exists_form_avoid_primes (insert P h𝒲.toFinset)
    (fun W' hW' => by
      rcases Finset.mem_insert.mp hW' with rfl | hW'
      · exact ⟨hP.isPrime, hP.multiHomog, hP.relevant⟩
      · have h' := (h𝒲P W' (h𝒲.mem_toFinset.mp hW')).1
        exact ⟨h'.isPrime, h'.multiHomog, h'.relevant⟩) c
  have hhP : h ∉ P := hhS P (Finset.mem_insert_self _ _)
  have hh𝒲 : ∀ W' ∈ 𝒲, h ∉ W' := fun W' hW' =>
    hhS W' (Finset.mem_insert_of_mem (h𝒲.mem_toFinset.mpr hW'))
  obtain ⟨m, hm, hmW⟩ := exists_form_not_mem_of_isRelevant (H := W) hWp.1.relevant (e - c)
  have hfm : IsMultiHomog (f * m) e := by
    have := IsWeightedHomogeneous.mul hf hm
    rwa [add_tsub_cancel_of_le hce] at this
  have hgm : IsMultiHomog (g * m) e := by
    have := IsWeightedHomogeneous.mul hg hm
    rwa [add_tsub_cancel_of_le hce] at this
  have hgmW : g * m ∉ W := fun h' => (this.mem_or_mem h').elim hgW' hmW
  have hgmP : g * m ∉ P := fun h' => hgmW (hWp.2 h')
  have hq0 : ∀ a : MRing ι F, a ∉ P →
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P a) ≠ 0 :=
    fun a ha => by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact ha
  refine ⟨_, div_mem_degZeroLoc P 𝒲 hfm hh hhP hh𝒲, _, div_mem_degZeroLoc P 𝒲 hgm hh hhP hh𝒲,
    ⟨_, div_mem_degZeroLoc P {W} hh hgm hgmP (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact hgmW),
      ?_⟩, ?_⟩
  · rw [div_mul_div_comm, mul_comm, div_self (mul_ne_zero (hq0 _ hhP) (hq0 _ hgmP))]
  · have h1 := hq0 _ hgP
    have h2 := hq0 _ hhP
    simp only [map_mul]
    field_simp

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end
