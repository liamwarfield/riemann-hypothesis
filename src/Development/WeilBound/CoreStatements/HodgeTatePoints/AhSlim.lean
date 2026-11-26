module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ArithIntersectionSystemOfPoincareLelong
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PIntCoordChange
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PIntCoordGeoNum
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcLinPrimeLe
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinPrimeCut
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedExceptionalChart
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedExceptionalLeadingForm
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GraphStatementHolds
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KleimanNefCriteriaHold
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SiuInequalityIntegralHolds
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsFormOfMemChartRingZ
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.EmbeddingPiecesOfIntersectionAndResolution
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.GrassmannHeightZ2OfInputsAndZ2
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodReductionDvrModelExists
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinalTheoremOfInputsRight
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DeepStROfVolume
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateOfFarguesExact
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.QuotientByFiniteFlatOfFreeQuotient
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FreeQuotientSchemeHolds
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ResKOfResolutionPrincipalisation
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PtsIntegralConjLineEq
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GagaSections
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PackingStatement
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PtsIntegralCurveConst

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PoincareLelongOfInv
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HorizontalDivSuppTwist
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HorizontalDivSuppTwist
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

namespace GlobalTheory.CompanionTheory.Ar.Tw

theorem twist_sup_span_le {K : Type} {ι : K → Type} (p : ℕ) {P W : Ideal (MRing ι)}
    {s : MRing ι} (h : P ⊔ Ideal.span {s} ≤ W) :
    twist p P ⊔ Ideal.span {(inc s : MRing (Tb ι))} ≤ twist p W := by
  refine sup_le (sup_le ?_ le_sup_right) ?_
  · exact (Ideal.map_mono (le_sup_left.trans h)).trans le_sup_left
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (h (Ideal.mem_sup_right
      (Ideal.mem_span_singleton_self s))))

theorem sup_span_le_comap_inc {K : Type} {ι : K → Type} (p : ℕ) {P : Ideal (MRing ι)}
    {s : MRing ι} {Q : Ideal (MRing (Tb ι))}
    (h : twist p P ⊔ Ideal.span {(inc s : MRing (Tb ι))} ≤ Q) :
    P ⊔ Ideal.span {s} ≤ Q.comap inc := by
  refine sup_le ?_ ?_
  · exact Ideal.map_le_iff_le_comap.mp ((le_sup_left.trans le_sup_left).trans h)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact h (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))

theorem twist_le_of_map_le {K : Type} {ι : K → Type} (p : ℕ) {P W : Ideal (MRing ι)}
    {s : MRing ι} {Q : Ideal (MRing (Tb ι))}
    (h : twist p P ⊔ Ideal.span {(inc s : MRing (Tb ι))} ≤ Q) (hW : W ≤ Q.comap inc) :
    twist p W ≤ Q :=
  sup_le (Ideal.map_le_iff_le_comap.mpr hW) ((le_sup_right.trans le_sup_left).trans h)

theorem horizontal_divSupp_twist (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ)
    (P : Ideal (MRing ι)) (s : MRing ι)
    (hp : ∀ W, W ∈ divSupp P s → IsHorizontal W → (twist p W).IsPrime) :
    {W' | W' ∈ divSupp (twist p P) (inc s) ∧ IsHorizontal W'} =
      twist p '' {W | W ∈ divSupp P s ∧ IsHorizontal W} := by
  ext W'
  constructor
  · rintro ⟨⟨hmin, hrel⟩, hhor⟩
    have hprime : W'.IsPrime := hmin.1.1
    have hle := hmin.1.2
    have hc : P ⊔ Ideal.span {s} ≤ W'.comap inc := sup_span_le_comap_inc p hle
    have : (W'.comap inc).IsPrime := Ideal.comap_isPrime _ _
    obtain ⟨W0, hW0, hW0le⟩ := Ideal.exists_minimalPrimes_le hc
    have hrel0 : IsRelevant W0 := by
      intro k
      obtain ⟨i, hi⟩ := hrel (some k)
      refine ⟨i, fun h => hi ?_⟩
      have := hW0le h
      simpa [inc, oldIdx] using this
    have hhor0 : IsHorizontal W0 := by
      rw [IsHorizontal, eq_bot_iff] at hhor ⊢
      intro n hn
      refine hhor ?_
      have h1 : (C n : MRing ι) ∈ W'.comap inc := hW0le hn
      simpa [inc] using h1
    have hmem : W0 ∈ divSupp P s := ⟨hW0, hrel0⟩
    refine ⟨W0, ⟨hmem, hhor0⟩, ?_⟩
    have htw : twist p W0 ≤ W' := twist_le_of_map_le p hle hW0le
    exact le_antisymm htw (hmin.2 ⟨hp W0 hmem hhor0, twist_sup_span_le p hW0.1.2⟩ htw)
  · rintro ⟨W, ⟨⟨hmin, hrel⟩, hhor⟩, rfl⟩
    have hprime : W.IsPrime := hmin.1.1
    refine ⟨⟨⟨⟨hp W ⟨hmin, hrel⟩ hhor, twist_sup_span_le p hmin.1.2⟩, ?_⟩,
      isRelevant_twist p hprime.ne_top hrel⟩, isHorizontal_twist p hhor⟩
    rintro Q ⟨hQ, hQle⟩ hQtw
    have hcomap : Q.comap inc ≤ W := by
      have := Ideal.comap_mono (f := inc) hQtw
      rwa [comap_inc_twist] at this
    have := hQ
    have hW : W ≤ Q.comap inc :=
      hmin.2 ⟨Ideal.comap_isPrime _ _, sup_span_le_comap_inc p hQle⟩ hcomap
    exact twist_le_of_map_le p hQle hW

end GlobalTheory.CompanionTheory.Ar.Tw
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HorizontalDivSuppTwistStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.horizontal_divSupp_twist_eq_image : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (P : Ideal (MRing ι)) (s : MRing ι), (∀ W, W ∈ divSupp P s → IsHorizontal W → (twist p W).IsPrime) → {W' | W' ∈ divSupp (twist p P) (inc s) ∧ IsHorizontal W'} = twist p '' {W | W ∈ divSupp P s ∧ IsHorizontal W} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.horizontal_divSupp_twist | exact GlobalTheory.CompanionTheory.Ar.Tw.horizontal_divSupp_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.horizontal_divSupp_twist <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RingKrullDimTwistSucc
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RingKrullDimTwistSucc
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Tw

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def baseD (p : ℕ) (W : Ideal (MRing ι)) : (MRing ι ⧸ W) →+* (MRing (Tb ι) ⧸ twist p W) :=
  Ideal.Quotient.lift W ((Ideal.Quotient.mk (twist p W)).comp inc) fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha))

def baseP (p : ℕ) (W : Ideal (MRing ι)) :
    Polynomial (MRing ι ⧸ W) →+* (MRing (Tb ι) ⧸ twist p W) :=
  Polynomial.eval₂RingHom (baseD p W) (Ideal.Quotient.mk (twist p W) yN)

def quadP (p : ℕ) (W : Ideal (MRing ι)) : Polynomial (Polynomial (MRing ι ⧸ W)) :=
  Polynomial.X ^ 2 + Polynomial.C (Polynomial.C ((p : ℤ) : MRing ι ⧸ W) * Polynomial.X ^ 2)

theorem quadraticPolynomial_monic (p : ℕ) (W : Ideal (MRing ι)) : (quadP p W).Monic := by
  exact Polynomial.monic_X_pow_add_C _ two_ne_zero

theorem quadraticPolynomial_natDegree (p : ℕ) (W : Ideal (MRing ι)) [Nontrivial (MRing ι ⧸ W)] : (quadP p W).natDegree = 2 := by
  exact Polynomial.natDegree_X_pow_add_C

def coordA (p : ℕ) (W : Ideal (MRing ι)) : (Σ o, Tb ι o) → AdjoinRoot (quadP p W)
  | ⟨none, j⟩ => (![AdjoinRoot.root _, AdjoinRoot.of _ Polynomial.X] : Fin 2 → _) j
  | ⟨some k, i⟩ => AdjoinRoot.of _ (Polynomial.C (Ideal.Quotient.mk W (X ⟨k, i⟩)))

def toA (p : ℕ) (W : Ideal (MRing ι)) : MRing (Tb ι) →+* AdjoinRoot (quadP p W) :=
  (aeval (coordA p W) : MRing (Tb ι) →ₐ[ℤ] AdjoinRoot (quadP p W)).toRingHom

theorem toA_inc (p : ℕ) (W : Ideal (MRing ι)) (f : MRing ι) :
    toA p W (inc f) = AdjoinRoot.of _ (Polynomial.C (Ideal.Quotient.mk W f)) := by
  have h : (toA p W).comp inc =
      (AdjoinRoot.of (quadP p W)).comp (Polynomial.C.comp (Ideal.Quotient.mk W)) := by
    apply MvPolynomial.ringHom_ext'
    · exact RingHom.ext_int _ _
    · intro i
      simp only [RingHom.comp_apply, toA, inc, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X,
        aeval_X]
      rfl
  exact RingHom.congr_fun h f

theorem toA_xN (p : ℕ) (W : Ideal (MRing ι)) : toA p W xN = AdjoinRoot.root _ := by
  simp only [toA, xN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  rfl

theorem toA_yN (p : ℕ) (W : Ideal (MRing ι)) : toA p W yN = AdjoinRoot.of _ Polynomial.X := by
  simp only [toA, yN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
  rfl

theorem toA_quad (p : ℕ) (W : Ideal (MRing ι)) : toA p W (quad p) = 0 := by
  have h : AdjoinRoot.mk (quadP p W) (Polynomial.X ^ 2 +
      Polynomial.C (Polynomial.C ((p : ℤ) : MRing ι ⧸ W) * Polynomial.X ^ 2)) = 0 :=
    AdjoinRoot.mk_self
  set_option synthInstance.maxHeartbeats 200000 in
  simp only [map_add (f := _), map_pow, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C, map_intCast,
    Int.cast_natCast, map_natCast] at h
  have hC : toA p W (MvPolynomial.C (p : ℤ)) = (p : AdjoinRoot (quadP p W)) := by
    rw [map_natCast MvPolynomial.C p, map_natCast]
  simp only [quad, map_add (f := toA p W), map_mul, map_pow, toA_xN, toA_yN, hC]
  linear_combination h

theorem twist_le_ker_toA (p : ℕ) (W : Ideal (MRing ι)) : twist p W ≤ RingHom.ker (toA p W) := by
  unfold twist
  apply sup_le
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, RingHom.mem_ker, toA_inc, Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero,
      map_zero]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact (RingHom.mem_ker).2 (toA_quad p W)

def quotA (p : ℕ) (W : Ideal (MRing ι)) : (MRing (Tb ι) ⧸ twist p W) →+* AdjoinRoot (quadP p W) :=
  Ideal.Quotient.lift _ (toA p W) fun _ ha => twist_le_ker_toA p W ha

theorem quotA_mk (p : ℕ) (W : Ideal (MRing ι)) (f : MRing (Tb ι)) :
    quotA p W (Ideal.Quotient.mk _ f) = toA p W f := by
  exact Ideal.Quotient.lift_mk _ _ _

theorem baseD_mk (p : ℕ) (W : Ideal (MRing ι)) (f : MRing ι) :
    baseD p W (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ (inc f) := by
  exact Ideal.Quotient.lift_mk _ _ _

theorem baseP_C (p : ℕ) (W : Ideal (MRing ι)) (a : MRing ι ⧸ W) :
    baseP p W (Polynomial.C a) = baseD p W a := by
  simp [baseP]

theorem baseP_X (p : ℕ) (W : Ideal (MRing ι)) :
    baseP p W Polynomial.X = Ideal.Quotient.mk _ yN := by
  simp [baseP]

theorem quotA_baseP (p : ℕ) (W : Ideal (MRing ι)) (g : Polynomial (MRing ι ⧸ W)) :
    quotA p W (baseP p W g) = AdjoinRoot.of _ g := by
  have h : (quotA p W).comp (baseP p W) = AdjoinRoot.of (quadP p W) := by
    apply Polynomial.ringHom_ext
    · intro a
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [RingHom.comp_apply, baseP_C, baseD_mk, quotA_mk, toA_inc]
    · rw [RingHom.comp_apply, baseP_X, quotA_mk, toA_yN]
  exact RingHom.congr_fun h g

theorem baseMap_injective (p : ℕ) (W : Ideal (MRing ι)) [Nontrivial (MRing ι ⧸ W)] :
    Function.Injective (baseP p W) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro g hg
  have h0 : AdjoinRoot.of (quadP p W) g = 0 := by
    rw [← quotA_baseP, hg, map_zero]
  rw [← AdjoinRoot.mk_C, AdjoinRoot.mk_eq_zero] at h0
  obtain ⟨q, hq⟩ := h0
  by_cases hq0 : q = 0
  · rw [hq0, mul_zero, Polynomial.C_eq_zero] at hq
    exact hq
  · have h1 := congrArg Polynomial.natDegree hq
    rw [Polynomial.natDegree_C, (quadraticPolynomial_monic p W).natDegree_mul' hq0, quadraticPolynomial_natDegree] at h1
    omega

theorem mk_quad_eq_zero (p : ℕ) (W : Ideal (MRing ι)) :
    Ideal.Quotient.mk (twist p W) (quad p) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)

theorem baseMap_isIntegralElem_xN (p : ℕ) (W : Ideal (MRing ι)) :
    (baseP p W).IsIntegralElem (Ideal.Quotient.mk (twist p W) xN) := by
  refine ⟨quadP p W, quadraticPolynomial_monic p W, ?_⟩
  rw [← mk_quad_eq_zero p W]
  have hp : (Ideal.Quotient.mk (twist p W)) (MvPolynomial.C (p : ℤ)) =
      (p : MRing (Tb ι) ⧸ twist p W) := by
    rw [map_natCast MvPolynomial.C p, map_natCast]
  simp only [quadP, quad, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, map_mul, map_pow, map_add, baseP_X, map_intCast,
    Int.cast_natCast, hp, map_natCast, Polynomial.eval₂_natCast]

theorem baseMap_isIntegralElem_X (p : ℕ) (W : Ideal (MRing ι)) (q : Σ o, Tb ι o) :
    (baseP p W).IsIntegralElem (Ideal.Quotient.mk (twist p W) (X q)) := by
  obtain ⟨o, j⟩ := q
  cases o with
  | none =>
    revert j
    change ∀ j : Fin 2, _
    intro j
    fin_cases j
    · exact baseMap_isIntegralElem_xN p W
    · have h := RingHom.isIntegralElem_map (baseP p W) (x := Polynomial.X)
      rw [baseP_X] at h
      exact h
  | some k =>
    have h : Ideal.Quotient.mk (twist p W) (X ⟨some k, j⟩ : MRing (Tb ι)) =
        baseP p W (Polynomial.C (Ideal.Quotient.mk W (X ⟨k, j⟩))) := by
      rw [baseP_C, baseD_mk]
      simp [inc, oldIdx]
    rw [h]
    exact RingHom.isIntegralElem_map _

theorem baseMap_isIntegral (p : ℕ) (W : Ideal (MRing ι)) (b : MRing (Tb ι) ⧸ twist p W) :
    (baseP p W).IsIntegralElem b := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
  induction f using MvPolynomial.induction_on
  · rw [eq_intCast MvPolynomial.C, map_intCast, ← map_intCast (baseP p W)]
    exact RingHom.isIntegralElem_map _
  · rw [map_add (f := _)]
    exact RingHom.IsIntegralElem.add _ ‹_› ‹_›
  · rw [map_mul]
    exact RingHom.IsIntegralElem.mul _ ‹_› (baseMap_isIntegralElem_X p W _)

theorem ringKrullDim_twist (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ)
    (W : Ideal (MRing ι)) (hW : W.IsPrime) :
    ringKrullDim (MRing (Tb ι) ⧸ twist p W) = ringKrullDim (MRing ι ⧸ W) + 1 := by
  haveI : W.IsPrime := hW
  haveI : Nontrivial (MRing ι ⧸ W) := inferInstance
  haveI : IsNoetherianRing (MRing ι) :=
    inferInstanceAs (IsNoetherianRing (MvPolynomial ((k : K) × ι k) ℤ))
  letI : Algebra (Polynomial (MRing ι ⧸ W)) (MRing (Tb ι) ⧸ twist p W) := (baseP p W).toAlgebra
  haveI : Algebra.IsIntegral (Polynomial (MRing ι ⧸ W)) (MRing (Tb ι) ⧸ twist p W) :=
    ⟨fun b => baseMap_isIntegral p W b⟩
  rw [ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective (baseMap_injective p W),
    Polynomial.ringKrullDim_of_isNoetherianRing]

end GlobalTheory.CompanionTheory.Ar.Tw
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.RingKrullDimTwistSuccStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringKrullDim_twist_succ : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (W : Ideal (MRing ι)), W.IsPrime → ringKrullDim (MRing (Tb ι) ⧸ twist p W) = ringKrullDim (MRing ι ⧸ W) + 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.ringKrullDim_twist | exact GlobalTheory.CompanionTheory.Ar.Tw.ringKrullDim_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.ringKrullDim_twist <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistIsMultiHomogIdeal
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistIsMultiHomogIdeal
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Tw

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem oldIdx_injective {K : Type} {ι : K → Type} :
    Function.Injective (oldIdx (ι := ι)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  change (⟨some a, b⟩ : (o : Option K) × Tb ι o) = ⟨some c, d⟩ at h
  cases h
  rfl

theorem isMultiHomog_inc {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] {f : MRing ι} {a : K → ℕ}
    (hf : IsMultiHomog f a) :
    IsMultiHomog (inc f : MRing (Tb ι)) (fun o => o.elim 0 a) := by
  classical
  intro m hm o
  have hinj : Function.Injective (oldIdx (ι := ι)) := oldIdx_injective
  change m ∈ (MvPolynomial.rename oldIdx f).support at hm
  rw [MvPolynomial.support_rename_of_injective hinj, Finset.mem_image] at hm
  obtain ⟨m', hm', rfl⟩ := hm
  cases o with
  | none =>
    simp only [Option.elim_none]
    apply Finset.sum_eq_zero
    intro i _
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨q, hq⟩
    have h0 := congrArg (fun z : (o : Option K) × Tb ι o => z.1) hq
    simp [oldIdx] at h0
  | some k =>
    simp only [Option.elim_some]
    refine (Fintype.sum_equiv (show Tb ι (some k) ≃ ι k from Equiv.refl _) _
      (fun i => m' ⟨k, i⟩) (fun i => ?_)).trans (hf m' hm' k)
    exact Finsupp.mapDomain_apply_of_injective hinj m' ⟨k, i⟩

theorem sum_single_none {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] (j : Fin 2) (o : Option K) :
    ∑ i, (Finsupp.single (⟨none, j⟩ : Σ o, Tb ι o) 2) ⟨o, i⟩ = o.elim 2 (fun _ => 0) := by
  classical
  cases o with
  | none =>
    simp only [Option.elim_none]
    refine (Fintype.sum_equiv (show Tb ι none ≃ Fin 2 from Equiv.refl _) _
      (fun i : Fin 2 => (Finsupp.single (⟨none, j⟩ : Σ o, Tb ι o) 2) ⟨none, i⟩) (fun _ => rfl)).trans ?_
    rw [Fin.sum_univ_two]
    fin_cases j <;> simp [Finsupp.single_apply] <;>
      (intro h
       have h2 := eq_of_heq (Sigma.mk.inj_iff.mp h).2
       have h3 := congrArg (fun t : Fin 2 => (t : ℕ)) h2
       exact absurd h3 (by decide))
  | some k =>
    simp only [Option.elim_some]
    apply Finset.sum_eq_zero
    intro i _
    rw [Finsupp.single_apply, if_neg]
    intro h
    have h0 := congrArg (fun z : (o : Option K) × Tb ι o => z.1) h
    simp at h0

theorem isMultiHomog_quad {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] (p : ℕ) :
    IsMultiHomog (quad p : MRing (Tb ι)) (fun o => o.elim 2 (fun _ => 0)) := by
  classical
  intro m hm o
  have h1 : (xN ^ 2 : MRing (Tb ι)) =
      MvPolynomial.monomial (Finsupp.single (⟨none, (0 : Fin 2)⟩ : (o : Option K) × Tb ι o) 2) (1 : ℤ) := by
    simp only [xN, MvPolynomial.X_pow_eq_monomial]
  have h2 : (MvPolynomial.C (p : ℤ) * yN ^ 2 : MRing (Tb ι)) =
      MvPolynomial.monomial (Finsupp.single (⟨none, (1 : Fin 2)⟩ : (o : Option K) × Tb ι o) 2) (p : ℤ) := by
    simp only [yN, MvPolynomial.X_pow_eq_monomial, MvPolynomial.C_mul_monomial, mul_one]
  have hq : (quad p : MRing (Tb ι)) =
      MvPolynomial.monomial (Finsupp.single (⟨none, (0 : Fin 2)⟩ : (o : Option K) × Tb ι o) 2) (1 : ℤ) +
      MvPolynomial.monomial (Finsupp.single (⟨none, (1 : Fin 2)⟩ : (o : Option K) × Tb ι o) 2) (p : ℤ) := by
    unfold quad
    rw [h1, h2]
  rw [hq] at hm
  have hm2 := Finset.mem_union.mp (MvPolynomial.support_add hm)
  rcases hm2 with h | h
  · have h' := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset h)
    subst h'
    exact sum_single_none (ι := ι) 0 o
  · have h' := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset h)
    subst h'
    exact sum_single_none (ι := ι) 1 o

theorem isMultiHomogIdeal_twist (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ)
    (W : Ideal (MRing ι)) (hW : IsMultiHomogIdeal W) : IsMultiHomogIdeal (twist p W) := by
  obtain ⟨S, hS, rfl⟩ := hW
  refine ⟨(inc '' S) ∪ {quad p}, ?_, ?_⟩
  · rintro f (⟨g, hg, rfl⟩ | hf)
    · obtain ⟨a, ha⟩ := hS g hg
      exact ⟨_, isMultiHomog_inc ha⟩
    · rw [Set.mem_singleton_iff] at hf
      subst hf
      exact ⟨_, isMultiHomog_quad p⟩
  · rw [twist, Ideal.map_span, Ideal.span_union]

end GlobalTheory.CompanionTheory.Ar.Tw
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistIsMultiHomogIdealStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_isMultiHomogIdeal : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (W : Ideal (MRing ι)), IsMultiHomogIdeal W → IsMultiHomogIdeal (twist p W) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.isMultiHomogIdeal_twist | exact GlobalTheory.CompanionTheory.Ar.Tw.isMultiHomogIdeal_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.isMultiHomogIdeal_twist <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwLineSmoothConjInvariantGlue
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwLineSmoothConjInvariantGlue
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Tw.Lines

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem conj_contDiff {T : Type} [Fintype T] :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : T → ℂ => fun q => starRingEnd ℂ (z q)) :=
  contDiff_pi.2 fun q => Complex.conjCLE.contDiff.comp (contDiff_apply ℝ (fun _ => ℂ) q)

theorem oldPart_contDiff :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (basePart₂ : ((Σ o, Tb ι o) → ℂ) → (Σ k, ι k) → ℂ) :=
  contDiff_pi.2 fun _ => contDiff_apply ℝ (fun _ => ℂ) _

theorem chi_contDiffOn (p : ℕ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chi (ι := ι) p) {u | ∀ o, ∃ i, u ⟨o, i⟩ ≠ 0} := by
  have hx : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : (Σ o, Tb ι o) → ℂ => u ⟨none, (0 : Fin 2)⟩) := contDiff_apply ℝ (fun _ => ℂ) _
  have hy : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : (Σ o, Tb ι o) → ℂ => u ⟨none, (1 : Fin 2)⟩) := contDiff_apply ℝ (fun _ => ℂ) _
  have hnum : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : (Σ o, Tb ι o) → ℂ =>
      (u ⟨none, (0 : Fin 2)⟩ * (starRingEnd ℂ) (u ⟨none, (1 : Fin 2)⟩)).im) :=
    Complex.imCLM.contDiff.comp (hx.mul (Complex.conjCLE.contDiff.comp hy))
  have hden : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : (Σ o, Tb ι o) → ℂ =>
      ‖u ⟨none, (0 : Fin 2)⟩‖ ^ 2 + ‖u ⟨none, (1 : Fin 2)⟩‖ ^ 2) :=
    (hx.norm_sq ℝ).add (hy.norm_sq ℝ)
  have hq : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : (Σ o, Tb ι o) → ℂ =>
      (u ⟨none, (0 : Fin 2)⟩ * (starRingEnd ℂ) (u ⟨none, (1 : Fin 2)⟩)).im /
        (‖u ⟨none, (0 : Fin 2)⟩‖ ^ 2 + ‖u ⟨none, (1 : Fin 2)⟩‖ ^ 2))
      {u | ∀ o, ∃ i, u ⟨o, i⟩ ≠ 0} := by
    refine hnum.contDiffOn.div hden.contDiffOn fun u hu => ?_
    have h0 : 0 ≤ ‖u ⟨none, (0 : Fin 2)⟩‖ ^ 2 := by positivity
    have h1 : 0 ≤ ‖u ⟨none, (1 : Fin 2)⟩‖ ^ 2 := by positivity
    have key : ∀ j : Fin 2, u ⟨none, j⟩ ≠ 0 →
        ‖u ⟨none, (0 : Fin 2)⟩‖ ^ 2 + ‖u ⟨none, (1 : Fin 2)⟩‖ ^ 2 ≠ 0 := by
      intro j hj
      have hpos : 0 < ‖u ⟨none, j⟩‖ ^ 2 := by positivity
      have hj2 : j = 0 ∨ j = 1 := by fin_cases j <;> simp
      rcases hj2 with rfl | rfl <;> exact ne_of_gt (by linarith)
    obtain ⟨i, hi⟩ := hu none
    exact key i hi
  exact (contDiffOn_const.add (contDiffOn_const.mul hq))

theorem chi_conj (p : ℕ) (u : (Σ o, Tb ι o) → ℂ) :
    chi p (fun q => starRingEnd ℂ (u q)) = 1 - chi p u := by
  have him : ((starRingEnd ℂ) (u ⟨none, (0 : Fin 2)⟩) *
      (starRingEnd ℂ) ((starRingEnd ℂ) (u ⟨none, (1 : Fin 2)⟩))).im =
      -(u ⟨none, (0 : Fin 2)⟩ * (starRingEnd ℂ) (u ⟨none, (1 : Fin 2)⟩)).im := by
    rw [Complex.conj_conj, ← Complex.conj_im, map_mul, Complex.conj_conj]
  simp only [chi, RCLike.norm_conj, him]
  ring

theorem chi_vPlus (p : ℕ) (hp : p ≠ 0) (z : (Σ k, ι k) → ℂ) : chi p (glue z (vPlus p)) = 1 := by
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hp)
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg p)
  have e0 : glue z (vPlus p) ⟨none, (0 : Fin 2)⟩ = cRoot p := rfl
  have e1 : glue z (vPlus p) ⟨none, (1 : Fin 2)⟩ = 1 := rfl
  have hn : ‖cRoot p‖ ^ 2 = p := by
    rw [cRoot, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, hsq]
  have him : (cRoot p).im = Real.sqrt p := by simp [cRoot]
  rw [chi, e0, e1]
  simp only [map_one, mul_one, norm_one, one_pow, hn, him]
  have : ((p : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem chi_vMinus (p : ℕ) (hp : p ≠ 0) (z : (Σ k, ι k) → ℂ) : chi p (glue z (vMinus p)) = 0 := by
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hp)
  have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg p)
  have e0 : glue z (vMinus p) ⟨none, (0 : Fin 2)⟩ = -cRoot p := rfl
  have e1 : glue z (vMinus p) ⟨none, (1 : Fin 2)⟩ = 1 := rfl
  have hn : ‖cRoot p‖ ^ 2 = p := by
    rw [cRoot, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, hsq]
  have him : (cRoot p).im = Real.sqrt p := by simp [cRoot]
  rw [chi, e0, e1]
  simp only [map_one, mul_one, norm_one, one_pow, norm_neg, hn, Complex.neg_im, him]
  have : ((p : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem conj_ne {T : Type} {B : T → Type} {u : (Σ o, B o) → ℂ} {o : T} (h : ∃ i, u ⟨o, i⟩ ≠ 0) :
    ∃ i, (fun q => starRingEnd ℂ (u q)) ⟨o, i⟩ ≠ 0 := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, by simpa using hi⟩

theorem conjLine_smooth (A : HermLine ι) (hA : IsSmoothHerm A) : IsSmoothHerm (conjLine A) := by
  have hA' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A.h
      {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := hA
  exact hA'.comp (s := {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0})
    (conj_contDiff (T := Σ k, ι k)).contDiffOn fun z hz k => conj_ne (hz k)

theorem twLine_smooth (p : ℕ) (A : HermLine ι) (hA : IsSmoothHerm A) :
    IsSmoothHerm (twLine p A) := by
  have hA' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A.h
      {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := hA
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : (Σ o, Tb ι o) → ℂ => A.h (basePart₂ u)) {u | ∀ o, ∃ i, u ⟨o, i⟩ ≠ 0} :=
    ContDiffOn.comp (t := {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) hA' oldPart_contDiff.contDiffOn
      fun _ hu k => oldPart_ne hu k
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : (Σ o, Tb ι o) → ℂ => A.h fun q => starRingEnd ℂ (basePart₂ u q))
      {u | ∀ o, ∃ i, u ⟨o, i⟩ ≠ 0} :=
    ContDiffOn.comp (t := {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) hA'
      (conj_contDiff.comp oldPart_contDiff).contDiffOn
      fun _ hu k => conj_ne (oldPart_ne hu k)
  have l1 := h1.log fun u hu => (A.pos _ (oldPart_ne hu)).ne'
  have l2 := h2.log fun u hu => (A.pos _ fun k => conj_ne (oldPart_ne hu k)).ne'
  have hc := chi_contDiffOn (ι := ι) p
  have hE := (((hc.mul l1).add (((contDiffOn_const (c := (1 : ℝ))).sub hc).mul l2))).exp
  refine ContDiffOn.congr hE fun u hu => ?_
  change twH p A u = _
  have hu' : ∀ o, ∃ i, u ⟨o, i⟩ ≠ 0 := hu
  rw [twH, if_pos hu']

theorem twLine_conj (p : ℕ) (A : HermLine ι) : IsConjInvariantH (twLine p A) := by
  intro u
  change twH p A (fun q => starRingEnd ℂ (u q)) = twH p A u
  have hsame : (∀ o, ∃ i, (fun q => starRingEnd ℂ (u q)) ⟨o, i⟩ ≠ 0) ↔ ∀ o, ∃ i, u ⟨o, i⟩ ≠ 0 :=
    forall_congr' fun o => exists_congr fun i => by simp
  by_cases hu : ∀ o, ∃ i, u ⟨o, i⟩ ≠ 0
  · rw [twH, twH, if_pos (hsame.mpr hu), if_pos hu, chi_conj]
    have e1 : basePart₂ (fun q => starRingEnd ℂ (u q)) = fun q => starRingEnd ℂ (basePart₂ u q) := rfl
    have e2 : (fun q => starRingEnd ℂ (basePart₂ (fun q => starRingEnd ℂ (u q)) q)) = basePart₂ u := by
      funext q; simp [basePart₂]
    rw [e2, e1]
    congr 1
    ring
  · rw [twH, twH, if_neg (fun h => hu (hsame.mp h)), if_neg hu]

theorem glue_block {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) {v : Fin 2 → ℂ}
    (hv : v 1 ≠ 0) : ∀ o, ∃ i, glue z v ⟨o, i⟩ ≠ 0 := by
  intro o
  cases o with
  | none => exact ⟨(1 : Fin 2), hv⟩
  | some k => exact hz k

theorem twLine_vPlus (p : ℕ) (hp : p ≠ 0) (A : HermLine ι) (z : (Σ k, ι k) → ℂ)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : (twLine p A).h (glue z (vPlus p)) = A.h z := by
  change twH p A _ = _
  have hv : vPlus p 1 ≠ 0 := by simp [vPlus]
  have ho : basePart₂ (glue z (vPlus p)) = z := rfl
  rw [twH, if_pos (glue_block hz hv), chi_vPlus p hp, ho]
  simp only [one_mul, sub_self, zero_mul, add_zero]
  exact Real.exp_log (A.pos z hz)

theorem twLine_vMinus (p : ℕ) (hp : p ≠ 0) (A : HermLine ι) (z : (Σ k, ι k) → ℂ)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : (twLine p A).h (glue z (vMinus p)) = (conjLine A).h z := by
  change twH p A _ = A.h fun q => starRingEnd ℂ (z q)
  have hv : vMinus p 1 ≠ 0 := by simp [vMinus]
  have ho : basePart₂ (glue z (vMinus p)) = z := rfl
  rw [twH, if_pos (glue_block hz hv), chi_vMinus p hp, ho]
  simp only [zero_mul, sub_zero, one_mul, zero_add]
  exact Real.exp_log (A.pos _ fun k => conj_ne (hz k))

theorem twLine_main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (A : HermLine ι), p ≠ 0 → (IsSmoothHerm A → IsSmoothHerm (twLine p A)) ∧ (IsSmoothHerm A → IsSmoothHerm (conjLine A)) ∧ IsConjInvariantH (twLine p A) ∧ (∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (twLine p A).h (glue z (vPlus p)) = A.h z) ∧ (∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (twLine p A).h (glue z (vMinus p)) = (conjLine A).h z) :=
  fun _ _ _ _ p A hp => ⟨twLine_smooth p A, conjLine_smooth A, twLine_conj p A,
    twLine_vPlus p hp A, twLine_vMinus p hp A⟩

end GlobalTheory.CompanionTheory.Ar.Tw.Lines
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwLineSmoothConjInvariantGlueStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twLine_smooth_conjInvariant_glue : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (A : HermLine ι), p ≠ 0 → (IsSmoothHerm A → IsSmoothHerm (twLine p A)) ∧ (IsSmoothHerm A → IsSmoothHerm (conjLine A)) ∧ IsConjInvariantH (twLine p A) ∧ (∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (twLine p A).h (glue z (vPlus p)) = A.h z) ∧ (∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → (twLine p A).h (glue z (vMinus p)) = (conjLine A).h z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.Lines.twLine_main | exact GlobalTheory.CompanionTheory.Ar.Tw.Lines.twLine_main | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.Lines.twLine_main <;> assumption)
end
end

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Tw.Main
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory

theorem exists_prime_noRoot {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (S : Set (Ideal (MRing ι))) (hS : S.Finite) (h : ∀ W ∈ S, W.IsPrime ∧ IsHorizontal W) :
    ∃ p : ℕ, p.Prime ∧ ∀ W ∈ S, NoRoot p W := by
  classical
  have hbad : ∀ W ∈ S, {p : ℕ | p.Prime ∧ ∃ a b : MRing ι ⧸ W, b ≠ 0 ∧ a ^ 2 + (p : MRing ι ⧸ W) * b ^ 2 = 0}.Finite := by
    intro W hW
    obtain ⟨hp, hh⟩ := h W hW
    haveI := hp
    haveI : IsDomain (MRing ι ⧸ W) := Ideal.Quotient.isDomain W
    haveI : CharZero (MRing ι ⧸ W) := by
      refine ⟨fun a b hab => ?_⟩
      have h0 : (C (((a : ℤ) - (b : ℤ))) : MRing ι) ∈ W := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        simpa [sub_eq_zero] using hab
      have h1 : ((a : ℤ) - (b : ℤ)) ∈ W.comap (C : ℤ →+* MRing ι) := h0
      rw [show W.comap (C : ℤ →+* MRing ι) = ⊥ from hh, Ideal.mem_bot] at h1
      omega
    exact GlobalTheory.T.finite_primes_sum_squares_zero _ _ (Ideal.Quotient.mk W) Ideal.Quotient.mk_surjective
  have hfin : (⋃ W ∈ S, {p : ℕ | p.Prime ∧ ∃ a b : MRing ι ⧸ W, b ≠ 0 ∧ a ^ 2 + (p : MRing ι ⧸ W) * b ^ 2 = 0}).Finite :=
    hS.biUnion hbad
  obtain ⟨p, hp, hpn⟩ := (Nat.infinite_setOf_prime.diff hfin).nonempty
  refine ⟨p, hp, fun W hW a b hab => ?_⟩
  by_contra hb
  apply hpn
  refine Set.mem_biUnion hW ⟨hp, Ideal.Quotient.mk W a, Ideal.Quotient.mk W b, ?_, ?_⟩
  · rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  · have := Ideal.Quotient.eq_zero_iff_mem.mpr hab
    simpa using this

theorem isArithVar_twist {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {p : ℕ}
    {Q : Ideal (MRing ι)} {d : ℕ} (hQ : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar Q d) (hR : NoRoot p Q) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (twist p Q) d := by
  obtain ⟨hK, hM, hH, hd⟩ := hQ
  refine ⟨⟨none⟩, ⟨GlobalTheory.T.twist_isPrime_of_isPrime_of_noRoot K ι p Q hM.1 hR, GlobalTheory.T.twist_isMultiHomogIdeal K ι p Q hM.2.1,
    isRelevant_twist p hM.1.ne_top hM.2.2⟩, isHorizontal_twist p hH, ?_⟩
  haveI := hM.1
  rw [GlobalTheory.T.ringKrullDim_twist_succ K ι p Q hM.1, hd, Fintype.card_option, ← add_assoc]
  push_cast
  rfl

theorem inc_notMem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {p : ℕ}
    {Q : Ideal (MRing ι)} {s : MRing ι} (hs : s ∉ Q) : inc s ∉ twist p Q := fun h =>
  hs (by rw [← comap_inc_twist p Q]; exact h)

theorem oldIdx_injective {K : Type} {ι : K → Type} : Function.Injective (oldIdx (ι := ι)) := by
  rintro ⟨k, i⟩ ⟨k', i'⟩ h
  obtain rfl : k = k' := Option.some_injective _ (congrArg Sigma.fst h)
  have : i = i' := eq_of_heq (Sigma.mk.inj h).2
  rw [this]

theorem isMultiHomog_inc {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a) :
    IsMultiHomog (inc s) (fun o => match o with | none => 0 | some k => a k) := by
  classical
  intro m hm o
  simp only [inc, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hm
  rw [MvPolynomial.support_rename_of_injective oldIdx_injective] at hm
  obtain ⟨m0, hm0, rfl⟩ := Finset.mem_image.mp hm
  cases o with
  | none =>
    show ∑ i, (Finsupp.mapDomain oldIdx m0) ⟨none, i⟩ = 0
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.mapDomain_notin_range]
    rintro ⟨q, hq⟩
    cases hq
  | some k =>
    show ∑ i, (Finsupp.mapDomain oldIdx m0) ⟨some k, i⟩ = a k
    rw [← hs m0 hm0 k]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finsupp.mapDomain_apply_of_injective (f := oldIdx (ι := ι)) oldIdx_injective m0 ⟨k, i⟩

theorem isSectionOn_twist {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {p : ℕ}
    {Q : Ideal (MRing ι)} {A : HermLine ι} {s : MRing ι} (hs : IsSectionOn Q A s) :
    IsSectionOn (twist p Q) (twLine p A) (inc s) := by
  obtain ⟨a, ha, hh, hn⟩ := hs
  refine ⟨fun o => match o with | none => 0 | some k => a k, fun o => ?_, isMultiHomog_inc hh, inc_notMem hn⟩
  cases o with
  | none => rfl
  | some k => exact ha k

theorem embL_inj {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {v : Fin 2 → ℂ}
    (h1 : v 1 = 1) : Function.Injective (embL v : (((k : K) → ι k) → ℂ) → _) := by
  intro w w' h
  funext j
  have := congrFun h (fun o => match o with | none => (1 : Fin 2) | some k => j k)
  simpa [embL, h1] using this

theorem twist_integral (hI : PtsIntegrableStatement) (hD : PtsIndepStatement)
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {p : ℕ} (hp : p ≠ 0)
    {Q : Ideal (MRing ι)} {e : ℕ} {L : Fin e → HermLine ι} {A : HermLine ι} {s : MRing ι}
    (hQ : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar Q (e + 1)) (hR : NoRoot p Q) (hL : ∀ j, IsSmoothHerm (L j))
    (hA : IsSmoothHerm A) (hs : IsSectionOn Q A s) :
    ptsIntegral (twist p Q) (pot fun j => twLine p (L j)) (logNorm (twLine p A) (inc s)) =
      ptsIntegral Q (pot L) (logNorm A s) +
        ptsIntegral Q (pot fun j => conjLine (L j)) (logNorm (conjLine A) s) := by
  classical
  have hQ' : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (twist p Q) (e + 1) := isArithVar_twist hQ hR
  have hKne : Nonempty K := hQ.1
  have hF := fun B : HermLine ι => GlobalTheory.T.twLine_smooth_conjInvariant_glue K ι p B hp
  have hL' : ∀ j, IsSmoothHerm (twLine p (L j)) := fun j => (hF _).1 (hL j)
  have hA' : IsSmoothHerm (twLine p A) := (hF _).1 hA
  have hLc : ∀ j, IsSmoothHerm (conjLine (L j)) := fun j => (hF _).2.1 (hL j)
  have hAc : IsSmoothHerm (conjLine A) := (hF _).2.1 hA
  have hs' : IsSectionOn (twist p Q) (twLine p A) (inc s) := isSectionOn_twist hs
  have hsc : IsSectionOn Q (conjLine A) s := hs
  obtain ⟨Ψ, hΨ⟩ := goodProjExists (Option K) (Tb ι) (twist p Q) e hQ'
  have good : ∀ v : Fin 2 → ℂ, v 0 ^ 2 + (p : ℂ) * v 1 ^ 2 = 0 → v 1 ≠ 0 → IsGoodProj Q (pj v Ψ) := by
    intro v hv hv1 z hz
    have := hΨ _ (glue_mem_mcPts hz hv hv1)
    rw [segre_glue] at this
    exact this
  have v1p : vPlus p 1 = 1 := by simp [vPlus]
  have v1m : vMinus p 1 = 1 := by simp [vMinus]
  have gp := good _ (vPlus_root p) (by rw [v1p]; exact one_ne_zero)
  have gm := good _ (vMinus_root p) (by rw [v1m]; exact one_ne_zero)
  have atOf : ∀ {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {P : Ideal (MRing ι')}
      {Φ : (((k : K') → ι' k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {M : Fin e → HermLine ι'}
      {B : HermLine ι'} {t : MRing ι'}, ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (e + 1) → IsGoodProj P Φ →
      (∀ j, IsSmoothHerm (M j)) → IsSmoothHerm B → IsSectionOn P B t →
      ptsIntegral P (pot M) (logNorm B t) = ptsIntegralAt P Φ (pot M) (logNorm B t) := by
    intro K' _ ι' _ P Φ M B t h1 h2 h3 h4 h5
    have hex : ∃ Φ : (((k : K') → ι' k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Φ := ⟨Φ, h2⟩
    unfold ptsIntegral
    rw [dite_eq_left hex]
    exact hD K' ι' P e _ Φ M B t h1 hex.choose_spec h2 h3 h4 h5
  rw [atOf hQ' hΨ hL' hA' hs', atOf hQ gp hL hA hs, atOf hQ gm hLc hAc hsc]
  have sp := GlobalTheory.T.twist_height_integral_decomposition K ι p Q e Ψ (fun j => twLine p (L j)) (twLine p A) L A s (vPlus p) hp hQ hQ' hΨ hL' hA' hs'
    (Or.inl rfl) (fun j z hz => (hF _).2.2.2.1 z hz.1) (fun z hz => (hF _).2.2.2.1 z hz.1)
  have sm := GlobalTheory.T.twist_height_integral_decomposition K ι p Q e Ψ (fun j => twLine p (L j)) (twLine p A) (fun j => conjLine (L j)) (conjLine A) s
    (vMinus p) hp hQ hQ' hΨ hL' hA' hs' (Or.inr rfl) (fun j z hz => (hF _).2.2.2.2 z hz.1)
    (fun z hz => (hF _).2.2.2.2 z hz.1)
  have hae : ∀ᵐ y, (∑ᶠ w ∈ fibre (twist p Q) Ψ y, sheetDensity (twist p Q) Ψ (pot fun j => twLine p (L j)) (logNorm (twLine p A) (inc s)) y w) =
      (∑ᶠ w ∈ fibre Q (pj (vPlus p) Ψ) y, sheetDensity Q (pj (vPlus p) Ψ) (pot L) (logNorm A s) y w) +
      ∑ᶠ w ∈ fibre Q (pj (vMinus p) Ψ) y, sheetDensity Q (pj (vMinus p) Ψ) (pot fun j => conjLine (L j)) (logNorm (conjLine A) s) y w := by
    filter_upwards [sp, sm] with y hpl hmi
    have fpl := fibreFinite K ι Q e _ hQ gp y
    have fmi := fibreFinite K ι Q e _ hQ gm y
    have hdis : Disjoint (embL (vPlus p) '' fibre Q (pj (vPlus p) Ψ) y)
        (embL (vMinus p) '' fibre Q (pj (vMinus p) Ψ) y) := by
      rw [Set.disjoint_left]
      rintro _ ⟨w, hw, rfl⟩ ⟨w', hw', he⟩
      have hc : cRoot p ≠ 0 := by
        simp [cRoot, Real.sqrt_eq_zero', hp, Nat.pos_of_ne_zero hp]
      have hww : w' = w := by
        funext j
        have := congrFun he (fun o => match o with | none => (1 : Fin 2) | some k => j k)
        simpa [embL, v1p, v1m] using this
      subst hww
      have hz : w' = 0 := by
        funext j
        have := congrFun he (fun o => match o with | none => (0 : Fin 2) | some k => j k)
        simp only [embL, vPlus, vMinus, LinearMap.coe_mk, AddHom.coe_mk] at this
        have h2 : w' j * (2 * cRoot p) = 0 := by
          have h3 : w' j * (-cRoot p) = w' j * cRoot p := by simpa using this
          linear_combination -h3
        simpa [hc] using h2
      obtain ⟨z, -, -, h⟩ := hw
      rw [hz, map_zero] at h
      have := congrFun h 0
      simp at this
    rw [GlobalTheory.T.fibre_twist_eq_union_embeddings K ι p Q e Ψ y hp hKne hQ.2.1.2.1, finsum_mem_union hdis (fpl.image _) (fmi.image _),
      finsum_mem_image (embL_inj v1p).injOn, finsum_mem_image (embL_inj v1m).injOn]
    simp only [hpl, hmi]
  unfold ptsIntegralAt
  rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_add
    (hI K ι Q e _ L A s hQ gp hL hA hs) (hI K ι Q e _ _ _ s hQ gm hLc hAc hsc)]

theorem twist_double (hI : PtsIntegrableStatement) (hD : PtsIndepStatement)
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {p : ℕ} (hp : p ≠ 0)
    {Q : Ideal (MRing ι)} {e : ℕ} {L : Fin e → HermLine ι} {A : HermLine ι} {s : MRing ι}
    (hQ : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar Q (e + 1)) (hR : NoRoot p Q) (hL : ∀ j, IsSmoothHerm (L j))
    (hA : IsSmoothHerm A) (hs : IsSectionOn Q A s) :
    ptsIntegral (twist p Q) (pot fun j => twLine p (L j)) (logNorm (twLine p A) (inc s)) =
      2 * ptsIntegral Q (pot L) (logNorm A s) := by
  rw [twist_integral hI hD hp hQ hR hL hA hs, GlobalTheory.T.ptsIntegral_conjLine_eq hD K ι Q e L A s hQ hL hA hs]
  ring

theorem pot_cons {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    (B : HermLine ι) (L : Fin e → HermLine ι) :
    pot (Fin.cons B L : Fin (e + 1) → HermLine ι) =
      Fin.cons (fun z => Real.log (B.h z)) (pot L) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j <;> rfl

theorem tw_cons {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ} (p : ℕ)
    (B : HermLine ι) (L : Fin e → HermLine ι) :
    (fun j => twLine p ((Fin.cons B L : Fin (e + 1) → HermLine ι) j)) =
      (Fin.cons (twLine p B) (fun j => twLine p (L j)) : Fin (e + 1) → HermLine (Tb ι)) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j <;> rfl

theorem logNorm_inv_one {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (B : HermLine ι) : logNorm (invLine B) 1 = fun z => Real.log (B.h z) := by
  funext z
  simp [logNorm, invLine]

theorem logNorm_tw_inv_one {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (p : ℕ)
    (B : HermLine ι) : logNorm (twLine p (invLine B)) (inc 1) = fun z => Real.log ((twLine p B).h z) := by
  classical
  funext z
  have hh : (twLine p (invLine B)).h z = ((twLine p B).h z)⁻¹ := by
    show twH p (invLine B) z = (twH p B z)⁻¹
    unfold twH
    split_ifs with h
    · rw [← Real.exp_neg]
      congr 1
      simp only [invLine, Real.log_inv]
      ring
    · simp
  simp [logNorm, hh]

theorem isSectionOn_inv_one {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Q : Ideal (MRing ι)} (hQ : Q ≠ ⊤) {B : HermLine ι} (hB : B.a = 0) :
    IsSectionOn Q (invLine B) 1 := by
  refine ⟨0, fun k => by simp [invLine, hB], fun m hm k => ?_, fun h => hQ ((Ideal.eq_top_iff_one _).mpr h)⟩
  have : m = 0 := by
    by_contra h0
    classical
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one, if_neg (Ne.symm h0)] at hm
    exact hm rfl
  simp [this]

theorem isSmooth_inv {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {B : HermLine ι} (hB : IsSmoothHerm B) : IsSmoothHerm (invLine B) :=
  ContDiffOn.inv hB fun z hz => (B.pos z hz).ne'

theorem tw_cons_smooth {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    {B : HermLine ι} {L : Fin e → HermLine ι} (hB : IsSmoothHerm B) (hL : ∀ j, IsSmoothHerm (L j)) :
    ∀ j, IsSmoothHerm ((Fin.cons B L : Fin (e + 1) → HermLine ι) j) := fun j => by
  refine Fin.cases ?_ (fun i => ?_) j
  · exact hB
  · exact hL i

theorem poincareLelong_of_inv :
    ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GlobalTheory.CompanionTheory.Hypotheses₂.PoincareLelongInv →
      GlobalTheory.CompanionTheory.Ar.Pub.PoincareLelong := by
  intro hRK hInv K _ ι _ P n L A B s hP hL hA hB hBa hs
  classical
  have hI : PtsIntegrableStatement := GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegrable_of_resK hRK
  have hD : PtsIndepStatement := ptsIndep_of (GlobalTheory.T.resolution_exists_of_resolution_statement hRK) resBridge
  have hPp : P.IsPrime := hP.2.1.1
  set H : Set (Ideal (MRing ι)) := {W | W ∈ divSupp P s ∧ IsHorizontal W} with hH
  have hHfin : H.Finite := (divSupp_finite P s).subset fun W h => h.1
  have hHar : ∀ W ∈ H, ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W (n + 1) := fun W h =>
    (divSuppArith K ι P (n + 1) A s W hP hs h.1).1 h.2
  obtain ⟨p, hp, hpS⟩ := exists_prime_noRoot (insert P H) (hHfin.insert P) (by
    rintro W (rfl | hW)
    · exact ⟨hPp, hP.2.2.1⟩
    · exact ⟨(hHar W hW).2.1.1, hW.2⟩)
  have hp0 : p ≠ 0 := hp.ne_zero
  have hRP : NoRoot p P := hpS P (Set.mem_insert _ _)
  have hRW : ∀ W ∈ H, NoRoot p W := fun W h => hpS W (Set.mem_insert_of_mem _ h)
  have hF := fun C : HermLine ι => GlobalTheory.T.twLine_smooth_conjInvariant_glue K ι p C hp0
  have hP' : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (twist p P) (n + 2) := isArithVar_twist hP hRP
  have hInv' := hInv (Option K) (Tb ι) (twist p P) n (fun j => twLine p (L j)) (twLine p A) (twLine p B)
    (inc s) hP' (fun j => (hF _).1 (hL j)) ((hF _).1 hA) ((hF _).1 hB)
    (fun j => (hF _).2.2.1) (hF _).2.2.1 (hF _).2.2.1
    (by funext o; cases o with
        | none => rfl
        | some k => exact congrFun hBa k)
    (isSectionOn_twist hs)

  have e1 := twist_double hI hD hp0 (e := n + 1) (L := Fin.cons B L) (A := A) (s := s) hP hRP
    (tw_cons_smooth hB hL) hA hs
  rw [tw_cons, pot_cons, pot_cons] at e1
  have e3 := twist_double hI hD hp0 (e := n + 1) (L := Fin.cons A L) (A := invLine B) (s := 1) hP hRP
    (tw_cons_smooth hA hL) (isSmooth_inv hB) (isSectionOn_inv_one hPp.ne_top hBa)
  rw [tw_cons, pot_cons, pot_cons, logNorm_inv_one, logNorm_tw_inv_one] at e3
  have e2 : ∀ W ∈ H, ptsIntegral (twist p W) (pot fun j => twLine p (L j))
      (fun z => Real.log ((twLine p B).h z)) = 2 * ptsIntegral W (pot L) (fun z => Real.log (B.h z)) := by
    intro W hW
    have hWa := hHar W hW
    have := twist_double hI hD hp0 (e := n) (L := L) (A := invLine B) (s := 1) hWa (hRW W hW) hL
      (isSmooth_inv hB) (isSectionOn_inv_one hWa.2.1.1.ne_top hBa)
    rwa [logNorm_inv_one, logNorm_tw_inv_one] at this
  have hsup : twist p P ⊔ Ideal.span {inc s} =
      (P ⊔ Ideal.span {s}).map inc ⊔ Ideal.span {quad p} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, twist, sup_right_comm]
  have hdiv := GlobalTheory.T.horizontal_divSupp_twist_eq_image K ι p P s (fun W hW hh =>
    GlobalTheory.T.twist_isPrime_of_isPrime_of_noRoot K ι p W (hHar W ⟨hW, hh⟩).2.1.1 (hRW W ⟨hW, hh⟩))
  have hsum : (∑ᶠ (W') (_ : W' ∈ divSupp (twist p P) (inc s) ∧ IsHorizontal W'),
        (multAt (twist p P ⊔ Ideal.span {inc s}) W' : ℝ) *
          ptsIntegral W' (pot fun j => twLine p (L j)) (fun z => Real.log ((twLine p B).h z))) =
      2 * ∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
        (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) (fun z => Real.log (B.h z)) := by
    have h1 : (∑ᶠ (W') (_ : W' ∈ divSupp (twist p P) (inc s) ∧ IsHorizontal W'),
        (multAt (twist p P ⊔ Ideal.span {inc s}) W' : ℝ) *
          ptsIntegral W' (pot fun j => twLine p (L j)) (fun z => Real.log ((twLine p B).h z))) =
        ∑ᶠ W' ∈ {W' | W' ∈ divSupp (twist p P) (inc s) ∧ IsHorizontal W'},
        (multAt (twist p P ⊔ Ideal.span {inc s}) W' : ℝ) *
          ptsIntegral W' (pot fun j => twLine p (L j)) (fun z => Real.log ((twLine p B).h z)) := rfl
    have h2 : (∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
        (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) (fun z => Real.log (B.h z))) =
        ∑ᶠ W ∈ H, (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) (fun z => Real.log (B.h z)) := rfl
    rw [h1, h2, hdiv, finsum_mem_image (twist_injective p).injOn, mul_finsum_mem]
    refine finsum_mem_congr rfl fun W hW => ?_
    rw [e2 W hW, hsup, GlobalTheory.T.multAt_twist_quad_eq K ι p _ W hW.1.1 (GlobalTheory.T.twist_isPrime_of_isPrime_of_noRoot K ι p W (hHar W hW).2.1.1 (hRW W hW))]
    ring
  have hInv2 : ptsIntegral (twist p P)
      (Fin.cons (fun z => Real.log ((twLine p B).h z)) (pot fun j => twLine p (L j)))
      (logNorm (twLine p A) (inc s)) = _ := hInv'
  rw [e1, hsum, e3] at hInv2
  linarith

end GlobalTheory.CompanionTheory.Ar.Tw.Main
end
end

namespace PositivityTheory.HtPt.Ah

open GlobalTheory.CompanionTheory.Ar

theorem resK (h₁ : GlobalTheory.CompanionTheory.Hypotheses₂.ResolutionCharZero) (h₂ : GlobalTheory.CompanionTheory.Hypotheses₂.PrincipalisationCharZero) :
    ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement :=
  GlobalTheory.CompanionTheory.Hypotheses₂.ResKSide.resK_of_resolution_principalisation h₁ h₂

theorem ais (h₁ : GlobalTheory.CompanionTheory.Hypotheses₂.ResolutionCharZero) (h₂ : GlobalTheory.CompanionTheory.Hypotheses₂.PrincipalisationCharZero)
    (hPL : GlobalTheory.CompanionTheory.Hypotheses₂.PoincareLelongInv) : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement :=
  Pub.arithIntersectionSystem_of_poincareLelong_resK (Tw.Main.poincareLelong_of_inv (resK h₁ h₂) hPL) (resK h₁ h₂)

theorem quot : GR.QuotientByFiniteFlatStatement :=
  GR.QuotSide.quotientByFiniteFlat_of_freeQuotient GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuotientScheme_holds

end PositivityTheory.HtPt.Ah
