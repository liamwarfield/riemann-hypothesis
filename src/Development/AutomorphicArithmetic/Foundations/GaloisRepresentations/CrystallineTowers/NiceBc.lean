module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTower
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.NormLtOneOfIrreducible
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PIsoPts

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.NiceBc
noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory.GalV (HTower)
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.Seam

private theorem fEt_of_isPullback {P Y Z' Z : Scheme.{0}} {v : P ⟶ Y} {s' : P ⟶ Z'} {s : Y ⟶ Z} {g : Z' ⟶ Z} {d : ℕ}
    (h : IsPullback v s' s g) (hs : FEt s d) : FEt s' d := by
  refine ⟨MorphismProperty.of_isPullback (P := @IsFinite) h hs.1,
    MorphismProperty.of_isPullback (P := @Etale) h hs.2.1, ?_⟩
  intro K _ _ x
  rw [← hs.2.2 K (x ≫ g)]
  refine Nat.card_congr
    { toFun := fun y => ⟨y.1 ≫ v, by rw [Category.assoc, h.w, ← Category.assoc, y.2]⟩
      invFun := fun y => ⟨h.lift y.1 x (by rw [y.2]), h.lift_snd _ _ _⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro y
    apply Subtype.ext
    apply h.hom_ext
    · simp
    · simp [y.2]
  · intro y
    apply Subtype.ext
    simp

private theorem isPullback_sΩ {k : Type} [Field k] (H : HTower k) (K : Type) [Field K] [Algebra k K] (g : H.Γ) :
    IsPullback (pullback.fst (H.s g ≫ H.q) (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (H.sΩ K g) (H.s g)
      (pullback.fst H.q (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  have hfst : H.sΩ K g ≫ pullback.fst H.q (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      pullback.fst (H.s g ≫ H.q) (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫ H.s g :=
    pullback.lift_fst _ _ _
  have hsnd : H.sΩ K g ≫ pullback.snd H.q (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      pullback.snd (H.s g ≫ H.q) (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    pullback.lift_snd _ _ _
  refine IsPullback.of_bot (v₂₁ := pullback.snd H.q (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (v₂₂ := H.q)
    (h₃₁ := Spec.map (CommRingCat.ofHom (algebraMap k K))) ?_ hfst.symm (IsPullback.of_hasPullback _ _)
  rw [hsnd]
  exact IsPullback.of_hasPullback _ _

theorem niceBc : NiceBc := by
  intro k K _ _ τ H hN
  obtain ⟨hsm, hproj, hfet⟩ := hN
  letI : Algebra k K := τ.toAlgebra
  unfold bcAlong
  refine ⟨?_, ?_, ?_⟩
  · haveI := hsm
    show Smooth (pullback.snd H.q (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    infer_instance
  · exact GlobalTheory.ProjSpace.isProjOver_pullback_snd (algebraMap k K) hproj
  · intro g
    obtain ⟨d, hd⟩ := hfet g
    exact ⟨d, fEt_of_isPullback (isPullback_sΩ H K g) hd⟩

end UpperTheory.Gal.Seam

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.GoodOf
noncomputable section

open CategoryTheory Limits AlgebraicGeometry CrystallineSemistableComparison

namespace UpperTheory.Gal.Seam

section Ring

variable (O : Type) [CommRing O] (ϖ : O) (n : ℕ)

private abbrev chartI : Ideal (MvPolynomial (Fin (n + 1)) O) :=
  Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => (i : ℕ) < 1), MvPolynomial.X i) - MvPolynomial.C ϖ}

private theorem prod_one_branch :
    (∏ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => (i : ℕ) < 1), (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) O)) =
      MvPolynomial.X 0 := by
  have hs : Finset.univ.filter (fun i : Fin (n + 1) => (i : ℕ) < 1) = {0} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      ext
      simp only [Fin.val_zero]
      omega
    · rintro rfl
      simp
  rw [hs, Finset.prod_singleton]

private def evalFirst : MvPolynomial (Fin (n + 1)) O →+* MvPolynomial (Fin n) O :=
  (MvPolynomial.aeval (Fin.cons (MvPolynomial.C ϖ) MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin n) O)).toRingHom

private def toPoly : (MvPolynomial (Fin (n + 1)) O ⧸ chartI O ϖ n) →+* MvPolynomial (Fin n) O :=
  Ideal.Quotient.lift _ (evalFirst O ϖ n) (by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [prod_one_branch]
    simp [evalFirst])

private def fromPoly : MvPolynomial (Fin n) O →+* (MvPolynomial (Fin (n + 1)) O ⧸ chartI O ϖ n) :=
  (Ideal.Quotient.mk _).comp (MvPolynomial.rename Fin.succ : MvPolynomial (Fin n) O →ₐ[O] _).toRingHom

private theorem mk_X_zero :
    Ideal.Quotient.mk (chartI O ϖ n) (MvPolynomial.X 0) = Ideal.Quotient.mk (chartI O ϖ n) (MvPolynomial.C ϖ) := by
  rw [Ideal.Quotient.eq]
  apply Ideal.subset_span
  rw [prod_one_branch]
  rfl

private def chartEquiv : (MvPolynomial (Fin (n + 1)) O ⧸ chartI O ϖ n) ≃+* MvPolynomial (Fin n) O :=
  RingEquiv.ofRingHom (toPoly O ϖ n) (fromPoly O ϖ n)
    (by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
      · simp [toPoly, fromPoly, evalFirst]
      · simp [toPoly, fromPoly, evalFirst])
    (by
      refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_))
      · simp [toPoly, fromPoly, evalFirst]
      · refine Fin.cases ?_ (fun j => ?_) i
        · simp [toPoly, fromPoly, evalFirst, mk_X_zero]
        · simp [toPoly, fromPoly, evalFirst])

private theorem chartEquiv_algebraMap (o : O) :
    chartEquiv O ϖ n (algebraMap O _ o) = MvPolynomial.C o := by
  change toPoly O ϖ n (Ideal.Quotient.mk _ (MvPolynomial.C o)) = _
  simp [toPoly, evalFirst]

end Ring

theorem goodOf : GoodOf := by
  intro l _ K _ M hs hp
  refine ⟨hp, ?_⟩
  haveI : IsDiscreteValuationRing (OK l K) := OK_dvr
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (OK l K)
  refine ⟨ϖ, hϖ, fun x => ?_⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    M.X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let e := (Scheme.ΓSpecIso (CommRingCat.of (OK l K))).commRingCatIsoToRingEquiv
  have hsm : (M.p.appLE ⊤ V le_top).hom.Smooth :=
    M.p.smooth_appLE (isAffineOpen_top _) hV le_top
  let φ : OK l K →+* Γ(M.X, V) := (M.p.appLE ⊤ V le_top).hom.comp e.symm.toRingHom
  have hφ : φ.Smooth := RingHom.Smooth.propertyIsLocal.respectsIso.2 _ _ hsm
  algebraize [φ]
  obtain ⟨r, hrx, hr⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth (OK l K)
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have hxr : x ∈ M.X.basicOpen r := by
    have h1 : hV.primeIdealOf ⟨x, hxV⟩ ∈ hV.fromSpec ⁻¹ᵁ M.X.basicOpen r := by
      rw [hV.fromSpec_preimage_basicOpen]
      exact hrx
    have h2 : hV.fromSpec (hV.primeIdealOf ⟨x, hxV⟩) ∈ M.X.basicOpen r := h1
    rwa [hV.fromSpec_primeIdealOf] at h2
  have hstd : ((Scheme.ΓSpecIso (CommRingCat.of (OK l K))).inv ≫
      M.p.appLE ⊤ (M.X.basicOpen r) le_top).hom.IsStandardSmooth := by
    have := hV.isLocalization_basicOpen r
    rw [← RingHom.isStandardSmooth_algebraMap] at hr
    convert RingHom.isStandardSmooth_respectsIso.1 _
      (IsLocalization.algEquiv (.powers r) _ Γ(M.X, M.X.basicOpen r)).toRingEquiv hr
    ext a
    dsimp
    simp only [IsScalarTower.algebraMap_apply (OK l K) Γ(M.X, V) (Localization _),
      IsLocalization.map_eq]
    simp only [RingHom.algebraMap_toAlgebra, RingHomCompTriple.comp_apply,
      ← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]
    rw [AlgEquiv.commutes]
    first
      | (rw [CommRingCat.comp_apply, ← Scheme.Hom.appLE_map (V := V) M.p le_top
            (homOfLE (M.X.basicOpen_le r)).op, CommRingCat.comp_apply]; rfl)
      | (simp only [φ, e, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
            Iso.commRingCatIsoToRingEquiv_symm_apply, ← CommRingCat.comp_apply,
            ← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]; rfl)
  obtain ⟨k, g, hgC, hg⟩ := hstd.exists_etale_mvPolynomial
  refine ⟨M.X.basicOpen r, hV.basicOpen r, hxr, k + 1, 1, le_rfl, by omega,
    g.comp (chartEquiv (OK l K) ϖ k).toRingHom, ?_, ?_⟩
  · exact RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective (chartEquiv (OK l K) ϖ k).bijective) hg
  · rw [← hgC]
    ext a
    change g (chartEquiv (OK l K) ϖ k (algebraMap (OK l K) _ a)) = g (MvPolynomial.C a)
    congr 1
    exact chartEquiv_algebraMap (OK l K) ϖ k a

end UpperTheory.Gal.Seam
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.IntMap
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.Pst CrystallineSemistableComparison UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.Seam

section Place

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}

private theorem exists_den {x : E} (hx : w.valuation E x ≤ 1) :
    ∃ a b : 𝓞 E, b ∉ w.asIdeal ∧ x * algebraMap (𝓞 E) E b = algebraMap (𝓞 E) E a := by
  obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hd1 : algebraMap (𝓞 E) E d ≠ 0 := by simpa using hd0
  rw [map_div₀, div_le_one₀ (zero_lt_iff.2 (by simpa using hd1)), HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap] at hx
  set k := (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {d})).factors with hk
  have hv : w.intValuation d = WithZero.exp (-(k : ℤ)) := w.intValuation_if_neg hd0
  have h1 : d ∈ w.asIdeal ^ k := (w.intValuation_le_pow_iff_mem d k).1 hv.le
  have h2 : n ∈ w.asIdeal ^ k := (w.intValuation_le_pow_iff_mem n k).1 (hx.trans hv.le)
  have h3 : d ∉ w.asIdeal ^ (k + 1) := fun h => by
    have := (w.intValuation_le_pow_iff_mem d (k + 1)).2 h
    rw [hv, WithZero.exp_le_exp] at this
    push_cast at this
    omega
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h1)
  have h4 : ¬ J ≤ w.asIdeal := fun h => h3 <| by
    have : d ∈ Ideal.span {d} := Ideal.mem_span_singleton_self d
    rw [hJ] at this
    rw [pow_succ]
    exact Ideal.mul_mono_right h this
  obtain ⟨b, hbJ, hb⟩ := SetLike.not_le_iff_exists.1 h4
  have h5 : n * b ∈ Ideal.span {d} := hJ ▸ Ideal.mul_mem_mul h2 hbJ
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h5
  refine ⟨a, b, hb, ?_⟩
  rw [div_mul_eq_mul_div, div_eq_iff hd1, ← map_mul, ← map_mul, ha]

private theorem mem_of_int (a : 𝓞 E) : algebraMap E Ω (algebraMap (𝓞 E) E a) ∈ A := by
  have h : IsIntegral A (algebraMap E Ω (algebraMap (𝓞 E) E a)) :=
    ((RingOfIntegers.isIntegral_coe a).algebraMap (B := Ω)).tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [← hy]
  exact y.2

private theorem val_eq_one (hA : IsPlaceOver A w) {b : 𝓞 E} (hb : b ∉ w.asIdeal) :
    A.valuation (algebraMap E Ω (algebraMap (𝓞 E) E b)) = 1 :=
  le_antisymm ((A.valuation_le_one_iff _).2 (mem_of_int b)) (not_lt.1 fun h => hb ((hA b).1 h))

private theorem mem_of_le_one (hA : IsPlaceOver A w) {x : E} (hx : w.valuation E x ≤ 1) :
    algebraMap E Ω x ∈ A := by
  obtain ⟨a, b, hb, e⟩ := exists_den hx
  rw [← A.valuation_le_one_iff]
  have h := congrArg (fun y => A.valuation (algebraMap E Ω y)) e
  simp only [map_mul, val_eq_one hA hb, mul_one] at h
  rw [h]
  exact (A.valuation_le_one_iff _).2 (mem_of_int a)

private theorem val_lt_one (hA : IsPlaceOver A w) {x : E} (hx : w.valuation E x < 1) :
    A.valuation (algebraMap E Ω x) < 1 := by
  obtain ⟨a, b, hb, e⟩ := exists_den hx.le
  have hb1 : w.valuation E (algebraMap (𝓞 E) E b) = 1 :=
    le_antisymm (w.valuation_le_one b) (not_lt.1 fun h => hb ((w.valuation_lt_one_iff_mem b).1 h))
  have ha : a ∈ w.asIdeal := by
    rw [← w.valuation_lt_one_iff_mem (K := E)]
    change w.valuation E (algebraMap (𝓞 E) E a) < 1
    rw [← e, map_mul, hb1, mul_one]
    exact hx
  have h := congrArg (fun y => A.valuation (algebraMap E Ω y)) e
  simp only [map_mul, val_eq_one hA hb, mul_one] at h
  rw [h]
  exact (hA a).2 ha

private theorem le_one_of_mem (hA : IsPlaceOver A w) {x : E} (hx : algebraMap E Ω x ∈ A) :
    w.valuation E x ≤ 1 := by
  by_contra h
  have h1 : 1 < w.valuation E x := not_le.1 h
  have h0 : w.valuation E x ≠ 0 := (zero_lt_one.trans h1).ne'
  have h2 : w.valuation E x⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ h1
  have h3 := val_lt_one hA h2
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at h0
  have h4 : A.valuation (algebraMap E Ω x) ≠ 0 := by simpa using hx0
  rw [map_inv₀, map_inv₀, inv_lt_one₀ (zero_lt_iff.2 h4)] at h3
  exact absurd ((A.valuation_le_one_iff _).2 hx) (not_le.2 h3)

end Place

private theorem mem_OK_iff {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (x : ↥K) :
    x ∈ OK l K ↔ ‖(x : PadicAlgCl l)‖ ≤ 1 :=
  GroundTheory.PAdicHodge.mem_normInteger

private theorem isUnit_OK_iff {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (y : ↥(OK l K)) :
    IsUnit y ↔ ‖((y : ↥K) : PadicAlgCl l)‖ = 1 := by
  have hmul : ∀ a b : ↥(OK l K), ‖(((a * b : ↥(OK l K)) : ↥K) : PadicAlgCl l)‖ =
      ‖((a : ↥K) : PadicAlgCl l)‖ * ‖((b : ↥K) : PadicAlgCl l)‖ := fun a b => norm_mul _ _
  have hle : ∀ a : ↥(OK l K), ‖((a : ↥K) : PadicAlgCl l)‖ ≤ 1 := fun a => (mem_OK_iff _).1 a.2
  constructor
  · rintro ⟨u, rfl⟩
    have h := hmul u (↑u⁻¹ : ↥(OK l K))
    rw [Units.mul_inv] at h
    have h1 : ‖(((1 : ↥(OK l K)) : ↥K) : PadicAlgCl l)‖ = 1 := norm_one
    rw [h1] at h
    have h2 := hle u
    have h3 := hle (↑u⁻¹ : ↥(OK l K))
    have h4 := norm_nonneg (((u : ↥(OK l K)) : ↥K) : PadicAlgCl l)
    nlinarith
  · intro h
    have hy0 : (y : ↥K) ≠ 0 := fun h0 => by
      rw [h0] at h
      simp at h
    have hinv : (y : ↥K)⁻¹ ∈ OK l K := by
      rw [mem_OK_iff]
      change ‖((y : ↥K) : PadicAlgCl l)⁻¹‖ ≤ 1
      rw [norm_inv, h, inv_one]
    exact IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ hy0))

theorem intMap : IntMap := by
  intro E Ω _ _ _ _ _ l _ w A hA O _ _ _ Bw hj
  haveI : IsDiscreteValuationRing (Ow w) := (w.valuation E).valuationSubring_isDiscreteValuationRing
  have hmem : ∀ x : Ow w, algebraMap E Ω (algebraMap (Ow w) E x) ∈ A := fun x =>
    mem_of_le_one hA ((Valuation.mem_valuationSubring_iff _ _).1 x.2)
  have hφ : ∀ x : Ow w, ((kOf Bw).comp (algebraMap (Ow w) E)) x ∈ OK l Bw.Kw.1 := fun x =>
    (mem_OK_iff _).2 ((hj _).1 (hmem x))
  refine ⟨((kOf Bw).comp (algebraMap (Ow w) E)).codRestrict (OK l Bw.Kw.1) hφ, fun x => rfl, fun ϖ hϖ => ?_⟩
  let ν : Ow w → ℝ := fun x => ‖Bw.j (algebraMap E Ω (algebraMap (Ow w) E x))‖
  let M : ↥(OK l Bw.Kw.1) → ℝ := fun y => ‖((y : ↥Bw.Kw.1) : PadicAlgCl l)‖
  have hν1 : ∀ x, ν x ≤ 1 := fun x => (hj _).1 (hmem x)
  have hνmul : ∀ x y, ν (x * y) = ν x * ν y := fun x y => by simp only [ν, map_mul, norm_mul]
  have hϖ0 : (algebraMap (Ow w) E ϖ) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hϖw : w.valuation E (algebraMap (Ow w) E ϖ) < 1 := by
    by_contra h
    have h1 : w.valuation E (algebraMap (Ow w) E ϖ) = 1 :=
      le_antisymm ((Valuation.mem_valuationSubring_iff _ _).1 ϖ.2) (not_lt.1 h)
    have hinv : (algebraMap (Ow w) E ϖ)⁻¹ ∈ (w.valuation E).valuationSubring := by
      rw [Valuation.mem_valuationSubring_iff, map_inv₀, h1, inv_one]
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ hϖ0)))
  have hϖ1 : ν ϖ < 1 := (Induces.valuation_lt_one_iff hj _).1 (val_lt_one hA hϖw)
  have hϖp : 0 < ν ϖ := norm_pos_iff.2 ((map_ne_zero _).2 ((map_ne_zero _).2 hϖ0))
  have hbound : ∀ y : ↥(OK l Bw.Kw.1), M y < 1 → 0 < M y → M y ≤ ν ϖ := by
    intro y hy hpos
    obtain ⟨_, ⟨x, rfl⟩, hx⟩ := Metric.mem_closure_iff.1 (Bw.j_dense (y : ↥Bw.Kw.1).2) _ hpos
    rw [dist_eq_norm] at hx
    set t : PadicAlgCl l := Bw.j (algebraMap E Ω x) with ht
    set s : PadicAlgCl l := ((y : ↥Bw.Kw.1) : PadicAlgCl l) with hs
    have hM : M y = ‖s‖ := rfl
    rw [hM] at hy hpos ⊢
    have h1 : ‖t‖ ≤ ‖s‖ := by
      have h := IsUltrametricDist.norm_add_le_max s (t - s)
      rw [add_sub_cancel, norm_sub_rev] at h
      exact h.trans (max_le le_rfl hx.le)
    have h2 : ‖s‖ ≤ ‖t‖ := by
      have h := IsUltrametricDist.norm_add_le_max t (s - t)
      rw [add_sub_cancel] at h
      exact (le_max_iff.1 h).resolve_right (not_le.2 hx)
    have hxw : w.valuation E x ≤ 1 := le_one_of_mem hA ((hj _).2 (h1.trans hy.le))
    let ξ : Ow w := ⟨x, (Valuation.mem_valuationSubring_iff _ _).2 hxw⟩
    have hξ : ν ξ = ‖t‖ := rfl
    have hnu : ¬ IsUnit ξ := by
      rintro ⟨u, hu⟩
      have h3 := hνmul u (↑u⁻¹ : Ow w)
      rw [Units.mul_inv, hu, hξ] at h3
      have h4 : ν 1 = 1 := by simp [ν]
      rw [h4] at h3
      have h5 := hν1 (↑u⁻¹ : Ow w)
      have h6 := norm_nonneg t
      nlinarith
    have hmax : ξ ∈ Ideal.span {ϖ} := by
      rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]
      exact (IsLocalRing.mem_maximalIdeal ξ).2 hnu
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmax
    have h3 : ν ξ = ν c * ν ϖ := by rw [← hc, hνmul]
    have h4 := hν1 c
    have h5 : ‖t‖ ≤ ν ϖ := by
      rw [← hξ, h3]
      nlinarith
    exact h2.trans h5
  set φ := ((kOf Bw).comp (algebraMap (Ow w) E)).codRestrict (OK l Bw.Kw.1) hφ with hφdef
  have hMϖ : M (φ ϖ) = ν ϖ := rfl
  have hMmul : ∀ a b, M (a * b) = M a * M b := fun a b => norm_mul _ _
  have hMle : ∀ a, M a ≤ 1 := fun a => (mem_OK_iff _).1 a.2
  rw [irreducible_iff]
  refine ⟨fun h => ?_, fun a b hab => ?_⟩
  · have := (isUnit_OK_iff _).1 h
    change M (φ ϖ) = 1 at this
    rw [hMϖ] at this
    exact hϖ1.ne this
  · by_contra hn
    obtain ⟨ha, hb⟩ := not_or.1 hn
    have ha1 : M a < 1 := lt_of_le_of_ne (hMle a) fun h => ha ((isUnit_OK_iff _).2 h)
    have hb1 : M b < 1 := lt_of_le_of_ne (hMle b) fun h => hb ((isUnit_OK_iff _).2 h)
    have hprod : ν ϖ = M a * M b := by rw [← hMϖ, hab, hMmul]
    have ha0 : 0 ≤ M a := norm_nonneg _
    have hb0 : 0 ≤ M b := norm_nonneg _
    have hap : 0 < M a := lt_of_le_of_ne ha0 fun h => by
      rw [← h, zero_mul] at hprod
      exact hϖp.ne' hprod
    have hbp : 0 < M b := lt_of_le_of_ne hb0 fun h => by
      rw [← h, mul_zero] at hprod
      exact hϖp.ne' hprod
    have h1 := hbound a ha1 hap
    have h2 := hbound b hb1 hbp
    have h3 : M a * M b ≤ ν ϖ * ν ϖ := mul_le_mul h1 h2 hb0 hϖp.le
    nlinarith

end UpperTheory.Gal.Seam
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.NegVan
open CategoryTheory Limits CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.Seam

private theorem H_subsingleton_of_neg (R : Type) [CommRing R] (E : Spc) (F : Shv R) {n : ℤ} (hn : n < 0) :
    Subsingleton (H R E F n) := by
  haveI hK : ((chains R).obj E).IsStrictlyLE 0 :=
    (inferInstance : CochainComplex.IsStrictlyLE (((chainsN R).obj E).extend ComplexShape.embeddingDownNat) 0)
  haveI hL : (res R F).IsStrictlyGE 0 := by
    dsimp [res]
    infer_instance
  have hz : ∀ z : Cochain ((chains R).obj E) (res R F) n, z = 0 := by
    intro z
    apply Cochain.ext
    intro p q hpq
    by_cases hp : 0 < p
    · exact (CochainComplex.isZero_of_isStrictlyLE ((chains R).obj E) 0 p hp).eq_of_src _ _
    · exact (CochainComplex.isZero_of_isStrictlyGE (res R F) 0 q (by omega)).eq_of_tgt _ _
  constructor
  intro a b
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective a
  obtain ⟨y, rfl⟩ := CohomologyClass.mk_surjective b
  congr 1
  apply Subtype.ext
  rw [hz x.1, hz y.1]

theorem UpperTheory.Gal.Seam.negVan :
    NegVan := by
  intro l _ X n hn
  haveI : ∀ k : ℕ, Subsingleton (HtL l k (sch.obj X) n 0) := fun k =>
    H_subsingleton_of_neg (ZMod (l ^ k)) (sch.obj X) (tw (l ^ k) 0) hn
  haveI : Subsingleton (Hl l (sch.obj X) n 0) := by
    dsimp only [Hl]
    infer_instance
  dsimp only [HQ]
  infer_instance
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.BcCover
noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.GalV
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.G3

namespace UpperTheory.Gal.Seam

private theorem sq_up {A B A' B' S S' : Scheme.{0}} {f : A ⟶ B} {qB : B ⟶ S} {qA : A ⟶ S} (hA : f ≫ qB = qA) {g : S' ⟶ S}
    {fA : A' ⟶ A} {pA : A' ⟶ S'} (hA' : IsPullback fA pA qA g) {w : B' ⟶ B} {pB : B' ⟶ S'} (hB : IsPullback w pB qB g)
    {f' : A' ⟶ B'} (h1 : f' ≫ w = fA ≫ f) (h2 : f' ≫ pB = pA) : IsPullback fA f' f w := by
  subst hA; subst h2
  have s : IsPullback (f' ≫ pB) fA g (f ≫ qB) := hA'.flip
  exact (IsPullback.of_right s h1 hB.flip).flip

private abbrev spf {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) : sp B ⟶ sp A := Spec.map (CommRingCat.ofHom f)

private theorem fEt_bc : FEtBasic := pFEtBasic pPtsOfSplits

private theorem splits_bc : SplitsBasic := pSplitsBasic (pSplitsPts pIsoPts) pPtsOfSplits

section

variable {k K O O' L : Type} [Field k] [Field K] [CommRing O] [CommRing O'] [Algebra O k] [Algebra O' K] [Field L]
  (τ : k →+* K) (φ : O →+* O')

private theorem gen_sq (hφ : ∀ x, algebraMap O' K (φ x) = τ (algebraMap O k x)) :
    gen O' K ≫ spf φ = spf τ ≫ gen O k := by
  simp only [gen, spf, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact hφ x

variable {H : HTower k} {θ : H.Γ → L} (C : Cover H θ O) (hφ : ∀ x, algebraMap O' K (φ x) = τ (algebraMap O k x))

include hφ in
private theorem pullback_square_commutes : (pullback.fst H.q (spf τ) ≫ C.π) ≫ C.p = (pullback.snd H.q (spf τ) ≫ gen O' K) ≫ spf φ := by
  rw [Category.assoc, C.ov, Category.assoc, gen_sq τ φ hφ, ← Category.assoc, pullback.condition, Category.assoc]

private def piY : pullback H.q (spf τ) ⟶ pullback C.p (spf φ) :=
  pullback.lift (pullback.fst H.q (spf τ) ≫ C.π) (pullback.snd H.q (spf τ) ≫ gen O' K) (pullback_square_commutes τ φ C hφ)

private theorem piY_fst : piY τ φ C hφ ≫ pullback.fst C.p (spf φ) = pullback.fst H.q (spf τ) ≫ C.π := pullback.lift_fst _ _ _

private theorem piY_snd : piY τ φ C hφ ≫ pullback.snd C.p (spf φ) = pullback.snd H.q (spf τ) ≫ gen O' K := pullback.lift_snd _ _ _

private def wG : pullback (pullback.snd C.p (spf φ)) (gen O' K) ⟶ pullback C.p (gen O k) :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ spf τ) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, gen_sq τ φ hφ])

private theorem wG_fst : wG τ φ C hφ ≫ pullback.fst C.p (gen O k) =
    pullback.fst (pullback.snd C.p (spf φ)) (gen O' K) ≫ pullback.fst C.p (spf φ) := pullback.lift_fst _ _ _

private theorem wG_snd : wG τ φ C hφ ≫ pullback.snd C.p (gen O k) =
    pullback.snd (pullback.snd C.p (spf φ)) (gen O' K) ≫ spf τ := pullback.lift_snd _ _ _

private theorem sqG : IsPullback (wG τ φ C hφ) (pullback.snd (pullback.snd C.p (spf φ)) (gen O' K))
    (pullback.snd C.p (gen O k)) (spf τ) := by
  have a := IsPullback.of_hasPullback (pullback.snd C.p (spf φ)) (gen O' K)
  have b := IsPullback.of_hasPullback C.p (spf φ)
  have c : IsPullback (pullback.fst (pullback.snd C.p (spf φ)) (gen O' K) ≫ pullback.fst C.p (spf φ))
      (pullback.snd (pullback.snd C.p (spf φ)) (gen O' K)) C.p (gen O' K ≫ spf φ) := a.paste_horiz b
  rw [gen_sq τ φ hφ, ← wG_fst τ φ C hφ] at c
  exact IsPullback.of_right c (wG_snd τ φ C hφ) (IsPullback.of_hasPullback C.p (gen O k))

private def piK' : pullback H.q (spf τ) ⟶ pullback (pullback.snd C.p (spf φ)) (gen O' K) :=
  pullback.lift (piY τ φ C hφ) (pullback.snd H.q (spf τ)) (piY_snd τ φ C hφ)

private theorem piK'_fst : piK' τ φ C hφ ≫ pullback.fst (pullback.snd C.p (spf φ)) (gen O' K) = piY τ φ C hφ := pullback.lift_fst _ _ _

private theorem piK'_snd : piK' τ φ C hφ ≫ pullback.snd (pullback.snd C.p (spf φ)) (gen O' K) = pullback.snd H.q (spf τ) :=
  pullback.lift_snd _ _ _

private theorem sqPi : IsPullback (pullback.fst H.q (spf τ)) (piK' τ φ C hφ) (piK C) (wG τ φ C hφ) := by
  refine sq_up (piK_snd C) (IsPullback.of_hasPullback H.q (spf τ)) (sqG τ φ C hφ) ?_ (piK'_snd τ φ C hφ)
  apply pullback.hom_ext
  · rw [Category.assoc, wG_fst, ← Category.assoc, piK'_fst, piY_fst, Category.assoc, pullback.lift_fst]
  · rw [Category.assoc, wG_snd, ← Category.assoc, piK'_snd, Category.assoc, piK_snd, pullback.condition]

private theorem a_q (δ : C.Δ) : C.a δ ≫ H.q = H.q := by
  obtain ⟨h, -⟩ := id C.spl
  have := congrArg (· ≫ pullback.snd C.p (gen O k)) (h δ)
  simpa only [Category.assoc, pullback.lift_snd] using this


variable (H) in
private abbrev sB (g : H.Γ) : pullback (H.s g ≫ H.q) (spf τ) ⟶ pullback H.q (spf τ) := bcMap (spf τ) (H.s g) rfl


variable (H) in
private abbrev tB (g : H.Γ) : pullback (H.s g ≫ H.q) (spf τ) ⟶ pullback H.q (spf τ) := bcMap (spf τ) (H.t g) (H.comm g)

private abbrev aB (δ : C.Δ) : pullback H.q (spf τ) ⟶ pullback H.q (spf τ) := bcMap (spf τ) (C.a δ) (a_q C δ)

private theorem a_spl : Splits (piK' τ φ C hφ) (piK' τ φ C hφ) (aB τ C) := by
  haveI := C.finπ
  haveI := C.etπ
  have h0 := splits_bc.1 (piK C) (piK C) C.Δ C.a (pullback.fst H.q (spf τ)) C.spl
  have hσ : ∀ δ, aB τ C δ ≫ piK' τ φ C hφ = piK' τ φ C hφ := by
    intro δ
    obtain ⟨ha, -⟩ := id C.spl
    have e1 : piK' τ φ C hφ ≫ wG τ φ C hφ = pullback.fst H.q (spf τ) ≫ piK C := (sqPi τ φ C hφ).w.symm
    apply (sqG τ φ C hφ).hom_ext
    · rw [Category.assoc, e1, ← Category.assoc, bcMap_fst, Category.assoc, ha δ]
    · rw [Category.assoc, piK'_snd, bcMap_snd]
  refine (splits_bc.2 _ _ _ _ (sqPi τ φ C hφ) (piK' τ φ C hφ) C.Δ (aB τ C) hσ).2 ?_
  have e1 : piK' τ φ C hφ ≫ wG τ φ C hφ = pullback.fst H.q (spf τ) ≫ piK C := (sqPi τ φ C hφ).w.symm
  have e2 : (fun δ => aB τ C δ ≫ pullback.fst H.q (spf τ)) = fun δ => pullback.fst H.q (spf τ) ≫ C.a δ :=
    funext fun δ => bcMap_fst _ _ _
  rw [e1, e2]
  exact h0

private def bcC : Cover (bcAlong H τ) θ O' where
  Y := pullback C.p (spf φ)
  p := pullback.snd C.p (spf φ)
  smooth := MorphismProperty.of_isPullback (P := @Smooth) (IsPullback.of_hasPullback C.p (spf φ)) C.smooth
  proj := GlobalTheory.ProjSpace.isProjOver_pullback_snd φ C.proj
  π := piY τ φ C hφ
  ov := piY_snd τ φ C hφ
  Δ := C.Δ
  grp := C.grp
  fin := C.fin
  a := aB τ C
  finπ := MorphismProperty.of_isPullback (P := @IsFinite) (sqPi τ φ C hφ) C.finπ
  etπ := MorphismProperty.of_isPullback (P := @Etale) (sqPi τ φ C hφ) C.etπ
  one := by
    apply pullback.hom_ext
    · erw [bcMap_fst, C.one, Category.comp_id]
    · erw [bcMap_snd, Category.id_comp]
  mul x y := by
    apply pullback.hom_ext
    · erw [bcMap_fst, Category.assoc, bcMap_fst, ← Category.assoc, bcMap_fst, Category.assoc, C.mul]
    · erw [bcMap_snd, Category.assoc, bcMap_snd, bcMap_snd]
  spl := a_spl τ φ C hφ
  fix δ := by
    obtain ⟨g, hi, ht, hθ⟩ := C.fix δ
    have sq : IsPullback (pullback.fst (H.s g ≫ H.q) (spf τ)) (sB τ H g) (H.s g) (pullback.fst H.q (spf τ)) :=
      sq_up rfl (IsPullback.of_hasPullback _ _) (IsPullback.of_hasPullback H.q (spf τ)) (bcMap_fst _ _ _) (bcMap_snd _ _ _)
    refine ⟨g, sq.isIso_snd_of_isIso, ?_, hθ⟩
    change tB τ H g = sB τ H g ≫ aB τ C δ
    apply pullback.hom_ext
    · rw [bcMap_fst, Category.assoc, bcMap_fst, ← Category.assoc, bcMap_fst, Category.assoc, ht]
    · rw [bcMap_snd, Category.assoc, bcMap_snd, bcMap_snd]
  dim := by
    obtain ⟨d, hd⟩ := C.dim
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange d
    exact ⟨d, MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d) (IsPullback.of_hasPullback C.p (spf φ)) hd⟩

private theorem bcC_onto (h : C.Onto) : (bcC τ φ C hφ).Onto :=
  MorphismProperty.of_isPullback (P := @Surjective) (sqPi τ φ C hφ) h

private theorem bcC_lies (g : H.Γ) {T : Scheme.{0}} (s t : T ⟶ C.Y) (m : ℕ) (hL : C.Lies g s t m) {T' : Scheme.{0}}
    (v : T' ⟶ T) (s' t' : T' ⟶ pullback C.p (spf φ)) (hv : IsPullback v s' s (pullback.fst C.p (spf φ)))
    (ht : t' ≫ pullback.fst C.p (spf φ) = v ≫ t) (hp : t' ≫ pullback.snd C.p (spf φ) = s' ≫ pullback.snd C.p (spf φ)) :
    (bcC τ φ C hφ).Lies g s' t' m := by
  obtain ⟨hm, κ, h, h2, hF⟩ := hL
  have hsf : sB τ H g ≫ pullback.fst H.q (spf τ) = pullback.fst (H.s g ≫ H.q) (spf τ) ≫ H.s g := bcMap_fst _ _ _
  have htf : tB τ H g ≫ pullback.fst H.q (spf τ) = pullback.fst (H.s g ≫ H.q) (spf τ) ≫ H.t g := bcMap_fst _ _ _
  have hss : sB τ H g ≫ pullback.snd H.q (spf τ) = pullback.snd (H.s g ≫ H.q) (spf τ) := bcMap_snd _ _ _
  have hts : tB τ H g ≫ pullback.snd H.q (spf τ) = pullback.snd (H.s g ≫ H.q) (spf τ) := bcMap_snd _ _ _
  have l1 : (pullback.fst (H.s g ≫ H.q) (spf τ) ≫ κ) ≫ s = (sB τ H g ≫ piY τ φ C hφ) ≫ pullback.fst C.p (spf φ) := by
    rw [Category.assoc, Category.assoc, piY_fst, ← Category.assoc (sB τ H g), hsf, Category.assoc, h]
  have k1 : hv.lift _ _ l1 ≫ v = pullback.fst (H.s g ≫ H.q) (spf τ) ≫ κ := hv.lift_fst _ _ _
  have k2 : hv.lift _ _ l1 ≫ s' = sB τ H g ≫ piY τ φ C hφ := hv.lift_snd _ _ _
  generalize hv.lift _ _ l1 = κ' at k1 k2
  have e1 : κ' ≫ t' = tB τ H g ≫ piY τ φ C hφ := by
    apply pullback.hom_ext
    · rw [Category.assoc, ht, ← Category.assoc, k1, Category.assoc, Category.assoc, piY_fst, h2, ← Category.assoc (tB τ H g), htf,
        Category.assoc]
    · rw [Category.assoc, hp, ← Category.assoc, k2, Category.assoc, Category.assoc, piY_snd, ← Category.assoc, ← Category.assoc, hss, hts]

  let b : pullback (piY τ φ C hφ) s' ⟶ pullback C.π s :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst H.q (spf τ)) (pullback.snd _ _ ≫ v) (by
      rw [Category.assoc, ← piY_fst τ φ C hφ, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, hv.w])
  have b1 : b ≫ pullback.fst C.π s = pullback.fst (piY τ φ C hφ) s' ≫ pullback.fst H.q (spf τ) := pullback.lift_fst _ _ _
  have b2 : b ≫ pullback.snd C.π s = pullback.snd (piY τ φ C hφ) s' ≫ v := pullback.lift_snd _ _ _
  have sA : IsPullback (pullback.fst (piY τ φ C hφ) s') (b ≫ pullback.snd C.π s) (pullback.fst H.q (spf τ) ≫ C.π) s := by
    rw [b2, ← piY_fst τ φ C hφ]
    exact (IsPullback.of_hasPullback (piY τ φ C hφ) s').paste_vert hv.flip
  have sB' : IsPullback (pullback.fst (piY τ φ C hφ) s') b (pullback.fst H.q (spf τ)) (pullback.fst C.π s) :=
    IsPullback.of_bot sA b1.symm (IsPullback.of_hasPullback C.π s)
  have sC : IsPullback b (pullback.fst (piY τ φ C hφ) s' ≫ pullback.snd H.q (spf τ)) (pullback.fst C.π s ≫ H.q) (spf τ) :=
    sB'.flip.paste_vert (IsPullback.of_hasPullback H.q (spf τ))
  have h' : sB τ H g ≫ piY τ φ C hφ = κ' ≫ s' := k2.symm
  have sq : IsPullback (pullback.fst (H.s g ≫ H.q) (spf τ)) (pullback.lift (sB τ H g) κ' h') (pullback.lift (H.s g) κ h) b := by
    refine sq_up (by rw [pullback.lift_fst_assoc]) (IsPullback.of_hasPullback _ _) sC ?_ ?_
    · apply pullback.hom_ext
      · rw [Category.assoc, b1, ← Category.assoc, pullback.lift_fst, hsf, Category.assoc, pullback.lift_fst]
      · rw [Category.assoc, b2, ← Category.assoc, pullback.lift_snd, k1, Category.assoc, pullback.lift_snd]
    · rw [← Category.assoc, pullback.lift_fst, hss]
  exact ⟨hm, κ', h', e1, fEt_bc.1 _ _ _ _ m sq hF⟩

private theorem bcC_good (h : C.Good) : (bcC τ φ C hφ).Good := by
  intro g
  obtain ⟨T, s, t, d, m, hs, hst, hL⟩ := h g
  have hv := IsPullback.of_hasPullback s (pullback.fst C.p (spf φ))
  have c : (pullback.fst s (pullback.fst C.p (spf φ)) ≫ t) ≫ C.p =
      (pullback.snd s (pullback.fst C.p (spf φ)) ≫ pullback.snd C.p (spf φ)) ≫ spf φ := by
    rw [Category.assoc, hst, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, pullback.condition]
  have sq := IsPullback.of_hasPullback C.p (spf φ)
  exact ⟨pullback s (pullback.fst C.p (spf φ)), pullback.snd _ _, sq.lift _ _ c, d, m, fEt_bc.1 _ _ _ _ d hv hs,
    sq.lift_snd _ _ _, bcC_lies τ φ C hφ g s t m hL _ _ _ hv (sq.lift_fst _ _ _) (sq.lift_snd _ _ _)⟩

end

theorem bcCover : BcCover := by
  intro k K O O' L _ _ _ _ _ _ _ τ φ hφ H θ C
  refine ⟨bcC τ φ C hφ, pullback.fst C.p (spf φ), IsPullback.of_hasPullback C.p (spf φ), piY_fst τ φ C hφ,
    bcC_onto τ φ C hφ, bcC_good τ φ C hφ, ?_⟩
  intro g T s t m _ hL T' v s' t' hv ht hp
  exact bcC_lies τ φ C hφ g s t m hL v s' t' hv ht hp

end UpperTheory.Gal.Seam

end
end
