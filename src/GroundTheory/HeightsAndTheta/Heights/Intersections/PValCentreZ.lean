module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.StFibreOverFinite

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PValCentreZ
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo regularityEmbedding_holds

noncomputable section

theorem ValCentreZ.proof : ValCentreZ.Statement := by
  intro K _ ι _ P hP
  have := hP.1
  intro R
  classical
  set L := FractionRing (MRing ι ⧸ P)
  have hX0 : ∀ {f : MRing ι}, f ∉ P → toFrac P f ≠ 0 := fun hf h => hf (toFrac_eq_zero.mp h)

  have hj : ∀ k, ∃ i, (X ⟨k, i⟩ : MRing ι) ∉ P ∧
      ∀ i', R.valuation (toFrac P (X ⟨k, i'⟩)) ≤ R.valuation (toFrac P (X ⟨k, i⟩)) := by
    intro k
    obtain ⟨i₀, hi₀⟩ := hP.2.2 k
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun i => (X ⟨k, i⟩ : MRing ι) ∉ P)
      (fun i => R.valuation (toFrac P (X ⟨k, i⟩))) ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₀⟩⟩
    refine ⟨i, (Finset.mem_filter.mp hi).2, fun i' => ?_⟩
    by_cases hi' : (X ⟨k, i'⟩ : MRing ι) ∈ P
    · rw [toFrac_eq_zero.mpr hi', map_zero]; exact zero_le
    · exact hmax i' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'⟩)
  choose j hjP hjmax using hj
  choose r hr using fun p : Σ k, ι k =>
    exists_funField_mul_eq (P := P) (isMultiHomog_X_single p.1 p.2) (isMultiHomog_X_single p.1 (j p.1)) (hjP p.1)

  have hrle : ∀ p, R.valuation (r p : L) ≤ 1 := by
    intro p
    have hvj : R.valuation (toFrac P (X ⟨p.1, j p.1⟩)) ≠ 0 := by
      rw [Ne, Valuation.zero_iff]; exact hX0 (hjP p.1)
    have h := congrArg R.valuation (hr p)
    rw [map_mul] at h
    have hle : R.valuation (r p : L) * R.valuation (toFrac P (X ⟨p.1, j p.1⟩)) ≤
        1 * R.valuation (toFrac P (X ⟨p.1, j p.1⟩)) := by
      rw [one_mul]; exact (le_of_eq h).trans (hjmax p.1 p.2)
    exact le_of_mul_le_mul_right hle (zero_lt_iff.mpr hvj)

  have hmem : ∀ g, (chartHom r g : L) ∈ R := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => rw [chartHom_coe, eval₂Hom_C, eq_intCast]; exact intCast_mem R a
    | add f g hf hg => rw [map_add (f := _), Subring.coe_add]; exact add_mem hf hg
    | mul_X f p hf =>
      rw [map_mul, Subring.coe_mul]
      refine mul_mem hf ?_
      rw [← R.valuation_le_one_iff]
      simpa [chartHom] using hrle p

  obtain ⟨E, _, ψE, hψE⟩ : ∃ (E : Type) (_ : Field E) (ψE : MRing ι →+* E),
      ∀ g, ψE g = 0 ↔ R.valuation (chartHom r g : L) < 1 := by
    refine ⟨IsLocalRing.ResidueField R, inferInstance,
      (IsLocalRing.residue R).comp (((funField P).subtype.comp (chartHom r)).codRestrict R hmem), fun g => ?_⟩
    rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff,
      ValuationSubring.mem_nonunits_iff]
    exact Iff.rfl

  have hform : ∀ (g : MRing ι) (a : K → ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a →
      (g ∈ RingHom.ker (RegularityFunctionFieldNumber.specMap ψE ∅) ↔ R.valuation (chartHom r g : L) < 1) := by
    intro g a hg
    rw [RingHom.mem_ker, RegularityFunctionFieldNumber.specMap_form ψE ∅ hg, ← hψE, mul_eq_zero, MvPolynomial.C_eq_zero]
    refine or_iff_right (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ ?_)
    simp [RegularityFunctionFieldNumber.cS, MvPolynomial.X_ne_zero]
  have hPW : P ≤ RingHom.ker (RegularityFunctionFieldNumber.specMap ψE ∅) := by
    obtain ⟨S, hS, hPS⟩ := hP.2.1
    refine hPS.le.trans (Ideal.span_le.mpr fun g hg => ?_)
    obtain ⟨a, ha⟩ := hS g hg
    have hgP : g ∈ P := hPS ▸ Ideal.subset_span hg
    rw [SetLike.mem_coe, hform g a ha]
    have h1 := chartHom_mul j r hr ha
    rw [toFrac_eq_zero.mpr hgP] at h1
    rw [(mul_eq_zero.mp h1).resolve_right (toFrac_prod_ne_zero j hjP a), map_zero]
    exact zero_lt_one
  refine ⟨RingHom.ker (RegularityFunctionFieldNumber.specMap ψE ∅),
    ⟨RingHom.ker_isPrime _, RegularityValuationCentre.ker_isMultiHomogIdeal ψE, fun k => ⟨j k, ?_⟩⟩, hPW, ?_⟩
  ·
    have hrj : (r ⟨k, j k⟩ : L) = 1 :=
      mul_right_cancel₀ (hX0 (hjP k)) ((hr ⟨k, j k⟩).trans (one_mul _).symm)
    rw [hform _ _ (isMultiHomog_X_single k (j k))]
    have hXr : chartHom r (X ⟨k, j k⟩) = r ⟨k, j k⟩ := eval₂Hom_X' _ _ _
    rw [hXr, hrj, Valuation.map_one]
    exact lt_irrefl 1
  ·
    intro b f g hf hg hgW
    have hM := toFrac_prod_ne_zero j hjP b
    have e : toFrac P f / toFrac P g = (chartHom r f : L) / (chartHom r g : L) := by
      rw [← chartHom_mul j r hr hf, ← chartHom_mul j r hr hg, mul_div_mul_right _ _ hM]
    have hvg : R.valuation (chartHom r g : L) = 1 :=
      le_antisymm ((R.valuation_le_one_iff _).mpr (hmem g)) (not_lt.mp fun h => hgW ((hform g b hg).mpr h))
    change toFrac P f / toFrac P g ∈ R ∧
      (f ∈ RingHom.ker (RegularityFunctionFieldNumber.specMap ψE ∅) ↔ toFrac P f / toFrac P g ∈ R.nonunits)
    rw [e, ValuationSubring.mem_nonunits_iff, map_div₀, hvg, div_one, hform f b hf]
    refine ⟨(R.valuation_le_one_iff _).mp ?_, Iff.rfl⟩
    rw [map_div₀, hvg, div_one]
    exact (R.valuation_le_one_iff _).mpr (hmem f)

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.FunFieldExistsInv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem regRing_intCast_coe (P : Ideal (MRing ι)) (n : ℤ) :
    (((n : regRing P) : funField P) : FractionRing (MRing ι ⧸ P)) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (C n)) := by
  rw [eq_intCast C n, map_intCast, map_intCast]
  simp

theorem funField_exists_inv {P : Ideal (MRing ι)} [hPp : P.IsPrime] (y : funField P)
    (hy : (y : FractionRing (MRing ι ⧸ P)) ≠ 0) :
    ∃ x : funField P, (x : FractionRing (MRing ι ⧸ P)) * (y : FractionRing (MRing ι ⧸ P)) = 1 := by
  have hφ : ∀ s, s ∉ P → algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) ≠ 0 :=
    fun s hs => by rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]; exact hs
  have hFL : (y : FractionRing (MRing ι ⧸ P)) ∈ locRing P P := by
    have hx := y.2
    unfold funField at hx
    unfold locRing
    refine Subring.closure_mono ?_ hx
    rintro _ ⟨u, v, a, hv, hu, hva, rfl⟩
    refine ⟨u, v, a, hv, fun h => ?_, hu, hva, rfl⟩
    have h0 : Ideal.Quotient.mk P v = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h
    exact zero_notMem_nonZeroDivisors (h0 ▸ hv)
  obtain ⟨u, v, a, hu, hv, hvP, huv⟩ := LocRingFrac.proof K ι P P hPp hPp le_rfl _ hFL
  have huP : u ∉ P := fun h => by
    have h0 : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]
    rw [← huv] at h0
    exact mul_ne_zero hy (hφ v hvP) h0
  obtain ⟨x, hx⟩ := exists_funField_mul_eq hv hu huP
  refine ⟨x, mul_right_cancel₀ (hφ v hvP) ?_⟩
  rw [mul_assoc, huv, hx, one_mul]

theorem regRing_exists_coe {P : Ideal (MRing ι)} {y : funField P} (hy : y ∈ regRing P) :
    ∃ b : regRing P, (b : funField P) = y :=
  ⟨⟨y, hy⟩, rfl⟩

theorem RegularityMaximalSurjective.proof (h₁ : RegularityOrder.Statement) (h₂ : RegularityLocalPrime.Statement) : RegularityMaximalSurjective.Statement := by
  classical
  intro K _ ι _ P hP m hm
  have hPp : P.IsPrime := hP.2.1.1
  have hL : LocRingLocal.Statement := LocRingLocal.proof LocRingFrac.proof

  have hmZ : (m.comap (algebraMap ℤ (regRing P))).IsMaximal := by
    have : Module.Finite ℤ (regRing P) := (h₁ K ι P hP).2.1
    have : Algebra.IsIntegral ℤ (regRing P) := Algebra.IsIntegral.of_finite ℤ _
    exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ) m
  have hp := Submodule.IsPrincipal.prime_generator_of_isPrime (is_prime := hmZ.isPrime) _
    (Ring.ne_bot_of_isMaximal_of_not_isField hmZ Int.not_isField)
  set p := Submodule.IsPrincipal.generator (m.comap (algebraMap ℤ (regRing P)))
  have hZ : ∀ n : ℤ, (n : regRing P) ∈ m ↔ p ∣ n := fun n => by
    rw [← Submodule.IsPrincipal.mem_iff_generator_dvd, Ideal.mem_comap, algebraMap_int_eq, eq_intCast]
  have hCp : C p ∉ P := fun h => by
    have h' : p ∈ P.comap (C : ℤ →+* MRing ι) := h
    rw [hP.2.2.1] at h'
    exact hp.ne_zero (Ideal.mem_bot.mp h')
  have hp0 : (p : regRing P) ≠ 0 := fun h => by
    have h' := regRing_intCast_coe P p
    rw [h, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero, eq_comm, IsFractionRing.to_map_eq_zero_iff,
      Ideal.Quotient.eq_zero_iff_mem] at h'
    exact hCp h'

  have hS : {W | IsClosedPt W ∧ P ≤ W ∧ C p ∈ W}.Finite :=
    (divSupp_finite P (C p)).subset fun W hW =>
      (RegularityDivisorSupportClosed.proof K ι P (C p) 0 W hP (RegularityDenominator.isMultiHomog_C p) hCp).2 hW
  let g : Ideal (MRing ι) → Ideal (regRing P) := fun W =>
    if h : IsClosedPt W ∧ P ≤ W then regMaxAt P W h.1 h.2 (hL K ι P W hPp h.1.1.1 h.2).1 else ⊥
  have hgW : ∀ W (h : IsClosedPt W ∧ P ≤ W), g W = regMaxAt P W h.1 h.2 (hL K ι P W hPp h.1.1.1 h.2).1 :=
    fun W h => dif_pos h
  by_contra hcon
  push Not at hcon

  let T : Finset (Ideal (regRing P)) := insert ⊥ (hS.toFinset.image g)
  have hT : ¬ ((m : Set (regRing P)) ⊆ ⋃ i ∈ (↑T : Set (Ideal (regRing P))), ((fun i => i) i : Set (regRing P))) := by
    rw [Ideal.subset_union_prime (f := fun i : Ideal (regRing P) => i) ⊥ ⊥ fun i hi h1 _ => ?_]
    · rintro ⟨i, hi, hle⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact hp0 (Ideal.mem_bot.1 (hle ((hZ p).2 dvd_rfl)))
      · obtain ⟨W, hW, rfl⟩ := Finset.mem_image.1 hi
        obtain ⟨hWc, hPW, -⟩ := hS.mem_toFinset.1 hW
        obtain ⟨x, hx, z, hz, hxz⟩ := hcon W hWc hPW
        have h' := hle hx
        rw [hgW W ⟨hWc, hPW⟩] at h'
        exact (not_mem_regMaxAt_iff hWc hPW _ x).2 ⟨z, hz, hxz⟩ h'
    · rcases Finset.mem_insert.1 hi with rfl | hi
      · exact absurd rfl h1
      · obtain ⟨W, hW, rfl⟩ := Finset.mem_image.1 hi
        obtain ⟨hWc, hPW, -⟩ := hS.mem_toFinset.1 hW
        rw [hgW W ⟨hWc, hPW⟩]
        exact (regMaxAt_isMaximal h₁ hL hP hWc hPW _).isPrime
  obtain ⟨a, ham, ha⟩ := Set.not_subset.1 hT
  simp only [Set.mem_iUnion, SetLike.mem_coe, not_exists] at ha
  have ha0 : ((a : funField P) : FractionRing (MRing ι ⧸ P)) ≠ 0 := fun h =>
    ha ⊥ (Finset.mem_insert_self _ _) (Ideal.mem_bot.2 (Subtype.ext (Subtype.ext (by rw [h, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero]))))

  obtain ⟨x, hxa⟩ := funField_exists_inv (a : funField P) ha0
  obtain ⟨n, hpn, hn⟩ := h₂ K ι P p x hP hp fun W hWc hPW hpW => by
    have h' := ha (g W) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem g (hS.mem_toFinset.2 ⟨hWc, hPW, hpW⟩)))
    rw [hgW W ⟨hWc, hPW⟩] at h'
    obtain ⟨z, hz, haz⟩ := (not_mem_regMaxAt_iff hWc hPW _ a).1 h'
    rwa [show (x : FractionRing (MRing ι ⧸ P)) = z by rw [← mul_one (x : FractionRing (MRing ι ⧸ P)), ← haz,
      ← mul_assoc, hxa, one_mul]]

  refine hpn ((hZ n).1 ?_)
  obtain ⟨b, hb⟩ := regRing_exists_coe hn
  have he : a * b = (n : regRing P) := by
    apply Subtype.ext
    apply Subtype.ext
    rw [Subring.coe_mul, Subring.coe_mul, hb, Subring.coe_mul, Subring.coe_intCast, Subring.coe_intCast,
      Subring.coe_intCast]
    rw [mul_left_comm, mul_comm ((a : funField P) : FractionRing (MRing ι ⧸ P)), hxa, mul_one]
  rw [← he]
  exact m.mul_mem_right b ham

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.AevalMemAdjoin
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace FibreTranscendence

theorem aeval_red {L : Type} [Field L] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) L] {J : Type} (y : J → L)
    (g : MvPolynomial J ℤ) :
    aeval y (MvPolynomial.map (Int.castRingHom (ZMod p)) g) = aeval y g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp only [map_add (f := _), hf, hg]
  | mul_X f i hf => simp only [map_mul, hf, map_X, aeval_X]

theorem aeval_mem_adjoin {L : Type} [Field L] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) L] {J : Type} (y : J → L)
    (g : MvPolynomial J ℤ) : aeval y g ∈ IntermediateField.adjoin (ZMod p) (Set.range y) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [intCast_mem]
  | add f g hf hg => simpa using add_mem hf hg
  | mul_X f i hf =>
    simpa using mul_mem hf (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)

variable {K : Type} {ι : K → Type}

theorem ker_aeval_F {L : Type} [Field L] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) L] (y : (Σ k, ι k) → L)
    {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J) (hJ : RingHom.ker (aeval y : MRing ι →ₐ[ℤ] L) = J) :
    RingHom.ker (aeval y : MRingOver (ZMod p) ι →ₐ[ZMod p] L) = J.map (PointVertical.red (ι := ι) p) := by
  ext f
  obtain ⟨g, rfl⟩ := PointVertical.red_surjective (ι := ι) p f
  rw [PointVertical.mem_map_red_iff p hp, RingHom.mem_ker, ← hJ, RingHom.mem_ker]
  exact iff_of_eq (congrArg (· = 0) (aeval_red p y g))

theorem trdeg_adjoin [Fintype K] [∀ k, Fintype (ι k)] (hE : EvalKerKrullDim.Statement) {L : Type} [Field L] (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) L]
    (y : (Σ k, ι k) → L) {J : Ideal (MRing ι)} (hp : ((p : ℕ) : MRing ι) ∈ J)
    (hJ : RingHom.ker (aeval y : MRing ι →ₐ[ℤ] L) = J) {n : ℕ} (hV : IsProjVarF (J.map (PointVertical.red (ι := ι) p)) n) :
    Algebra.trdeg (ZMod p) (IntermediateField.adjoin (ZMod p) (Set.range y)) = ((n + Fintype.card K : ℕ) : Cardinal) := by
  have h := hE K ι (ZMod p) L y
  rw [ker_aeval_F p y hp hJ, hV.2] at h
  have h' : (Algebra.trdeg (ZMod p) (IntermediateField.adjoin (ZMod p) (Set.range y))).toENat =
      ((n + Fintype.card K : ℕ) : ℕ∞) := by exact_mod_cast h.symm
  exact Cardinal.toENat_eq_natCast.mp h'

end FibreTranscendence


open FibreTranscendence in
theorem FibreTranscendenceDegreeAlt.proof (hE : EvalKerKrullDim.Statement) : FibreTranscendenceDegreeAlt.Statement := by
  intro K _ ι _ K' _ ι' _ κ v p _ W' n hv hp hW hV G'
  classical
  have hpI : ((p : ℕ) : MRing ι) ∈ imageZ v W' := by
    show rename v ((p : ℕ) : MRing ι) ∈ W'
    simpa using hp
  have hΦp : ((p : ℕ) : G'.Φ) = 0 := by
    have h := hpI
    rw [← G'.ker_x, RingHom.mem_ker] at h
    simpa using h
  have hΦ'p : ((p : ℕ) : G'.Φ') = 0 := by
    have h := hp
    rw [← G'.genericFibre_ker_target, RingHom.mem_ker] at h
    simpa using h
  have : CharP G'.Φ p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hΦp
  have : CharP G'.Φ' p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hΦ'p
  let _ : Algebra (ZMod p) G'.Φ := ZMod.algebra _ p
  let _ : Algebra (ZMod p) G'.Φ' := ZMod.algebra _ p
  have : IsScalarTower (ZMod p) G'.Φ G'.Φ' := IsScalarTower.of_algebraMap_eq fun a =>
    DFunLike.congr_fun (Subsingleton.elim (algebraMap (ZMod p) G'.Φ')
      ((algebraMap G'.Φ G'.Φ').comp (algebraMap (ZMod p) G'.Φ))) a

  have hx := trdeg_adjoin hE p G'.x hpI G'.ker_x
    (by rw [← PointVertical.imageVar_red p v hp]; exact hV)
  have htop : IntermediateField.adjoin (ZMod p) (Set.range G'.x) = ⊤ := by
    refine eq_top_iff.2 fun c _ => ?_
    obtain ⟨f, g, -, rfl⟩ := G'.gen c
    exact div_mem (aeval_mem_adjoin p _ f) (aeval_mem_adjoin p _ g)
  have hΦ : Algebra.trdeg (ZMod p) G'.Φ = ((n + Fintype.card K : ℕ) : Cardinal) := by
    rw [← hx, htop, IntermediateField.topEquiv.trdeg_eq]

  set E := IntermediateField.adjoin G'.Φ
    (Set.range fun q : (Σ k : FibreBlock κ, ι' k.1) => G'.x' ⟨q.1.1, q.2⟩) with hEdef
  have hEeq : E.restrictScalars (ZMod p) = IntermediateField.adjoin (ZMod p) (Set.range G'.x') := by
    refine le_antisymm (fun c hc => ?_) (IntermediateField.adjoin_le_iff.2 ?_)
    · have hle : E.toSubfield ≤ (IntermediateField.adjoin (ZMod p) (Set.range G'.x')).toSubfield := by
        rw [hEdef, IntermediateField.adjoin_toSubfield]
        refine Subfield.closure_le.2 (Set.union_subset ?_ ?_)
        · rintro _ ⟨c, rfl⟩
          obtain ⟨f, g, -, rfl⟩ := G'.gen c
          have key : ∀ f : MRing ι, algebraMap G'.Φ G'.Φ' (aeval G'.x f) = aeval G'.x' (rename v f) := by
            intro f
            induction f using MvPolynomial.induction_on with
            | C a => simp
            | add f g hf hg => simp only [map_add (f := _), hf, hg]
            | mul_X f i hf => simp only [map_mul, hf, aeval_X, rename_X, G'.compat]
          rw [map_div₀, key, key]
          exact div_mem (aeval_mem_adjoin p _ _) (aeval_mem_adjoin p _ _)
        · rintro _ ⟨q, rfl⟩
          exact IntermediateField.subset_adjoin _ _ ⟨_, rfl⟩
      exact hle hc
    · rintro _ ⟨q, rfl⟩
      show G'.x' q ∈ E
      by_cases hq : q.1 ∈ Set.range κ
      · obtain ⟨q0, rfl⟩ := hv.2.2.2 q hq
        rw [G'.compat]
        exact E.algebraMap_mem _
      · exact IntermediateField.subset_adjoin _ _ ⟨⟨⟨q.1, hq⟩, q.2⟩, rfl⟩
  have hEt : Algebra.trdeg (ZMod p) E = ((n + Fintype.card K' : ℕ) : Cardinal) := by
    rw [← trdeg_adjoin hE p G'.x' hp G'.genericFibre_ker_target hW, ← hEeq]
    rfl

  have hadd := trdeg_add_eq (ZMod p) G'.Φ (A := E)
  rw [hΦ, hEt] at hadd
  have hc : Fintype.card (FibreBlock κ) + Fintype.card K = Fintype.card K' := by
    simp only [← Nat.card_eq_fintype_card]
    have h1 := Set.ncard_add_ncard_compl (Set.range κ)
    rw [Set.ncard_range_of_injective hv.1, add_comm] at h1
    exact h1
  have hlt : Algebra.trdeg G'.Φ E < Cardinal.aleph0 := by
    refine lt_of_le_of_lt (le_add_self.trans_eq hadd) Cardinal.natCast_lt_aleph0
  obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.1 hlt
  rw [hm] at hadd ⊢
  have : n + Fintype.card K + m = n + Fintype.card K' := by exact_mod_cast hadd
  exact_mod_cast (by omega : m = Fintype.card (FibreBlock κ))

end GroundTheory.Heights₂.Heights.Inter
end
end
