module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscBDefs

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussHeights.PlaceSumHeights.PlaceSumStatements.PlaceSumTheorem.HtPlacesSum
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussHeights.PlaceSumHeights.PlaceSumStatements.PlaceSumLemmas.GaussValuationSums.PlacesOverHeightOnePrime
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussHeights.PlaceSumHeights.PlaceSumStatements.PlaceSumLemmas.GaussValuationSums.ValPlWtAddEqZero
namespace PI.HtPlacesSumWork

open IsDedekindDomain WithZero IsLocalRing ReciprocityTheory.ChartRestriction.G.T0

theorem valPl_wt_add_eq_zero {a b : WithTop ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b = 0) :
    a = 0 := by
  induction a using WithTop.recTopCoe with
  | top => simp at h
  | coe a =>
    induction b using WithTop.recTopCoe with
    | top => simp at h
    | coe b =>
      norm_cast at ha hb h ⊢
      omega

theorem valPl_log_le {g : ℤᵐ⁰} (hg : g ≠ 0) : g ≤ 1 ↔ log g ≤ 0 := by
  rw [← log_le_log hg one_ne_zero, log_one]

theorem valPl_log_lt {g : ℤᵐ⁰} (hg : g ≠ 0) : g < 1 ↔ log g < 0 := by
  rw [← not_le, ← not_le, ← log_le_log one_ne_zero hg, log_one]

theorem valPl_mem_vRing {Φ : Type*} [Field Φ] (u : AddValuation Φ (WithTop ℤ)) (x : Φ) :
    x ∈ vRing u ↔ 0 ≤ u x := by
  exact Iff.rfl

theorem valPl_max_iff {Φ : Type*} [Field Φ] (V : ValuationSubring Φ)
    (u : AddValuation Φ (WithTop ℤ)) (hV : ∀ x, x ∈ V ↔ 0 ≤ u x) (y : V) :
    y ∈ maximalIdeal V ↔ 0 < u (y : Φ) := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hnu
    rcases ((hV y).1 y.2).lt_or_eq with h | h
    · exact h
    exfalso
    apply hnu
    have hy0 : (y : Φ) ≠ 0 := by
      intro e
      rw [e, AddValuation.map_zero] at h
      exact WithTop.top_ne_zero h.symm
    have hinv : (y : Φ)⁻¹ ∈ V := (hV _).2 (by rw [AddValuation.map_inv, ← h, neg_zero])
    exact (Units.mkOfMulEqOne y ⟨_, hinv⟩ (Subtype.ext (by simp [hy0]))).isUnit
  · intro hpos hu
    obtain ⟨z, hz⟩ := hu.exists_right_inv
    have e : u ((y : Φ) * (z : Φ)) = 0 := by
      have := congrArg (fun t : V => u (t : Φ)) hz
      simpa using this
    rw [AddValuation.map_mul] at e
    exact hpos.ne' (valPl_wt_add_eq_zero ((hV y).1 y.2) ((hV z).1 z.2) e)

section Addv

variable {S L : Type*} [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] (v : HeightOneSpectrum S)

variable (L) in
open Classical in
noncomputable def addv : AddValuation L (WithTop ℤ) :=
  AddValuation.of (fun x => if x = 0 then ⊤ else (((-log (v.valuation L x) : ℤ)) : WithTop ℤ))
    (by simp) (by simp)
    (by
      intro x y
      by_cases hx : x = 0
      · subst hx; simp
      by_cases hy : y = 0
      · subst hy; simp
      by_cases hxy : x + y = 0
      · simp [hxy]
      simp only [hx, hy, hxy, ite_false]
      rw [← WithTop.coe_min, WithTop.coe_le_coe]
      have hx' : v.valuation L x ≠ 0 := by simpa using hx
      have hy' : v.valuation L y ≠ 0 := by simpa using hy
      have hxy' : v.valuation L (x + y) ≠ 0 := by simpa using hxy
      have h := (v.valuation L).map_add x y
      rcases le_max_iff.mp h with h | h
      · have := (log_le_log hxy' hx').mpr h
        rw [min_le_iff]; left; omega
      · have := (log_le_log hxy' hy').mpr h
        rw [min_le_iff]; right; omega)
    (by
      intro x y
      by_cases hx : x = 0
      · subst hx; simp
      by_cases hy : y = 0
      · subst hy; simp
      have hx' : v.valuation L x ≠ 0 := by simpa using hx
      have hy' : v.valuation L y ≠ 0 := by simpa using hy
      simp only [hx, hy, mul_eq_zero, or_self, ite_false, map_mul, log_mul hx' hy']
      rw [← WithTop.coe_add]; congr 1; ring)

theorem addv_apply {x : L} (hx : x ≠ 0) :
    addv L v x = (((-log (v.valuation L x) : ℤ)) : WithTop ℤ) := by
  rw [addv, AddValuation.of_apply, ite_eq_right hx]

theorem addv_alg {s : S} (hs : s ≠ 0) :
    addv L v (algebraMap S L s) = (((-log (v.intValuation s) : ℤ)) : WithTop ℤ) := by
  rw [addv_apply v ((map_ne_zero_iff _ (IsFractionRing.injective S L)).2 hs),
    HeightOneSpectrum.valuation_of_algebraMap]

theorem addv_nonneg_iff (x : L) : 0 ≤ addv L v x ↔ v.valuation L x ≤ 1 := by
  by_cases hx : x = 0
  · subst hx
    simp
  rw [addv_apply v hx, WithTop.coe_nonneg, neg_nonneg,
    valPl_log_le ((Valuation.ne_zero_iff _).2 hx)]

theorem addv_nonneg (s : S) : 0 ≤ addv L v (algebraMap S L s) := by
  rw [addv_nonneg_iff]
  exact v.valuation_le_one s

theorem addv_pos_iff (s : S) : 0 < addv L v (algebraMap S L s) ↔ s ∈ v.asIdeal := by
  by_cases hs : s = 0
  · subst hs
    simp
  rw [addv_alg v hs, WithTop.coe_pos, neg_pos, ← valPl_log_lt (v.intValuation_ne_zero s hs),
    HeightOneSpectrum.intValuation_lt_one_iff_mem]

theorem addv_isNormDiscrete : IsNormDiscrete (addv L v) := by
  refine ⟨fun a ha => by rw [addv_apply v ha]; exact WithTop.coe_ne_top, ?_⟩
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  have hπ0 : π ≠ 0 := by
    rintro rfl
    simp at hπ
    exact WithZero.exp_ne_zero hπ.symm
  exact ⟨algebraMap S L π, by rw [addv_alg v hπ0, hπ, log_exp]; rfl⟩

theorem addv_inj {v v' : HeightOneSpectrum S} (h : addv L v = addv L v') : v = v' := by
  apply HeightOneSpectrum.ext
  ext s
  rw [← addv_pos_iff (L := L) v, ← addv_pos_iff (L := L) v', h]

private theorem eq_addv_lemma (w : AddValuation L (WithTop ℤ))
    (h0 : ∀ s : S, 0 ≤ w (algebraMap S L s))
    (hQ : ∀ s : S, 0 < w (algebraMap S L s) ↔ s ∈ v.asIdeal) (hne : ∃ π : L, w π = 1) :
    vRing w = HeightOneSpectrum.valuationSubringAtPrime L v := by
  set D := HeightOneSpectrum.valuationSubringAtPrime L v
  have hDle : D ≤ vRing w := by
    intro x hx
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective v.asIdeal.primeCompl (⟨x, hx⟩ : D)
    have hspec := IsLocalization.mk'_spec D a b
    dsimp only at hab
    rw [hab] at hspec
    have hL := congrArg (algebraMap D L) hspec
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at hL
    have hw := congrArg w hL
    rw [AddValuation.map_mul] at hw
    have hb0 : w (algebraMap S L b) = 0 :=
      le_antisymm (not_lt.1 (fun h => b.2 ((hQ b).1 h))) (h0 b)
    rw [hb0, add_zero] at hw
    rw [valPl_mem_vRing]
    show 0 ≤ w (algebraMap D L ⟨x, hx⟩)
    rw [hw]
    exact h0 a
  have hP := ValuationSubring.ofPrime_idealOfLE D (vRing w) hDle
  by_cases hbot : D.idealOfLE (vRing w) hDle = ⊥
  · simp only [hbot, ValuationSubring.ofPrime_bot] at hP
    exfalso
    obtain ⟨π, hπ⟩ := hne
    have hm : π⁻¹ ∈ vRing w := by
      rw [← hP]
      exact ValuationSubring.mem_top _
    rw [valPl_mem_vRing, AddValuation.map_inv, hπ] at hm
    exact absurd hm (by decide)
  · have hmax : (D.idealOfLE (vRing w) hDle).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hbot
    simp only [IsLocalRing.eq_maximalIdeal hmax, ValuationSubring.ofPrime_top] at hP
    exact hP.symm

private theorem eq_addv_lemma_2 {Φ : Type*} [Field Φ] (u1 u2 : AddValuation Φ (WithTop ℤ))
    (h1 : IsNormDiscrete u1) (h2 : IsNormDiscrete u2) (he : ∀ x, 0 ≤ u1 x ↔ 0 ≤ u2 x) : u1 = u2 := by
  have fin : ∀ u : AddValuation Φ (WithTop ℤ), IsNormDiscrete u → ∀ x : Φ, x ≠ 0 →
      ∃ k : ℤ, u x = k := by
    intro u hu x hx
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 (hu.1 x hx)
    exact ⟨k, hk.symm⟩
  have hpow : ∀ (u : AddValuation Φ (WithTop ℤ)) (π : Φ), u π = 1 → ∀ n : ℕ,
      u (π ^ n) = ((n : ℤ) : WithTop ℤ) := by
    intro u π h n
    rw [AddValuation.map_pow, h, nsmul_one]
    simp
  have hinv : ∀ (u : AddValuation Φ (WithTop ℤ)) (x : Φ) (k : ℤ), x ≠ 0 → u x = k →
      u x⁻¹ = ((-k : ℤ) : WithTop ℤ) := by
    intro u x k hx hk
    have h := congrArg u (mul_inv_cancel₀ hx)
    rw [AddValuation.map_mul, AddValuation.map_one, hk] at h
    have hne : u x⁻¹ ≠ ⊤ := by
      intro ht
      rw [ht] at h
      simp at h
    obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.1 hne
    rw [← hj] at h ⊢
    norm_cast at h ⊢
    omega
  obtain ⟨π1, hπ1⟩ := h1.2
  obtain ⟨π2, hπ2⟩ := h2.2
  have hπ10 : π1 ≠ 0 := by
    rintro rfl
    simp at hπ1
  have hπ20 : π2 ≠ 0 := by
    rintro rfl
    simp at hπ2
  have hπ1' : u1 π1 = ((1 : ℤ) : WithTop ℤ) := by simpa using hπ1
  have hπ2' : u2 π2 = ((1 : ℤ) : WithTop ℤ) := by simpa using hπ2
  obtain ⟨c, hc⟩ := fin u2 h2 π1 hπ10
  obtain ⟨d, hd⟩ := fin u1 h1 π2 hπ20
  have hcpos : 0 < c := by
    have e := he π1⁻¹
    rw [hinv u1 π1 1 hπ10 hπ1', hinv u2 π1 c hπ10 hc] at e
    norm_cast at e
    omega
  have hdpos : 0 < d := by
    have e := he π2⁻¹
    rw [hinv u1 π2 d hπ20 hd, hinv u2 π2 1 hπ20 hπ2'] at e
    norm_cast at e
    omega
  have hc1 : c = 1 := by
    have e := he (π2 * π1⁻¹)
    rw [AddValuation.map_mul, AddValuation.map_mul, hd, hinv u1 π1 1 hπ10 hπ1', hπ2',
      hinv u2 π1 c hπ10 hc] at e
    norm_cast at e
    omega
  have hπ1u2 : u2 π1 = 1 := by rw [hc, hc1]; rfl
  ext x
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨m, hm⟩ := fin u1 h1 x hx
  obtain ⟨a, ha⟩ := fin u2 h2 x hx
  have key : ∀ n : ℕ, (0 ≤ m + n ↔ 0 ≤ a + n) ∧ (0 ≤ -m + n ↔ 0 ≤ -a + n) := by
    intro n
    have e1 := he (x * π1 ^ n)
    rw [AddValuation.map_mul, AddValuation.map_mul, hm, ha, hpow u1 π1 hπ1 n, hpow u2 π1 hπ1u2 n] at e1
    have e2 := he (x⁻¹ * π1 ^ n)
    rw [AddValuation.map_mul, AddValuation.map_mul, hinv u1 x m hx hm, hinv u2 x a hx ha,
      hpow u1 π1 hπ1 n, hpow u2 π1 hπ1u2 n] at e2
    norm_cast at e1 e2
  have k1 := key (-m).toNat
  have k2 := key ((-m).toNat - 1)
  have k3 := key m.toNat
  have k4 := key (m.toNat - 1)
  rw [hm, ha]
  norm_cast
  omega

theorem eq_addv (w : AddValuation L (WithTop ℤ)) (hw : IsNormDiscrete w)
    (h0 : ∀ s : S, 0 ≤ w (algebraMap S L s))
    (hQ : ∀ s : S, 0 < w (algebraMap S L s) ↔ s ∈ v.asIdeal) : w = addv L v := by
  have hA := eq_addv_lemma v w h0 hQ hw.2
  have hB := eq_addv_lemma v (addv L v) (addv_nonneg v) (addv_pos_iff v) (addv_isNormDiscrete v).2
  apply eq_addv_lemma_2 w (addv L v) hw (addv_isNormDiscrete v)
  intro x
  rw [← valPl_mem_vRing, ← valPl_mem_vRing, hA, hB]

end Addv

section Places

variable (O F L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [Algebra O L] [IsScalarTower O F L]

def PlacesOver : Set (AddValuation L (WithTop ℤ)) :=
  {w | IsNormDiscrete w ∧ ∀ a : O, 0 ≤ w (algebraMap O L a) ∧
    (0 < w (algebraMap O L a) ↔ a ∈ maximalIdeal O)}

noncomputable def fres (w : AddValuation L (WithTop ℤ)) : ℕ :=
  letI := resAlg (F := F) w
  Module.finrank (ResidueField ((vRing w).comap (algebraMap F L))) (ResidueField (vRing w))

variable {O F L}
variable [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]
  [FaithfulSMul O L]

theorem valPl_comap (Q : Ideal (integralClosure O L)) [Q.IsMaximal] :
    Q.comap (algebraMap O (integralClosure O L)) = maximalIdeal O :=
  IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal Q)

theorem valPl_ne_bot (Q : Ideal (integralClosure O L)) [Q.IsMaximal] : Q ≠ ⊥ := by
  intro h
  have hc := valPl_comap Q
  have hinj : Function.Injective (algebraMap O (integralClosure O L)) := by
    refine Function.Injective.of_comp (f := algebraMap (integralClosure O L) L) ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
    exact FaithfulSMul.algebraMap_injective O L
  rw [h, Ideal.comap_bot_of_injective _ hinj] at hc
  exact IsDiscreteValuationRing.not_a_field O hc.symm

def valPl_hv (Q : {Q : Ideal (integralClosure O L) // Q.IsMaximal}) :
    HeightOneSpectrum (integralClosure O L) :=
  have := Q.2
  ⟨Q.1, Q.2.isPrime, valPl_ne_bot Q.1⟩

variable (O L) in
noncomputable def plOf (Q : {Q : Ideal (integralClosure O L) // Q.IsMaximal}) :
    AddValuation L (WithTop ℤ) :=
  addv L (valPl_hv Q)

theorem plOf_mem (Q : {Q : Ideal (integralClosure O L) // Q.IsMaximal}) :
    plOf O L Q ∈ PlacesOver O L := by
  have := Q.2
  refine ⟨addv_isNormDiscrete _, fun a => ?_⟩
  rw [IsScalarTower.algebraMap_apply O (integralClosure O L) L a]
  refine ⟨addv_nonneg _ _, ?_⟩
  rw [plOf, addv_pos_iff, ← valPl_comap Q.1]
  rfl

theorem plOf_injective : Function.Injective (plOf O L) := by
  intro Q Q' h
  have hv := addv_inj h
  exact Subtype.ext (congrArg HeightOneSpectrum.asIdeal hv)

theorem plOf_nonneg {w : AddValuation L (WithTop ℤ)} (hw : w ∈ PlacesOver O L)
    (b : integralClosure O L) : 0 ≤ w (algebraMap (integralClosure O L) L b) := by
  have hO : ∀ a : O, algebraMap O L a ∈ vRing w := fun a => (valPl_mem_vRing w _).2 (hw.2 a).1
  let f : O →+* vRing w := (algebraMap O L).codRestrict (vRing w) hO
  have hc : (algebraMap (vRing w) L).comp f = algebraMap O L := RingHom.ext fun _ => rfl
  obtain ⟨p, hp, hpb⟩ := (mem_integralClosure_iff O L).1 b.2
  have hint : IsIntegral (vRing w) (b : L) := ⟨p.map f, hp.map f, by rw [Polynomial.eval₂_map, hc]; exact hpb⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have hmem : (b : L) ∈ vRing w := by
    rw [← hy]
    exact y.2
  exact (valPl_mem_vRing w _).1 hmem

theorem mem_range_plOf {w : AddValuation L (WithTop ℤ)} (hw : w ∈ PlacesOver O L) :
    ∃ Q, plOf O L Q = w := by
  let f : integralClosure O L →+* vRing w := (algebraMap (integralClosure O L) L).codRestrict (vRing w)
    (fun b => (valPl_mem_vRing w _).2 (plOf_nonneg hw b))
  let Q : Ideal (integralClosure O L) := (maximalIdeal (vRing w)).comap f
  have hQmem : ∀ b : integralClosure O L, b ∈ Q ↔ 0 < w (algebraMap (integralClosure O L) L b) :=
    fun b => Ideal.mem_comap.trans (valPl_max_iff (vRing w) w (valPl_mem_vRing w) (f b))
  have hinj : Function.Injective (algebraMap O (integralClosure O L)) := by
    refine Function.Injective.of_comp (f := algebraMap (integralClosure O L) L) ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
    exact FaithfulSMul.algebraMap_injective O L
  have hQne : Q ≠ ⊥ := by
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (IsDiscreteValuationRing.not_a_field O)
    intro hb
    have hm : algebraMap O (integralClosure O L) a ∈ Q := by
      rw [hQmem, ← IsScalarTower.algebraMap_apply]
      exact ((hw.2 a).2).2 ha
    rw [hb, Ideal.mem_bot] at hm
    exact ha0 (hinj (by rw [hm, map_zero]))
  have hmax : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQne
  refine ⟨⟨Q, hmax⟩, ?_⟩
  symm
  exact eq_addv _ w hw.1 (fun b => plOf_nonneg hw b) (fun b => (hQmem b).symm)

theorem plOf_e (Q : {Q : Ideal (integralClosure O L) // Q.IsMaximal}) {ϖ : O}
    (hϖ : Irreducible ϖ) :
    plOf O L Q (algebraMap O L ϖ) = (((Q.1.ramificationIdx O : ℕ) : ℤ) : WithTop ℤ) := by
  have := Q.2
  have hinj : Function.Injective (algebraMap O (integralClosure O L)) := by
    refine Function.Injective.of_comp (f := algebraMap (integralClosure O L) L) ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
    exact FaithfulSMul.algebraMap_injective O L
  have hb0 : algebraMap O (integralClosure O L) ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  haveI : Q.1.LiesOver (maximalIdeal O) := ⟨(valPl_comap Q.1).symm⟩
  have hmap : Ideal.map (algebraMap O (integralClosure O L)) (maximalIdeal O) =
      Ideal.span {algebraMap O (integralClosure O L) ϖ} := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.map_span, Set.image_singleton]
  have hne : Ideal.map (algebraMap O (integralClosure O L)) (maximalIdeal O) ≠ ⊥ := by
    rw [hmap, Ne, Ideal.span_singleton_eq_bot]
    exact hb0
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count (maximalIdeal O) Q.1 hne, hmap]
  rw [plOf, IsScalarTower.algebraMap_apply O (integralClosure O L) L, addv_alg _ hb0,
    HeightOneSpectrum.intValuation_if_neg _ hb0, log_exp, neg_neg]
  have hc := Ideal.count_associates_factors_eq (I := Ideal.span {algebraMap O (integralClosure O L) ϖ})
    (J := Q.1) (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hb0) Q.2.isPrime
    (valPl_ne_bot Q.1)
  exact congrArg (fun n : ℕ => (((n : ℤ)) : WithTop ℤ)) hc

theorem plOf_f (Q : {Q : Ideal (integralClosure O L) // Q.IsMaximal}) :
    fres F L (plOf O L Q) = Q.1.inertiaDeg O := by
  have := Q.2
  have : Q.1.LiesOver (maximalIdeal O) := ⟨(valPl_comap Q.1).symm⟩
  rw [Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal O) Q.1]
  have hwm := plOf_mem (O := O) Q
  set w := plOf O L Q with hw_def
  letI : Field (O ⧸ maximalIdeal O) := Ideal.Quotient.field _
  letI : Field (integralClosure O L ⧸ Q.1) := Ideal.Quotient.field _
  let V := vRing w
  let V0 := V.comap (algebraMap F L)
  have hV0 : ∀ x : F, x ∈ V0 ↔ 0 ≤ (w.comap (algebraMap F L)) x := fun x => Iff.rfl
  let φO : O →+* ResidueField V0 := (residue V0).comp ((algebraMap O F).codRestrict V0
    (fun a => by
      show 0 ≤ w (algebraMap F L (algebraMap O F a))
      rw [← IsScalarTower.algebraMap_apply]; exact (hwm.2 a).1))
  have hφO : ∀ a, φO a = 0 ↔ a ∈ maximalIdeal O := by
    intro a
    simp only [φO, RingHom.comp_apply, residue_eq_zero_iff]
    rw [valPl_max_iff V0 _ hV0]
    show 0 < w (algebraMap F L (algebraMap O F a)) ↔ _
    rw [← IsScalarTower.algebraMap_apply]; exact (hwm.2 a).2
  have hsurjO : Function.Surjective φO := by
    intro r
    obtain ⟨y, rfl⟩ := residue_surjective r
    suffices h : ∃ a : O, algebraMap O F a = (y : F) by
      obtain ⟨a, ha⟩ := h; exact ⟨a, congrArg (residue V0) (Subtype.ext ha)⟩
    rcases ValuationRing.isInteger_or_isInteger O (y : F) with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨a, ha⟩
    · by_cases hy0 : (y : F) = 0
      · exact ⟨0, by rw [map_zero, hy0]⟩
      have hau : IsUnit a := by
        by_contra hna
        have hpos := (hwm.2 a).2.mpr ((mem_maximalIdeal _).mpr hna)
        rw [IsScalarTower.algebraMap_apply O F L, ha, map_inv₀] at hpos
        have hyv : 0 ≤ w (algebraMap F L y) := y.2
        have hne : algebraMap F L (y : F) ≠ 0 := (map_ne_zero _).mpr hy0
        have hs : w (algebraMap F L y)⁻¹ + w (algebraMap F L y) = 0 := by
          rw [← AddValuation.map_mul, inv_mul_cancel₀ hne, AddValuation.map_one]
        exact (ne_of_gt hpos) (valPl_wt_add_eq_zero hpos.le hyv hs)
      obtain ⟨u, rfl⟩ := hau
      refine ⟨↑u⁻¹, ?_⟩
      have h1 : algebraMap O F (↑u⁻¹ : O) * algebraMap O F (u : O) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      rw [ha] at h1
      exact (eq_inv_of_mul_eq_one_left h1).trans (inv_inv _)
  let i : (O ⧸ maximalIdeal O) ≃+* ResidueField V0 :=
    RingEquiv.ofBijective (Ideal.Quotient.lift _ φO (fun a ha => (hφO a).mpr ha))
      ⟨RingHom.injective _, fun r => by
        obtain ⟨a, ha⟩ := hsurjO r
        exact ⟨Ideal.Quotient.mk _ a, by rw [Ideal.Quotient.lift_mk]; exact ha⟩⟩
  let φB : integralClosure O L →+* ResidueField V :=
    (residue V).comp ((algebraMap (integralClosure O L) L).codRestrict V (plOf_nonneg hwm))
  have hQmem : ∀ b, b ∈ Q.1 ↔ 0 < w (algebraMap (integralClosure O L) L b) := fun b =>
    (addv_pos_iff (valPl_hv Q) b).symm
  have hφB : ∀ b ∈ Q.1, φB b = 0 := fun b hb =>
    (residue_eq_zero_iff _).mpr ((valPl_max_iff V w (valPl_mem_vRing w) _).mpr ((hQmem b).mp hb))
  have hsurjB : Function.Surjective φB := by
    intro r
    obtain ⟨y, rfl⟩ := residue_surjective r
    have hyv : (valPl_hv Q).valuation L (y : L) ≤ 1 := (addv_nonneg_iff (valPl_hv Q) _).mp y.2
    obtain ⟨n, d, hnd⟩ :=
      HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (v := valPl_hv Q) (y : L) hyv
    obtain ⟨e, i0, hi0, hde⟩ := Ideal.IsMaximal.exists_inv Q.2 d.2
    refine ⟨n * e, ?_⟩
    have h1 : φB d * φB e = 1 := by
      have : ((d : integralClosure O L) * e) = 1 - i0 := by rw [← hde]; ring
      rw [← map_mul, this, map_sub, map_one, hφB i0 hi0, sub_zero]
    have h2 : φB n = residue V y * φB d := by
      simp only [φB, RingHom.comp_apply]
      rw [← map_mul]; congr 1; apply Subtype.ext; exact hnd.symm
    rw [map_mul, h2, mul_assoc, h1, mul_one]
  let j : (integralClosure O L ⧸ Q.1) ≃+* ResidueField V :=
    RingEquiv.ofBijective (Ideal.Quotient.lift _ φB hφB)
      ⟨RingHom.injective _, fun r => by
        obtain ⟨b, hb⟩ := hsurjB r
        exact ⟨Ideal.Quotient.mk _ b, by rw [Ideal.Quotient.lift_mk]; exact hb⟩⟩
  simp only [fres]
  letI := resAlg (F := F) w
  symm
  refine Algebra.finrank_eq_of_equiv_equiv i j ?_
  apply Ideal.Quotient.ringHom_ext
  ext a
  show ResidueField.map (comapIncl V (algebraMap F L)) (φO a) =
    φB (algebraMap O (integralClosure O L) a)
  simp only [φO, φB, RingHom.comp_apply]
  erw [ResidueField.map_residue]
  apply congrArg (residue V)
  apply Subtype.ext
  show algebraMap F L (algebraMap O F a) =
    algebraMap (integralClosure O L) L (algebraMap O (integralClosure O L) a)
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

end Places

section Main

variable (O F L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [Algebra O L] [IsScalarTower O F L]
  [FiniteDimensional F L] [Algebra.IsSeparable F L]

theorem valPl {ϖ : O} (hϖ : Irreducible ϖ) (e : AddValuation L (WithTop ℤ) → ℤ)
    (he : ∀ w ∈ PlacesOver O L, (e w : WithTop ℤ) = w (algebraMap O L ϖ)) :
    (PlacesOver O L).Finite ∧
      ∑ᶠ (w : AddValuation L (WithTop ℤ)) (_ : w ∈ PlacesOver O L), (fres F L w : ℤ) * e w =
        Module.finrank F L := by
  obtain ⟨hded, -, -, -, hmf, hsum⟩ := ReciprocityTheory.MultiplicativeHeights.Closed.dedekindRank O F L
  have : IsFractionRing (integralClosure O L) L :=
    integralClosure.isFractionRing_of_finite_extension F L
  have : FaithfulSMul O L := (faithfulSMul_iff_algebraMap_injective O L).mpr (by
    rw [IsScalarTower.algebraMap_eq O F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective O F))
  have : Finite {Q : Ideal (integralClosure O L) // Q.IsMaximal} := hmf.to_subtype
  have hrange : PlacesOver O L = Set.range (plOf O L) := Set.ext fun w =>
    ⟨fun hw => mem_range_plOf hw, by rintro ⟨Q, rfl⟩; exact plOf_mem Q⟩
  refine ⟨hrange ▸ Set.finite_range _, ?_⟩
  rw [hrange, finsum_mem_range (plOf_injective (O := O) (L := L))]
  have hterm : ∀ Q : {Q : Ideal (integralClosure O L) // Q.IsMaximal},
      (fres F L (plOf O L Q) : ℤ) * e (plOf O L Q) =
        ((Q.1.ramificationIdx O * Q.1.inertiaDeg O : ℕ) : ℤ) := by
    intro Q
    have h1 := he _ (plOf_mem Q)
    rw [plOf_e Q hϖ] at h1
    have h2 : e (plOf O L Q) = (Q.1.ramificationIdx O : ℤ) := by exact_mod_cast h1
    rw [h2, plOf_f]; push_cast; ring
  simp_rw [hterm]
  have := Fintype.ofFinite {Q : Ideal (integralClosure O L) // Q.IsMaximal}
  rw [finsum_eq_sum_of_fintype] at hsum ⊢
  rw [← hsum]; push_cast; rfl

end Main

end PI.HtPlacesSumWork
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussHeights.PlaceSumHeights.PlaceSumStatements.PlaceSumLemmas.GaussValuationSums.GaussMaximalIdeal
namespace PI.HtPlacesSumWork

open NumberField IsLocalRing ReciprocityTheory.ChartRestriction.G.T0

variable {K : Type} [Field K] [NumberField K] (D N : ℕ)
  (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

theorem gauss_C_mem_iff (s : 𝓞 K) :
    (MvPolynomial.C s : OT K D N) ∈ laT D N la ↔ s ∈ la.asIdeal := by
  constructor
  · intro h
    have h' : (MvPolynomial.C s : ReciprocityTheory.ChartRestriction.G.T0.OT K D N) ∈
        Ideal.map (MvPolynomial.C : 𝓞 K →+* ReciprocityTheory.ChartRestriction.G.T0.OT K D N) la.asIdeal := h
    have h0 := (MvPolynomial.mem_map_C_iff.mp h') 0
    simpa using h0
  · intro h
    exact Ideal.mem_map_of_mem _ h

theorem gauss_unif : ∃ π ∈ la.asIdeal, π ≠ 0 ∧ ∃ s ∉ la.asIdeal,
    ∀ a ∈ la.asIdeal, ∃ b, s * a = π * b := by
  have hp0 : la.asIdeal ≠ ⊥ := la.ne_bot
  have hp1 : la.asIdeal ≠ ⊤ := la.isPrime.ne_top
  have hlt : la.asIdeal ^ 2 < la.asIdeal := by
    have := Ideal.pow_right_strictAnti la.asIdeal hp0 hp1 (show 1 < 2 by norm_num)
    simpa using this
  obtain ⟨π, hπ, hπ2⟩ := SetLike.exists_of_lt hlt
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact hπ2 (Ideal.zero_mem _)
  obtain ⟨J, hJ⟩ : la.asIdeal ∣ Ideal.span {π} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hπ)
  have hJp : ¬ J ≤ la.asIdeal := by
    intro hle
    apply hπ2
    have h1 : π ∈ la.asIdeal * J := by
      rw [← hJ]; exact Ideal.mem_span_singleton_self π
    have h2 : la.asIdeal * J ≤ la.asIdeal ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mono_right hle
    exact h2 h1
  obtain ⟨s, hsJ, hsp⟩ := SetLike.not_le_iff_exists.mp hJp
  refine ⟨π, hπ, hπ0, s, hsp, fun a ha => ?_⟩
  have hmem : a * s ∈ Ideal.span {π} := by
    rw [hJ]; exact Ideal.mul_mem_mul ha hsJ
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hmem
  exact ⟨b, by rw [mul_comm s a, ← hb, mul_comm]⟩

theorem gauss_inj : Function.Injective (algebraMap (OT K D N) (Op D N la)) :=
  IsLocalization.injective (M := (ReciprocityTheory.ChartRestriction.G.T0.laT D N la).primeCompl)
    (S := ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (Ideal.primeCompl_le_nonZeroDivisors _)

theorem gauss_maximalIdeal {π : 𝓞 K} (hπ : π ∈ la.asIdeal) {s : 𝓞 K} (hs : s ∉ la.asIdeal)
    (h : ∀ a ∈ la.asIdeal, ∃ b, s * a = π * b) :
    maximalIdeal (Op D N la) =
      Ideal.span {algebraMap (OT K D N) (Op D N la) (MvPolynomial.C π)} := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal (I := ReciprocityTheory.ChartRestriction.G.T0.laT D N la)]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    show Ideal.map (MvPolynomial.C : 𝓞 K →+* ReciprocityTheory.ChartRestriction.G.T0.OT K D N) la.asIdeal ≤ _
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_span_singleton']
    obtain ⟨b, hb⟩ := h a ha
    have hsP : (MvPolynomial.C s : ReciprocityTheory.ChartRestriction.G.T0.OT K D N) ∈ (ReciprocityTheory.ChartRestriction.G.T0.laT D N la).primeCompl :=
      fun hm => hs ((gauss_C_mem_iff D N la s).mp hm)
    obtain ⟨u, hu⟩ := IsLocalization.map_units (S := ReciprocityTheory.ChartRestriction.G.T0.Op D N la)
      (⟨_, hsP⟩ : (ReciprocityTheory.ChartRestriction.G.T0.laT D N la).primeCompl)
    have key := congrArg (fun t => algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N)
      (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (MvPolynomial.C t)) hb
    simp only [map_mul] at key
    have hu' : (u : ReciprocityTheory.ChartRestriction.G.T0.Op D N la) = algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N)
        (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (MvPolynomial.C s) := hu
    refine ⟨(↑u⁻¹ : ReciprocityTheory.ChartRestriction.G.T0.Op D N la) * algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N)
      (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (MvPolynomial.C b), ?_⟩
    symm
    calc algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N) (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (MvPolynomial.C a)
        = (↑u⁻¹ : ReciprocityTheory.ChartRestriction.G.T0.Op D N la) * ((u : ReciprocityTheory.ChartRestriction.G.T0.Op D N la) *
          algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N) (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (MvPolynomial.C a)) := by
          rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = _ := by rw [hu', key]; ring
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_map_of_mem _ ((gauss_C_mem_iff D N la π).mpr hπ)

theorem gauss_dvr : IsDiscreteValuationRing (Op D N la) := by
  obtain ⟨π, hπ, hπ0, s, hs, h⟩ := gauss_unif la
  have hmax := gauss_maximalIdeal D N la hπ hs h
  have : IsDomain (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors _)
  have : IsNoetherianRing (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) :=
    IsLocalization.isNoetherianRing (ReciprocityTheory.ChartRestriction.G.T0.laT D N la).primeCompl _ inferInstance
  have hne : algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N) (ReciprocityTheory.ChartRestriction.G.T0.Op D N la)
      (MvPolynomial.C π) ≠ 0 := by
    intro h0
    apply hπ0
    have h1 := gauss_inj D N la (h0.trans (map_zero _).symm)
    simpa using h1
  have hnf : ¬ IsField (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) := by
    intro hF
    have hmem : algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N) (ReciprocityTheory.ChartRestriction.G.T0.Op D N la)
        (MvPolynomial.C π) ∈ maximalIdeal (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) := by
      rw [hmax]; exact Ideal.mem_span_singleton_self _
    obtain ⟨y, hy⟩ := hF.mul_inv_cancel hne
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem (isUnit_iff_exists_inv.mpr ⟨y, hy⟩)
  have hprin : (maximalIdeal (ReciprocityTheory.ChartRestriction.G.T0.Op D N la)).IsPrincipal := ⟨⟨_, hmax⟩⟩
  exact ((IsDiscreteValuationRing.TFAE (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) hnf).out 1 5).mpr hprin

theorem gauss_lift (x : OT K D N) :
    OpToKT D N la (algebraMap (OT K D N) (Op D N la) x) =
      algebraMap (KTp K D N) (KTf K D N) (OTtoKT K D N x) := by
  rw [ReciprocityTheory.ChartRestriction.G.T0.OpToKT, IsLocalization.lift_eq, RingHom.comp_apply]

theorem gauss_clear (p : KTp K D N) :
    ∃ x : OT K D N, ∃ n : 𝓞 K, n ≠ 0 ∧
      OTtoKT K D N x = OTtoKT K D N (MvPolynomial.C n) * p := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    (p.support.image fun v => p.coeff v)
  have hint_r : ∀ v ∈ p.support, ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = (b : 𝓞 K) • p.coeff v := by
    intro v hv
    exact RingHom.mem_rangeS.mp (hb _ (Finset.mem_image_of_mem _ hv))
  choose! g hg using hint_r
  refine ⟨∑ v ∈ p.support, MvPolynomial.monomial v (g v), b, nonZeroDivisors.coe_ne_zero b, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ReciprocityTheory.ChartRestriction.G.T0.OTtoKT, map_sum, MvPolynomial.map_C]
  conv_rhs => rw [p.as_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [MvPolynomial.map_monomial, MvPolynomial.C_mul_monomial, hg v hv, Algebra.smul_def]

theorem gauss_frac :
    @IsFractionRing (Op D N la) _ (KTf K D N) _ (OpToKT D N la).toAlgebra := by
  letI := (ReciprocityTheory.ChartRestriction.G.T0.OpToKT D N la).toAlgebra
  have : IsDomain (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors _)
  have intInj : Function.Injective (ReciprocityTheory.ChartRestriction.G.T0.OTtoKT K D N) :=
    MvPolynomial.map_injective _ (IsFractionRing.injective (𝓞 K) K)
  have fracInj : Function.Injective (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N)) :=
    IsFractionRing.injective (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N)
  have hCinj : ∀ k : 𝓞 K, k ≠ 0 → (MvPolynomial.C k : ReciprocityTheory.ChartRestriction.G.T0.OT K D N) ≠ 0 :=
    fun k hk hC => hk (by simpa using hC)
  have hfinj : Function.Injective (ReciprocityTheory.ChartRestriction.G.T0.OpToKT D N la) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective (ReciprocityTheory.ChartRestriction.G.T0.laT D N la).primeCompl x
    have h1 := congrArg (ReciprocityTheory.ChartRestriction.G.T0.OpToKT D N la)
      (IsLocalization.mk'_spec (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) a t)
    rw [map_mul, hx, zero_mul, gauss_lift] at h1
    have ha : a = 0 := by
      apply intInj
      apply fracInj
      rw [map_zero, map_zero]
      exact h1.symm
    subst ha
    show IsLocalization.mk' (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (0 : ReciprocityTheory.ChartRestriction.G.T0.OT K D N) t = 0
    rw [IsLocalization.mk'_zero]
  refine ⟨fun y => ?_, fun z => ?_, fun {x y} hxy => ?_⟩
  · apply isUnit_iff_ne_zero.mpr
    intro h0
    exact nonZeroDivisors.coe_ne_zero y (hfinj (h0.trans (map_zero _).symm))
  · obtain ⟨P, Q, hQ, rfl⟩ := IsFractionRing.div_surjective (A := ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) z
    obtain ⟨a, n, hn, ha⟩ := gauss_clear D N P
    obtain ⟨b, m, hm, hb⟩ := gauss_clear D N Q
    have hQ0 : Q ≠ 0 := nonZeroDivisors.ne_zero hQ
    have hQ' : algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) Q ≠ 0 :=
      fun h0 => hQ0 (fracInj (h0.trans (map_zero _).symm))
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [map_zero] at hb
      have hc : ReciprocityTheory.ChartRestriction.G.T0.OTtoKT K D N (MvPolynomial.C m) = 0 := by
        rcases mul_eq_zero.mp hb.symm with hc | hc
        · exact hc
        · exact absurd hc hQ0
      exact hCinj m hm (intInj (hc.trans (map_zero _).symm))
    have hden : algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N) (ReciprocityTheory.ChartRestriction.G.T0.Op D N la)
        (b * MvPolynomial.C n) ∈ nonZeroDivisors (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) :=
      mem_nonZeroDivisors_of_ne_zero fun h0 => (mul_ne_zero hb0 (hCinj n hn))
        (gauss_inj D N la (h0.trans (map_zero _).symm))
    refine ⟨⟨algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N) (ReciprocityTheory.ChartRestriction.G.T0.Op D N la)
      (a * MvPolynomial.C m), ⟨_, hden⟩⟩, ?_⟩
    show algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) P /
        algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) Q *
        ReciprocityTheory.ChartRestriction.G.T0.OpToKT D N la (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N)
          (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (b * MvPolynomial.C n)) =
      ReciprocityTheory.ChartRestriction.G.T0.OpToKT D N la (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.OT K D N)
          (ReciprocityTheory.ChartRestriction.G.T0.Op D N la) (a * MvPolynomial.C m))
    rw [gauss_lift, gauss_lift]
    simp only [map_mul, ha, hb]
    rw [div_mul_eq_mul_div, div_eq_iff hQ']
    ring
  · exact ⟨1, by rw [hfinj hxy]⟩

end PI.HtPlacesSumWork
end

namespace PI.HtPlacesSumWork

open NumberField IsLocalRing ReciprocityTheory.ChartRestriction.G.T0

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {Ω : ι → Type}
  [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] {WT : Type} [AddCommGroup WT] {A : ι → Type}
  [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]

theorem places_over_height_one_prime (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c))
    (d : Data K ι Ω WT A) : LeafSt.places_over_la 𝒜 d := by
  intro hd h la c
  letI : Algebra (Op d.D d.N la) (KTf K d.D d.N) := (OpToKT d.D d.N la).toAlgebra
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  letI : Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := (d.OpToS h la c).toAlgebra
  have : IsScalarTower (Op d.D d.N la) (KTf K d.D d.N) (OmS (Ω c) d.D d.N) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsDiscreteValuationRing (Op d.D d.N la) := gauss_dvr d.D d.N la
  have : IsFractionRing (Op d.D d.N la) (KTf K d.D d.N) := by
    let f := algebraMap (KTp K d.D d.N) (KTf K d.D d.N)
    let g := OTtoKT K d.D d.N
    have hf : Function.Injective f := IsFractionRing.injective _ _
    have hg : Function.Injective g :=
      MvPolynomial.map_injective _ (IsFractionRing.injective (𝓞 K) K)
    have hinj : Function.Injective (OpToKT d.D d.N la) := by
      apply (IsLocalization.injective_iff_map_algebraMap_eq (laT d.D d.N la).primeCompl _).2
      intro x y
      refine ⟨congrArg (OpToKT d.D d.N la), fun hxy => ?_⟩
      rw [gauss_lift, gauss_lift] at hxy
      exact congrArg _ (hg (hf hxy))
    have : FaithfulSMul (Op d.D d.N la) (KTf K d.D d.N) :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
    apply IsFractionRing.of_field
    intro z
    obtain ⟨P, Q, hQ, rfl⟩ := IsFractionRing.div_surjective (A := KTp K d.D d.N) z
    obtain ⟨a, n, hn, ha⟩ := gauss_clear d.D d.N P
    obtain ⟨b, m, hm, hb⟩ := gauss_clear d.D d.N Q
    have hC (k : 𝓞 K) (hk : k ≠ 0) : f (g (MvPolynomial.C k)) ≠ 0 :=
      (map_ne_zero_iff (f.comp g) (hf.comp hg)).2 (MvPolynomial.C_ne_zero.mpr hk)
    have hQ' : f Q ≠ 0 := (map_ne_zero_iff f hf).2 (nonZeroDivisors.ne_zero hQ)
    refine ⟨algebraMap (OT K d.D d.N) (Op d.D d.N la) (a * MvPolynomial.C m),
      algebraMap (OT K d.D d.N) (Op d.D d.N la) (b * MvPolynomial.C n), ?_⟩
    change f P / f Q = OpToKT d.D d.N la (algebraMap _ _ (a * MvPolynomial.C m)) /
      OpToKT d.D d.N la (algebraMap _ _ (b * MvPolynomial.C n))
    rw [gauss_lift, gauss_lift]
    change f P / f Q = f (g (a * MvPolynomial.C m)) / f (g (b * MvPolynomial.C n))
    change g a = g (MvPolynomial.C n) * P at ha
    change g b = g (MvPolynomial.C m) * Q at hb
    simp only [map_mul, ha, hb]
    apply (div_eq_div_iff hQ' (mul_ne_zero (mul_ne_zero (hC m hm) hQ') (hC n hn))).2
    ring
  have : FiniteDimensional (d.KT c) (OmS (Ω c) d.D d.N) := d.KT_finiteDimensional hd c
  let e : KTf K d.D d.N ≃+* d.KT c :=
    (d.KTtoS h c).rangeRestrictFieldEquiv.trans (RingEquiv.subfieldCongr (d.KTtoS_fieldRange h c))
  have hc : (algebraMap (KTf K d.D d.N) (OmS (Ω c) d.D d.N)).comp e.symm.toRingHom =
      (RingEquiv.refl (OmS (Ω c) d.D d.N)).toRingHom.comp (algebraMap (d.KT c) (OmS (Ω c) d.D d.N)) := by
    refine RingHom.ext fun y => ?_
    have he (z : KTf K d.D d.N) : (e z : OmS (Ω c) d.D d.N) = d.KTtoS h c z := rfl
    change d.KTtoS h c (e.symm y) = (y : OmS (Ω c) d.D d.N)
    rw [← he, RingEquiv.apply_symm_apply]
  have : FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) :=
    Module.Finite.of_equiv_equiv e.symm (RingEquiv.refl _) hc
  have hrk : Module.finrank (KTf K d.D d.N) (OmS (Ω c) d.D d.N) = d.delc c :=
    (Algebra.finrank_eq_of_equiv_equiv e.symm (RingEquiv.refl _) hc).symm
  have : Algebra.IsSeparable (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := inferInstance
  have hcomp : ∀ x : OT K d.D d.N,
      algebraMap (Op d.D d.N la) (OmS (Ω c) d.D d.N) (algebraMap (OT K d.D d.N) (Op d.D d.N la) x) =
        d.OTtoS c x := by
    intro x
    show d.KTtoS h c (OpToKT d.D d.N la (algebraMap _ _ x)) = _
    rw [gauss_lift]
    exact IsFractionRing.lift_algebraMap _ _
  have hset : d.PlOver la c = PlacesOver (Op d.D d.N la) (OmS (Ω c) d.D d.N) := by
    ext w
    constructor
    · rintro ⟨hnd, hw⟩
      refine ⟨hnd, fun a => ?_⟩
      obtain ⟨⟨x, m⟩, rfl⟩ := IsLocalization.mk'_surjective (laT d.D d.N la).primeCompl a
      have hm0 : w (d.OTtoS c m) = 0 :=
        le_antisymm (not_lt.mp fun hp => m.2 ((hw m).2.mp hp)) (hw m).1
      have hsp := congrArg (algebraMap (Op d.D d.N la) (OmS (Ω c) d.D d.N))
        (IsLocalization.mk'_spec (Op d.D d.N la) x m)
      rw [map_mul, hcomp, hcomp] at hsp
      have hv := congrArg w hsp
      rw [AddValuation.map_mul, hm0, add_zero] at hv
      rw [hv, IsLocalization.AtPrime.mk'_mem_maximal_iff (S := Op d.D d.N la) (I := laT d.D d.N la)]
      exact hw x
    · rintro ⟨hnd, hO⟩
      refine ⟨hnd, fun x => ?_⟩
      rw [← hcomp x, ← IsLocalization.AtPrime.to_map_mem_maximal_iff (Op d.D d.N la) (laT d.D d.N la)]
      exact hO _
  obtain ⟨π, hπ, hπ0, s, hs, hps⟩ := gauss_unif la
  have hmax := gauss_maximalIdeal d.D d.N la hπ hs hps
  have hϖ : Irreducible (algebraMap (OT K d.D d.N) (Op d.D d.N la) (MvPolynomial.C π)) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax
  have hWres : ∀ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (a : 𝓞 K),
      d.Wres c w (algebraMap K (Ω c) (a : K)) = w (d.OTtoS c (MvPolynomial.C a)) := by
    intro w a
    show w (algebraMap (Ω c) (OmS (Ω c) d.D d.N) (algebraMap K (Ω c) (a : K))) = _
    congr 1
    show _ = d.sH c (MvPolynomial.map (algebraMap (𝓞 K) K) (MvPolynomial.C a))
    rw [MvPolynomial.map_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]
  have hne : d.OTtoS c (MvPolynomial.C π) ≠ 0 := by
    rw [← hcomp]
    intro h0
    have h1 : algebraMap (Op d.D d.N la) (KTf K d.D d.N)
        (algebraMap (OT K d.D d.N) (Op d.D d.N la) (MvPolynomial.C π)) = 0 :=
      (d.KTtoS h c).injective (by rw [map_zero]; exact h0)
    have h2 : algebraMap (OT K d.D d.N) (Op d.D d.N la) (MvPolynomial.C π) = 0 :=
      (IsFractionRing.injective (Op d.D d.N la) (KTf K d.D d.N)) (by rw [h1, map_zero])
    have h3 : (MvPolynomial.C π : OT K d.D d.N) = 0 :=
      gauss_inj d.D d.N la (by rw [map_zero]; exact h2)
    exact hπ0 (by simpa using h3)
  have he : ∀ w ∈ PlacesOver (Op d.D d.N la) (OmS (Ω c) d.D d.N),
      ((ramIdx (d.Wres c w) la : ℤ) : WithTop ℤ) = w (algebraMap (Op d.D d.N la)
        (OmS (Ω c) d.D d.N) (algebraMap (OT K d.D d.N) (Op d.D d.N la) (MvPolynomial.C π))) := by
    intro w hw
    rw [hcomp]
    obtain ⟨n0, hn0⟩ := WithTop.ne_top_iff_exists.mp (hw.1.1 _ hne)
    rw [← hn0]
    suffices hr : ramIdx (d.Wres c w) la = n0 by rw [hr]
    apply IsLeast.csInf_eq
    refine ⟨⟨π, hπ, hπ0, by rw [hWres, hn0]⟩, ?_⟩
    rintro n ⟨a, ha, -, hna⟩
    rw [hWres] at hna
    have hmem : algebraMap (OT K d.D d.N) (Op d.D d.N la) (MvPolynomial.C a) ∈
        maximalIdeal (Op d.D d.N la) := by
      rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (Op d.D d.N la) (laT d.D d.N la)]
      exact Ideal.mem_map_of_mem _ ha
    rw [hmax, Ideal.mem_span_singleton'] at hmem
    obtain ⟨y, hy⟩ := hmem
    have hv := congrArg (fun t => w (algebraMap (Op d.D d.N la) (OmS (Ω c) d.D d.N) t)) hy
    simp only [map_mul, AddValuation.map_mul, hcomp] at hv
    rw [← hn0, hna] at hv
    have hle : (n0 : WithTop ℤ) ≤ n := by
      rw [← hv]; exact le_add_of_nonneg_left (hw.2 y).1
    exact_mod_cast hle
  have key := valPl (Op d.D d.N la) (KTf K d.D d.N) (OmS (Ω c) d.D d.N) hϖ
    (fun w => ramIdx (d.Wres c w) la) he
  rw [hset]
  refine ⟨key.1, ?_⟩
  rw [← hrk]
  exact key.2

end PI.HtPlacesSumWork
end

open NumberField

theorem HtPlacesSum {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {Ω : ι → Type}
    [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] {WT : Type} [AddCommGroup WT] {A : ι → Type}
    [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
    [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c))
    (d : ReciprocityTheory.ChartRestriction.G.T0.Data K ι Ω WT A) : ReciprocityTheory.ChartRestriction.G.T0.LeafSt.places_over_la 𝒜 d :=
  PI.HtPlacesSumWork.places_over_height_one_prime 𝒜 d
end

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem places_over_la (hd : d.AxH 𝒜) (h : d.S1) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (c : ι) :
    (d.PlOver la c).Finite ∧
      (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.PlOver la c),
        (d.fze h c w : ℤ) * ramIdx (K := K) (d.Wres c w) la) = d.delc c :=
  HtPlacesSum 𝒜 d hd h la c

end Data

end ReciprocityTheory.ChartRestriction.G.T0
