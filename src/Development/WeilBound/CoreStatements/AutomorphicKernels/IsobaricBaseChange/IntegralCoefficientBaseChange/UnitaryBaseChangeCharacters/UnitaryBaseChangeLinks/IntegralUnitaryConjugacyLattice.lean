module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.CharpolyDvdOfAevalEqZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormApproximationFirstLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedAdjoinRootOfSeparable
namespace GlobalTheory.ReducedAdjoinRootSeparable

theorem isReduced_adjoinRoot_of_separable {k : Type} [Field k] {f : Polynomial k}
    (hf : f.Separable) : IsReduced (AdjoinRoot f) := by
  have h1 : IsRadical f := isRadical_iff_squarefree_or_zero.2 (Or.inl hf.squarefree)
  have h2 : (Ideal.span {f}).IsRadical := isRadical_iff_span_singleton.1 h1
  exact (Ideal.isRadical_iff_quotient_reduced _).1 h2

end GlobalTheory.ReducedAdjoinRootSeparable
end

open Polynomial Matrix Formalism.UG

namespace GlobalTheory.NormEq

theorem eq_zero_of_forall_mem_maxSpec {A : Type} [CommRing A] [IsArtinianRing A] [IsReduced A] {y : A}
    (h : ∀ I : MaximalSpectrum A, y ∈ I.asIdeal) : y = 0 := by
  apply (IsArtinianRing.equivPi A).injective
  rw [map_zero]
  funext I
  rw [IsArtinianRing.equivPi_apply]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (h I)

theorem exists_mul_invol_eq_of_fixed_unit {R : Type} [CommRing R] [Finite R] [IsReduced R]
    (τ : R →+* R) (hτ : ∀ a, τ (τ a) = a) {b : R} (hb : IsUnit (τ b - b)) {x : R} (hx : IsUnit x)
    (hxτ : τ x = x) : ∃ z : R, IsUnit z ∧ z * τ z = x := by
  classical
  haveI : IsArtinianRing R := inferInstance
  have hsurj : Function.Surjective τ := fun a => ⟨τ a, hτ a⟩
  obtain ⟨tI, hmem, htt⟩ : ∃ tI : MaximalSpectrum R → MaximalSpectrum R,
      (∀ I y, y ∈ (tI I).asIdeal ↔ τ y ∈ I.asIdeal) ∧ ∀ I, tI (tI I) = I := by
    have hmax : ∀ I : MaximalSpectrum R, (I.asIdeal.comap τ).IsMaximal := fun I => by
      haveI := I.isMaximal
      exact Ideal.comap_isMaximal_of_surjective τ hsurj
    refine ⟨fun I => ⟨I.asIdeal.comap τ, hmax I⟩, fun I y => Iff.rfl, fun I => ?_⟩
    ext y
    change τ (τ y) ∈ I.asIdeal ↔ y ∈ I.asIdeal
    rw [hτ]
  have hnot : ∀ (I : MaximalSpectrum R) {u : R}, IsUnit u → u ∉ I.asIdeal := fun I u hu hI =>
    I.isMaximal.ne_top (Ideal.eq_top_of_isUnit_mem _ hI hu)

  have hfixed : ∀ I : MaximalSpectrum R, ∃ a : R, tI I = I → a * τ a - x ∈ I.asIdeal := by
    intro I
    by_cases hI : tI I = I
    · have hle : I.asIdeal ≤ I.asIdeal.comap τ := fun y hy => by
        rw [Ideal.mem_comap, ← hmem, hI]; exact hy
      haveI := I.isMaximal
      letI : Field (R ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
      haveI : Finite (R ⧸ I.asIdeal) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
      let ρ := Ideal.quotientMap I.asIdeal τ hle
      have hρ : ∀ y, ρ (Ideal.Quotient.mk I.asIdeal y) = Ideal.Quotient.mk I.asIdeal (τ y) :=
        fun y => Ideal.quotientMap_mk
      have hinv : Function.Involutive ρ := fun c => by
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective c
        rw [hρ, hρ, hτ]
      have hne : ∃ c, ρ c ≠ c := ⟨Ideal.Quotient.mk I.asIdeal b, fun h => by
        rw [hρ, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem] at h
        exact hnot I hb h⟩
      obtain ⟨a', ha'⟩ := GlobalTheory.exists_mul_invol_eq_of_fixed (R ⧸ I.asIdeal) ρ hinv hne
        (Ideal.Quotient.mk I.asIdeal x) (by rw [hρ, hxτ])
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
      refine ⟨a, fun _ => ?_⟩
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ← hρ, ha', sub_self]
    · exact ⟨0, fun h => absurd h hI⟩
  choose a ha using hfixed
  let r : MaximalSpectrum R → R := fun I =>
    if WellOrderingRel I (tI I) then x else if WellOrderingRel (tI I) I then 1 else a I
  obtain ⟨z, hz⟩ : ∃ z : R, ∀ I, z - r I ∈ I.asIdeal := by
    refine ⟨(IsArtinianRing.equivPi R).symm (fun I => Ideal.Quotient.mk I.asIdeal (r I)), fun I => ?_⟩
    have h1 := congrFun ((IsArtinianRing.equivPi R).apply_symm_apply
      (fun I => Ideal.Quotient.mk I.asIdeal (r I))) I
    rw [IsArtinianRing.equivPi_apply] at h1
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, sub_self]
  have hτz : ∀ I, τ z - τ (r (tI I)) ∈ I.asIdeal := fun I => by
    rw [← map_sub, ← hmem]; exact hz (tI I)
  have hfix_of : ∀ I, ¬ WellOrderingRel I (tI I) → ¬ WellOrderingRel (tI I) I → tI I = I := fun I h1 h2 => by
    rcases trichotomous_of WellOrderingRel I (tI I) with h | h | h
    · exact absurd h h1
    · exact h.symm
    · exact absurd h h2
  have key : ∀ I : MaximalSpectrum R, z * τ z - x ∈ I.asIdeal ∧ z ∉ I.asIdeal := by
    intro I
    have hzI := hz I
    have hτzI := hτz I
    by_cases h1 : WellOrderingRel I (tI I)
    · have e1 : r I = x := if_pos h1
      have e2 : r (tI I) = 1 := by
        simp only [r, htt]
        rw [if_neg (asymm_of WellOrderingRel h1), if_pos h1]
      rw [e1] at hzI
      rw [e2, map_one] at hτzI
      refine ⟨?_, fun hzm => hnot I hx (by simpa using I.asIdeal.sub_mem hzm hzI)⟩
      have : z * τ z - x = (z - x) * τ z + x * (τ z - 1) := by ring
      rw [this]
      exact I.asIdeal.add_mem (I.asIdeal.mul_mem_right _ hzI) (I.asIdeal.mul_mem_left _ hτzI)
    · by_cases h2 : WellOrderingRel (tI I) I
      · have e1 : r I = 1 := by simp only [r]; rw [if_neg h1, if_pos h2]
        have e2 : r (tI I) = x := by
          simp only [r, htt]
          rw [if_pos h2]
        rw [e1] at hzI
        rw [e2, hxτ] at hτzI
        refine ⟨?_, fun hzm => hnot I isUnit_one (by simpa using I.asIdeal.sub_mem hzm hzI)⟩
        have : z * τ z - x = (z - 1) * τ z + (τ z - x) := by ring
        rw [this]
        exact I.asIdeal.add_mem (I.asIdeal.mul_mem_right _ hzI) hτzI
      · have hI := hfix_of I h1 h2
        have e1 : r I = a I := by simp only [r]; rw [if_neg h1, if_neg h2]
        rw [e1] at hzI
        rw [hI, e1] at hτzI
        have haI := ha I hI
        refine ⟨?_, fun hzm => ?_⟩
        · have : z * τ z - x = (z - a I) * τ z + a I * (τ z - τ (a I)) + (a I * τ (a I) - x) := by ring
          rw [this]
          exact I.asIdeal.add_mem (I.asIdeal.add_mem (I.asIdeal.mul_mem_right _ hzI)
            (I.asIdeal.mul_mem_left _ hτzI)) haI
        · have haM : a I ∈ I.asIdeal := by simpa using I.asIdeal.sub_mem hzm hzI
          exact hnot I hx (by simpa using I.asIdeal.sub_mem (I.asIdeal.mul_mem_right (τ (a I)) haM) haI)
  refine ⟨z, ?_, sub_eq_zero.1 (eq_zero_of_forall_mem_maxSpec fun I => (key I).1)⟩
  by_contra hu
  obtain ⟨M, hM, hzM⟩ := exists_max_ideal_of_mem_nonunits (show z ∈ nonunits R from hu)
  exact (key ⟨M, hM⟩).2 hzM

end GlobalTheory.NormEq

namespace GlobalTheory.NormEq

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mul_ofAdd_one_le_of_lt_one {a : WithZero (Multiplicative ℤ)} (ha : a < 1) :
    a * ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤ 1 := by
  induction a using WithZero.recZeroCoe with
  | zero => simp
  | coe m =>
    rw [← WithZero.coe_one, WithZero.coe_lt_coe] at ha
    rw [← WithZero.coe_mul, ← WithZero.coe_one, WithZero.coe_le_coe]
    rw [← ofAdd_toAdd m, ← ofAdd_add, ← ofAdd_zero, Multiplicative.ofAdd_le]
    rw [← ofAdd_toAdd m, ← ofAdd_zero, Multiplicative.ofAdd_lt] at ha
    omega

theorem mem_span_piO_of_lt {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (y : intL L)
    (hy : Valued.v (y : L) < 1) : y ∈ Ideal.span {piO h} := by
  have hϖ : ϖ ≠ 0 := by
    intro h0
    have := h.2.2.2.1
    rw [h0, map_zero] at this
    exact WithZero.zero_ne_coe this
  have hc : (y : L) / ϖ ∈ intL L := by
    change Valued.v ((y : L) / ϖ) ≤ 1
    rw [map_div₀, h.2.2.2.1, div_eq_mul_inv, ← WithZero.coe_inv, ← ofAdd_neg, neg_neg]
    exact mul_ofAdd_one_le_of_lt_one hy
  rw [Ideal.mem_span_singleton']
  exact ⟨⟨_, hc⟩, Subtype.ext (by simp [div_mul_cancel₀ _ hϖ])⟩

theorem isUnit_of_v_eq_one (y : intL L) (hy : Valued.v (y : L) = 1) : IsUnit y := by
  have hy0 : (y : L) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hy; exact zero_ne_one hy
  have hinv : (y : L)⁻¹ ∈ intL L := by
    change Valued.v ((y : L)⁻¹) ≤ 1
    rw [map_inv₀, hy, inv_one]
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (by simp [hy0])⟩

theorem span_piO_isMaximal {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) :
    (Ideal.span {piO h}).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h1 => ?_, fun J y _ hy hyJ => ?_⟩
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
    have hv := congrArg (fun t : intL L => Valued.v (t : L)) hc
    simp only [Subring.coe_mul, coe_piO, map_mul, h.2.2.2.1, OneMemClass.coe_one, map_one] at hv
    have hc1 : Valued.v (c : L) ≤ 1 := c.2
    have hlt : Valued.v (c : L) * ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < 1 :=
      calc Valued.v (c : L) * ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
          ≤ 1 * ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by gcongr
        _ < 1 := by
          rw [one_mul]
          exact_mod_cast (WithZero.coe_lt_coe.2 (by decide : (Multiplicative.ofAdd (-1 : ℤ)) < 1))
    exact absurd hv hlt.ne
  · have hv : Valued.v (y : L) = 1 := by
      rcases lt_or_eq_of_le (show Valued.v (y : L) ≤ 1 from y.2) with hl | he
      · exact absurd (mem_span_piO_of_lt h y hl) hy
      · exact he
    rw [Ideal.eq_top_of_isUnit_mem J hyJ (isUnit_of_v_eq_one y hv)]
    trivial

theorem finite_quot_span_piO {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) :
    Finite (intL L ⧸ Ideal.span {piO h}) := by
  let V := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  have hc := h.2.2.2.2.2.2
  have hq := h.2.2.2.2.2.1
  have hfin0 := Nat.finite_of_card_ne_zero (hc.trans_ne (by positivity))
  haveI : Finite (V ⧸ IsLocalRing.maximalIdeal V) := hfin0
  let f : V →+* intL L :=
    { toFun := fun y => ⟨(y : L), (Valuation.mem_valuationSubring_iff _ _).1 y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hker : ∀ y ∈ IsLocalRing.maximalIdeal V, (Ideal.Quotient.mk (Ideal.span {piO h})).comp f y = 0 := by
    intro y hy
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    by_contra hn
    have hv : Valued.v (y : L) = 1 := by
      rcases lt_or_eq_of_le (show Valued.v (y : L) ≤ 1 from (f y).2) with hl | he
      · exact absurd (mem_span_piO_of_lt h (f y) hl) hn
      · exact he
    apply (IsLocalRing.mem_maximalIdeal _).1 hy
    have hy0 : (y : L) ≠ 0 := by
      intro h0; rw [h0, map_zero] at hv; exact zero_ne_one hv
    have hinv : (y : L)⁻¹ ∈ V := by
      rw [Valuation.mem_valuationSubring_iff, map_inv₀, hv, inv_one]
    exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (show (y : L) * (y : L)⁻¹ = 1 from mul_inv_cancel₀ hy0)⟩
  let g := Ideal.Quotient.lift (IsLocalRing.maximalIdeal V) ((Ideal.Quotient.mk (Ideal.span {piO h})).comp f) hker
  refine Finite.of_surjective g fun a => ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨Ideal.Quotient.mk _ ⟨(y : L), (Valuation.mem_valuationSubring_iff _ _).2 y.2⟩, ?_⟩
  rfl

theorem isReduced_adjoinRoot_of_separable {k : Type} [Field k] {f : k[X]} (hf : f.Separable) :
    IsReduced (AdjoinRoot f) := by
  first
  | exact @_root_.GlobalTheory.ReducedAdjoinRootSeparable.isReduced_adjoinRoot_of_separable
  | exact _root_.GlobalTheory.ReducedAdjoinRootSeparable.isReduced_adjoinRoot_of_separable
  | (apply _root_.GlobalTheory.ReducedAdjoinRootSeparable.isReduced_adjoinRoot_of_separable <;> assumption)
  | (intros; apply _root_.GlobalTheory.ReducedAdjoinRootSeparable.isReduced_adjoinRoot_of_separable <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ReducedAdjoinRootSeparable.isReduced_adjoinRoot_of_separable <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ReducedAdjoinRootSeparable.isReduced_adjoinRoot_of_separable ..)

theorem exists_mul_conj_sub_mem_piPow_one : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))]
    (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)),
    P.1.Separable → ∀ x : (GlobalTheory.UTr.Alg P)ˣ, x ∈ GlobalTheory.UTr.plus P → ∃ u : (GlobalTheory.UTr.Alg P)ˣ,
      (x : GlobalTheory.UTr.Alg P) - (u : GlobalTheory.UTr.Alg P) * GlobalTheory.UTr.conj P u ∈ GlobalTheory.NormEq.piPow h P 1 := by
  intro L _ _ σ ϖ q h P hP x hx
  classical
  let I0 : Ideal (intL L) := Ideal.span {piO h}
  haveI : I0.IsMaximal := span_piO_isMaximal h
  letI : Field (intL L ⧸ I0) := Ideal.Quotient.field I0
  haveI : Finite (intL L ⧸ I0) := finite_quot_span_piO h
  let J : Ideal (GlobalTheory.UTr.Alg P) := piPow h P 1
  have hJ : J = (Ideal.map (AdjoinRoot.of P.1) I0 : Ideal (GlobalTheory.UTr.Alg P)) := by
    change Ideal.span {algebraMap (intL L) (GlobalTheory.UTr.Alg P) (piO h) ^ 1} =
      Ideal.map (AdjoinRoot.of P.1) (Ideal.span {piO h})
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    exact pow_one _
  let e1 : (GlobalTheory.UTr.Alg P ⧸ J) ≃+* (GlobalTheory.UTr.Alg P ⧸ (Ideal.map (AdjoinRoot.of P.1) I0 : Ideal (GlobalTheory.UTr.Alg P))) :=
    Ideal.quotEquivOfEq hJ
  let e2 : (GlobalTheory.UTr.Alg P ⧸ (Ideal.map (AdjoinRoot.of P.1) I0 : Ideal (GlobalTheory.UTr.Alg P))) ≃+*
      AdjoinRoot (P.1.map (Ideal.Quotient.mk I0)) :=
    AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot I0 P.1
  let e := e1.trans e2
  haveI : IsReduced (AdjoinRoot (P.1.map (Ideal.Quotient.mk I0))) :=
    isReduced_adjoinRoot_of_separable (hP.map)
  haveI : IsReduced (GlobalTheory.UTr.Alg P ⧸ J) := isReduced_of_injective e.toRingHom e.injective
  haveI : Module.Finite (intL L ⧸ I0) (AdjoinRoot (P.1.map (Ideal.Quotient.mk I0))) :=
    (AdjoinRoot.powerBasis' (P.2.1.map (Ideal.Quotient.mk I0))).finite
  haveI : Finite (AdjoinRoot (P.1.map (Ideal.Quotient.mk I0))) := Module.finite_of_finite (intL L ⧸ I0)
  haveI : Finite (GlobalTheory.UTr.Alg P ⧸ J) := Finite.of_equiv _ e.symm.toEquiv

  have hsig : ∀ b, sigO σ h.2.1 (sigO σ h.2.1 b) = b := fun b => Subtype.ext (h.1 b)
  have hsp : sigO σ h.2.1 (piO h) = piO h := Subtype.ext h.2.2.1
  set_option backward.isDefEq.respectTransparency false in
  have hle : J ≤ J.comap (GlobalTheory.UTr.conj P) := Ideal.span_le.2 (Set.singleton_subset_iff.2 (by
    change GlobalTheory.UTr.conj P ((algebraMap (intL L) (GlobalTheory.UTr.Alg P) (piO h)) ^ 1) ∈ J
    simp only [pow_one, GlobalTheory.UTr.conj_algebraMap, hsp]
    exact Ideal.subset_span (by simp only [Set.mem_singleton_iff, pow_one]; rfl)))
  let τ := Ideal.quotientMap J (GlobalTheory.UTr.conj P) hle
  have hτ' : ∀ y, τ (Ideal.Quotient.mk J y) = Ideal.Quotient.mk J (GlobalTheory.UTr.conj P y) :=
    fun y => by simpa only [τ] using (Ideal.quotientMap_mk (H := hle) (x := y))
  have hτ : ∀ a, τ (τ a) = a := fun a => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [hτ', hτ', GlobalTheory.UTr.conj_conj P hsig]

  obtain ⟨x0, hx0, hv⟩ := h.2.2.2.2.1
  let d : intL L := sigO σ h.2.1 ⟨x0, hx0⟩ - ⟨x0, hx0⟩
  have hd : IsUnit d := isUnit_of_v_eq_one d (by change Valued.v (σ x0 - x0) = 1; exact hv)
  let b : GlobalTheory.UTr.Alg P ⧸ J := Ideal.Quotient.mk J (algebraMap (intL L) _ ⟨x0, hx0⟩)
  have hb : IsUnit (τ b - b) := by
    have : τ b - b = Ideal.Quotient.mk J (algebraMap (intL L) (GlobalTheory.UTr.Alg P) d) := by
      simp only [b, hτ', GlobalTheory.UTr.conj_algebraMap, d, map_sub]
    rw [this]
    exact (hd.map _).map _
  have hxu : IsUnit (Ideal.Quotient.mk J (x : GlobalTheory.UTr.Alg P)) := x.isUnit.map _
  have hxτ : τ (Ideal.Quotient.mk J (x : GlobalTheory.UTr.Alg P)) = Ideal.Quotient.mk J (x : GlobalTheory.UTr.Alg P) := by
    rw [hτ', GlobalTheory.UTr.mem_plus.1 hx]
  obtain ⟨zb, hzb, hzz⟩ := exists_mul_invol_eq_of_fixed_unit τ hτ hb hxu hxτ
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective zb
  obtain ⟨wb, hw⟩ := hzb.exists_right_inv
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective wb
  set_option backward.isDefEq.respectTransparency false in
  have hzw : IsUnit (z * w) := isUnit_of_sub_one_mem h P le_rfl (by
    change z * w - 1 ∈ J
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hw, map_one, sub_self])
  have hz : IsUnit z := isUnit_of_mul_isUnit_left hzw
  refine ⟨hz.unit, ?_⟩
  rw [IsUnit.unit_spec]
  change _ ∈ J
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ← hτ', hzz, sub_self]

end GlobalTheory.NormEq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFiltrationComplete
open Polynomial Matrix Formalism.UG

noncomputable section

open Filter Topology

namespace GlobalTheory.NormEq.Cmpl

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem exists_pow_lt {w γ : WithZero (Multiplicative ℤ)}
    (hw : w = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) (hγ : γ ≠ 0) :
    ∃ N : ℕ, w ^ N < γ := by
  subst hw
  obtain ⟨g, rfl⟩ := WithZero.ne_zero_iff_exists.mp hγ
  refine ⟨(-Multiplicative.toAdd g).toNat + 1, ?_⟩
  rw [← WithZero.coe_pow, WithZero.coe_lt_coe, ← ofAdd_toAdd g, ← ofAdd_nsmul, Multiplicative.ofAdd_lt]
  simp only [toAdd_ofAdd, smul_neg, nsmul_eq_mul, mul_one]
  omega

theorem ball_mem_nhds_of_ne {x c : L} (hc : c ≠ 0) : {y | Valued.v (y - x) < Valued.v c} ∈ 𝓝 x := by
  rw [Valued.mem_nhds]
  have h' : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).restrict c ≠ 0 := by simp [hc]
  exact ⟨Units.mk0 _ h', fun y hy => (Valuation.restrict_lt_iff _).1 hy⟩

theorem exists_lim_of_cauchy [CompleteSpace L] {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (s : ℕ → L) (hsO : ∀ n, Valued.v (s n) ≤ 1)
    (hs : ∀ N : ℕ, ∃ M, ∀ m ≥ M, ∀ n ≥ M, Valued.v (s n - s m) ≤ Valued.v ϖ ^ N) :
    ∃ ℓ, Valued.v ℓ ≤ 1 ∧ ∀ N : ℕ, ∀ᶠ n in atTop, Valued.v (s n - ℓ) ≤ Valued.v ϖ ^ N := by
  have hϖ0 : ϖ ≠ 0 := fun h0 => by rw [h0, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  have hcs : CauchySeq s := by
    rw [(Valued.hasBasis_uniformity L (WithZero (Multiplicative ℤ))).cauchySeq_iff]
    intro γ _
    obtain ⟨c, hc⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective
      (.ofClass (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))) γ.1
    have hc' : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).restrict c = γ.1 := hc
    have hc0 : Valued.v c ≠ 0 := by
      intro h0
      rw [(Valued.v).zero_iff.mp h0, map_zero] at hc'
      exact γ.ne_zero hc'.symm
    obtain ⟨N, hN⟩ := exists_pow_lt hϖ hc0
    obtain ⟨M, hM⟩ := hs N
    refine ⟨M, fun m hm n hn => ?_⟩
    change (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).restrict (s n - s m) < γ.1
    rw [← hc', Valuation.restrict_lt_iff]
    exact lt_of_le_of_lt (hM m hm n hn) hN
  obtain ⟨ℓ, hℓ⟩ := cauchySeq_tendsto_of_complete hcs
  have hev : ∀ N : ℕ, ∀ᶠ n in atTop, Valued.v (s n - ℓ) < Valued.v ϖ ^ N := fun N => by
    have := hℓ (ball_mem_nhds_of_ne (x := ℓ) (pow_ne_zero N hϖ0))
    simpa [map_pow] using this
  refine ⟨ℓ, ?_, fun N => (hev N).mono fun n hn => hn.le⟩
  obtain ⟨n, hn⟩ := (hev 0).exists
  rw [pow_zero] at hn
  have e : ℓ = s n - (s n - ℓ) := by ring
  rw [e]
  exact (Valued.v.map_sub _ _).trans (max_le (hsO n) hn.le)

variable {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (sigO σ h.2.1))

theorem mem_piPow_iff {N : ℕ} {a : GlobalTheory.UTr.Alg P} :
    a ∈ piPow h P N ↔ ∀ i, Valued.v (((GlobalTheory.UTr.powBasis P).repr a i : intL L) : L) ≤ Valued.v ϖ ^ N := by
  with_unfolding_all
    unfold GlobalTheory.UTr.Alg at *
    have hϖ0 : ϖ ≠ 0 := fun h0 => by
      have := h.2.2.2.1; rw [h0, map_zero] at this; exact WithZero.zero_ne_coe this
    constructor
    · intro ha i
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      set_option backward.isDefEq.respectTransparency false in
        rw [← map_pow, mul_comm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, Subring.coe_mul,
        SubmonoidClass.coe_pow, coe_piO, map_mul, map_pow]
      calc _ ≤ Valued.v ϖ ^ N * 1 := mul_le_mul' le_rfl (((GlobalTheory.UTr.powBasis P).repr c i).2)
        _ = _ := mul_one _
    · intro ha
      have hϖN : ϖ ^ N ≠ 0 := pow_ne_zero _ hϖ0
      let d : Fin P.1.natDegree → intL L := fun i => ⟨((GlobalTheory.UTr.powBasis P).repr a i : L) / ϖ ^ N, by
        change Valued.v (((GlobalTheory.UTr.powBasis P).repr a i : L) / ϖ ^ N) ≤ 1
        rw [map_div₀, map_pow]
        exact (div_le_one₀ (zero_lt_iff.mpr (pow_ne_zero _ ((Valued.v).ne_zero_iff.mpr hϖ0)))).mpr (ha i)⟩
      refine Ideal.mem_span_singleton'.mpr ⟨(GlobalTheory.UTr.powBasis P).equivFun.symm d, ?_⟩
      refine (GlobalTheory.UTr.powBasis P).ext_elem fun i => ?_
      have hd : (GlobalTheory.UTr.powBasis P).repr ((GlobalTheory.UTr.powBasis P).equivFun.symm d) i = d i := by
        rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
      set_option backward.isDefEq.respectTransparency false in
        rw [← map_pow, mul_comm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, hd]
      apply Subtype.ext
      rw [Subring.coe_mul, SubmonoidClass.coe_pow, coe_piO]
      exact mul_div_cancel₀ _ hϖN

theorem eq_zero_of_forall_mem_piPow {z : GlobalTheory.UTr.Alg P} (hz : ∀ N, z ∈ piPow h P N) : z = 0 := by
  refine (GlobalTheory.UTr.powBasis P).ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply]
  by_contra hne
  have hne' : (((GlobalTheory.UTr.powBasis P).repr z i : intL L) : L) ≠ 0 := fun h0 => hne (Subtype.ext h0)
  obtain ⟨N, hN⟩ := exists_pow_lt h.2.2.2.1 ((Valued.v).ne_zero_iff.mpr hne')
  exact absurd ((mem_piPow_iff h P).mp (hz N) i) (not_le.mpr hN)

theorem exists_lim_alg [CompleteSpace L] (a : ℕ → GlobalTheory.UTr.Alg P)
    (ha : ∀ N, ∃ M, ∀ m ≥ M, ∀ n ≥ M, a n - a m ∈ piPow h P N) :
    ∃ y, ∀ N, ∀ᶠ n in atTop, a n - y ∈ piPow h P N := by
  have hco : ∀ i, ∃ ℓ : L, Valued.v ℓ ≤ 1 ∧ ∀ N : ℕ, ∀ᶠ n in atTop,
      Valued.v ((((GlobalTheory.UTr.powBasis P).repr (a n) i : intL L) : L) - ℓ) ≤ Valued.v ϖ ^ N := by
    intro i
    refine exists_lim_of_cauchy h.2.2.2.1 _ (fun n => ((GlobalTheory.UTr.powBasis P).repr (a n) i).2) fun N => ?_
    obtain ⟨M, hM⟩ := ha N
    refine ⟨M, fun m hm n hn => ?_⟩
    have := (mem_piPow_iff h P).mp (hM m hm n hn) i
    rwa [map_sub, Finsupp.sub_apply, AddSubgroupClass.coe_sub] at this
  choose ℓ hℓO hℓ using hco
  refine ⟨(GlobalTheory.UTr.powBasis P).equivFun.symm (fun i => ⟨ℓ i, hℓO i⟩), fun N => ?_⟩
  filter_upwards [Filter.eventually_all.mpr (fun i => hℓ i N)] with n hn
  rw [mem_piPow_iff]
  intro i
  have hd : (GlobalTheory.UTr.powBasis P).repr ((GlobalTheory.UTr.powBasis P).equivFun.symm (fun i => ⟨ℓ i, hℓO i⟩)) i =
      ⟨ℓ i, hℓO i⟩ := by
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [map_sub, Finsupp.sub_apply, hd, AddSubgroupClass.coe_sub]
  exact hn i

end GlobalTheory.NormEq.Cmpl

namespace GlobalTheory.NormEq


open Cmpl in
theorem filtrationComplete_filt : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)),
    GroundTheory.LocalField.FiltrationComplete (GlobalTheory.NormEq.filt h P) := by
  with_unfolding_all
    intro L _ _ _ σ ϖ q h P x hx
    have ha : ∀ N, ∃ M, ∀ m ≥ M, ∀ n ≥ M, (((x n).val : (AdjoinRoot P.1)) - (x m).val) ∈ piPow h P N := by
      intro N
      obtain ⟨M, hM⟩ := hx N
      refine ⟨M, fun m hm n hn => ?_⟩
      have h1 : ((x n / x m : ((AdjoinRoot P.1))ˣ) : (AdjoinRoot P.1)) - 1 ∈ piPow h P N := hM m hm n hn
      have e : ((x n).val : (AdjoinRoot P.1)) - x m = ((x m).val : (AdjoinRoot P.1)) * (((x n / x m : ((AdjoinRoot P.1))ˣ) : (AdjoinRoot P.1)) - 1) := by
        rw [div_eq_mul_inv, Units.val_mul]
        linear_combination (-((x n).val : (AdjoinRoot P.1))) * (x m).mul_inv
      rw [e]; exact Ideal.mul_mem_left _ _ h1
    have hb : ∀ N, ∃ M, ∀ m ≥ M, ∀ n ≥ M,
        (((x n)⁻¹ : ((AdjoinRoot P.1))ˣ) : (AdjoinRoot P.1)) - ((x m)⁻¹ : ((AdjoinRoot P.1))ˣ) ∈ piPow h P N := by
      intro N
      obtain ⟨M, hM⟩ := hx N
      refine ⟨M, fun m hm n hn => ?_⟩
      have h1 : ((x n / x m : ((AdjoinRoot P.1))ˣ) : (AdjoinRoot P.1)) - 1 ∈ piPow h P N := hM m hm n hn
      have e : (((x n)⁻¹ : ((AdjoinRoot P.1))ˣ) : (AdjoinRoot P.1)) - ((x m)⁻¹ : ((AdjoinRoot P.1))ˣ) =
          -(((x n)⁻¹ : ((AdjoinRoot P.1))ˣ) : (AdjoinRoot P.1)) * (((x n / x m : ((AdjoinRoot P.1))ˣ) : (AdjoinRoot P.1)) - 1) := by
        rw [div_eq_mul_inv, Units.val_mul]
        linear_combination (((x m)⁻¹ : ((AdjoinRoot P.1))ˣ) : (AdjoinRoot P.1)) * (x n).inv_mul
      rw [e]; exact Ideal.mul_mem_left _ _ h1
    obtain ⟨y, hy⟩ := exists_lim_alg h P _ ha
    obtain ⟨y', hy'⟩ := exists_lim_alg h P _ hb
    unfold GlobalTheory.UTr.Alg at y y' hy hy'
    have hyy : y * y' = 1 := by
      rw [← sub_eq_zero]
      refine eq_zero_of_forall_mem_piPow h P fun N => ?_
      obtain ⟨n, hn1, hn2⟩ := ((hy N).and (hy' N)).exists
      have e : y * y' - 1 = -(((x n).val : (AdjoinRoot P.1)) - y) * y' -
          ((x n).val : (AdjoinRoot P.1)) * ((((x n)⁻¹ : ((AdjoinRoot P.1))ˣ) : (AdjoinRoot P.1)) - y') := by
        linear_combination (x n).mul_inv
      rw [e]
      exact (piPow h P N).sub_mem ((piPow h P N).mul_mem_right _ ((piPow h P N).neg_mem hn1))
        ((piPow h P N).mul_mem_left _ hn2)
    refine ⟨⟨y, y', hyy, by rw [mul_comm]; exact hyy⟩, fun N => ?_⟩
    obtain ⟨M, hM⟩ := eventually_atTop.mp (hy N)
    refine ⟨M, fun n hn => ?_⟩
    rw [mem_filt, div_eq_mul_inv, Units.val_mul, Units.inv_mk, Units.val_mk]
    have e : ((x n).val : (AdjoinRoot P.1)) * y' - 1 = (((x n).val : (AdjoinRoot P.1)) - y) * y' := by
      linear_combination hyy
    rw [e]
    exact (piPow h P N).mul_mem_right _ (hM n hn)

end GlobalTheory.NormEq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormApproximationFiltration
open Polynomial Matrix Formalism.UG

noncomputable section

namespace GlobalTheory.NormEq

theorem exists_norm_lift_step : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)) (m : ℕ), 1 ≤ m → ∀ x : (GlobalTheory.UTr.Alg P)ˣ, x ∈ GlobalTheory.UTr.plus P → x ∈ GlobalTheory.NormEq.filt h P m → ∃ u : (GlobalTheory.UTr.Alg P)ˣ, u ∈ GlobalTheory.NormEq.filt h P m ∧ (x : GlobalTheory.UTr.Alg P) - (u : GlobalTheory.UTr.Alg P) * GlobalTheory.UTr.conj P u ∈ GlobalTheory.NormEq.piPow h P (m + 1) := by
  intro L _ _ σ ϖ q h P m hm x hx hxm
  obtain ⟨x₀, hx₀, hv⟩ := h.2.2.2.2.1
  have hve : Valued.v (x₀ - σ x₀) = 1 := by rw [← Valuation.map_neg, neg_sub]; exact hv
  have he : x₀ - σ x₀ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hve; exact zero_ne_one hve
  have hcO : x₀ * (x₀ - σ x₀)⁻¹ ∈ intL L := by
    change Valued.v (x₀ * (x₀ - σ x₀)⁻¹) ≤ 1
    rw [map_mul, map_inv₀, hve, inv_one, mul_one]; exact hx₀
  let cO : intL L := ⟨_, hcO⟩
  have hcs : cO + sigO σ h.2.1 cO = 1 := by
    apply Subtype.ext
    change x₀ * (x₀ - σ x₀)⁻¹ + σ (x₀ * (x₀ - σ x₀)⁻¹) = 1
    have e2 : σ x₀ - x₀ = -(x₀ - σ x₀) := by ring
    rw [map_mul, map_inv₀, map_sub, h.1, e2, inv_neg]
    field_simp
    ring
  set ι := algebraMap (intL L) (GlobalTheory.UTr.Alg P) with hι
  set πA := ι (piO h) with hπA
  have hconjπ : GlobalTheory.UTr.conj P πA = πA := by
    rw [hπA, GlobalTheory.UTr.conj_algebraMap]; congr 1; exact Subtype.ext h.2.2.1
  have hconjc : GlobalTheory.UTr.conj P (ι cO) + ι cO = 1 := by
    have := congrArg ι hcs
    rw [map_add (f := _), map_one] at this
    rw [hι, GlobalTheory.UTr.conj_algebraMap]; rw [← this]; ring
  have h1 : (x : GlobalTheory.UTr.Alg P) - 1 ∈ Ideal.span {πA ^ m} := hxm
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h1
  have hxc : GlobalTheory.UTr.conj P (x : GlobalTheory.UTr.Alg P) = x := (GlobalTheory.UTr.mem_plus (P := P)).1 hx
  have hca : πA ^ m * GlobalTheory.UTr.conj P a = πA ^ m * a := by
    have := congrArg (GlobalTheory.UTr.conj P) ha
    rw [map_mul, map_pow, hconjπ, map_sub, map_one, hxc] at this
    rw [mul_comm, this, ← ha, mul_comm]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hu1 : (1 + πA ^ (k + 1) * (ι cO * a)) - 1 ∈ GlobalTheory.NormEq.piPow h P (k + 1) := by
    rw [add_sub_cancel_left]; exact Ideal.mem_span_singleton'.2 ⟨ι cO * a, mul_comm _ _⟩
  refine ⟨(GlobalTheory.NormEq.isUnit_of_sub_one_mem h P hm hu1).unit, hu1, ?_⟩
  change (x : GlobalTheory.UTr.Alg P) - (1 + πA ^ (k + 1) * (ι cO * a)) *
    GlobalTheory.UTr.conj P (1 + πA ^ (k + 1) * (ι cO * a)) ∈ Ideal.span {πA ^ (k + 1 + 1)}
  have e1 : GlobalTheory.UTr.conj P (1 + πA ^ (k + 1) * (ι cO * a)) =
      1 + πA ^ (k + 1) * (GlobalTheory.UTr.conj P (ι cO) * GlobalTheory.UTr.conj P a) := by
    rw [map_add (f := _), map_one, map_mul, map_pow, hconjπ, map_mul]
  rw [e1, Ideal.mem_span_singleton']
  refine ⟨-(πA ^ k * ι cO * a * GlobalTheory.UTr.conj P (ι cO) * GlobalTheory.UTr.conj P a), ?_⟩
  linear_combination ha + GlobalTheory.UTr.conj P (ι cO) * hca + πA ^ (k + 1) * a * hconjc

end GlobalTheory.NormEq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateSelfReciprocalCharpoly
open Polynomial Matrix Formalism.UG

namespace GlobalTheory.UTr

theorem isCsr_charpoly_of_cT_mul_eq_one : ∀ (R : Type) [CommRing R] (s : R →+* R) (n : ℕ)
    (M : Matrix (Fin n) (Fin n) R), cT s M * M = 1 → GlobalTheory.UTr.IsCsr s M.charpoly := by
  intro R _ s n M hM
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  set N := cT s M with hNdef
  have hdeg : M.charpoly.natDegree = n := by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hdegN : N.charpoly.natDegree = n := by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hmap : M.charpoly.map s = N.charpoly := by
    rw [← Matrix.charpoly_map, ← Matrix.charpoly_transpose]; rfl
  have hrev : (M.charpoly.map s).reflect n = N.charpolyRev := by
    rw [hmap, ← Matrix.reverse_charpoly, Polynomial.reverse, hdegN]
  have hdetN : N.det * M.det = 1 := by rw [← Matrix.det_mul, hM, Matrix.det_one]
  have hNd : N.det = s M.det := by
    rw [hNdef, cT, Matrix.det_transpose, RingHom.map_det]; rfl
  have h0 : M.charpoly.coeff 0 = (-1) ^ n * M.det := by
    rw [Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg,
      one_pow, one_mul]
  have hs0 : s (M.charpoly.coeff 0) = (-1) ^ n * N.det := by
    rw [h0, map_mul, map_pow, map_neg, map_one, hNd]
  refine ⟨Matrix.charpoly_monic M, ?_⟩
  rw [hdeg, hrev, Matrix.charpolyRev, hs0]
  have hA : (1 - (X : R[X]) • N.map C) * M.map C = -charmatrix M := by
    rw [sub_mul, one_mul, smul_mul_assoc, ← Matrix.map_mul, hM, Matrix.map_one _ (map_zero C) (map_one C),
      charmatrix, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply, neg_sub]; rfl
  have e1 : (1 - (X : R[X]) • N.map C).det * C M.det = (-1) ^ n * M.charpoly := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.det_mul, hA, Matrix.det_neg, Fintype.card_fin]; rfl
  have e2 : C N.det * C M.det = (1 : R[X]) := by rw [← C_mul, hdetN, C_1]
  rw [C_mul, C_pow, C_neg, C_1]
  linear_combination (-C N.det) * e1 + (1 - (X : R[X]) • N.map C).det * e2

end GlobalTheory.UTr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemAllPowers
open Polynomial Matrix Formalism.UG

noncomputable section

namespace GlobalTheory.NormEq

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem eq_zero_of_forall_v_le {c : L}
    (hc : ∀ m : ℕ, Valued.v c ≤ ((Multiplicative.ofAdd (-(m : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    c = 0 := by
  by_contra h0
  have hv : Valued.v c ≠ 0 := (_root_.map_ne_zero _).2 h0
  obtain ⟨g, hg⟩ := WithZero.ne_zero_iff_exists.1 hv
  have := hc (1 - Multiplicative.toAdd g).toNat
  rw [← hg, WithZero.coe_le_coe] at this
  have h2 : Multiplicative.toAdd g ≤ -(((1 - Multiplicative.toAdd g).toNat : ℕ) : ℤ) := by
    have := Multiplicative.toAdd_le.2 this
    simpa using this
  omega

theorem int_eq_zero_of_forall_dvd {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) {c : intL L}
    (hc : ∀ m : ℕ, piO h ^ m ∣ c) : c = 0 := by
  refine Subtype.ext (eq_zero_of_forall_v_le fun m => ?_)
  obtain ⟨d, hd⟩ := hc m
  have hd' : (c : L) = ϖ ^ m * (d : L) := by
    rw [hd]; simp
  have hdv : Valued.v (d : L) ≤ 1 := d.2
  rw [hd', map_mul, map_pow, h.2.2.2.1]
  calc ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ m * Valued.v (d : L)
      ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ m * 1 := by gcongr
    _ = _ := by
      rw [mul_one, ← WithZero.coe_pow, ← ofAdd_nsmul]
      congr 2
      simp

theorem eq_zero_of_forall_mem_piPow {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q)
    (P : GlobalTheory.UTr.Csr (sigO σ h.2.1)) (a : GlobalTheory.UTr.Alg P) (ha : ∀ m, a ∈ piPow h P m) : a = 0 := by
  refine (GlobalTheory.UTr.powBasis P).ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply]
  refine int_eq_zero_of_forall_dvd h fun m => ?_
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (ha m)
  refine ⟨(GlobalTheory.UTr.powBasis P).repr b i, ?_⟩
  have he : b * (algebraMap (intL L) (GlobalTheory.UTr.Alg P)) (piO h) ^ m =
      (piO h ^ m) • b := by
    rw [Algebra.smul_def, map_pow, mul_comm]
  change b * (algebraMap (intL L) (GlobalTheory.UTr.Alg P)) (piO h) ^ m = a at hb
  rw [← hb, he, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem sep : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (ϖ : L) (q : ℕ)
    (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)) (a : GlobalTheory.UTr.Alg P),
    (∀ m, a ∈ GlobalTheory.NormEq.piPow h P m) → a = 0 :=
  fun _ _ _ _ _ _ h P a ha => eq_zero_of_forall_mem_piPow h P a ha

end GlobalTheory.NormEq
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.NormApproximationFirstLevel
open Polynomial Matrix Formalism.UG
theorem _root_.GlobalTheory.T.norm_approximation_first_level : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)), P.1.Separable → ∀ x : (GlobalTheory.UTr.Alg P)ˣ, x ∈ GlobalTheory.UTr.plus P → ∃ u : (GlobalTheory.UTr.Alg P)ˣ, (x : GlobalTheory.UTr.Alg P) - (u : GlobalTheory.UTr.Alg P) * GlobalTheory.UTr.conj P u ∈ GlobalTheory.NormEq.piPow h P 1 := by
  first | exact @GlobalTheory.NormEq.exists_mul_conj_sub_mem_piPow_one | exact GlobalTheory.NormEq.exists_mul_conj_sub_mem_piPow_one | (intros; apply GlobalTheory.NormEq.exists_mul_conj_sub_mem_piPow_one <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.NormFiltrationComplete
open Polynomial Matrix Formalism.UG
theorem _root_.GlobalTheory.T.norm_filtration_complete : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)), GroundTheory.LocalField.FiltrationComplete (GlobalTheory.NormEq.filt h P) := by
  first | exact @GlobalTheory.NormEq.filtrationComplete_filt | exact GlobalTheory.NormEq.filtrationComplete_filt | (intros; apply GlobalTheory.NormEq.filtrationComplete_filt <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.NormApproximationFiltration
open Polynomial Matrix Formalism.UG
theorem _root_.GlobalTheory.T.norm_approximation_filtration : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)) (m : ℕ), 1 ≤ m → ∀ x : (GlobalTheory.UTr.Alg P)ˣ, x ∈ GlobalTheory.UTr.plus P → x ∈ GlobalTheory.NormEq.filt h P m → ∃ u : (GlobalTheory.UTr.Alg P)ˣ, u ∈ GlobalTheory.NormEq.filt h P m ∧ (x : GlobalTheory.UTr.Alg P) - (u : GlobalTheory.UTr.Alg P) * GlobalTheory.UTr.conj P u ∈ GlobalTheory.NormEq.piPow h P (m + 1) := by
  first | exact @GlobalTheory.NormEq.exists_norm_lift_step | (intros; apply GlobalTheory.NormEq.exists_norm_lift_step <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.ConjugateSelfReciprocalCharpoly
open Polynomial Matrix Formalism.UG
theorem _root_.GlobalTheory.T.conjugate_self_reciprocal_charpoly : ∀ (R : Type) [CommRing R] (s : R →+* R) (n : ℕ) (M : Matrix (Fin n) (Fin n) R), cT s M * M = 1 → GlobalTheory.UTr.IsCsr s M.charpoly := by
  first | exact @GlobalTheory.UTr.isCsr_charpoly_of_cT_mul_eq_one | (intros; apply GlobalTheory.UTr.isCsr_charpoly_of_cT_mul_eq_one <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.EqZeroOfMemAllPowers
open Polynomial Matrix Formalism.UG
theorem _root_.GlobalTheory.T.eq_zero_of_mem_all_powers : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)) (a : GlobalTheory.UTr.Alg P), (∀ m, a ∈ GlobalTheory.NormEq.piPow h P m) → a = 0 := by
  first | exact @GlobalTheory.NormEq.sep | (intros; apply GlobalTheory.NormEq.sep <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.IntegralUnitaryConjugacyLattice
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.NormEq

open GlobalTheory.UTr GroundTheory.LocalField

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem sigO_piO {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) : sigO σ h.2.1 (piO h) = piO h :=
  Subtype.ext h.2.2.1

theorem conj_mem_piPow {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : Csr (sigO σ h.2.1)) (m : ℕ)
    {a : Alg P} (ha : a ∈ piPow h P m) : conj P a ∈ piPow h P m := by
  set_option backward.isDefEq.respectTransparency false in
    unfold piPow at *
    simp only [Ideal.mem_span_singleton] at ha ⊢
    obtain ⟨b, rfl⟩ := ha
    have hp : conj P (algebraMap (intL L) (Alg P) (piO h)) = algebraMap (intL L) (Alg P) (piO h) :=
      (GlobalTheory.UTr.conj_algebraMap P _).trans (congrArg _ (sigO_piO h))
    exact ⟨conj P b, by
      rw [map_mul, map_pow]
      exact congrArg (fun x : Alg P => x ^ m * conj P b) hp⟩

theorem normU_mem_filt {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (P : Csr (sigO σ h.2.1)) (m : ℕ)
    {g : (Alg P)ˣ} (hg : g ∈ filt h P m) : normU P g ∈ filt h P m := by
  set_option backward.isDefEq.respectTransparency false in
    change (g : Alg P) - 1 ∈ piPow h P m at hg
    change ((normU P g : (Alg P)ˣ) : Alg P) - 1 ∈ piPow h P m
    have hc : conj P (g : Alg P) - 1 ∈ piPow h P m := by
      have := conj_mem_piPow h P m hg
      rwa [map_sub, map_one] at this
    have e : ((normU P g : (Alg P)ˣ) : Alg P) - 1 = ((g : Alg P) - 1) * conj P (g : Alg P) + (conj P (g : Alg P) - 1) := by
      rw [val_normU]; ring
    rw [e]
    exact (piPow h P m).add_mem ((piPow h P m).mul_mem_right _ hg) hc

theorem div_mem_of_sub_mem {R : Type} [CommRing R] {I : Ideal R} {x u : Rˣ} (hx : (x : R) - u ∈ I) :
    ((x / u : Rˣ) : R) - 1 ∈ I := by
  have e : ((x / u : Rˣ) : R) - 1 = ((x : R) - u) * ((u⁻¹ : Rˣ) : R) := by
    rw [div_eq_mul_inv, Units.val_mul, sub_mul, Units.mul_inv]
  rw [e]; exact I.mul_mem_right _ hx

theorem normU_surj (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) (P : Csr (sigO σ h.2.1)) (hP : P.1.Separable)
    (x : (Alg P)ˣ) (hx : x ∈ plus P) : ∃ u : (Alg P)ˣ, normU P u = x := by
  have hs : ∀ b, sigO σ h.2.1 (sigO σ h.2.1 b) = b := fun b => Subtype.ext (h.1 b)
  let f : (Alg P)ˣ →* plus P := (normU P).codRestrict (plus P) (normU_mem_plus P hs)
  let E : ℕ → Subgroup (plus P) := fun m => (filt h P m).comap (plus P).subtype
  have hE : Antitone E := fun a b hab => Subgroup.comap_mono (filt_antitone h P hab)
  have hsepE : FiltrationSeparated E := by
    intro g hg
    have h0 : ((g : (Alg P)ˣ) : Alg P) - 1 = 0 := GlobalTheory.T.eq_zero_of_mem_all_powers L σ ϖ q h P _ fun m => hg m
    exact Subtype.ext (Units.ext (sub_eq_zero.1 h0))
  have hE0 : E (id 0) = ⊤ := by
    ext g; change ((g : (Alg P)ˣ) ∈ filt h P 0) ↔ True
    rw [filt_zero]; exact ⟨fun _ => trivial, fun _ => Subgroup.mem_top _⟩
  have hmap : ∀ n, ∀ g ∈ filt h P n, f g ∈ E (id n) := fun n g hg => normU_mem_filt h P n hg
  have hgr : ∀ n, ∀ z ∈ E (id n), ∃ g ∈ filt h P n, z / f g ∈ E (id (n + 1)) := by
    intro n z hz
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · obtain ⟨u, hu⟩ := GlobalTheory.T.norm_approximation_first_level L σ ϖ q h P hP z.1 z.2
      refine ⟨u, by rw [filt_zero]; exact Subgroup.mem_top u, ?_⟩
      show ((z.1 / normU P u : (Alg P)ˣ) : Alg P) - 1 ∈ piPow h P (0 + 1)
      exact div_mem_of_sub_mem hu
    · obtain ⟨u, hu, hu'⟩ := GlobalTheory.T.norm_approximation_filtration L σ ϖ q h P n hn z.1 z.2 hz
      refine ⟨u, hu, ?_⟩
      show ((z.1 / normU P u : (Alg P)ˣ) : Alg P) - 1 ∈ piPow h P (n + 1)
      exact div_mem_of_sub_mem hu'
  obtain ⟨u, hu⟩ := surjective_of_graded_surjective (F := filt h P) (E := E) (filt_antitone h P) hE
    (GlobalTheory.T.norm_filtration_complete L σ ϖ q h P) hsepE f tendsto_id (filt_zero h P) hE0 hmap hgr ⟨x, hx⟩
  exact ⟨u, congrArg Subtype.val hu⟩

end GlobalTheory.NormEq

namespace GlobalTheory.NormEq
open GlobalTheory.UTr

theorem hermUnit_eq_norm : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (σ : L →+* L) (ϖ : L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n : ℕ) (y : Matrix (Fin n) (Fin n) L) (Q₀ : (intL L)[X]), (∀ i j, y i j ∈ intL L) → cT σ y * y = 1 → y.charpoly = Q₀.map (intL L).subtype → Q₀.Separable → ∀ t : GL (Fin n) L, (∀ i j, t.val i j ∈ intL L) → (∀ i j, (t⁻¹ : GL (Fin n) L).val i j ∈ intL L) → cT σ t.val = t.val → (∃ p : (intL L)[X], t.val = aeval y (p.map (intL L).subtype)) → ∃ s : GL (Fin n) L, s.val * y = y * s.val ∧ s.val * cT σ s.val = t.val := by
  intro L _ _ _ σ ϖ q h n y Q₀ hy hyu hch hsep t ht hti htc ⟨p, hp⟩
  let sO := sigO σ h.2.1
  let Φ : Matrix (Fin n) (Fin n) (intL L) →+* Matrix (Fin n) (Fin n) L := (intL L).subtype.mapMatrix
  have hΦinj : Function.Injective Φ := fun a b hab => by
    ext i j; exact congrFun (congrFun hab i) j
  let yO : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨y i j, hy i j⟩
  have hyO : Φ yO = y := rfl
  have hΦcT : ∀ M, Φ (cT sO M) = cT σ (Φ M) := fun M => rfl
  have hchO : yO.charpoly = Q₀ := by
    apply Polynomial.map_injective _ (intL L).subtype_injective
    rw [← hch, ← hyO]
    exact (Matrix.charpoly_map yO (intL L).subtype).symm
  have hyuO : cT sO yO * yO = 1 := hΦinj (by rw [map_mul, hΦcT, hyO, hyu, map_one])
  have hcsr : IsCsr sO Q₀ := hchO ▸ GlobalTheory.T.conjugate_self_reciprocal_charpoly _ sO n yO hyuO
  let P : Csr sO := ⟨Q₀, hcsr⟩
  have hg : aeval yO P.1 = 0 := by
    show aeval yO Q₀ = 0
    rw [← hchO]; exact Matrix.aeval_self_charpoly yO
  let ev := evalMat P yO hg
  have hev : ∀ r : (intL L)[X], ev (aeval (root P) r) = aeval yO r := fun r => by
    rw [← aeval_algHom_apply, evalMat_root]
  have hevinj : ∀ z, ev z = 0 → z = 0 := by
    intro z hz
    obtain ⟨r, rfl⟩ := exists_aeval_root P z
    rw [hev] at hz
    have hd := GlobalTheory.T.charpoly_dvd_of_aeval_eq_zero_alt (intL L) n yO r (hchO ▸ hsep) hz
    rw [hchO] at hd
    exact (aeval_root_eq_zero_iff P).2 hd
  have hevinj' : Function.Injective ev := (injective_iff_map_eq_zero ev).2 hevinj
  have hcomp : Φ.comp (algebraMap (intL L) (Matrix (Fin n) (Fin n) (intL L))) =
      (algebraMap L (Matrix (Fin n) (Fin n) L)).comp (intL L).subtype := by
    ext a i j
    simp only [RingHom.coe_comp, Function.comp_apply, Φ, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.algebraMap_matrix_apply]
    split_ifs <;> simp
  have hΦaeval : ∀ r : (intL L)[X], Φ (aeval yO r) = aeval y (r.map (intL L).subtype) := by
    intro r
    rw [aeval_def, aeval_def, Polynomial.hom_eval₂, eval₂_map, hcomp, hyO]

  let tz : Alg P := aeval (root P) p
  let tO := ev tz
  have htO : Φ tO = t.val := by rw [show tO = aeval yO p from hev p, hΦaeval, hp]
  let tiO : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨(t⁻¹ : GL (Fin n) L).val i j, hti i j⟩
  have htiO : tO * tiO = 1 := hΦinj (by
    rw [map_mul, htO, map_one]; exact t.mul_inv)
  have hdet : IsUnit tO.det := isUnit_iff_exists_inv.2 ⟨tiO.det, by rw [← Matrix.det_mul, htiO, Matrix.det_one]⟩
  have hunit : IsUnit tz := by
    have h0 : aeval tz tO.charpoly = 0 := hevinj _ (by
      rw [← aeval_algHom_apply]; exact Matrix.aeval_self_charpoly tO)
    have hc0 : IsUnit (tO.charpoly.coeff 0) := by
      have := Matrix.det_eq_sign_charpoly_coeff tO
      rw [this] at hdet
      exact isUnit_of_mul_isUnit_right hdet
    have e := congrArg (aeval tz) (X_mul_divX_add tO.charpoly)
    rw [h0, map_add (f := _), map_mul, aeval_X, aeval_C] at e
    have hu : IsUnit (tz * aeval tz tO.charpoly.divX) := by
      rw [eq_neg_of_add_eq_zero_left e]
      exact (hc0.map _).neg
    exact isUnit_of_mul_isUnit_left hu
  let T : (Alg P)ˣ := hunit.unit

  have hyuO' : yO * cT sO yO = 1 := mul_eq_one_comm.1 hyuO
  let gU : UJ sO (1 : Matrix (Fin n) (Fin n) (intL L)) :=
    ⟨⟨yO, cT sO yO, hyuO', hyuO⟩, by
      show cT sO yO * 1 * yO = 1
      rw [Matrix.mul_one, hyuO]⟩
  have hcT : ∀ z, cT sO (ev z) = ev (conj P z) := fun z => by
    have := cT_evalMat P gU hg z
    rwa [Matrix.mul_one, Matrix.one_mul] at this
  have htz : conj P tz = tz := hevinj' (by
    rw [← hcT]
    exact hΦinj (by rw [hΦcT, htO, htc]))
  have hT : T ∈ plus P := (GlobalTheory.UTr.mem_plus (P := P)).2 htz
  obtain ⟨u, hu⟩ := normU_surj L σ ϖ q h P hsep T hT
  let Ψ : Alg P →* Matrix (Fin n) (Fin n) L := (Φ.comp ev.toRingHom : Alg P →+* _)
  refine ⟨Units.map Ψ u, ?_, ?_⟩
  · show Φ (ev u) * y = y * Φ (ev u)
    rw [← hyO, ← map_mul, ← map_mul]
    congr 1
    rw [← evalMat_root P yO hg, ← map_mul, ← map_mul, mul_comm]
  · show Φ (ev u) * cT σ (Φ (ev u)) = t.val
    rw [← hΦcT, hcT, ← map_mul, ← map_mul, ← val_normU, hu, ← htO]
    rfl

end GlobalTheory.NormEq
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.IntegralUnitaryConjugacyLatticeStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.exists_commute_mul_cT_eq_of_integral_hermitian_polynomial : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (σ : L →+* L) (ϖ : L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n : ℕ) (y : Matrix (Fin n) (Fin n) L) (Q₀ : (intL L)[X]), (∀ i j, y i j ∈ intL L) → cT σ y * y = 1 → y.charpoly = Q₀.map (intL L).subtype → Q₀.Separable → ∀ t : GL (Fin n) L, (∀ i j, t.val i j ∈ intL L) → (∀ i j, (t⁻¹ : GL (Fin n) L).val i j ∈ intL L) → cT σ t.val = t.val → (∃ p : (intL L)[X], t.val = aeval y (p.map (intL L).subtype)) → ∃ s : GL (Fin n) L, s.val * y = y * s.val ∧ s.val * cT σ s.val = t.val := by
  first | exact @GlobalTheory.NormEq.hermUnit_eq_norm | (intros; apply GlobalTheory.NormEq.hermUnit_eq_norm <;> assumption)
end
