module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PLocMax
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma red_art {R : Type} [CommRing R] [IsArtinianRing R] [IsReduced R] (y : R) :
    ∃ z, y * (1 - y * z) = 0 := by
  obtain ⟨n, w, hw⟩ := IsArtinian.exists_pow_succ_smul_dvd y (1 : R)
  simp only [smul_eq_mul, mul_one] at hw
  refine ⟨w, IsReduced.eq_zero _ ⟨n + 1, ?_⟩⟩
  have h : y ^ n * (1 - y * w) = 0 := by
    rw [mul_sub, mul_one, ← mul_assoc, ← pow_succ, hw, sub_self]
  rw [mul_pow, pow_succ, pow_succ]
  calc y ^ n * y * ((1 - y * w) ^ n * (1 - y * w))
      = y * (1 - y * w) ^ n * (y ^ n * (1 - y * w)) := by ac_rfl
    _ = 0 := by rw [h, mul_zero]

private theorem exists_const_sub_mem_span_tco_of_mem_rA {F L : Type} [Field F] [Field L] [Algebra ℂ F] [Algebra ℂ L] [Algebra F L]
    [IsScalarTower ℂ F L] (d : ℕ) (x : Fin (d + 1) → Fˣ) (f : F) (hf : f ∈ rA ℂ (xv x) {0}) :
    ∃ c : ℂ, ∃ hb : algebraMap F L f ∈ rB ℂ L (xv x) {0},
      (⟨_, hb⟩ : rB ℂ L (xv x) {0}) - algebraMap ℂ _ c ∈ Ideal.span (Set.range fun j : Fin d =>
        (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0})) := by
  have memB : ∀ g ∈ rA ℂ (xv x) {0}, algebraMap F L g ∈ rB ℂ L (xv x) {0} := by
    intro g hg
    rw [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
    exact isIntegral_algebraMap (x := (⟨g, hg⟩ : rA ℂ (xv x) {0}))
  unfold rA at hf
  induction hf using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨i, hi, j, rfl⟩ := hy
    rw [Finset.mem_singleton] at hi
    subst hi
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
    · refine ⟨1, memB _ (Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, 0, rfl⟩), ?_⟩
      convert Ideal.zero_mem _
      rw [sub_eq_zero]
      apply Subtype.ext
      simp
    · refine ⟨0, tco_mem ℂ L (xv x) k, ?_⟩
      rw [map_zero, sub_zero]
      exact Ideal.subset_span ⟨k, rfl⟩
  | algebraMap c0 =>
    refine ⟨c0, memB _ (Subalgebra.algebraMap_mem _ c0), ?_⟩
    convert Ideal.zero_mem _
    rw [sub_eq_zero]
    apply Subtype.ext
    simp [IsScalarTower.algebraMap_apply ℂ F L]
  | add f g _ _ ihf ihg =>
    obtain ⟨c, hb, h⟩ := ihf
    obtain ⟨c', hb', h'⟩ := ihg
    refine ⟨c + c', by rw [map_add (f := _)]; exact Subalgebra.add_mem _ hb hb', ?_⟩
    convert Ideal.add_mem _ h h' using 1
    apply Subtype.ext
    simp only [map_add (f := _), Subalgebra.coe_sub, Subalgebra.coe_add, Subalgebra.coe_algebraMap]
    ring
  | mul f g _ _ ihf ihg =>
    obtain ⟨c, hb, h⟩ := ihf
    obtain ⟨c', hb', h'⟩ := ihg
    refine ⟨c * c', by rw [map_mul]; exact Subalgebra.mul_mem _ hb hb', ?_⟩
    convert Ideal.add_mem _ (Ideal.mul_mem_right (⟨_, hb'⟩ : rB ℂ L (xv x) {0}) _ h)
      (Ideal.mul_mem_left _ (algebraMap ℂ (rB ℂ L (xv x) {0}) c) h') using 1
    apply Subtype.ext
    simp only [map_mul, Subalgebra.coe_sub, Subalgebra.coe_add, Subalgebra.coe_mul,
      Subalgebra.coe_algebraMap]
    ring

private lemma fin_quot {F L : Type} [Field F] [Field L] [Algebra ℂ F] [Algebra ℂ L] [Algebra F L]
    [IsScalarTower ℂ F L] (d : ℕ) (x : Fin (d + 1) → Fˣ) (hc : IsFinCover ℂ L (xv x)) :
    Module.Finite ℂ ((rB ℂ L (xv x) {0}) ⧸ (Ideal.span (Set.range fun j : Fin d =>
      (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0})))) := by
  classical
  have hfin := (GlobalTheory.T.finite_cover_chart_smooth_normal ℂ F L d (xv x) hc {0} (Finset.singleton_nonempty 0)).1
  obtain ⟨s, hs⟩ := hfin.fg_top
  refine ⟨⟨s.image (fun z => Ideal.Quotient.mk _ (⟨z.1, z.2⟩ : rB ℂ L (xv x) {0})), ?_⟩⟩
  rw [eq_top_iff]
  rintro q -
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hy : (⟨y.1, y.2⟩ : integralClosure (rA ℂ (xv x) {0}) L) ∈
      Submodule.span (rA ℂ (xv x) {0}) (s : Set (integralClosure (rA ℂ (xv x) {0}) L)) := by
    rw [hs]
    trivial
  change Ideal.Quotient.mk _ (⟨(⟨y.1, y.2⟩ : integralClosure (rA ℂ (xv x) {0}) L).1,
    (⟨y.1, y.2⟩ : integralClosure (rA ℂ (xv x) {0}) L).2⟩ : rB ℂ L (xv x) {0}) ∈ _
  generalize (⟨y.1, y.2⟩ : integralClosure (rA ℂ (xv x) {0}) L) = z at hy ⊢
  induction hy using Submodule.span_induction with
  | mem w hw => exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hw))
  | zero =>
    convert Submodule.zero_mem _ using 1
    exact map_zero (Ideal.Quotient.mk _)
  | add u w _ _ hu hw =>
    convert Submodule.add_mem _ hu hw using 1
    exact map_add (Ideal.Quotient.mk _) _ _
  | smul r u _ hu =>
    obtain ⟨c, hb, hc'⟩ := exists_const_sub_mem_span_tco_of_mem_rA (L := L) d x r.1 r.2
    set_option synthInstance.maxHeartbeats 200000 in
    have e : (⟨((r • u : integralClosure (rA ℂ (xv x) {0}) L) : L), (r • u).2⟩ : rB ℂ L (xv x) {0}) =
        ⟨_, hb⟩ * ⟨u.1, u.2⟩ := by
      apply Subtype.ext
      simp [Algebra.smul_def]
      exact Or.inl rfl
    rw [e, map_mul, Ideal.Quotient.eq.mpr hc', Ideal.Quotient.mk_algebraMap, ← Algebra.smul_def]
    exact Submodule.smul_mem _ c hu

theorem UpperTheory.Gal.productCup_of_system.locMax_of :
    ValBasic → LocMax := by
  intro _ F L _ _ _ _ _ _ d x hc hred e v hv
  obtain ⟨b, hb, hbv, heb, hev⟩ := hv
  rw [mul_zero] at hev
  haveI : Module.Finite ℂ ((rB ℂ L (xv x) {0}) ⧸ (Ideal.span (Set.range fun j : Fin d =>
      (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0})))) := fin_quot d x hc
  haveI : IsArtinianRing ((rB ℂ L (xv x) {0}) ⧸ (Ideal.span (Set.range fun j : Fin d =>
      (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0})))) := IsArtinianRing.of_finite ℂ _
  haveI : IsReduced ((rB ℂ L (xv x) {0}) ⧸ (Ideal.span (Set.range fun j : Fin d =>
      (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0})))) := hred
  obtain ⟨zq, hz⟩ := red_art (Ideal.Quotient.mk (Ideal.span (Set.range fun j : Fin d =>
      (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0}))) ⟨b * v, hbv⟩)
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective zq
  have hmem : (⟨b * v, hbv⟩ : rB ℂ L (xv x) {0}) * (1 - ⟨b * v, hbv⟩ * z) ∈
      Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0})) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_sub, map_one, map_mul]
    exact hz
  obtain ⟨c, hcsum⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  have he1 : e.1 (1 - ⟨b * v, hbv⟩ * z) = 1 := by
    rw [map_sub, map_one, map_mul]
    change 1 - e.1 ⟨b * v, hbv⟩ * e.1 z = 1
    rw [hev, zero_mul, sub_zero]
  have hes : e.1 (⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z)) ≠ 0 := by
    rw [map_mul, he1, mul_one]
    exact heb
  have hs0 : ((⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) : L) ≠ 0 := by
    intro h
    apply hes
    rw [show (⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) = 0 from Subtype.ext h, map_zero]
  have key : ((⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) : L) * v =
      ∑ l, (c l : L) * tt L x l := by
    have h1 : (((⟨b * v, hbv⟩ : rB ℂ L (xv x) {0}) * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) : L) =
        ∑ l, (c l : L) * tt L x l := by
      rw [← hcsum]
      simp [tt]
    rw [← h1]
    simp only [Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_one]
    ring
  refine ⟨fun l => (c l : L) * ((⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) : L)⁻¹,
    fun l => ⟨⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z), hes, ?_⟩, ?_⟩
  · rw [mul_comm, mul_assoc, inv_mul_cancel₀ hs0, mul_one]
    exact (c l).2
  · calc v = ((⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) : L)⁻¹ *
          (((⟨b, hb⟩ * (1 - ⟨b * v, hbv⟩ * z) : rB ℂ L (xv x) {0}) : L) * v) := by
          rw [← mul_assoc, inv_mul_cancel₀ hs0, one_mul]
      _ = _ := by
          rw [key, Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ => by ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.IntegralClosureFiniteGenerated
set_option autoImplicit false

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system


open scoped IntermediateField.algebraAdjoinAdjoin in
private theorem tb_F {F : Type} [Field F] [Algebra ℂ F] {d : ℕ} {x : Fin (d + 1) → F} (pd : IsPd ℂ x) :
    IsTranscendenceBasis ℂ (fun j : Fin d => x j.succ / x 0) := by
  refine pd.indep.isTranscendenceBasis_iff_isAlgebraic.mpr ⟨fun a => ?_⟩
  refine (IsFractionRing.isAlgebraic_iff (Algebra.adjoin ℂ (Set.range fun j : Fin d => x j.succ / x 0))
    (IntermediateField.adjoin ℂ (Set.range fun j : Fin d => x j.succ / x 0)) F).mpr ?_
  have ha : a ∈ IntermediateField.adjoin ℂ (Set.range fun j : Fin d => x j.succ / x 0) := by
    rw [pd.gen]; trivial
  exact isAlgebraic_algebraMap (⟨a, ha⟩ : IntermediateField.adjoin ℂ (Set.range fun j : Fin d => x j.succ / x 0))

private theorem algHom_finite_of_proper {F K L : Type} [Field F] [Field K] [Field L] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ L]
    [Algebra F K] [IsScalarTower ℂ F K] [Algebra F L] [IsScalarTower ℂ F L] {d : ℕ} {x : Fin (d + 1) → F}
    (pd : IsPd ℂ x) [FiniteDimensional F K] [FiniteDimensional F L] (j2 : K →ₐ[ℂ] L) :
    j2.toRingHom.Finite := by
  have hF := tb_F pd
  set t : Fin d → F := fun j => x j.succ / x 0 with ht
  have hL : IsTranscendenceBasis ℂ (algebraMap F L ∘ t) := hF.algebraMap_comp
  have hK : IsTranscendenceBasis ℂ (algebraMap F K ∘ t) := hF.algebraMap_comp
  letI : Algebra K L := j2.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ K L := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  have hw : AlgebraicIndependent ℂ (algebraMap K L ∘ (algebraMap F K ∘ t)) :=
    hK.1.map' (f := IsScalarTower.toAlgHom ℂ K L) (algebraMap K L).injective
  have hwb : IsTranscendenceBasis ℂ (algebraMap K L ∘ (algebraMap F K ∘ t)) :=
    hw.isTranscendenceBasis_of_trdeg_le_of_finite (by rw [← hL.cardinalMk_eq_trdeg])
  have halg : Algebra.IsAlgebraic K L := hwb.isAlgebraic_iff.2 fun i => isAlgebraic_algebraMap _
  obtain ⟨s, hs⟩ := (Module.finite_def (R := F) (M := L)).1 inferInstance
  let S : Set L := (s : Set L) ∪ Set.range (algebraMap F L ∘ t)
  have hSfin : S.Finite := s.finite_toSet.union (Set.finite_range _)
  haveI : Finite S := hSfin
  have htop : IntermediateField.adjoin K S = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    let P : IntermediateField ℂ L := (IntermediateField.adjoin K S).restrictScalars ℂ
    have hP : ∀ f : F, algebraMap F L f ∈ P := by
      have hle : IntermediateField.adjoin ℂ (Set.range t) ≤ P.comap (IsScalarTower.toAlgHom ℂ F L) := by
        rw [IntermediateField.adjoin_le_iff]
        rintro _ ⟨j, rfl⟩
        exact IntermediateField.subset_adjoin K S (Or.inr ⟨j, rfl⟩)
      rw [pd.gen] at hle
      exact fun f => hle (IntermediateField.mem_top)
    have hy : y ∈ Submodule.span F (s : Set L) := by rw [hs]; trivial
    induction hy using Submodule.span_induction with
    | mem z hz => exact IntermediateField.subset_adjoin K S (Or.inl hz)
    | zero => exact zero_mem _
    | add a c _ _ ha hc => exact add_mem ha hc
    | smul r a _ ha =>
      rw [Algebra.smul_def]
      exact mul_mem (hP r) ha
  haveI : FiniteDimensional K (IntermediateField.adjoin K S) :=
    IntermediateField.finiteDimensional_adjoin fun z _ => (halg.isAlgebraic z).isIntegral
  rw [htop] at this
  change Module.Finite K L
  exact (IntermediateField.topEquiv (F := K) (E := L)).toLinearEquiv.finiteDimensional

private theorem fg_rB {F L : Type} [Field F] [Field L] [Algebra ℂ F] [Algebra ℂ L] [Algebra F L]
    [IsScalarTower ℂ F L] {d : ℕ} {x : Fin (d + 1) → F} (pd : IsPd ℂ x) [FiniteDimensional F L]
    (J : Finset (Fin (d + 1))) : (rB ℂ L x J).FG := by
  rcases J.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · have hbot : rB ℂ L x ∅ = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      haveI : Algebra.IsIntegral ℂ (rA ℂ x ∅) := Algebra.IsIntegral.adjoin (by simp)
      have h : IsIntegral ℂ y := isIntegral_trans (A := rA ℂ x ∅) y hy
      have := minpoly.mem_range_of_degree_eq_one ℂ y
        (IsAlgClosed.degree_eq_one_of_irreducible ℂ (minpoly.irreducible h))
      exact Algebra.mem_bot.2 this
    rw [hbot]
    exact Subalgebra.fg_bot
  · haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap ℂ F).injective
    haveI : IsFractionRing (rA ℂ x J) F := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing ℂ F d x pd J ⟨i, hi⟩).1
    haveI : IsNoetherianRing (rA ℂ x J) := (GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing ℂ F d x pd J ⟨i, hi⟩).2
    haveI := rA_isIntegrallyClosed pd hi
    set_option synthInstance.maxHeartbeats 200000 in
      haveI : Module.Finite (rA ℂ x J) (integralClosure (rA ℂ x J) L) :=
        IsIntegralClosure.finite (rA ℂ x J) F L (integralClosure (rA ℂ x J) L)
    have hfg : (rA ℂ x J).FG := by
      refine Subalgebra.fg_def.2 ⟨_, ?_, rfl⟩
      refine ((J.finite_toSet.prod (Set.finite_univ (α := Fin (d + 1)))).image
        fun p => x p.2 / x p.1).subset ?_
      rintro _ ⟨i', hi', j, rfl⟩
      exact ⟨(i', j), ⟨hi', trivial⟩, rfl⟩
    haveI : Algebra.FiniteType ℂ (rA ℂ x J) := (Subalgebra.fg_iff_finiteType _).1 hfg
    set_option synthInstance.maxHeartbeats 200000 in
      have hft : Algebra.FiniteType ℂ (integralClosure (rA ℂ x J) L) :=
        Algebra.FiniteType.trans (S := rA ℂ x J) inferInstance inferInstance
    exact (Subalgebra.fg_iff_finiteType (rB ℂ L x J)).2 hft

private theorem integralClosure_finiteGenerated {F K L : Type} [Field F] [Field K] [Field L] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ L]
    [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ} {x : Fin (d + 1) → F} (pd : IsPd ℂ x) [FiniteDimensional F K]
    (j2 : K →ₐ[ℂ] L) (hf : j2.toRingHom.Finite) (J : Finset (Fin (d + 1))) : (R2 x j2 J).FG := by
  letI : Algebra K L := j2.toRingHom.toAlgebra
  letI : Algebra F L := ((algebraMap K L).comp (algebraMap F K)).toAlgebra
  haveI : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℂ K L := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  haveI : IsScalarTower ℂ F L := IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap ℂ L c = algebraMap K L (algebraMap F K (algebraMap ℂ F c))
    rw [← IsScalarTower.algebraMap_apply ℂ F K c]
    exact (j2.commutes c).symm
  haveI : Module.Finite K L := hf
  haveI : FiniteDimensional F L := Module.Finite.trans K L
  let A := rA ℂ x J
  let B := (rB ℂ K x J).map j2
  let φ : A →+* B :=
    { toFun := fun a => ⟨algebraMap K L (algebraMap F K a),
        Subalgebra.mem_map.2 ⟨algebraMap F K a, (integralClosure A K).algebraMap_mem a, rfl⟩⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  letI : Algebra A B := φ.toAlgebra
  haveI : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsIntegral A B := ⟨fun b => by
    obtain ⟨c, hc, hb⟩ := Subalgebra.mem_map.1 b.2
    have h1 : IsIntegral A (algebraMap K L c) := IsIntegral.algebraMap hc
    have h2 : algebraMap B L b = algebraMap K L c := hb.symm
    rw [← h2] at h1
    exact (isIntegral_algebraMap_iff ).1 h1⟩
  have e : R2 x j2 J = rB ℂ L x J := by
    ext y
    constructor
    · intro hy
      exact isIntegral_trans (A := B) y hy
    · intro hy
      exact IsIntegral.tower_top (A := B) hy
  rw [e]
  exact fg_rB pd J

theorem rYFT_of :
    RYFT := by
  intro F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 h I J hI
  have pd := h.covZ.pd
  haveI := h.covZ.fin
  haveI := h.covY.fin
  have h1 : (rB ℂ K' (xv x) I).FG := fg_rB h.covY.pd I
  have h2 : (R2 (xv x) j2 J).FG := integralClosure_finiteGenerated pd j2 (algHom_finite_of_proper pd j2) J
  exact (Subalgebra.fg_iff_finiteType _).1 (h1.sup h2)

end UpperTheory.Gal.productCup_of_system

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PDtPull
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem alt_expand {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] {d q : ℕ} (f : M [⋀^Fin q]→ₗ[R] N) (a : Fin q → Fin d → R) (v : Fin d → M) :
    f (fun i => ∑ l, a i l • v l) =
      ∑ S : {S : Finset (Fin d) // S.card = q},
        (Matrix.of fun i j => a i (S.1.orderEmbOfFin S.2 j)).det •
          f (fun j => v (S.1.orderEmbOfFin S.2 j)) := by
  classical
  have h1 : f (fun i => ∑ l, a i l • v l) =
      ∑ φ : Fin q → Fin d, (∏ i, a i (φ i)) • f (fun i => v (φ i)) := by
    have h := f.toMultilinearMap.map_sum (fun i l => a i l • v l)
    refine h.trans (Finset.sum_congr rfl fun φ _ => ?_)
    exact f.toMultilinearMap.map_smul_univ _ _
  let e : {S : Finset (Fin d) // S.card = q} → Fin q → Fin d := fun S j => S.1.orderEmbOfFin S.2 j
  have he : ∀ S, Function.Injective (e S) := fun S => (S.1.orderEmbOfFin S.2).injective
  have hr : ∀ S, Set.range (e S) = S.1 := fun S => Finset.range_orderEmbOfFin S.1 S.2
  let Φ : (Σ _ : {S : Finset (Fin d) // S.card = q}, Equiv.Perm (Fin q)) →
      {φ : Fin q → Fin d // Function.Injective φ} :=
    fun p => ⟨e p.1 ∘ p.2, (he p.1).comp p.2.injective⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · rintro ⟨S, σ⟩ ⟨S', σ'⟩ h
      have h' : e S ∘ σ = e S' ∘ σ' := congrArg Subtype.val h
      have hS : S = S' := by
        apply Subtype.ext
        apply Finset.coe_injective
        rw [← hr S, ← hr S', ← σ.surjective.range_comp (e S), ← σ'.surjective.range_comp (e S'), h']
      subst hS
      have : σ = σ' := by
        ext i
        exact congrArg _ (he S (congrFun h' i))
      rw [this]
    · rintro ⟨φ, hφ⟩
      have hc : (Finset.univ.image φ).card = q := by
        rw [Finset.card_image_of_injective _ hφ]; simp
      let S : {S : Finset (Fin d) // S.card = q} := ⟨_, hc⟩
      have hm : ∀ i, ∃ j, e S j = φ i := fun i => by
        have : φ i ∈ Set.range (e S) := by rw [hr]; simp [S]
        exact this
      choose s hs using hm
      have hsi : Function.Injective s := fun i i' h => hφ (by rw [← hs, ← hs, h])
      refine ⟨⟨S, Equiv.ofBijective s (Finite.injective_iff_bijective.1 hsi)⟩, ?_⟩
      apply Subtype.ext
      funext i
      exact hs i
  rw [h1, ← Fintype.sum_subtype_add_sum_subtype (fun φ : Fin q → Fin d => Function.Injective φ)]
  have h0 : ∑ φ : {φ : Fin q → Fin d // ¬ Function.Injective φ},
      (∏ i, a i (φ.1 i)) • f (fun i => v (φ.1 i)) = 0 := by
    refine Finset.sum_eq_zero fun φ _ => ?_
    have : ¬ Function.Injective (fun i => v (φ.1 i)) := fun h => φ.2 fun i i' hi => h (by simp [hi])
    rw [f.map_eq_zero_of_not_injective _ this, smul_zero]
  rw [h0, add_zero, ← hΦ.sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← Matrix.det_transpose, Matrix.det_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hp := f.map_perm (fun j => v (e S j)) σ
  have hp' : f (fun i => v (e S (σ i))) = Equiv.Perm.sign σ • f (fun j => v (e S j)) := hp
  change (∏ i, a i (e S (σ i))) • f (fun i => v (e S (σ i))) = _
  rw [hp']
  have hq : ∏ i, (Matrix.of fun i j => a i (S.1.orderEmbOfFin S.2 j)).transpose (σ i) i =
      ∏ i, a i (e S (σ i)) := by
    rfl
  rw [hq]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h, e]

private theorem mapDR_iM (K L : Type) [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] [Algebra K L]
    [IsScalarTower ℂ K L] (n : ℕ) (v : Fin n → K) :
    mapDR ℂ K L (ExteriorAlgebra.ιMulti K n fun a => D ℂ K (v a)) =
      ExteriorAlgebra.ιMulti L n fun a => D ℂ L (algebraMap K L (v a)) := by
  simp only [ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 2
  funext a
  simp [mapDR, map1, KaehlerDifferential.map_D]

private theorem pullback_kahler_iMulti {K L : Type} [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] (j2 : K →ₐ[ℂ] L)
    (n : ℕ) (v : Fin n → K) :
    pr2L j2 (ExteriorAlgebra.ιMulti K n fun a => D ℂ K (v a)) =
      ExteriorAlgebra.ιMulti L n fun a => D ℂ L (j2 (v a)) := by
  letI : Algebra K L := j2.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ K L := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  exact mapDR_iM K L n v

private theorem iM_cast {L : Type} [Field L] [Algebra ℂ L] {d : ℕ} (S : Finset (Fin d)) (q : ℕ)
    (h : S.card = q) (w : Fin d → Ω[L⁄ℂ]) :
    ExteriorAlgebra.ιMulti L q (fun j => w (S.orderEmbOfFin h j)) =
      ExteriorAlgebra.ιMulti L S.card (fun j => w (S.orderEmbOfFin rfl j)) := by
  subst h; rfl

theorem UpperTheory.Gal.productCup_of_system.dtPull_of :
    LocOne → ValBasic → DtPull := by
  intro hLO hVB F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 Fx A hY e he T
  refine ⟨?_, ?_⟩
  · refine (mapDR_iM K K' _ _).trans ?_
    unfold dtS
    congr 1
    funext a
    rw [tt, tt, IsScalarTower.algebraMap_apply F K K']
  · obtain ⟨hle, ⟨ev, hev⟩, hbv, -⟩ := hVB K' (rB ℂ K' (xv x) {0}) e.1
    have hLoc := hLO F K' d x hY.covY hY.red e
    have htB : ∀ l, tt K' x l ∈ rB ℂ K' (xv x) {0} := fun l => tco_mem ℂ K' (xv x) l
    have ht0 : ∀ l, ev ⟨tt K' x l, hle (htB l)⟩ = 0 := fun l => by
      obtain ⟨h, hh⟩ := (hev _ _).1 (hbv ⟨tt K' x l, htB l⟩)
      exact hh.trans (e.2 l)
    choose g hgv hgt using hY.tan e he
    have hg : ∀ m l, ∃ h : g m l ∈ loc (rB ℂ K' (xv x) {0}) e.1, ev ⟨g m l, h⟩ = A e m l :=
      fun m l => (hev _ _).1 (hgv m l)
    choose hgl hge using hg
    choose c hcl hcD using fun m l => hLoc (g m l) (hgl m l)
    let ah : Matrix (Fin d) (Fin d) (loc (rB ℂ K' (xv x) {0}) e.1) := fun m l =>
      ⟨g m l, hgl m l⟩ + ∑ l', ⟨tt K' x l', hle (htB l')⟩ * ⟨c m l' l, hcl m l' l⟩
    have hah : ∀ m l, (ah m l : K') = g m l + ∑ l', tt K' x l' * c m l' l := fun m l => by
      simp [ah]
    have hAh : ev.mapMatrix ah = A e := by
      ext m l
      change ev (⟨g m l, hgl m l⟩ + ∑ l', ⟨tt K' x l', hle (htB l')⟩ * ⟨c m l' l, hcl m l' l⟩) = A e m l
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_add (f := _), map_sum, hge]
      simp only [map_mul, ht0, zero_mul, Finset.sum_const_zero, add_zero]
    have hD : ∀ m, D ℂ K' (j2 (tt K x m)) = ∑ l, (ah m l : K') • D ℂ K' (tt K' x l) := by
      intro m
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hgt m, map_sum]
      simp_rw [hah, add_smul, Finset.sum_add_distrib, Derivation.leibniz, hcD, Finset.smul_sum,
        Finset.sum_smul, smul_smul]
      rw [Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_comm
    refine ⟨fun S => if hS : S.card = T.card then
      (((ah.submatrix (T.orderEmbOfFin rfl) (S.orderEmbOfFin hS)).det :
        loc (rB ℂ K' (xv x) {0}) e.1) : K') else 0, ?_, ?_⟩
    · have h1 : pr2L j2 (dtS K x T) = ExteriorAlgebra.ιMulti K' T.card (fun a =>
          ∑ l, (ah (T.orderEmbOfFin rfl a) l : K') • D ℂ K' (tt K' x l)) := by
        unfold dtS
        rw [pullback_kahler_iMulti]
        congr 1
        funext a
        exact hD _
      rw [h1, alt_expand (ExteriorAlgebra.ιMulti K' T.card)
        (fun a l => (ah (T.orderEmbOfFin rfl a) l : K')) (fun l => D ℂ K' (tt K' x l)),
        Finset.sum_subtype (Finset.univ.powersetCard T.card) (p := fun S => S.card = T.card)
          (by simp [Finset.mem_powersetCard])]
      refine Finset.sum_congr rfl fun S _ => ?_
      simp only [dif_pos S.2]
      rw [iM_cast S.1 T.card S.2 (fun l => D ℂ K' (tt K' x l))]
      unfold dtS
      congr 1
      exact ((loc (rB ℂ K' (xv x) {0}) e.1).val.map_det
        (ah.submatrix (T.orderEmbOfFin rfl) (S.1.orderEmbOfFin S.2))).symm
    · intro S hS
      simp only [dif_pos hS]
      refine (hev _ _).2 ⟨SetLike.coe_mem _, ?_⟩
      change ev (ah.submatrix (T.orderEmbOfFin rfl) (S.orderEmbOfFin hS)).det = _
      rw [AlgHom.map_det, ← hAh]
      rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PEdgeB
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma lft_mono' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {s t : Finset (ι ⊕ₗ κ)} (h : s ⊆ t) :
    lft s ⊆ lft t := by
  intro a ha
  simp only [lft, Finset.mem_toLeft, Finset.mem_map] at ha ⊢
  obtain ⟨u, hu, e⟩ := ha
  exact ⟨u, h hu, e⟩

private lemma rgt_mono' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {s t : Finset (ι ⊕ₗ κ)} (h : s ⊆ t) :
    rgt s ⊆ rgt t := by
  intro a ha
  simp only [rgt, Finset.mem_toRight, Finset.mem_map] at ha ⊢
  obtain ⟨u, hu, e⟩ := ha
  exact ⟨u, h hu, e⟩

private lemma omB_mono' {L : Type} [Field L] [Algebra ℂ L] {B B' : Subalgebra ℂ L} (h : B ≤ B') (q : ℕ) :
    omB ℂ L B q ≤ omB ℂ L B' q := by
  refine Submodule.span_mono ?_
  rintro y ⟨b, hb, v, hv, rfl⟩
  exact ⟨b, h hb, v, fun j => h (hv j), rfl⟩

private lemma wd_empty' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] (w : ι → Module.End ℂ E)
    (c : Finset ι → E) : wd w c ∅ = 0 := by
  simp [wd]

private lemma acx_C' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] {A : Finset ι → Submodule ℂ E}
    {w : ι → Module.End ℂ E} {n : ℤ} {c : Finset ι → E} :
    c ∈ (acx A w).C n ↔ ∀ s, c s ∈ (if (s.card : ℤ) = n then A s else ⊥ : Submodule ℂ E) :=
  ⟨fun h s => h s trivial, fun h s _ => h s⟩

private lemma cech_C' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] {A : Finset ι → Submodule ℂ E}
    {n : ℤ} {c : Finset ι → E} :
    c ∈ (cech A).C n ↔ ∀ s, c s ∈ (if s.Nonempty ∧ (s.card : ℤ) = n + 1 then A s else ⊥ : Submodule ℂ E) :=
  ⟨fun h s => h s trivial, fun h s _ => h s⟩

theorem UpperTheory.Gal.productCup_of_system.edgeB_of :
    EdgeInj → RowEx → L1 → RYBasic → WdUni → WdBasic → EdgeB := by
  intro hEI hRow hL1 hRY hU hW
  intro F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 h0 y hy hB
  obtain ⟨hRI, hGood, hRmono, -, -⟩ := hRY F K K' d x j2 h0
  have lu : ∀ I J : Finset (Fin (d + 1)), lft (uni I J) = I := fun I J =>
    (hU _ _ (DR ℂ K') (fun _ => 1) (fun _ => 0) I J).2.1
  have ru : ∀ I J : Finset (Fin (d + 1)), rgt (uni I J) = J := fun I J =>
    (hU _ _ (DR ℂ K') (fun _ => 1) (fun _ => 0) I J).2.2.1
  have cu : ∀ I J : Finset (Fin (d + 1)), (uni I J).card = I.card + J.card := fun I J =>
    (hU _ _ (DR ℂ K') (fun _ => 1) (fun _ => 0) I J).2.2.2.1
  let G : Finset (Two d) → Submodule ℂ (DR ℂ K') := fun s => omB ℂ K' (RY (xv x) j2 (lft s) (rgt s)) d
  have hGm : ∀ I J, G (uni I J) = omB ℂ K' (RY (xv x) j2 I J) d := by
    intro I J
    simp only [G, lu, ru]
  have hG0 : ∀ I, G (uni I ∅) = omB ℂ K' (rB ℂ K' (xv x) I) d := by
    intro I
    rw [hGm, hRI]
  have hcech : (fun I => G (uni I ∅)) = fun I => omB ℂ K' (rB ℂ K' (xv x) I) d := funext hG0
  have hmix : (fun I J => G (uni I J)) = fun I J => omB ℂ K' (RY (xv x) j2 I J) d :=
    funext fun I => funext fun J => hGm I J
  obtain ⟨γ, hγ, hγ0, hγI⟩ := hEI (Fin (d + 1)) (DR ℂ K') G d y
    (by rw [hcech]; exact hy) (by rw [hmix]; exact hB)
  let A : Finset (Two d) → Submodule ℂ (DR ℂ K') := fun s => if (lft s).Nonempty then G s else ⊥
  have hAn : ∀ s, (lft s).Nonempty → A s = G s := fun s hs => if_pos hs
  have hAe : ∀ s, ¬ (lft s).Nonempty → A s = ⊥ := fun s hs => if_neg hs
  have hWOk : WOk A (fun _ => 1) := by
    refine ⟨fun _ _ => Commute.one_left _, ?_⟩
    intro s i _ m hm
    by_cases hs : (lft s).Nonempty
    · have hsub : s ⊆ insert i s := Finset.subset_insert _ _
      have hs' : (lft (insert i s)).Nonempty := hs.mono (lft_mono' hsub)
      rw [hAn _ hs] at hm
      show m ∈ A (insert i s)
      rw [hAn _ hs']
      exact omB_mono' (hRmono _ _ _ _ (lft_mono' hsub) (rgt_mono' hsub)) d hm
    · rw [hAe _ hs, Submodule.mem_bot] at hm
      show m ∈ A (insert i s)
      rw [hm]
      exact Submodule.zero_mem _
  have hKE : ∀ b, KE (colA A (fun _ => 1) b) ((d : ℤ) + 2) := by
    intro b m _
    by_cases hb : b.Nonempty
    · have e : (fun L => A (uni b L)) = fun J => omB ℂ K' (RY (xv x) j2 b J) d := by
        funext L
        rw [hAn _ (by rw [lu]; exact hb), hGm]
      show (acx (fun L => A (uni b L)) fun _ => 1).Z m ≤ (acx (fun L => A (uni b L)) fun _ => 1).B m
      rw [e]
      exact hRow F K K' d x j2 h0 d b hb m
    · intro c hc
      have hc0 : c = 0 := by
        funext L
        have h1 := acx_C'.1 hc.1 L
        have hA : A (uni b L) = ⊥ := hAe _ (by rw [lu]; exact hb)
        have h2 : c L ∈ (⊥ : Submodule ℂ (DR ℂ K')) := by
          simp only [hA, ite_self] at h1
          exact h1
        exact (Submodule.mem_bot ℂ).1 h2
      rw [hc0]
      exact Submodule.zero_mem _
  have hdelta : ∀ c : Finset (Two d) → DR ℂ K', wd (fun _ => (1 : Module.End ℂ (DR ℂ K'))) c = deltaL ℂ _ _ c :=
    (hW (Two d) (DR ℂ K') A (fun _ => 1)).2.2.2.2.1
  have hdelta' : ∀ c : Finset (Fin (d + 1)) → DR ℂ K', wd (fun _ => (1 : Module.End ℂ (DR ℂ K'))) c = deltaL ℂ _ _ c :=
    (hW (Fin (d + 1)) (DR ℂ K') (fun _ => ⊥) (fun _ => 1)).2.2.2.2.1
  have hγZ : γ ∈ (acx A fun _ => 1).Z ((d : ℤ) + 1) := by
    refine ⟨?_, ?_⟩
    · refine acx_C'.2 fun s => ?_
      have h1 := cech_C'.1 hγ.1 s
      by_cases hc : (s.card : ℤ) = (d : ℤ) + 1
      · rw [if_pos hc]
        by_cases hs : (lft s).Nonempty
        · rw [hAn _ hs]
          have hne : s.Nonempty := by
            rw [← Finset.card_pos]
            omega
          rw [if_pos ⟨hne, hc⟩] at h1
          exact h1
        · rw [hAe _ hs, Submodule.mem_bot]
          have hl : lft s = ∅ := Finset.not_nonempty_iff_eq_empty.1 hs
          have := hγ0 (rgt s)
          rwa [← hl, (hU _ _ (DR ℂ K') (fun _ => 1) (fun _ => 0) ∅ ∅).2.2.2.2 s] at this
      · rw [if_neg hc]
        rw [if_neg (fun h => hc h.2)] at h1
        exact h1
    · show wd _ γ = 0
      rw [hdelta]
      exact hγ.2
  have hBγ : γ ∈ (acx A fun _ => 1).B ((d : ℤ) + 1) := by
    refine hL1 (Fin (d + 1)) (Fin (d + 1)) (DR ℂ K') A (fun _ => 1) ((d : ℤ) + 2) ((d : ℤ) + 1) hWOk hKE γ hγZ ?_ ?_
    · intro b L hL
      exfalso
      have : L.card ≤ d + 1 := by simpa using Finset.card_le_univ L
      omega
    · intro b hb
      exfalso
      have : (0 : ℤ) ≤ b.card := by positivity
      omega
  obtain ⟨η, hη, he⟩ := hBγ
  refine Submodule.mem_map.2 ⟨fun b => η (uni b ∅), ?_, ?_⟩
  · refine cech_C'.2 fun b => ?_
    have h1 := acx_C'.1 hη (uni b ∅)
    rw [cu] at h1
    simp only [Finset.card_empty, add_zero] at h1
    by_cases hb : b.Nonempty ∧ (b.card : ℤ) = (d : ℤ) - 1 + 1
    · rw [if_pos hb]
      have hc : (b.card : ℤ) = (d : ℤ) + 1 - 1 := by omega
      rw [if_pos hc, hAn _ (by rw [lu]; exact hb.1), hG0] at h1
      exact h1
    · rw [if_neg hb]
      by_cases hc : (b.card : ℤ) = (d : ℤ) + 1 - 1
      · have hne : ¬ b.Nonempty := fun h => hb ⟨h, by omega⟩
        rw [if_pos hc, hAe _ (by rw [lu]; exact hne)] at h1
        exact h1
      · rw [if_neg hc] at h1
        exact h1
  · funext I
    have e1 := (hU _ _ (DR ℂ K') (fun _ => 1) η I ∅).1
    rw [wd_empty', smul_zero, add_zero] at e1
    have e2 : wd (fun _ => (1 : Module.End ℂ (DR ℂ K'))) η = γ := he
    rw [e2, hγI] at e1
    rw [e1]
    exact (congrFun (hdelta' _) I).symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ExistsPt
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

section IntegralMvPolynomialLemmas
variable {L V σ : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L)
  [AddCommGroup V] [Module L V] [Module ℂ V] [IsScalarTower ℂ L V]

variable [LinearOrder σ]

end IntegralMvPolynomialLemmas

end UpperTheory.Gal.productCup_of_system

private theorem lG_of_lemma {L : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L)
    [Algebra.FiniteType ℂ B] (I : Ideal B) (hI : I ≠ ⊤) :
    ∃ e : B →ₐ[ℂ] ℂ, ∀ b ∈ I, e b = 0 := by
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  letI := Ideal.Quotient.field M
  haveI : Module.Finite ℂ (B ⧸ M) := finite_of_finite_type_of_isJacobsonRing ℂ (B ⧸ M)
  haveI : Algebra.IsIntegral ℂ (B ⧸ M) := Algebra.IsIntegral.of_finite ℂ _
  have hbij : Function.Bijective (algebraMap ℂ (B ⧸ M)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let φ := AlgEquiv.ofBijective (Algebra.ofId ℂ (B ⧸ M)) hbij
  refine ⟨φ.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ M), fun b hb => ?_⟩
  have h0 : Ideal.Quotient.mk M b = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hIM hb)
  simp [h0]

private theorem lG_of_lemma_2 {L W : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L)
    [AddCommGroup W] [Module L W] [Module ℂ W] [IsScalarTower ℂ L W] (N : Submodule ℂ W)
    (hN : ∀ b : B, ∀ v ∈ N, (b : L) • v ∈ N) (e : B →ₐ[ℂ] ℂ) :
    ∃ S : Submodule ℂ W, (∀ x ∈ S, ∃ b : B, e b ≠ 0 ∧ (b : L) • x ∈ N) ∧
      ∀ x, (∃ b : B, e b ≠ 0 ∧ (b : L) • x ∈ N) → x ∈ S := by
  refine ⟨{ carrier := {x | ∃ b : B, e b ≠ 0 ∧ (b : L) • x ∈ N}
            add_mem' := ?_
            zero_mem' := ⟨1, by simp, by simp⟩
            smul_mem' := ?_ }, fun x hx => hx, fun x hx => hx⟩
  · rintro x y ⟨b1, h1, hx⟩ ⟨b2, h2, hy⟩
    refine ⟨b1 * b2, by simp [h1, h2], ?_⟩
    rw [smul_add]
    apply N.add_mem
    · rw [Subalgebra.coe_mul, mul_comm (b1 : L), mul_smul]
      exact hN b2 _ hx
    · rw [Subalgebra.coe_mul, mul_smul]
      exact hN b1 _ hy
  · rintro c x ⟨b, hb, hx⟩
    exact ⟨b, hb, by rw [smul_comm]; exact N.smul_mem c hx⟩

private theorem lG_of_lemma_3 {L W : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L)
    [Algebra.FiniteType ℂ B] [AddCommGroup W] [Module L W] [Module ℂ W] [IsScalarTower ℂ L W]
    (N : Submodule ℂ W) (hN : ∀ b : B, ∀ v ∈ N, (b : L) • v ∈ N) (x : W)
    (hx : ∀ e : B →ₐ[ℂ] ℂ, ∃ b : B, e b ≠ 0 ∧ (b : L) • x ∈ N) : x ∈ N := by
  let I : Ideal B :=
    { carrier := {b | (b : L) • x ∈ N}
      add_mem' := fun {a c} ha hc => by
        simp only [Set.mem_setOf_eq, Subalgebra.coe_add, add_smul] at *
        exact N.add_mem ha hc
      zero_mem' := by simp
      smul_mem' := fun c {b} hb => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, Subalgebra.coe_mul, mul_smul] at *
        exact hN c _ hb }
  by_cases hI : I = ⊤
  · have h1 : (1 : B) ∈ I := by rw [hI]; exact Submodule.mem_top
    change ((1 : B) : L) • x ∈ N at h1
    simpa using h1
  · obtain ⟨e, he⟩ := lG_of_lemma B I hI
    obtain ⟨b, hb, hbx⟩ := hx e
    exact absurd (he b hbx) hb

theorem UpperTheory.Gal.productCup_of_system.lG_of :
    LG := by
  intro L _ _ B _ V σ _ _ _ _ _ _ A w hA
  have hAs : ∀ s, ∀ b : B, ∀ v ∈ A s, (b : L) • v ∈ A s := fun s b v hv => by
    simpa using hA s (b : L) b.2 v hv
  have hloc : ∀ (e : B →ₐ[ℂ] ℂ) (N : Submodule ℂ V), (∀ b : B, ∀ v ∈ N, (b : L) • v ∈ N) →
      ∀ v ∈ locM B e N, ∃ b : B, e b ≠ 0 ∧ (b : L) • v ∈ N := by
    intro e N hN v hv
    obtain ⟨S, hS1, hS2⟩ := lG_of_lemma_2 B N hN e
    have hle : locM B e N ≤ S := by
      unfold locM
      rw [Submodule.span_le]
      intro u hu
      exact hS2 u hu
    exact hS1 v (hle hv)
  constructor
  · intro n c hc
    have hwd : ∀ (b : L) (x : Finset σ → V),
        wd (fun i => Algebra.lsmul ℂ ℂ V (w i)) (b • x) =
          b • wd (fun i => Algebra.lsmul ℂ ℂ V (w i)) x := by
      intro b x
      funext t
      simp [wd, Finset.smul_sum, smul_comm b]
    have hC : ∀ (A' : Finset σ → Submodule ℂ V) (x : Finset σ → V),
        x ∈ (acx A' fun i => Algebra.lsmul ℂ ℂ V (w i)).C (n - 1) ↔
          ∀ s, x s ∈ (if (s.card : ℤ) = n - 1 then A' s else ⊥) := by
      intro A' x
      simp [acx, Submodule.mem_pi]
    have hB : ∀ (A' : Finset σ → Submodule ℂ V) (c : Finset σ → V),
        c ∈ (acx A' fun i => Algebra.lsmul ℂ ℂ V (w i)).B n ↔
          ∃ x ∈ (acx A' fun i => Algebra.lsmul ℂ ℂ V (w i)).C (n - 1),
            wd (fun i => Algebra.lsmul ℂ ℂ V (w i)) x = c := by
      intro A' c
      simp [Cx.B, acx]
    have hCstab : ∀ b : B, ∀ x ∈ (acx A fun i => Algebra.lsmul ℂ ℂ V (w i)).C (n - 1),
        (b : L) • x ∈ (acx A fun i => Algebra.lsmul ℂ ℂ V (w i)).C (n - 1) := by
      intro b x hx
      rw [hC] at hx ⊢
      intro s
      have hxs := hx s
      simp only [Pi.smul_apply]
      split_ifs at hxs ⊢ with h
      · exact hAs s b _ hxs
      · rw [Submodule.mem_bot] at hxs ⊢
        simp [hxs]
    have hNstab : ∀ b : B, ∀ c ∈ (acx A fun i => Algebra.lsmul ℂ ℂ V (w i)).B n,
        (b : L) • c ∈ (acx A fun i => Algebra.lsmul ℂ ℂ V (w i)).B n := by
      intro b c hc
      rw [hB] at hc ⊢
      obtain ⟨x, hx, rfl⟩ := hc
      exact ⟨_, hCstab b x hx, hwd _ _⟩
    refine lG_of_lemma_3 B _ hNstab c fun e => ?_
    obtain ⟨x, hx, rfl⟩ := (hB _ _).1 (hc e)
    obtain ⟨S, hS1, hS2⟩ := lG_of_lemma_2 B _ hCstab e
    have hxS : x ∈ S := by
      rw [← Finset.univ_sum_single x]
      refine S.sum_mem fun s _ => ?_
      have hxs := (hC _ x).1 hx s
      split_ifs at hxs with h
      · obtain ⟨b, hb, hbv⟩ := hloc e (A s) (hAs s) _ hxs
        apply hS2
        refine ⟨b, hb, ?_⟩
        rw [hC]
        intro t
        by_cases hts : t = s
        · subst hts
          simpa [h] using hbv
        · simp [hts]
      · rw [Submodule.mem_bot] at hxs
        rw [hxs, Pi.single_zero]
        exact S.zero_mem
    obtain ⟨b, hb, hbx⟩ := hS1 x hxS
    exact ⟨b, hb, (hB _ _).2 ⟨_, hbx, hwd _ _⟩⟩
  · intro m hm
    have hmem : ∀ r ∈ Set.range w, ∀ u ∈ A ∅,
        r • u ∈ sm (Algebra.lsmul ℂ ℂ V) (A ∅) (Set.range w) := by
      intro r hr u hu
      unfold sm
      exact (le_iSup₂ (f := fun r (_ : r ∈ Set.range w) =>
        Submodule.map (Algebra.lsmul ℂ ℂ V r) (A ∅)) r hr) (Submodule.mem_map_of_mem hu)
    have hstab : ∀ b : B, ∀ v ∈ sm (Algebra.lsmul ℂ ℂ V) (A ∅) (Set.range w),
        (b : L) • v ∈ sm (Algebra.lsmul ℂ ℂ V) (A ∅) (Set.range w) := by
      intro b v hv
      have hle : sm (Algebra.lsmul ℂ ℂ V) (A ∅) (Set.range w) ≤
          (sm (Algebra.lsmul ℂ ℂ V) (A ∅) (Set.range w)).comap (Algebra.lsmul ℂ ℂ V (b : L)) := by
        conv_lhs => unfold sm
        refine iSup₂_le fun r hr => ?_
        rintro _ ⟨u, hu, rfl⟩
        rw [Submodule.mem_comap]
        simp only [Algebra.lsmul_coe]
        rw [smul_comm]
        exact hmem r hr _ (hAs ∅ b u hu)
      simpa using hle hv
    refine lG_of_lemma_3 B _ hstab m fun e => ?_
    obtain ⟨S, hS1, hS2⟩ := lG_of_lemma_2 B _ hstab e
    apply hS1
    have hle : sm (Algebra.lsmul ℂ ℂ V) (locM B e (A ∅)) (Set.range w) ≤ S := by
      conv_lhs => unfold sm
      refine iSup₂_le fun r hr => ?_
      rintro _ ⟨v, hv, rfl⟩
      obtain ⟨b, hb, hbv⟩ := hloc e (A ∅) (hAs ∅) v hv
      apply hS2
      refine ⟨b, hb, ?_⟩
      simp only [Algebra.lsmul_coe]
      rw [smul_comm]
      exact hmem r hr _ hbv
    exact hle (hm e)
end
