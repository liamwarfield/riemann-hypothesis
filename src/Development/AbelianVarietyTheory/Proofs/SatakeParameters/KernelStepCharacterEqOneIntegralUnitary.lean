module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralHilbert90FiniteIdelesTrivialWhereTrivial

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceComponentEqOneIffComponentsOverEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceComponentEqOneIffComponentsOverEqOne
open NumberField IsDedekindDomain Formalism.L2.DIV
open scoped TensorProduct

namespace GlobalTheory.AfIsoPrV

theorem prV_eq_one_iff_afIso : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (z : AfE F E), Formalism.UG.prV (E := E) v z = 1 ↔ ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v → GlobalTheory.Mem.Col2.afIso F E z P = 1 := by
  intro F E _ _ _ _ _ v z
  obtain ⟨ι, hι⟩ := GlobalTheory.AdeleBaseChange.exists_toAd F E
  let ι' : AfE F E ≃+* FiniteAdeleRing (𝓞 E) E :=
    RingEquiv.ofBijective ι ⟨GlobalTheory.AdeleBaseChange.map_injective hι, GlobalTheory.AdeleBaseChange.map_surjective hι⟩
  have hiso : GlobalTheory.TwU.IsAdIso ι' :=
    ⟨GlobalTheory.AdeleBaseChange.map_tmul_one hι,
      fun y => ⟨fun hy => GlobalTheory.AdeleBaseChange.map_mem_int hι hy,
        fun hy => GlobalTheory.AdeleBaseChange.mem_int_of_map hι hy⟩⟩
  have he : ι z = GlobalTheory.Mem.Col2.afIso F E z := GlobalTheory.isAdIso_eq_afIso F E ι' hiso z
  rw [GlobalTheory.AdeleBaseChange.prV_eq_one_iff hι, he]

end GlobalTheory.AfIsoPrV
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceComponentEqOneIffComponentsOverEqOneStatement
open NumberField IsDedekindDomain Formalism.L2.DIV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeComponent_eq_one_iff_components_over_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (z : AfE F E), Formalism.UG.prV (E := E) v z = 1 ↔ ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v → GlobalTheory.Mem.Col2.afIso F E z P = 1 := by
  first | exact @GlobalTheory.AfIsoPrV.prV_eq_one_iff_afIso | exact GlobalTheory.AfIsoPrV.prV_eq_one_iff_afIso | (intros; apply GlobalTheory.AfIsoPrV.prV_eq_one_iff_afIso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnPrimeToBasePrimePreservesCommonPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnPrimeToBasePrimePreservesCommonPlace
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TwU

namespace GlobalTheory.TwU

theorem seamP_under_eq : ∀ (D : D7) (X : Fields) (s : Seam D X), s.Ok → X.Ok → ∀ P Q : HeightOneSpectrum (𝓞 X.E), P.under (𝓞 X.F) = Q.under (𝓞 X.F) → (seamP s P).under (𝓞 D.host.F) = (seamP s Q).under (𝓞 D.host.F) := by
  intro D X s hs hX P Q h
  have key : ∀ a : 𝓞 D.host.F, ∃ r : 𝓞 X.F,
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a = RingOfIntegers.mapRingEquiv s.iE (algebraMap (𝓞 X.F) (𝓞 X.E) r) := by
    intro a
    set b := (RingOfIntegers.mapRingEquiv s.iE).symm (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) with hb
    have hbe : RingOfIntegers.mapRingEquiv s.iE b = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a := by
      rw [hb, RingEquiv.apply_symm_apply]
    have hfix : X.conjO b = b := by
      apply RingOfIntegers.ext
      apply s.iE.injective
      have h1 : s.iE (b : X.E) = ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) :=
        congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) hbe
      have h2 : ((X.conjO b : 𝓞 X.E) : X.E) = star (b : X.E) := rfl
      rw [h2, hs.2, h1]
      have h3 : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) =
          algebraMap D.host.F D.host.E (a : D.host.F) := rfl
      rw [h3, ← Formalism.BasicNotions.Examples₂.star_eq_conj]
      exact (D.sp.cm.fixed _).2 ⟨_, rfl⟩
    obtain ⟨r, hr⟩ := GlobalTheory.TwistPlaces.exists_of_conj_eq hX hfix
    exact ⟨r, by rw [hr, hbe]⟩
  apply HeightOneSpectrum.ext
  rw [HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal]
  ext a
  obtain ⟨r, hr⟩ := key a
  have hPQ : r ∈ Ideal.under (𝓞 X.F) P.asIdeal ↔ r ∈ Ideal.under (𝓞 X.F) Q.asIdeal := by
    rw [← HeightOneSpectrum.under_asIdeal, ← HeightOneSpectrum.under_asIdeal, h]
  simp only [Ideal.under, Ideal.mem_comap] at hPQ ⊢
  rw [hr, mem_seamP, mem_seamP]
  exact hPQ

end GlobalTheory.TwU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnPrimeToBasePrimePreservesCommonPlaceStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TwU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnPrimeToBasePrime_preserves_common_place : ∀ (D : D7) (X : Fields) (s : Seam D X), s.Ok → X.Ok → ∀ P Q : HeightOneSpectrum (𝓞 X.E), P.under (𝓞 X.F) = Q.under (𝓞 X.F) → (seamP s P).under (𝓞 D.host.F) = (seamP s Q).under (𝓞 D.host.F) := by
  first | exact @GlobalTheory.TwU.seamP_under_eq | exact GlobalTheory.TwU.seamP_under_eq | (intros; apply GlobalTheory.TwU.seamP_under_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OpenCharacterEqOneOfIntegralUnitOneAtRamified
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OpenCharacterEqOneOfIntegralUnitOneAtRamified
open NumberField IsDedekindDomain Formalism.L2.DIV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.UnitCut

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


open Classical in
def cutA (z : FiniteAdeleRing (𝓞 E) E) (hz : ∀ P : HeightOneSpectrum (𝓞 E), Valued.v (z P) ≤ 1)
    (S : Set (HeightOneSpectrum (𝓞 E))) : FiniteAdeleRing (𝓞 E) E :=
  ⟨fun P => if P ∈ S then z P else 1, Filter.Eventually.of_forall fun P => by
    by_cases h : P ∈ S
    · simp only [h, if_true]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hz P)
    · simp only [h, if_false]
      exact one_mem _⟩

open Classical in
theorem cutA_apply (z : FiniteAdeleRing (𝓞 E) E) (hz : ∀ P : HeightOneSpectrum (𝓞 E), Valued.v (z P) ≤ 1)
    (S : Set (HeightOneSpectrum (𝓞 E))) (P : HeightOneSpectrum (𝓞 E)) :
    cutA z hz S P = if P ∈ S then z P else 1 := by
  rfl

open GlobalTheory.Mem.Col2 (afIso mem_rInt_iff mem_suppAt_iff)

section Cut

theorem apply_mul (a b : FiniteAdeleRing (𝓞 E) E) (P : HeightOneSpectrum (𝓞 E)) : (a * b) P = a P * b P := rfl

theorem apply_one (P : HeightOneSpectrum (𝓞 E)) : (1 : FiniteAdeleRing (𝓞 E) E) P = 1 := rfl

theorem int_val {x : (AfE F E)ˣ} (hx : x ∈ intU F E) (P : HeightOneSpectrum (𝓞 E)) :
    Valued.v (afIso F E (x : AfE F E) P) ≤ 1 :=
  (mem_rInt_iff F E _).1 hx.1 P

theorem int_inv {x : (AfE F E)ˣ} (hx : x ∈ intU F E) (P : HeightOneSpectrum (𝓞 E)) :
    Valued.v (afIso F E ((x⁻¹ : (AfE F E)ˣ) : AfE F E) P) ≤ 1 :=
  (mem_rInt_iff F E _).1 hx.2 P

theorem afIso_mul_inv (x : (AfE F E)ˣ) (P : HeightOneSpectrum (𝓞 E)) :
    afIso F E (x : AfE F E) P * afIso F E ((x⁻¹ : (AfE F E)ˣ) : AfE F E) P = 1 := by
  rw [← apply_mul, ← map_mul, Units.mul_inv, map_one, apply_one]

theorem eq_of_afIso {y y' : (AfE F E)ˣ} (h : ∀ P, afIso F E (y : AfE F E) P = afIso F E (y' : AfE F E) P) : y = y' :=
  Units.ext ((afIso F E).injective (FiniteAdeleRing.ext _ h))

def cutU (x : (AfE F E)ˣ) (hx : x ∈ intU F E) (S : Set (HeightOneSpectrum (𝓞 E))) : (AfE F E)ˣ where
  val := (afIso F E).symm (cutA (afIso F E (x : AfE F E)) (int_val hx) S)
  inv := (afIso F E).symm (cutA (afIso F E ((x⁻¹ : (AfE F E)ˣ) : AfE F E)) (int_inv hx) S)
  val_inv := by
    rw [← map_mul, (afIso F E).symm_apply_eq, map_one]
    refine FiniteAdeleRing.ext _ fun P => ?_
    rw [apply_mul, cutA_apply, cutA_apply, apply_one]
    split_ifs
    · exact afIso_mul_inv x P
    · exact one_mul 1
  inv_val := by
    rw [← map_mul, (afIso F E).symm_apply_eq, map_one]
    refine FiniteAdeleRing.ext _ fun P => ?_
    rw [apply_mul, cutA_apply, cutA_apply, apply_one]
    split_ifs
    · rw [mul_comm]; exact afIso_mul_inv x P
    · exact one_mul 1

open Classical in
theorem afIso_cutU (x : (AfE F E)ˣ) (hx : x ∈ intU F E) (S : Set (HeightOneSpectrum (𝓞 E)))
    (P : HeightOneSpectrum (𝓞 E)) :
    afIso F E (cutU x hx S : AfE F E) P = if P ∈ S then afIso F E (x : AfE F E) P else 1 := by
  show afIso F E ((afIso F E).symm _) P = _
  rw [RingEquiv.apply_symm_apply, cutA_apply]

theorem afIso_cutU_inv (x : (AfE F E)ˣ) (hx : x ∈ intU F E) (S : Set (HeightOneSpectrum (𝓞 E)))
    (P : HeightOneSpectrum (𝓞 E)) : Valued.v (afIso F E (((cutU x hx S)⁻¹ : (AfE F E)ˣ) : AfE F E) P) ≤ 1 := by
  show Valued.v (afIso F E ((afIso F E).symm _) P) ≤ 1
  rw [RingEquiv.apply_symm_apply, cutA_apply]
  split_ifs
  · exact int_inv hx P
  · rw [map_one]

theorem cutU_mem_intU (x : (AfE F E)ˣ) (hx : x ∈ intU F E) (S : Set (HeightOneSpectrum (𝓞 E))) :
    cutU x hx S ∈ intU F E := by
  refine ⟨(mem_rInt_iff F E _).2 fun P => ?_, (mem_rInt_iff F E _).2 fun P => afIso_cutU_inv x hx S P⟩
  show Valued.v (afIso F E (cutU x hx S : AfE F E) P) ≤ 1
  rw [afIso_cutU]
  split_ifs
  · exact int_val hx P
  · rw [map_one]

theorem cutU_union (x : (AfE F E)ˣ) (hx : x ∈ intU F E) {S S' : Set (HeightOneSpectrum (𝓞 E))} (hd : Disjoint S S') :
    cutU x hx (S ∪ S') = cutU x hx S * cutU x hx S' := by
  refine eq_of_afIso fun P => ?_
  rw [Units.val_mul, map_mul, apply_mul, afIso_cutU, afIso_cutU, afIso_cutU]
  by_cases h : P ∈ S
  · have h' : P ∉ S' := Set.disjoint_left.1 hd h
    simp [h, h']
  · by_cases h' : P ∈ S' <;> simp [h, h']

theorem cutU_univ (x : (AfE F E)ˣ) (hx : x ∈ intU F E) : cutU x hx Set.univ = x :=
  eq_of_afIso fun P => by rw [afIso_cutU]; simp

theorem cutU_empty (x : (AfE F E)ˣ) (hx : x ∈ intU F E) : cutU x hx ∅ = 1 :=
  eq_of_afIso fun P => by rw [afIso_cutU, Units.val_one, map_one, apply_one]; simp

theorem cutU_mem_inertAt (x : (AfE F E)ˣ) (hx : x ∈ intU F E) (v : HeightOneSpectrum (𝓞 F)) :
    cutU x hx {P | P.under (𝓞 F) = v} ∈ inertAt E v :=
  ⟨cutU_mem_intU x hx _, (mem_suppAt_iff F E v _).2 fun P hP => by
    rw [afIso_cutU]
    simp [hP]⟩

theorem natCast_notMem_of_under {P : HeightOneSpectrum (𝓞 E)} {N : ℕ} (h : (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal) :
    (N : 𝓞 E) ∉ P.asIdeal := fun h' => h (by
  show (N : 𝓞 F) ∈ P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
  rw [Ideal.mem_comap, map_natCast]
  exact h')

theorem cutU_mem_congN (x : (AfE F E)ˣ) (hx : x ∈ intU F E) {N : ℕ} (hN : 0 < N) :
    cutU x hx {P | (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal} ∈ congN F E N := by
  rw [GlobalTheory.Mem.ReadEx.mem_congN_iff]
  refine ⟨cutU_mem_intU x hx _, (afIso F E).symm (algebraMap E _ (N : E)⁻¹ *
    (afIso F E (cutU x hx {P | (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal} : AfE F E) - 1)), ?_, ?_⟩
  · rw [mem_rInt_iff, RingEquiv.apply_symm_apply]
    intro P
    show Valued.v ((algebraMap E (FiniteAdeleRing (𝓞 E) E) (N : E)⁻¹) P *
      (afIso F E (cutU x hx {P | (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal} : AfE F E) P - 1)) ≤ 1
    rw [afIso_cutU]
    by_cases h : (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal
    · have h3 : Valued.v ((algebraMap E (FiniteAdeleRing (𝓞 E) E) (N : E)⁻¹) P) = 1 := by
        change Valued.v (algebraMap E (P.adicCompletion E) (N : E)⁻¹) = 1
        rw [map_inv₀, map_inv₀, ← map_natCast (algebraMap (𝓞 E) E), GlobalTheory.TwistPlaces.valued_int,
          GlobalTheory.TwistPlaces.intValuation_eq_one P (natCast_notMem_of_under h), inv_one]
      have h4 : P ∈ {P : HeightOneSpectrum (𝓞 E) | (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal} := h
      rw [if_pos h4, map_mul, h3, one_mul]
      exact Valuation.map_sub_le _ (int_val hx P) (by rw [map_one])
    · have h4 : P ∉ {P : HeightOneSpectrum (𝓞 E) | (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal} := h
      rw [if_neg h4, sub_self, mul_zero, map_zero]
      exact zero_le'
  · apply (afIso F E).injective
    rw [map_mul, RingEquiv.apply_symm_apply, map_natCast, GlobalTheory.Mem.ReadEx.inv_mul_mul_nat hN, map_sub, map_one]

end Cut

theorem map_eq_one_of_one_at_ramified : ∀ (F E L : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Field L] (σ : L →+* ℂ) (ξ : Chr F E L), ξ ∈ openChr F E L → (ratId F E).range ≤ ξ.ker → ∀ x ∈ intU F E,
    (∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) ∈ Qprime ξ → GlobalTheory.Mem.Col2.afIso F E (x : AfE F E) P = 1) → ξ x = 1 := by
  intro F E L _ _ _ _ _ _ _ ξ hξ _ x hx h1
  classical
  obtain ⟨N, hN, hk⟩ := hξ
  have h0 : Ideal.span {(N : 𝓞 F)} ≠ ⊥ := by simpa using hN.ne'
  have hT : {v : HeightOneSpectrum (𝓞 F) | (N : 𝓞 F) ∈ v.asIdeal}.Finite :=
    (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 hv
  have key : ∀ T : Finset (HeightOneSpectrum (𝓞 F)), ξ (cutU x hx {P | P.under (𝓞 F) ∈ T}) = 1 := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      have e : {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) ∈ (∅ : Finset (HeightOneSpectrum (𝓞 F)))} = ∅ := by
        ext P
        simp
      rw [e, cutU_empty, map_one]
    | insert v T hv ih =>
      have e : {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) ∈ insert v T} =
          {P | P.under (𝓞 F) = v} ∪ {P | P.under (𝓞 F) ∈ T} := by
        ext P
        simp
      have hd : Disjoint {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) = v} {P | P.under (𝓞 F) ∈ T} :=
        Set.disjoint_left.2 fun P h h' => hv (by
          have h2 : P.under (𝓞 F) = v := h
          have h3 : P.under (𝓞 F) ∈ T := h'
          rw [← h2]
          exact h3)
      rw [e, cutU_union x hx hd, map_mul, ih, mul_one]
      by_cases hq : v ∈ Qprime ξ
      · have e1 : cutU x hx {P | P.under (𝓞 F) = v} = 1 := eq_of_afIso fun P => by
          rw [afIso_cutU, Units.val_one, map_one, apply_one]
          split_ifs with hP
          · have h2 : P.under (𝓞 F) = v := hP
            exact h1 P (by rw [h2]; exact hq)
          · rfl
        rw [e1, map_one]
      · have hle : inertAt E v ≤ ξ.ker := by
          by_contra h
          exact hq h
        exact MonoidHom.mem_ker.1 (hle (cutU_mem_inertAt x hx v))
  have hd : Disjoint {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) ∈ hT.toFinset}
      {P | (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal} :=
    Set.disjoint_left.2 fun P h h' => h' (by simpa using h)
  have eu : {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) ∈ hT.toFinset} ∪
      {P | (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal} = Set.univ := by
    ext P
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.Finite.mem_toFinset, Set.mem_univ, iff_true]
    exact em _
  have e : cutU x hx {P | P.under (𝓞 F) ∈ hT.toFinset} * cutU x hx {P | (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal} = x := by
    rw [← cutU_union x hx hd, eu, cutU_univ]
  have e2 := congrArg ξ e
  rw [map_mul, key, one_mul, MonoidHom.mem_ker.1 (hk (cutU_mem_congN x hx hN))] at e2
  exact e2.symm

end GlobalTheory.UnitCut
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OpenCharacterEqOneOfIntegralUnitOneAtRamifiedStatement
open NumberField IsDedekindDomain Formalism.L2.DIV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.openCharacter_eq_one_of_integralUnit_one_at_ramified : ∀ (F E L : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field L] (σ : L →+* ℂ) (ξ : Chr F E L), ξ ∈ openChr F E L → (ratId F E).range ≤ ξ.ker → ∀ x ∈ intU F E, (∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) ∈ Qprime ξ → GlobalTheory.Mem.Col2.afIso F E (x : AfE F E) P = 1) → ξ x = 1 := by
  first | exact @GlobalTheory.UnitCut.map_eq_one_of_one_at_ramified | exact GlobalTheory.UnitCut.map_eq_one_of_one_at_ramified | (intros; apply GlobalTheory.UnitCut.map_eq_one_of_one_at_ramified <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AfIsoEqZeroIff
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AfIsoEqZeroIff
open NumberField IsDedekindDomain Formalism.L2.DIV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.AfeLocTr

open HeightOneSpectrum

def IsIntAd {E : Type} [Field E] [NumberField E] (z : FiniteAdeleRing (𝓞 E) E) : Prop :=
  ∀ Q : HeightOneSpectrum (𝓞 E), Valued.v (z Q) ≤ 1

theorem eq_zero_of_le_exp {x : WithZero (Multiplicative ℤ)} (h : ∀ n : ℕ, x ≤ WithZero.exp (-(n : ℤ))) : x = 0 := by
  by_contra hx
  have e := WithZero.exp_log hx
  set n : ℕ := (-WithZero.log x + 1).toNat
  have h1 := h n
  rw [← e, WithZero.exp_le_exp] at h1
  have h2 := Int.self_le_toNat (-WithZero.log x + 1)
  omega

theorem exists_gen {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    ∃ h : ℕ, 0 < h ∧ ∃ α : 𝓞 E, Ideal.span {α} = P.asIdeal ^ h := by
  have hP : P.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 E)) := mem_nonZeroDivisors_of_ne_zero P.ne_bot
  set h := Fintype.card (ClassGroup (𝓞 E))
  have hPh : P.asIdeal ^ h ∈ nonZeroDivisors (Ideal (𝓞 E)) := pow_mem hP h
  have h1 : ClassGroup.mk0 ⟨P.asIdeal ^ h, hPh⟩ = 1 := by
    have e : (⟨P.asIdeal ^ h, hPh⟩ : nonZeroDivisors (Ideal (𝓞 E))) = ⟨P.asIdeal, hP⟩ ^ h := Subtype.ext (by simp)
    rw [e, map_pow, pow_card_eq_one]
  haveI := (ClassGroup.mk0_eq_one_iff hPh).1 h1
  exact ⟨h, Fintype.card_pos, _, Ideal.span_singleton_generator _⟩

theorem comp_eq_zero_iff {E : Type} [Field E] [NumberField E] (z : FiniteAdeleRing (𝓞 E) E) (hz : IsIntAd z)
    (P : HeightOneSpectrum (𝓞 E)) :
    z P = 0 ↔ ∀ n : ℕ, ∃ π : 𝓞 E, π ≠ 0 ∧ π ∈ P.asIdeal ^ n ∧
      IsIntAd (algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E π)⁻¹ * z) := by
  constructor
  · intro h0 n
    obtain ⟨h, hh, α, hα⟩ := exists_gen P
    have hα0 : α ≠ 0 := by
      rintro rfl
      rw [Ideal.span_singleton_eq_bot.2 rfl] at hα
      exact pow_ne_zero _ P.ne_bot hα.symm
    have hαP : α ∈ P.asIdeal := Ideal.pow_le_self hh.ne' (hα ▸ Ideal.mem_span_singleton_self α)
    refine ⟨α ^ n, pow_ne_zero _ hα0, Ideal.pow_mem_pow hαP n, fun Q => ?_⟩
    show Valued.v (((algebraMap (𝓞 E) E (α ^ n))⁻¹ : E) * z Q) ≤ 1
    by_cases hQ : Q = P
    · subst hQ
      rw [h0, mul_zero, map_zero]
      exact zero_le'
    · have hαQ : α ∉ Q.asIdeal := by
        intro hm
        have h2 : P.asIdeal ^ h ≤ Q.asIdeal := by rw [← hα, Ideal.span_singleton_le_iff_mem]; exact hm
        exact hQ (HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top (Q.isPrime.le_of_pow_le h2)).symm)
      have hv : Q.valuation E (algebraMap (𝓞 E) E (α ^ n)) = 1 :=
        (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) Q).2 fun hm => hαQ (Q.isPrime.mem_of_pow_mem n hm)
      rw [map_mul, valuedAdicCompletion_eq_valuation', map_inv₀, hv, inv_one, one_mul]
      exact hz Q
  · intro h
    refine (Valued.v.zero_iff).1 (eq_zero_of_le_exp fun n => ?_)
    obtain ⟨π, hπ0, hπn, hint⟩ := h n
    have h1 : Valued.v (((algebraMap (𝓞 E) E π)⁻¹ : E) * z P) ≤ 1 := hint P
    rw [map_mul, valuedAdicCompletion_eq_valuation', map_inv₀, valuation_of_algebraMap] at h1
    have hv0 : P.intValuation π ≠ 0 := P.intValuation_ne_zero π hπ0
    have h2 : Valued.v (z P) ≤ P.intValuation π := by
      calc Valued.v (z P) = P.intValuation π * ((P.intValuation π)⁻¹ * Valued.v (z P)) := by
            rw [← mul_assoc, mul_inv_cancel₀ hv0, one_mul]
        _ ≤ P.intValuation π * 1 := by gcongr
        _ = P.intValuation π := mul_one _
    exact h2.trans ((P.intValuation_le_pow_iff_mem π n).2 hπn)

end GlobalTheory.AfeLocTr

namespace GlobalTheory.AfeLocTr

open HeightOneSpectrum

theorem transport_zero {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] (s : E ≃+* E')
    (Φ : FiniteAdeleRing (𝓞 E) E ≃+* FiniteAdeleRing (𝓞 E') E')
    (hΦ : ∀ x : E, Φ (algebraMap E _ x) = algebraMap E' _ (s x)) (hI : ∀ z, IsIntAd (Φ z) ↔ IsIntAd z)
    (P : HeightOneSpectrum (𝓞 E)) (Q : HeightOneSpectrum (𝓞 E'))
    (hPQ : ∀ a ∈ P.asIdeal, RingOfIntegers.mapRingEquiv s a ∈ Q.asIdeal)
    (z : FiniteAdeleRing (𝓞 E) E) (hz : IsIntAd z) (h0 : z P = 0) : Φ z Q = 0 := by
  rw [comp_eq_zero_iff z hz] at h0
  rw [comp_eq_zero_iff (Φ z) ((hI z).2 hz)]
  intro n
  obtain ⟨π, hπ0, hπn, hint⟩ := h0 n
  set f := RingOfIntegers.mapRingEquiv s
  refine ⟨f π, (map_ne_zero_iff _ f.injective).2 hπ0, ?_, ?_⟩
  · have h1 : Ideal.map f P.asIdeal ≤ Q.asIdeal := Ideal.map_le_iff_le_comap.2 hPQ
    have h2 : f π ∈ Ideal.map f (P.asIdeal ^ n) := Ideal.mem_map_of_mem _ hπn
    rw [Ideal.map_pow] at h2
    exact Ideal.pow_right_mono h1 n h2
  · have e : algebraMap (𝓞 E') E' (f π) = s (algebraMap (𝓞 E) E π) := RingOfIntegers.mapRingEquiv_apply s π
    have e2 : algebraMap E' (FiniteAdeleRing (𝓞 E') E') (algebraMap (𝓞 E') E' (f π))⁻¹ * Φ z =
        Φ (algebraMap E (FiniteAdeleRing (𝓞 E) E) (algebraMap (𝓞 E) E π)⁻¹ * z) := by
      rw [map_mul, hΦ, map_inv₀ s, e]
    rw [e2]
    exact (hI _).2 hint

theorem afIso_eq_zero_iff : ∀ (F E F' E' : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field F'] [NumberField F'] [Field E'] [NumberField E'] [Algebra F' E'] (s : E ≃+* E') (φ : AfE F E ≃+* AfE F' E'), (∀ x : E, φ (x ⊗ₜ[F] 1) = s x ⊗ₜ[F'] 1) → (∀ y, φ y ∈ RInt F' E' ↔ y ∈ RInt F E) → ∀ y ∈ RInt F E, ∀ P : HeightOneSpectrum (𝓞 E), (GlobalTheory.Mem.Col2.afIso F' E' (φ y) (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s) P) = 0 ↔ GlobalTheory.Mem.Col2.afIso F E y P = 0) := by
  intro F E F' E' _ _ _ _ _ _ _ _ _ _ s φ hφ hR y hy P
  set ι := GlobalTheory.Mem.Col2.afIso F E
  set ι' := GlobalTheory.Mem.Col2.afIso F' E'
  set Φ : FiniteAdeleRing (𝓞 E) E ≃+* FiniteAdeleRing (𝓞 E') E' := ι.symm.trans (φ.trans ι')
  have hΦa : ∀ w, Φ w = ι' (φ (ι.symm w)) := fun _ => rfl
  have hΦ : ∀ x : E, Φ (algebraMap E _ x) = algebraMap E' _ (s x) := fun x => by
    rw [hΦa, ← GlobalTheory.Mem.Col2.afIso_tmul_one F E x, RingEquiv.symm_apply_apply, hφ, GlobalTheory.Mem.Col2.afIso_tmul_one]
  have hI : ∀ w, IsIntAd (Φ w) ↔ IsIntAd w := fun w => by
    unfold IsIntAd
    rw [hΦa, ← GlobalTheory.Mem.Col2.mem_rInt_iff, hR, GlobalTheory.Mem.Col2.mem_rInt_iff, RingEquiv.apply_symm_apply]
  have hΦy : Φ (ι y) = ι' (φ y) := by rw [hΦa, RingEquiv.symm_apply_apply]
  have hz : IsIntAd (ι y) := (GlobalTheory.Mem.Col2.mem_rInt_iff F E y).1 hy
  set Q := HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s) P
  have hQ : ∀ b : 𝓞 E', b ∈ Q.asIdeal ↔ (RingOfIntegers.mapRingEquiv s).symm b ∈ P.asIdeal := fun b => Iff.rfl
  rw [← hΦy]
  constructor
  · intro h0
    have hΦ' : ∀ x : E', Φ.symm (algebraMap E' _ x) = algebraMap E _ (s.symm x) := fun x => by
      rw [RingEquiv.symm_apply_eq, hΦ, RingEquiv.apply_symm_apply]
    have hI' : ∀ w, IsIntAd (Φ.symm w) ↔ IsIntAd w := fun w => by
      rw [← hI, RingEquiv.apply_symm_apply]
    have hQP : ∀ a ∈ Q.asIdeal, RingOfIntegers.mapRingEquiv s.symm a ∈ P.asIdeal := fun a ha => by
      have e : RingOfIntegers.mapRingEquiv s.symm a = (RingOfIntegers.mapRingEquiv s).symm a := rfl
      rw [e]
      exact (hQ a).1 ha
    have := transport_zero s.symm Φ.symm hΦ' hI' Q P hQP (Φ (ι y)) ((hI _).2 hz) h0
    rwa [RingEquiv.symm_apply_apply] at this
  · intro h0
    refine transport_zero s Φ hΦ hI P Q (fun a ha => ?_) (ι y) hz h0
    rw [hQ, RingEquiv.symm_apply_apply]
    exact ha

end GlobalTheory.AfeLocTr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AfIsoEqZeroIffStatement
open NumberField IsDedekindDomain Formalism.L2.DIV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.afIso_ringEquiv_eq_zero_iff : ∀ (F E F' E' : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field F'] [NumberField F'] [Field E'] [NumberField E'] [Algebra F' E'] (s : E ≃+* E') (φ : AfE F E ≃+* AfE F' E'), (∀ x : E, φ (x ⊗ₜ[F] 1) = s x ⊗ₜ[F'] 1) → (∀ y, φ y ∈ RInt F' E' ↔ y ∈ RInt F E) → ∀ y ∈ RInt F E, ∀ P : HeightOneSpectrum (𝓞 E), (GlobalTheory.Mem.Col2.afIso F' E' (φ y) (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s) P) = 0 ↔ GlobalTheory.Mem.Col2.afIso F E y P = 0) := by
  first | exact @GlobalTheory.AfeLocTr.afIso_eq_zero_iff | exact GlobalTheory.AfeLocTr.afIso_eq_zero_iff | (intros; apply GlobalTheory.AfeLocTr.afIso_eq_zero_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTypePrimeUnderEq
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTypePrimeUnderEq
open NumberField IsDedekindDomain Formalism.L2.Col

noncomputable section
namespace GlobalTheory.GprimUnder

theorem conjO_conjO (X : Fields) (a : 𝓞 X.E) : X.conjO (X.conjO a) = a := by
  apply RingOfIntegers.ext
  show star (star (a : X.E)) = (a : X.E)
  exact star_star _

theorem conjO_algebraMap (X : Fields) (hX : X.Ok) (x : 𝓞 X.F) :
    X.conjO (algebraMap (𝓞 X.F) (𝓞 X.E) x) = algebraMap (𝓞 X.F) (𝓞 X.E) x := by
  apply RingOfIntegers.ext
  show star ((algebraMap (𝓞 X.F) (𝓞 X.E) x : 𝓞 X.E) : X.E) = ((algebraMap (𝓞 X.F) (𝓞 X.E) x : 𝓞 X.E) : X.E)
  have : ((algebraMap (𝓞 X.F) (𝓞 X.E) x : 𝓞 X.E) : X.E) = algebraMap X.F X.E (x : X.F) := rfl
  rw [this]
  exact hX.star_F _

theorem mem_divs_iff {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} (ha : a ≠ 0) (P : HeightOneSpectrum A) :
    P ∈ divs a ↔ a ∈ P.asIdeal := by
  have hfin : {P : HeightOneSpectrum A | a ∈ P.asIdeal}.Finite := by
    have h0 : Ideal.span {a} ≠ ⊥ := by simpa using ha
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  unfold divs
  rw [dite_eq_left hfin, Set.Finite.mem_toFinset]
  rfl

def conjPrime (X : Fields) (P : HeightOneSpectrum (𝓞 X.E)) : HeightOneSpectrum (𝓞 X.E) where
  asIdeal := P.asIdeal.comap X.conjO
  isPrime := Ideal.comap_isPrime X.conjO P.asIdeal
  ne_bot := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    intro h
    have h1 : X.conjO x ∈ P.asIdeal.comap X.conjO := by
      rw [Ideal.mem_comap, conjO_conjO]
      exact hx
    rw [h, Ideal.mem_bot] at h1
    apply hx0
    rw [← conjO_conjO X x, h1, map_zero]

theorem mem_conjPrime (X : Fields) (P : HeightOneSpectrum (𝓞 X.E)) (a : 𝓞 X.E) :
    a ∈ (conjPrime X P).asIdeal ↔ X.conjO a ∈ P.asIdeal := Ideal.mem_comap

theorem under_conjPrime (X : Fields) (hX : X.Ok) (P : HeightOneSpectrum (𝓞 X.E)) :
    (conjPrime X P).under (𝓞 X.F) = P.under (𝓞 X.F) := by
  apply HeightOneSpectrum.ext
  ext x
  show algebraMap (𝓞 X.F) (𝓞 X.E) x ∈ (conjPrime X P).asIdeal ↔ algebraMap (𝓞 X.F) (𝓞 X.E) x ∈ P.asIdeal
  rw [mem_conjPrime, conjO_algebraMap X hX]

theorem exists_vG_under : ∀ (X : Fields) (Pr : Primes X), X.Ok → Pr.Ok → ∀ (i : Fin 2) (P : HeightOneSpectrum (𝓞 X.E)),
    ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal → ∃ P' ∈ Pr.vG i, P'.under (𝓞 X.F) = P.under (𝓞 X.F) := by
  intro X Pr hX hPr i P hP
  have hg0 : ((Pr.g i : ℕ) : 𝓞 X.E) ≠ 0 := Nat.cast_ne_zero.2 (hPr.g_prime i).ne_zero
  have hc0 : X.conjO (Pr.piG i) ≠ 0 := by
    intro h
    have h1 := hPr.piG_norm i
    rw [h, mul_zero] at h1
    exact hg0 h1.symm
  have hvG : ∀ v, v ∈ Pr.vG i ↔ X.conjO (Pr.piG i) ∈ v.asIdeal := fun v => mem_divs_iff hc0 v
  rw [← hPr.piG_norm i] at hP
  rcases P.isPrime.mem_or_mem hP with h | h
  · refine ⟨conjPrime X P, (hvG _).2 ?_, under_conjPrime X hX P⟩
    rw [mem_conjPrime, conjO_conjO]
    exact h
  · exact ⟨P, (hvG P).2 h, rfl⟩

end GlobalTheory.GprimUnder
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTypePrimeUnderEqStatement
open NumberField IsDedekindDomain Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_typePrime_under_eq : ∀ (X : Fields) (Pr : Primes X), X.Ok → Pr.Ok → ∀ (i : Fin 2) (P : HeightOneSpectrum (𝓞 X.E)), ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal → ∃ P' ∈ Pr.vG i, P'.under (𝓞 X.F) = P.under (𝓞 X.F) := by
  first | exact @GlobalTheory.GprimUnder.exists_vG_under | exact GlobalTheory.GprimUnder.exists_vG_under | (intros; apply GlobalTheory.GprimUnder.exists_vG_under <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmDataConjIsConjOf
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmDataConjIsConjOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV

namespace GlobalTheory

theorem cmData_sig_isConjOf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] (hc : CMData F E), IsConjOf hc.sig := by
  intro F E _ _ _ _ _ _ hc
  refine ⟨fun h0 => ?_, fun e => star_star e, fun e he => (hc.fixed e).1 he⟩
  have hs : Function.Surjective (algebraMap F E) := fun e => (hc.fixed e).1 (AlgHom.congr_fun h0 e)
  have h1 : Module.finrank F E = 1 :=
    (LinearEquiv.finrank_eq (LinearEquiv.ofBijective (Algebra.linearMap F E)
      ⟨(algebraMap F E).injective, hs⟩)).symm.trans (Module.finrank_self F)
  have := hc.deg2
  omega

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmDataConjIsConjOfStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmData_conj_isConjOf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E), IsConjOf hc.sig := by
  first | exact @GlobalTheory.cmData_sig_isConjOf | exact GlobalTheory.cmData_sig_isConjOf | (intros; apply GlobalTheory.cmData_sig_isConjOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelStepCharacterEqOneIntegralUnitary
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.L2.Forms
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TieUnr


set_option maxHeartbeats 4000000 in
theorem mt_eq_one_of_intUnit : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i < D.R.m, ∀ y : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), Matrix.GeneralLinearGroup.det y.1 ∈ intU D.host.F D.host.E → (∀ v, UnderSB t μ v → Formalism.UG.prV (E := D.host.E) v ((Matrix.GeneralLinearGroup.det y.1 : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) = 1) → (t.O u μ).mt (i + 1) (dtU y) = 1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a H T i hi y hint hsupp
  classical
  letI := D.host.cmStar
  have hzU : Matrix.GeneralLinearGroup.det y.1 ∈ U1 (sigD D) := det_in_unitary_one D.host.F D.host.E (sigD D) 1 1 (by simp) y.1 y.2
  obtain ⟨x', hx'int, hx'h90, hx'supp⟩ := GlobalTheory.T.integral_h90_preimage_trivial_at_places_over_trivial D.host.F D.host.E (sigD D) (GlobalTheory.T.cmData_conj_isConjOf _ _ D.sp.cm)
    (GlobalTheory.HeckeAdjoint.unramified_host D) _ hzU hint
  set x : (AfE t.X.F t.X.E)ˣ := Units.map A.iA.symm.toRingHom.toMonoidHom x' with hxdef
  have hxx : Units.map A.iA.toRingHom.toMonoidHom x = x' := by
    ext
    simp [x]
  have hq : A.q x = dtU y := H.q_dt x y (by rw [hxx, hx'h90])
  have hcoe : ∀ w : AfE t.X.F t.X.E, A.iA w ∈ RInt D.host.F D.host.E ↔ w ∈ RInt t.X.F t.X.E := H.iA_int
  have hxint : x ∈ intU t.X.F t.X.E := by
    refine ⟨(hcoe _).1 ?_, (hcoe _).1 ?_⟩
    · simpa [x] using hx'int.1
    · simpa [x] using hx'int.2

  have hsub : ∀ {K : Type} [Field K] [NumberField K] (w : FiniteAdeleRing (𝓞 K) K) (P : HeightOneSpectrum (𝓞 K)),
      (w - 1) P = w P - 1 := fun _ _ => rfl
  have hsuppX : ∀ Q : HeightOneSpectrum (𝓞 t.X.E), (∃ P ∈ SB t μ, P.under (𝓞 t.X.F) = Q.under (𝓞 t.X.F)) →
      GlobalTheory.Mem.Col2.afIso t.X.F t.X.E (x : AfE t.X.F t.X.E) Q = 1 := by
    rintro Q ⟨P, hP, hPQ⟩
    have hxm1 : (x : AfE t.X.F t.X.E) - 1 ∈ RInt t.X.F t.X.E := sub_mem hxint.1 (one_mem _)
    have key := GlobalTheory.T.afIso_ringEquiv_eq_zero_iff t.X.F t.X.E D.host.F D.host.E t.seam.iE A.iA H.iA_rat H.iA_int _ hxm1 Q
    have e1 : A.iA ((x : AfE t.X.F t.X.E) - 1) = (x' : AfE D.host.F D.host.E) - 1 := by
      rw [map_sub, map_one]
      simp [x]
    rw [e1] at key
    have hA : GlobalTheory.Mem.Col2.afIso t.X.F t.X.E ((x : AfE t.X.F t.X.E) - 1) Q =
        GlobalTheory.Mem.Col2.afIso t.X.F t.X.E (x : AfE t.X.F t.X.E) Q - 1 := by
      rw [map_sub, map_one]; rfl
    have hB : GlobalTheory.Mem.Col2.afIso D.host.F D.host.E ((x' : AfE D.host.F D.host.E) - 1) (seamP t.seam Q) =
        GlobalTheory.Mem.Col2.afIso D.host.F D.host.E (x' : AfE D.host.F D.host.E) (seamP t.seam Q) - 1 := by
      rw [map_sub, map_one]; rfl
    rw [← sub_eq_zero, ← hA]
    refine key.1 ?_
    show GlobalTheory.Mem.Col2.afIso D.host.F D.host.E ((x' : AfE D.host.F D.host.E) - 1) (seamP t.seam Q) = 0
    rw [hB, sub_eq_zero]
    refine hx'supp _ fun R hR => ?_
    have hv : UnderSB t μ ((seamP t.seam Q).under (𝓞 D.host.F)) := by
      refine ⟨P, hP, ?_⟩
      show ((seamP t.seam Q).under (𝓞 D.host.F)).asIdeal = ((seamP t.seam P).under (𝓞 D.host.F)).asIdeal
      rw [GlobalTheory.T.columnPrimeToBasePrime_preserves_common_place D t.X t.seam t.seam_ok H.fields.ok P Q hPQ]
    exact (GlobalTheory.T.placeComponent_eq_one_iff_components_over_eq_one _ _ _ _).1 (hsupp _ hv) R hR
  have hvG : ∀ P : HeightOneSpectrum (𝓞 t.X.E), (∃ k, ((t.Pr.g k : ℕ) : 𝓞 t.X.E) ∈ P.asIdeal) →
      GlobalTheory.Mem.Col2.afIso t.X.F t.X.E (x : AfE t.X.F t.X.E) P = 1 := by
    rintro P ⟨k, hk⟩
    obtain ⟨P', hP', hu⟩ := GlobalTheory.T.exists_typePrime_under_eq t.X t.Pr H.fields.ok t.pr_ok k P hk
    refine hsuppX P ⟨P', Finset.mem_union_left _ ?_, hu⟩
    fin_cases k
    · exact Finset.mem_union_left _ hP'
    · exact Finset.mem_union_right _ hP'
  have hiso : IsAdIso (GlobalTheory.Mem.Col2.afIso t.X.F t.X.E) :=
    ⟨GlobalTheory.Mem.Col2.afIso_tmul_one _ _, GlobalTheory.Mem.Col2.mem_rInt_iff _ _⟩
  have hmu : ∀ j : Fin D.R.m, D.muTil (j.1 + 1) (A.q x) = 1 := by
    intro j
    rw [H.muTil _ hiso j (GlobalTheory.Mem.ReadEx.toIdl t.X.F t.X.E x) x (fun w => rfl) (GlobalTheory.Mem.ReadEx.toIdl_snd x).symm]
    refine Units.ext ?_
    have h1 := GlobalTheory.Mem.ReadEx.map_toIdl_eq_one (H.mu0 j).tame hxint (fun P hP => ?_)
    · rw [h1]
    · have hg : ∃ k, ((t.Pr.g k : ℕ) : 𝓞 t.X.E) ∈ P.asIdeal := by
        by_contra hc
        push_neg at hc
        exact hP ((H.mu0 j).unr P hc)
      have h2 := hvG P hg
      show Valued.v (GlobalTheory.Mem.Col2.afIso t.X.F t.X.E ((x : AfE t.X.F t.X.E) - 1) P) ≤ _
      rw [map_sub, map_one, hsub, h2, sub_self, map_zero]
      exact zero_le'
  have hxi : (t.tup μ : Chr t.X.F t.X.E t.X.K) x = 1 := by
    have hmem := (t.tup μ).2
    simp only [tupGrp, finChar, Subgroup.mem_inf] at hmem
    refine GlobalTheory.T.openCharacter_eq_one_of_integralUnit_one_at_ramified t.X.F t.X.E t.X.K t.seam.σ₀ _ hmem.1.1.1.1.2 hmem.1.1.1.1.1 x hxint fun P hP => hsuppX P ?_
    refine ⟨t.sel (P.under (𝓞 t.X.F)), Finset.mem_union_right _ ?_, ?_⟩
    · have hs : (t.sel (P.under (𝓞 t.X.F))).under (𝓞 t.X.F) = P.under (𝓞 t.X.F) :=
        GlobalTheory.TwistPlaces.under_eq_iff.2 (H.sel _)
      refine (GlobalTheory.TwistPlaces.mem_QE_iff H.sel (t.tup μ)).2 ⟨?_, ?_⟩
      · rw [hs]; exact hP
      · rw [hs]
    · exact GlobalTheory.TwistPlaces.under_eq_iff.2 (H.sel _)
  rw [← hq]
  by_cases hμ : μ = D.what₂.mu0
  · rw [(H.ref hμ).2]
    exact hmu ⟨i, hi⟩
  · obtain ⟨ξ, hξ, hmt⟩ := H.tw μ hμ rfl
    rw [hmt u, twMt, if_pos ⟨by omega, by omega⟩, MonoidHom.mul_apply, hmu ⟨i, hi⟩, one_mul, hξ x, hxi, map_one]

end GlobalTheory.TieUnr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelStepCharacterEqOneIntegralUnitaryStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelStepCharacter_eq_one_integralUnitary : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i < D.R.m, ∀ y : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), Matrix.GeneralLinearGroup.det y.1 ∈ intU D.host.F D.host.E → (∀ v, UnderSB t μ v → Formalism.UG.prV (E := D.host.E) v ((Matrix.GeneralLinearGroup.det y.1 : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) = 1) → (t.O u μ).mt (i + 1) (dtU y) = 1) := by
  first | exact @GlobalTheory.TieUnr.mt_eq_one_of_intUnit | exact GlobalTheory.TieUnr.mt_eq_one_of_intUnit | (intros; apply GlobalTheory.TieUnr.mt_eq_one_of_intUnit <;> assumption)
end
