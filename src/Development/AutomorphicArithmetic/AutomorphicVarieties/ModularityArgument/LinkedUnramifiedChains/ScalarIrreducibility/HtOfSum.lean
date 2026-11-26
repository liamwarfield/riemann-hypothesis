module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.IrrTI
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMParameterQuotient
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.HasObs

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.FlatAss
private theorem flatAss_ann {A R : Type} [CommRing A] [CommRing R] [Algebra A R] [Module.Flat A R]
    (P : Ideal A) (a : A) (hmem : ∀ b, b ∈ P ↔ b * a = 0) (r : R) (h : a • r = 0) :
    r ∈ P.map (algebraMap A R) := by
  have h1 : ∑ _i : Fin 1, a • r = 0 := by
    rw [Fin.sum_univ_one]
    exact h
  obtain ⟨l, c, y, hy, hc⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (f := fun _ : Fin 1 => a)
      (x := fun _ : Fin 1 => r) h1
  have hr : r = ∑ j, c 0 j • y j := hy 0
  rw [hr]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [Algebra.smul_def]
  refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ((hmem _).2 ?_))
  have h2 := hc j
  rw [Fin.sum_univ_one] at h2
  rw [mul_comm]
  exact h2

private theorem flatAss_annih {A R : Type} [CommRing A] [CommRing R] [Algebra A R] [Module.Flat A R]
    (P : Ideal A) (a : A) (hmem : ∀ b, b ∈ P ↔ b * a = 0) :
    Module.annihilator R (Ideal.span {algebraMap A R a} : Ideal R) = P.map (algebraMap A R) := by
  apply le_antisymm
  · intro r hr
    have h0 : r * algebraMap A R a = 0 :=
      congrArg Subtype.val (Module.mem_annihilator.1 hr
        ⟨algebraMap A R a, Ideal.mem_span_singleton_self _⟩)
    refine flatAss_ann P a hmem r ?_
    rw [Algebra.smul_def, mul_comm]
    exact h0
  · refine Ideal.map_le_iff_le_comap.2 fun b hb => ?_
    rw [Ideal.mem_comap, Module.mem_annihilator]
    rintro ⟨n, hn⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hn
    apply Subtype.ext
    change algebraMap A R b * (c * algebraMap A R a) = 0
    rw [mul_left_comm, ← map_mul, (hmem b).1 hb, map_zero, mul_zero]

private theorem flatAss_alg {A R : Type} [CommRing A] [CommRing R] [IsNoetherianRing A]
    [IsNoetherianRing R] [Algebra A R] [Module.Flat A R] (Q : Ideal R) (hQ : Q.IsPrime)
    (hmin : ∀ P ∈ associatedPrimes R R, P ≤ Q → P ∈ minimalPrimes R)
    (P : Ideal A) (hP : P ∈ associatedPrimes A A) (hPQ : P ≤ Q.comap (algebraMap A R)) :
    P ∈ minimalPrimes A := by
  haveI : Algebra.HasGoingDown A R := Algebra.HasGoingDown.of_flat
  obtain ⟨hPp, a, hPa⟩ := isAssociatedPrime_iff.1 hP
  have hmem : ∀ b, b ∈ P ↔ b * a = 0 := fun b => by
    rw [hPa, Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul]
  have hmapQ : P.map (algebraMap A R) ≤ Q := Ideal.map_le_iff_le_comap.2 hPQ
  haveI := hQ
  obtain ⟨Q', hQ'min, hQ'Q⟩ := Ideal.exists_minimalPrimes_le hmapQ
  have hQ'ass : Q' ∈ associatedPrimes R R := by
    have h1 := hQ'min
    rw [← flatAss_annih P a hmem] at h1
    exact associatedPrimes.subset_of_injective (Submodule.injective_subtype _)
      (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R _ h1)
  have hQ'm := hmin Q' hQ'ass hQ'Q
  haveI hQ'p : Q'.IsPrime := hQ'min.1.1
  refine ⟨⟨hPp, bot_le⟩, fun p hp hpP => ?_⟩
  haveI := hp.1
  have hPc : P ≤ Q'.comap (algebraMap A R) := Ideal.map_le_iff_le_comap.1 hQ'min.1.2
  haveI : Q'.LiesOver (Q'.comap (algebraMap A R)) := ⟨rfl⟩
  obtain ⟨Q'', hle, hQ''p, hlies⟩ := Ideal.exists_ideal_le_liesOver_of_le Q' (hpP.trans hPc)
  have hge := hQ'm.2 ⟨hQ''p, bot_le⟩ hle
  have heq : Q'' = Q' := le_antisymm hle hge
  rw [hlies.over, heq]
  exact hPc

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

theorem UpperTheory.V.J.flatAss :
    ∀ (A R : Type) [CommRing A] [CommRing R] [IsNoetherianRing A] [IsNoetherianRing R] (ι : A →+* R), ι.Flat → ∀ Q : Ideal R, Q.IsPrime →
        (∀ P ∈ associatedPrimes R R, P ≤ Q → P ∈ minimalPrimes R) → ∀ P ∈ associatedPrimes A A, P ≤ Q.comap ι → P ∈ minimalPrimes A :=
  fun A R _ _ _ _ ι hι Q hQ hmin P hP hPQ =>
    @flatAss_alg A R _ _ _ _ ι.toAlgebra hι Q hQ hmin P hP hPQ
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.FlatHt
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

theorem UpperTheory.V.J.flatHt :
    ∀ (A R : Type) [CommRing A] [CommRing R] [IsNoetherianRing A] [IsNoetherianRing R] (ι : A →+* R), ι.Flat → ∀ (q : Ideal A) (Q : Ideal R),
        Q.IsPrime → Q.comap ι = q → Q ∈ (q.map ι).minimalPrimes → Q.height = q.height := by
  intro A R _ _ _ _ ι hι q Q hQ hcomap hmin
  letI : Algebra A R := ι.toAlgebra
  haveI : Module.Flat A R := hι
  haveI : Algebra.HasGoingDown A R := Algebra.HasGoingDown.of_flat
  haveI : q.IsPrime := hcomap ▸ Ideal.comap_isPrime ι Q
  haveI : Q.LiesOver q := ⟨hcomap.symm⟩
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown q Q]
  suffices h0 : (Q.map (Ideal.Quotient.mk (q.map (algebraMap A R)))).height = 0 by
    rw [h0, add_zero]
  have hJQ : q.map (algebraMap A R) ≤ Q := hmin.1.2
  have hker : RingHom.ker (Ideal.Quotient.mk (q.map (algebraMap A R))) ≤ Q := by
    rw [Ideal.mk_ker]
    exact hJQ
  haveI : (Q.map (Ideal.Quotient.mk (q.map (algebraMap A R)))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  rw [Ideal.height_eq_zero_iff]
  refine ⟨⟨inferInstance, bot_le⟩, ?_⟩
  rintro K ⟨hK, -⟩ hKQ
  have hle : K.comap (Ideal.Quotient.mk (q.map (algebraMap A R))) ≤ Q := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp (hKQ hx)
    have hd : y - x ∈ q.map (algebraMap A R) := Ideal.Quotient.eq.mp hxy
    have hx' : x = y - (y - x) := by ring
    rw [hx']
    exact Q.sub_mem hy (hJQ hd)
  have hc : Q ≤ K.comap (Ideal.Quotient.mk (q.map (algebraMap A R))) := by
    refine hmin.2 ⟨Ideal.comap_isPrime _ K, ?_⟩ hle
    intro x hx
    have hx2 : x ∈ q.map (algebraMap A R) := hx
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx2]
    exact K.zero_mem
  exact Ideal.map_le_iff_le_comap.mpr hc
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.CmOfRegularLocal
set_option linter.overlappingInstances false

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

open GroundTheory.Heights₂.Heights in
private theorem cm_of_regular_local (A : Type) [CommRing A] [IsRegularLocalRing A] :
    IsCohenMacaulayLocalRing A := by
  haveI hL : IsLocalRing A := IsRegularLocalRing.toIsLocalRing
  haveI hN : IsNoetherian A A := IsRegularLocalRing.toIsNoetherian
  obtain ⟨rs, hreg, hmax, hlen⟩ := GroundTheory.Arith.SchemeCoh.exists_isRegular_ofList_eq_maximalIdeal (R := A)
  refine @IsCohenMacaulayLocalRing.mk A _ hL hN ⟨rs, fun r hr => ?_, hreg.toIsWeaklyRegular, hlen.symm⟩
  rw [← hmax]
  exact Ideal.subset_span hr


open GroundTheory.Heights₂.Heights in
private theorem ass_min_of_surj {A B : Type} [CommRing A] [IsCohenMacaulayLocalRing A] [CommRing B]
    [Nontrivial B] (φ : A →+* B) (hφ : Function.Surjective φ) {k : ℕ} (x : Fin k → A)
    (hx : ∀ i, x i ∈ maximalIdeal A) (hk : RingHom.ker φ = Ideal.span (Set.range x))
    (hd : ringKrullDim B + (k : WithBot ℕ∞) ≤ ringKrullDim A) {P : Ideal B}
    (hP : P ∈ associatedPrimes B B) : P ∈ minimalPrimes B := by
  classical
  set I : Ideal A := Ideal.span (Set.range x) with hI
  let e : A ⧸ I ≃+* B := (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hφ)
  have hdimB : ringKrullDim B = ringKrullDim (A ⧸ I) := (ringKrullDim_eq_of_ringEquiv e).symm
  have hs : ((Finset.univ.image x : Finset A) : Set A) = Set.range x := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hcard : (Finset.univ.image x).card ≤ k :=
    Finset.card_image_le.trans (Finset.card_fin k).le
  have hle : ringKrullDim A ≤ ringKrullDim (A ⧸ I) + (k : WithBot ℕ∞) := by
    have h0 := ringKrullDim_le_ringKrullDim_quotient_add_card (R := A) (Finset.univ.image x) (by
      rw [hs, IsLocalRing.ringJacobson_eq_maximalIdeal]
      rintro _ ⟨i, rfl⟩
      exact hx i)
    rw [hs] at h0
    refine h0.trans ?_
    gcongr
  have heq : ringKrullDim (A ⧸ I) + (k : WithBot ℕ∞) = ringKrullDim A :=
    le_antisymm (hdimB ▸ hd) hle
  have hCM : IsCohenMacaulayLocalRing (A ⧸ I) :=
    CMParameterQuotient.proof CMRegularElement.proof A k x hx heq
  have : IsCohenMacaulayLocalRing B := IsCohenMacaulayLocalRing.of_ringEquiv e
  exact mem_minimalPrimes_of_mem_associatedPrimes hP

private theorem min_of_localized {R : Type} [CommRing R] (Q : Ideal R) [Q.IsPrime] {P : Ideal R}
    (hP : P ∈ associatedPrimes R R) (hPQ : P ≤ Q)
    (h : ∀ P' ∈ associatedPrimes (Localization.AtPrime Q) (Localization.AtPrime Q),
      P' ∈ minimalPrimes (Localization.AtPrime Q)) : P ∈ minimalPrimes R := by
  have hPprime : P.IsPrime := hP.1
  have hdis : Disjoint (Q.primeCompl : Set R) (P : Set R) := by
    rw [Set.disjoint_left]
    intro a ha haP
    exact ha (hPQ haP)
  set P' : Ideal (Localization.AtPrime Q) := P.map (algebraMap R (Localization.AtPrime Q)) with hP'
  have hcomap : Ideal.comap (algebraMap R (Localization.AtPrime Q)) P' = P :=
    IsLocalization.under_map_of_isPrime_disjoint Q.primeCompl (Localization.AtPrime Q) hPprime hdis
  have hass : P' ∈ associatedPrimes (Localization.AtPrime Q) (Localization.AtPrime Q) := by
    refine Module.associatedPrimes.mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
      Q.primeCompl (Algebra.linearMap R (Localization.AtPrime Q)) P' ?_
    rw [hcomap]
    exact hP
  have hmin : P' ∈ (Ideal.map (algebraMap R (Localization.AtPrime Q)) (⊥ : Ideal R)).minimalPrimes := by
    rw [Ideal.map_bot]
    exact h P' hass
  rw [IsLocalization.minimalPrimes_map Q.primeCompl (Localization.AtPrime Q) (⊥ : Ideal R)] at hmin
  have key : Ideal.comap (algebraMap R (Localization.AtPrime Q)) P' ∈ (⊥ : Ideal R).minimalPrimes := hmin
  rw [hcomap] at key
  exact key

theorem UpperTheory.V.J.unmix :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (N N' : ℕ) (R : Type) [CommRing R]
        (p : MvPowerSeries (Fin N) O →+* R) (f : Fin N' → MvPowerSeries (Fin N) O), Function.Surjective p → RingHom.ker p = Ideal.span (Set.range f) →
        ∀ Q : Ideal R, Q.IsPrime → Q.height + N' ≤ (Q.comap p).height → ∀ P ∈ associatedPrimes R R, P ≤ Q → P ∈ minimalPrimes R := by
  intro O _ _ _ _ N N' R _ p f hp hker Q hQ hht P hP hPQ
  set q : Ideal (MvPowerSeries (Fin N) O) := Q.comap p with hq
  haveI : IsRegularLocalRing (MvPowerSeries (Fin N) O) :=
    GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries O (Fin N)
  haveI : IsRegularLocalRing (Localization.AtPrime q) :=
    GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.localization_atPrime q
  haveI : GroundTheory.Heights₂.Heights.IsCohenMacaulayLocalRing (Localization.AtPrime q) :=
    cm_of_regular_local _
  let φ : Localization.AtPrime q →+* Localization.AtPrime Q := Localization.localRingHom q Q p rfl
  have hφ : Function.Surjective φ := RingHom.surjective_localRingHom_of_surjective p hp Q
  have hkerφ : RingHom.ker φ = (RingHom.ker p).map (algebraMap _ (Localization.AtPrime q)) :=
    IsLocalization.ker_map (M := q.primeCompl) (S := Localization.AtPrime q)
      (Localization.AtPrime Q) p (Submonoid.map_comap_eq_of_surjective hp Q.primeCompl)
  have hkx : RingHom.ker φ = Ideal.span (Set.range (fun i => algebraMap _ (Localization.AtPrime q) (f i))) := by
    rw [hkerφ, hker, Ideal.map_span, ← Set.range_comp]
    rfl
  have hx : ∀ i, algebraMap _ (Localization.AtPrime q) (f i) ∈ maximalIdeal (Localization.AtPrime q) := by
    intro i
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q]
    have hfi : f i ∈ RingHom.ker p := by
      rw [hker]
      exact Ideal.subset_span ⟨i, rfl⟩
    show p (f i) ∈ Q
    rw [RingHom.mem_ker.mp hfi]
    exact Q.zero_mem
  have hd : ringKrullDim (Localization.AtPrime Q) + (N' : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime q) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q),
      IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)]
    exact_mod_cast hht
  refine min_of_localized Q hP hPQ ?_
  intro P' hP'
  exact ass_min_of_surj φ hφ _ hx hkx hd hP'
end

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

private theorem ht_of_sum {h : ℕ∞} {N : ℕ} {D : WithBot ℕ∞} (hD : D = 1)
    (e : (h : WithBot ℕ∞) + D = (N + 1 : ℕ)) : h = N := by
  subst hD
  have e2 : ((h + 1 : ℕ∞) : WithBot ℕ∞) = (((N + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    rw [WithBot.coe_add, WithBot.coe_one, WithBot.coe_natCast]
    exact e
  have e3 : h + 1 = ((N + 1 : ℕ) : ℕ∞) := WithBot.coe_injective e2
  induction h using ENat.recTopCoe with
  | top =>
    rw [top_add] at e3
    exact absurd e3.symm (ENat.coe_ne_top _)
  | coe k =>
    norm_cast at e3 ⊢
    omega

private theorem le_of_add {a : ℕ∞} {b c : ℕ} (h : ((c + b : ℕ) : ℕ∞) ≤ a + b) : (c : ℕ∞) ≤ a := by
  induction a using ENat.recTopCoe with
  | top => exact le_top
  | coe k =>
    norm_cast at h ⊢
    omega

theorem UpperTheory.V.J.htLow :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (F : Fr.Frame l (ResidueField c.O)) (C₀ n : ℕ), F.Ok C₀ → (n = 2 ∨ n = 3) →
        ∀ (S : Fr.Space c.O F n), ∀ (q x : Ideal S.A) (L : S.Loc x) (Q : Ideal L.R), Over S L q Q →
          ((n * F.d + 1 : ℕ) : ℕ∞) ≤ q.height ∧ (Q.height ≤ ((n * F.d + 1 : ℕ) : ℕ∞) → ∀ P ∈ associatedPrimes S.A S.A, P ≤ q → P ∈ minimalPrimes S.A) := by
  intro l _ c _ F C₀ n hF hn S q x L Q hO
  obtain ⟨hQ, him, hmin, hdim⟩ := hO
  obtain ⟨N, N', p, f, hN, hp, hker⟩ := Fr.pres hF hn S x L
  obtain ⟨hfl, -, -⟩ := Fr.loc_flat hF hn S x L
  have hA : IsNoetherianRing S.A := (Fr.gr_A hF hn S).2.2.2.2.2.1
  have hR : IsNoetherianRing L.R := inferInstance
  obtain ⟨h1, h2⟩ := htPres L.O' N N' L.R p f hp hker Q hQ
  have hc : (Ideal.comap p Q).height = N := ht_of_sum hdim h1
  have hfh : Q.height = q.height := flatHt S.A L.R L.ι hfl q Q hQ him hmin
  have hlow : ((n * F.d + 1 : ℕ) : ℕ∞) ≤ Q.height := by
    apply le_of_add (b := N')
    rw [Nat.add_comm, ← hN, ← hc]
    exact h2
  refine ⟨hfh ▸ hlow, fun hle P hP hPq => ?_⟩
  have hu : Q.height + N' ≤ (Ideal.comap p Q).height := by
    rw [hc, hN, Nat.cast_add, add_comm (N' : ℕ∞)]
    exact add_le_add hle le_rfl
  refine flatAss S.A L.R L.ι hfl Q hQ (unmix L.O' N N' L.R p f hp hker Q hQ hu) P hP ?_
  change P ≤ L.im Q
  rw [him]
  exact hPq
