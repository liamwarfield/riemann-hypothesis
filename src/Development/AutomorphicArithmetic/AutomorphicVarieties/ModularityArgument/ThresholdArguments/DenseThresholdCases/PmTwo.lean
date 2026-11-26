module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.PtLaws
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EndsRankThreeOfLocal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSolDescent

@[expose] public section

attribute [-instance] Formalism.BasicNotions.NTypes.instMray Formalism.BasicNotions.NTypes.nfMray Formalism.BasicNotions.NTypes.algKM UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Alg.IsCO.complete UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.LinkTwo
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem exists_placeOver_of_placeOver_lp {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    (A : ValuationSubring Ω) (v : W.Plc (W.Lp L)) (h : IsPlaceOver A v) : ∃ w : W.Plc L, IsPlaceOver A w := by
  have hle : ∀ x : 𝓞 L, algebraMap L Ω x ∈ A := by
    intro x
    have h1 : IsIntegral ℤ (algebraMap L Ω x) :=
      (RingOfIntegers.isIntegral_coe x).map (IsScalarTower.toAlgHom ℤ L Ω)
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp (h1.tower_top (A := A))
    rw [← hy]
    exact y.2
  let g : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A.toSubring hle
  have hmem : ∀ x : 𝓞 L, x ∈ (IsLocalRing.maximalIdeal A).comap g ↔ A.valuation (algebraMap L Ω x) < 1 := by
    intro x
    rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
    rfl
  have hnb : (IsLocalRing.maximalIdeal A).comap g ≠ ⊥ := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    intro hb
    have hm : algebraMap (𝓞 (W.Lp L)) (𝓞 L) y ∈ (IsLocalRing.maximalIdeal A).comap g := by
      rw [hmem]
      have he : (algebraMap L Ω) ↑((algebraMap (𝓞 (W.Lp L)) (𝓞 L)) y) = (algebraMap (W.Lp L) Ω) ↑y := rfl
      rw [he]
      exact (h y).mpr hy
    rw [hb, Ideal.mem_bot] at hm
    have e : ((algebraMap (𝓞 (W.Lp L)) (𝓞 L) y : 𝓞 L) : L) = algebraMap (W.Lp L) L (y : W.Lp L) := rfl
    rw [hm] at e
    have e2 : (y : W.Lp L) = 0 := (algebraMap (W.Lp L) L).injective (by rw [← e, map_zero]; rfl)
    exact hy0 (RingOfIntegers.ext (by rw [e2]; rfl))
  refine ⟨⟨(IsLocalRing.maximalIdeal A).comap g, Ideal.comap_isPrime _ _, hnb⟩, ?_⟩
  intro x
  exact (hmem x).symm

theorem UpperTheory.Gal.projectedFormsSystemPart.mkSetP :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω], l ≠ 2 → (∀ A : ValuationSubring Ω, Ine (F := W.Lp L) A ≤ (W.resP L Ω).range) → ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime) → l ∈ S → (∀ q ∈ S, ∀ A : ValuationSubring Ω, A.valuation (q : Ω) < 1 → Dec (F := W.Lp L) A ≤ (W.resP L Ω).range) → ∀ A₀ : W.Vl l L → ValuationSubring Ω, (∀ v, IsPlaceOver (A₀ v) v.1) → ∀ (v₀ : W.Plc (W.Lp L)) (B : ValuationSubring Ω) (p : ℕ), p.Prime → p ≠ 2 → p ∉ S → ¬ (p : ℤ) ∣ discr L → ((p : ℕ) : 𝓞 (W.Lp L)) ∈ v₀.asIdeal → normV v₀ = p → IsPlaceOver B v₀ → Dec (F := W.Lp L) B ≤ (W.resP L Ω).range → ∃ s : W.HidaSetting l L Ω, s.p = p ∧ (∀ v : W.Vl l L, s.A v = A₀ v) ∧ s.A s.v0 = B ∧ s.S.Finite ∧ (∀ q ∈ S, ¬ B.valuation (q : Ω) < 1) ∧ ∀ (A : ValuationSubring Ω) (v : W.Plc (W.Lp L)), IsPlaceOver A v → v ∉ s.S → ∀ q ∈ S, ¬ A.valuation (q : Ω) < 1 := by
  intro l _ L Ω _ _ _ _ _ _ hl hunr S hSp hlS hSd A₀ hA₀ v₀ B p hp hp2 hpS hdisc hpv hnorm hB hBd
  classical
  have eq_of_mem {q : ℕ} (hq : q.Prime) (hqv : (q : 𝓞 (W.Lp L)) ∈ v₀.asIdeal) : p = q := by
    by_contra hne
    obtain ⟨a, b, hab⟩ := Nat.Coprime.cast (R := 𝓞 (W.Lp L)) ((Nat.coprime_primes hp hq).2 hne)
    exact v₀.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ add_mem (v₀.asIdeal.mul_mem_left a hpv) (v₀.asIdeal.mul_mem_left b hqv)))
  have val_nat {A : ValuationSubring Ω} {v : W.Plc (W.Lp L)} (h : IsPlaceOver A v) (q : ℕ) :
      A.valuation (q : Ω) < 1 ↔ (q : 𝓞 (W.Lp L)) ∈ v.asIdeal := by
    rw [← map_natCast (algebraMap (W.Lp L) Ω) q]
    exact h (q : 𝓞 (W.Lp L))
  have fin_nat {q : ℕ} (hq : q ≠ 0) : {v : W.Plc (W.Lp L) | (q : 𝓞 (W.Lp L)) ∈ v.asIdeal}.Finite := by
    have h := Ideal.finite_factors (I := Ideal.span {(q : 𝓞 (W.Lp L))}) fun hspan =>
      Nat.cast_ne_zero.mpr hq (Ideal.span_singleton_eq_bot.mp hspan)
    simpa only [Ideal.dvd_span_singleton] using h
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hpl : p ≠ l := fun e => hpS (e ▸ hlS)
  have hlv₀ : ((l : ℕ) : 𝓞 (W.Lp L)) ∉ v₀.asIdeal := fun h => hpl (eq_of_mem Fact.out h)
  let Aof : W.Plc (W.Lp L) → ValuationSubring Ω := fun v =>
    if h : ((l : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal then A₀ ⟨v, h⟩
    else if v = v₀ then B else Classical.choose (exists_isPlaceOver Ω v)
  have hAof : ∀ v, IsPlaceOver (Aof v) v := by
    intro v
    simp only [Aof]
    split_ifs with h1 h2
    · exact hA₀ _
    · subst h2
      exact hB
    · exact Classical.choose_spec (exists_isPlaceOver Ω v)
  have hA0 : Aof v₀ = B := by
    simp only [Aof, dite_eq_right hlv₀, ite_true]
  let wof : W.Plc (W.Lp L) → W.Plc L := fun v => Classical.choose (exists_placeOver_of_placeOver_lp (Aof v) v (hAof v))
  have hwof : ∀ v, IsPlaceOver (Aof v) (wof v) := fun v => Classical.choose_spec (exists_placeOver_of_placeOver_lp (Aof v) v (hAof v))
  have hStf : {v : W.Plc (W.Lp L) | ∃ q ∈ S, ((q : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal ∧
      ((l : ℕ) : 𝓞 (W.Lp L)) ∉ v.asIdeal}.Finite := by
    refine (Set.Finite.biUnion S.finite_toSet fun q hq => fin_nat (hSp q hq).ne_zero).subset ?_
    rintro v ⟨q, hq, hqv, -⟩
    exact Set.mem_biUnion hq hqv
  let St := hStf.toFinset
  have hSt : ∀ v, v ∈ St ↔ ∃ q ∈ S, ((q : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal ∧ ((l : ℕ) : 𝓞 (W.Lp L)) ∉ v.asIdeal :=
    fun v => hStf.mem_toFinset
  have hSt_l : ∀ u ∈ St, ((l : ℕ) : 𝓞 (W.Lp L)) ∉ u.asIdeal := by
    intro u hu
    obtain ⟨q, -, -, h⟩ := (hSt u).mp hu
    exact h
  have hv0 : v₀ ∉ St := by
    intro hv
    obtain ⟨q, hq, hqv, -⟩ := (hSt v₀).mp hv
    obtain rfl := eq_of_mem (hSp q hq) hqv
    exact hpS hq
  have hsplit : ∀ v : W.Plc (W.Lp L), ((l : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal ∨ v ∈ St ∨ v = v₀ →
      Dec (Aof v) ≤ (W.resP L Ω).range := by
    rintro v (h | h | rfl)
    · exact hSd l hlS (Aof v) ((val_nat (hAof v) l).mpr h)
    · obtain ⟨q, hq, hqv, -⟩ := (hSt v).mp h
      exact hSd q hq (Aof v) ((val_nat (hAof v) q).mpr hqv)
    · rw [hA0]
      exact hBd
  have exists_conj : ∃ c : G (W.Lp L) Ω, ∃ j : Ω →+* ℂ, ∀ x, j (c x) = starRingEnd ℂ (j x) := by
    obtain ⟨φ⟩ : Nonempty (L →+* ℂ) := inferInstance
    let : Algebra L ℂ := φ.toAlgebra
    have : Algebra.IsAlgebraic L Ω := IsAlgClosure.isAlgebraic
    let j : Ω →ₐ[L] ℂ := _root_.IsAlgClosed.lift
    let : Algebra Ω ℂ := (j : Ω →+* ℂ).toAlgebra
    have : IsScalarTower (W.Lp L) Ω ℂ :=
      IsScalarTower.of_algebraMap_eq fun x => (j.commutes (x : L)).symm
    let conjugation : ℂ →ₐ[W.Lp L] ℂ :=
      { starRingEnd ℂ with commutes' := fun x => (mem_maximalRealSubfield_iff (x : L)).1 x.2 φ }
    exact ⟨conjugation.restrictNormal' Ω, j, fun x => conjugation.restrictNormal_commutes Ω x⟩
  obtain ⟨c, hc⟩ := exists_conj
  refine ⟨W.HidaSetting.mk hl (fun A _ _ => hunr A) c hc wof Aof hwof hAof St hSt_l v₀ hv0 p hp hp2 hpl hdisc hnorm
    hsplit, rfl, ?_, hA0, ?_, ?_, ?_⟩
  · intro v
    show Aof v.1 = A₀ v
    simp only [Aof, dite_eq_left v.2]
  · refine (((fin_nat hl0).union St.finite_toSet).union (Set.finite_singleton v₀)).subset ?_
    rintro v (h | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  · intro q hq hlt
    rw [val_nat hB] at hlt
    obtain rfl := eq_of_mem (hSp q hq) hlt
    exact hpS hq
  · intro A v hAv hvS q hq hlt
    rw [val_nat hAv] at hlt
    by_cases hlv : ((l : ℕ) : 𝓞 (W.Lp L)) ∈ v.asIdeal
    · exact hvS (Or.inl hlv)
    · exact hvS (Or.inr (Or.inl ((hSt v).mpr ⟨q, hq, hlt, hlv⟩)))

private theorem mem_ine_of_apply_eq_of_mem_ine {Ω F F' : Type} [Field Ω] [Field F] [Field F'] [NumberField F] [NumberField F']
    [Algebra F Ω] [Algebra F' Ω] {A : ValuationSubring Ω} {σ : G F Ω} {τ : G F' Ω}
    (h : ∀ x : Ω, τ x = σ x) (hs : σ ∈ Ine A) : τ ∈ Ine A := by
  obtain ⟨h1, h2⟩ := hs
  refine ⟨?_, fun x hx => by simpa only [h x] using h2 x hx⟩
  change τ ∈ Dec A
  rw [mem_Dec]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
    ← apply_mem_iff_of_mem_Dec h1 (τ⁻¹ x), ← h]
  simp

private theorem dec_of_ok_of_valuation_lt_one {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    {D : Raw Ω c} (T : Tower D) (hOk : T.Ok) (q : ℕ) (hq : q ∈ D.S) (A : ValuationSubring Ω)
    (hA : A.valuation (q : Ω) < 1) : Dec (F := W.Lp T.L) A ≤ (W.resP T.L Ω).range := by
  intro σ hσ
  obtain ⟨hF, ⟨φ, hφ, hφL⟩, hGal⟩ := galEq T
  let σ' : G ℚ Ω := σ.restrictScalars ℚ
  have h1 : σ' ∈ Dec (F := ℚ) A := by
    rw [mem_Dec] at hσ ⊢
    exact hσ
  have hK : σ' ∈ T.K.fixingSubgroup := hOk.split q hq A hA h1
  have hFix : ∀ x ∈ T.F, σ' x = x := by
    intro x hx
    obtain ⟨y, rfl⟩ := (hF x).mp hx
    exact σ.commutes y
  have hLeq : T.L = T.F ⊔ T.K := by
    cases T
    assumption
  have hL : σ' ∈ T.L.fixingSubgroup := by
    rw [hLeq, IntermediateField.fixingSubgroup_sup]
    exact ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).mpr hFix, hK⟩
  let g : G T.L Ω := AlgEquiv.ofRingEquiv (f := σ'.toRingEquiv)
    (fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).mp hL x x.2)
  rw [← hφL, hGal]
  exact ⟨g, AlgEquiv.ext fun x => (hφ σ x).symm⟩

theorem UpperTheory.Gal.projectedFormsSystemPart.setAv :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} (T : Tower D), D.Good → T.Ok → ∀ p₀ : ℕ, p₀ ≠ 0 → ∃ Y : SetD T, ¬ Y.s.p ∣ p₀ := by
  intro Ω _ _ _ l _ c D T hG hOk p₀ hp₀
  obtain ⟨g₀, hg₁, hg₂⟩ := gEx T hOk
  obtain ⟨e, he⟩ := placesEq T
  obtain ⟨hF, ⟨φ, hφ, hφL⟩, hGal⟩ := galEq T
  have hunr : ∀ A : ValuationSubring Ω, Ine (F := W.Lp T.L) A ≤ (W.resP T.L Ω).range := by
    intro A σ hσ
    exact (hφL σ).mp (hOk.unr A (mem_ine_of_apply_eq_of_mem_ine (hφ σ) hσ))
  have hbf := barFacts hG
  let bu (γ : G ℚ Ω →* c.Oˣ) : G T.L Ω →* (ResidueField c.O)ˣ :=
    ((Units.map (residue c.O).toMonoidHom).comp γ).comp (resQ T.L)
  have bu_val (γ : G ℚ Ω →* c.Oˣ) (g : G T.L Ω) :
      (bu γ g : ResidueField c.O) = Raw.bar γ (resQ T.L g) := rfl
  have bu_open (γ : G ℚ Ω →* c.Oˣ) (h : IsOpen {g : G ℚ Ω | Raw.bar γ g = 1}) :
      IsOpen ((bu γ).ker : Set (G T.L Ω)) := by
    have hk : ((bu γ).ker : Set (G T.L Ω)) = resQ T.L ⁻¹' {g | Raw.bar γ g = 1} := by
      ext g
      simp [MonoidHom.mem_ker, Units.ext_iff, bu_val]
    rw [hk]
    exact h.preimage (Af.continuous_restrictScalarsHom ℚ T.L Ω)
  have eq_of_ker {γ : G ℚ Ω →* c.Oˣ} {a b : G T.L Ω} (h : a⁻¹ * b ∈ (bu γ).ker) :
      bu γ a = bu γ b := by
    rwa [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h
  let U : Subgroup (G T.L Ω) := (⨅ i : Fin 4, (bu (chi D T.pr i)).ker) ⊓ (bu D.om).ker
  have hUo : IsOpen (U : Set (G T.L Ω)) := by
    rw [Subgroup.coe_inf, Subgroup.coe_iInf]
    refine (isOpen_iInter_of_finite fun i => bu_open _ ?_).inter (bu_open _ hbf.2.1)
    unfold chi
    exact hbf.1 _
  let M : ℕ := p₀ * 2 * (∏ q ∈ D.S, q) * (NumberField.discr T.L).natAbs
  have hM : M ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero hp₀ two_ne_zero) ?_) ?_
    · exact Finset.prod_ne_zero_iff.mpr fun q hq => (hG.S_prime q hq).ne_zero
    · exact Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero T.L)
  obtain ⟨v, B, p, hp, hpM, hpv, hnorm, hB, hBd, hU1, hU2⟩ := v0Ex T.L Ω U hUo g₀ M hM
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hpM (((dvd_mul_left 2 p₀).mul_right _).mul_right _)
  have hpS : p ∉ D.S := fun h =>
    hpM ((((Finset.dvd_prod_of_mem (fun q => q) h).mul_left (p₀ * 2))).mul_right _)
  have hdisc : ¬ (p : ℤ) ∣ NumberField.discr T.L := fun h =>
    hpM ((Int.natCast_dvd.mp h).mul_left _)
  obtain ⟨s, hsp, hsA, hsv0, hSf, hBaway, hAway⟩ :=
    UpperTheory.Gal.projectedFormsSystemPart.mkSetP l T.L Ω hG.l_odd hunr D.S hG.S_prime hG.l_mem
      (fun q hq A hA => dec_of_ok_of_valuation_lt_one T hOk q hq A hA) (fun v => T.pl (e v)) he v B p hp hp2 hpS hdisc hpv hnorm hB hBd
  have hchi : ∀ d ∈ Dec (s.A s.v0), ∀ i j : Fin 4,
      Raw.bar (chi D T.pr i) ((resQ T.L) d) = Raw.bar (chi D T.pr j) ((resQ T.L) d) := by
    intro d hd i j
    rw [hsv0] at hd
    obtain ⟨n, hn⟩ := hU1 d hd
    have key : ∀ k : Fin 4, Raw.bar (chi D T.pr k) ((resQ T.L) d) = Raw.bar (chi D T.pr k) ((resQ T.L) g₀) ^ n := by
      intro k
      have hk := eq_of_ker (γ := chi D T.pr k) (Subgroup.mem_iInf.mp hn.1 k)
      rw [← bu_val, ← bu_val, hk]
      exact (congrArg Units.val (map_zpow (bu (chi D T.pr k)) g₀ n)).trans (Units.val_zpow_eq_zpow_val _ _)
    rw [key i, key j, hg₁ i j]
  have hom : ∃ d ∈ Dec (s.A s.v0), Raw.bar D.om ((resQ T.L) d) ≠ 1 := by
    rw [hsv0]
    obtain ⟨d, hd, hdU⟩ := hU2
    refine ⟨d, hd, ?_⟩
    have hk := eq_of_ker (γ := D.om) hdU.2
    rw [← bu_val, hk, bu_val]
    exact hg₂
  refine ⟨SetD.mk s e hsA hSf (fun A w h1 h2 => hAway A w h1 h2) (by rw [hsv0]; exact hBaway) hchi hom (ccOf T s), ?_⟩
  show ¬ s.p ∣ p₀
  rw [hsp]
  intro h
  exact hpM (((h.mul_right 2).mul_right _).mul_right _)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DnPmDown
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphyDescentSolvableCMToImaginaryQuadraticA
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWOfOne
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Z.Bc
theorem UpperTheory.GalN.V.ofOne0_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → Third → Across → ∀ (K Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω]
    [IsAlgClosure ℚ Ω], Module.finrank ℚ K = 2 → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n →
    ∀ (r : G ℚ Ω →* GL (Fin n) (Qbar l)) (θ : G ℚ Ω →* (Qbar l)ˣ), IsAlgChar ι θ → DualTw r θ →
    IsIrr (r.comp (resG ℚ K Ω)) → IsAut ι (r.comp (resG ℚ K Ω)) → IsAutomorphicOverImagQuad ι r := by
  intro hP hT hA K Ω _ _ _ _ _ _ _ _ hK l _ ι n hn r θ hθ hd hirr haut hc K' _ _ _ inst _ tow hK' hirr'
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  obtain ⟨K'', _, _, _, _, _, hK'', h1, h2⟩ := hT K K' Ω hK hK' l n r hirr hirr'
  have h3 := hA K K'' Ω hK hK'' l ι n hn r θ hc hθ hd h1 haut
  rw [inf_comm] at h2
  have h4 := hA K'' K' Ω hK'' hK' l ι n hn r θ hc hθ hd h2 h3
  exact (_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hP K' Ω l ι n _).2.1.1 h4
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAcross
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Z.Bc
open scoped Matrix
private theorem across_cc (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] : ∃ c : G ℚ Ω, IsConjEl c := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  let j : Ω →ₐ[ℚ] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  let τ : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := starRingAut) fun x => by simp
  exact ⟨τ.restrictNormal Ω, algebraMap Ω ℂ, fun x => AlgEquiv.restrictNormal_commutes τ Ω x⟩
private theorem across_pair {F₀ F Ω k : Type} [Field F₀] [Field F] [Field Ω] [Algebra F₀ F] [Algebra F₀ Ω] [Algebra F Ω]
    [IsScalarTower F₀ F Ω] [Field k] {n : ℕ} (r : G F₀ Ω →* GL (Fin n) k) (θ : G F₀ Ω →* kˣ) (h : DualTw r θ)
    (c : G F₀ Ω) : ∃ P, IsPairing c (r.comp (resG F₀ F Ω)) (θ.comp (resG F₀ F Ω)) P := by
  obtain ⟨J, hJ⟩ := h
  refine ⟨J * r c⁻¹, fun s s' h => ?_⟩
  have h' : resG F₀ F Ω s' = c * resG F₀ F Ω s * c⁻¹ := h
  have e : r c⁻¹ * r (resG F₀ F Ω s') = r (resG F₀ F Ω s) * r c⁻¹ := by
    rw [h', ← map_mul, ← map_mul]; congr 1; group
  have e' : (r c⁻¹).val * (r (resG F₀ F Ω s')).val = (r (resG F₀ F Ω s)).val * (r c⁻¹).val := congrArg Units.val e
  have hp := hJ (resG F₀ F Ω s)
  simp only [MonoidHom.comp_apply]
  rw [Units.val_mul, ← Matrix.smul_mul, ← hp]
  simp only [Matrix.mul_assoc, e']
private theorem across_tf (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] : Module.IsTorsionFree L Ω :=
  DivisionSemiring.to_moduleIsTorsionFree
attribute [local instance] across_tf
private theorem across_up (L Ω : Type) [Field L] [CharZero L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra L Ω] :
    IsAlgClosure L Ω :=
  ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩
private theorem across_irr {Γ Δ Δ' k : Type} [Group Γ] [Group Δ] [Group Δ'] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (f : Δ →* Γ) (f' : Δ' →* Γ) (h : ∀ s, ∃ t, f' t = f s) (H : IsIrr (r.comp f)) : IsIrr (r.comp f') := by
  refine ⟨H.1, fun _ _ _ => trivial, fun W hW hI => H.2.2 W hW fun s v hv => ?_⟩
  obtain ⟨t, ht⟩ := h s
  have := hI t v hv
  rw [MonoidHom.comp_apply, ht] at this
  exact this
theorem UpperTheory.V.Z.Bc.across_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → SolC → BiQuad → Across := by
  intro _ hS hB K K' Ω _ _ _ _ _ _ _ iA _ _ iT iT' iC hK hK' l _ ι n hn r θ hr hθ hd hirr haut
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain rfl : iA = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  obtain ⟨M, _, _, iM, _, _, _, _, _, _, _, hs, hs', hM, -⟩ := hB K K' Ω hK hK'
  haveI := across_up K Ω
  haveI := across_up K' Ω
  haveI := across_up M Ω
  obtain ⟨c, hc⟩ := across_cc Ω
  have he : (r.comp (resG ℚ K Ω)).comp (resG K M Ω) = (r.comp (resG ℚ K' Ω)).comp (resG K' M Ω) :=
    MonoidHom.ext fun s => rfl
  have hi : IsIrr ((r.comp (resG ℚ K Ω)).comp (resG K M Ω)) := by
    refine across_irr r _ ((resG ℚ K Ω).comp (resG K M Ω)) ?_ hirr
    rintro ⟨s, ⟨t, rfl⟩, h2⟩
    obtain ⟨u, rfl⟩ := (hM t).2 h2
    exact ⟨u, rfl⟩
  obtain ⟨P, hP⟩ := across_pair (F := K) r θ hd c
  obtain ⟨P', hP'⟩ := across_pair (F := K') r θ hd c
  have h1 := (hS ℚ K M Ω hs ⟨inferInstance, Or.inr ⟨hK, inferInstance⟩⟩ inferInstance iM l ι n hn _ θ
    (hr.comp (continuous_restrictScalarsHom ℚ K Ω)) hi hθ (UpperTheory.V.Ws.auSign θ) ⟨c, P, hc, hP⟩).1 haut
  rw [he] at h1 hi
  exact (hS ℚ K' M Ω hs' ⟨inferInstance, Or.inr ⟨hK', inferInstance⟩⟩ inferInstance iM l ι n hn _ θ
    (hr.comp (continuous_restrictScalarsHom ℚ K' Ω)) hi hθ (UpperTheory.V.Ws.auSign θ) ⟨c, P', hc, hP'⟩).2 h1
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Z.Bc
theorem UpperTheory.GalN.V.isAutomorphicOverImagQuad_of_restriction_aut_irr (H : _root_.UpperTheory.V.Af.HypothesesH') (hS : SolC) (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    (K L : IntermediateField ℚ Ω) [NumberField K] [NumberField L] [IsCMField K] [IsCMField L] (hle : K ≤ L)
    (hK : Module.finrank ℚ K = 2) (hgal : IsGalois ℚ L) (hsol : IsSolvable (L ≃ₐ[ℚ] L)) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (n : ℕ) (hn : 1 ≤ n) (r : G ℚ Ω →* GL (Fin n) (Qbar l)) (θ : G ℚ Ω →* (Qbar l)ˣ) (hr : Continuous r) (hθ : IsAlgChar ι θ)
    (hd : DualTw r θ) (hirr : IsIrr (r.comp (resG ℚ L Ω))) (haut : IsAut ι (r.comp (resG ℚ L Ω))) : IsAutomorphicOverImagQuad ι r := by
  letI : Algebra K L := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower K L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : IsGalois K L := IsGalois.tower_top_of_isGalois ℚ K L
  haveI : Group.IsSolvable (L ≃ₐ[ℚ] L) := hsol
  have s2 : IsSolvable (L ≃ₐ[K] L) :=
    Group.isSolvable_of_isSolvable_injective (f := (AlgEquiv.restrictScalarsHom ℚ : (L ≃ₐ[K] L) →* (L ≃ₐ[ℚ] L)))
      (AlgEquiv.restrictScalars_injective ℚ)
  have e : (r.comp (resG ℚ K Ω)).comp (resG K L Ω) = r.comp (resG ℚ L Ω) := rfl
  have i2 : IsIrr ((r.comp (resG ℚ K Ω)).comp (resG K L Ω)) := e ▸ hirr
  have i1 : IsIrr (r.comp (resG ℚ K Ω)) := (UpperTheory.galoisRep_irreducibility_criterion.1 _ _ _ n _).1 _ i2
  have hconj : ∃ c : G ℚ Ω, IsConjEl c := by
    have : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
    let j : Ω →ₐ[ℚ] ℂ := _root_.IsAlgClosed.lift
    let E : IntermediateField ℚ ℂ := j.fieldRange
    let e : Ω ≃ₐ[ℚ] E := AlgEquiv.ofInjectiveField j
    have : Normal ℚ E := Normal.of_algEquiv e
    let f : E →ₐ[ℚ] ℂ := (starRingEnd ℂ).toRatAlgHom.comp E.val
    let g : E ≃ₐ[ℚ] E := f.restrictNormal' E
    have hg (y : E) : (g y : ℂ) = starRingEnd ℂ (y : ℂ) :=
      f.restrictNormal_commutes E y
    have he (x : Ω) : (e x : ℂ) = j x := rfl
    refine ⟨e.trans (g.trans e.symm), j.toRingHom, fun x => ?_⟩
    show j (e.symm (g (e x))) = starRingEnd ℂ (j x)
    rw [← he, AlgEquiv.apply_symm_apply, hg, he]
  obtain ⟨c, hc⟩ := hconj
  obtain ⟨P, hP⟩ := id hd
  have hp : IsPairing c (r.comp (resG ℚ K Ω)) (θ.comp (resG ℚ K Ω)) (P * r c⁻¹) := fun s s' h => by
    have h' : resG ℚ K Ω s' = c * resG ℚ K Ω s * c⁻¹ := h
    have e0 : r c⁻¹ * r (resG ℚ K Ω s') = r (resG ℚ K Ω s) * r c⁻¹ := by rw [h', ← map_mul, ← map_mul]; congr 1; group
    have e' := congrArg Units.val e0
    have h1 := hP (resG ℚ K Ω s)
    simp only [Units.val_mul, MonoidHom.comp_apply] at e' ⊢
    rw [← Matrix.smul_mul, ← h1]
    simp only [Matrix.mul_assoc, e']
  refine _root_.UpperTheory.GalN.V.ofOne0_alt H third (_root_.UpperTheory.V.Z.Bc.across_alt H hS biQuad) K Ω hK l ι n hn r θ hθ hd i1 ?_
  exact (hS ℚ K L Ω s2 ⟨inferInstance, Or.inr ⟨hK, inferInstance⟩⟩ inferInstance inferInstance l ι n hn _ θ
    (hr.comp (continuous_restrictScalarsHom ℚ K Ω)) i2 hθ (Ws.auSign _) ⟨c, _, hc, hp⟩).2 (e ▸ haut)
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AuKap
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
theorem UpperTheory.V.Ws.isAlgChar_pushCh_link_kappa :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (ι : PadicAlgCl l ≃+* ℂ), Af.IsAlgChar ι (W.pushCh (algebraMap c'.O (PadicAlgCl l)) K.κ) := by
  intro hP Ω _ _ _ l _ c D T c' h K ι
  refine (_root_.UpperTheory.V.Af.algOfCyc_s hP T.L Ω l ι).1 _ (auCont c' K.κ K.κ_cont) fun w hw => ?_
  obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
  have hl : A.valuation (l : Ω) < 1 := by
    have h1 := (hA ((l : ℕ) : 𝓞 T.L)).2 hw
    have e : algebraMap T.L Ω (((l : ℕ) : 𝓞 T.L) : T.L) = (l : Ω) := by simp
    rwa [e] at h1
  obtain ⟨a, b, k, hk, -, H⟩ := K.cyc A hl
  refine ⟨A, hA, a, k, hk, fun s hs => ?_⟩
  rw [← (auChi T.L Ω c').1]
  have h2 := congrArg (Units.map (algebraMap c'.O (PadicAlgCl l)).toMonoidHom) (H s hs).1
  rw [map_pow, map_mul, map_zpow, map_one] at h2
  exact h2
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
open UpperTheory.V.Z.Win in
theorem UpperTheory.V.Z.Win.Dn.pmDown_alt :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (ι : PadicAlgCl l ≃+* ℂ) (y : X.A →ₐ[c'.O] PadicAlgCl l),
        T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l)) →
        ∀ r : G ℚ Ω →* M4 (PadicAlgCl l), r.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r → Continuous r → D.Mult r →
          Irr (r.comp T.L.fixingSubgroup.subtype) → _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (Af.tw (r.comp (resQ T.L)).toHomUnits (W.pushCh (algebraMap c'.O (PadicAlgCl l)) K.κ)) → _root_.UpperTheory.V.Aut.IsAut4Alt ι r := by
  intro U Ω _ _ _ l _ c D T hF _ c' h K X ι y hW r hr hc hm hi h1
  have hG : D.Good := hF.2.elim (fun a => a.1.1) (fun a => a.1.1)
  obtain ⟨hi1, -⟩ := auIrr _ (r.comp (resQ T.L)) hi fun g =>
    ⟨IntermediateField.fixingSubgroupEquiv T.L g, rfl⟩
  have h2 := (_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida U.pr T.L Ω l ι 4 _).2.2 h1
  have hκ := _root_.UpperTheory.V.Ws.isAlgChar_pushCh_link_kappa U.pr D T c' h K ι
  have hN := _root_.UpperTheory.GalN.V.csdN'_alt U.pr.toClassicalTheorems (by norm_num) h1
  have hκc : Continuous (W.pushCh (algebraMap c'.O (PadicAlgCl l)) K.κ) := hκ.choose_spec.1
  have hcr : Continuous r.toHomUnits := Units.continuous_iff.2 ⟨hc, hc.comp continuous_inv⟩
  have hW3 := _root_.UpperTheory.V.Z.Win.Dn.twist'_alt U.pr.toClassicalTheorems ((_root_.UpperTheory.V.Af.algOfCyc_s U.pr T.L Ω l ι).2.1 _ _ hκ hκ).2 hκc.inv
    (hN.2 (Af.Bc.irrBasic.2 _ _ _ _ _ (hcr.comp (Af.continuous_restrictScalarsHom ℚ T.L Ω)) hκc))
  have h3 := _root_.UpperTheory.V.Af.twist_invariance_automorphic U.pr T.L Ω l ι 4 _ _ h2 ((_root_.UpperTheory.V.Af.algOfCyc_s U.pr T.L Ω l ι).2.1 _ _ hκ hκ).2
  have h4 : Af.tw (Af.tw (r.comp (resQ T.L)).toHomUnits (W.pushCh (algebraMap c'.O (PadicAlgCl l)) K.κ))
      (W.pushCh (algebraMap c'.O (PadicAlgCl l)) K.κ)⁻¹ = r.toHomUnits.comp (Af.resG ℚ T.L Ω) := by
    ext g : 2
    rw [Af.tw_val, Af.tw_val, smul_smul, MonoidHom.inv_apply, Units.inv_mul, one_smul]
    rfl
  rw [h4] at h3 hW3
  obtain ⟨hgal, hsol⟩ := auGal D T
  obtain ⟨P, hP⟩ := auPair r (W.pushCh (algebraMap c.O (PadicAlgCl l)) D.th) hm 1
  have h0 := _root_.UpperTheory.GalN.V.isAutomorphicOverImagQuad_of_restriction_aut_irr U.pr (Z.Bc.solC_of_solDescent (_root_.UpperTheory.V.Af.solvable_descent_of_printed_hida U.pr)) Ω T.K T.L (T.hL ▸ le_sup_right) T.degK hgal hsol l ι 4
    (by norm_num) r.toHomUnits (W.pushCh (algebraMap c.O (PadicAlgCl l)) D.th)
    (Units.continuous_iff.2 ⟨hc, hc.comp continuous_inv⟩) (_root_.UpperTheory.V.Ws.isAlgChar_pushCh_th_of_good U.pr D hG ι)
    ⟨P, fun s => by simpa using hP s⟩ hi1 h3
  obtain ⟨hI, hFl, hU⟩ := UpperTheory.V.Keep.ptLaws D T hG hF.1 hF.1.locL c' h X y hW r hr
  have hle : T.K ≤ T.L := T.hL ▸ le_sup_right
  letI : Algebra T.K T.L := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower T.K T.L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℚ T.K T.L := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : IsGalois T.K T.L := IsGalois.tower_top_of_isGalois ℚ T.K T.L
  haveI : Group.IsSolvable (T.L ≃ₐ[ℚ] T.L) := hsol
  have s2 : Group.IsSolvable (T.L ≃ₐ[T.K] T.L) :=
    Group.isSolvable_of_isSolvable_injective (f := (AlgEquiv.restrictScalarsHom ℚ : (T.L ≃ₐ[T.K] T.L) →* (T.L ≃ₐ[ℚ] T.L)))
      (AlgEquiv.restrictScalars_injective ℚ)
  have e : (r.toHomUnits.comp (Af.resG ℚ T.K Ω)).comp (Af.resG T.K T.L Ω) = r.toHomUnits.comp (Af.resG ℚ T.L Ω) := rfl
  have i2 : Af.IsIrr ((r.toHomUnits.comp (Af.resG ℚ T.K Ω)).comp (Af.resG T.K T.L Ω)) := e ▸ hi1
  have i1 : Af.IsIrr (r.toHomUnits.comp (Af.resG ℚ T.K Ω)) := (Af.Bc.irrBasic.1 _ _ _ 4 _).1 _ i2
  have hcK : Continuous (r.toHomUnits.comp (Af.resG ℚ T.K Ω)) := hcr.comp (Af.continuous_restrictScalarsHom ℚ T.K Ω)
  obtain ⟨Q, hQ⟩ := auPair r (W.pushCh (algebraMap c.O (PadicAlgCl l)) D.th) hm D.cc
  have hpol : Af.Sol.Pol ι (r.toHomUnits.comp (Af.resG ℚ T.K Ω)) :=
    ⟨ℚ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, _, D.cc, Q, _root_.UpperTheory.V.Ws.isAlgChar_pushCh_th_of_good U.pr D hG ι, auSign _, hG.isCC, fun s s' h => by
        have h' : Af.resG ℚ T.K Ω s' = D.cc * Af.resG ℚ T.K Ω s * D.cc⁻¹ := h
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h']
        exact hQ _⟩
  have fl := (flagLaws ℚ Ω l 4 r.toHomUnits).2.2.2 T.K
  have hWK : _root_.UpperTheory.V.Z.Win.WitA ι (r.toHomUnits.comp (Af.resG ℚ T.K Ω)) :=
    _root_.UpperTheory.V.Z.Win.Dn.down'_alt T.L U.pr s2 (by norm_num) hcK i2 hpol (h0 hcr T.K T.degK i1) (fl.2.1 hFl) (fl.1 hI) (fun w hw _ => hU w hw) (e ▸ hW3)
  exact _root_.UpperTheory.GalN.V.isAutQA_of_isAutomorphicOverImagQuad_of_witAQ h0 fun _ => _root_.UpperTheory.V.Z.Win.Dn.across'_alt U.pr T.K Ω T.degK (by norm_num)
    (fun A hA g hg x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hF.1.split l hG.l_mem A hA hg) x x.2) hcr h0
    ⟨_, _root_.UpperTheory.V.Ws.isAlgChar_pushCh_th_of_good U.pr D hG ι, P, fun s => by simpa using hP s⟩ hI hFl i1 hWK
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LinkTwo
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk
theorem UpperTheory.Gal.projectedFormsSystemPart.exists_two_links_same_kappa_not_dvd_of_fit_deep :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∃ c₁ : Coef l, ∀ (c' : Coef l) (h : c.O ≤ c'.O), c₁.O ≤ c'.O → ∃ K K' : Link T c' h, K'.κ = K.κ ∧ ¬ K'.s.p ∣ K.s.p := by
  intro hU Ω _ _ _ l _ c D T hF hD
  have hC : Ctx2 D ∨ Ctx3 D := hF.2.imp And.left And.left
  have hG : D.Good := hC.elim And.left And.left
  have hO := hF.1
  have hPre : Nonempty (Pre T) := by
    obtain ⟨η, N, m, hN, hK, hm, hη, hcc, hun, hv⟩ := etaEx hC
    obtain ⟨κ₀, m', h1, h2, h3, h4, h5⟩ := Tw.kap0 Ω l hG.l_odd T.K T.degK
      (hO.split 2 hG.two_mem) η N m hN hK hm hη hcc (fun A => by
        by_cases hA : Raw.Away D.S A
        · exact Or.inl (hun A hA)
        · simp only [Raw.Away, not_forall, not_not] at hA
          obtain ⟨p, hp, hA⟩ := hA
          exact Or.inr (hO.split p hp A hA))
    obtain ⟨γ, g1, g2, g3, g4⟩ := halfEx hG
    have hl := hG.pl_over l Fact.out
    obtain ⟨t, β, c₁, b1, b2, b3, b4, b5, b6, b7, U, hU, b8⟩ :=
      Tw.bt0 Ω l hG.l_odd T.K T.degK (D.pl l) hl (hO.split l hG.l_mem _ hl)
    exact ⟨{ κ₀ := κ₀, γ := γ, β := β, t := t, κ₀_open := h1, κ₀_ord := ⟨m', h2, h3⟩,
             κ₀_conj := fun σ hσ s s' e hs => by rw [h4 σ hσ s s' e]; exact hv _ hs
             κ₀_unr := fun A hA => h5 A (hun A hA), γ_cont := g1, γ_red := g2, γ_sq := g3, γ_ker := g4,
             β_cont := b3, t_cont := b1, β_t := b2, β_red := fun s => (b4 s).2,
             conj := fun σ hσ s s' e => ⟨b6 σ hσ s s' e, b5 σ hσ s s' e⟩, t_unr := b7,
             cyc := betaCyc Ω l T.K T.degK (D.pl l) hl β b6 U hU b8 }⟩
  obtain ⟨P⟩ := hPre
  obtain ⟨k1, k2, k3⟩ := kapCont P
  obtain ⟨u1, u2, u3⟩ := kapUnr P hG
  let Q : QCh T :=
    { κ := P.κ, β := P.βL, t := P.tL, κ_cont := k1, β_cont := k2, t_cont := k3, β_t := fun _ hg => P.β_t hg,
      β_red := fun _ => P.β_red _, conj := kapConj P hD, t_unr := u1, unr := u2, tame := u3, mu := kapMu P hG,
      cyc := kapCyc P hG }
  obtain ⟨c₁, -, hL, hκ, hβ, -⟩ := Pr.coefEx l c T.L Ω Q.κ Q.β Q.κ_cont Q.β_cont
  refine ⟨c₁, fun c' h h₁ => ?_⟩
  obtain ⟨κ, a1, a2, -⟩ := liftO c' Q.κ Q.κ_cont fun g => h₁ (hκ g)
  obtain ⟨β, b1, b2, b3⟩ := liftO c' Q.β Q.β_cont fun g => h₁ (hβ g)
  obtain ⟨X⟩ := ochOf Q c' h κ β a1 b1 a2 b2 fun g => b3 g (Q.β_red g)
  have key : ∀ Y : SetD T, ∃ K : Link T c' h, K.κ = X.κ ∧ K.s = Y.s := fun Y => by
    obtain ⟨V, hV⟩ := hU.lev l T.L Ω Y.s Y.s.S Y.fin subset_rfl Y.s.split
    obtain ⟨r, r1, r2, r3⟩ := residEx X Y V hG hO hV
    obtain ⟨σ, hσ, hc⟩ := Y.cc
    obtain ⟨g₀, -, hg₀⟩ := Y.om0
    exact ⟨{ s := Y.s, V := V, hV := hV, noMu := noMu hG T.L g₀ hg₀, large := fun τ x => h₁ (hL τ x), e := Y.e, hA := Y.hA,
             κ := X.κ, β := X.β, t := X.t, κ_cont := X.κ_cont, β_cont := X.β_cont, t_cont := X.t_cont, β_t := X.β_t,
             β_red := X.β_red, conj := fun g g' e => X.conj σ hσ g g' (hc g g' e), t_unr := X.t_unr,
             unr := fun A v hA hv g hg =>
               ⟨X.unr A (Y.away A v hA hv) hg, (((barFacts hG).2.2 A (Y.away A v hA hv) _ ⟨hg.1, hg.2⟩)).2⟩
             tame := X.tame
             mu := fun v g hg => by
               obtain ⟨a, ha⟩ := (prFacts l T.L Ω Y.s V).2.2.2 v g hg
               exact X.mu g a ha
             cyc := X.cyc, r := r, chib := fun i g => by rw [r1]; rfl
             psib := r2, th := r3, v0 := v0ok X Y V hG r r1 }, rfl, rfl⟩
  obtain ⟨Y, -⟩ := UpperTheory.Gal.projectedFormsSystemPart.setAv T hG hO 1 one_ne_zero
  obtain ⟨Y', hY⟩ := UpperTheory.Gal.projectedFormsSystemPart.setAv T hG hO Y.s.p Y.s.p_prime.ne_zero
  obtain ⟨K, k1, k2⟩ := key Y
  obtain ⟨K', k3, k4⟩ := key Y'
  exact ⟨K, K', k3.trans k1.symm, by rw [k2, k4]; exact hY⟩
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PmAutO
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
theorem UpperTheory.Gal.projectedFormsSystemPart.pmAutO_alt :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (Λ : W.LamObj K.r) (ι : PadicAlgCl l ≃+* ℂ) (J₀ : Ideal B.B), B.ModularAlt ι J₀ Λ → ∀ φ : B.B →ₐ[c'.O] X.B, K.IsPhi X 0 B φ → ∀ J : Ideal X.B, J = J₀.map φ → ∀ y : X.A →ₐ[c'.O] PadicAlgCl l, (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
        T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l)) →
        ∀ r : G ℚ Ω →* M4 (PadicAlgCl l), r.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r → Continuous r → D.Mult r →
          Irr (r.comp T.L.fixingSubgroup.subtype) → _root_.UpperTheory.Gal.projectedFormsSystemPart.AutOffN K.s.v0 ι (Af.tw (r.comp (resQ T.L)).toHomUnits (W.pushCh (algebraMap c'.O (PadicAlgCl l)) K.κ)) := by
  intro U Ω _ _ _ l _ c D T hF _ c' h K X B Λ ι J₀ hM φ hφ J hJ y hy hW r hr hc hm hi
  have hG : D.Good := hF.2.elim (fun a => a.1.1) (fun a => a.1.1)
  let x : B.Pt := (y.comp (IsScalarTower.toAlgHom c'.O X.B X.A)).comp φ
  have hx : ∀ b, x b = y (algebraMap X.B X.A (φ b)) := fun _ => rfl
  have hJx : J₀ ≤ RingHom.ker x := fun b hb => hy _ (hJ ▸ Ideal.mem_map_of_mem φ hb)
  have hrL : (X.P.map (y : X.A →+* PadicAlgCl l)).r.comp (resLe T.F_le) = r.comp (resQ T.L) := by
    rw [← hr]; rfl
  have hcL : Continuous (r.comp (resQ T.L)) := hc.comp (Af.continuous_restrictScalarsHom _ _ _)
  have hanti : StrictAnti fun i => (D.wts4 i : ℤ) := by
    have := hG.two_le
    refine Fin.strictAnti_iff_succ_lt.2 fun i => ?_
    fin_cases i <;> simp [Raw.wts4] <;> omega
  obtain ⟨w, hw⟩ := auArith U.pr.toClassicalTheorems.litN.aut.art D T c' h K X B φ hφ y x hx
    (auPsiCont D T c' h K X B 0 φ hφ y x hx (hrL ▸ hcL)) _ hanti hW
  have hrep := auRep D T c' h K X B 0 φ hφ y x hx
  rw [hrL, pow_zero, mul_one] at hrep
  obtain ⟨hi1, hi2⟩ := auIrr _ (r.comp (resQ T.L)) hi fun g =>
    ⟨IntermediateField.fixingSubgroupEquiv T.L g, rfl⟩
  exact _root_.UpperTheory.Gal.projectedFormsSystemPart.end2oN K.v0 hM.end2 x w _ hJx hw hrep (hi2 _)
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ModularDeformationQuotientRegularAtPoint
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
attribute [local instance high] DivisionSemiring.to_moduleIsTorsionFree
theorem UpperTheory.V.Ws.modular_deformation_quotient_regular_at_point_alt :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (Λ : W.LamObj K.r) (ι : PadicAlgCl l ≃+* ℂ) (J₀ : Ideal B.B), B.ModularAlt ι J₀ Λ → ∀ φ : B.B →ₐ[c'.O] X.B, K.IsPhi X 0 B φ → ∀ J : Ideal X.B, J = J₀.map φ → ∀ (k : Type) [Field k] [Finite k] [Algebra c'.O k] (y : X.A →ₐ[c'.O] PowerSeries k),
        (∀ b ∈ maximalIdeal X.B, PowerSeries.constantCoeff (y (algebraMap X.B X.A b)) = 0) →
        (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
        (∀ v i j, i ≠ j → ∃ s ∈ T.U1 v, y (X.P.ψ v i s) ≠ y (X.P.ψ v j s)) →
        Irr (mapRep ((algebraMap (PowerSeries k) (FractionRing (PowerSeries k))).comp (y : X.A →+* PowerSeries k)) X.P.r) →
        X.LocZero J (y : X.A →+* PowerSeries k) := by
  intro _ Ω _ _ _ l _ c D T hF hD c' h K X B Λ ι J₀ hM φ hφ J hJ k _ _ _ y hy hyJ hU hI q hq hqy
  have hQ := P1.psPair D T c' h X k y hy
  haveI : IsLocalHom (algebraMap c'.O k) := ⟨fun a ha => by
    by_contra hn
    exact ha.ne_zero (hQ.loc a hn)⟩
  letI : Algebra (ResidueField c'.O) k := (ResidueField.lift (algebraMap c'.O k)).toAlgebra
  haveI : IsScalarTower c'.O (ResidueField c'.O) k := IsScalarTower.of_algebraMap_eq fun a => rfl
  obtain ⟨hfin, hchar, -⟩ := P1.coefRes c'
  obtain ⟨ρ, hρ, hρc⟩ := P1.rhoEx D T c' h K (PowerSeries k) _ (maximalIdeal _) (fun a ha => by
    rw [PowerSeries.algebraMap_apply, hQ.loc a ha, map_zero]; exact zero_mem _) hQ.pair hQ.cont
  obtain ⟨P, hP, hform⟩ := P1.formEx D T hF hD c' h K _ _ ρ hQ.pair hρ
  obtain ⟨ψ, hψ, hflag⟩ := P1.psiEx D T c' h K _ _ ρ hQ.pair hρ
  obtain ⟨hψr, hψc⟩ := P1.redPsi D T c' h K k _ hQ ψ hψ
  let x : W.Point K.r :=
    { K := k, ρ := ρ, cont := hρc, P := P, symm := hP, form := hform, red := P1.redDet D T c' h K k _ hQ ρ hρ
      ine := P1.ineTriv D T c' h K _ _ ρ hQ.pair hρ, ψ := ψ, ψ_red := hψr, flag := fun v => hflag _ _ v }
  obtain ⟨hne, hA⟩ := P1.condA D T hF hD c' h K _ _ ψ hψ (fun v i j hij => by
    obtain ⟨s, hs, hne⟩ := hU v i j hij
    have e := (sxPdMap (Φ := T.fr ∅) ((algebraMap c'.O X.A).comp (inc h)) (y : X.A →+* PowerSeries k) X.P).1
    exact ⟨s, hs, fun hh => hne ((e v i s).symm.trans (hh.trans (e v j s)))⟩)
  obtain ⟨n1, n2, n3⟩ := h4 l K.s.odd K.V.frame c'.O K.r x hne hψc hA
    (P1.irrL D T c' h K x _ hQ hρ hI) (P1.condC D T hF hD c' h K) (P1.condD D T hF hD c' h K)
  let f : B.B →ₐ[c'.O] x.A := (y.comp (IsScalarTower.toAlgHom c'.O X.B X.A)).comp φ
  have hf : B.IsPt x f := P1.mapsPt D T c' h K X B φ hφ _ y ρ ψ hρ hψ
  have key := hM.p1 x f ⟨n1, n2, n3, P1.n4V0 l _ _ 4 K.r K.v0 x⟩ hf
    (fun b hb => hyJ _ (hJ ▸ Ideal.mem_map_of_mem φ hb)) ⟨q.comap φ, hq.comap φ⟩ (fun b hb => hqy _ hb)
  rw [hJ]
  exact Ideal.map_le_iff_le_comap.2 key
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPmFin
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
section Abstract
variable {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
private theorem pf_const [IsDomain R] (h0 : ∀ a ∈ maximalIdeal O, algebraMap O R a = 0) {y : R} (hy : IsIntegral O y) :
    ∃ a, y = algebraMap O R a := by
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) y
  refine ⟨a, ?_⟩
  by_contra hne
  letI : Algebra (ResidueField O) R := (Ideal.Quotient.lift (maximalIdeal O) (algebraMap O R) h0).toAlgebra
  haveI : IsScalarTower O (ResidueField O) R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h1 : IsIntegral (ResidueField O) (y - algebraMap O R a) := (hy.sub isIntegral_algebraMap).tower_top
  exact ha (h1.isUnit (sub_ne_zero.2 hne))
private theorem pf_sect (h0 : ∀ a ∈ maximalIdeal O, algebraMap O R a = 0) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] :
    ∃ s : B →ₐ[O] R, (∀ b ∈ maximalIdeal B, s b = 0) ∧ ∀ (f : B →ₐ[O] R) (b : B), (∃ a, f b = algebraMap O R a) → f b = s b := by
  let j : ResidueField O →ₐ[O] R := Ideal.Quotient.liftₐ (maximalIdeal O) (Algebra.ofId O R) h0
  refine ⟨j.comp (res O B), fun b hb => ?_, ?_⟩
  · rw [AlgHom.comp_apply, (res_eq_zero_iff O B b).2 hb, map_zero]
  · rintro f b ⟨a, ha⟩
    rw [AlgHom.comp_apply, ← res_map f, ha, AlgHom.commutes, AlgHom.commutes]
private theorem pf_cont {Γ B : Type} [TopologicalSpace Γ] [CommRing B] [Algebra O B] [IsCO O B] (f : B →ₐ[O] R) {u : Γ → B}
    (hu : AdicCont (maximalIdeal B) u) : AdicCont (maximalIdeal R) fun g => f (u g) := fun N => by
  have hle : maximalIdeal B ^ N ≤ (maximalIdeal R ^ N).comap (f : B →+* R) := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    show f y ∈ maximalIdeal R
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hy
  exact (hu N).comp (Ideal.quotientMap _ (f : B →+* R) hle)
private theorem pf_lam {l : ℕ} [Fact l.Prime] {F : W.GFrame l} [Algebra ℤ_[l] O] {n : ℕ} {r : W.Resid F O n} (Λ : W.LamObj r)
    (h0 : ∀ a ∈ maximalIdeal O, algebraMap O R a = 0) (f : Λ.Λ →ₐ[O] R)
    (hf : ∀ v i g, ∃ a, f (Λ.κ v i g) = algebraMap O R a) (x : Λ.Λ) : ∃ a, f x = algebraMap O R a := by
  obtain ⟨s, hs, hsf⟩ := pf_sect h0 Λ.Λ
  have hi : W.IsInert r fun v i => W.pushCh (f : Λ.Λ →+* R) (Λ.κ v i) := fun v i => by
    obtain ⟨ψ, hψ, he⟩ := Λ.inert v i
    refine ⟨W.pushCh (f : Λ.Λ →+* R) ψ, ⟨pf_cont f hψ.cont, fun g => (res_map f _).trans (hψ.red g), fun g => ?_⟩, ?_⟩
    · show f (ψ g) = _
      rw [hψ.mu g, f.commutes]
    · exact congrArg (W.pushCh (f : Λ.Λ →+* R)) he
  have he : f = s := (Λ.univ R _ hi).unique (fun _ _ => rfl) fun v i =>
    MonoidHom.ext fun g => Units.ext (hsf f _ (hf v i g)).symm
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
  have h1 := hs _ ha
  rw [map_sub, AlgHom.commutes, sub_eq_zero] at h1
  exact ⟨a, he ▸ h1⟩
private theorem pf_int {Λ B : Type} [CommRing Λ] [CommRing B] [Algebra O Λ] [Algebra O B] (t : Λ →ₐ[O] B) (J : Ideal B)
    (hfin : ((Ideal.Quotient.mk J).comp (t : Λ →+* B)).Finite) (f : B →ₐ[O] R) (hJ : ∀ b ∈ J, f b = 0)
    (hc : ∀ x, ∃ a, f (t x) = algebraMap O R a) (b : B) : IsIntegral O (f b) := by
  obtain ⟨p, hp, hb⟩ := hfin.to_isIntegral (Ideal.Quotient.mk J b)
  have h1 := congrArg (Ideal.Quotient.lift J (f : B →+* R) hJ) hb
  rw [hom_eval₂, map_zero] at h1
  have hl : p.map ((f.comp t : Λ →ₐ[O] R) : Λ →+* R) ∈ lifts (algebraMap O R) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    obtain ⟨a, ha⟩ := hc (p.coeff n)
    exact ⟨a, by rw [coeff_map]; exact ha.symm⟩
  obtain ⟨q, hq, -, hm⟩ := lifts_and_natDegree_eq_and_monic hl (hp.map _)
  refine ⟨q, hm, ?_⟩
  rw [← eval_map, hq, eval_map]
  exact h1
variable {O₀ Γ : Type} [CommRing O₀] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O₀ Γ} {a : O₀ →+* O} (X : Space Φ a)
private theorem pf_sq (f : X.B →ₐ[O] R) (g : Γ) (hg : ∀ n, IsIntegral O (f ((X.cp (g ^ 2)).coeff n))) (n : ℕ) :
    IsIntegral O (f ((X.cp g).coeff n)) := by
  let S₀ : Subring X.B := (integralClosure O R).toSubring.comap (f : X.B →+* R)
  let S : Subring X.A := S₀.map (algebraMap X.B X.A)
  have h1 := AlgebraTools.charpolyPowInt X.A (Fin 4) S (X.P.r g) 2 two_pos (fun i => by
    rw [← map_pow, ← X.cp_map, coeff_map]
    exact ⟨_, hg i, rfl⟩) n
  rw [← X.cp_map, coeff_map] at h1
  obtain ⟨p, hp, hb⟩ := h1
  have hl : p.map S.subtype ∈ lifts ((algebraMap X.B X.A).comp S₀.subtype) := by
    rw [lifts_iff_coeff_lifts]
    intro m
    obtain ⟨y, hy, he⟩ := (p.coeff m).2
    exact ⟨⟨y, hy⟩, by rw [coeff_map]; exact he⟩
  obtain ⟨q, hq, -, hm⟩ := lifts_and_natDegree_eq_and_monic hl (hp.map _)
  have h2 : q.eval₂ S₀.subtype ((X.cp g).coeff n) = 0 := by
    apply X.inj
    rw [hom_eval₂, map_zero, ← eval_map, hq, eval_map]
    exact hb
  let j : S₀ →+* integralClosure O R := ((f : X.B →+* R).comp S₀.subtype).codRestrict _ fun y => y.2
  have h3 : IsIntegral (integralClosure O R) (f ((X.cp g).coeff n)) := by
    refine ⟨q.map j, hm.map j, ?_⟩
    have h4 := congrArg (f : X.B →+* R) h2
    rw [hom_eval₂, map_zero] at h4
    rw [eval₂_map]
    exact h4
  exact isIntegral_trans _ h3
private theorem pf_gen [IsDomain R] (h0 : ∀ a ∈ maximalIdeal O, algebraMap O R a = 0) (f : X.B →ₐ[O] R)
    (h1 : ∀ g n, IsIntegral O (f ((X.cp g).coeff n))) (h2 : ∀ v i, ∀ s ∈ Φ.Gv v, IsIntegral O (f (X.ψ v i s))) :
    ∀ b ∈ maximalIdeal X.B, f b = 0 := by
  obtain ⟨s, hs, hsf⟩ := pf_sect h0 X.B
  rw [X.genB R f s (fun g n => hsf f _ (pf_const h0 (h1 g n))) fun v i g hg => hsf f _ (pf_const h0 (h2 v i g hg))]
  exact hs
private theorem pf_unit {u : Oˣ} {y : R} (h : IsIntegral O (algebraMap O R u * y)) : IsIntegral O y := by
  have h1 := (isIntegral_algebraMap (R := O) (A := R) (x := (u⁻¹ : Oˣ))).mul h
  rwa [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul] at h1
end Abstract
section Galois
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} (T : Tower D)
private theorem pf_lift {g : G T.F Ω} (hg : resQ T.F g ∈ T.K.fixingSubgroup) : ∃ g' : G T.L Ω, resLe T.F_le g' = g := by
  have h1 : resQ T.F g ∈ T.F.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    exact fun x hx => g.commutes ⟨x, hx⟩
  have h2 : resQ T.F g ∈ T.L.fixingSubgroup := by
    rw [T.hL, IntermediateField.fixingSubgroup_sup]
    exact ⟨h1, hg⟩
  rw [IntermediateField.mem_fixingSubgroup_iff] at h2
  exact ⟨{ g.toRingEquiv with commutes' := fun x => h2 x.1 x.2 }, AlgEquiv.ext fun _ => rfl⟩
private theorem pf_sqK (g : G ℚ Ω) : g ^ 2 ∈ T.K.fixingSubgroup := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : IsGalois ℚ Ω := inferInstance
  have hi : T.K.fixingSubgroup.index = 2 := by
    rw [← T.degK]
    exact (IntermediateField.finrank_eq_fixingSubgroup_index Ω T.K).symm
  exact Subgroup.sq_mem_of_index_two hi g
end Galois
theorem UpperTheory.V.Ws.exists_pow_maximalIdeal_le_of_modular_phi :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (Λ : W.LamObj K.r) (ι : PadicAlgCl l ≃+* ℂ) (J₀ : Ideal B.B), B.ModularAlt ι J₀ Λ → ∀ φ : B.B →ₐ[c'.O] X.B, K.IsPhi X 0 B φ → ∀ J : Ideal X.B, J = J₀.map φ → ∃ n : ℕ, maximalIdeal X.B ^ n ≤ J ⊔ (maximalIdeal c'.O).map (algebraMap c'.O X.B) ⊔
        Ideal.span {b | ∃ v i, ∃ s ∈ Ine (F := T.F) (T.pl v), b = X.ψ v i s - 1} := by
  intro _ Ω _ _ _ l _ c D T hT _ c' h K X B Λ ι J₀ hM φ hφ J hJ
  refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (IsNoetherian.noetherian _)
  rw [Ideal.radical_eq_sInf]
  refine le_sInf ?_
  rintro q ⟨hq, hp⟩
  have hl : l ∈ D.S := hT.2.elim (fun x => x.1.1.l_mem) fun x => x.1.1.l_mem
  let π : X.B →ₐ[c'.O] X.B ⧸ q := Ideal.Quotient.mkₐ c'.O q
  haveI : IsCO c'.O (X.B ⧸ q) := co_quot c'.O X.B _ π Ideal.Quotient.mk_surjective
  have hπ : ∀ b, π b = 0 ↔ b ∈ q := fun b => Ideal.Quotient.eq_zero_iff_mem
  have h0 : ∀ a ∈ maximalIdeal c'.O, algebraMap c'.O (X.B ⧸ q) a = 0 := fun a ha => by
    rw [← π.commutes, hπ]
    exact hq (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ ha)))
  have hone : ∀ v i, ∀ s ∈ Ine (F := T.F) (T.pl v), π (X.ψ v i s) = 1 := fun v i s hs => by
    rw [← sub_eq_zero, ← map_one π, ← map_sub, hπ]
    exact hq (Ideal.mem_sup_right (Ideal.subset_span ⟨v, i, s, hs, rfl⟩))
  have hΛ := pf_lam Λ h0 ((π.comp φ).comp (Λ.toPair B.u)) fun v i g => by
    have h1 : Λ.toPair B.u (Λ.κ v i g) = B.u.ψ v i g :=
      congrArg Units.val (DFunLike.congr_fun (W.LamObj.toPair_spec K.r Λ B.u v i) g)
    refine ⟨K.κ g.1.1 * K.β g.1.1 ^ 0, ?_⟩
    have h2 : resLe T.F_le g.1.1 ∈ Ine (F := T.F) (T.pl (K.e v)) :=
      (congrArg (fun A => resLe T.F_le g.1.1 ∈ Ine (F := T.F) A) (K.hA v)).mp g.2
    rw [AlgHom.comp_apply, AlgHom.comp_apply, h1, hφ.2 v i g.1, map_mul, π.commutes, hone _ _ _ h2, mul_one]
  have hB := pf_int (Λ.toPair B.u) J₀ hM.ring.fin (π.comp φ) (fun b hb => by
    rw [AlgHom.comp_apply, hπ]
    exact hq (Ideal.mem_sup_left (Ideal.mem_sup_left (hJ ▸ Ideal.mem_map_of_mem _ hb)))) hΛ
  intro b hb
  rw [← hπ]
  refine pf_gen X h0 π (fun g => pf_sq X π g fun n => ?_) (fun v i s hs => ?_) b hb
  · obtain ⟨g', hg'⟩ := pf_lift T (g := g ^ 2) (by rw [map_pow]; exact pf_sqK T _)
    have h1 := hB ((B.u.D.chi (MonoidAlgebra.single (K.V.pr g') 1)).coeff n)
    have h2 := congrArg (fun p => p.coeff n) (hφ.1 g')
    simp only [coeff_map, coeff_scaleRoots, hg'] at h2
    rw [AlgHom.comp_apply] at h1
    erw [h2] at h1
    rw [map_mul, map_pow, π.commutes, mul_comm, ← map_pow, ← Units.val_pow_eq_pow_val, ← Units.val_mul,
      ← Units.val_pow_eq_pow_val] at h1
    exact pf_unit h1
  · obtain ⟨v, rfl⟩ := K.e.surjective v
    obtain ⟨g', rfl⟩ := pf_lift T (g := s) (hT.1.split l hl _ (T.ovl (K.e v)) hs)
    have hg : g' ∈ Dec (F := T.L) (K.s.A v) := by
      rw [K.hA]
      exact hs
    have h1 := hB (B.u.ψ v i ⟨g', hg⟩)
    rw [AlgHom.comp_apply, hφ.2 v i ⟨g', hg⟩, map_mul, π.commutes, ← Units.val_pow_eq_pow_val, ← Units.val_mul] at h1
    exact pf_unit h1
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
theorem UpperTheory.Gal.projectedFormsSystemPart.promodular_existence_of_local_zero (U : _root_.UpperTheory.V.Ws.UnramifiedInputs)
    (hS : ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (Λ : W.LamObj K.r) (ι : PadicAlgCl l ≃+* ℂ) (J₀ : Ideal B.B), B.ModularAlt ι J₀ Λ → ∀ φ : B.B →ₐ[c'.O] X.B, K.IsPhi X 0 B φ → ∀ J : Ideal X.B, J = J₀.map φ → ∀ y : X.A →ₐ[c'.O] PadicAlgCl l, T.IsSeedAlt ι (X.P.map (y : X.A →+* PadicAlgCl l)) →
      X.LocZero J (y : X.A →+* PadicAlgCl l)) : _root_.UpperTheory.V.Ws.PMExAlt := by
  intro Ω _ _ _ l _ c D T hF hD ι
  obtain ⟨c₁, hc₁⟩ := _root_.UpperTheory.Gal.projectedFormsSystemPart.exists_two_links_same_kappa_not_dvd_of_fit_deep U D T hF hD
  refine ⟨c₁, fun c' h h₁ X => ?_⟩
  obtain ⟨K, K', hκ, hp⟩ := hc₁ c' h h₁
  obtain ⟨⟨B, -⟩, hφ⟩ := _root_.UpperTheory.V.Ws.exists_phi_universal_ordinary_det_ring_of_link U D T hF hD c' h K X 0
  obtain ⟨φ, hφ⟩ := hφ B
  obtain ⟨Λ, -⟩ := U.lam l T.L Ω K.s K.V c' 4 K.r
  obtain ⟨J₀, hJ⟩ := U.modU l T.L Ω K.s K.V K.hV K.noMu c' K.large 4 (by norm_num) K.r B Λ ι
  obtain ⟨⟨B', -⟩, hφ'⟩ := _root_.UpperTheory.V.Ws.exists_phi_universal_ordinary_det_ring_of_link U D T hF hD c' h K' X 0
  obtain ⟨φ', hφ'⟩ := hφ' B'
  obtain ⟨Λ', -⟩ := U.lam l T.L Ω K'.s K'.V c' 4 K'.r
  obtain ⟨J₀', hJ'⟩ := U.modU l T.L Ω K'.s K'.V K'.hV K'.noMu c' K'.large 4 (by norm_num) K'.r B' Λ' ι
  have hl : ∀ {b}, b ∈ J₀.map φ → b ∈ J₀.map φ ⊔ J₀'.map φ' := fun hb => Ideal.mem_sup_left hb
  have hr : ∀ {b}, b ∈ J₀'.map φ' → b ∈ J₀.map φ ⊔ J₀'.map φ' := fun hb => Ideal.mem_sup_right hb
  refine ⟨J₀.map φ ⊔ J₀'.map φ', ?_, fun k _ _ _ y y1 y2 y3 y4 q hq hy => sup_le ?_ ?_, fun y y1 q hq hy => sup_le ?_ ?_,
    fun y y1 => _root_.UpperTheory.V.Ws.pmPur_w_alt U D T hF hD c' h K X B Λ ι J₀ hJ φ hφ _ rfl y fun b hb => y1 b (hl hb),
    fun y y1 y2 r r1 r2 r3 r4 => ?_⟩
  · obtain ⟨n, hn⟩ := _root_.UpperTheory.V.Ws.exists_pow_maximalIdeal_le_of_modular_phi U D T hF hD c' h K X B Λ ι J₀ hJ φ hφ _ rfl
    exact ⟨n, hn.trans (sup_le_sup_right (sup_le_sup_right le_sup_left _) _)⟩
  · exact _root_.UpperTheory.V.Ws.modular_deformation_quotient_regular_at_point_alt U D T hF hD c' h K X B Λ ι J₀ hJ φ hφ _ rfl k y y1 (fun b hb => y2 b (hl hb)) y3 y4 q hq hy
  · exact _root_.UpperTheory.V.Ws.modular_deformation_quotient_regular_at_point_alt U D T hF hD c' h K' X B' Λ' ι J₀' hJ' φ' hφ' _ rfl k y y1 (fun b hb => y2 b (hr hb)) y3 y4 q hq hy
  · exact hS D T hF hD c' h K X B Λ ι J₀ hJ φ hφ _ rfl y y1 q hq hy
  · exact hS D T hF hD c' h K' X B' Λ' ι J₀' hJ' φ' hφ' _ rfl y y1 q hq hy
  · have a := _root_.UpperTheory.Gal.projectedFormsSystemPart.pmAutO_alt U D T hF hD c' h K X B Λ ι J₀ hJ φ hφ _ rfl y (fun b hb => y1 b (hl hb)) y2 r r1 r2 r3 r4
    have b := _root_.UpperTheory.Gal.projectedFormsSystemPart.pmAutO_alt U D T hF hD c' h K' X B' Λ' ι J₀' hJ' φ' hφ' _ rfl y (fun b hb => y1 b (hr hb)) y2 r r1 r2 r3 r4
    rw [hκ] at b
    exact _root_.UpperTheory.V.Z.Win.Dn.pmDown_alt U D T hF hD c' h K X ι y y2 r r1 r2 r3 r4
      (_root_.UpperTheory.Gal.projectedFormsSystemPart.glueN (by norm_num) (UpperTheory.Gal.projectedFormsSystemPart.v0_ne hp) a b)
end
