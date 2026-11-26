module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.AutP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.PurityTempered.AlgPowConst
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.RealExistenceFromPublished
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExtReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.UntwistS
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.LevelFRes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.UnlGap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.UsedOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BlochKatoNonpositiveWeight
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LevBasis

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.FreePU
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th
open scoped Pointwise

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.UnlRes
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section
open UpperTheory.V.Af.Bc
open scoped Pointwise

private theorem move {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K]
    [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω]
    (w : HeightOneSpectrum (𝓞 K)) {A : ValuationSubring Ω} (hA : IsPlaceOver A (w.under (𝓞 F))) :
    ∃ (B : ValuationSubring Ω) (g : G F Ω), IsPlaceOver B w ∧
      (∀ s ∈ Dec (F := F) A, g⁻¹ * s * g ∈ Dec (F := F) B) ∧
      (∀ s ∈ Dec (F := K) B, g * res F Ω K s * g⁻¹ ∈ Dec (F := F) A) ∧
      ∀ s ∈ Ine (F := K) B, g * res F Ω K s * g⁻¹ ∈ Ine (F := F) A := by
  obtain ⟨B, hB⟩ := (exists_isPlaceOver Ω w : ∃ B : ValuationSubring Ω, IsPlaceOver B w)
  have hB' : IsPlaceOver B (w.under (𝓞 F)) := fun x => by
    rw [IsScalarTower.algebraMap_apply F K Ω]
    exact hB (algebraMap (𝓞 F) (𝓞 K) x)
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hB' hA
  have hm : ∀ x, x ∈ B ↔ g x ∈ g • B := fun x => ValuationSubring.smul_mem_pointwise_smul_iff.symm
  have hv : ∀ y, (g • B).valuation (g y) < 1 ↔ B.valuation y < 1 := fun y => by
    rw [valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, ← hm, ← hm, map_eq_zero_iff _ g.injective]
  have hD : ∀ s ∈ Dec (F := K) B, g * res F Ω K s * g⁻¹ ∈ Dec (F := F) (g • B) := fun s hs => by
    have h1 : res F Ω K s • B = B := hs
    show (g * res F Ω K s * g⁻¹) • g • B = g • B
    rw [mul_smul, mul_smul, inv_smul_smul, h1]
  have hD' : ∀ s ∈ Dec (F := F) (g • B), g⁻¹ * s * g ∈ Dec (F := F) B := fun s hs => by
    have h1 : s • g • B = g • B := hs
    show (g⁻¹ * s * g) • B = B
    rw [mul_smul, mul_smul, h1, inv_smul_smul]
  refine ⟨B, g, hB, hD', hD, fun s hs => ⟨hD s hs.1, fun x hx => ?_⟩⟩
  obtain ⟨y, rfl⟩ := g.surjective x
  have e : (g * res F Ω K s * g⁻¹) (g y) = g (s y) := by
    show g (s (g.symm (g y))) = _
    rw [AlgEquiv.symm_apply_apply]
  rw [e, ← map_sub, hv]
  exact hs.2 y ((B.valuation_le_one_iff _).2 ((hm y).2 (((g • B).valuation_le_one_iff _).1 hx)))

private theorem nat_mem_under {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (l : ℕ)
    (w : HeightOneSpectrum (𝓞 L)) : ((l : ℕ) : 𝓞 F) ∈ (w.under (𝓞 F)).asIdeal ↔ ((l : ℕ) : 𝓞 L) ∈ w.asIdeal := by
  change algebraMap (𝓞 F) (𝓞 L) _ ∈ w.asIdeal ↔ _
  rw [map_natCast]

private theorem char_conj {Γ C : Type} [Group Γ] [CommGroup C] (χ : Γ →* C) (g s : Γ) : χ (g * s * g⁻¹) = χ s := by
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]

private theorem rep_conj {Γ C : Type} [Group Γ] [Group C] (r : Γ →* C) (P : C) (g s : Γ) :
    P * r g * r s * (P * r g)⁻¹ = P * r (g * s * g⁻¹) * P⁻¹ := by
  rw [map_mul, map_mul, map_inv]
  group

private theorem flag_move {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K]
    [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω]
    {l : ℕ} [Fact l.Prime] {n M : ℕ} {m : Fin n → ℤ} {r : G F Ω →* GL (Fin n) (Qbar l)}
    (w : HeightOneSpectrum (𝓞 K)) {A : ValuationSubring Ω} (hA : IsPlaceOver A (w.under (𝓞 F)))
    {κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ} (hκ : FlagAt M m r A κ) :
    ∃ (B : ValuationSubring Ω) (d : ↥(Dec (F := K) B) →* ↥(Dec (F := F) A)), IsPlaceOver B w ∧
      FlagAt M m (r.comp (res F Ω K)) B (fun i => (κ i).comp d) ∧
      (∀ s, cycBar F Ω l (d s) = cycBar K Ω l s) ∧
      (Dec (F := F) B ≤ (res F Ω K).range → Function.Surjective d) := by
  obtain ⟨χ, hχ, ⟨P, hP⟩, hκ⟩ := hκ
  obtain ⟨B, g, hB, hD', hD, hI⟩ := move w hA
  let d : ↥(Dec (F := K) B) →* ↥(Dec (F := F) A) :=
    (((MulAut.conj g).toMonoidHom.comp (res F Ω K)).comp (Dec (F := K) B).subtype).codRestrict _
      fun s => hD s s.2
  have hd : ∀ s, (d s : G F Ω) = g * res F Ω K s * g⁻¹ := fun _ => rfl
  refine ⟨B, d, hB, ⟨fun i => (χ i).comp (res F Ω K), fun i s hs => hχ i _ hs,
    ⟨P * r g, fun s => ?_⟩, fun i s hs => ?_⟩, fun s => ?_, fun H s => ?_⟩
  · rw [MonoidHom.comp_apply, rep_conj]
    exact hP (d s)
  · have h := hκ i (d s) (hI s hs)
    rw [hd, char_conj, char_conj] at h
    exact h
  · rw [hd, char_conj]
    rfl
  · obtain ⟨t, ht⟩ := H (hD' s s.2)
    have htD : t ∈ Dec (F := K) B := by
      have h1 : res F Ω K t • B = B := by
        rw [ht]
        exact hD' s s.2
      exact h1
    refine ⟨⟨t, htD⟩, Subtype.ext ?_⟩
    rw [hd]
    show g * res F Ω K t * g⁻¹ = s
    rw [ht]
    group

end

theorem UpperTheory.V.Th.unlRes :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (n M : ℕ) (m : Fin n → ℤ) (r : G ℚ Ω →* GL (Fin n) (Qbar l)), 1 ≤ M → ((∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Dec (F := ℚ) A ≤ (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω).range) → Unl l M m r → Unl l M m (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω))) ∧ ((∀ i j, m i ≠ m j + 1) → Af.Level l M m r → Unl l M m (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω))) := by
  intro K Ω _ _ _ _ _ _ _ l _ n M m r hM
  refine ⟨fun hdec H w hw => ?_, fun hm H w hw => ?_⟩
  · obtain ⟨A, hA, κ, hκ, hu⟩ := H (w.under (𝓞 ℚ)) ((nat_mem_under l w).2 hw)
    obtain ⟨B, d, hB, hF, hc, hs⟩ := flag_move w hA hκ
    have hv : B.valuation (l : Ω) < 1 := by
      simpa only [map_natCast] using (hB (l : 𝓞 K)).2 hw
    refine ⟨B, hB, _, hF, fun i j e => hu i j (MonoidHom.ext fun s => ?_)⟩
    obtain ⟨t, rfl⟩ := hs (hdec B hv) s
    have h1 := DFunLike.congr_fun e t
    change κ i (d t) = κ j (d t) * cycBar K Ω l t at h1
    change κ i (d t) = κ j (d t) * cycBar ℚ Ω l (d t)
    rw [hc, h1]
  · obtain ⟨A, hA, κ, hκ⟩ := (Lev.LevelF.of_level H).above (w.under (𝓞 ℚ)) ((nat_mem_under l w).2 hw)
    obtain ⟨B, d, hB, hF, -, -⟩ := flag_move w hA hκ
    exact ⟨B, hB, _, hF, Lev.unlGap K Ω l n M hM m _ w hw B hB _ hF hm⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.UnlPlace
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Th

private theorem unl_place {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {p : ℕ} (hp : p.Prime)
    {A : ValuationSubring Ω} (hA : A.valuation (p : Ω) < 1) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    IsPlaceOver A w := by
  intro x
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, (k : 𝓞 ℚ) = x :=
    ⟨Rat.ringOfIntegersEquiv x, by
      rw [← map_intCast Rat.ringOfIntegersEquiv.symm, Int.cast_id, RingEquiv.symm_apply_apply]⟩
  have hc : ∀ k : ℤ, algebraMap ℚ Ω ((k : 𝓞 ℚ) : ℚ) = (k : Ω) := fun k => by simp
  have hv1 : ∀ k : ℤ, A.valuation (k : Ω) ≤ 1 := by
    intro k
    have := A.valuation_le_one (k : A)
    simpa using this
  have hA' : A.valuation ((p : ℤ) : Ω) < 1 := by simpa using hA
  have hw' : ((p : ℤ) : 𝓞 ℚ) ∈ w.asIdeal := by simpa using hw
  rw [hc]
  by_cases hk : (p : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    constructor
    · intro _
      rw [Int.cast_mul]
      exact w.asIdeal.mul_mem_right _ hw'
    · intro _
      rw [Int.cast_mul, map_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left zero_le' hA' (hv1 m)
  · have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    obtain ⟨a, b, hab⟩ := (hpr.irreducible.coprime_iff_not_dvd).mpr hk
    constructor
    · intro hlt
      exfalso
      have h1 : A.valuation ((a : Ω) * ((p : ℤ) : Ω)) < 1 := by
        rw [map_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hv1 a) zero_le' hA'
      have h2 : A.valuation ((b : Ω) * (k : Ω)) < 1 := by
        rw [map_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hv1 b) zero_le' hlt
      have h3 := A.valuation.map_add_lt h1 h2
      rw [← Int.cast_mul, ← Int.cast_mul, ← Int.cast_add, hab, Int.cast_one, map_one] at h3
      exact lt_irrefl _ h3
    · intro hmem
      exfalso
      apply w.isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have : ((a * p + b * k : ℤ) : 𝓞 ℚ) ∈ w.asIdeal := by
        rw [Int.cast_add, Int.cast_mul, Int.cast_mul]
        exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hw') (w.asIdeal.mul_mem_left _ hmem)
      rwa [hab, Int.cast_one] at this

theorem UpperTheory.V.Th.spUnl :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ N : ℕ, 1 ≤ N → Af.KillsMu N D.ψ → Af.KillsMu N D.ξ → Af.KillsMu N D.om → ∀ r, D.EPt r → Unl l N ![(D.e : ℤ) + 1, D.e, 1, 0] r.toHomUnits := by
  intro Ω _ _ _ l _ c D hG N hN hψ hξ hom r hr
  obtain ⟨R, iR, iA, iC, ρ, y, hpt, rfl⟩ := hr
  let r' : ↥(D.Gp l) →* GradeZeroInterpolatingElement.M4 (PadicAlgCl l) := (mapRep (↑y) ρ.hom).comp (D.Gp l).subtype
  have hon : Loc.PtOn D D.condL r' := ⟨R, iR, iA, iC, D.loc ρ l, y, hpt.atL, rfl⟩
  obtain ⟨h, κ, hfl, hine, -, -, -, hdist⟩ := Loc.spPtL D hG r' hon
  have hcyc : ∀ g : G ℚ Ω, ((cycBar ℚ Ω l g : (Qbar l)ˣ) : Qbar l) = (((chiO ℚ Ω l c.O g : (↥c.O)ˣ) : ↥c.O) : PadicAlgCl l) := by
    intro g
    show algebraMap ℚ_[l] (PadicAlgCl l) ((cycZ ℚ Ω l g : ℤ_[l]) : ℚ_[l]) = algebraMap ℤ_[l] (PadicAlgCl l) (cycZ ℚ Ω l g : ℤ_[l])
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
    rfl
  have hinv : ∀ u : (↥c.O)ˣ, (((u⁻¹ : (↥c.O)ˣ) : ↥c.O) : PadicAlgCl l) = ((u : ↥c.O) : PadicAlgCl l)⁻¹ := by
    intro u
    apply eq_inv_of_mul_eq_one_left
    rw [← Subalgebra.coe_mul, Units.inv_mul]
    rfl
  have hne : ∀ u : (↥c.O)ˣ, ((u : ↥c.O) : PadicAlgCl l) ≠ 0 := by
    intro u h0
    have h1 : ((u : ↥c.O) : PadicAlgCl l) * (((u⁻¹ : (↥c.O)ˣ) : ↥c.O) : PadicAlgCl l) = 1 := by
      rw [← Subalgebra.coe_mul, Units.mul_inv]
      rfl
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  let ι : (↥c.O)ˣ →* (Qbar l)ˣ := Units.map (MonoidHomClass.toMonoidHom c.O.val)
  intro w hw
  refine ⟨D.pl l, unl_place Fact.out (hG.pl_over l Fact.out) hw, κ, ?_, ?_⟩
  · refine ⟨![ι.comp (D.om⁻¹ * D.ξ * D.ψ), ι.comp D.ψ, ι.comp (D.om⁻¹ * D.ξ), 1], ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> intro s hs <;>
        simp [ι, hom s hs, hξ s hs, hψ s hs]
    · refine ⟨h⁻¹, fun s => ?_⟩
      simp only [inv_inv, Units.val_mul, MonoidHom.coe_toHomUnits]
      exact hfl s
    · intro i s hs
      apply Units.ext
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, hine i s hs, hcyc]
      fin_cases i <;>
        simp [ι, Raw.ps, Raw.th, Raw.al, Raw.Psi, Chr.Psi, hinv] <;>
        (try rw [zpow_add₀ (hne _), zpow_one, zpow_natCast]) <;> dsimp [MonoidHomClass.toMonoidHom] <;> ring
  · intro i j heq
    by_cases hij : i = j
    · subst hij
      apply hG.decompSigma_ord
      have h1 : cycBar ℚ Ω l (D.s0 : G ℚ Ω) = 1 := by
        have e1 := congrArg (fun f => f D.s0) heq
        simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Subgroup.coe_subtype] at e1
        exact (mul_eq_left.mp e1.symm)
      have h2 : cycZ ℚ Ω l (D.s0 : G ℚ Ω) = 1 := by
        apply Units.ext
        have e2 := congrArg Units.val h1
        have e3 : algebraMap ℚ_[l] (Qbar l) ((cycZ ℚ Ω l (D.s0 : G ℚ Ω) : ℤ_[l]) : ℚ_[l]) = algebraMap ℚ_[l] (Qbar l) 1 := by
          rw [map_one]
          exact e2
        have e4 := (algebraMap ℚ_[l] (Qbar l)).injective e3
        exact PadicInt.ext e4
      rw [h2]
      exact IsOfFinOrder.one
    · have hmem : D.sg l ∈ D.Gp l := ((UpperTheory.V.GradeZeroInterpolatingElement.facts D hG).2.1 l (Finset.mem_insert_self _ _)).1
      obtain ⟨g, -, hg⟩ := hdist i j hij ⊤ (by simp) ⟨⟨D.sg l, hmem⟩, trivial, rfl⟩
      apply hg
      rw [heq, MonoidHom.mul_apply, Units.val_mul, MonoidHom.comp_apply, hcyc]
      rfl
end
