module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.SphOfWit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.AdmissibleResidualOfHyp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightOfSizeBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.ExistsResLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IneConj

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.KatoTwoW
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Z.Win

namespace UpperTheory.V.Z.Kato.WeilSphericalRecords

def KatoTwoW : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω]
    (e N : ℕ) (θ ψ : G ℚ Ω →* (Qbar l)ˣ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)), Used l Ω K e N θ ψ W →
    ∀ (ι : Qbar l ≃+* ℂ) (f : Af.Newform (2 * e + 1)), f.Att ι (Af.tw W (cycBar ℚ Ω l ^ (-(e : ℤ)))) → WitAQ ι W →
      Af.BlochKatoSelmerVanishes l (Loc.colRep (Af.tw W 1)) ∧ Af.BlochKatoSelmerVanishes l (Loc.colRep (Af.tw W θ))

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
  {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N}

theorem kUse (hK : KatoTwo) (D : Dat Ω K c e ψ) {θ ψ' : G ℚ Ω →* (Qbar l)ˣ} {W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l)}
    (u : Used l Ω K e N θ ψ' W) (ι : Qbar l ≃+* ℂ) (h : D.IsModular ι W) :
    Af.BlochKatoSelmerVanishes l (Loc.colRep (Af.tw W 1)) ∧ Af.BlochKatoSelmerVanishes l (Loc.colRep (Af.tw W θ)) :=
  h.elim fun f hf => hK l Ω K e N θ ψ' W u ι f hf

theorem kUse' (hK : KatoTwoW) (_ : Dat Ω K c e ψ) {θ ψ' : G ℚ Ω →* (Qbar l)ˣ} {W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l)}
    (u : Used l Ω K e N θ ψ' W) (ι : Qbar l ≃+* ℂ)
    (h : (∃ f : Af.Newform (2 * e + 1), f.Att ι (Af.tw W (cycBar ℚ Ω l ^ (-(e : ℤ))))) ∧ WitAQ ι W) :
    Af.BlochKatoSelmerVanishes l (Loc.colRep (Af.tw W 1)) ∧ Af.BlochKatoSelmerVanishes l (Loc.colRep (Af.tw W θ)) :=
  h.1.elim fun f hf => hK l Ω K e N θ ψ' W u ι f hf h.2

end UpperTheory.V.Z.Kato.WeilSphericalRecords
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.RecFrob
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.CuspRep Polynomial
open UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Kato.WeilSphericalRecords

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

end UpperTheory.V.Z.Kato.WeilSphericalRecords
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.DecConj
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords UpperTheory.Zero.LLC
open scoped Pointwise

private theorem gap_pow {C : Type} [CommGroup C] (x : C) (a b : ℤ) (m : ℕ)
    (h : (x ^ a) ^ m = (x ^ b * x) ^ m) : x ^ ((m : ℤ) * (a - b - 1)) = 1 := by
  have h' : x ^ (a * m) = x ^ ((b + 1) * m) := by
    rw [zpow_mul, zpow_mul, zpow_add_one, zpow_natCast, zpow_natCast, h]
  have hc : (m : ℤ) * (a - b - 1) = a * m - (b + 1) * m := by ring
  rw [hc, zpow_sub, h', mul_inv_cancel]

private theorem exp_ne (e : ℕ) (he : 1 ≤ e) (m : ℕ) (hm : 1 ≤ m) (i j : Fin 2) :
    (m : ℤ) * ((![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) i - (![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) j - 1) ≠ 0 := by
  refine mul_ne_zero (by exact_mod_cast (by omega : m ≠ 0)) ?_
  fin_cases i <;> fin_cases j <;> simp <;> omega

private def decConj {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (A B : ValuationSubring Ω) (γ : G F Ω) (h : γ • A = B) :
    ↥(Dec (F := F) B) →* ↥(Dec (F := F) A) where
  toFun u := ⟨γ⁻¹ * u * γ, by
    have hu := mem_Dec.1 u.2
    rw [mem_Dec, mul_smul, mul_smul, h, hu, ← h, inv_smul_smul]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.potOf :
    PotOf := by
  intro F Ω _ _ _ _ _ l _ e he r w A κ hl hA hE
  obtain ⟨⟨g, hg⟩, hI⟩ := hE
  have hvA : A.valuation (l : Ω) < 1 := by
    have h1 := (hA (l : 𝓞 F)).2 hl
    simpa using h1
  have hv : ∀ (t : Dec (F := F) A), (t : G F Ω) ∈ Ine A → ∀ i : Fin 2,
      κ i t = cycBar F Ω l ↑t ^ ((![(e : ℤ), -(e : ℤ)] : Fin 2 → ℤ) i) := by
    intro t ht i
    fin_cases i
    · exact (hI t ht).1
    · exact (hI t ht).2
  intro A' hA'
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hA hA'
  refine ⟨fun i => (κ i).comp (decConj A A' σ hσ), ?_, ?_⟩
  · refine ⟨g * r σ⁻¹, fun s => ?_⟩
    have hc : ((decConj A A' σ hσ s : Dec (F := F) A) : G F Ω) = σ⁻¹ * ↑s * σ := rfl
    have key : g * r σ⁻¹ * r ↑s * (g * r σ⁻¹)⁻¹ = g * r ↑(decConj A A' σ hσ s) * g⁻¹ := by
      rw [hc, map_mul, map_mul, map_inv]
      group
    rw [key]
    exact hg _
  · intro i j m hm heq
    obtain ⟨g0, hg0, hn⟩ := Ws.Pt.cycIne F Ω l A hvA _ (exp_ne e he m hm i j)
    have hA'σ : σ⁻¹ • A' = A := by rw [← hσ, inv_smul_smul]
    have hg1 : σ * g0 * σ⁻¹ ∈ Ine A' := by
      have h2 := (Two.ineConj F Ω σ⁻¹).1 A' g0 (by rw [hA'σ]; exact hg0)
      rwa [inv_inv] at h2
    have ht : decConj A A' σ hσ ⟨σ * g0 * σ⁻¹, Ine_le_Dec A' hg1⟩ = ⟨g0, Ine_le_Dec A hg0⟩ :=
      Subtype.ext (by
        show σ⁻¹ * (σ * g0 * σ⁻¹) * σ = g0
        group)
    have hcyc : cycBar F Ω l (σ * g0 * σ⁻¹) = cycBar F Ω l g0 := by
      rw [map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]
    have h3 := DFunLike.congr_fun heq ⟨σ * g0 * σ⁻¹, Ine_le_Dec A' hg1⟩
    simp only [MonoidHom.pow_apply, MonoidHom.mul_apply, MonoidHom.comp_apply,
      Subgroup.coe_subtype] at h3
    rw [ht, hv _ hg0 i, hv _ hg0 j, hcyc] at h3
    exact hn (gap_pow (cycBar F Ω l g0) _ _ m h3)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.IsFrobOfRs
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords UpperTheory.Zero.LLC
open scoped Pointwise

section Res

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra ℚ K] [Algebra K Ω] [IsScalarTower ℚ K Ω]

private abbrev rs : G K Ω →* G ℚ Ω := AlgEquiv.restrictScalarsHom ℚ

private theorem rs_smul (s : G K Ω) (A : ValuationSubring Ω) : (rs s : G ℚ Ω) • A = s • A := by
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

private theorem rs_mem_Dec {s : G K Ω} {A : ValuationSubring Ω} :
    (rs s : G ℚ Ω) ∈ Dec (F := ℚ) A ↔ s ∈ Dec (F := K) A := by
  rw [mem_Dec, mem_Dec, rs_smul]

private theorem rs_mem_Ine {s : G K Ω} {A : ValuationSubring Ω} (hs : s ∈ Ine (F := K) A) :
    (rs s : G ℚ Ω) ∈ Ine (F := ℚ) A :=
  ⟨rs_mem_Dec.2 hs.1, hs.2⟩

private theorem isFrob_of_rs {s : G K Ω} {A : ValuationSubring Ω} {q : ℕ} (hs : IsFrob A q (rs s : G ℚ Ω)) :
    IsFrob A q s :=
  ⟨rs_mem_Dec.1 hs.1, hs.2⟩

private theorem exists_rs (σ : G ℚ Ω) (h : ∀ x : K, σ (algebraMap K Ω x) = algebraMap K Ω x) :
    ∃ s : G K Ω, rs s = σ :=
  ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) h, AlgEquiv.ext fun _ => rfl⟩

private theorem cycBar_rs (l : ℕ) [Fact l.Prime] (s : G K Ω) : cycBar ℚ Ω l (rs s) = cycBar K Ω l s := by
  have h : MulSemiringAction.toRingAut (G ℚ Ω) Ω (rs s) = MulSemiringAction.toRingAut (G K Ω) Ω s :=
    RingEquiv.ext fun _ => rfl
  simp only [cycBar, cycZ, MonoidHom.comp_apply, h]

private def resDec (A : ValuationSubring Ω) : ↥(Dec (F := K) A) →* ↥(Dec (F := ℚ) A) :=
  (rs.comp (Dec (F := K) A).subtype).codRestrict (Dec (F := ℚ) A) fun s => rs_mem_Dec.2 s.2

private theorem exact_res {l : ℕ} [Fact l.Prime] {e : ℕ} {V : G ℚ Ω →* GL (Fin 2) (Qbar l)}
    {A : ValuationSubring Ω} {κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ} (h : Exact e V A κ) :
    Exact e (V.comp (rs : G K Ω →* G ℚ Ω)) A fun i => (κ i).comp (resDec A) := by
  obtain ⟨⟨g, hg⟩, hI⟩ := h
  refine ⟨⟨g, fun s => hg (resDec A s)⟩, fun s hs => ?_⟩
  have h2 := hI (resDec A s) (rs_mem_Ine hs)
  have h3 : cycBar ℚ Ω l ((resDec A s : ↥(Dec (F := ℚ) A)) : G ℚ Ω) = cycBar K Ω l s := cycBar_rs l (s : G K Ω)
  rw [h3] at h2
  exact h2

private theorem frobIn_res {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {e q : ℕ} {A : ValuationSubring Ω}
    {κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ} {B : Multiset ℂˣ}
    (hfix : ∀ g ∈ Dec (F := ℚ) A, ∀ x : K, g (algebraMap K Ω x) = algebraMap K Ω x)
    (h : FrobIn ι e q A (fun i => (κ i).comp (resDec (K := K) A)) B) : FrobIn ι e q A κ B := by
  intro σ hσ
  obtain ⟨s, hs⟩ := exists_rs (K := K) (σ : G ℚ Ω) (hfix _ σ.2)
  have hd : s ∈ Dec (F := K) A := rs_mem_Dec.1 (hs ▸ σ.2)
  have hr : resDec A (⟨s, hd⟩ : ↥(Dec (F := K) A)) = σ := Subtype.ext hs
  obtain ⟨b, hb, he⟩ := h ⟨s, hd⟩ (isFrob_of_rs (by rw [hs]; exact hσ))
  refine ⟨b, hb, ?_⟩
  have h3 : cycBar ℚ Ω l (σ : G ℚ Ω) = cycBar K Ω l s := by rw [← hs]; exact cycBar_rs l s
  rw [h3]
  have h4 : ((κ 0).comp (resDec (K := K) A)) ⟨s, hd⟩ = κ 0 σ := by
    rw [MonoidHom.comp_apply, hr]
  rw [← h4]
  exact he

end Res

theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.locQ :
    PlainRec → PlainOf → RecTExists → BcSplit → PotOf → LocK → LocQ := by
  intro hPR hPO hRT hBC hPot hLK l _ hl2 Ω _ _ _ ι e he V π hc hirr hM hreg hatt v A κ hlv hA hE hor
  obtain ⟨K, _, _, _, _, _, _, P, w, hfr, hirrK, hregP, hpol, hattP, hAw, hlw, hnorm, hfix, hsat⟩ :=
    hBC l hl2 Ω ι V π hc hirr hM hreg hatt v A hlv hA
  have hEx := exact_res (K := K) hE
  have hcK : Continuous (V.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) :=
    hc.comp (UpperTheory.V.Af.continuous_restrictScalarsHom _ _ _)
  have hWP : PlainAt P w := by
    rcases hor with hW | ⟨B, hB⟩
    · have hWA := hW K hfr hirrK
      obtain ⟨rc, hrc⟩ := hRT K Ω A w hAw
      have hpu := hPot K Ω l e he _ w A _ hlw hAw hEx
      intro σ hσ
      exact (guard_of hPR hregP hattP hWA (Or.inr (Or.inr hpu)) hrc hσ).1
    · exact (hPO K 2 (by norm_num) P w).2 ⟨B, (hsat B).1 hB⟩
  obtain ⟨⟨B₀, hB₀⟩, hF⟩ := hLK K Ω l hl2 ι e he _ P hcK hregP hpol hattP w A _ hlw hAw hEx hWP
  refine ⟨⟨B₀, (hsat B₀).2 hB₀⟩, fun B hB => ?_⟩
  have h := hF B ((hsat B).1 hB)
  rw [hnorm] at h
  exact frobIn_res hfix h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.BcSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormEqNormV
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

namespace GlobalTheory.LiftAbsPow

open GlobalTheory.CuspRep.InfType

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M]

theorem v_map_eq_one {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
    (i : v.adicCompletion K ≃+* w.adicCompletion M) (hi : Continuous i) {x : v.adicCompletion K}
    (hx : Valued.v x = 1) : Valued.v (i x) = 1 := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have h0 : Valued.v (i x) ≠ 0 := by simpa using hx0
  have h1 : Valued.v (i x) ≤ 1 := (GlobalTheory.TypeBlockFix.v_map_le_one_iff v w i hi x).2 hx.le
  have h2 : Valued.v (i x⁻¹) ≤ 1 := (GlobalTheory.TypeBlockFix.v_map_le_one_iff v w i hi _).2 (by rw [map_inv₀, hx, inv_one])
  rw [map_inv₀, map_inv₀] at h2
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (i x) * (Valued.v (i x))⁻¹ := (mul_inv_cancel₀ h0).symm
    _ ≤ Valued.v (i x) * 1 := mul_le_mul' le_rfl h2
    _ = Valued.v (i x) := mul_one _

theorem v_map_unif {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
    (i : v.adicCompletion K ≃+* w.adicCompletion M) (hi : Continuous i) {p : v.adicCompletion K}
    (hp : Valued.v p = WithZero.exp (-1)) : Valued.v (i p) = WithZero.exp (-1) := by
  have hp0 : p ≠ 0 := by rintro rfl; rw [map_zero] at hp; exact WithZero.exp_ne_zero hp.symm
  have hlt : Valued.v (i p) < 1 := (GlobalTheory.TypeBlockFix.v_map_lt_one_iff v w i hi p).2 (by
    rw [hp, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
  have key : ∀ z : w.adicCompletion M, Valued.v z < 1 → Valued.v z ≤ Valued.v (i p) := fun z hz => by
    have hy : Valued.v (i.symm z) < 1 := (GlobalTheory.TypeBlockFix.v_map_lt_one_iff v w i hi _).1 (by simpa using hz)
    rw [GlobalTheory.SplitUnif.lt_one_iff, ← hp] at hy
    have h3 : Valued.v (i.symm z / p) ≤ 1 := by
      rw [map_div₀]
      exact div_le_one_of_le₀ hy zero_le
    have h4 := (GlobalTheory.TypeBlockFix.v_map_le_one_iff v w i hi _).2 h3
    rw [map_div₀, map_div₀, RingEquiv.apply_symm_apply] at h4
    have hip : 0 < Valued.v (i p) := by
      rw [zero_lt_iff]; simpa using hp0
    exact (div_le_one₀ hip).1 h4
  obtain ⟨q, hq⟩ := w.valuation_exists_uniformizer M
  have hq' : Valued.v ((q : M) : w.adicCompletion M) = WithZero.exp (-1) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hq]
  refine le_antisymm ((GlobalTheory.SplitUnif.lt_one_iff _).1 hlt) ?_
  rw [← hq']
  exact key _ (by rw [hq', ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)

theorem v_map_eq {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
    (i : v.adicCompletion K ≃+* w.adicCompletion M) (hi : Continuous i) (x : v.adicCompletion K) :
    Valued.v (i x) = Valued.v x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨p0, hp0⟩ := v.valuation_exists_uniformizer K
  set p : v.adicCompletion K := (p0 : v.adicCompletion K)
  have hp : Valued.v p = WithZero.exp (-1) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hp0]
  have hpne : p ≠ 0 := by rintro h; rw [h, map_zero] at hp; exact WithZero.exp_ne_zero hp.symm
  have hvx : Valued.v x ≠ 0 := by simpa using hx
  set k := WithZero.log (Valued.v x)
  have hk : Valued.v x = WithZero.exp k := (WithZero.exp_log hvx).symm
  obtain ⟨u, hu, e⟩ : ∃ u, Valued.v u = 1 ∧ x = u * (p ^ k)⁻¹ := by
    refine ⟨x * p ^ k, ?_, ?_⟩
    · rw [map_mul, map_zpow₀, hp, hk, ← WithZero.exp_zsmul, ← WithZero.exp_add, smul_eq_mul]
      simp
    · field_simp
  rw [e]
  simp only [map_mul, map_inv₀, map_zpow₀]
  rw [v_map_eq_one i hi hu, hu, v_map_unif i hi hp, hp]

theorem card_residue (v : HeightOneSpectrum (𝓞 K)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) = Ideal.absNorm v.asIdeal := by
  have hF : ∀ s : 𝓞 K, Valued.v (algebraMap K (v.adicCompletion K) s) = v.intValuation s := fun s =>
    (v.valuedAdicCompletion_eq_valuation' _).trans (HeightOneSpectrum.valuation_of_algebraMap v s)
  exact GlobalTheory.SplitUnif.card_residueField v (algebraMap K (v.adicCompletion K)) v (fun _ => rfl) fun s => by
    rw [hF, HeightOneSpectrum.intValuation_lt_one_iff_mem]

theorem absNorm_eq {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
    (i : v.adicCompletion K ≃+* w.adicCompletion M) (hi : Continuous i) :
    Ideal.absNorm v.asIdeal = Ideal.absNorm w.asIdeal := by
  let ψ : v.adicCompletionIntegers K ≃+* w.adicCompletionIntegers M :=
    { toFun := fun a => ⟨i a, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2
        ((v_map_eq i hi a).le.trans ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 a.2))⟩
      invFun := fun b => ⟨i.symm b, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by
        rw [← v_map_eq i hi, RingEquiv.apply_symm_apply]
        exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 b.2)⟩
      left_inv := fun a => Subtype.ext (i.symm_apply_apply a)
      right_inv := fun b => Subtype.ext (i.apply_symm_apply b)
      map_mul' := fun a b => Subtype.ext (map_mul i (a : v.adicCompletion K) (b : v.adicCompletion K))
      map_add' := fun a b => Subtype.ext (map_add i (a : v.adicCompletion K) (b : v.adicCompletion K)) }
  rw [← card_residue v, ← card_residue w]
  exact Nat.card_congr (IsLocalRing.ResidueField.mapEquiv ψ).toEquiv

end GlobalTheory.LiftAbsPow

namespace GlobalTheory.LiftAbsPow

open GlobalTheory.CuspRep.InfType GlobalTheory.HeckeGal.Model

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M]

end GlobalTheory.LiftAbsPow

namespace GlobalTheory.LiftAbsPow

open GlobalTheory.CuspRep.InfType GlobalTheory.HeckeGal.Model

theorem absNorm_eq_normV {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Ideal.absNorm v.asIdeal = normV v := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

end GlobalTheory.LiftAbsPow
end
end

noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Kato.WeilSphericalRecords

end UpperTheory.V.Z.Kato.WeilSphericalRecords
end
end
