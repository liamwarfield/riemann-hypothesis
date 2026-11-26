module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.IsoJ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.HsLaw
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.FinitePartSplitInfinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinSLoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactPartCentralizerLeConjIntegralUnitary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.OkConj

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.RhoInt
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.Dict.Br

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

private theorem rho_coe (P : Pre L) (v : Pl (Lp L)) (w : Plc L) (h : un w = v) (a : Kv v) :
    P.rho v w h ⟨a, 0⟩ = P.φ v w h a := by
  show P.φ v w h a + P.φ v w h 0 * P.rt w = _
  simp

private theorem exists_over (P : Pre L) (v : Pl (Lp L)) : ∃ w : Plc L, un w = v := by
  by_contra hne
  push_neg at hne
  have hE : IsEmpty {w : Plc L // un w = v} := ⟨fun w => hne w.1 w.2⟩
  have h01 := (rhoBij L P v).1 (a₁ := 0) (a₂ := 1) (funext fun w => (hE.false w).elim)
  exact zero_ne_one h01

private theorem conj_int (a : Af L) (hA : ∀ u : Plc L, pLoc L u a ∈ u.adicCompletionIntegers L) (w : Plc L) :
    pLoc L w (cjF a) ∈ w.adicCompletionIntegers L := by
  rw [pLoc_conjFin, HeightOneSpectrum.mem_adicCompletionIntegers, (conjLoc_spec _ w).2.2]
  exact hA _

private theorem star_int (P : Pre L) (v : Pl (Lp L)) (x : Lsq (Kv v) (cv v P.Δ))
    (hx : ∀ w h, P.rho v w h x ∈ w.adicCompletionIntegers L) (w : Plc L) (h : un w = v) :
    P.rho v w h (star x) ∈ w.adicCompletionIntegers L := by
  classical
  have hf : ∀ u : Plc L, (if h : un u = v then P.rho v u h x else 0) ∈ u.adicCompletionIntegers L := fun u => by
    by_cases hu : un u = v
    · rw [dite_eq_left hu]; exact hx u hu
    · rw [dite_eq_right hu]; exact zero_mem _
  let a : Af L := ⟨fun u => if h : un u = v then P.rho v u h x else 0, Filter.Eventually.of_forall hf⟩
  have ha : ∀ w h, P.rho v w h x = pLoc L w a := fun w h => by
    show _ = dite _ _ _
    rw [dite_eq_left h]
  rw [rhoStar L P v x a ha w h]
  exact conj_int a hf w

end UpperTheory.V.Z.Sym.Dict.Br

theorem UpperTheory.V.Z.Sym.Dict.Br.rhoInt :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (P : Pre L), ∀ v (x : Lsq (Kv v) (cv v P.Δ)), IsIntegral (Ov v) x ↔ ∀ w h, P.rho v w h x ∈ w.adicCompletionIntegers L := by
  intro L _ _ _ P v x
  constructor
  · intro hx w h
    obtain ⟨p, hp, he⟩ := hx
    let f : Ov v →+* w.adicCompletionIntegers L :=
      ((P.φ v w h).comp (algebraMap (Ov v) (Kv v))).codRestrict (w.adicCompletionIntegers L)
        fun a => (rhoDiv L P v w h _).2 a.2
    have hc : (P.rho v w h).comp (algebraMap (Ov v) (Lsq (Kv v) (cv v P.Δ))) =
        (algebraMap (w.adicCompletionIntegers L) (Kw w)).comp f := by
      refine RingHom.ext fun a => ?_
      exact rho_coe P v w h _
    have hi : IsIntegral (w.adicCompletionIntegers L) (P.rho v w h x) := by
      refine ⟨p.map f, hp.map f, ?_⟩
      rw [Polynomial.eval₂_map, ← hc, ← Polynomial.hom_eval₂, he, map_zero]
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
    rw [← hy]
    exact y.2
  · intro hx
    obtain ⟨w, h⟩ := exists_over P v
    have hs := star_int P v x hx w h
    have ht : 2 * x.re ∈ v.adicCompletionIntegers (Lp L) := by
      rw [← rhoDiv L P v w h, ← rho_coe P v w h]
      have : (⟨2 * x.re, 0⟩ : Lsq (Kv v) (cv v P.Δ)) = x + star x := by
        apply QuadraticAlgebra.ext <;> simp [two_mul]
      rw [this, map_add (f := _)]
      exact add_mem (hx w h) hs
    have hn : x.re * x.re - cv v P.Δ * (x.im * x.im) ∈ v.adicCompletionIntegers (Lp L) := by
      rw [← rhoDiv L P v w h, ← rho_coe P v w h]
      have : (⟨x.re * x.re - cv v P.Δ * (x.im * x.im), 0⟩ : Lsq (Kv v) (cv v P.Δ)) = x * star x := by
        apply QuadraticAlgebra.ext <;> simp <;> ring
      rw [this, map_mul]
      exact mul_mem (hx w h) hs
    let t : Ov v := ⟨_, ht⟩
    let n : Ov v := ⟨_, hn⟩
    refine ⟨Polynomial.X ^ 2 - (Polynomial.C t * Polynomial.X + Polynomial.C (-n)),
      Polynomial.monic_X_pow_sub (Polynomial.degree_linear_le.trans_lt (by norm_num)), ?_⟩
    have e1 : algebraMap (Ov v) (Lsq (Kv v) (cv v P.Δ)) t = ⟨2 * x.re, 0⟩ := rfl
    have e2 : algebraMap (Ov v) (Lsq (Kv v) (cv v P.Δ)) (-n) = ⟨-(x.re * x.re - cv v P.Δ * (x.im * x.im)), 0⟩ := rfl
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, e1, e2]
    apply QuadraticAlgebra.ext <;> simp [pow_two, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] <;> ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.IsoAbs
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem continuous_of_val_iff {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k']
    [IsNonarchimedeanLocalField k'] (i : k ≃+* k')
    (h : ∀ a b, valuation k' (i a) ≤ valuation k' (i b) ↔ valuation k a ≤ valuation k b) :
    Continuous i := by
  refine continuous_of_continuousAt_zero (i : k →+* k').toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  change Filter.Tendsto i (nhds 0) (nhds 0)
  rw [(IsValuativeTopology.hasBasis_nhds_zero' k').tendsto_right_iff]
  intro r hr
  obtain ⟨c, rfl⟩ := valuation_surjective r
  have hc : valuation k (i.symm c) ≠ 0 := by
    intro h0
    have h2 := (h (i.symm c) 0).2 (by simp [h0])
    simp only [RingEquiv.apply_symm_apply, map_zero, le_zero_iff] at h2
    exact hr h2
  have hm : {x : k | valuation k x < valuation k (i.symm c)} ∈ nhds (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mpr ⟨_, hc, subset_rfl⟩
  filter_upwards [hm] with a ha
  have h3 := h (i.symm c) a
  rw [RingEquiv.apply_symm_apply] at h3
  exact not_le.1 fun h4 => absurd (h3.1 h4) (not_le.2 ha)

theorem UpperTheory.V.Z.Sym.Dict.Br.isoAbs :
    ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k'), IsoOk i → ∀ (z : ℂ) (a : kˣ), absPow k' z (Units.map (i : k →* k') a) = absPow k z a := by
  intro k k' _ _ _ _ _ _ _ _ i hi z a
  have h1 := (isoVal k k' i hi).1
  have hc : Continuous i := continuous_of_val_iff i h1
  have hc' : Continuous i.symm := continuous_of_val_iff i.symm fun a b => by
    have := h1 (i.symm a) (i.symm b)
    simpa only [RingEquiv.apply_symm_apply] using this.symm
  have hn := GlobalTheory.SplitWeil.nabs_map_of_homeomorph i hc hc' a
  ext
  rw [val_absPow, val_absPow]
  exact congrArg (fun t : ℝ => (t : ℂ) ^ z) hn
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.ExistsUnr
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.Dict.Br.QuadraticCharacterExistence

open scoped WithZero

private theorem exists_unr {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (c : ℂˣ) :
    ∃ χ : Kˣ →* ℂˣ, (∀ u : Oˣ, χ (Units.map (algebraMap O K : O →* K) u) = 1) ∧
      ∀ (ϖ : O) (x : Kˣ), Irreducible ϖ → (x : K) = algebraMap O K ϖ → χ x = c := by
  let w : HeightOneSpectrum O := IsDiscreteValuationRing.maximalIdeal O
  let f : Kˣ →* Multiplicative ℤ :=
    (WithZero.unitsWithZeroEquiv (α := Multiplicative ℤ)).toMonoidHom.comp
      (Units.map ((w.valuation K : Valuation K ℤᵐ⁰) : K →* ℤᵐ⁰))
  have hf : ∀ (x : Kˣ) (n : Multiplicative ℤ), w.valuation K (x : K) = (n : ℤᵐ⁰) → f x = n := by
    intro x n h
    apply WithZero.coe_injective
    exact (WithZero.coe_unitsWithZeroEquiv_eq_units_val _).trans h
  refine ⟨(zpowersHom ℂˣ c⁻¹).comp f, fun u => ?_, fun ϖ x hϖ hx => ?_⟩
  · have h1 : w.valuation K (Units.map (algebraMap O K : O →* K) u : K) = ((1 : Multiplicative ℤ) : ℤᵐ⁰) := by
      rw [Units.coe_map, MonoidHom.coe_coe, HeightOneSpectrum.valuation_of_algebraMap, WithZero.coe_one,
        HeightOneSpectrum.intValuation_eq_one_iff]
      exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h u.isUnit
    rw [MonoidHom.comp_apply, hf _ _ h1, map_one]
  · have h1 : w.valuation K (x : K) = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : ℤᵐ⁰) := by
      rw [hx, HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.intValuation_singleton _ hϖ.ne_zero hϖ.maximalIdeal_eq]
      rfl
    rw [MonoidHom.comp_apply, hf _ _ h1]
    simp [zpowersHom_apply]

private theorem delta_ne {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L) : R.Δ ≠ 0 := by
  intro h
  have h1 : (QuadraticAlgebra.omega : Lsq (Lp L) R.Δ) * QuadraticAlgebra.omega = 0 := by
    ext <;> simp [h]
  have h2 : R.e QuadraticAlgebra.omega = 0 := by
    have := congrArg R.e h1
    rw [map_mul, map_zero] at this
    exact mul_self_eq_zero.1 this
  have h3 : (QuadraticAlgebra.omega : Lsq (Lp L) R.Δ) = 0 := by
    exact (map_eq_zero_iff R.e R.e.injective).1 h2
  have := congrArg QuadraticAlgebra.im h3
  simp at this

private theorem hs_one {K : Type} [Field K] [CharZero K] {D : K} (h0 : D ≠ 0) (h : IsSquare D) (x : K) : hs D x = 1 := by
  obtain ⟨r, rfl⟩ := h
  have hr : r ≠ 0 := fun e => h0 (by rw [e, mul_zero])
  refine if_pos ⟨(x + 1) / 2, (x - 1) / (2 * r), ?_⟩
  field_simp
  ring

private theorem hs_neg {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    {D : K} (L : IsLoc O D) (hD : ¬ IsSquare D) {p : O} (hp : Irreducible p) : hs D (algebraMap O K p) = -1 := by
  haveI := L.frac
  obtain ⟨ε, s, hs0, rfl⟩ := L.even
  have hp' : algebraMap O K p ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hp.ne_zero
  refine if_neg fun ⟨a, b, e⟩ => L.not_even hp ?_
  have e' : a ^ 2 - algebraMap O K ε * (s * b) ^ 2 = algebraMap O K p := by rw [← e]; ring
  exact e' ▸ L.even_of_norm ε (fun ⟨r, hr⟩ => hD ⟨r * s, by rw [hr]; ring⟩) (e' ▸ hp')

end UpperTheory.V.Z.Sym.Dict.Br.QuadraticCharacterExistence

open UpperTheory.V.Z.Sym.Dict.Br.QuadraticCharacterExistence in
theorem UpperTheory.V.Z.Sym.Dict.Br.chiEx :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (R : RingBr L), ∃ χ : ∀ v : Pl (Lp L), (Kv v)ˣ →* ℂˣ, (∀ v : Pl (Lp L), (2 : 𝓞 (Lp L)) ∉ v.asIdeal ∨ IsSquare (cv v R.Δ) → IsChi (Ov v) (cv v R.Δ) (χ v)) := by
  intro L _ _ _ R
  have key : ∀ v : Pl (Lp L), ∃ χ : (Kv v)ˣ →* ℂˣ,
      (2 : 𝓞 (Lp L)) ∉ v.asIdeal ∨ IsSquare (cv v R.Δ) → IsChi (Ov v) (cv v R.Δ) χ := by
    intro v
    obtain ⟨hf, -, hfin, -⟩ := locBase (Lp L) v
    haveI := hf
    haveI := hfin
    have hq : (Nat.card (IsLocalRing.ResidueField (Ov v)) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 Nat.card_pos.ne'
    by_cases hsq : IsSquare (cv v R.Δ)
    · haveI : CharZero (Kv v) := charZero_of_injective_ringHom (cv v).injective
      have hΔ : cv v R.Δ ≠ 0 := (map_ne_zero _).2 (delta_ne R)
      obtain ⟨χ, h1, h2⟩ := exists_unr (O := Ov v) (K := Kv v) (Units.mk0 _ (div_ne_zero one_ne_zero hq))
      refine ⟨χ, fun _ => ⟨h1, fun ϖ x hϖ hx => ?_⟩⟩
      rw [h2 ϖ x hϖ hx, hs_one hΔ hsq]
      rfl
    · obtain ⟨χ, h1, h2⟩ := exists_unr (O := Ov v) (K := Kv v)
        (Units.mk0 _ (div_ne_zero (neg_ne_zero.2 one_ne_zero) hq))
      refine ⟨χ, fun h => ⟨h1, fun ϖ x hϖ hx => ?_⟩⟩
      have hL := R.loc v (h.resolve_right hsq)
      rw [h2 ϖ x hϖ hx, hx, hs_neg hL hsq hϖ]
      rfl
  choose χ hχ using key
  exact ⟨χ, hχ⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.MapOne
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem star_map {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L)
    (x : Matrix (Fin 2) (Fin 2) (Lsq (Lp L) R.Δ)) :
    ((x.map R.e).map (IsCMField.complexConj L))ᵀ = (star x).map R.e := by
  ext i j
  simp [Matrix.star_apply, R.e_star]

private theorem map_mul' {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L)
    (x y : Matrix (Fin 2) (Fin 2) (Lsq (Lp L) R.Δ)) :
    (x * y).map R.e = x.map R.e * y.map R.e :=
  map_mul (R.e : Lsq (Lp L) R.Δ →+* L).mapMatrix x y

private theorem map_one' {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L) :
    (1 : Matrix (Fin 2) (Fin 2) (Lsq (Lp L) R.Δ)).map R.e = 1 :=
  map_one (R.e : Lsq (Lp L) R.Δ →+* L).mapMatrix

private theorem map_det' {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L)
    (x : Matrix (Fin 2) (Fin 2) (Lsq (Lp L) R.Δ)) :
    (x.map R.e).det = R.e x.det :=
  ((R.e : Lsq (Lp L) R.Δ →+* L).map_det x).symm

theorem UpperTheory.V.Z.Sym.Dict.Br.rSEx :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (R : RingBr L), ∃ r : SU R.Δ ≃* ↥(ratU L 2 ⊓ SUA L), (∀ γ w, mL w (r γ : UA L 2) = (mt (γ : DX R.Δ)).map fun x => algebraMap L (Kw w) (R.e x)) ∧ ∀ γ (τ : L →+* ℂ), (cEmb τ (r γ : UA L 2) : Matrix (Fin 2) (Fin 2) ℂ) = (mt (γ : DX R.Δ)).map fun x => τ (R.e x) := by
  intro L _ _ _ R
  have hrf := ratFacts L 2
  obtain ⟨hs1, hs2⟩ := suIff (Lp L) R.Δ
  let E : GL (Fin 2) (Lsq (Lp L) R.Δ) →* GL (Fin 2) L :=
    GeneralLinearGroup.map (R.e : Lsq (Lp L) R.Δ →+* L)
  have hEc : ∀ g, (E g : Matrix (Fin 2) (Fin 2) L) = (g : Matrix (Fin 2) (Fin 2) _).map R.e := fun g => rfl
  have hdet1 : ∀ γ : SU R.Δ, (mt (γ : DX R.Δ)).det = 1 := by
    intro γ
    have h : GeneralLinearGroup.det ((γ : DX R.Δ) : GL (Fin 2) (Lsq (Lp L) R.Δ)) = 1 := γ.2
    simpa using congrArg Units.val h
  have hstar : ∀ γ : SU R.Δ, star (mt (γ : DX R.Δ)) * mt (γ : DX R.Δ) = 1 := by
    intro γ
    rw [(hs1 γ).1, hdet1, one_smul]
  have hdetE : ∀ γ : SU R.Δ, GeneralLinearGroup.det (E ((γ : DX R.Δ) : GL (Fin 2) (Lsq (Lp L) R.Δ))) = 1 := by
    intro γ
    apply Units.ext
    have : (E ((γ : DX R.Δ) : GL (Fin 2) (Lsq (Lp L) R.Δ)) : Matrix (Fin 2) (Fin 2) L).det = 1 := by
      rw [hEc, map_det', hdet1, map_one]
    simpa using this
  have hmem : ∀ γ : SU R.Δ, ratGL L 2 (E ((γ : DX R.Δ) : GL (Fin 2) (Lsq (Lp L) R.Δ))) ∈ UA L 2 := by
    intro γ
    rw [(hrf _).1, hEc, star_map, ← map_mul', hstar, map_one']
  let φ1 : SU R.Δ →* UA L 2 :=
    ((ratGL L 2).comp (E.comp ((DX R.Δ).subtype.comp (SU R.Δ).subtype))).codRestrict (UA L 2) hmem
  have hφ1 : ∀ γ, ((φ1 γ : UA L 2) : GlobalTheory.CuspRep.GA L 2) = ratGL L 2 (E ((γ : DX R.Δ) : GL (Fin 2) (Lsq (Lp L) R.Δ))) := fun _ => rfl
  have hmem2 : ∀ γ, φ1 γ ∈ ratU L 2 ⊓ SUA L := by
    intro γ
    refine ⟨?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.2 ⟨_, rfl⟩
    · show GeneralLinearGroup.det ((φ1 γ : UA L 2) : GlobalTheory.CuspRep.GA L 2) = 1
      rw [hφ1]
      exact (((hrf _).2.2 (hmem γ)).2.2).2 (hdetE γ)
  let φ2 : SU R.Δ →* ↥(ratU L 2 ⊓ SUA L) := φ1.codRestrict _ hmem2
  have hinj : Function.Injective φ2 := by
    intro a b hab
    have h1 : ((φ1 a : UA L 2) : GlobalTheory.CuspRep.GA L 2) = ((φ1 b : UA L 2) : GlobalTheory.CuspRep.GA L 2) :=
      congrArg (fun x : ↥(ratU L 2 ⊓ SUA L) => ((x : UA L 2) : GlobalTheory.CuspRep.GA L 2)) hab
    rw [hφ1, hφ1] at h1
    have h2 := (hrf (E 1)).2.1 h1
    have h3 : mt (a : DX R.Δ) = mt (b : DX R.Δ) := by
      have h4 := congrArg (fun g : GL (Fin 2) L => (g : Matrix (Fin 2) (Fin 2) L)) h2
      simp only [hEc] at h4
      exact Matrix.ext fun i j => R.e.injective (congrFun (congrFun h4 i) j)
    exact Subtype.ext (Subtype.ext (Units.ext h3))
  have hsurj : Function.Surjective φ2 := by
    rintro ⟨x, hx1, hx2⟩
    obtain ⟨g, hg⟩ := Subgroup.mem_subgroupOf.1 hx1
    have hgU : ratGL L 2 g ∈ UA L 2 := hg ▸ x.2
    have hdx : GeneralLinearGroup.det ((x : UA L 2) : GlobalTheory.CuspRep.GA L 2) = 1 := hx2
    have hdg : GeneralLinearGroup.det g = 1 := by
      apply ((hrf g).2.2 hgU).2.2.1
      rw [hg]; exact hdx
    have hconj := ((hrf g).1).1 hgU
    let m : Matrix (Fin 2) (Fin 2) (Lsq (Lp L) R.Δ) := (g : Matrix (Fin 2) (Fin 2) L).map R.e.symm
    have hm : m.map R.e = g := by
      ext i j; simp [m]
    have hms : star m * m = 1 := by
      have h1 : (star m * m).map R.e = (1 : Matrix (Fin 2) (Fin 2) (Lsq (Lp L) R.Δ)).map R.e := by
        rw [map_mul', ← star_map, hm, hconj, map_one']
      exact Matrix.ext fun i j => R.e.injective (congrFun (congrFun h1 i) j)
    have hmd : m.det = 1 := by
      apply R.e.injective
      rw [← map_det', hm, map_one]
      simpa using congrArg Units.val hdg
    obtain ⟨h, hh⟩ := hs2 m hms hmd
    have hSU : h ∈ SU R.Δ := by
      show GeneralLinearGroup.det (h : GL (Fin 2) (Lsq (Lp L) R.Δ)) = 1
      apply Units.ext
      have : (mt h).det = 1 := hh ▸ hmd
      simpa using this
    refine ⟨⟨h, hSU⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    show ratGL L 2 (E (h : GL (Fin 2) (Lsq (Lp L) R.Δ))) = _
    rw [← hg]
    congr 1
    apply Units.ext
    rw [hEc]
    show (mt h).map R.e = _
    rw [hh, hm]
  refine ⟨MulEquiv.ofBijective φ2 ⟨hinj, hsurj⟩, ?_, ?_⟩
  · intro γ w
    have := ((hrf _).2.2 (hmem γ)).1 w
    exact this.trans (by rw [hEc]; ext i j; rfl)
  · intro γ τ
    have := ((hrf _).2.2 (hmem γ)).2.1 τ
    exact this.trans (by rw [hEc]; ext i j; rfl)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.PhiGUnitary
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private noncomputable def phiG {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L) :
    U3 R.Δ →* GL (Fin 3) L :=
  (GeneralLinearGroup.map (R.e : Lsq (Lp L) R.Δ →+* L)).comp Unitary.toUnits

private theorem phiG_coe {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L) (γ : U3 R.Δ) :
    (phiG R γ : Matrix (Fin 3) (Fin 3) L) = (γ : Matrix (Fin 3) (Fin 3) _).map fun x => R.e x := rfl

private theorem phiG_unitary {L : Type} [Field L] [NumberField L] [IsCMField L] (R : RingBr L) (γ : U3 R.Δ) :
    ((phiG R γ : Matrix (Fin 3) (Fin 3) L).map (IsCMField.complexConj L))ᵀ * (phiG R γ : Matrix (Fin 3) (Fin 3) L) = 1 := by
  have h : star (γ : Matrix (Fin 3) (Fin 3) (Lsq (Lp L) R.Δ)) * (γ : Matrix (Fin 3) (Fin 3) (Lsq (Lp L) R.Δ)) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp γ.2
  have e1 : ((phiG R γ : Matrix (Fin 3) (Fin 3) L).map (IsCMField.complexConj L))ᵀ =
      (star (γ : Matrix (Fin 3) (Fin 3) (Lsq (Lp L) R.Δ))).map fun x => R.e x := by
    ext i j
    simp [phiG_coe, Matrix.star_apply, R.e_star]
  rw [e1, phiG_coe]
  have e2 := congrArg (fun m => m.map (R.e : Lsq (Lp L) R.Δ →+* L)) h
  simp only [Matrix.map_mul] at e2
  simpa using e2

theorem UpperTheory.V.Z.Sym.Dict.Br.rGEx :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (R : RingBr L), ∃ r : U3 R.Δ ≃* ratU L 3, (∀ γ w, mL w (r γ : UA L 3) = (γ : Matrix (Fin 3) (Fin 3) _).map fun x => algebraMap L (Kw w) (R.e x)) ∧ ∀ γ (τ : L →+* ℂ), (cEmb τ (r γ : UA L 3) : Matrix (Fin 3) (Fin 3) ℂ) = (γ : Matrix (Fin 3) (Fin 3) _).map fun x => τ (R.e x) := by
  intro L _ _ _ R
  have hU : ∀ γ : U3 R.Δ, ratGL L 3 (phiG R γ) ∈ UA L 3 := fun γ =>
    (ratFacts L 3 (phiG R γ)).1.mpr (phiG_unitary R γ)
  let f : U3 R.Δ →* ratU L 3 :=
    { toFun := fun γ => ⟨⟨ratGL L 3 (phiG R γ), hU γ⟩, Subgroup.mem_subgroupOf.mpr ⟨phiG R γ, rfl⟩⟩
      map_one' := by
        apply Subtype.ext; apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext; apply Subtype.ext
        simp }
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : ratGL L 3 (phiG R a) = ratGL L 3 (phiG R b) := congrArg Subtype.val (congrArg Subtype.val hab)
    have h2 := (ratFacts L 3 1).2.1 h1
    have h3 : (phiG R a : Matrix (Fin 3) (Fin 3) L) = phiG R b := congrArg Units.val h2
    apply Subtype.ext
    exact Matrix.ext fun i j => R.e.injective (congrFun (congrFun h3 i) j)
  have hsurj : Function.Surjective f := by
    rintro ⟨⟨x, hx⟩, hr⟩
    obtain ⟨g, hg⟩ := Subgroup.mem_subgroupOf.mp hr
    change ratGL L 3 g = x at hg
    subst hg
    have hc := (ratFacts L 3 g).1.mp hx
    let M : Matrix (Fin 3) (Fin 3) (Lsq (Lp L) R.Δ) := (g : Matrix (Fin 3) (Fin 3) L).map fun x => R.e.symm x
    have hM : star M * M = 1 := by
      have e1 : star M = (((g : Matrix (Fin 3) (Fin 3) L).map (IsCMField.complexConj L))ᵀ).map fun x => R.e.symm x := by
        refine Matrix.ext fun i j => R.e.injective ?_
        simp [M, Matrix.star_apply, R.e_star]
      have e2 := congrArg (fun m => m.map (R.e.symm : L →+* Lsq (Lp L) R.Δ)) hc
      simp only [Matrix.map_mul] at e2
      rw [e1]
      simpa [M] using e2
    refine ⟨⟨M, Matrix.mem_unitaryGroup_iff'.mpr hM⟩, ?_⟩
    have hp : phiG R ⟨M, Matrix.mem_unitaryGroup_iff'.mpr hM⟩ = g := by
      apply Units.ext
      ext i j
      simp [phiG_coe, M]
    apply Subtype.ext; apply Subtype.ext
    exact congrArg (ratGL L 3) hp
  refine ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩, ?_, ?_⟩
  · intro γ w
    exact ((ratFacts L 3 (phiG R γ)).2.2 (hU γ)).1 w
  · intro γ τ
    exact ((ratFacts L 3 (phiG R γ)).2.2 (hU γ)).2.1 τ
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.MemKGLIff
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem mem_KGL_iff {L : Type} [Field L] [NumberField L] [IsCMField L] (w : Plc L) {n : ℕ}
    (x : GL (Fin n) (Kw w)) : x ∈ GlobalTheory.LFun.KGL w (n := n) ↔
      (∀ i j, (x : Matrix (Fin n) (Fin n) (Kw w)) i j ∈ w.adicCompletionIntegers L) ∧
      ∀ i j, ((x⁻¹ : GL (Fin n) (Kw w)) : Matrix (Fin n) (Fin n) (Kw w)) i j ∈ w.adicCompletionIntegers L := by
  rw [← GlobalTheory.HeckeEigConj.KO_eq_KGL, GlobalTheory.SplitFlip.mem_KO_iff]
  have h : ∀ y : Kw w, y ∈ 𝒪[Kw w] ↔ y ∈ w.adicCompletionIntegers L := fun y => ((intsOv L w).2 y).symm
  simp only [h]

theorem UpperTheory.V.Z.Sym.Dict.Br.okG :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (B : Bridge L), (∀ (g : GA B.Δ) v, g.1 v ∈ KU (Ov v) _ ↔ ∀ w, un w = v → cLoc w (B.bG g : UA L 3) ∈ GlobalTheory.LFun.KGL w (n := 3)) ∧ (∀ (g : GA B.Δ) v, g.1 v = 1 ↔ ∀ w, un w = v → cLoc w (B.bG g : UA L 3) = 1) ∧ ∀ w (S : B.toRingBr.Split w) (g : GA B.Δ), cLoc w (B.bG g : UA L 3) = GeneralLinearGroup.map (S.i : Kv (un w) →+* Kw w) (Sig.eU S.hs (g.1 (un w))) := by
  intro L _ _ _ B
  have hm : ∀ (g : GA B.Δ) (w : Plc L) (i j : Fin 3),
      (cLoc w (B.bG g : UA L 3) : Matrix (Fin 3) (Fin 3) (Kw w)) i j
        = B.ρ _ w rfl ((g.1 (un w) : Matrix (Fin 3) (Fin 3) _) i j) :=
    fun g w i j => congrFun (congrFun (B.bG_loc g w) i) j
  have hi : ∀ (g : GA B.Δ) (w : Plc L) (i j : Fin 3),
      (((cLoc w (B.bG g : UA L 3))⁻¹ : GL (Fin 3) (Kw w)) : Matrix (Fin 3) (Fin 3) (Kw w)) i j
        = B.ρ _ w rfl (star ((g.1 (un w) : Matrix (Fin 3) (Fin 3) _) j i)) := by
    intro g w i j
    have h := hm g⁻¹ w i j
    rw [B.bG.map_inv, InvMemClass.coe_inv, map_inv] at h
    exact h
  refine ⟨fun g v => ?_, fun g v => ?_, fun w S g => ?_⟩
  · constructor
    · intro hK w h
      subst h
      rw [mem_KGL_iff]
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · rw [hm]
        exact (B.ρ_int _ _).1 (hK i j).1 w rfl
      · rw [hi]
        exact (B.ρ_int _ _).1 (hK j i).2 w rfl
    · intro H i j
      refine ⟨(B.ρ_int _ _).2 fun w h => ?_, (B.ρ_int _ _).2 fun w h => ?_⟩
      · subst h
        have := ((mem_KGL_iff _ _).1 (H w rfl)).1 i j
        rwa [hm] at this
      · subst h
        have := ((mem_KGL_iff _ _).1 (H w rfl)).2 j i
        rwa [hi] at this
  · constructor
    · intro h1 w h
      subst h
      apply Units.ext
      have := B.bG_loc g w
      rw [h1] at this
      refine this.trans ?_
      exact Matrix.map_one _ (map_zero _) (map_one _)
    · intro H
      apply Subtype.ext
      refine Matrix.ext fun i j => ?_
      apply sub_eq_zero.1
      apply B.ρ_inj
      intro w h
      cases h
      have e2 := hm g w i j
      rw [H w rfl, Units.val_one] at e2
      have e3 : B.ρ _ w rfl ((1 : Matrix (Fin 3) (Fin 3) (Lsq (Kv (un w)) (cv (un w) B.Δ))) i j) = (1 : Matrix (Fin 3) (Fin 3) (Kw w)) i j :=
        congrFun (congrFun (Matrix.map_one (B.ρ _ w rfl) (map_zero _) (map_one _)) i) j
      rw [map_sub, ← e2]
      exact sub_eq_zero.2 e3.symm
  · apply Units.ext
    refine (B.bG_loc g w).trans ?_
    refine Matrix.ext fun i j => ?_
    exact S.ρ_eq _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.RhoGlob
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Dict.Br.rhoGlob :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (P : Pre L), ∀ v w h (x : Lsq (Lp L) P.Δ), P.rho v w h (lmap (cv v) P.Δ x) = algebraMap L (Kw w) (P.e x) := by
  intro L _ _ _ P v w h x
  have hx : x = algebraMap (Lp L) (Lsq (Lp L) P.Δ) x.re
      + algebraMap (Lp L) (Lsq (Lp L) P.Δ) x.im * QuadraticAlgebra.omega := by
    ext <;> simp [QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im]
  have lhs : P.rho v w h (lmap (cv v) P.Δ x)
      = P.φ v w h (cv v x.re) + P.φ v w h (cv v x.im) * P.rt w := rfl
  rw [lhs, P.φ_alg, P.φ_alg, Pre.rt]
  conv_rhs => rw [hx]
  rw [map_add (f := _), map_mul, P.e_alg, P.e_alg, map_add (f := _), map_mul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.GlobEx
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Dict.Br.globEx :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L], ∃ (Δ : Lp L) (e : Lsq (Lp L) Δ ≃+* L), (∀ x, e (star x) = IsCMField.complexConj L (e x)) ∧ (∀ a : Lp L, e (algebraMap _ _ a) = algebraMap (Lp L) L a) ∧ ∀ σ : Lp L →+* ℝ, σ Δ < 0 :=
  _root_.UpperTheory.Reformulated.B.Qh37.globEx
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.EvenVal
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Dict.Br.evenVal :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (P : Pre L), Dict.Unr L → ∀ v : Pl (Lp L), EvenVal (Ov v) (cv v P.Δ) := by
  intro L _ _ _ P hU v
  have hval : ∀ x : Lp L, Valued.v (cv v x) = v.valuation (Lp L) x := fun x =>
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  have hδ : P.e QuadraticAlgebra.omega * P.e QuadraticAlgebra.omega = algebraMap (Lp L) L P.Δ := by
    rw [← map_mul, QuadraticAlgebra.omega_mul_omega_eq_algebraMap, map_zero, zero_mul, add_zero,
      P.e_alg]
  have hδ0 : P.e QuadraticAlgebra.omega ≠ 0 := by
    intro h0
    have h1 : (QuadraticAlgebra.omega : Lsq (Lp L) P.Δ) = 0 := P.e.injective (by rw [h0, map_zero])
    have h2 := congrArg QuadraticAlgebra.im h1
    simp at h2
  haveI := v.isMaximal
  obtain ⟨Q, hQm, hQl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [hQl.over, Ideal.under, Ideal.comap_bot_of_injective]
    exact FaithfulSMul.algebraMap_injective _ _
  let w : HeightOneSpectrum (𝓞 L) := ⟨Q, hQm.isPrime, hQ0⟩
  haveI : w.asIdeal.LiesOver v.asIdeal := hQl
  have hr : w.asIdeal.ramificationIdx (𝓞 (Lp L)) = 1 := by
    haveI := hU w
    haveI : w.asIdeal.IsPrime := w.isPrime
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := 𝓞 (Lp L)) (p := w.asIdeal)
  have hv := IsDedekindDomain.HeightOneSpectrum.valuation_liesOver L v w P.Δ
  rw [hr, pow_one, ← hδ, map_mul] at hv
  have hw0 : w.valuation L (P.e QuadraticAlgebra.omega) ≠ 0 := by simpa using hδ0
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer (Lp L)
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ
    exact WithZero.zero_ne_coe hπ
  let t : Lp L := π ^ (-WithZero.log (w.valuation L (P.e QuadraticAlgebra.omega)))
  have ht0 : t ≠ 0 := zpow_ne_zero _ hπ0
  have ht : v.valuation (Lp L) t = w.valuation L (P.e QuadraticAlgebra.omega) := by
    simp only [t, map_zpow₀, hπ, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one, neg_neg]
    exact WithZero.exp_log hw0
  have hu1 : Valued.v (cv v (P.Δ / t ^ 2)) = 1 := by
    rw [hval, map_div₀, map_pow, ht, hv, sq]
    exact div_self (mul_ne_zero hw0 hw0)
  have hu2 : Valued.v (cv v (P.Δ / t ^ 2)⁻¹) = 1 := by
    rw [hval, map_inv₀, ← hval, hu1, inv_one]
  have hne : P.Δ / t ^ 2 ≠ 0 := div_ne_zero (by
      intro h0
      apply hδ0
      exact mul_self_eq_zero.mp (by rw [hδ, h0, map_zero])) (pow_ne_zero _ ht0)
  refine ⟨⟨⟨cv v (P.Δ / t ^ 2), le_of_eq hu1⟩, ⟨cv v (P.Δ / t ^ 2)⁻¹, le_of_eq hu2⟩, ?_, ?_⟩,
    cv v t, (map_ne_zero (cv v)).2 ht0, ?_⟩
  · apply Subtype.ext
    show cv v (P.Δ / t ^ 2) * cv v (P.Δ / t ^ 2)⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hne, map_one]
  · apply Subtype.ext
    show cv v (P.Δ / t ^ 2)⁻¹ * cv v (P.Δ / t ^ 2) = 1
    rw [← map_mul, inv_mul_cancel₀ hne, map_one]
  · show cv v P.Δ = cv v (P.Δ / t ^ 2) * cv v t ^ 2
    rw [← map_pow, ← map_mul, div_mul_cancel₀ _ (pow_ne_zero _ ht0)]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.KglIff
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem kgl_iff {L : Type} [Field L] [NumberField L] (w : Plc L) (x : GL (Fin 2) (w.adicCompletion L)) :
    x ∈ GlobalTheory.LFun.KGL w (n := 2) ↔ (∀ i j, x.val i j ∈ w.adicCompletionIntegers L) ∧
      ∀ i j, (x⁻¹).val i j ∈ w.adicCompletionIntegers L :=
  ⟨fun h => ⟨fun i j => GlobalTheory.CptCent.entry_mem_of_mem_GLint' _ h i j,
      fun i j => GlobalTheory.CptCent.entry_mem_of_mem_GLint' _ (inv_mem h) i j⟩,
    fun h => GlobalTheory.CptCent.mem_GLint_of_entries' _ x h.1 h.2⟩

theorem UpperTheory.V.Z.Sym.Dict.Br.okS :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (B : Bridge L), (∀ (g : SA B.Δ) v, (g : DA B.Δ).1 v ∈ KD _ (Ov v) ↔ ∀ w, un w = v → cLoc w (B.bS g : UA L 2) ∈ GlobalTheory.LFun.KGL w (n := 2)) ∧ (∀ (g : SA B.Δ) v, (g : DA B.Δ).1 v = 1 ↔ ∀ w, un w = v → cLoc w (B.bS g : UA L 2) = 1) ∧ ∀ w (S : B.toRingBr.Split w) (g : SA B.Δ), cLoc w (B.bS g : UA L 2) = GeneralLinearGroup.map (S.i : Kv (un w) →+* Kw w) (Sig.eD S.hs ((g : DA B.Δ).1 (un w))) := by
  intro L _ _ _ B
  have loc : ∀ (g : SA B.Δ) (w : Plc L) i j, (cLoc w (B.bS g : UA L 2)).val i j =
      B.ρ _ w rfl (Glob.mt ((g : DA B.Δ).1 (un w)) i j) := fun g w i j => by
    have := B.bS_loc g w
    exact congrFun (congrFun this i) j
  have locI : ∀ (g : SA B.Δ) (w : Plc L) i j, ((cLoc w (B.bS g : UA L 2))⁻¹).val i j =
      B.ρ _ w rfl (Glob.mt ((g : DA B.Δ).1 (un w))⁻¹ i j) := fun g w i j => by
    have h := loc g⁻¹ w i j
    rw [map_inv] at h
    simpa using h
  refine ⟨fun g v => ?_, fun g v => ?_, fun w S g => ?_⟩
  · rw [mem_KD]
    constructor
    · rintro ⟨h1, h2⟩ w rfl
      refine (kgl_iff w _).2 ⟨fun i j => ?_, fun i j => ?_⟩
      · rw [loc]
        exact (B.ρ_int _ _).1 (h1 i j) w rfl
      · rw [locI]
        exact (B.ρ_int _ _).1 (h2 i j) w rfl
    · intro h
      refine ⟨fun i j => (B.ρ_int _ _).2 fun w hw => ?_, fun i j => (B.ρ_int _ _).2 fun w hw => ?_⟩
      · subst hw
        have := ((kgl_iff w _).1 (h w rfl)).1 i j
        rwa [loc] at this
      · subst hw
        have := ((kgl_iff w _).1 (h w rfl)).2 i j
        rwa [locI] at this
  · constructor
    · rintro h w rfl
      apply Units.ext
      refine Matrix.ext fun i j => ?_
      rw [loc, h]
      change B.ρ _ w rfl ((1 : Matrix (Fin 2) (Fin 2) _) i j) = (1 : Matrix (Fin 2) (Fin 2) _) i j
      rcases eq_or_ne i j with rfl | hij
      · simp
      · simp [Matrix.one_apply_ne hij]
    · intro h
      have e : Glob.mt ((g : DA B.Δ).1 v) = 1 := by
        ext1 i j
        rw [← sub_eq_zero]
        refine B.ρ_inj v _ fun w hw => ?_
        subst hw
        have h1 := loc g w i j
        rw [h w rfl] at h1
        rw [map_sub, ← h1]
        change (1 : Matrix (Fin 2) (Fin 2) _) i j - B.ρ _ w rfl ((1 : Matrix (Fin 2) (Fin 2) _) i j) = 0
        rcases eq_or_ne i j with rfl | hij
        · simp
        · simp [Matrix.one_apply_ne hij]
      exact Subtype.ext (Units.ext e)
  · apply Units.ext
    refine Matrix.ext fun i j => ?_
    rw [loc]
    exact S.ρ_eq _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.PhiEx
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Dict.Br.phiEx :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L], ∃ φ : ∀ (v : Pl (Lp L)) (w : Plc L), un w = v → Kv v →+* Kw w, (∀ v w h, Continuous (φ v w h)) ∧ ∀ v w h (a : Lp L), φ v w h (cv v a) = algebraMap L (Kw w) (algebraMap (Lp L) L a) := by
  intro L _ _ _
  have hlo : ∀ (v : Pl (Lp L)) (w : Plc L), un w = v → w.asIdeal.LiesOver v.asIdeal := by
    intro v w h
    subst h
    exact ⟨rfl⟩
  refine ⟨fun v w h => @GroundTheory.Global.SemiLocal.completionMap _ _ _ _ _ _ _ v w (hlo v w h), ?_, ?_⟩
  · intro v w h
    exact @GroundTheory.Global.SemiLocal.continuous_completionMap _ _ _ _ _ _ _ v w (hlo v w h)
  · intro v w h a
    have e := @GroundTheory.Global.SemiLocal.completionMap_algebraMap _ _ _ _ _ _ _ v w (hlo v w h) a
    simp only [cv]
    rw [e]
    exact IsScalarTower.algebraMap_apply (Lp L) L _ a
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.SplitCore
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem exists_adele {L : Type} [Field L] [NumberField L] [IsCMField L] (w : Plc L) (c : Kw w) :
    ∃ a : Af L, pLoc L w a = c ∧ ∀ u : Plc L, u ≠ w → pLoc L u a = 0 := by
  classical
  refine ⟨⟨Function.update (fun _ => 0) w c, ?_⟩, ?_, ?_⟩
  · filter_upwards [(Set.finite_singleton w).compl_mem_cofinite] with u hu
    have hu' : u ≠ w := hu
    simp [Function.update_of_ne hu']
  · show Function.update (fun _ => 0) w c w = c
    simp
  · intro u hu
    show Function.update (fun _ => 0) w c u = 0
    simp [Function.update_of_ne hu]

private theorem decomp {K : Type} [Field K] {D : K} (x : Lsq K D) :
    x = algebraMap K (Lsq K D) x.re + algebraMap K (Lsq K D) x.im * QuadraticAlgebra.omega := by
  ext <;> simp

private theorem omega_sq {K : Type} [Field K] {D : K} :
    (QuadraticAlgebra.omega : Lsq K D) * QuadraticAlgebra.omega = algebraMap K (Lsq K D) D := by
  ext <;> simp

private theorem ne_zero_of_equiv {K M : Type} [Field K] [Field M] {D : K} (e : Lsq K D ≃+* M) : D ≠ 0 := by
  rintro rfl
  have hz : e QuadraticAlgebra.omega * e QuadraticAlgebra.omega = 0 := by
    rw [← map_mul, omega_sq, map_zero, map_zero]
  have hz' : e QuadraticAlgebra.omega = 0 := mul_self_eq_zero.mp hz
  have hz'' : (QuadraticAlgebra.omega : Lsq K 0) = 0 := e.injective (by rw [hz', map_zero])
  have := congrArg QuadraticAlgebra.im hz''
  simp at this

theorem UpperTheory.V.Z.Sym.Dict.Br.splitCore :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (R : RingBr L) (w : Plc L), IsSplitAt w → ∃ (s : Kv (un w)) (hs : s * s = cv (un w) R.Δ) (i : Kv (un w) ≃+* Kw w), s ≠ 0 ∧ ∀ x, R.ρ _ w rfl x = i (Sig.proj hs x) := by
  intro L _ _ _ R w hw
  obtain ⟨u, huw, hu⟩ := hw
  have hu' : un u = un w := hu
  let f : Kv (un w) →+* Kw w := (R.ρ _ w rfl).comp (algebraMap _ _)
  have hf : Function.Injective f := f.injective
  have hdec : ∀ x : Lsq (Kv (un w)) (cv (un w) R.Δ),
      R.ρ _ w rfl x = f x.re + f x.im * R.ρ _ w rfl QuadraticAlgebra.omega := by
    intro x
    conv_lhs => rw [decomp x]
    simp [f]
  obtain ⟨a₁, h₁u, h₁o⟩ := exists_adele u (1 : Kw u)
  obtain ⟨y, hy⟩ := R.ρ_surj (un w) a₁
  have hyw : R.ρ _ w rfl y = 0 := (hy w rfl).trans (h₁o w huw.symm)
  have hyu : R.ρ _ u hu' y = 1 := (hy u hu').trans h₁u
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hyu
  have him : y.im ≠ 0 := by
    intro h0
    apply hy0
    have h1 := hdec y
    rw [hyw, h0, map_zero, zero_mul, add_zero] at h1
    have h2 : y.re = 0 := hf (by rw [← h1, map_zero])
    exact QuadraticAlgebra.ext h2 h0
  have hfim : f y.im ≠ 0 := fun h => him (hf (by rw [h, map_zero]))
  set r := R.ρ _ w rfl QuadraticAlgebra.omega with hr
  let s : Kv (un w) := -y.re / y.im
  have hrs : r = f s := by
    have h1 := hdec y
    rw [hyw] at h1
    simp only [s, map_div₀, map_neg]
    field_simp
    linear_combination -h1
  have hs : s * s = cv (un w) R.Δ := by
    apply hf
    rw [map_mul, ← hrs, hr, ← map_mul, omega_sq]
    rfl
  have hsur : Function.Surjective f := by
    intro c
    obtain ⟨a, hac, -⟩ := exists_adele w c
    obtain ⟨x, hx⟩ := R.ρ_surj (un w) a
    refine ⟨Sig.proj hs x, ?_⟩
    have h1 := hdec x
    rw [hx w rfl, hac, hrs] at h1
    rw [h1]
    simp [Sig.proj, mul_comm]
  refine ⟨s, hs, RingEquiv.ofBijective f ⟨hf, hsur⟩, ?_, ?_⟩
  · intro h0
    apply ne_zero_of_equiv R.e
    have h1 : cv (un w) R.Δ = 0 := by rw [← hs, h0, zero_mul]
    exact (cv (un w)).injective (by rw [h1, map_zero])
  · intro x
    rw [hdec x, hrs]
    show _ = f (Sig.proj hs x)
    simp [Sig.proj, mul_comm]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.IntegralCongrOfForallAbove
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

attribute [-instance] UpperTheory.V.Z.Sym.Glob.rpMul UpperTheory.V.Z.Sym.Glob.rpInv

theorem UpperTheory.V.Z.Sym.Dict.Br.integral_congr_of_forall_above :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (B : Bridge L), ∀ (y : DA B.Δ) (m₀ : ℕ), m₀ ≠ 0 → ∃ m : ℕ, m ≠ 0 ∧ ∀ (g : SA B.Δ) (v : Pl (Lp L)), (∀ w, un w = v → ∀ i j, ∃ a ∈ w.adicCompletionIntegers L, (mL w (B.bS g : UA L 2) - 1) i j = (m : Kw w) * a) → ∀ i j, ∃ a, IsIntegral (Ov v) a ∧ (mt ((y⁻¹ * g * y : DA B.Δ).1 v) - 1) i j = (m₀ : Lsq (Kv v) (cv v B.Δ)) * a := by
  intro L _ _ _ B y m₀ hm₀
  obtain ⟨N₁, hN₁, h₁⟩ := den_DA y
  obtain ⟨N₂, hN₂, h₂⟩ := den_DA y⁻¹
  have hm : m₀ * (N₁ * N₂) ≠ 0 := mul_ne_zero hm₀ (mul_ne_zero hN₁ hN₂)
  refine ⟨m₀ * (N₁ * N₂), hm, fun g v hg i j => ?_⟩
  generalize hmm : m₀ * (N₁ * N₂) = m at hm hg
  haveI : CharZero (Kv v) := charZero_of_injective_algebraMap (algebraMap (Lp L) (Kv v)).injective
  have hmK : (m : Kv v) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hinv : (m : Lsq (Kv v) (cv v B.Δ)) * algebraMap (Kv v) (Lsq (Kv v) (cv v B.Δ)) (m : Kv v)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap (Kv v) (Lsq (Kv v) (cv v B.Δ))), ← map_mul, mul_inv_cancel₀ hmK, map_one]
  have hE : ∀ k l, ∃ b, IsIntegral (Ov v) b ∧
      (mt ((g : DA B.Δ).1 v) - 1) k l = (m : Lsq (Kv v) (cv v B.Δ)) * b := by
    intro k l
    refine ⟨algebraMap (Kv v) _ (m : Kv v)⁻¹ * (mt ((g : DA B.Δ).1 v) - 1) k l, ?_, ?_⟩
    · refine (B.ρ_int v _).2 fun w h => ?_
      subst h
      obtain ⟨a, ha, e⟩ := hg w rfl k l
      rw [B.bS_loc] at e
      have e2 : B.ρ _ w rfl ((mt ((g : DA B.Δ).1 (un w)) - 1) k l) = (m : Kw w) * a := by
        rw [← e]
        simp [Matrix.sub_apply, Matrix.one_apply, apply_ite (B.ρ _ w rfl)]
      have e3 : B.ρ _ w rfl (algebraMap (Kv (un w)) _ (m : Kv (un w))⁻¹) * (m : Kw w) = 1 := by
        rw [← map_natCast (B.ρ _ w rfl), ← map_mul, mul_comm, hinv, map_one]
      rw [map_mul, e2, ← mul_assoc, e3, one_mul]
      exact ha
    · rw [← mul_assoc, hinv, one_mul]
  choose E hE hE' using hE
  have hAB : mt ((y⁻¹ : DA B.Δ).1 v) * mt (y.1 v) = 1 := by
    have h : (y⁻¹ : DA B.Δ).1 v * y.1 v = 1 := inv_mul_cancel (y.1 v)
    exact congrArg Glob.mt h
  have hprod : mt ((y⁻¹ * g * y : DA B.Δ).1 v) = mt ((y⁻¹ : DA B.Δ).1 v) * mt ((g : DA B.Δ).1 v) * mt (y.1 v) := rfl
  refine ⟨∑ k, ∑ l, ((N₂ : Lsq (Kv v) (cv v B.Δ)) * mt ((y⁻¹ : DA B.Δ).1 v) i k) * E k l * ((N₁ : Lsq (Kv v) (cv v B.Δ)) * mt (y.1 v) l j),
    IsIntegral.sum _ fun k _ => IsIntegral.sum _ fun l _ => ((h₂ v i k).mul (hE k l)).mul (h₁ v l j), ?_⟩
  have hsub : mt ((y⁻¹ * g * y : DA B.Δ).1 v) - 1 = mt ((y⁻¹ : DA B.Δ).1 v) * (mt ((g : DA B.Δ).1 v) - 1) * mt (y.1 v) := by
    rw [hprod, mul_sub, sub_mul, mul_one, hAB]
  rw [hsub]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hE', ← hmm]
  push_cast
  ring
end

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Dict.Br.ringEx : RingEx := by
  intro L _ _ _ hU
  obtain ⟨Δ, e, h1, h2, h3⟩ := globEx L
  obtain ⟨φ, h4, h5⟩ := phiEx L
  let P : Pre L := ⟨Δ, e, h1, h2, φ, h4, h5⟩
  refine ⟨⟨Δ, e, h1, h2, h3, fun v hv => ?_, P.rho, rhoGlob L P, fun v x hx => ?_, fun v a => ?_, rhoInt L P, rhoStar L P,
    fun v w h a => ?_⟩⟩
  · obtain ⟨a, b, c, d⟩ := locBase (Lp L) v
    exact ⟨a, b, c, d hv, evenVal L P hU v⟩
  · exact (rhoBij L P v).1 (funext fun w => (hx w.1 w.2).trans (map_zero _).symm)
  · obtain ⟨x, hx⟩ := (rhoBij L P v).2 fun w => pLoc L w.1 a
    exact ⟨x, fun w h => congrFun hx ⟨w, h⟩⟩
  · have : P.rho v w h (algebraMap _ _ a) = P.φ v w h a := by
      change P.φ v w h (algebraMap (Kv v) (Lsq (Kv v) (cv v P.Δ)) a).re + P.φ v w h (algebraMap (Kv v) (Lsq (Kv v) (cv v P.Δ)) a).im * P.rt w = _
      simp
    rw [this]
    exact rhoDiv L P v w h a

theorem UpperTheory.V.Z.Sym.Dict.Br.groupEx : GroupEx := by
  intro L _ _ _ R
  obtain ⟨a, ha⟩ := bGEx L R
  obtain ⟨b, hb⟩ := bSEx L R
  obtain ⟨c, hc, hc'⟩ := rGEx L R
  obtain ⟨d, hd, hd'⟩ := rSEx L R
  exact ⟨⟨R, a, ha, b, hb, c, hc, hc', d, hd, hd'⟩, rfl⟩

theorem UpperTheory.V.Z.Sym.Dict.Br.splitEx (L : Type) [Field L] [NumberField L] [IsCMField L] (R : RingBr L) (w : Plc L)
    (hw : IsSplitAt w) : Nonempty (R.Split w) := by
  obtain ⟨s, hs, i, h0, hρ⟩ := splitCore L R w hw
  have hi : IsoOk i := ⟨fun a => by
    have e : i a = R.ρ _ w rfl (algebraMap _ _ a) := by
      rw [hρ]
      congr 1
      change a = (algebraMap (Kv (un w)) (Lsq (Kv (un w)) (cv (un w) R.Δ)) a).re + s * (algebraMap (Kv (un w)) (Lsq (Kv (un w)) (cv (un w) R.Δ)) a).im
      simp
    rw [← (intsOv L w).2, ← (intsOv (Lp L) (un w)).2, e]
    exact R.ρ_div _ w rfl a⟩
  obtain ⟨v1, v2, v3, v4⟩ := isoVal _ _ i hi
  obtain ⟨j1, j2⟩ := isoJ _ _ i hi
  refine ⟨⟨s, hs, h0, i, hρ, v1, isoAbs _ _ i hi, v2, v4, v3, j1, fun n g => ?_⟩⟩
  rw [← GlobalTheory.HeckeEigConj.KO_eq_KGL]
  exact j2 n g

theorem UpperTheory.V.Z.Sym.Dict.Br.bridgeEx : BridgeEx := by
  intro L _ _ _ hU
  obtain ⟨R⟩ := ringEx L hU
  obtain ⟨B, -⟩ := groupEx L R
  exact ⟨B, splitEx L _, chiEx L _, (okFin L B).1, (okFin L B).2, (okG L B).1, (okG L B).2.1, (okG L B).2.2,
    (okS L B).1, (okS L B).2.1, (okS L B).2.2, okConj L B, integral_congr_of_forall_above L B⟩
