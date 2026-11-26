module

public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartFormalBiext
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatFullLinearLevelStructure
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIdem
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ChartValJ
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueNormalisedPullbackChainRule

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpec
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpec
set_option autoImplicit false
open IsLocalRing

namespace GlobalTheory.PlaceInt

section
variable {V : Type} [CommRing V] [IsLocalRing V]

theorem mem_maximalIdeal_mvPowerSeries_iff {τ : Type} (f : MvPowerSeries τ V) :
    f ∈ maximalIdeal (MvPowerSeries τ V) ↔ MvPowerSeries.constantCoeff f ∈ maximalIdeal V := by
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]

variable [IsNoetherianRing V] [IsAdicComplete (maximalIdeal V) V]

theorem isAdicComplete_mvPowerSeries_finite (τ : Type) [Finite τ] :
    IsAdicComplete (maximalIdeal (MvPowerSeries τ V)) (MvPowerSeries τ V) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin τ

  have ha : MvPowerSeries.HasSubst
      (fun i : Fin n => (MvPowerSeries.X (e.symm i) : MvPowerSeries τ V)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hb : MvPowerSeries.HasSubst
      (fun t : τ => (MvPowerSeries.X (e t) : MvPowerSeries (Fin n) V)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hba : ∀ f : MvPowerSeries (Fin n) V,
      MvPowerSeries.substAlgHom (R := V) hb (MvPowerSeries.substAlgHom (R := V) ha f) = f := by
    intro f
    rw [MvPowerSeries.substAlgHom_comp_substAlgHom_apply]
    have hX : (fun i : Fin n => MvPowerSeries.substAlgHom (R := V) hb
        (MvPowerSeries.X (e.symm i) : MvPowerSeries τ V)) = MvPowerSeries.X := by
      funext i
      rw [MvPowerSeries.substAlgHom_X, Equiv.apply_symm_apply]
    rw [MvPowerSeries.substAlgHom_apply, hX, MvPowerSeries.subst_self, id]
  have hab : ∀ g : MvPowerSeries τ V,
      MvPowerSeries.substAlgHom (R := V) ha (MvPowerSeries.substAlgHom (R := V) hb g) = g := by
    intro g
    rw [MvPowerSeries.substAlgHom_comp_substAlgHom_apply]
    have hX : (fun t : τ => MvPowerSeries.substAlgHom (R := V) ha
        (MvPowerSeries.X (e t) : MvPowerSeries (Fin n) V)) = MvPowerSeries.X := by
      funext t
      rw [MvPowerSeries.substAlgHom_X, Equiv.symm_apply_apply]
    rw [MvPowerSeries.substAlgHom_apply, hX, MvPowerSeries.subst_self, id]
  let E : MvPowerSeries (Fin n) V ≃+* MvPowerSeries τ V :=
    { toFun := MvPowerSeries.substAlgHom (R := V) ha
      invFun := MvPowerSeries.substAlgHom (R := V) hb
      left_inv := hba
      right_inv := hab
      map_mul' := map_mul _
      map_add' := map_add _ }
  have := GlobalTheory.CohenStructure.isAdicComplete_mvPowerSeries V n
  exact GlobalTheory.CohenStructure.isAdicComplete_of_ringEquiv E

variable {σ τ : Type} [Finite σ] [Finite τ]

theorem exists_algHom_evC (a : σ → MvPowerSeries τ V)
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) ∈ maximalIdeal V) :
    ∃ ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V, ∀ j, ψ (MvPowerSeries.X j) = a j := by
  have := isAdicComplete_mvPowerSeries_finite (V := V) τ
  refine (GlobalTheory.mvPowerSeries_eval_of_pow_mem (MvPowerSeries τ V) (maximalIdeal _) σ a
    (fun j => ⟨1, ?_⟩)).1 inferInstance V
  rw [pow_one, mem_maximalIdeal_mvPowerSeries_iff]
  exact ha j

private theorem mvPowerSeries_algHom_ext_of_X_eq (a : σ → MvPowerSeries τ V)
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) ∈ maximalIdeal V)
    (ψ ψ' : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V) (h : ∀ j, ψ (MvPowerSeries.X j) = a j)
    (h' : ∀ j, ψ' (MvPowerSeries.X j) = a j) : ψ = ψ' := by
  have := isAdicComplete_mvPowerSeries_finite (V := V) τ
  have key := (GlobalTheory.mvPowerSeries_eval_of_pow_mem (MvPowerSeries τ V) (maximalIdeal _) σ a
    (fun j => ⟨1, by rw [pow_one, mem_maximalIdeal_mvPowerSeries_iff]; exact ha j⟩)).2
    inferInstance V ψ.toRingHom ψ'.toRingHom
    (fun t => by
      show ψ (MvPowerSeries.C t) = ψ' (MvPowerSeries.C t)
      have hC : (MvPowerSeries.C t : MvPowerSeries σ V) = algebraMap V (MvPowerSeries σ V) t := by
        rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      rw [hC, ψ.commutes, ψ'.commutes]) h h'
  exact AlgHom.ext fun f => RingHom.congr_fun key f

theorem evC_eq_algHom (a : σ → MvPowerSeries τ V)
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) ∈ maximalIdeal V)
    (ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V) (hψ : ∀ j, ψ (MvPowerSeries.X j) = a j)
    (f : MvPowerSeries σ V) : evC a f = ψ f := by
  have h : ∃ φ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V, ∀ j, φ (MvPowerSeries.X j) = a j :=
    ⟨ψ, hψ⟩
  rw [evC, dite_eq_left h, mvPowerSeries_algHom_ext_of_X_eq a ha h.choose ψ h.choose_spec hψ]

theorem constantCoeff_evC_mem (a : σ → MvPowerSeries τ V)
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) ∈ maximalIdeal V) (f : MvPowerSeries σ V)
    (hf : MvPowerSeries.constantCoeff f ∈ maximalIdeal V) :
    MvPowerSeries.constantCoeff (evC a f) ∈ maximalIdeal V := by
  obtain ⟨ψ, hψ⟩ := exists_algHom_evC a ha
  rw [evC_eq_algHom a ha ψ hψ f]

  let χ₁ : MvPowerSeries σ V →+* ResidueField V :=
    (residue V).comp (MvPowerSeries.constantCoeff.comp ψ.toRingHom)
  let χ₂ : MvPowerSeries σ V →+* ResidueField V := (residue V).comp MvPowerSeries.constantCoeff
  have hC : ∀ t : V, ψ (MvPowerSeries.C t) = MvPowerSeries.C t := fun t => by
    have := ψ.commutes t
    rwa [MvPowerSeries.algebraMap_apply, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply] at this
  have key := (GlobalTheory.mvPowerSeries_eval_of_pow_mem (ResidueField V) ⊥ σ (fun _ => 0)
    (fun _ => ⟨1, by simp⟩)).2 inferInstance V χ₁ χ₂
    (fun t => by simp [χ₁, χ₂, hC])
    (fun j => by
      simp only [χ₁, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hψ]
      exact (residue_eq_zero_iff _).2 (ha j))
    (fun j => by simp [χ₂])
  have hf' := RingHom.congr_fun key f
  simp only [χ₁, χ₂, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hf'
  rw [← residue_eq_zero_iff, hf']
  exact (residue_eq_zero_iff _).2 hf

end

theorem evC_spec : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (σ τ ρ : Type) [Finite σ] [Finite τ] [Finite ρ] (a : σ → MvPowerSeries τ V), (∀ j, MvPowerSeries.constantCoeff (a j) ∈ maximalIdeal V) → (∃ ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V, (∀ j, ψ (MvPowerSeries.X j) = a j) ∧ ∀ f, evC a f = ψ f) ∧ (∀ f, MvPowerSeries.constantCoeff f ∈ maximalIdeal V → MvPowerSeries.constantCoeff (evC a f) ∈ maximalIdeal V) ∧ ((∀ j, MvPowerSeries.constantCoeff (a j) = 0) → ∀ f, evC a f = MvPowerSeries.subst a f) ∧ ∀ b : τ → MvPowerSeries ρ V, (∀ j, MvPowerSeries.constantCoeff (b j) ∈ maximalIdeal V) → ∀ f, evC b (evC a f) = evC (fun j => evC b (a j)) f := by
  intro V _ _ _ _ _ σ τ ρ _ _ _ a ha
  refine ⟨?_, fun f hf => constantCoeff_evC_mem a ha f hf, ?_, ?_⟩
  · obtain ⟨ψ, hψ⟩ := exists_algHom_evC a ha
    exact ⟨ψ, hψ, fun f => evC_eq_algHom a ha ψ hψ f⟩
  · intro h0 f
    have hs : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero h0
    rw [evC_eq_algHom a ha (MvPowerSeries.substAlgHom (R := V) hs)
      (fun j => MvPowerSeries.substAlgHom_X hs j) f]
    exact MvPowerSeries.substAlgHom_apply hs f
  · intro b hb f
    obtain ⟨ψa, hψa⟩ := exists_algHom_evC a ha
    obtain ⟨ψb, hψb⟩ := exists_algHom_evC b hb
    have hc : ∀ j, MvPowerSeries.constantCoeff (evC b (a j)) ∈ maximalIdeal V :=
      fun j => constantCoeff_evC_mem b hb (a j) (ha j)

    rw [evC_eq_algHom (fun j => evC b (a j)) hc (ψb.comp ψa)
      (fun j => by rw [AlgHom.comp_apply, hψa, evC_eq_algHom b hb ψb hψb]) f,
      evC_eq_algHom a ha ψa hψa, evC_eq_algHom b hb ψb hψb, AlgHom.comp_apply]

end GlobalTheory.PlaceInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpecStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeriesSubstConstTerms_local_algHom_spec : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (σ τ ρ : Type) [Finite σ] [Finite τ] [Finite ρ] (a : σ → MvPowerSeries τ V), (∀ j, MvPowerSeries.constantCoeff (a j) ∈ maximalIdeal V) → (∃ ψ : MvPowerSeries σ V →ₐ[V] MvPowerSeries τ V, (∀ j, ψ (MvPowerSeries.X j) = a j) ∧ ∀ f, evC a f = ψ f) ∧ (∀ f, MvPowerSeries.constantCoeff f ∈ maximalIdeal V → MvPowerSeries.constantCoeff (evC a f) ∈ maximalIdeal V) ∧ ((∀ j, MvPowerSeries.constantCoeff (a j) = 0) → ∀ f, evC a f = MvPowerSeries.subst a f) ∧ ∀ b : τ → MvPowerSeries ρ V, (∀ j, MvPowerSeries.constantCoeff (b j) ∈ maximalIdeal V) → ∀ f, evC b (evC a f) = evC (fun j => evC b (a j)) f := by
  first | exact @GlobalTheory.PlaceInt.evC_spec | exact GlobalTheory.PlaceInt.evC_spec | (intros; apply GlobalTheory.PlaceInt.evC_spec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsCdvrFiniteExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceExtField

open IsDedekindDomain

section Val

variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']

theorem vV_unit (u : Vˣ) : vV V (algebraMap V K' u) = 0 := by
  have : valV V (algebraMap V K' u) = 1 := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h u.isUnit
  simp [vV, this]

theorem vV_pow {x : K'} (hx : x ≠ 0) (n : ℕ) : vV V (x ^ n) = n * vV V x := by
  simp [vV]

theorem vV_pos {a : V} (ha : a ≠ 0) (hu : ¬ IsUnit a) : 0 < vV V (algebraMap V K' a) := by
  have h0 : algebraMap V K' a ≠ 0 := by simpa using ha
  have : valV V (algebraMap V K' a) < 1 := by
    rw [valV, HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hu
  have := (WithZero.log_lt_log (valV_ne_zero (V := V) h0) one_ne_zero).2 this
  simp only [vV]; simp at this; omega

theorem vV_irr {a : V} (ha : Irreducible a) : vV V (algebraMap V K' a) = 1 := by
  have : valV V (algebraMap V K' a) = WithZero.exp (-1 : ℤ) := by
    rw [valV, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_singleton _ ha.ne_zero ha.maximalIdeal_eq
  simp [vV, this]

theorem exists_index {V' K'' : Type} [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] [Field K'']
    [Algebra V' K''] [IsFractionRing V' K''] (j : V →+* V') [IsLocalHom j] (i : K' →+* K'')
    (hi : ∀ v, i (algebraMap V K' v) = algebraMap V' K'' (j v)) :
    ∃ r : ℕ, 0 < r ∧ ∀ x, vV V' (i x) = (r : ℤ) * vV V x := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible V
  have inj : ∀ v, v ≠ 0 → algebraMap V' K'' (j v) ≠ 0 := fun v hv => by
    rw [← hi]; simpa using hv
  have pos : 0 < vV V' (algebraMap V' K'' (j p)) :=
    vV_pos (fun h => inj p hp.ne_zero (by simp [h])) (fun h => hp.not_isUnit (isUnit_of_map_unit j p h))
  obtain ⟨r, hr⟩ := Int.eq_ofNat_of_zero_le pos.le
  have key : ∀ v : V, v ≠ 0 → vV V' (i (algebraMap V K' v)) = (r : ℤ) * vV V (algebraMap V K' v) := by
    intro v hv
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hv hp
    have h1 : algebraMap V K' p ≠ 0 := by simpa using hp.ne_zero
    have h2 : algebraMap V K' u ≠ 0 := by simp
    rw [hi, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow,
      vV_mul (inj _ u.ne_zero) (pow_ne_zero _ (inj p hp.ne_zero)), vV_mul h2 (pow_ne_zero _ h1),
      vV_pow (inj p hp.ne_zero), vV_pow h1, vV_unit, vV_irr hp, hr]
    have := vV_unit (K' := K'') (Units.map j.toMonoidHom u)
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at this
    rw [this]; ring
  refine ⟨r, by omega, fun x => ?_⟩
  by_cases hx : x = 0
  · simp [hx, vV]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hx
  have hb1 : algebraMap V K' b ≠ 0 := by simpa using hb0
  have e : algebraMap V K' a / algebraMap V K' b * algebraMap V K' b = algebraMap V K' a := div_mul_cancel₀ _ hb1
  have e1 := vV_mul (V := V) hx hb1
  have e2 := vV_mul (V := V') ((map_ne_zero i).2 hx) ((map_ne_zero i).2 hb1)
  rw [← map_mul, e, key a ha0, key b hb0] at e2
  rw [e] at e1
  rw [e1] at e2
  linarith

end Val

theorem exists_cdvr_finite_extension : ∀ (T : CDVR) (L : Type) [Field L] [Algebra T.Fr L] [FiniteDimensional T.Fr L], ∃ (T' : CDVR) (iT : T.Fr →+* T'.Fr) (e : ℕ) (ψ : L ≃+* T'.Fr) (φ : T.V →+* T'.V), 0 < e ∧ (∀ a : T.Fr, vV T'.V (iT a) = (e : ℤ) * vV T.V a) ∧ (∀ a, ψ (algebraMap T.Fr L a) = iT a) ∧ (∀ a, algebraMap T'.V T'.Fr (φ a) = iT (algebraMap T.V T.Fr a)) ∧ (T.FinRes → T'.FinRes) := by
  intro T L _ _ _
  haveI : CharZero T.Fr := algebraRat.charZero _
  obtain ⟨W, _, _, _, _, _, _, _, hc, hfin, hinj, hloc, -, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension T.V T.Fr L
  haveI : CharZero W := charZero_of_injective_algebraMap hinj
  let T' : CDVR := { V := W }
  let ψ : L ≃+* FractionRing W := (FractionRing.algEquiv W L).symm.toRingEquiv
  let iT : T.Fr →+* FractionRing W := ψ.toRingHom.comp (algebraMap T.Fr L)
  have hφ : ∀ a, iT (algebraMap T.V T.Fr a) = algebraMap W (FractionRing W) (algebraMap T.V W a) := by
    intro a
    have h1 : algebraMap T.Fr L (algebraMap T.V T.Fr a) = algebraMap W L (algebraMap T.V W a) :=
      (RingHom.congr_fun hc a).symm
    change (FractionRing.algEquiv W L).symm (algebraMap T.Fr L (algebraMap T.V T.Fr a)) = _
    rw [h1, AlgEquiv.commutes]
  obtain ⟨e, he, hv⟩ := exists_index (algebraMap T.V W) iT hφ
  refine ⟨T', iT, e, ψ, algebraMap T.V W, he, hv, fun a => rfl, fun a => (hφ a).symm, fun h => ?_⟩
  haveI : Finite (ResidueField T.V) := h
  exact Module.finite_of_finite (ResidueField T.V) (M := ResidueField W)

end GlobalTheory.PlaceExtField
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralChartFormalBiextensionGaugeBound
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralChartFormalBiextensionGaugeBound
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.ChartBiext

theorem constantCoeff_gauge {R K O : Type} [CommRing R] [CommRing K] [Algebra ℚ K] [Algebra R K] [CommRing O] [StarRing O]
    {d : ℕ} (B : FB R d O) {h : PS K 2 d} (hh : B.IsCanonGauge K h) : MvPowerSeries.constantCoeff h = 0 := by
  have hz : ∀ p : Fin 2 × Fin d,
      MvPowerSeries.constantCoeff ((![0, pt K d 0] : Fin 2 → Pt K 1 d) p.1 p.2) = 0 := by
    rintro ⟨i, j⟩
    fin_cases i <;> simp [pt]
  have hsub := MvPowerSeries.hasSubst_of_constantCoeff_zero hz
  set c := MvPowerSeries.constantCoeff h with hc
  have hdec : h = MvPowerSeries.C c + (h - MvPowerSeries.C c) := by ring
  have hrest : MvPowerSeries.constantCoeff (h - MvPowerSeries.C c) = 0 := by simp [hc]
  have key := congrArg MvPowerSeries.constantCoeff hh.ax0
  rw [ev, hdec, MvPowerSeries.subst_add hsub, map_add (f := _),
    MvPowerSeries.constantCoeff_subst_eq_zero hsub hz hrest] at key
  simpa using key

theorem toK_self {K : Type} [CommRing K] {σ : Type} (f : MvPowerSeries σ K) :
    MvPowerSeries.map (algebraMap K K) f = f := by
  ext m
  simp

theorem nabValN_congr {R R' K O : Type} [CommRing R] [CommRing R'] [CommRing K] [Algebra ℚ K] [Algebra R K] [Algebra R' K]
    [CommRing O] [StarRing O] {d : ℕ} (B : FB R d O) (B' : FB R' d O) (hF : B.FK K = B'.FK K)
    (hA : ∀ a, B.actK K a = B'.actK K a) (h : PS K 2 d) (w0 : O) (m : ℕ) {n : ℕ} (f : PS K n d) {Ix : Type} [Fintype Ix]
    (cp : Ix → Fin n) (u : Ix → Fin d → K) (P : MvPolynomial Ix K) :
    nabValN B K h w0 m f cp u P = nabValN B' K h w0 m f cp u P := by
  simp only [nabValN, FB.hL, hF, hA]

end GlobalTheory.ChartBiext


open GlobalTheory.ChartBiext in
theorem GlobalTheory.PlaceInt.integralBiext_gauge_eig_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), ∃ B : FB T.V (chD C.ch) (𝓞 E), IsBT C B ∧ ∀ B : FB T.V (chD C.ch) (𝓞 E), IsBT C B → B.IsCanonGauge T.Fr (gaugeOf C) ∧ MvPowerSeries.constantCoeff (gaugeOf C) = 0 ∧ (letI := io.toAlgebra; (∀ (ℓ : Lt1 Dw) (a : 𝓞 E), (dAct T.Fr B a).mulVec (C.ch.uvec ℓ) = io (embK c ℓ.1 a) • C.ch.uvec ℓ) ∧ ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ChBound C e ρ w n → ∀ (k : ℕ) (P : MvPolynomial (LtN Dw n) T.Fr), P ∈ FFV (Dw := Dw) T w n → ∀ g : PS T.V n (chD C.ch), ((-ρ : ℝ) : EReal) ≤ nval T.V e (nabValN B T.Fr (gaugeOf C) H.w0 k (FB.toK T.Fr g) (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) P)) := by
  intro E _ _ _ H Dw l Xo c inst hstar T io y C

  have hinst : inst = H.starRing := by
    cases inst with
    | @mk toStarMul star_add =>
      cases toStarMul with
      | @mk toInvolutiveStar star_mul =>
        cases toInvolutiveStar with
        | @mk toStar star_involutive =>
          cases toStar with
          | @mk s =>
            have hs : s = fun a => H.bar a := funext hstar
            subst hs
            rfl
  subst hinst
  letI : StarRing (𝓞 E) := H.starRing
  obtain ⟨BT, hF, hA, h1, h2, hs, had, hK⟩ := GlobalTheory.integralChart_formalBiext E H Dw l Xo c T io y C
  obtain ⟨hFK, hAK, hG, hC⟩ := hK T.Fr
  refine ⟨BT, ⟨hF, hA, h1, h2, hs, had⟩, ?_⟩
  intro B hB
  obtain ⟨hBF, hBA, hB1, hB2, hBs, hBa⟩ := hB

  have eFK : B.FK T.Fr = BT.FK T.Fr := by
    funext i
    show MvPowerSeries.map _ (B.G.F i) = MvPowerSeries.map _ (BT.G.F i)
    rw [hBF, hF]
  have eAK : ∀ a, B.actK T.Fr a = BT.actK T.Fr a := by
    intro a
    funext i
    show MvPowerSeries.map _ (B.A.act a i) = MvPowerSeries.map _ (BT.A.act a i)
    rw [hBA, hA]
  have hgB : B.IsCanonGauge T.Fr (gaugeOf C) ↔ BT.IsCanonGauge T.Fr (gaugeOf C) :=
    GlobalTheory.FBDescent.gauge_iff B BT T.Fr eFK eAK (by rw [hB1, h1]) (by rw [hB2, h2]) (by rw [hBs, hs])
      (fun a => by rw [hBa, had]) (gaugeOf C)
  have hgT : BT.IsCanonGauge T.Fr (gaugeOf C) := by
    rw [GlobalTheory.ChartBiext.toK_self] at hC
    exact (hG _).2 hC
  have hgauge : B.IsCanonGauge T.Fr (gaugeOf C) := hgB.2 hgT
  refine ⟨hgauge, GlobalTheory.ChartBiext.constantCoeff_gauge B hgauge, ?_⟩
  letI := io.toAlgebra
  have eFK' : B.FK T.Fr = C.ch.B.FK T.Fr := eFK.trans hFK
  have eAK' : ∀ a, B.actK T.Fr a = C.ch.B.actK T.Fr a := fun a => (eAK a).trans (hAK a)
  refine ⟨fun ℓ a => ?_, ?_⟩
  ·
    have hd : dAct T.Fr B a = dAct T.Fr C.ch.B a := by
      unfold dAct
      rw [eAK' a]
    rw [hd]
    exact GlobalTheory.PowGerm.eigDirSt E H Dw l Xo c T io y C a ℓ
  · intro e ρ w n hb k P hP g
    have hint : IsIntPS T (FB.toK T.Fr g) := fun m =>
      ⟨MvPowerSeries.coeff m g, by simp [FB.toK, MvPowerSeries.coeff_map]⟩
    have hle : nuLocC C e k w n ≤ nval T.V e (nabValN C.ch.B T.Fr C.ch.h H.w0 k (FB.toK T.Fr g)
        (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) P) := by
      unfold nuLocC
      exact iInf₂_le_of_le P hP (iInf₂_le (FB.toK T.Fr g) hint)
    rw [GlobalTheory.ChartBiext.nabValN_congr B C.ch.B eFK' eAK']
    exact (hb k).trans hle
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralChartFormalBiextensionGaugeBoundStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralChart_formalBiextension_gauge_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), ∃ B : FB T.V (chD C.ch) (𝓞 E), IsBT C B ∧ ∀ B : FB T.V (chD C.ch) (𝓞 E), IsBT C B → B.IsCanonGauge T.Fr (gaugeOf C) ∧ MvPowerSeries.constantCoeff (gaugeOf C) = 0 ∧ (letI := io.toAlgebra; (∀ (ℓ : Lt1 Dw) (a : 𝓞 E), (dAct T.Fr B a).mulVec (C.ch.uvec ℓ) = io (embK c ℓ.1 a) • C.ch.uvec ℓ) ∧ ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ChBound C e ρ w n → ∀ (k : ℕ) (P : MvPolynomial (LtN Dw n) T.Fr), P ∈ FFV (Dw := Dw) T w n → ∀ g : PS T.V n (chD C.ch), ((-ρ : ℝ) : EReal) ≤ nval T.V e (nabValN B T.Fr (gaugeOf C) H.w0 k (FB.toK T.Fr g) (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) P)) := by
  first | exact @GlobalTheory.PlaceInt.integralBiext_gauge_eig_bound | exact GlobalTheory.PlaceInt.integralBiext_gauge_eig_bound | (intros; apply GlobalTheory.PlaceInt.integralBiext_gauge_eig_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TorsionRationalOverFiniteExtensionLevelStructure
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TorsionRationalOverFiniteExtensionLevelStructure
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory

namespace TorsionRat

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem sp_epi {K L : Type} [Field K] [Field L] (i : K →+* L) : Epi (spMap i) := by
  have : Flat (spMap i) := by
    letI := i.toAlgebra
    exact HasRingHomProperty.Spec_iff.2 (inferInstance : Module.Flat K L)
  have : Surjective (spMap i) := ⟨fun x => ⟨(⊥ : PrimeSpectrum L), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem exists_finset_of_field {K F : Type} [Field K] [Field F] [Algebra K F] {Y : Scheme.{0}} (s : Y ⟶ Sp K)
    [LocallyOfFiniteType s] (p : Sp F ⟶ Y) (hp : p ≫ s = spMap (algebraMap K F)) :
    ∃ S : Finset F, ∀ L : IntermediateField K F, (S : Set F) ⊆ L →
      ∃ q : Sp L ⟶ Y, spMap (algebraMap L F) ≫ q = p := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hpt, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (p (IsLocalRing.closedPoint F))) isOpen_univ
  have hU : IsAffineOpen U := hU
  obtain ⟨f, hf⟩ : ∃ f : Γ(Y, U) ⟶ CommRingCat.of F, Spec.map f ≫ hU.fromSpec = p := by
    refine ⟨Spec.preimage (IsOpenImmersion.lift hU.fromSpec p ?_), ?_⟩
    · rintro _ ⟨y, rfl⟩
      rw [hU.range_fromSpec, Subsingleton.elim (α := PrimeSpectrum F) y (IsLocalRing.closedPoint F)]
      exact hpt
    · rw [Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _
  obtain ⟨g, hg⟩ : ∃ g : CommRingCat.of K ⟶ Γ(Y, U), Spec.map g = hU.fromSpec ≫ s :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  have hgf : g ≫ f = CommRingCat.ofHom (algebraMap K F) :=
    Spec.map_injective (by
      rw [Spec.map_comp, hg, ← Category.assoc, hf]
      exact hp)
  have hV : ∀ r : K, f.hom (g.hom r) = algebraMap K F r := fun r => congrArg (fun q => q.hom r) hgf
  have hft : g.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map g) := by rw [hg]; infer_instance
    exact HasRingHomProperty.Spec_iff.1 this
  let _ : Algebra K Γ(Y, U) := g.hom.toAlgebra
  obtain ⟨t, ht⟩ := (show Algebra.FiniteType K Γ(Y, U) from hft).out
  refine ⟨t.image f.hom, fun L hL => ?_⟩
  have hr : ∀ a, f.hom a ∈ L := fun a => by
    have ha : a ∈ Algebra.adjoin K (t : Set Γ(Y, U)) := ht ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact hL (Finset.mem_image_of_mem _ hx)
    | algebraMap r => exact (hV r).symm ▸ L.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  let f' : Γ(Y, U) ⟶ CommRingCat.of L := CommRingCat.ofHom (f.hom.codRestrict L hr)
  refine ⟨Spec.map f' ≫ hU.fromSpec, ?_⟩
  change Spec.map _ ≫ Spec.map f' ≫ hU.fromSpec = _
  rw [← hf, ← Spec.map_comp_assoc]
  rfl

theorem exists_finset_over {K F : Type} [Field K] [Field F] [Algebra K F] {X : Scheme.{0}} (G : Over X)
    [LocallyOfFiniteType G.hom] (x : Sp K ⟶ X) (p : Over.mk (spMap (algebraMap K F) ≫ x) ⟶ G) :
    ∃ S : Finset F, ∀ L : IntermediateField K F, (S : Set F) ⊆ L →
      ∃ q : Over.mk (spMap (algebraMap K L) ≫ x) ⟶ G, spMap (algebraMap L F) ≫ q.left = p.left := by
  obtain ⟨S, hS⟩ := exists_finset_of_field (pullback.snd G.hom x)
    (pullback.lift p.left (spMap (algebraMap K F)) (Over.w p)) (pullback.lift_snd _ _ _)
  refine ⟨S, fun L hL => ?_⟩
  obtain ⟨q, hq⟩ := hS L hL
  have h1 : spMap (algebraMap L F) ≫ q ≫ pullback.fst G.hom x = p.left := by
    rw [← Category.assoc, hq]; exact pullback.lift_fst _ _ _
  refine ⟨Over.homMk (q ≫ pullback.fst G.hom x) ?_, h1⟩
  haveI := sp_epi (algebraMap L F)
  rw [← cancel_epi (spMap (algebraMap L F))]
  change spMap (algebraMap L F) ≫ (q ≫ pullback.fst G.hom x) ≫ G.hom =
    spMap (algebraMap L F) ≫ spMap (algebraMap K L) ≫ x
  rw [← Category.assoc, h1, ← Category.assoc, sp_comp]
  exact Over.w p

theorem comp_injective {X : Scheme.{0}} {G : Over X} {K L : Type} [Field K] [Field L] {x : Sp K ⟶ X} {y : Sp L ⟶ X}
    (ψ : K →+* L) (g : Over.mk y ⟶ Over.mk x) (hg : g.left = spMap ψ) {a b : Over.mk x ⟶ G}
    (h : g ≫ a = g ≫ b) : a = b := by
  haveI := sp_epi ψ
  have h' : spMap ψ ≫ a.left = spMap ψ ≫ b.left := hg ▸ congrArg CommaMorphism.left h
  exact Over.OverMorphism.ext ((cancel_epi _).1 h')

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem exists_level_of_isAlgClosed (Xo : Moduli Dw l) {K : Type} [Field K] [IsAlgClosed K] (x : Sp K ⟶ Xo.X)
    {M : ℕ} (hM : 0 < M) :
    ∃ ev : Dw.La → (ptO Xo x ⟶ Xo.univ.t.G), (∀ a b, ev (a + b) = ev a * ev b) ∧
      (∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ Xo.univ.t.act.act o) ∧ (∀ a, ev a = 1 ↔ Dw.ModN M a) ∧
      ∀ w : ptO Xo x ⟶ Xo.univ.t.G, w ^ M = 1 ↔ ∃ a, ev a = w := by
  obtain ⟨β, hβ⟩ := Spec.map_surjective (x ≫ Xo.s)
  obtain ⟨-, I, -⟩ := Xo.univ.geom K x β.hom hβ.symm
  exact ⟨I.ev M, I.add M, I.lin M, I.ker M hM, I.onto M hM⟩

theorem exists_enum (Xo : Moduli Dw l) {M : ℕ} (hM : 0 < M) :
    ∃ (J : Type) (_ : Finite J), ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Xo.X),
      ∃ u : J → (ptO Xo x ⟶ Xo.univ.t.G), Function.Injective u ∧ ∀ w, w ^ M = 1 ↔ ∃ j, u j = w := by
  obtain ⟨J, _, π, r, hr, hπ⟩ := LevelFlat.exists_finite_quotient Dw M hM
  refine ⟨J, inferInstance, fun K _ _ x => ?_⟩
  obtain ⟨ev, hadd, -, hker, honto⟩ := exists_level_of_isAlgClosed Xo x hM
  have hI : ∀ a b, ev a = ev b ↔ π a = π b := fun a b => by
    have h : ev a = ev (a - b) * ev b := by rw [← hadd, sub_add_cancel]
    rw [hπ, h, mul_eq_right, hker]
  refine ⟨fun j => ev (r j), fun i j hij => ?_, fun w => (honto w).trans ⟨?_, ?_⟩⟩
  · have := (hI _ _).1 hij
    rwa [hr, hr] at this
  · rintro ⟨a, rfl⟩
    exact ⟨π a, (hI _ _).2 (hr _)⟩
  · rintro ⟨j, rfl⟩
    exact ⟨_, rfl⟩

theorem exists_eq_comp_of_isAlgClosed (Xo : Moduli Dw l) {M : ℕ} (hM : 0 < M) {K L : Type} [Field K] [Field L]
    [IsAlgClosed K] [IsAlgClosed L] {x : Sp K ⟶ Xo.X} {y : Sp L ⟶ Xo.X} (ψ : K →+* L) (g : ptO Xo y ⟶ ptO Xo x)
    (hg : g.left = spMap ψ) (w : ptO Xo y ⟶ Xo.univ.t.G) (hw : w ^ M = 1) :
    ∃ a : ptO Xo x ⟶ Xo.univ.t.G, a ^ M = 1 ∧ g ≫ a = w := by
  obtain ⟨J, _, hJ⟩ := exists_enum Xo hM
  obtain ⟨u, hu, hu'⟩ := hJ K x
  obtain ⟨v, -, hv'⟩ := hJ L y
  have hp : ∀ j, u j ^ M = 1 := fun j => (hu' _).2 ⟨j, rfl⟩
  choose τ hτ using fun j => (hv' (g ≫ u j)).1 (by rw [← MonObj.comp_pow, hp, MonObj.comp_one])
  have hτi : Function.Injective τ := fun i j hij =>
    hu (comp_injective ψ g hg (by rw [← hτ, ← hτ, hij]))
  obtain ⟨j, rfl⟩ := (hv' w).1 hw
  obtain ⟨i, rfl⟩ := Finite.surjective_of_injective hτi j
  exact ⟨u i, hp i, (hτ i).symm⟩

theorem allRat_of_isAlgClosure (Xo : Moduli Dw l) {M : ℕ} (hM : 0 < M) {L F : Type} [Field L] [Field F] [Algebra L F]
    [IsAlgClosed F] [Algebra.IsAlgebraic L F] (x : Sp L ⟶ Xo.X) (y : Sp F ⟶ Xo.X)
    (hy : spMap (algebraMap L F) ≫ x = y)
    (h : ∀ w : ptO Xo y ⟶ Xo.univ.t.G, w ^ M = 1 →
      ∃ a : ptO Xo x ⟶ Xo.univ.t.G, spMap (algebraMap L F) ≫ a.left = w.left) : AllRat Xo x M := by
  intro Ω _ ψ w hw
  let Ω' := AlgebraicClosure Ω
  let i : Ω →+* Ω' := algebraMap Ω Ω'
  letI : Algebra L Ω' := (i.comp ψ).toAlgebra
  let σ : F →ₐ[L] Ω' := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hσ : (σ : F →+* Ω').comp (algebraMap L F) = i.comp ψ := σ.comp_algebraMap
  let g₁ : ptO Xo (spMap i ≫ spMap ψ ≫ x) ⟶ ptO Xo (spMap ψ ≫ x) := Over.homMk (spMap i) rfl
  let g₂ : ptO Xo (spMap i ≫ spMap ψ ≫ x) ⟶ ptO Xo y := Over.homMk (spMap (σ : F →+* Ω')) (by
    change spMap (σ : F →+* Ω') ≫ y = spMap i ≫ spMap ψ ≫ x
    rw [← hy, ← Category.assoc, ← Category.assoc, sp_comp, sp_comp, hσ])
  obtain ⟨b, hb, hb'⟩ := exists_eq_comp_of_isAlgClosed Xo hM (σ : F →+* Ω') g₂ rfl (g₁ ≫ w)
    (by rw [← MonObj.comp_pow, hw, MonObj.comp_one])
  obtain ⟨a, ha⟩ := h b hb
  refine ⟨a, ?_⟩
  haveI := sp_epi i
  have h1 : spMap (σ : F →+* Ω') ≫ b.left = spMap i ≫ w.left := congrArg CommaMorphism.left hb'
  refine (cancel_epi (spMap i)).1 (h1.symm.trans ?_)
  rw [← ha, ← Category.assoc, ← Category.assoc, sp_comp, sp_comp, hσ]

theorem exists_finite_allRat (Xo : Moduli Dw l) {K : Type} [Field K] (x : Sp K ⟶ Xo.X) {M : ℕ} (hM : 0 < M) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L), FiniteDimensional K L ∧
      AllRat Xo (spMap (algebraMap K L) ≫ x) M := by
  let F := AlgebraicClosure K
  haveI := Xo.univ.proper
  obtain ⟨J, _, hJ⟩ := exists_enum Xo hM
  obtain ⟨u, -, hu⟩ := hJ F (spMap (algebraMap K F) ≫ x)
  choose S hS using fun j => exists_finset_over Xo.univ.t.G x (u j)
  let s : Set F := ⋃ j, (S j : Set F)
  haveI : Finite s := (Set.finite_iUnion fun j => (S j).finite_toSet).to_subtype
  let L := IntermediateField.adjoin K s
  refine ⟨L, inferInstance, inferInstance,
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral, ?_⟩
  refine allRat_of_isAlgClosure Xo hM (F := F) _ (spMap (algebraMap K F) ≫ x) ?_ fun w hw => ?_
  · rw [← Category.assoc, sp_comp]
    rfl
  · obtain ⟨j, rfl⟩ := (hu w).1 hw
    exact hS j L ((Set.subset_iUnion (fun j => (S j : Set F)) j).trans (IntermediateField.subset_adjoin _ _))

theorem allRat_baseChange (Xo : Moduli Dw l) {K : Type} [Field K] {x : Sp K ⟶ Xo.X} {M : ℕ} (h : AllRat Xo x M)
    (L : Type) [Field L] (ψ : K →+* L) : AllRat Xo (spMap ψ ≫ x) M := by
  have key : ∀ (Ω : Type) [Field Ω] (ψ : K →+* Ω) (y : Sp Ω ⟶ Xo.X), y = spMap ψ ≫ x →
      ∀ w : ptO Xo y ⟶ Xo.univ.t.G, w ^ M = 1 → ∃ a : ptO Xo x ⟶ Xo.univ.t.G, w.left = spMap ψ ≫ a.left := by
    intro Ω _ ψ y hy
    subst hy
    exact h Ω ψ
  intro Ω _ χ w hw
  obtain ⟨a, ha⟩ := key Ω (χ.comp ψ) _ (by rw [← Category.assoc, sp_comp]) w hw
  let g' : ptO Xo (spMap ψ ≫ x) ⟶ ptO Xo x := Over.homMk (spMap ψ) rfl
  have h1 : (g' ≫ a).left = spMap ψ ≫ a.left := rfl
  refine ⟨g' ≫ a, ha.trans ?_⟩
  exact (congrArg (· ≫ a.left) (sp_comp ψ χ).symm).trans
    ((Category.assoc _ _ _).trans (congrArg (spMap χ ≫ ·) h1.symm))

theorem exists_level_of_allRat (Xo : Moduli Dw l) {K : Type} [Field K] {x : Sp K ⟶ Xo.X} {M : ℕ} (hM : 0 < M)
    (h : AllRat Xo x M) :
    ∃ ev : Dw.La → (ptO Xo x ⟶ Xo.univ.t.G), (∀ a b, ev (a + b) = ev a * ev b) ∧
      (∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ Xo.univ.t.act.act o) ∧ (∀ a, ev a = 1 ↔ Dw.ModN M a) ∧
      ∀ w : ptO Xo x ⟶ Xo.univ.t.G, w ^ M = 1 → ∃ a, ev a = w := by
  let F := AlgebraicClosure K
  let ψ : K →+* F := algebraMap K F
  let g : ptO Xo (spMap ψ ≫ x) ⟶ ptO Xo x := Over.homMk (spMap ψ) rfl
  have inj : ∀ {a b : ptO Xo x ⟶ Xo.univ.t.G}, g ≫ a = g ≫ b → a = b := fun h => comp_injective ψ g rfl h
  obtain ⟨ev, hadd, hlin, hker, honto⟩ := exists_level_of_isAlgClosed Xo (spMap ψ ≫ x) hM
  choose e he using fun a => h F ψ (ev a) ((honto _).2 ⟨a, rfl⟩)
  have he' : ∀ a, g ≫ e a = ev a := fun a => Over.OverMorphism.ext (he a).symm
  refine ⟨e, fun a b => inj ?_, fun o a => inj ?_, fun a => ?_, fun w hw => ?_⟩
  · rw [MonObj.comp_mul, he', he', he', hadd]
  · rw [← Category.assoc, he', he', hlin]
  · rw [← hker, ← he']
    exact ⟨fun h1 => by rw [h1, MonObj.comp_one], fun h1 => inj (by rw [h1, MonObj.comp_one])⟩
  · obtain ⟨a, ha⟩ := (honto (g ≫ w)).1 (by rw [← MonObj.comp_pow, hw, MonObj.comp_one])
    exact ⟨a, inj ((he' a).trans ha)⟩

end TorsionRat


open TorsionRat in
theorem torsion_rational_over_finite_extension :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X) (M : ℕ), 0 < M → (∃ (L : Type) (_ : Field L) (_ : Algebra K L), FiniteDimensional K L ∧ AllRat Xo (spMap (algebraMap K L) ≫ x) M) ∧ (AllRat Xo x M → (∀ (L : Type) [Field L] (ψ : K →+* L), AllRat Xo (spMap ψ ≫ x) M) ∧ ∃ ev : Dw.La → (ptO Xo x ⟶ Xo.univ.t.G), (∀ a b, ev (a + b) = ev a * ev b) ∧ (∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ Xo.univ.t.act.act o) ∧ (∀ a, ev a = 1 ↔ Dw.ModN M a) ∧ ∀ w : (ptO Xo x ⟶ Xo.univ.t.G), w ^ M = 1 → ∃ a, ev a = w) :=
  fun _ _ _ _ _ _ _ Xo _ _ x _ hM =>
    ⟨exists_finite_allRat Xo x hM, fun h => ⟨fun L _ ψ => allRat_baseChange Xo h L ψ, exists_level_of_allRat Xo hM h⟩⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TorsionRationalOverFiniteExtensionLevelStructureStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_rational_over_finite_extension_level_structure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X) (M : ℕ), 0 < M → (∃ (L : Type) (_ : Field L) (_ : Algebra K L), FiniteDimensional K L ∧ AllRat Xo (spMap (algebraMap K L) ≫ x) M) ∧ (AllRat Xo x M → (∀ (L : Type) [Field L] (ψ : K →+* L), AllRat Xo (spMap ψ ≫ x) M) ∧ ∃ ev : Dw.La → (ptO Xo x ⟶ Xo.univ.t.G), (∀ a b, ev (a + b) = ev a * ev b) ∧ (∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ Xo.univ.t.act.act o) ∧ (∀ a, ev a = 1 ↔ Dw.ModN M a) ∧ ∀ w : (ptO Xo x ⟶ Xo.univ.t.G), w ^ M = 1 → ∃ a, ev a = w) := by
  first | exact @GlobalTheory.torsion_rational_over_finite_extension | exact GlobalTheory.torsion_rational_over_finite_extension | (intros; apply GlobalTheory.torsion_rational_over_finite_extension <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HostFieldGaloisDegreeDiscrConjMovesPrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HostFieldGaloisDegreeDiscrConjMovesPrimes
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open Formalism.BasicNotions Formalism.MainNotions IsDedekindDomain
open scoped Pointwise

namespace GlobalTheory.PlaceInt

theorem host_bar_eq_smul (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (x : 𝓞 D.host.E) :
    H.bar x = D.host.conj • x := by
  apply RingOfIntegers.ext
  let φ : D.host.E →+* ℂ := Classical.choice inferInstance
  apply φ.injective
  rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]
  exact (D.host.conjE_apply φ x).symm

theorem host_galois_discr_moves : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E), IsGalois ℚ D.host.E ∧ Module.finrank ℚ D.host.E = 4 * D.R.ord ∧ (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr D.host.E → p ∣ D.host.condN) ∧ ∀ p ∈ D.host.condN.primeFactors, p.Prime ∧ ∀ 𝔭 : Ideal (𝓞 D.host.E), 𝔭.IsPrime → (p : 𝓞 D.host.E) ∈ 𝔭 → ∃ x ∈ 𝔭, H.bar x ∉ 𝔭 := by
  intro D H
  refine ⟨D.host.galois, D.host.der.finrank_E, D.host.der.discr_primes.1, ?_⟩
  · intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    refine ⟨hpp, fun P hP hmem => ?_⟩
    by_contra hall
    push Not at hall
    have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hpp).irreducible
    have hlo : P.LiesOver (Ideal.span {(p : ℤ)}) := by
      refine ⟨hmax.eq_of_le (Ideal.IsPrime.under ℤ P).ne_top ?_⟩
      rw [Ideal.span_le, Set.singleton_subset_iff]
      show algebraMap ℤ (𝓞 D.host.E) (p : ℤ) ∈ P
      rw [map_natCast]
      exact hmem
    have hbb : ∀ x : 𝓞 D.host.E, H.bar (H.bar x) = x := fun x => by
      apply RingOfIntegers.ext
      rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]
    refine D.host.der.decompConj p hpp (Nat.dvd_of_mem_primeFactors hp) P ?_
    rw [MulAction.mem_stabilizer_iff]
    ext x
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    have hinv : (D.host.conj)⁻¹ • x = H.bar x := by
      rw [inv_smul_eq_iff, ← host_bar_eq_smul D H, hbb]
    rw [hinv]
    refine ⟨fun h => ?_, hall x⟩
    have := hall _ h
    rwa [hbb] at this

end GlobalTheory.PlaceInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HostFieldGaloisDegreeDiscrConjMovesPrimesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open Formalism.BasicNotions Formalism.MainNotions IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hostField_galois_degree_discr_conj_moves_primes : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E), IsGalois ℚ D.host.E ∧ Module.finrank ℚ D.host.E = 4 * D.R.ord ∧ (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr D.host.E → p ∣ D.host.condN) ∧ ∀ p ∈ D.host.condN.primeFactors, p.Prime ∧ ∀ 𝔭 : Ideal (𝓞 D.host.E), 𝔭.IsPrime → (p : 𝓞 D.host.E) ∈ 𝔭 → ∃ x ∈ 𝔭, H.bar x ∉ 𝔭 := by
  first | exact @GlobalTheory.PlaceInt.host_galois_discr_moves | exact GlobalTheory.PlaceInt.host_galois_discr_moves | (intros; apply GlobalTheory.PlaceInt.host_galois_discr_moves <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TotalDegreeLeOfRowDeg
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

set_option autoImplicit false

namespace GlobalTheory.PlaceInt

theorem span_mul_prod_of_eq {E T : Type} [Field E] [Fintype T] {F F' : IntermediateField ℚ ℂ} (h : F' = F)
    (A B : Set E) (f : T → E →+* F) (f' : T → E →+* F')
    (hf : ∀ τ x, f' τ x = IntermediateField.equivOfEq h.symm (f τ x)) (m : T → ℕ) (β : F)
    (hβ : Submodule.span (𝓞 F) {β} * ∏ τ, Submodule.span (𝓞 F) (f τ '' A) ^ m τ =
      ∏ τ, Submodule.span (𝓞 F) (f τ '' B) ^ m τ) :
    Submodule.span (𝓞 F') {IntermediateField.equivOfEq h.symm β} * ∏ τ, Submodule.span (𝓞 F') (f' τ '' A) ^ m τ =
      ∏ τ, Submodule.span (𝓞 F') (f' τ '' B) ^ m τ := by
  subst h
  have hff : f' = f := funext fun τ => RingHom.ext fun x => hf τ x
  subst hff
  exact hβ

theorem totalDegree_le_of_rowDeg {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ) {k : Type} [Field k] (a : T → ℕ → ℕ)
    (P : MvPolynomial (Letter T r n) k) (hP : RowDeg r n k a P) :
    P.totalDegree ≤ ∑ τ, ∑ i : Fin (r τ), a τ i := by
  unfold MvPolynomial.totalDegree
  refine Finset.sup_le fun m hm => le_of_eq ?_
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => hP m hm σ i

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n)

theorem eF_embF (τ : E →+* ℂ) (x : E) : d.eF (embF c τ x) = embF d.c₂ τ x := by
  exact Subtype.ext rfl

theorem map_eF_mem_symO (Λ : GenLat E n) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ symO c Λ) :
    MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P ∈ symO (Dw := Dw) d.c₂ Λ := by
  have key : symO c Λ ≤ (symO (Dw := Dw) d.c₂ Λ).comap (MvPolynomial.map (d.eF : c.F →+* d.c₂.F)) := by
    refine Subring.closure_le.2 ?_
    rintro f (⟨o, rfl⟩ | ⟨σ, i, b, hb, rfl⟩)
    · refine Subring.mem_comap.2 (Subring.subset_closure (Or.inl ⟨⟨d.eF o, ?_⟩, ?_⟩))
      · exact o.2.map (d.eF : c.F →+* d.c₂.F).toIntAlgHom
      · rw [MvPolynomial.map_C]
        rfl
    · refine Subring.mem_comap.2 (Subring.subset_closure (Or.inr ⟨σ, i, b, hb, ?_⟩))
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [letB, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, RingHom.coe_coe, eF_embF]
  exact key hP

end

theorem eF_transfer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (Λ : GenLat E n), (∀ β : c.F, BetaIs (Dw := Dw) c Λ β → BetaIs (Dw := Dw) d.c₂ Λ (d.eF β)) ∧ (∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ w → MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P ∈ harmL d.c₂ Λ w ∧ P.totalDegree ≤ Formalism.L2.Pj.DF Dw w) ∧ ∀ (w : (E →+* ℂ) × ℕ → ℕ) (α : 𝓞 E), d.eF (nrm Dw c w α) = nrm Dw d.c₂ w α := by
  intro E _ _ _ H Dw l Xo c n d Λ
  refine ⟨?_, ?_, ?_⟩
  · intro β hβ
    unfold BetaIs idealAt at hβ ⊢
    exact span_mul_prod_of_eq d.hF (detSet Λ.La) (detSet Λ.Ln) (fun τ => embF c τ) (fun τ => embF d.c₂ τ)
      (fun τ x => (eF_embF d τ x).symm) Dw.mult β hβ
  · intro w P hP
    obtain ⟨hH, hS⟩ := hP
    refine ⟨⟨GlobalTheory.map_mem_HHa Dw.mult n (d.eF : c.F →+* d.c₂.F) d.eF.surjective ComplexEmbedding.conjugate
      (InPsi H) (fun τ i => w (τ, i)) P hH, map_eF_mem_symO d Λ P hS⟩, ?_⟩
    exact totalDegree_le_of_rowDeg Dw.mult n (fun τ i => w (τ, i)) P hH.2.2
  · intro w α
    simp only [nrm, embK, map_prod, map_pow, RingHom.comp_apply, eF_embF]

end GlobalTheory.PlaceInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueChainRuleNormalizedPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueChainRuleNormalizedPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlaceInt

theorem hv_pulls : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (S : Type) [Field S] [Algebra c.F S] (y : FrPt Xo c S) (a : 𝓞 E) (N k k' : ℕ), a * H.bar a = (N : 𝓞 E) → k' = k * N → ∀ (n : ℕ) (F : Fin n → SecN Xo y.x k) (F' : Fin n → SecN Xo y.x k'), (∀ b, Pulls Xo a (F b) (F' b)) → ∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HH c w n → hv Xo c nab y k' F' P = algebraMap c.F S (nrm Dw c w a) * hv Xo c nab y k F P := by
  intro E _ _ _ H Dw l Xo c inst hstar nab hnab S _ _ y a N k k' haN hk n F F' hF w P hP
  have e : inst = H.starRing := GlobalTheory.PowGerm.starRing_ext_of_star _ _ (fun x => (hstar x).trans rfl)
  subst e

  obtain ⟨⟨b, hbM⟩, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 c.F)) P.support
    (fun m => P.coeff m)
  have hb0 : algebraMap (𝓞 c.F) c.F b ≠ 0 := by
    intro h0
    exact nonZeroDivisors.ne_zero hbM ((IsFractionRing.injective (𝓞 c.F) c.F) (by rw [h0, map_zero]))

  have hsmul : ∀ (k0 : ℕ) (G : Fin n → SecN Xo y.x k0),
      hv Xo c nab y k0 G (algebraMap (𝓞 c.F) c.F b • P) =
        algebraMap c.F S (algebraMap (𝓞 c.F) c.F b) * hv Xo c nab y k0 G P := by
    intro k0 G
    unfold hv
    rw [MvPolynomial.support_smul_eq hb0, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [MvPolynomial.coeff_smul, smul_eq_mul, map_mul, _root_.mul_assoc]

  have hQ : algebraMap (𝓞 c.F) c.F b • P ∈ harmA c w n := by
    unfold HH HHa at hP
    obtain ⟨h1, h2, h3⟩ := hP
    refine ⟨⟨Submodule.smul_mem _ _ h1, fun σ i i' hi t => by rw [map_smul, h2 σ i i' hi t],
      fun m hm σ i => h3 m (MvPolynomial.support_smul hm) σ i⟩, fun m => ?_⟩
    rw [MvPolynomial.coeff_smul, smul_eq_mul]
    by_cases hm : m ∈ P.support
    · obtain ⟨r, hr⟩ := hb m hm
      have hr' : algebraMap (𝓞 c.F) c.F r = algebraMap (𝓞 c.F) c.F b * P.coeff m := by
        rw [hr, Algebra.smul_def]
      rw [← hr']
      exact r.2
    · rw [MvPolynomial.notMem_support_iff.mp hm, mul_zero]
      exact Subring.zero_mem _
  have key : hv Xo c nab y k' F' (algebraMap (𝓞 c.F) c.F b • P) =
      algebraMap c.F S (nrm Dw c w a) * hv Xo c nab y k F (algebraMap (𝓞 c.F) c.F b • P) :=
    GlobalTheory.T.harmonic_value_normalised_pullback_chain_rule E H Dw l Xo c nab hnab S y a N k (k' : ℤ) (by rw [hstar]; exact haN)
      (by exact_mod_cast hk) n F F' (fun i => hF i) w _ hQ
  rw [hsmul, hsmul, _root_.mul_left_comm] at key
  exact mul_left_cancel₀ ((map_ne_zero _).mpr hb0) key
end GlobalTheory.PlaceInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueChainRuleNormalizedPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonic_value_chain_rule_normalized_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (S : Type) [Field S] [Algebra c.F S] (y : FrPt Xo c S) (a : 𝓞 E) (N k k' : ℕ), a * H.bar a = (N : 𝓞 E) → k' = k * N → ∀ (n : ℕ) (F : Fin n → SecN Xo y.x k) (F' : Fin n → SecN Xo y.x k'), (∀ b, Pulls Xo a (F b) (F' b)) → ∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HH c w n → hv Xo c nab y k' F' P = algebraMap c.F S (nrm Dw c w a) * hv Xo c nab y k F P := by
  first | exact @GlobalTheory.PlaceInt.hv_pulls | exact GlobalTheory.PlaceInt.hv_pulls | (intros; apply GlobalTheory.PlaceInt.hv_pulls <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CardFunLevQ
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem GlobalTheory.PlaceInt.card_fun_levQ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (n : ℕ), Nat.card (Fin n → LevQ Dw l) = l.M ^ (Module.finrank ℚ E / 2 * (Dw.p + Dw.q) * n) := by
  intro E _ _ _ H Dw l n
  rw [Nat.card_fun, (GlobalTheory.card_levQ E H Dw l).2, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul]
  rfl
end
