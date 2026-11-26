module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FixedUnr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.SubquotientSupport.FixedDvd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.ExtraV

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self UpperTheory.V.UnitaryThreeInertia.Coef.isLocalRing

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevDefs
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Af.Bc UpperTheory.V.Br
namespace UpperTheory.V.Lev
def FixedDvdAlt : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (n M : ℕ), 1 ≤ M →
    ∀ (w : HeightOneSpectrum (𝓞 F)), (M : 𝓞 F) ∈ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (rc : IrrGL (k := w.adicCompletion F) → WD h), _root_.UpperTheory.Zero.LLC.IsRecT h rc → ∀ σ : SmIrr (GL (Fin n) (w.adicCompletion F)),
      (∀ s : ↥(Ine (F := F) A), (∀ ζ : Ω, ζ ^ M = 1 → (s : G F Ω) ζ = ζ) →
        (rc (algNorm σ)).charPol (ineIncl h s) = (X - 1) ^ n) → HasFixed σ.ρ (KLoc F w n M)
def FixedUnrAlt : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (n : ℕ)
    (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (k := w.adicCompletion F) → WD h), _root_.UpperTheory.Zero.LLC.IsRecT h rc → ∀ (σ : SmIrr (GL (Fin n) (w.adicCompletion F)))
    (μ : Fin n → ↥(Weil h) →* ℂˣ), (∀ s, (rc (algNorm σ)).charPol s = ∏ i, (X - C (μ i s : ℂ))) →
    (∀ i (s : ↥(Ine (F := F) A)), μ i (ineIncl h s) = 1) →
    GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SmGL.iwahori (w.adicCompletion F) (Fin n)) ≠ ⊥ ∧
      ((∀ i j, ∃ s, (μ i s : ℂ) ≠ ((normV w : ℕ) : ℂ) ^ deg s * μ j s) → GlobalTheory.SmGL.IsSpherical σ.ρ)
def FixedSsAlt : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n M : ℕ), 1 ≤ M → ∀ (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : Induces Bw) (κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ),
      FlagAt M m r A κ → IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := F) A).subtype) →
      ∀ (rc : IrrGL (k := w.adicCompletion F) → WD h), _root_.UpperTheory.Zero.LLC.IsRecT h rc → ∀ σ : SmIrr (GL (Fin n) (w.adicCompletion F)),
      (IsAbPol n (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := F) A).subtype)) →
        ∀ s, (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := F) A).subtype)).charPol s = (rc (algNorm σ)).charPol s) →
      (l ∣ M ∨ (∀ i j, κ i ≠ κ j * (cycBar F Ω l).comp (Dec (F := F) A).subtype) ∨
        (GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SmGL.iwahori (w.adicCompletion F) (Fin n)) ≠ ⊥ → GlobalTheory.SmGL.IsSpherical σ.ρ)) →
      HasFixed σ.ρ (KLoc F w n M)
end UpperTheory.V.Lev
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EqOneOfDvd
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevFixedUnr
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
end
abbrev _root_.UpperTheory.V.Lev.fixedUnr_s_ty : Prop :=
    _root_.UpperTheory.V.Af.Hypotheses' → _root_.UpperTheory.V.Lev.FixedUnrAlt
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem eq_one_of_dvd {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (hf : f.IsSemisimple) {n : ℕ} (hd : f.charpoly ∣ (X - C 1) ^ n) : f = 1 := by
  obtain ⟨q, hq⟩ := hd
  have h0 := congrArg (Polynomial.aeval f) hq
  rw [map_mul, LinearMap.aeval_self_charpoly, zero_mul, map_pow, map_sub, Polynomial.aeval_X,
    Polynomial.aeval_C] at h0
  have hs : (f - algebraMap ℂ (Module.End ℂ V) 1).IsSemisimple :=
    Module.End.isSemisimple_sub_algebraMap_iff.2 hf
  have := sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h0⟩ hs)
  rwa [map_one] at this
section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
private theorem link {n m : ℕ} (b : WDRep h (Fin m → ℂ)) (μ : Fin n → Weil h →* ℂˣ)
    (hp : ∀ s, (b.ρ s).charpoly = ∏ i, (X - C (μ i s : ℂ))) (hN : b.N ≠ 0) :
    ∃ i j, (μ i (frob h) : ℂ) = ((normV w : ℕ) : ℂ) * μ j (frob h) := by
  have hs := b.semisimple (frob h)
  have htop : ⨆ c, Module.End.eigenspace (b.ρ (frob h)) c = ⊤ := by
    have h1 := Module.End.iSup_maxGenEigenspace_eq_top (b.ρ (frob h))
    simpa only [hs.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] using h1
  obtain ⟨c, v, hv, hNv⟩ : ∃ c v, v ∈ Module.End.eigenspace (b.ρ (frob h)) c ∧ b.N v ≠ 0 := by
    by_contra hc
    push_neg at hc
    refine hN (LinearMap.ker_eq_top.1 (top_le_iff.1 ?_))
    rw [← htop]
    exact iSup_le fun c v hv => hc c v hv
  have hfv : b.ρ (frob h) v = c • v := Module.End.mem_eigenspace_iff.1 hv
  have hv0 : v ≠ 0 := fun e => hNv (by rw [e, map_zero])
  have root : ∀ z u, u ≠ 0 → b.ρ (frob h) u = z • u → ∃ i, z = (μ i (frob h) : ℂ) := fun z u hu e => by
    have h1 : Module.End.HasEigenvalue (b.ρ (frob h)) z :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 e, hu⟩
    have h2 := Module.End.hasEigenvalue_iff_isRoot_charpoly _ _ |>.1 h1
    rw [hp, Polynomial.IsRoot.def, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h2
    obtain ⟨i, -, hi⟩ := h2
    exact ⟨i, by simpa [sub_eq_zero] using hi⟩
  have hc2 : b.ρ (frob h) (b.N v) = (((normV w : ℕ) : ℂ) * c) • b.N v := by
    rw [b.comm_apply, deg_frob, zpow_one, hfv, map_smul, smul_smul]
  obtain ⟨j, hj⟩ := root _ _ hv0 hfv
  obtain ⟨i, hi⟩ := root _ _ hNv hc2
  exact ⟨i, j, by rw [← hi, ← hj]⟩
private theorem link_all {n : ℕ} (μ : Fin n → Weil h →* ℂˣ) (hu : ∀ i (s : Ine (F := E) A), μ i (ineIncl h s) = 1)
    {i j : Fin n} (e : (μ i (frob h) : ℂ) = ((normV w : ℕ) : ℂ) * μ j (frob h)) (s : Weil h) :
    (μ i s : ℂ) = ((normV w : ℕ) : ℂ) ^ deg s * μ j s := by
  obtain ⟨t, ht⟩ := exists_eq_zpow_mul (deg_frob (h := h)) s
  have hv : ∀ k, (μ k s : ℂ) = (μ k (frob h) : ℂ) ^ deg s := fun k => by
    conv_lhs => rw [ht]
    rw [map_mul, map_zpow, hu, mul_one, Units.val_zpow_eq_zpow_val]
  rw [hv, hv, e, mul_zpow]
end
theorem UpperTheory.V.Z.Win.T2.fixedUnr_alt :
    _root_.UpperTheory.V.Lev.fixedUnr_s_ty := by
  intro P F Ω _ _ _ _ _ n w A h rc hrc σ μ hp hu
  obtain ⟨a, ha, ε, H⟩ := _root_.UpperTheory.V.Z.Win.toV' hrc
  haveI : CharZero (w.adicCompletion F) := algebraRat.charZero _
  have hine : ∀ t : Ine (F := F) A, (rc (algNorm σ)).charPol (ineIncl h t) = (X - C 1) ^ n := fun t => by
    rw [hp]
    simp [hu]
  constructor
  · have hfx : fixed (algNorm σ).rep (iwahori (w.adicCompletion F) (Fin (algNorm σ).1)) ≠ ⊥ := by
      refine UnramSupport.fixed_iwahori_ne_bot P.litN.loc.geo P.litN.loc.zel P.litN.loc.bz _ _ _ _
        (algNorm σ).2.rep.smooth (algNorm σ).2.rep.irr fun s hs y hy => ?_
      have hyc : y.IsCusp := hs.isCusp hy
      obtain ⟨m, b, hb, hirr⟩ := id ((H.cusp y).1 hyc)
      have hN : b.N = 0 := by
        have h0 := TemperedRec.monodromy_zero_of_irreducible_weilDeligne F Ω A w h (rc y) ((H.cusp y).1 hyc)
        rwa [← hb, WD.monodromyZero_ofWeilDeligneRepClass_iff] at h0
      have hI : ∀ t : Ine (F := F) A, b.ρ (ineIncl h t) = 1 := fun t => by
        refine eq_one_of_dvd _ (b.semisimple _) (n := n) ?_
        rw [← WD.charPol_mk, hb, ← hine t, H.supp _ s hs]
        exact Multiset.dvd_prod (Multiset.mem_map_of_mem (fun y => (rc y).charPol (ineIncl h t)) hy)
      have hunr : (rc y).unr := by
        rw [← hb, WD.unr_mk]
        exact ⟨hN, hI⟩
      exact isUnramChar_of_isCusp_of_isSpherical P.litN.loc.geo P.litN.loc.bz P.litN.loc.zel _ y hyc
        ((H.sph y).2 hunr)
    have hfx' : fixed (IrrGL.of σ.ρ σ.smooth σ.irred).rep (iwahori (w.adicCompletion F) (Fin n)) ≠ ⊥ :=
      GlobalTheory.AboveL.IwaFix.fixed_iwahori_ne_bot_of_twist _
        ((IrrGL.of σ.ρ σ.smooth σ.irred).twEquiv _ (isSmoothChar_absPow _)) hfx
    exact fixed_ne_bot_of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm hfx'
  · intro hne
    obtain ⟨m, b, hb⟩ := (rc (algNorm σ)).exists_rep
    have hpb : ∀ s, (b.ρ s).charpoly = ∏ i, (X - C (μ i s : ℂ)) := fun s => by
      rw [← WD.charPol_mk, hb]
      exact hp s
    have hN : b.N = 0 := by
      by_contra h0
      obtain ⟨i, j, e⟩ := link b μ hpb h0
      obtain ⟨s, hs⟩ := hne i j
      exact hs (link_all μ hu e s)
    have hunr : (rc (algNorm σ)).unr := by
      rw [← hb, WD.unr_mk]
      refine ⟨hN, fun t => eq_one_of_dvd _ (b.semisimple _) (n := n) ?_⟩
      rw [← WD.charPol_mk, hb, hine t]
    obtain ⟨v, hv0, hv⟩ := UpperTheory.hasFixed_of_algNorm_fixed_ne_bot F w n σ _ le_rfl ((H.sph _).2 hunr)
    exact (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.Parabolic.mem_fixed.2 hv, hv0⟩
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.FixedDvd
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevFixedDvd
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
abbrev _root_.UpperTheory.V.Lev.fixedDvd_s_ty : Prop :=
    _root_.UpperTheory.V.Af.Hypotheses' → _root_.UpperTheory.V.Lev.FixedDvdAlt
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem UpperTheory.V.Z.Win.T2.eq_one_of_charpoly_dvd {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (hf : f.IsSemisimple) {n : ℕ} (hd : f.charpoly ∣ (Polynomial.X - 1) ^ n) : f = 1 := by
  obtain ⟨q, hq⟩ := hd
  have h0 := congrArg (Polynomial.aeval f) hq
  rw [map_mul, LinearMap.aeval_self_charpoly, zero_mul, map_pow, map_sub, Polynomial.aeval_X,
    map_one] at h0
  have hs : (f - algebraMap ℂ (Module.End ℂ V) 1).IsSemisimple :=
    Module.End.isSemisimple_sub_algebraMap_iff.2 hf
  rw [map_one] at hs
  exact sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h0⟩ hs)
private theorem UpperTheory.V.Z.Win.T2.char_of_dvd {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (M n : ℕ) (hM : 1 ≤ M) (x z : WD h)
    (hx : ∀ s : ↥(Ine (F := F) A), (∀ ζ : Ω, ζ ^ M = 1 → (s : G F Ω) ζ = ζ) →
      x.charPol (ineIncl h s) = (Polynomial.X - 1) ^ n)
    (hz : IsIrrWD z) (hd : ∀ σ, z.charPol σ ∣ x.charPol σ) :
    ∃ (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ), z = WD.lpOfChar h ξ hξ ∧
      ∀ s : ↥(Ine (F := F) A), (∀ ζ : Ω, ζ ^ M = 1 → (s : G F Ω) ζ = ζ) → ξ (ineIncl h s) = 1 := by
  obtain ⟨m, b, rfl, hb⟩ := hz
  have key : ∀ s : ↥(Ine (F := F) A), (∀ ζ : Ω, ζ ^ M = 1 → (s : G F Ω) ζ = ζ) →
      b.ρ (ineIncl h s) = 1 := by
    intro s hs
    have h2 := hd (ineIncl h s)
    rw [hx s hs, WD.charPol_mk] at h2
    exact UpperTheory.V.Z.Win.T2.eq_one_of_charpoly_dvd _ (b.semisimple _) h2
  obtain ⟨ξ, hξ, h1, h2⟩ := UpperTheory.irreducible_weilDeligne_tame_level_eq_character F Ω w A h M hM m b hb key
  exact ⟨ξ, hξ, h1, fun s hs => h2 _ (key s hs)⟩
private theorem UpperTheory.V.Z.Win.T2.val_lt_one {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) {M : ℕ}
    (hw : (M : 𝓞 F) ∈ w.asIdeal) : valuation (w.adicCompletion F) (M : w.adicCompletion F) < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [(isEquiv (valuation (w.adicCompletion F))
    (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ)))).lt_one_iff_lt_one]
  have h : Valued.v (((algebraMap (𝓞 F) F (M : 𝓞 F) : F)) : w.adicCompletion F) =
      w.valuation F (algebraMap (𝓞 F) F (M : 𝓞 F)) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  have h2 : w.valuation F (algebraMap (𝓞 F) F (M : 𝓞 F)) < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem w _).mpr hw
  rw [← h] at h2
  have e : (((algebraMap (𝓞 F) F (M : 𝓞 F) : F)) : w.adicCompletion F) = ((M : ℕ) : w.adicCompletion F) := by
    rw [map_natCast]
    exact map_natCast (algebraMap F (w.adicCompletion F)) M
  rwa [e] at h2
private theorem UpperTheory.V.Z.Win.T2.good_ofChar {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (χ : kˣ →* ℂˣ) (hχ : GlobalTheory.SmGL.IsSmoothChar χ) :
    UpperTheory.Zero.LLC.Good (IrrGL.ofChar χ hχ) :=
  ⟨{IrrGL.ofChar χ hχ}, hasSupport_self (IrrGL.isCusp_ofChar χ hχ), fun y hy => by
    rw [Multiset.mem_singleton.1 hy]
    exact Or.inl rfl⟩
theorem UpperTheory.V.Z.Win.T2.fixedDvd' :
    _root_.UpperTheory.V.Lev.fixedDvd_s_ty := by
  intro P F Ω _ _ _ _ _ n M hM w hw A h rc hrc σ hL
  obtain ⟨a, ha, ε, H⟩ := _root_.UpperTheory.V.Z.Win.toV' hrc
  have hv : valuation (w.adicCompletion F) (M : w.adicCompletion F) < 1 := UpperTheory.V.Z.Win.T2.val_lt_one w hw
  have hM0 : (M : w.adicCompletion F) ≠ 0 := by
    rw [← map_natCast (algebraMap F (w.adicCompletion F)), map_ne_zero]
    exact Nat.cast_ne_zero.2 (by omega)
  have hu0 : uniformizer (w.adicCompletion F) ≠ 0 := by simp
  have hv0 : valuation (w.adicCompletion F) (M : w.adicCompletion F) ≠ 0 := by simpa using hM0
  let γ : (ValueGroupWithZero (w.adicCompletion F))ˣ :=
    Units.mk0 (valuation _ (M : w.adicCompletion F) / uniformizer (w.adicCompletion F)) (div_ne_zero hv0 hu0)
  have hlt : ∀ x : ValueGroupWithZero (w.adicCompletion F),
      x < γ ↔ x ≤ valuation _ (M : w.adicCompletion F) := fun x => by
    show x < _ / _ ↔ _
    rw [lt_div_iff₀ (zero_lt_iff.2 hu0)]
    refine ⟨fun h1 => not_lt.1 fun h2 => h1.not_ge ?_, fun h1 => (mul_le_mul_left h1 _).trans_lt
      (mul_lt_of_lt_one_right (zero_lt_iff.2 hv0) uniformizer_lt_one)⟩
    have hx : 0 < x := (zero_lt_iff.2 hv0).trans h2
    rwa [← div_le_iff₀' hx, le_uniformizer_iff, div_lt_one₀ hx]
  have hγ : γ ≤ 1 := by
    show _ / _ ≤ (1 : ValueGroupWithZero (w.adicCompletion F))
    rw [div_le_one₀ (zero_lt_iff.2 hu0), le_uniformizer_iff]
    exact hv
  obtain ⟨s, hs⟩ := GlobalTheory.LocGL.SupportRing.exists_hasSupport P.litN.loc.zel (algNorm σ)
  have hch : ∀ y ∈ s, ∃ χ hχ, y = IrrGL.ofChar χ hχ ∧ ∀ u : (w.adicCompletion F)ˣ,
      valuation (w.adicCompletion F) ((u : w.adicCompletion F) - 1) < γ → χ u = 1 := fun y hy => by
    obtain ⟨ξ, hξ, e, hξ1⟩ := UpperTheory.V.Z.Win.T2.char_of_dvd w A h M n hM _ (rc y) hL ((H.cusp y).1 (hs.isCusp hy)) fun τ => by
      rw [H.supp _ s hs τ]
      exact Multiset.dvd_prod (Multiset.mem_map_of_mem (fun y => (rc y).charPol τ) hy)
    obtain ⟨χ, hχ, rfl⟩ := ha.factor ξ hξ
    refine ⟨χ, hχ, H.inj _ _ (UpperTheory.V.Z.Win.T2.good_ofChar χ hχ) (e.trans (H.one χ hχ).symm), fun u hu => ?_⟩
    obtain ⟨τ, rfl⟩ := ha.surj u
    have h1 : valuation (w.adicCompletion F) (a τ : w.adicCompletion F) = 1 := by
      have := (valuation (w.adicCompletion F)).map_one_add_of_lt (hu.trans_le (Units.val_le_val.2 hγ))
      simpa using this
    obtain ⟨h2, h3⟩ := UpperTheory.inertia_fixes_roots_of_unity_of_artin_congruence P.litN.aut.art F Ω w A h a ha M hM τ h1 ((hlt _).1 hu)
    exact hξ1 ⟨τ, h2⟩ h3
  have hne := UpperTheory.jacquet_borel_nontrivial_of_character_support P.litN.loc.geo P.litN.loc.zel _ _ _ (algNorm σ).rep s hs fun y hy => by
    obtain ⟨χ, hχ, rfl, -⟩ := hch y hy
    rfl
  obtain ⟨y, hy0, hy⟩ := UpperTheory.jacquet_borel_exists_torus_congruence_fixed P.litN.loc.geo P.litN.loc.zel _ _ _ (algNorm σ).rep s γ hγ hs hch hne
  have hf := UpperTheory.fixed_congruence_ne_bot_of_jacquet_torus_fixed _ _ _ (algNorm σ).rep γ hγ
    ((P.litN.loc.bz _).1 _ _ _ (algNorm σ).2.rep.smooth (algNorm σ).2.rep.irr) y hy0 hy
  refine UpperTheory.hasFixed_of_algNorm_fixed_ne_bot F w n σ _ (fun g hg => (UpperTheory.mem_maximalCompact_and_congruent_of_mem_principalCongruence F w n M g hg).1) ?_
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hf
  exact (Submodule.ne_bot_iff _).2 ⟨v, fun g => hv ⟨g.1, fun i j => (hlt _).2 ((UpperTheory.mem_maximalCompact_and_congruent_of_mem_principalCongruence F w n M g.1 g.2).2 i j)⟩, hv0⟩
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevFixedSs
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.V.Lev.fixed_semisimple_of_flag_fixed_dvd_fixed_unramified :
    UpperTheory.V.Lev.FlagPol → _root_.UpperTheory.V.Lev.FixedDvdAlt → _root_.UpperTheory.V.Lev.FixedUnrAlt → _root_.UpperTheory.V.Lev.FixedSsAlt := by
  intro hP hD hU F Ω _ _ _ _ _ l _ ι n M hM m r hr w A h O _ _ _ Bw hj κ hF hst rc hrc σ hc hor
  obtain ⟨μ, hμ, hI, hG⟩ := hP F Ω l ι n M hM m r hr w A h O Bw hj κ hF hst
  have hpol : ∀ s, (rc (GlobalTheory.GalOfCusp.algNorm σ)).charPol s = ∏ i, (X - C (μ i s : ℂ)) := fun s => by
    rw [← hc ⟨μ, hμ⟩ s]
    exact hμ s
  by_cases hw : (M : 𝓞 F) ∈ w.asIdeal
  · refine hD F Ω n M hM w hw A h rc hrc σ fun s hs => ?_
    rw [hpol]
    simp [hI _ s hs]
  · have hin : ∀ i (s : ↥(Ine (F := F) A)), μ i (ineIncl h s) = 1 := fun i s =>
      hI i s (UpperTheory.inertia_fixes_roots_of_unity_prime_to_residue_char F Ω w A h M hw s s.2)
    obtain ⟨hiw, hsp⟩ := hU F Ω n w A h rc hrc σ μ hpol hin
    have hS : GlobalTheory.SmGL.IsSpherical σ.ρ := by
      rcases hor with ⟨k, rfl⟩ | hk | hs
      · exfalso
        have hlw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal := hj.mem_placesOver h
        exact hw (by rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hlw)
      · refine hsp fun i j => ?_
        by_contra hne
        push_neg at hne
        rcases hG i j hne with e | e
        · exact hk i j e
        · exact hk j i e
      · exact hs hiw
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hS
    exact ⟨v, hv0, fun u hu => by simpa using hv ⟨u, (UpperTheory.mem_maximalCompact_and_congruent_of_mem_principalCongruence F w n M u hu).1⟩⟩
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
theorem UpperTheory.V.Lev.fixedSs_of_prints (P : _root_.UpperTheory.V.Af.Hypotheses') : _root_.UpperTheory.V.Lev.FixedSsAlt :=
  _root_.UpperTheory.V.Lev.fixed_semisimple_of_flag_fixed_dvd_fixed_unramified UpperTheory.V.Lev.flagPol (_root_.UpperTheory.V.Z.Win.T2.fixedDvd' P) (_root_.UpperTheory.V.Z.Win.T2.fixedUnr_alt P)
end
