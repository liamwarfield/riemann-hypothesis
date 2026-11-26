module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCSDOfIsEtaT
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeneralAdmissibleOfIrreducibilityStmt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoMonodromyOfInertiaSeparableCharpoly
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthQuotEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsToricTorsionCubWeilOne
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormsLeSpanShortThetaSeries
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterArchimedeanForm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieSkewAdjointMatrixStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLieCoord
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinExistsHolds
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem LocLanglands.isSmoothChar_of_comp {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {a : Weil h →* (w.adicCompletion E)ˣ} (hs : Function.Surjective a)
    (hc : Continuous fun σ : Ine (F := E) A => a (ineIncl h σ))
    (ho : ∀ σ, ord (w.adicCompletion E) (a σ) = -deg σ) {χ : (w.adicCompletion E)ˣ →* ℂˣ}
    (hχ : WeilDeligne.IsSmooth (χ.comp a)) : IsSmoothChar χ := by
  haveI : CompactSpace (Ine (F := E) A) := isCompact_iff_compactSpace.1 (isClosed_Ine A).isCompact
  have hK : IsOpen {σ : Ine (F := E) A | χ (a (ineIncl h σ)) = 1} := hχ
  have hC : IsClosed ((fun σ : Ine (F := E) A => a (ineIncl h σ)) ''
      {σ : Ine (F := E) A | χ (a (ineIncl h σ)) = 1}ᶜ) :=
    (hK.isClosed_compl.isCompact.image hc).isClosed
  have hU : {x : (w.adicCompletion E)ˣ | valuation (w.adicCompletion E) (x : w.adicCompletion E) = 1} ∈ nhds 1 := by
    have h1 : {x : w.adicCompletion E | valuation (w.adicCompletion E) (x - 1) < 1} ∈ nhds 1 := by
      rw [IsValuativeTopology.mem_nhds_iff]
      exact ⟨1, fun z hz => by simpa [neg_add_eq_sub] using hz⟩
    have h2 := Units.continuous_val.continuousAt (x := (1 : (w.adicCompletion E)ˣ)) h1
    refine Filter.mem_of_superset h2 fun x hx => ?_
    have h3 : valuation (w.adicCompletion E) ((x : w.adicCompletion E) - 1) < 1 := hx
    have := Valuation.map_one_add_of_lt _ h3
    simpa using this
  refine Subgroup.isOpen_of_mem_nhds χ.ker (g := 1) ?_
  have h1 : (1 : (w.adicCompletion E)ˣ) ∈ ((fun σ : Ine (F := E) A => a (ineIncl h σ)) ''
      {σ : Ine (F := E) A | χ (a (ineIncl h σ)) = 1}ᶜ)ᶜ := by
    rintro ⟨σ, hσ, e⟩
    refine hσ ?_
    have e' : a (ineIncl h σ) = 1 := e
    simp [e']
  refine Filter.mem_of_superset (Filter.inter_mem hU (hC.isOpen_compl.mem_nhds h1)) ?_
  rintro x ⟨hx, hx'⟩
  obtain ⟨σ, rfl⟩ := hs x
  have h0 : deg σ = 0 := by
    have := ho σ
    rw [ord_eq_zero_iff.2 hx] at this
    omega
  by_contra hn
  exact hx' ⟨⟨σ, deg_eq_zero_iff.mp h0⟩, hn, rfl⟩

theorem localArtinExists_holds : LocalArtinExists := by
  intro E Ω _ _ _ _ _ A w h
  obtain ⟨art, hart⟩ := globalArtinReciprocity_holds E Ω
  obtain ⟨a, hs, ho, hg⟩ := T.exists_inverse_localArtin_weilGroup_hom E Ω A w h art hart
  have hc := T.inverseLocalArtin_continuousOn_inertia E Ω A w h art a hart ho hg
  refine ⟨a, hs, hc, ho, fun ξ hξ => ?_, fun art' hart' => ?_⟩
  · have hker : a.ker ≤ ξ.ker := fun σ hσ => by
      refine T.smoothWeilChar_eq_one_of_toAbsGaloisAb_eq_one E Ω A w h ξ hξ σ ?_
      rw [← hg σ, MonoidHom.mem_ker.1 hσ, map_one, map_one]
    have e : ξ = (a.liftOfSurjective hs ⟨ξ, hker⟩).comp a :=
      (MonoidHom.liftOfRightInverse_comp a _ (Function.rightInverse_surjInv hs) ⟨ξ, hker⟩).symm
    exact ⟨_, isSmoothChar_of_comp hs hc ho (e ▸ hξ), e⟩
  · rw [T.globalArtinReciprocityMap_unique E Ω art' art hart' hart]
    exact hg

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyTrivialEverywhere
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleLocal GlobalTheory.TypeLeaf

noncomputable section

namespace GlobalTheory.GoodRowMono

theorem separable_prod_teich {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y, x ≠ 0 → y ≠ 0 → t x = t y → x = y) {f : (ZMod g)[X]} (hf : Squarefree f) :
    (((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (t x)).prod).Separable := by
  have hnd : ((Formalism.CyclotomicNorms.rootsBar f).map t).Nodup :=
    (nodup_roots ((separable_map _).2 (PerfectField.separable_iff_squarefree.2 hf))).map (GlobalTheory.TameLabels.teich_injective t ht)
  have e : ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (t x)) =
      ((Formalism.CyclotomicNorms.rootsBar f).map t).map (fun a => X - C a) := by
    rw [Multiset.map_map]; rfl
  rw [e]
  have hs : ((((Formalism.CyclotomicNorms.rootsBar f).map t).map fun a => X - C a).prod).Splits :=
    Splits.multisetProd fun x hx => by
      obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 hx
      exact Splits.X_sub_C _
  refine (nodup_roots_iff_of_splits (monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a).ne_zero hs).1 ?_
  rw [roots_multiset_prod_X_sub_C]
  exact hnd

variable (D : D7)

variable {D}

theorem separable_fixed {σ : D.what₂.FT} {π : D.naut.CG D.R.r} (hg : D.nd.goodRow σ)
    (hlab : ∀ k v, D.nd.lab k σ v = D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG π (D.naut.plGw k v)))
    (k : Fin 2) (v : D.nd.PlG k) :
    (D.naut.inePol (D.naut.locG π (D.naut.plGw k v)) (D.ntypes.tg k v)).Separable := by
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hfull : (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG π (D.naut.plGw k v))).natDegree =
      D.naut.lpDim (D.naut.locG π (D.naut.plGw k v)) := by
    rw [← hlab, (D.nd.lab_monic k σ v).2, D.naut.locG_dim]
  rw [D.ntypes.inertiaCharpoly_type k v _ hfull, ← hlab]
  exact separable_prod_teich _ (D.ntypes.teichC_inj k) ((hg k).1.2.1 v)

end GlobalTheory.GoodRowMono
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalOfArtinReciprocity
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthsModuloSubmoduleAgree
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthsModuloSubmoduleAgree
noncomputable section

namespace GlobalTheory.LenModAgree

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

theorem lenMod_eq {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (S H : Submodule O M) :
    BlochKatoDuality.lenMod S H = lenModN S H := by
  unfold BlochKatoDuality.lenMod lenModN
  have h := (LinearMap.quotientInfEquivSupQuotient S H).length_eq
  rw [← h]
  have e : Submodule.comap S.subtype S ⊓ Submodule.comap S.subtype H = Submodule.comap S.subtype H := by simp
  exact (Submodule.quotEquivOfEq _ _ e).length_eq

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem main : (∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (A H : Submodule O M), lenModN A H = BlochKatoDuality.lenMod A H) ∧ ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (e : ℕ), LocBoundP i w hw r Xs M e ↔ LocBound i w hw r Xs M e := by
  refine ⟨fun O M _ _ _ A H => (lenMod_eq A H).symm, ?_⟩
  intro D i w hw r Xs k M e
  unfold LocBoundP LocBound
  rw [lenMod_eq]

end GlobalTheory.LenModAgree
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthsModuloSubmoduleAgreeStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lengths_modulo_submodule_agree : (∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (A H : Submodule O M), lenModN A H = BlochKatoDuality.lenMod A H) ∧ ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (e : ℕ), LocBoundP i w hw r Xs M e ↔ LocBound i w hw r Xs M e := by
  first | exact @GlobalTheory.LenModAgree.main | exact GlobalTheory.LenModAgree.main | (intros; apply GlobalTheory.LenModAgree.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CutCongruenceValEqHeckeValueIdealOffSupportVal
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CutCongruenceValEqHeckeValueIdealOffSupportVal
noncomputable section

namespace GlobalTheory.Pass.CutEq

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

theorem main : ∀ (D : D7) (i : D.nd.Loc) (Xs : Set (D.nd.X i)) (π : D.nd.X i),
    PairedCharacterCondition.CongruenceModules.vccCut i Xs π = GlobalTheory.Cut.vccOff i Xs π := by
  intro D i Xs π
  have h : ccAt (D.nd.T i) (cutLocus i Xs) π = GlobalTheory.Cut.ccOff i Xs π := by
    unfold ccAt GlobalTheory.Cut.ccOff Ideal.map
    congr 1
    ext a
    constructor
    · rintro ⟨f, hf, rfl⟩
      refine ⟨f.1, f.2, fun x hx hZ => ?_, rfl⟩
      have := congrFun (RingHom.mem_ker.1 hf) ⟨x, by simp [cutLocus, hx, hZ]⟩
      exact this
    · rintro ⟨f, hf, h0, rfl⟩
      refine ⟨⟨f, hf⟩, RingHom.mem_ker.2 (funext fun y => ?_), rfl⟩
      have hy := y.2
      simp only [cutLocus, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_not] at hy
      exact h0 y.1 hy.2 hy.1
  unfold vccCut GlobalTheory.Cut.vccOff
  rw [h]

end GlobalTheory.Pass.CutEq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CutCongruenceValEqHeckeValueIdealOffSupportValStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cutCongruenceVal_eq_heckeValueIdealOffSupportVal : ∀ (D : D7) (i : D.nd.Loc) (Xs : Set (D.nd.X i)) (π : D.nd.X i), PairedCharacterCondition.CongruenceModules.vccCut i Xs π = GlobalTheory.Cut.vccOff i Xs π := by
  first | exact @GlobalTheory.Pass.CutEq.main | exact GlobalTheory.Pass.CutEq.main | (intros; apply GlobalTheory.Pass.CutEq.main <;> assumption)
end
end

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

namespace GlobalTheory.StepGlobalPf

variable {D : D7} (i : D.nd.Loc)

theorem mapM_twistM {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (χ : GE D.nd →* (D.nd.O i)ˣ)
    (g : GE D.nd) :
    mapM (toK D.nd i) (twistM M χ) g = toK D.nd i ((χ g : (D.nd.O i)ˣ) : D.nd.O i) • mapM (toK D.nd i) M g := by
  ext a b
  simp [mapM, twistM, RingHom.mapMatrix_apply, Matrix.map_apply]

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem chi_one_eq_one (hD : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) {γ : GE D.nd} (hγ : r π γ = 1) : chiU D.nd i 1 γ = 1 := by
  obtain ⟨e, he⟩ := hD
  have ht : 0 < D.R.t := D.R.t_odd.pos
  set u := e.symm (0, Pi.single (⟨0, ht⟩ : Fin D.R.t) 1) with hu
  have h := congrArg (fun p => p.2 (⟨0, ht⟩ : Fin D.R.t)) (he γ u)
  have h1 : mapM (toK D.nd i) (rO D.nd i r π) γ = 1 := by
    simp [mapM, rO, hγ]
  simp only [h1, Matrix.one_mulVec, hu, LinearEquiv.apply_symm_apply, Pi.single_eq_same, mul_one] at h
  apply Units.ext
  apply IsFractionRing.injective (D.nd.O i) (KK D.nd i)
  simpa using h.symm

theorem noChiOff (Xs : Set (D.nd.X i)) (hG6 : TruncatedSeriesCountingIdentities.admG6 i r) : GlobalTheory.Cut.NoChiOff i r Xs := by
  intro x _ hxZ u hu
  by_contra hu0
  refine hxZ (hG6 x ⟨u, hu0, fun g => ?_⟩)
  have h := hu g
  rw [rTwO, mapM_twistM, Matrix.smul_mulVec] at h
  conv_rhs => rw [← h]
  rw [smul_smul, ← map_mul, MonoidHom.inv_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one,
    one_smul]

theorem unrOut (Xs : Set (D.nd.X i)) (hG4 : TruncatedSeriesCountingIdentities.admG4 i r) (hD : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) :
    GlobalTheory.Cut.UnrOut i r Xs := by
  intro v hvl hvS hvQ x _ γ hγ
  have hχ := chi_one_eq_one i r ρ π hD (hG4 π v hvl hvS hvQ γ hγ)
  have hx : rO D.nd i r x γ = 1 := by simp [rO, hG4 x v hvl hvS hvQ γ hγ]
  rw [rTwO, twistM]
  simp [hx, hχ]

theorem atS (Xs : Set (D.nd.X i)) (hG5 : TruncatedSeriesCountingIdentities.admG5 i r) (hG5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i) :
    ∀ v ∈ D.nd.S i, (GlobalTheory.Cut.QuadAt i r Xs v ∧ IsUnit (D.nd.zeta i v - 1)) ∨ GlobalTheory.Cut.PolyAt i r Xs π v := by
  intro v hv
  have hS := ((D.nd.S_def i v).1 hv).1
  have hv5 := hG5 v (Or.inl hv)
  have hv5x := hG5x v (Or.inl hv)
  have hp : (∃ k, v ∈ placesOver D.host.E (D.host.g k)) ∨
      (v ∈ placesOver D.host.E D.host.pde ∨
        (D.nd.l i = D.host.pde ∧ v ∈ placesOver D.host.E D.host.pde')) := by
    rcases hS with h | h | h
    · exact Or.inl ⟨0, h⟩
    · exact Or.inl ⟨1, h⟩
    · right
      split_ifs at h with hl
      · exact Or.inr ⟨hl, h⟩
      · exact Or.inl h
  rcases hp with hk | hp
  · right
    obtain ⟨Pp, hu, hP⟩ := hv5.2 hk hv hv5x.1
    refine ⟨Pp, fun x _ γ hγ => hP x γ hγ, ?_⟩
    rw [Polynomial.eval_map]
    have hz : D.nd.zeta i v = evT D.nd i π (algebraMap (D.nd.O i) (D.nd.T i) (chi1 D.nd i (D.nd.gam0 i v))) := rfl
    rw [hz, Polynomial.eval₂_at_apply]
    exact hu.map _
  · left
    exact ⟨fun x _ γ hγ => ((hv5.1 (Or.inr hp)) x).1 γ hγ, hv5x.2.2.2 hv hp⟩

theorem atQ (Xs : Set (D.nd.X i)) (hG5 : TruncatedSeriesCountingIdentities.admG5 i r) (hG5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i) :
    ∀ v ∈ D.nd.Q i, GlobalTheory.Cut.QuadAt i r Xs v ∧ D.nd.zeta i v ≠ 1 := fun v hv =>
  ⟨fun x _ γ hγ => ((hG5 v (Or.inr hv)).1 (Or.inl hv) x).1 γ hγ, (hG5x v (Or.inr hv)).2.2.1 hv⟩


end GlobalTheory.StepGlobalPf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPullbackSectionToLevelCover
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeClauses
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj

namespace GlobalTheory

theorem framedPoint_bcGenR (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) : BcGenRSt Xo c := by
  intro p T _ _ ψ y
  obtain ⟨z, hx, -, pm, h1, h2, h3⟩ :=
    GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c p.R T ψ y
  obtain ⟨x, _, _, _, _, _, s, gen⟩ := z
  dsimp only at hx pm h1 h2 h3
  subst hx
  have hpm : pm = Formalism.L2.Pj.bcPm ψ.toRingHom y.x := by
    apply pullback.hom_ext
    · exact h2.trans (Formalism.L2.Pj.bcPm_fst _ _).symm
    · exact h1.trans (Formalism.L2.Pj.bcPm_snd _ _).symm
  subst hpm
  exact ⟨s, h3, gen⟩

theorem framedPoint_baseChange_clauses :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), BcLieAnySt Xo c ∧ BcLieRSt Xo c ∧ BcGenRSt Xo c ∧ FrBCFieldSt Xo c := by
  intro E _ _ _ H Dw l Xo c
  refine ⟨?_, ?_, framedPoint_bcGenR E H Dw l Xo c, ?_⟩
  · intro S _ _ K _ _ ψ y τ w hw he
    exact GlobalTheory.frame_baseChange_eigen_basis E H Dw l Xo c S K ψ y τ w hw he
  · intro p T _ _ ψ y τ w hw he
    exact GlobalTheory.frame_baseChange_eigen_basis E H Dw l Xo c p.R T ψ y τ w hw he
  · intro S _ _ y K _ _ ψ
    exact GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c S K ψ y

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPullbackSectionToLevelCover
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameLift
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CovPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n)

abbrev algDn (S : Type) [CommRing S] [Algebra d.c₂.F S] : Algebra c.F S :=
  ((algebraMap d.c₂.F S).comp (d.eF : c.F →+* d.c₂.F)).toAlgebra

theorem frBor_down {S : Type} [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S] {t : Ix Dw → Sˣ}
    {y y' : FrPt Xo c S} {y₂ y₂' : FrPt d.Xo₂ d.c₂ S} (h : FrOver d y₂ y) (h' : FrOver d y₂' y')
    (hb : FrBor t y₂ y₂') : FrBor t y y' := by
  obtain ⟨e, hu, w, p, hw, p₁, p₂, H⟩ := (frOver_iff d _ _).1 h
  obtain ⟨e', hu', w', p', hw', p₁', p₂', H'⟩ := (frOver_iff d _ _).1 h'
  obtain rfl : w = w' := rigidified_iso_unique GlobalTheory.abelianSchemeLaws_all.1.globalFns (UnivPol.pol d.Xo₂)
    Xo.univ.t.PP.isLB d.m.φ w w' hw.1 hw'.1 _ _ hw.2 hw'.2
  obtain ⟨ex, bu, b, b₁, b₂, hbs⟩ := hb
  have ex' : y'.x = y.x := by rw [← e', ← e, ex]
  obtain ⟨a, a₁, a₂⟩ := exists_pm (G := Xo.univ.t.G) (x := y.x) (fst (Over.mk y'.x) Xo.univ.t.G).left
    (snd (Over.mk y'.x) Xo.univ.t.G).left (by rw [← ex']; exact pm_cond _)
  obtain ⟨q, k, q₁, q₂, hk, -⟩ := exists_pm_iso d.m e'
  obtain rfl : p' = q := pm_ext (p₁'.trans q₁.symm) (p₂'.trans q₂.symm)
  have sq : p' ≫ a = b ≫ p := by
    refine pm_ext ?_ ?_
    · rw [Category.assoc, a₁, p₁', Category.assoc, p₁, ← Category.assoc, b₁]
    · rw [Category.assoc, a₂, p₂', Category.assoc, p₂, b₂]
  refine ⟨ex', fun τ i => ?_, a, a₁, a₂, ?_⟩
  · obtain ⟨cf, c₁, c₂, hcf⟩ := bu τ i
    refine ⟨cf, c₁, c₂, ?_⟩
    have := (comb_iff d.m e (fun j => (y₂.tan τ j).1) cf (ex ▸ (y₂'.tan τ i).1)).1 hcf
    rw [funext (hu τ), hu'] at this
    exact this
  · refine (pull_scal_iff a₁ (fst (Over.mk y.x) Xo.univ.t.G).left (toΓ S (t none)) y.s y'.s).2
      fun Z r z i hi => ?_
    have er : (r ≫ k) ≫ p' = r := by rw [Category.assoc, hk, Category.comp_id]
    obtain ⟨j, hj⟩ := exists_chart d.Xo₂.univ.t.PP.isLB ((snd (Over.mk y₂'.x) d.Xo₂.univ.t.G).left ((r ≫ k) z))
    have hi₀ : (snd (Over.mk y'.x) Xo.univ.t.G).left (((r ≫ k) ≫ p') z) ∈ Xo.univ.t.PP.L.U i :=
      (congrArg (fun x => (snd (Over.mk y'.x) Xo.univ.t.G).left x ∈ Xo.univ.t.PP.L.U i) (pt_eq er z)).mpr hi
    have hi' : d.m.φ ((snd (Over.mk y₂'.x) d.Xo₂.univ.t.G).left ((r ≫ k) z)) ∈ Xo.univ.t.PP.L.U i :=
      (congrArg (· ∈ Xo.univ.t.PP.L.U i) (pt_eq p₁' ((r ≫ k) z))).mp hi₀
    have k₂ := H' Z (r ≫ k) z i j hi' hj
    have k₁ := (pull_scal_iff b₁ (fst (Over.mk y₂.x) d.Xo₂.univ.t.G).left (toΓ S (t none)) y₂.s y₂'.s).1 hbs
      Z (r ≫ k) z j hj
    have k₃ := H Z ((r ≫ k) ≫ b) z i j
      ((congrArg (fun t => d.m.φ t ∈ Xo.univ.t.PP.L.U i) (pt_eq b₁ ((r ≫ k) z))).mpr hi')
      ((congrArg (· ∈ d.Xo₂.univ.t.PP.L.U j) (pt_eq b₁ ((r ≫ k) z))).mpr hj)
    have e2 : r ≫ a = ((r ≫ k) ≫ b) ≫ p := by
      calc r ≫ a = ((r ≫ k) ≫ p') ≫ a := by rw [er]
        _ = (r ≫ k) ≫ (p' ≫ a) := Category.assoc _ _ _
        _ = (r ≫ k) ≫ (b ≫ p) := by rw [sq]
        _ = ((r ≫ k) ≫ b) ≫ p := (Category.assoc _ _ _).symm
    have e3 : (r ≫ a) ≫ (fst (Over.mk y.x) Xo.univ.t.G).left =
        ((r ≫ k) ≫ b) ≫ (fst (Over.mk y₂.x) d.Xo₂.univ.t.G).left := by
      calc (r ≫ a) ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = r ≫ (fst (Over.mk y'.x) Xo.univ.t.G).left := by
            rw [Category.assoc, a₂]
        _ = ((r ≫ k) ≫ p') ≫ (fst (Over.mk y'.x) Xo.univ.t.G).left := by rw [er]
        _ = (r ≫ k) ≫ (fst (Over.mk y₂'.x) d.Xo₂.univ.t.G).left := by rw [Category.assoc, p₂']
        _ = ((r ≫ k) ≫ b) ≫ (fst (Over.mk y₂.x) d.Xo₂.univ.t.G).left := by rw [Category.assoc (r ≫ k) b, b₂]
    have e4 : ((r ≫ k) ≫ b) ≫ (snd (Over.mk y₂.x) d.Xo₂.univ.t.G).left =
        (r ≫ k) ≫ (snd (Over.mk y₂'.x) d.Xo₂.univ.t.G).left := by rw [Category.assoc, b₁]
    rw [e3, e2, k₃, e4]
    conv_lhs => rw [← er]
    rw [k₂, k₁, mul_left_comm]

theorem below_exists (hO : GlobalTheory.ClsVal.Cmp.OverBase d) (hK : KA l ≤ KA d.l₂) {S : Type} [CommRing S]
    [Algebra c.F S] [Algebra d.c₂.F S] (hc : ∀ a : c.F, algebraMap d.c₂.F S (d.eF a) = algebraMap c.F S a)
    (y₂ : FrPt d.Xo₂ d.c₂ S) : ∃ y : FrPt Xo c S, FrOver d y₂ y := by
  refine GlobalTheory.ClassSumCompare.exists_frUnder d hc y₂ ?_
  rw [Category.assoc, hO hK, ← Category.assoc, y₂.x_over]
  unfold sOf
  rw [GlobalTheory.ClsVal.Cmp.spMap_comp']
  congr 1
  ext x
  simp only [RingHom.comp_apply]
  rw [← hc]
  exact congrArg _ (Subtype.ext rfl)


open Classical in
def pullRule (f : Rul Xo c) : Rul d.Xo₂ d.c₂ := fun p u =>
  letI := algDn d p.R
  if h : ∃ y : FrPt Xo c p.R, FrOver d u y then evR Xo c f h.choose else 0

end GlobalTheory.CovPull

namespace GlobalTheory.CovPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n)

instance tRing_reduced {K : Type} [Field K] (p : TRing K) : IsReduced p.R :=
  (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad

theorem wtRed (Xo : Moduli Dw l) (c : Coeff l) : ReciprocityTheory.ChartRestriction.G.PullbackSections.WtRed Xo c :=
  ReciprocityTheory.ChartRestriction.G.PullbackSections.wtRed_of Xo c (GlobalTheory.TransferCompare.evalWD_framed Xo c) (GlobalTheory.TransferCompare.allTest_framed Xo c)
    (GlobalTheory.borDesc_and_wtField _ _ _ _ Xo c).2 (GlobalTheory.framedPoint_baseChange_clauses _ _ _ _ Xo c).2.2.2

theorem pullRule_eq (f : Rul Xo c) (p : TRing d.c₂.F) (u : FrPt d.Xo₂ d.c₂ p.R) :
    letI := algDn d p.R
    ∀ y : FrPt Xo c p.R, FrOver d u y → pullRule d f p u = evR Xo c f y := by
  let _ := algDn d p.R
  intro y hy
  have h : ∃ y : FrPt Xo c p.R, FrOver d u y := ⟨y, hy⟩
  unfold pullRule
  rw [dite_eq_left h, GlobalTheory.ClassSumCompare.frUnder_unique d h.choose_spec hy]

end GlobalTheory.CovPull

namespace GlobalTheory.CovPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n)

theorem pullRule_mem (hO : GlobalTheory.ClsVal.Cmp.OverBase d) (hK : KA l ≤ KA d.l₂) {a : (E →+* ℂ) × ℕ → ℕ} {m : ℕ}
    {f : Rul Xo c} (hf : f ∈ sec Xo c a m) : pullRule d f ∈ sec d.Xo₂ d.c₂ a m := by
  refine ⟨fun p q φ u u' hm => ?_, fun p t u u' hb => ?_⟩
  · letI := algDn d p.R
    letI := algDn d q.R
    obtain ⟨y, hy⟩ := below_exists d hO hK (S := p.R) (fun _ => rfl) u
    obtain ⟨y', hy'⟩ := below_exists d hO hK (S := q.R) (fun _ => rfl) u'
    let φc : p.R →ₐ[c.F] q.R := ⟨φ.toRingHom, fun a => φ.commutes (d.eF a)⟩
    obtain ⟨w, hw⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c p.R q.R φc y
    have hw' : FrOver d u' w := GlobalTheory.FrameLift.frOver_map d (ψ := φc) (ψ₂ := φ) rfl hy hw hm
    obtain rfl : y' = w := GlobalTheory.ClassSumCompare.frUnder_unique d hy' hw'
    show pullRule d f q u' = φ (pullRule d f p u)
    rw [pullRule_eq d f q u' y' hy', pullRule_eq d f p u y hy]
    exact GlobalTheory.SupLawProbe.evR_map (GlobalTheory.TransferCompare.evalWD_framed Xo c) f hf.1 φc y
      (GlobalTheory.TransferCompare.allTest_framed Xo c p.R y) y' hw
  · letI := algDn d p.R
    obtain ⟨y, hy⟩ := below_exists d hO hK (S := p.R) (fun _ => rfl) u
    obtain ⟨y', hy'⟩ := below_exists d hO hK (S := p.R) (fun _ => rfl) u'
    show pullRule d f p u' = wchar (ex Dw a m) t * pullRule d f p u
    rw [pullRule_eq d f p u' y' hy', pullRule_eq d f p u y hy]
    exact wtRed Xo c a m f hf p.R t y y' (frBor_down d hy hy' hb)

theorem evR_pullRule (hO : GlobalTheory.ClsVal.Cmp.OverBase d) (hK : KA l ≤ KA d.l₂) {a : (E →+* ℂ) × ℕ → ℕ} {m : ℕ}
    {f : Rul Xo c} (hf : f ∈ sec Xo c a m) {k : Type} [Field k] [Algebra c.F k] [Algebra d.c₂.F k]
    (hc : ∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) (y₂ : FrPt d.Xo₂ d.c₂ k) (y : FrPt Xo c k)
    (hy : FrOver d y₂ y) : evR d.Xo₂ d.c₂ (pullRule d f) y₂ = evR Xo c f y := by
  have key : ∀ (p : TRing d.c₂.F) (φ : p.R →ₐ[d.c₂.F] k) (u : FrPt d.Xo₂ d.c₂ p.R), FrMap φ u y₂ →
      φ (pullRule d f p u) = evR Xo c f y := by
    intro p φ u hu
    letI := algDn d p.R
    obtain ⟨z, hz⟩ := below_exists d hO hK (S := p.R) (fun _ => rfl) u
    let φc : p.R →ₐ[c.F] k := ⟨φ.toRingHom, fun a => (φ.commutes (d.eF a)).trans (hc a)⟩
    obtain ⟨w, hw⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c p.R k φc z
    have hw' : FrOver d y₂ w := GlobalTheory.FrameLift.frOver_map d (ψ := φc) (ψ₂ := φ) rfl hz hw hu
    obtain rfl : y = w := GlobalTheory.ClassSumCompare.frUnder_unique d hy hw'
    rw [pullRule_eq d f p u z hz]
    exact (GlobalTheory.SupLawProbe.evR_map (GlobalTheory.TransferCompare.evalWD_framed Xo c) f hf.1 φc z
      (GlobalTheory.TransferCompare.allTest_framed Xo c p.R z) y hw).symm
  have hT := GlobalTheory.TransferCompare.allTest_framed d.Xo₂ d.c₂ k y₂
  have e : evR d.Xo₂ d.c₂ (pullRule d f) y₂ =
      hT.choose_spec.choose (pullRule d f hT.choose hT.choose_spec.choose_spec.choose) := by
    unfold evR evalAt
    rw [dite_eq_left hT]
  rw [e]
  exact key _ _ _ hT.choose_spec.choose_spec.choose_spec

end GlobalTheory.CovPull

namespace GlobalTheory.CovPull

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead

theorem exists_pull : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ,
    GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.d.IsLev → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ),
    ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∃ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ := by
  intro D T hT j hj σ _ C _ a n f hf
  have hpq : (T.Q.Dw j).p ≠ (T.Q.Dw j).q := by
    intro e
    have h1 := GlobalTheory.Dict.sig_add_of_pins T.Q hT.pins hj
    obtain ⟨k, hk⟩ := r_odd D
    omega
  have hA : T.Q.l.A = 1 := hT.pins.2.1.2
  have hO := GlobalTheory.ClsVal.Cmp.overBase_of_ne hpq hA C.d
  have hK : KA T.Q.l ≤ KA C.d.l₂ := GlobalTheory.Models.RankZero.KA_le_of_eq_one hA _
  obtain ⟨hf', hv⟩ := (GlobalTheory.FieldBC.rulBC_sec_val_linear _ _ _ _ _ _ _ C.hle).1 a n f hf
  refine ⟨pullRule C.d (GlobalTheory.FieldBC.rulBC C.hle f), pullRule_mem C.d hO hK hf', ?_⟩
  intro k _ _ _ _ h hc y₂ y hy
  rw [evR_pullRule C.d hO hK hf' hc y₂ y hy, hv k h y]

end GlobalTheory.CovPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPullbackSectionToLevelCoverStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pullback_section_to_levelCover : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.d.IsLev → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∃ f₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull f f₂ := by
  first | exact @GlobalTheory.CovPull.exists_pull | exact GlobalTheory.CovPull.exists_pull | (intros; apply GlobalTheory.CovPull.exists_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinFrobeniusAction
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ArtinCompareApply

theorem lift_localArtinMap_apply : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a → ∀ (ι : Ω →ₐ[E] Kbar w), IsLocEmb A w ι →
    ∀ (σ : Weil h) (τ : GalLoc w), Lifts ι τ (σ : G E Ω) →
    ∀ (z : Kbar w) (hz : z ∈ maximalAbelianExtension (w.adicCompletion E) (Kbar w)),
      τ ((localArtinMap (w.adicCompletion E) (Kbar w) (a σ) ⟨z, hz⟩ : maximalAbelianExtension (w.adicCompletion E) (Kbar w)) : Kbar w) = z := by
  intro E Ω _ _ _ _ _ A w h a ha ι hι σ τ hτ z hz
  have H := GlobalTheory.ArtinCompare.restrict_eq_inv_localArtinMap E Ω A w h ι hι a ha σ τ hτ
  set M := maximalAbelianExtension (w.adicCompletion E) (Kbar w)
  set g := localArtinMap (w.adicCompletion E) (Kbar w) (a σ)
  have e : AlgEquiv.restrictNormalHom M τ (g ⟨z, hz⟩) = ⟨z, hz⟩ := by
    rw [H, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have e2 := congrArg (fun y : M => (y : Kbar w)) e
  simp only [AlgEquiv.restrictNormalHom_apply] at e2
  exact e2

end GlobalTheory.ArtinCompareApply
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedOrthogonalityHolds
namespace GlobalTheory

theorem unramifiedOrthogonality_holds : ReciprocityTheory.Gal.UnramifiedOrthogonality :=
  GlobalTheory.CompanionTheory.Hypotheses₂.unramifiedOrthogonality

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CasimirEigenOrthogonal
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Published

noncomputable section

namespace GlobalTheory.CapOrth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ} {μ : Measure (GA E N)}
  {W : Submodule ℂ (Sm E N)} (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1)


open Classical in
def cls (x : Sm E N) : L2 (latticeGL E N) μ := if hx : x ∈ W then toL2ₗ μ W h ⟨x, hx⟩ else 0

theorem cls_mk {x : Sm E N} (hx : x ∈ W) : cls h x = toL2ₗ μ W h ⟨x, hx⟩ := dif_pos hx

theorem cls_add {x y : Sm E N} (hx : x ∈ W) (hy : y ∈ W) : cls h (x + y) = cls h x + cls h y := by
  rw [cls_mk h (W.add_mem hx hy), cls_mk h hx, cls_mk h hy, ← map_add (f := _)]; rfl

theorem cls_smul (c : ℂ) {x : Sm E N} (hx : x ∈ W) : cls h (c • x) = c • cls h x := by
  rw [cls_mk h (W.smul_mem c hx), cls_mk h hx, ← map_smul]; rfl

theorem cls_sub {x y : Sm E N} (hx : x ∈ W) (hy : y ∈ W) : cls h (x - y) = cls h x - cls h y := by
  rw [cls_mk h (W.sub_mem hx hy), cls_mk h hx, cls_mk h hy, ← map_sub]; rfl

variable (J : Submodule ℂ (Sm E N))

variable [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

end GlobalTheory.CapOrth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMapAdjointTranslateInvEqMulFrameMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMapAdjointTranslateInvEqMulFrameMatrix
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

namespace GlobalTheory.TranslateAdj

theorem frameAdjoint_translate_mul_frameConj_algebra {R S : Type} [CommRing R] [CommRing S] (σ : R →+* R) (f : R →+* S) {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) R) (G K K' : Matrix (Fin n) (Fin n) R) (P : Matrix (Fin m) (Fin m) R)
    (x : Matrix (Fin n) (Fin m) R) (βV : GL (Fin m) S) (βW : GL (Fin n) S)
    (hkey : (K'.map σ)ᵀ * G = G * K) (hP : P = 1) :
    (βV⁻¹).val * ((A * ((K' * x * P).map σ)ᵀ * G).map f) * βW.val =
      ((βV⁻¹).val * ((A * (x.map σ)ᵀ * G).map f) * βW.val) * ((βW⁻¹).val * K.map f * βW.val) := by
  subst hP
  have hβ : βW.val * (βW⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 : A * ((K' * x * (1 : Matrix (Fin m) (Fin m) R)).map σ)ᵀ * G = A * (x.map σ)ᵀ * G * K := by
    rw [Matrix.mul_one, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc A, Matrix.mul_assoc, hkey]
    simp only [Matrix.mul_assoc]
  rw [h1, Matrix.map_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc βW.val, hβ, Matrix.one_mul]

theorem frMapAdj_actO_inv : ∀ (D : D7) (V W : HSp D) (βV : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (βW : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (k : GA D W) (x : WO V W), frMapAdj V W βV βW (actO V W 1 k⁻¹ x) = (HMul.hMul (frMapAdj V W βV βW x) (HMul.hMul (HMul.hMul ((βW)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (βW).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) : Matrix (Fin V.rank) (Fin W.rank) (Formalism.IndefR.Datum.EAf D)) := by
  intro D V W βV βW k x
  have hU : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt W k⁻¹) * W.gram.map (incA D) * Formalism.L2.Theta.mt W k⁻¹ =
      W.gram.map (incA D) := (show HR (AF D.host.F) D.sp.cm.sig W.gram from k⁻¹).2
  have hi : Formalism.L2.Theta.mt W k⁻¹ * Formalism.L2.Theta.mt W k = 1 := by
    show Formalism.L2.Theta.mt W (k⁻¹ * k) = 1
    rw [inv_mul_cancel]; rfl
  have hkey : ((Formalism.L2.Theta.mt W k⁻¹).map (cA D)).transpose * W.gram.map (incA D) =
      W.gram.map (incA D) * Formalism.L2.Theta.mt W k := by
    calc _ = Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt W k⁻¹) * W.gram.map (incA D) *
          (Formalism.L2.Theta.mt W k⁻¹ * Formalism.L2.Theta.mt W k) := by rw [hi, Matrix.mul_one]; rfl
      _ = _ := by rw [← Matrix.mul_assoc, hU]
  have hmt1 : Formalism.L2.Theta.mt V (1 : GA D V)⁻¹ = 1 := by rw [inv_one]; rfl
  exact frameAdjoint_translate_mul_frameConj_algebra (cA D) (toEAf D) ((V.gram⁻¹).map (incA D)) (W.gram.map (incA D)) (Formalism.L2.Theta.mt W k)
    (Formalism.L2.Theta.mt W k⁻¹) (Formalism.L2.Theta.mt V (1 : GA D V)⁻¹) x βV βW hkey hmt1

end GlobalTheory.TranslateAdj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMapAdjointTranslateInvEqMulFrameMatrixStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameMapAdjoint_translate_inv_eq_mul_frameMatrix : ∀ (D : D7) (V W : HSp D) (βV : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (βW : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (k : GA D W) (x : WO V W), frMapAdj V W βV βW (actO V W 1 k⁻¹ x) = (HMul.hMul (frMapAdj V W βV βW x) (HMul.hMul (HMul.hMul ((βW)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (βW).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) : Matrix (Fin V.rank) (Fin W.rank) (Formalism.IndefR.Datum.EAf D)) := by
  first | exact @GlobalTheory.TranslateAdj.frMapAdj_actO_inv | exact GlobalTheory.TranslateAdj.frMapAdj_actO_inv | (intros; apply GlobalTheory.TranslateAdj.frMapAdj_actO_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KernelOperatorIntegrableContinuousSmooth
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KernelOperatorIntegrableContinuousSmooth
noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW

theorem measurable_smooth_comp_infGL {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    {X : Type} [MeasurableSpace X] (γ : X → GL (Fin a) (Cinf E))
    (hγ : Measurable (fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E)))) (φ : Sm E a) (g : GA E a) :
    Measurable (fun x => φ.1 (g * infGL E a (γ x))) := by
  classical
  have hc : Measurable (chart φ.1 g) := by
    have e : chart φ.1 g = (invSet E a).piecewise (chart φ.1 g) (fun _ => 0) := by
      funext x
      by_cases h : x ∈ invSet E a
      · simp [Set.piecewise, h]
      · have h' : ¬ IsUnit (Matrix.of x) := h
        simp only [Set.piecewise, h, if_false]
        simp [chart, h']
    rw [e]
    exact ContinuousOn.measurable_piecewise (φ.2 g).continuousOn continuousOn_const isOpen_invSet.measurableSet
  have hγ' : Measurable (fun x => toL (γ x).val) := hγ
  have h2 := hc.comp hγ'
  simpa [Function.comp_def, chart_val] using h2

theorem kerOp_integrable_continuous : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X)
    (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → ∀ φ : Sm E a, Continuous φ.1 →
    (∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C) →
      (∀ g, Integrable (fun x => k x * φ.1 (g * infGL E a (γ x))) ν) ∧ Continuous (kerOp ν k γ φ.1) := by
  intro E _ _ _ a X _ ν k γ hk φ hφc hb
  obtain ⟨C, hC⟩ := hb
  have hint : Integrable (fun x => ‖k x‖ * C) ν := by
    have h0 := hk.2.2 0
    simp only [pow_zero, mul_one] at h0
    exact h0.mul_const C
  have hm : ∀ g, AEStronglyMeasurable (fun x => k x * φ.1 (g * infGL E a (γ x))) ν := fun g =>
    (hk.1.mul (measurable_smooth_comp_infGL γ hk.2.1 φ g)).aestronglyMeasurable
  have hbd : ∀ g, ∀ᵐ x ∂ν, ‖k x * φ.1 (g * infGL E a (γ x))‖ ≤ ‖k x‖ * C := fun g =>
    Filter.Eventually.of_forall fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  refine ⟨fun g => Integrable.mono' hint (hm g) (hbd g), ?_⟩
  set_option synthInstance.maxHeartbeats 200000 in
  exact continuous_of_dominated hm hbd hint (Filter.Eventually.of_forall fun x =>
    continuous_const.mul (hφc.comp (continuous_id.mul continuous_const)))

end GlobalTheory.JSW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KernelOperatorIntegrableContinuousSmoothStatement
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelOperator_integrable_continuous_smooth : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X)
    (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → ∀ φ : Sm E a, Continuous φ.1 →
    (∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C) →
      (∀ g, Integrable (fun x => k x * φ.1 (g * infGL E a (γ x))) ν) ∧ Continuous (kerOp ν k γ φ.1) := by
  first | exact @GlobalTheory.JSW.kerOp_integrable_continuous | exact GlobalTheory.JSW.kerOp_integrable_continuous | (intros; apply GlobalTheory.JSW.kerOp_integrable_continuous <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimeIdempotentOfIdempotentSumPlaceSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimeIdempotentOfIdempotentSumPlaceSplit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

namespace GlobalTheory.IdemSumBranch

open GlobalTheory.StdFrames GlobalTheory.IdemSupport

variable {D : D7}

theorem cpt_idemSum {ea : AE D} {S : Finset (Pl D.host.E)} (h : IsIdemSum ea S) {Q : Pl D.host.E} (hQ : Q ∈ S) :
    cpt Q (toEAf D ea) = 1 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  have hs := map_sum ((cpt Q).comp (toEAf D)).toAddMonoidHom es S
  refine hs.trans ?_
  rw [Finset.sum_eq_single_of_mem Q hQ]
  · exact (cpt_of_isIdemAt (hes Q hQ)).1
  · intro R hR hne
    exact (cpt_of_isIdemAt (hes R hR)).2 Q hne.symm

theorem conjPrime_ne {ea : AE D} {S : Finset (Pl D.host.E)} (h : IsIdemSum ea S) {P Q : Pl D.host.E} (hP : P ∈ S)
    (hQ : Q ∈ S) : cP Q ≠ P := by
  intro hc
  have h1 := congrArg (fun t => cpt P (toEAf D t)) h.2
  simp only [RingHom.map_mul, RingHom.map_zero, cpt_idemSum h hP, one_mul] at h1
  rw [toEAf_cA, ← hc] at h1
  have h2 := cpt_sg_eq_zero h1
  rw [sg_sg, cpt_idemSum h hQ] at h2
  exact one_ne_zero h2

theorem branch : ∀ (D : D7) (P : Pl D.host.E) (e f ea : AE D) (S : Finset (Pl D.host.E)),
    IsPrimeIdem P e f → IsIdemSum ea S → P ∈ S → Formalism.L2.NTheta.IsIdemAt e P ∧ f = e + cA D e ∧ cA D f = f ∧
      infPart D f = 0 ∧ ∀ PP ∈ S, GlobalTheory.IdemSupport.cP PP ≠ P := by
  intro D P e f ea S h1 hS hP
  obtain ⟨hd, ε, hε, hf⟩ := of_isPrimeIdem (comp_toAd D) h1
  have hinf : infPart D f = 0 := hf ▸ (place_comp (comp_toAd D) hε).1
  rcases h1 with ⟨h1, h2⟩ | ⟨rfl, -⟩
  · refine ⟨h1, h2, ?_, hinf, fun Q hQ => conjPrime_ne hS hP hQ⟩
    rw [h2, RingHom.map_add (f := _), Formalism.L2.Theta.cA_cA, add_comm]
  · exfalso
    have h2 := (place_comp (comp_toAd D) hε).2.1 (cP P) (under_cP P)
    rw [← hf, hd.2.2 _ (conjPrime_ne hS hP hP)] at h2
    exact zero_ne_one h2

end GlobalTheory.IdemSumBranch
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimeIdempotentOfIdempotentSumPlaceSplitStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primeIdempotent_of_idempotentSum_place_split : ∀ (D : D7) (P : Pl D.host.E) (e f ea : AE D) (S : Finset (Pl D.host.E)), IsPrimeIdem P e f → IsIdemSum ea S → P ∈ S → Formalism.L2.NTheta.IsIdemAt e P ∧ f = e + cA D e ∧ cA D f = f ∧ infPart D f = 0 ∧ ∀ PP ∈ S, GlobalTheory.IdemSupport.cP PP ≠ P := by
  first | exact @GlobalTheory.IdemSumBranch.branch | exact GlobalTheory.IdemSumBranch.branch | (intros; apply GlobalTheory.IdemSumBranch.branch <;> assumption)
end
end
