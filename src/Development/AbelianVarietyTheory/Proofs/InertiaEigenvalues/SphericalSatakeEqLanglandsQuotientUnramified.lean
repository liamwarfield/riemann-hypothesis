module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisRepBaseChange
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDet
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongruenceLevelMapsIntoLatticeCongruence
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.SubsingletonOfScalar

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalSatakeEqLanglandsQuotientUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalSatakeEqLanglandsQuotientUnramified
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.SatakeL

theorem isL_single_unrChar : LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL →
    ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
      (x : IrrGL (k := k)) (α : Fin x.1 → ℂˣ), HasSatake x.rep α →
      IsL (Finset.univ.val.map fun i => Segment.single (IrrGL.ofChar (GlobalTheory.SmGL.unrChar k (α i))
        (isSmoothChar_of_isUnram (isUnram_unrChar k (α i)))) (IrrGL.isCusp_ofChar _ _)) x.rep := by
  intro hEx hLM hSC hZP hGL hBZ k _ _ _ _ _ x α hsat
  obtain ⟨𝔪, hL⟩ := hEx k x
  obtain ⟨h, y, hd, ⟨Δ, hord, hseg⟩, hcos⟩ := id hL

  have hsphy : ∀ a, IsSpherical (y a).rep :=
    GlobalTheory.T.isSpherical_factor_of_spherical_subquotient k h x.1 y hd x.2.rep.V x.rep hcos.isSubquotient hsat.2.1

  have hlen : ∀ i, (Δ i).len = 1 := fun i =>
    (GlobalTheory.T.sphericalSegmentRep_length_one_unramified hLM hSC hZP hGL hBZ k (Δ i) (y i) (hseg i) (hsphy i)).1
  have hsingle : ∀ i, Δ i = Segment.single (Δ i).first (Δ i).isCusp_first := fun i =>
    Segment.ext_first rfl (by rw [hlen i]; rfl)
  have hms : ∀ i, (Δ i).ms = {(Δ i).first} := fun i =>
    (congrArg Segment.ms (hsingle i)).trans (Segment.ms_single _ _)

  have h1 : HasSupport x.rep (msupp 𝔪) := GlobalTheory.T.langlandsClassification_supercuspidalSupport_multisegment hZP k 𝔪 x hL
  have h2 := GlobalTheory.T.supercuspidalSupport_of_principalSeries_subquotient k x.1 (fun i => GlobalTheory.SmGL.unrChar k (α i))
    (fun i => isSmoothChar_of_isUnram (isUnram_unrChar k (α i))) x.2.rep hsat.2.2
  have heq := GlobalTheory.T.supercuspidalSupport_unique_GL hGL hBZ hZP k x _ _ h1 h2
  have hsupp : msupp 𝔪 = Finset.univ.val.map fun i => (Δ i).first := by
    rw [msupp, ← hord.1, Multiset.bind_map]
    simp only [hms]
    exact Multiset.bind_singleton _ _
  rw [hsupp] at heq

  have hinj : Function.Injective fun D : Segment k => (D.first, D.len) := fun a b e =>
    Segment.ext_first (congrArg Prod.fst e) (congrArg Prod.snd e)
  have hm : 𝔪 = Finset.univ.val.map fun i => Segment.single (IrrGL.ofChar (GlobalTheory.SmGL.unrChar k (α i))
      (isSmoothChar_of_isUnram (isUnram_unrChar k (α i)))) (IrrGL.isCusp_ofChar _ _) := by
    apply Multiset.map_injective hinj
    have e1 := congrArg (Multiset.map fun ρ : IrrGL (k := k) => (ρ, 1)) heq
    simp only [Multiset.map_map, Function.comp_def] at e1
    rw [← hord.1, Multiset.map_map, Multiset.map_map]
    simp only [Function.comp_def, hlen]
    exact e1
  rw [← hm]
  exact hL

end GlobalTheory.LocLanglands.SatakeL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalSatakeEqLanglandsQuotientUnramifiedStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_satake_eq_langlandsQuotient_unramified : LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL (k := k)) (α : Fin x.1 → ℂˣ), HasSatake x.rep α → IsL (Finset.univ.val.map fun i => Segment.single (IrrGL.ofChar (GlobalTheory.SmGL.unrChar k (α i)) (isSmoothChar_of_isUnram (isUnram_unrChar k (α i)))) (IrrGL.isCusp_ofChar _ _)) x.rep := by
  first | exact @GlobalTheory.LocLanglands.SatakeL.isL_single_unrChar | exact GlobalTheory.LocLanglands.SatakeL.isL_single_unrChar | (intros; apply GlobalTheory.LocLanglands.SatakeL.isL_single_unrChar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInertDatumOfInvolutionUniformizer
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInertDatumOfInvolutionUniformizer
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertDatumGiven

open scoped TensorProduct

theorem continuous_of_valued_eq {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (s : K →+* K) (hs : ∀ x, Valued.v (s x) = Valued.v x) : Continuous s := by
  have h : Filter.Tendsto s (nhds 0) (nhds 0) := by
    rw [(Valued.hasBasis_nhds_zero K Γ₀).tendsto_iff (Valued.hasBasis_nhds_zero K Γ₀)]
    intro γ _
    refine ⟨γ, trivial, fun x hx => ?_⟩
    simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding] at hx ⊢
    rwa [hs]
  exact continuous_of_continuousAt_zero s (by simpa [ContinuousAt] using h)

theorem exists_inertDatum_of : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal → ¬ IsSplitAt w → ∀ (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → Formalism.UG.IsUnramInv ϖ s (Formalism.UG.qV (maximalRealSubfield L) v) → ∃ Dv : InertDatum L n v w, Dv.σw = s ∧ Dv.ϖ = ϖ := by
  intro L _ _ _ n v w hov hu hns s ϖ hs hU
  classical
  have hunder : w.under (𝓞 (maximalRealSubfield L)) = v := HeightOneSpectrum.ext hov
  have hw : Formalism.UG.IsInertAt (maximalRealSubfield L) L v w := by
    have h := GlobalTheory.InertPlaceConj.isInertAt_of_not_split w hu hns
    rwa [hunder] at h
  obtain ⟨c, hc, -⟩ := GlobalTheory.LFun.InertChart.existsUnique_isConjAt
    (IsCMField.complexConj L).toAlgHom hw hunder
  obtain ⟨ϖ', hU'⟩ := GlobalTheory.LFun.InertChart.exists_isUnramInv (GlobalTheory.InertDatumExist.isCMExt L) hw hc
  have hsc : s = c := by
    apply DFunLike.coe_injective
    refine GlobalTheory.UnramCompletion.ringHom_ext_of_continuous w (continuous_of_valued_eq s hU.2.1)
      (continuous_of_valued_eq c hU'.2.1) fun k => ?_
    rw [hs, GlobalTheory.LFun.InertChart.conj_algebraMap hc]
    rfl
  subst hsc
  obtain ⟨k, hk, hke⟩ := GlobalTheory.LFun.InertChart.exists_congr_antiJ (n := n) hU (B := 1) (one_mem _)
    (by simp [Formalism.UG.cT, Matrix.map_one])
  have hO : Formalism.UG.Ov L w = Formalism.UG.intL (w.adicCompletion L) := Subring.ext fun _ => Iff.rfl
  let e := (Algebra.TensorProduct.comm (maximalRealSubfield L) L
    (v.adicCompletion (maximalRealSubfield L))).toRingEquiv.trans (GlobalTheory.LFun.InertChart.complEquiv hw hunder)
  refine ⟨⟨e, s, ϖ, k, ?_, hU, ?_, ?_, ?_⟩, rfl, rfl⟩
  · intro x
    show GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _
        (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom _ x)) =
      s (GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _ x))
    rw [hc]
    congr 1
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · intro x
    rw [GlobalTheory.InertDatumExist.mem_tensInt_iff, GlobalTheory.LFun.InertChart.mem_intLoc_iff hw hunder, hO]
    exact Iff.rfl
  · rw [← hO]; exact hk
  · simpa using hke

end GlobalTheory.InertDatumGiven

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInertDatumOfInvolutionUniformizerStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inertDatum_of_involution_uniformizer : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal → ¬ IsSplitAt w → ∀ (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → Formalism.UG.IsUnramInv ϖ s (Formalism.UG.qV (maximalRealSubfield L) v) → ∃ Dv : InertDatum L n v w, Dv.σw = s ∧ Dv.ϖ = ϖ := by
  first | exact @GlobalTheory.InertDatumGiven.exists_inertDatum_of | exact GlobalTheory.InertDatumGiven.exists_inertDatum_of | (intros; apply GlobalTheory.InertDatumGiven.exists_inertDatum_of <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorEqGoodIdempotentTypePlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorEqGoodIdempotentTypePlaces
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowGood

section Act

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem hasType_flag1 {P : LevelP L.Pg L.r ℂ} {F : Theta.GA D V → ℂ} (h : HasType V β (withP L P) F) : HasType V β (flag1L L) F := by
  intro κ hκ x
  have h1 : rTup β L (finE V κ) = 1 := hκ.2.2
  rw [h κ ⟨hκ.1, hκ.2.1, by
    show rTup β L (finE V κ) ∈ P.H
    rw [h1]; exact P.H.one_mem⟩ x]
  unfold levChi
  rw [levFn_withP, levFn_flag1, h1, blockDiagonalExtendByOnePrimeField_one, one_mul]

end Act

theorem asAlgebraHom_eq_sum {G H M : Type} [Fintype G] [Group H] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ H M)
    (ε : G ≃ H) (a : MonoidAlgebra ℂ H) (z : M) : ρ.asAlgebraHom a z = ∑ g, a.coeff (ε g) • ρ (ε g) z := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb, add_smul, Finset.sum_add_distrib]
  | single h c =>
    obtain ⟨h, rfl⟩ := ε.surjective h
    rw [Representation.asAlgebraHom_single]
    simp [Finsupp.single_apply]

theorem pi_induction {I : Type} [Finite I] [DecidableEq I] {H : I → Type} [∀ i, Group (H i)] (p : (∀ i, H i) → Prop) (h1 : p 1)
    (hm : ∀ a b, p a → p b → p (a * b)) (hs : ∀ i x, p (Pi.mulSingle i x)) (a : ∀ i, H i) : p a := by
  cases nonempty_fintype I
  rw [← Finset.noncommProd_mulSingle a]
  exact Finset.noncommProd_induction _ _ _ p hm h1 fun i _ => hs i _


open scoped Classical in
theorem exists_act {D : D7} {s : ∀ k : Fin 2, D.nd.PlG k → SplitPlace D.host.E}
    {j : ∀ k v, ℚ_[D.host.g k] ≃+* (s k v).v.adicCompletion (maximalRealSubfield D.host.E)}
    {A : Type} [AddCommGroup A] [Module ℂ A] (ρA : GAf D.host.E D.R.r →* Module.End ℂ A)
    (ρ : Representation ℂ (G0g D.nd) (KFix D s j ρA))
    (hρ : ∀ k v y x, IsLiftAt (s k v) (j k v) y x → ∀ z,
      ((ρ (GlobalTheory.GoodTypes.facHom D k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y)) z : KFix D s j ρA) : A) = ρA x z)
    (q : G0g D.nd → GAf D.host.E D.R.r → Prop) (q1 : q 1 1) (qm : ∀ a x b y, q a x → q b y → q (a * b) (x * y))
    (ql : ∀ k v y x, IsLiftAt (s k v) (j k v) y x → q (GlobalTheory.GoodTypes.facHom D k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y)) x)
    (a : G0g D.nd) : ∃ x, q a x ∧ ∀ z, ((ρ a z : KFix D s j ρA) : A) = ρA x z := by
  refine pi_induction (fun a : G0g D.nd => ∃ x, q a x ∧ ∀ z, ((ρ a z : KFix D s j ρA) : A) = ρA x z) ?_ ?_ ?_ a
  · exact ⟨1, q1, fun z => by rw [map_one, map_one]; rfl⟩
  · rintro a b ⟨x, hx, hx'⟩ ⟨y, hy, hy'⟩
    exact ⟨x * y, qm _ _ _ _ hx hy, fun z => by rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hx', hy']⟩
  · rintro ⟨k, v⟩ h
    obtain ⟨y, rfl⟩ := GlobalTheory.GLp.Model.red_surjective (g := D.host.g k) D.R.r h
    obtain ⟨x, hx⟩ : ∃ x, IsLiftAt (s k v) (j k v) y x := GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.r (s k v) _
    exact ⟨x, ql k v y x hx, hρ k v y x hx⟩

theorem levelChoiceData_eq_withLevel_trivial {D : D7} {T : Type} (C : LevCh D T) (P : LevelP C.Pg D.R.r ℂ) : C.dat0 P = withP (C.dat0 C.triv) P := rfl

theorem hasType_rows {D : D7} {T : Type} (C : LevCh D T) {Sp : D.what₂.Tau → _} (θ) (M : Mult.DSModel (Yc D 0) Sp)
    (P : LevelP C.Pg D.R.r ℂ) {Tm : Mult.MMap M}
    (h : Tm ∈ Mult.Mult θ M (levS _ (C.βY 0) (C.dat0 P)) (levChi _ (C.βY 0) (C.dat0 P))) (v : M.Vec) :
    HasType (Yc D 0) (C.βY 0) (flag1L (C.dat0 C.triv)) (Tm v) := by
  rw [levelChoiceData_eq_withLevel_trivial] at h
  exact hasType_flag1 (L := C.dat0 C.triv) (P := P) fun κ hκ x => principalLevelFrame.mult_lev h v κ hκ x

theorem levChi_flag {D : D7} {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} (hs : L.s = 0) (hQ : L.Q = ∅)
    (x : Theta.GA D V) : levChi V β (flagL L) x = 1 := by
  unfold levChi levFn
  have h2 : ext1 (flagL L).P.H (flagL L).P.chi (rTup β (flagL L) (finE V x)) = 1 := subgroupCharExtension_one_apply _ _
  have h3 : (flagL L).s = 0 := hs
  have h4 : (flagL L).Q = ∅ := hQ
  rw [h2, h3, h4]
  simp

theorem fix_of_lifts_comp {D : D7} {s : ∀ k : Fin 2, D.nd.PlG k → SplitPlace D.host.E}
    {j : ∀ k v, ℚ_[D.host.g k] ≃+* (s k v).v.adicCompletion (maximalRealSubfield D.host.E)}
    {V : HSp D} {Sp : D.what₂.Tau → _} (P : principalLevelFrame.RowPsi V D.R.r) (M : Mult.DSModel V Sp) (β : GL (Fin V.rank) (EAf D))
    (L : LevDat D.host.E ℂ V.rank) (hs : L.s = 0) (hQ : L.Q = ∅) (φ : GAf D.host.E D.R.r →* GAf D.host.E D.R.r)
    (ρ : Representation ℂ (G0g D.nd) (KFix D s j ((principalLevelFrame.actM P M).comp φ)))
    (hρ : ∀ k v y x, IsLiftAt (s k v) (j k v) y x → ∀ z,
      ((ρ (GlobalTheory.GoodTypes.facHom D k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y)) z : KFix D s j ((principalLevelFrame.actM P M).comp φ)) :
        Mult.MMap M) = ((principalLevelFrame.actM P M).comp φ) x z)
    {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (cG : G0 L.Pg L.r ≃* G0g D.nd)
    (e : MonoidAlgebra ℂ (G0g D.nd)) (hc : ∀ g, e.coeff (cG (eG g)) = c g)
    (hl : ∀ k v y x, IsLiftAt (s k v) (j k v) y x →
      IsLevelLift V β L (cG.symm (GlobalTheory.GoodTypes.facHom D k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y))) (P.ψ (φ x)))
    (Tm : Mult.MMap M) (hK : Tm ∈ KFix D s j ((principalLevelFrame.actM P M).comp φ))
    (hty : ∀ v, HasType V β (flag1L L) (Tm v)) (hfix : Mult.postOn M (gaL V β L eG c) Tm = Tm) :
    ρ.asAlgebraHom e ⟨Tm, hK⟩ = ⟨Tm, hK⟩ := by
  have key := exists_act ((principalLevelFrame.actM P M).comp φ) ρ hρ (fun a x => IsLevelLift V β L (cG.symm a) (P.ψ (φ x)))
    (by
      refine ⟨P.into _, ?_, ?_⟩
      · rw [map_one φ, map_one P.ψ, map_one (finE V)]; exact one_mem _
      · rw [map_one φ, map_one P.ψ, map_one (finE V), rTup_one, map_one])
    (fun a x b y hx hy => by
      refine ⟨P.into _, ?_, ?_⟩
      · rw [map_mul φ, map_mul P.ψ, map_mul (finE V)]; exact mul_mem hx.2.1 hy.2.1
      · rw [map_mul φ, map_mul P.ψ, map_mul (finE V), rTup_mul hx.2.1 hy.2.1, hx.2.2, hy.2.2, map_mul])
    hl
  apply Subtype.ext
  rw [asAlgebraHom_eq_sum ρ (eG.trans cG).toEquiv, Submodule.coe_sum]
  apply MultilinearMap.ext
  intro v
  funext h
  have h1 : (∑ g : G, c g • actL V β L (eG g)) (Tm v) h = Tm v h :=
    congrFun (congrArg (fun U : Mult.MMap M => U v) hfix) h
  rw [LinearMap.sum_apply, Finset.sum_apply] at h1
  rw [MultilinearMap.sum_apply, Finset.sum_apply]
  refine Eq.trans (Finset.sum_congr rfl fun g _ => ?_) h1
  obtain ⟨x, hx, hx'⟩ := key (cG (eG g))
  rw [MulEquiv.symm_apply_apply] at hx
  have h2 := level_action_spec (hty v) ⟨_, hx⟩ _ hx h
  rw [levChi_flag hs hQ, inv_one, one_mul] at h2
  have e1 : (eG.trans cG).toEquiv g = cG (eG g) := rfl
  rw [e1, hc, Submodule.coe_smul, hx']
  exact congrArg (c g * ·) h2.symm

theorem good_idem_fix_conj : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) {X0 : BaseLevelRowSide D} (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → ∀ (s : ∀ k : Fin 2, D.nd.PlG k → SplitPlace D.host.E) (j : ∀ k v, ℚ_[D.host.g k] ≃+* (s k v).v.adicCompletion (maximalRealSubfield D.host.E)), (∀ k v, (s k v).w = D.naut.plGw k v) → (∀ k v, Continuous (j k v)) → ∀ (c : GAf D.host.E D.R.r), (∀ (k : Fin 2) (v : D.nd.PlG k) (y : GL (Fin D.R.r) ℤ_[D.host.g k]) (x : GAf D.host.E D.R.r), IsLiftAt (s k v) (j k v) y x → IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (cG.symm (GlobalTheory.GoodTypes.facHom D k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y))) (Y.PY.ψ (c * x * c⁻¹))) → ∀ (ρ : Representation ℂ (G0g D.nd) (KFix D s j ((principalLevelFrame.actM Y.PY (R.MY 0)).comp (MulAut.conj c).toMonoidHom))), (∀ (k : Fin 2) (v : D.nd.PlG k) (y : GL (Fin D.R.r) ℤ_[D.host.g k]) (x : GAf D.host.E D.R.r), IsLiftAt (s k v) (j k v) y x → ∀ z, ((ρ (GlobalTheory.GoodTypes.facHom D k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y)) z : KFix D s j ((principalLevelFrame.actM Y.PY (R.MY 0)).comp (MulAut.conj c).toMonoidHom)) : Mult.MMap (R.MY 0)) = ((principalLevelFrame.actM Y.PY (R.MY 0)).comp (MulAut.conj c).toMonoidHom) x z) → ∀ (b : Bool) (Tm : Mult.MMap (R.MY 0)) (hK : Tm ∈ KFix D s j ((principalLevelFrame.actM Y.PY (R.MY 0)).comp (MulAut.conj c).toMonoidHom)), Tm ∈ Mult.goodPart R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) R.toRealDat.e0 → ρ.asAlgebraHom D.ntypes.e0 ⟨Tm, hK⟩ = ⟨Tm, hK⟩ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP s j _ _ c hc ρ hρ b Tm hK hT
  obtain ⟨-, -, -, hco, -, -⟩ := hP.keep.grp
  exact fix_of_lifts_comp Y.PY (R.MY 0) (R.βY 0) (R.dat0 R.triv) rfl rfl (MulAut.conj c).toMonoidHom ρ hρ R.eG
    (RealDat.eC (A := A3.A) D.what₂.embLL) cG D.ntypes.e0 (fun g => (hco g).symm) hc Tm hK
    (fun v => hasType_rows R.toLevCh R.θ (R.MY 0) _ hT.1 v) (sub_eq_zero.1 (LinearMap.mem_ker.1 hT.2))

end GlobalTheory.RowGood

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorEqGoodIdempotentTypePlacesStatement
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodProjector_eq_goodIdempotent_typePlaces : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) {X0 : BaseLevelRowSide D} (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → ∀ (s : ∀ k : Fin 2, D.nd.PlG k → SplitPlace D.host.E) (j : ∀ k v, ℚ_[D.host.g k] ≃+* (s k v).v.adicCompletion (maximalRealSubfield D.host.E)), (∀ k v, (s k v).w = D.naut.plGw k v) → (∀ k v, Continuous (j k v)) → ∀ (c : GAf D.host.E D.R.r), (∀ (k : Fin 2) (v : D.nd.PlG k) (y : GL (Fin D.R.r) ℤ_[D.host.g k]) (x : GAf D.host.E D.R.r), IsLiftAt (s k v) (j k v) y x → IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (cG.symm (GlobalTheory.GoodTypes.facHom D k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y))) (Y.PY.ψ (c * x * c⁻¹))) → ∀ (ρ : Representation ℂ (G0g D.nd) (KFix D s j ((principalLevelFrame.actM Y.PY (R.MY 0)).comp (MulAut.conj c).toMonoidHom))), (∀ (k : Fin 2) (v : D.nd.PlG k) (y : GL (Fin D.R.r) ℤ_[D.host.g k]) (x : GAf D.host.E D.R.r), IsLiftAt (s k v) (j k v) y x → ∀ z, ((ρ (GlobalTheory.GoodTypes.facHom D k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y)) z : KFix D s j ((principalLevelFrame.actM Y.PY (R.MY 0)).comp (MulAut.conj c).toMonoidHom)) : Mult.MMap (R.MY 0)) = ((principalLevelFrame.actM Y.PY (R.MY 0)).comp (MulAut.conj c).toMonoidHom) x z) → ∀ (b : Bool) (Tm : Mult.MMap (R.MY 0)) (hK : Tm ∈ KFix D s j ((principalLevelFrame.actM Y.PY (R.MY 0)).comp (MulAut.conj c).toMonoidHom)), Tm ∈ Mult.goodPart R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) R.toRealDat.e0 → ρ.asAlgebraHom D.ntypes.e0 ⟨Tm, hK⟩ = ⟨Tm, hK⟩ := by
  first | exact @GlobalTheory.RowGood.good_idem_fix_conj | exact GlobalTheory.RowGood.good_idem_fix_conj | (intros; apply GlobalTheory.RowGood.good_idem_fix_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicSubLtOne
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowGood

open Matrix
open scoped TensorProduct

section Res

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def tr {F1 : Subfield E} (h : F1 = maximalRealSubfield E) : AL E →+* E ⊗[F1] Formalism.L2.Herm.Af F1 :=
  (GlobalTheory.LevSplit.swp F1 E).comp (GlobalTheory.Mem.R3.swapCast h).symm.toRingHom

theorem tr_rfl (z : AL E) : tr (rfl : maximalRealSubfield E = maximalRealSubfield E) z = z := by
  exact (Algebra.TensorProduct.comm _ _ _).apply_symm_apply z

theorem tr_int {F1 : Subfield E} (h : F1 = maximalRealSubfield E) {z : AL E} (hz : z ∈ ALint E) :
    tr h z ∈ Formalism.L2.Herm.intAf F1 E := by
  subst h
  rw [tr_rfl]
  have key : ReciprocityTheory.Aut.ALint E ≤ Formalism.L2.Herm.intAf (maximalRealSubfield E) E := by
    unfold ReciprocityTheory.Aut.ALint
    rw [Subring.closure_le]
    rintro x (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · exact Subring.subset_closure (Or.inl ⟨⟨(y : E), y, rfl⟩, rfl⟩)
    · exact Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
  exact key hz

theorem proj_le_one (s : SplitPlace E) {z : AL E} (hz : z ∈ Formalism.L2.Herm.intAf (maximalRealSubfield E) E) :
    Valued.v (s.proj z) ≤ 1 := by
  have key : Formalism.L2.Herm.intAf (maximalRealSubfield E) E ≤
      (s.v.adicCompletionIntegers (maximalRealSubfield E)).toSubring.comap s.proj := by
    show Subring.closure _ ≤ _
    rw [Subring.closure_le]
    rintro x (⟨⟨_, b, rfl⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩)
    · rw [SetLike.mem_coe, Subring.mem_comap, ValuationSubring.mem_toSubring,
        IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      simp only [ReciprocityTheory.Aut.SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      exact s.split_le_one b
    · rw [SetLike.mem_coe, Subring.mem_comap, ValuationSubring.mem_toSubring]
      simp only [ReciprocityTheory.Aut.SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      exact ha s.v
  have := key hz
  rwa [Subring.mem_comap, ValuationSubring.mem_toSubring,
    IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at this

theorem res_eq {F1 : Subfield E} (h : F1 = maximalRealSubfield E) (s : SplitPlace E) (z : AL E)
    (y : Formalism.L2.Herm.intAf F1 E) (hy : (y : E ⊗[F1] Formalism.L2.Herm.Af F1) = tr h z) (a : 𝓞 E)
    (ha : Valued.v (s.proj z - s.i (a : E)) < 1) : resS F1 s.w y = Ideal.Quotient.mk _ a := by
  subst h
  have key : ∀ (t : E ⊗[maximalRealSubfield E] Formalism.L2.Herm.Af (maximalRealSubfield E))
      (ht : t ∈ Formalism.L2.Herm.intAf (maximalRealSubfield E) E),
      ∃ c : 𝓞 E, Valued.v (s.proj t - s.i (c : E)) < 1 ∧
        resS (maximalRealSubfield E) s.w ⟨t, ht⟩ = Ideal.Quotient.mk _ c := by
    intro t ht
    refine Subring.closure_induction
      (p := fun t ht => ∃ c : 𝓞 E, Valued.v (s.proj t - s.i (c : E)) < 1 ∧
        resS (maximalRealSubfield E) s.w ⟨t, ht⟩ = Ideal.Quotient.mk _ c) ?_ ?_ ?_ ?_ ?_ ?_ ht
    · rintro x (⟨⟨_, b, rfl⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩)
      · refine ⟨b, ?_, ?_⟩
        · simp [ReciprocityTheory.Aut.SplitPlace.proj]
        · have e : (⟨_, Subring.subset_closure (Or.inl ⟨⟨_, b, rfl⟩, rfl⟩)⟩ : Formalism.L2.Herm.intAf (maximalRealSubfield E) E) =
              Formalism.L2.DIV.oToS (maximalRealSubfield E) E b :=
            Subtype.ext (Formalism.L2.DIV.oToS_coe (F := maximalRealSubfield E) b).symm
          rw [e, Formalism.L2.DIV.resS_oToS]
      · obtain ⟨D0, hD0, hD0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot s.v.ne_bot
        obtain ⟨r, hr⟩ := Formalism.UG.P.csApprox_local s.v D0 hD0ne (a s.v) (ha s.v)
        have hlt : s.v.intValuation D0 < 1 := by
          exact (s.v.intValuation_lt_one_iff_mem D0).mpr hD0
        have hi : s.i (((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) r : 𝓞 E)) : E) =
            algebraMap (𝓞 (maximalRealSubfield E)) (s.v.adicCompletion (maximalRealSubfield E)) r := by
          rw [ReciprocityTheory.Aut.split_coe_algebraMap, AlgHom.commutes,
            IsScalarTower.algebraMap_apply (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)
              (s.v.adicCompletion (maximalRealSubfield E)) r]
        refine ⟨algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) r, ?_, ?_⟩
        · have hp : s.proj ((1 : E) ⊗ₜ[maximalRealSubfield E] a) = a s.v := by
            simp only [ReciprocityTheory.Aut.SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
              Algebra.TensorProduct.lift_tmul, map_one, one_mul]
            rfl
          rw [hp, hi]
          exact hr.trans hlt
        · have hsplit : (⟨_, Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)⟩ : Formalism.L2.Herm.intAf (maximalRealSubfield E) E) =
              Formalism.L2.DIV.adS (maximalRealSubfield E) E (⟨a, ha⟩ - Formalism.L2.DIV.oToAd (maximalRealSubfield E) r) +
                Formalism.L2.DIV.oToS (maximalRealSubfield E) E (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) r) := by
            rw [← Formalism.L2.DIV.adS_oToAd, ← map_add (f := _), sub_add_cancel]
            exact Subtype.ext (Formalism.L2.DIV.adS_coe (E := E) ⟨a, ha⟩).symm
          rw [hsplit, map_add (f := _), Formalism.L2.DIV.resS_oToS, Formalism.L2.DIV.resS_adS_eq_zero s.w s.v s.w_under.symm, zero_add]
          show Valued.v (a s.v - algebraMap (𝓞 (maximalRealSubfield E)) (s.v.adicCompletion (maximalRealSubfield E)) r) < 1
          exact hr.trans hlt
    · refine ⟨0, by simp, ?_⟩
      change resS (maximalRealSubfield E) s.w 0 = _
      simp
    · refine ⟨1, by simp, ?_⟩
      change resS (maximalRealSubfield E) s.w 1 = _
      simp
    · rintro x y hx hy ⟨c1, h1, e1⟩ ⟨c2, h2, e2⟩
      refine ⟨c1 + c2, ?_, ?_⟩
      · have : s.proj (x + y) - s.i ((c1 + c2 : 𝓞 E) : E) = (s.proj x - s.i (c1 : E)) + (s.proj y - s.i (c2 : E)) := by
          push_cast
          rw [map_add (f := _), map_add (f := _)]
          ring
        rw [this]
        exact Valuation.map_add_lt _ h1 h2
      · change resS (maximalRealSubfield E) s.w (⟨x, hx⟩ + ⟨y, hy⟩) = _
        rw [map_add (f := _), e1, e2, map_add (f := _)]
    · rintro x hx ⟨c1, h1, e1⟩
      refine ⟨-c1, ?_, ?_⟩
      · have : s.proj (-x) - s.i ((-c1 : 𝓞 E) : E) = -(s.proj x - s.i (c1 : E)) := by
          push_cast
          rw [map_neg, map_neg]
          ring
        rw [this, Valuation.map_neg]
        exact h1
      · change resS (maximalRealSubfield E) s.w (-⟨x, hx⟩) = _
        rw [map_neg, e1, map_neg]
    · rintro x y hx hy ⟨c1, h1, e1⟩ ⟨c2, h2, e2⟩
      refine ⟨c1 * c2, ?_, ?_⟩
      · have : s.proj (x * y) - s.i ((c1 * c2 : 𝓞 E) : E) =
            s.proj x * (s.proj y - s.i (c2 : E)) + (s.proj x - s.i (c1 : E)) * s.i (c2 : E) := by
          push_cast
          rw [map_mul, map_mul]
          ring
        rw [this]
        have hx1 : Valued.v (s.proj x) ≤ 1 := proj_le_one s hx
        have hc2 : Valued.v (s.i (c2 : E)) ≤ 1 := s.split_le_one c2
        refine Valuation.map_add_lt _ ?_ ?_
        · rw [Valuation.map_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_left' hx1) h2
        · rw [Valuation.map_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_right' hc2) h1
      · change resS (maximalRealSubfield E) s.w (⟨x, hx⟩ * ⟨y, hy⟩) = _
        rw [map_mul, e1, e2, map_mul]
  obtain ⟨c, hc1, hc2⟩ := key y.1 y.2
  have hyz : (y : E ⊗[maximalRealSubfield E] Formalism.L2.Herm.Af (maximalRealSubfield E)) = z := by rw [hy, tr_rfl]
  rw [hyz] at hc1
  have hca : Valued.v (s.i ((c - a : 𝓞 E) : E)) < 1 := by
    have : s.i ((c - a : 𝓞 E) : E) = (s.proj z - s.i (a : E)) - (s.proj z - s.i (c : E)) := by
      push_cast
      rw [map_sub]
      ring
    rw [this]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ha hc1)
  have hmem : c - a ∈ s.w.asIdeal := (s.split_mem_ideal (c - a)).mpr hca
  have hyy : (⟨y.1, y.2⟩ : Formalism.L2.Herm.intAf (maximalRealSubfield E) E) = y := rfl
  rw [hyy] at hc2
  rw [hc2]
  exact Ideal.Quotient.eq.mpr hmem

end Res

section Padic

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {g : ℕ} [Fact g.Prime]

end Padic

end GlobalTheory.RowGood

end

noncomputable section

namespace GlobalTheory.RowGood

open Matrix
open scoped TensorProduct

end GlobalTheory.RowGood

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivOutsideMul
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TypeAct

section General

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem trivOutside_mul {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x y : GAf L n}
    (hx : TrivOutside T x) (hy : TrivOutside T y) : TrivOutside T (x * y) := by
  intro v hv
  show (((x.1 * y.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v) = 1
  rw [Units.val_mul, Matrix.map_mul, hx v hv, hy v hv, Matrix.one_mul]

theorem trivOutside_inv {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x : GAf L n}
    (hx : TrivOutside T x) : TrivOutside T x⁻¹ := by
  intro v hv
  have e : (((x⁻¹ : GAf L n).1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v) *
      ((x.1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L v) = 1 := by
    rw [← Matrix.map_mul]
    have : ((x⁻¹ : GAf L n).1 : Matrix (Fin n) (Fin n) (AL L)) * (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
    rw [this, Matrix.map_one _ (map_zero _) (map_one _)]
  rwa [hx v hv, Matrix.mul_one] at e

theorem commute_of_ne {v w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} (hvw : v ≠ w) {x y : GAf L n}
    (hx : TrivOutside {v} x) (hy : TrivOutside {w} y) : Commute x y := by
  show x * y = y * x
  apply Subtype.ext; apply Units.ext
  show (x.1 : Matrix (Fin n) (Fin n) (AL L)) * y.1 = (y.1 : Matrix (Fin n) (Fin n) (AL L)) * x.1
  ext i k
  rw [← sub_eq_zero]
  apply GlobalTheory.InertUmax.eq_zero_of_compAt L
  intro u
  rw [map_sub, sub_eq_zero]
  have hmx : ∀ A B : Matrix (Fin n) (Fin n) (AL L),
      compAt L u ((A * B) i k) = (A.map (compAt L u) * B.map (compAt L u)) i k := by
    intro A B; rw [← Matrix.map_mul]; rfl
  rw [hmx, hmx]
  by_cases hu : u = v
  · subst hu
    rw [hy u (by simpa using hvw), mul_one, one_mul]
  · rw [hx u (by simpa using hu), mul_one, one_mul]

variable {g : ℕ} [Fact g.Prime]

theorem isLiftAt_mul {s : SplitPlace L} {j : ℚ_[g] ≃+* s.v.adicCompletion (maximalRealSubfield L)}
    {y y' : GL (Fin n) ℤ_[g]} {x x' : GAf L n} (h : IsLiftAt s j y x) (h' : IsLiftAt s j y' x') :
    IsLiftAt s j (y * y') (x * x') :=
  ⟨trivOutside_mul h.1 h'.1, by rw [map_mul, h.2, h'.2, map_mul, map_mul]⟩

theorem isLiftAt_inv {s : SplitPlace L} {j : ℚ_[g] ≃+* s.v.adicCompletion (maximalRealSubfield L)}
    {y : GL (Fin n) ℤ_[g]} {x : GAf L n} (h : IsLiftAt s j y x) : IsLiftAt s j y⁻¹ x⁻¹ :=
  ⟨trivOutside_inv h.1, by rw [map_inv, h.2, map_inv, map_inv]⟩

theorem exists_isLiftAt (s : SplitPlace L) (j : ℚ_[g] ≃+* s.v.adicCompletion (maximalRealSubfield L))
    (y : GL (Fin n) ℤ_[g]) : ∃ x : GAf L n, IsLiftAt s j y x :=
  GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s _

end General

section Fix

variable (D : D7) (s : ∀ k : Fin 2, D.nd.PlG k → SplitPlace D.host.E)
    (j : ∀ k v, ℚ_[D.host.g k] ≃+* (s k v).v.adicCompletion (maximalRealSubfield D.host.E))
    {A : Type} [AddCommGroup A] [Module ℂ A] (ρA : GAf D.host.E D.R.r →* Module.End ℂ A)

theorem fix_of_mem {z : A} (hz : z ∈ KFix D s j ρA) {k : Fin 2} {v : D.nd.PlG k} {y : GL (Fin D.R.r) ℤ_[D.host.g k]}
    {x : GAf D.host.E D.R.r} (hl : IsLiftAt (s k v) (j k v) y x) (hy : GlobalTheory.GLp.red (D.host.g k) D.R.r y = 1) :
    ρA x z = z := by
  simp only [KFix, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hz
  exact hz k v ⟨y, hy⟩ x hl

theorem eq_of_red_eq {z : A} (hz : z ∈ KFix D s j ρA) {k : Fin 2} {v : D.nd.PlG k}
    {y y' : GL (Fin D.R.r) ℤ_[D.host.g k]} {x x' : GAf D.host.E D.R.r} (hl : IsLiftAt (s k v) (j k v) y x)
    (hl' : IsLiftAt (s k v) (j k v) y' x')
    (he : GlobalTheory.GLp.red (D.host.g k) D.R.r y = GlobalTheory.GLp.red (D.host.g k) D.R.r y') : ρA x z = ρA x' z := by
  have h1 := fix_of_mem D s j ρA hz (isLiftAt_mul (isLiftAt_inv hl) hl') (by rw [map_mul, map_inv, he, inv_mul_cancel])
  symm
  calc ρA x' z = ρA x (ρA (x⁻¹ * x') z) := by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
    _ = ρA x z := by rw [h1]

variable {D s j}

theorem map_mem (hinj : Function.Injective (fun kv : (Σ k : Fin 2, D.nd.PlG k) => (s kv.1 kv.2).v))
    {z : A} (hz : z ∈ KFix D s j ρA) {k : Fin 2} {v : D.nd.PlG k} {y : GL (Fin D.R.r) ℤ_[D.host.g k]}
    {x : GAf D.host.E D.R.r} (hl : IsLiftAt (s k v) (j k v) y x) : ρA x z ∈ KFix D s j ρA := by
  simp only [KFix, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero]
  rintro k' v' ⟨y', hy'⟩ x' hl'
  by_cases h : (⟨k', v'⟩ : Σ k : Fin 2, D.nd.PlG k) = ⟨k, v⟩
  · obtain ⟨rfl, hv⟩ := Sigma.mk.inj_iff.mp h
    cases eq_of_heq hv
    have h1 := fix_of_mem D s j ρA hz (isLiftAt_mul (isLiftAt_mul (isLiftAt_inv hl) hl') hl)
      (by rw [map_mul, map_mul, map_inv, hy', mul_one, inv_mul_cancel])
    rw [← Module.End.mul_apply, ← map_mul]
    conv_rhs => rw [← h1]
    rw [← Module.End.mul_apply, ← map_mul]
    simp only [mul_assoc, mul_inv_cancel_left]
  · have hne : (s k' v').v ≠ (s k v).v := fun e => h (hinj e)
    rw [← Module.End.mul_apply, ← map_mul, (commute_of_ne hne hl'.1 hl.1).eq, map_mul, Module.End.mul_apply,
      fix_of_mem D s j ρA hz hl' hy']

variable (D s j)

def liftAt (k : Fin 2) (v : D.nd.PlG k) (h : GL (Fin D.R.r) (ZMod (D.host.g k))) : GAf D.host.E D.R.r :=
  Classical.choose (exists_isLiftAt (n := D.R.r) (s k v) (j k v)
    (Function.surjInv (GlobalTheory.GLp.Model.red_surjective (g := D.host.g k) D.R.r) h))

theorem isLiftAt_liftAt (k : Fin 2) (v : D.nd.PlG k) (h : GL (Fin D.R.r) (ZMod (D.host.g k))) :
    IsLiftAt (s k v) (j k v) (Function.surjInv (GlobalTheory.GLp.Model.red_surjective (g := D.host.g k) D.R.r) h)
      (liftAt D s j k v h) :=
  Classical.choose_spec (exists_isLiftAt (n := D.R.r) (s k v) (j k v) _)

theorem red_surjInv (k : Fin 2) (h : GL (Fin D.R.r) (ZMod (D.host.g k))) :
    GlobalTheory.GLp.red (D.host.g k) D.R.r (Function.surjInv (GlobalTheory.GLp.Model.red_surjective (g := D.host.g k) D.R.r) h) = h :=
  Function.surjInv_eq _ h

theorem liftAt_apply {z : A} (hz : z ∈ KFix D s j ρA) {k : Fin 2} {v : D.nd.PlG k} {y : GL (Fin D.R.r) ℤ_[D.host.g k]}
    {x : GAf D.host.E D.R.r} (hl : IsLiftAt (s k v) (j k v) y x) :
    ρA (liftAt D s j k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y)) z = ρA x z :=
  eq_of_red_eq D s j ρA hz (isLiftAt_liftAt D s j k v _) hl (red_surjInv D k _)

def factAct (hinj : Function.Injective (fun kv : (Σ k : Fin 2, D.nd.PlG k) => (s kv.1 kv.2).v)) (k : Fin 2)
    (v : D.nd.PlG k) : GL (Fin D.R.r) (ZMod (D.host.g k)) →* Module.End ℂ (KFix D s j ρA) where
  toFun h := (ρA (liftAt D s j k v h)).restrict (fun z hz => map_mem ρA hinj hz (isLiftAt_liftAt D s j k v h))
  map_one' := by
    apply LinearMap.ext; rintro ⟨z, hz⟩
    apply Subtype.ext
    simp only [LinearMap.restrict_apply, Module.End.one_apply]
    have := eq_of_red_eq D s j ρA hz (isLiftAt_liftAt D s j k v 1) (⟨?_, ?_⟩ : IsLiftAt (s k v) (j k v) 1 1)
      (by rw [red_surjInv, map_one])
    · rw [this, map_one, Module.End.one_apply]
    · intro u _; exact Matrix.map_one _ (map_zero _) (map_one _)
    · rw [map_one, map_one, map_one]
  map_mul' a b := by
    apply LinearMap.ext; rintro ⟨z, hz⟩
    apply Subtype.ext
    simp only [LinearMap.restrict_apply, Module.End.mul_apply]
    rw [eq_of_red_eq D s j ρA hz (isLiftAt_liftAt D s j k v (a * b))
      (isLiftAt_mul (isLiftAt_liftAt D s j k v a) (isLiftAt_liftAt D s j k v b))
      (by rw [red_surjInv, map_mul, red_surjInv, red_surjInv]), map_mul, Module.End.mul_apply]

theorem factAct_apply (hinj : Function.Injective (fun kv : (Σ k : Fin 2, D.nd.PlG k) => (s kv.1 kv.2).v))
    {k : Fin 2} {v : D.nd.PlG k} {y : GL (Fin D.R.r) ℤ_[D.host.g k]} {x : GAf D.host.E D.R.r}
    (hl : IsLiftAt (s k v) (j k v) y x) (z : KFix D s j ρA) :
    ((factAct D s j ρA hinj k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y) z : KFix D s j ρA) : A) = ρA x z :=
  liftAt_apply D s j ρA z.2 hl

theorem factAct_commute (hinj : Function.Injective (fun kv : (Σ k : Fin 2, D.nd.PlG k) => (s kv.1 kv.2).v)) :
    Pairwise fun (a b : Σ k : Fin 2, D.nd.PlG k) => ∀ (x : GL (Fin D.R.r) (ZMod (D.host.g a.1)))
      (y : GL (Fin D.R.r) (ZMod (D.host.g b.1))),
      Commute (factAct D s j ρA hinj a.1 a.2 x) (factAct D s j ρA hinj b.1 b.2 y) := by
  rintro ⟨k, v⟩ ⟨k', v'⟩ hne x y
  have hv : (s k v).v ≠ (s k' v').v := fun e => hne (hinj e)
  have hc := commute_of_ne hv (isLiftAt_liftAt D s j k v x).1 (isLiftAt_liftAt D s j k' v' y).1
  apply LinearMap.ext; rintro ⟨z, hz⟩
  apply Subtype.ext
  show ρA (liftAt D s j k v x) (ρA (liftAt D s j k' v' y) z) = ρA (liftAt D s j k' v' y) (ρA (liftAt D s j k v x) z)
  rw [← Module.End.mul_apply, ← map_mul, hc.eq, map_mul, Module.End.mul_apply]

end Fix

theorem exists_rep : ∀ (D : D7) (s : ∀ k : Fin 2, D.nd.PlG k → SplitPlace D.host.E) (j : ∀ k v, ℚ_[D.host.g k] ≃+* (s k v).v.adicCompletion (maximalRealSubfield D.host.E)), Function.Injective (fun kv : (Σ k : Fin 2, D.nd.PlG k) => (s kv.1 kv.2).v) → ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (ρA : GAf D.host.E D.R.r →* Module.End ℂ A), ∃ ρ : Representation ℂ (G0g D.nd) (KFix D s j ρA), ∀ (k : Fin 2) (v : D.nd.PlG k) (y : GL (Fin D.R.r) ℤ_[D.host.g k]) (x : GAf D.host.E D.R.r), IsLiftAt (s k v) (j k v) y x → ∀ z : KFix D s j ρA, ((ρ (GlobalTheory.GoodTypes.facHom D k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y)) z : KFix D s j ρA) : A) = ρA x z := by
  intro D s j hinj A _ _ ρA
  classical
  refine ⟨MonoidHom.noncommPiCoprod (fun kv => factAct D s j ρA hinj kv.1 kv.2) (factAct_commute D s j ρA hinj), ?_⟩
  intro k v y x hl z
  rw [GlobalTheory.GoodTypes.facHom, MonoidHom.mulSingle_apply, MonoidHom.noncommPiCoprod_mulSingle]
  exact factAct_apply D s j ρA hinj hl z

end GlobalTheory.TypeAct

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFramedPointGoodReductionDefiniteSignatur
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFramedPointGoodReductionDefiniteSignatur
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GoodPts GlobalTheory.DefiniteAbelian
open scoped CategoryTheory.Obj

namespace GlobalTheory.GoodDefinite

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem abLocus_eq_univ_of_definite (Xo : Moduli Dw l) (hq : Dw.q = 0) (T : CDVR) (x : Sp T.Fr ⟶ Xo.X)
    (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m₁ : SABMap t' Xo.univ.t x)
    (m₂ : SABMap t' G (spMap (algebraMap T.V T.Fr))) : abLocus G.G = Set.univ := by
  obtain ⟨m, hm, hw⟩ := exists_w0_relation H
  obtain ⟨b, hb⟩ := Spec.map_surjective (x ≫ Xo.s)
  let β : KA l →+* T.Fr := b.hom
  have hβ : x ≫ Xo.s = spMap β := hb.symm
  have : CharZero T.Fr := (RingHom.charZero_iff β.injective).1 inferInstance
  let ρ : T.Fr := β (baseKA l).ρ
  have hρ : ρ ^ 2 = -(H.d : T.Fr) := by rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  have hm' : (4 : T.Fr) * m = 1 + H.d := by exact_mod_cast hm
  let z : T.Fr := (1 + ρ) / 2
  have hz2 : 2 * z = 1 + ρ := mul_div_cancel₀ _ two_ne_zero
  have hz : z * z + m = z := mul_left_cancel₀ (show (4 : T.Fr) ≠ 0 by norm_num) (by
    linear_combination (2 * z + ρ - 1) * hz2 + hρ + hm')
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : T.V, algebraMap T.V T.Fr z₀ = z := by
    rcases ValuationRing.isInteger_or_isInteger T.V z with h | ⟨u, hu⟩
    · exact h
    · by_cases h0 : z = 0
      · exact ⟨0, by rw [h0, map_zero]⟩
      · refine ⟨1 - m * u, ?_⟩
        rw [map_sub, map_one, map_mul, map_natCast, hu]
        field_simp
        linear_combination -hz
  let L := AlgebraicClosure T.Fr
  let a : T.Fr →+* L := algebraMap T.Fr L
  have : CharZero L := (RingHom.charZero_iff a.injective).1 inferInstance
  have hdet := (Xo.univ.geom L (spMap a ≫ x) (a.comp β) (by rw [Category.assoc, hβ, sp_comp])).1
  have h₁ := actsBy_of_detCond Dw hq _ (spMap a ≫ x) _ (a z)
    (by rw [← map_ofNat a 2, ← map_mul, hz2, map_add (f := _), map_one]; rfl) hdet
  have h₂ := (actsBy_pull m₂.cart (m₂.act H.w0) (spMap a) _).1 ((actsBy_pull m₁.cart (m₁.act H.w0) (spMap a) _).2 h₁)
  have := G.semi.smooth
  have := G.semi.separated
  have := G.act.hom H.w0
  have h₃ : ActsBy G.G (G.act.act H.w0) (𝟙 _) z₀ := by
    refine actsBy_of_injective (a.comp (algebraMap T.V T.Fr))
      (a.injective.comp (IsFractionRing.injective T.V T.Fr)) _ _ ?_
    rw [Category.comp_id, ← sp_comp, RingHom.comp_apply, hz₀]
    exact h₂
  refine Set.eq_univ_of_forall fun p K _ _ t _ => ?_
  obtain ⟨j, hj⟩ := Spec.map_surjective t
  have h₄ := actsBy_baseChange (k := K) j.hom (𝟙 _) _ h₃
  have ht : spMap j.hom ≫ 𝟙 _ = t := (Category.comp_id _).trans hj
  rw [ht] at h₄
  obtain ⟨X⟩ := G.semi.fibres K t
  exact isProper_of_actsBy X (OAct.pullback t G.G G.act) H.d_prime hm hw _
    ((actsBy_pull (isGrpPullback_pullback G.G t) (pullback.lift_fst _ _ _) _ _).2 (by rwa [Category.id_comp]))

theorem good_of_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), Dw.q = 0 →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), Good y := by
  intro E _ _ _ H Dw l Xo c hq T io y
  obtain ⟨G, t', m₁, m₂, -⟩ := y.2.2
  exact ⟨G, t', m₁, m₂, GlobalTheory.GoodProper.isProper_of_abLocus_eq_univ E H Dw l Xo T _ G t' m₁ m₂
    (abLocus_eq_univ_of_definite Xo hq T _ G t' m₁ m₂)⟩

end GlobalTheory.GoodDefinite
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFramedPointGoodReductionDefiniteSignaturStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg GlobalTheory.GoodPts GlobalTheory.GoodTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_framed_point_good_reduction_definite_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), Dw.q = 0 → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), Good y := by
  first | exact @GlobalTheory.GoodDefinite.good_of_definite | exact GlobalTheory.GoodDefinite.good_of_definite | (intros; apply GlobalTheory.GoodDefinite.good_of_definite <;> assumption)
end
end
