module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BciNarrowSwap
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LRSplit
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.ExistsCgTrueCharSide
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SphRead
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecSpehQuotStatement

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.UnitaryReadS
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeDefiniteGeneralOfOld
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Nontrivial
noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions.N _root_.Formalism.L2.Host GlobalTheory.CuspRep NumberField IsDedekindDomain


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
def trueK (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
    (η η' : HostCGu D.host 1)
    (h1 : ∀ w, (ParLaws.locG hL D.nd.plOm η w).unr)
    (h2 : ∀ w, ¬ IsSplitPl D.host w → (ParLaws.locG hL D.nd.plOm η w).frobEig = {-1})
    (h3 : ∀ w, (ParLaws.locG hL D.nd.plOm η' w).unr ∧ (ParLaws.locG hL D.nd.plOm η' w).frobEig = (ParLaws.locG hL D.nd.plOm η w).frobEig.map (·⁻¹))
    (h4 : ∀ w w', IsSplitPl D.host w → IsConjPl D.host w w' → ∀ a b : ℂ, (ParLaws.locG hL D.nd.plOm η w).frobEig = {a} →
      (ParLaws.locG hL D.nd.plOm η w').frobEig = {b} → a * b = 1) : CGK D.naut :=
  haveI := host_isCMField D.host
  have L := ParLaws.laws hL hF D.host D.nd.Om D.nd.plOm
  have U : ∀ {a} (π : HostCGu D.host a) w, D.naut.unr ((T.e w).symm (ParLaws.locG hL D.nd.plOm π w)) ↔ (ParLaws.locG hL D.nd.plOm π w).unr :=
    fun π w => by rw [T.unr, Equiv.apply_symm_apply]
  have Fr : ∀ {a} (π : HostCGu D.host a) w, (ParLaws.locG hL D.nd.plOm π w).unr →
      D.naut.frobEig ((T.e w).symm (ParLaws.locG hL D.nd.plOm π w)) = (ParLaws.locG hL D.nd.plOm π w).frobEig :=
    fun π w h => by rw [T.frobEig _ _ ((U π w).2 h), Equiv.apply_symm_apply]
  have Dm : ∀ {a} (π : HostCGu D.host a) w, D.naut.lpDim ((T.e w).symm (ParLaws.locG hL D.nd.plOm π w)) = a :=
    fun π w => by rw [← T.dim, Equiv.apply_symm_apply]; exact L.1 π w
  { CG := fun a => {_π : HostCGu D.host a // 0 < a}
    csd := fun π => π.1.IsCsd
    ralg := fun π => π.1.IsRegAlg
    locG := fun π w => (T.e w).symm (ParLaws.locG hL D.nd.plOm π.1 w)
    locG_dim := fun π w => Dm π.1 w
    locG_unr_ae := fun π => (L.2.1 π.1).mono fun w h => (U π.1 w).2 h
    tw := fun π χ => ⟨π.1.tw χ.1, π.2⟩
    locG_tw := fun π χ w => (T.e w).injective (by
      rw [T.char _ _ _ (Dm χ.1 w), Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact L.2.2.1 π.1 χ.1 w)
    infG := fun π τ => π.1.infChar τ
    infG_card := fun π => L.2.2.2.1 π.1
    ralg_def := fun π => L.2.2.2.2.1 π.1
    infG_tw := fun π χ => L.2.2.2.2.2.1 π.1 χ.1
    csd_tw := fun π χ => L.2.2.2.2.2.2.1 π.1 χ.1
    csd_unr := fun π w w' hπ hc hu => by
      have h := L.2.2.2.2.2.2.2.1 π.1 w w' hπ hc ((U π.1 w).1 hu)
      exact ⟨(U π.1 w').2 h.1, by rw [Fr π.1 w' h.1, Fr π.1 w ((U π.1 w).1 hu)]; exact h.2⟩
    etaT := ⟨η, one_pos⟩
    etaTinv := ⟨η', one_pos⟩
    etaT_unr := fun w => (U η w).2 (h1 w)
    etaT_inert := fun w h => by rw [Fr η w (h1 w)]; exact h2 w h
    etaTinv_def := fun w => ⟨(U η' w).2 (h3 w).1, by rw [Fr η' w (h3 w).1, Fr η w (h1 w)]; exact (h3 w).2⟩
    etaT_split := fun w w' hs hc a b ha hb => by
      rw [Fr η w (h1 w)] at ha; rw [Fr η w' (h1 w')] at hb; exact h4 w w' hs hc a b ha hb }


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
def trueCG (hL hF) (D : D7) (hE : IsEmpty D.nd.Loc) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (η η' h1 h2 h3 h4) :
    CGTrue hL (setCG D hE (trueK hL hF D T η η' h1 h2 h3 h4)) (wdCG hE _ T) where
  e := fun _ => Function.Embedding.subtype _
  surj := fun _ h π => ⟨⟨π, h⟩, rfl⟩
  zero := ⟨fun π => lt_irrefl 0 π.2⟩
  loc := fun _ _ w => (T.e w).apply_symm_apply _
  tw := fun _ _ _ => rfl
  inf := fun _ _ _ => rfl
  csd := fun _ _ => Iff.rfl

end GlobalTheory.HeightCounting
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToralOfIsSphericalLocProd
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.UnitaryBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCSupport

variable {E : Type} [Field E] [NumberField E]

abbrev clsOf {w : HeightOneSpectrum (𝓞 E)} {a : ℕ} (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) :
    IrrGL (k := w.adicCompletion E) :=
  IrrGL.of σ.ρ σ.smooth σ.irred

theorem good_of_good_locProd {c n : ℕ} {N : Fin c → ℕ} (h : ∑ i, N i = n) (w : HeightOneSpectrum (𝓞 E))
    (σ : ∀ i, SmIrr (GL (Fin (N i)) (w.adicCompletion E))) (hi : (locProd h w σ).IsIrreducible)
    (hG : Good (IrrGL.of (locProd h w σ) (isSmooth_parInd _ _) hi)) : ∀ i, Good (clsOf (σ i)) := by
  have hs : IsSubquotient (IrrGL.of (locProd h w σ) (isSmooth_parInd _ _) hi).rep
      (prodIrr (fun i => clsOf (σ i)) h) := by
    let e := prodIrrEquiv (k := w.adicCompletion E) h (fun i => (σ i).ρ) (fun i => (σ i).smooth) (fun i => (σ i).irred)
    let f := e.symm.trans (IrrGL.equivOf (locProd h w σ) (isSmooth_parInd _ _) hi)
    exact IsSubquotient.of_surjective f.toIntertwiningMap f.toLinearEquiv.surjective
  exact (GlobalTheory.RecT.good_toral_of_isSubquotient_prodIrr _ c (fun i => clsOf (σ i)) (IrrGL.of (locProd h w σ) (isSmooth_parInd _ _) hi) h hs).1 hG

theorem isSpherical_of_equiv {G X Y : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ G X} {τ : Representation ℂ G Y} (e : ρ.Equiv τ) {K : Subgroup G}
    (h : GlobalTheory.LGrp.IsSpherical ρ K) : GlobalTheory.LGrp.IsSpherical τ K := by
  obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨e.toIntertwiningMap x, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, ?_⟩
  · rw [← Representation.IntertwiningMap.isIntertwining ρ τ e.toIntertwiningMap k x, GlobalTheory.LGrp.mem_fixed.1 hx k hk]
  · intro h1
    exact h0 (e.toLinearEquiv.injective (by simpa using h1))

theorem isSphericalFor_of_eq {G X : Type} [Group G] [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ G X}
    {K K' : Subgroup G} (e : K = K') (h : GlobalTheory.SmGL.IsSphericalFor ρ K) : GlobalTheory.SmGL.IsSphericalFor ρ K' := e ▸ h

variable [IsCMField E]

end GlobalTheory.BCSupport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspReadTOfCuspRead
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
open GlobalTheory.CuspRep GlobalTheory.HeightCounting

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RecT

abbrev RecFam : Type 1 :=
  ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w), IrrGL (k := w.adicCompletion E) → WD h

set_option synthInstance.maxHeartbeats 400000

variable {R : Ranks} {H : Formalism.BasicNotions.Host R}

variable {Ω : Type} [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω]

end GlobalTheory.RecT

namespace GlobalTheory.RecT

open GlobalTheory.RowTie

section Read

open Formalism.MainNotions Formalism.MainNotions.N ReciprocityTheory.Aut Formalism.AUTREP _root_.Formalism.L2 GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC

end Read

end GlobalTheory.RecT

namespace GlobalTheory.RecT

open GlobalTheory.RowTie

end GlobalTheory.RecT

end
end

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.DefiniteBC GlobalTheory.RecT

namespace GlobalTheory.DefiniteBCGood

section Local

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.SmGL GlobalTheory.LocGL

variable {E : Type} [Field E] [NumberField E]

theorem good_of_isSpehQuot {a d N : ℕ} (h : ∑ _ : Fin d, a = N) {w : HeightOneSpectrum (𝓞 E)} (σ : LocIrr w a)
    (σ' : LocIrr w N) (hd : 1 ≤ d) (hq : IsSpehQuot h σ σ') (hG : Good (GlobalTheory.BCSupport.clsOf σ')) :
    Good (GlobalTheory.BCSupport.clsOf σ) := by
  obtain ⟨q, hq⟩ := hq
  let x := IrrGL.of σ.ρ σ.smooth σ.irred
  let T : ∀ i : Fin d, (GlobalTheory.SmGL.twist σ.ρ (detChar (Fin a) (absPow (w.adicCompletion E) (((d : ℂ) - 1) / 2 - (i : ℕ))))).Equiv
      (spehFactor x d i).rep := fun i =>
    (twistEquiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred) _).trans (x.twEquiv _ (isSmoothChar_absPow _))
  let M := multiProdEquiv (stdBlocks (fun _ : Fin d => a) h) T
  have hA : IsSubquotient (GlobalTheory.BCSupport.clsOf σ').rep σ'.ρ :=
    IsSubquotient.of_surjective (IrrGL.equivOf σ'.ρ σ'.smooth σ'.irred).toIntertwiningMap
      (IrrGL.equivOf σ'.ρ σ'.smooth σ'.irred).toLinearEquiv.surjective
  have hB : IsSubquotient σ'.ρ (spehInd h σ) := IsSubquotient.of_surjective q hq
  have hC : IsSubquotient (spehInd h σ) (prodIrr (spehFactor x d) h) :=
    IsSubquotient.of_surjective M.symm.toIntertwiningMap M.symm.toLinearEquiv.surjective
  have hs : IsSubquotient (GlobalTheory.BCSupport.clsOf σ').rep (prodIrr (spehFactor x d) h) := hA.trans (hB.trans hC)
  have h0 := (good_toral_of_isSubquotient_prodIrr _ d (spehFactor x d) (GlobalTheory.BCSupport.clsOf σ') h hs).1 hG ⟨0, hd⟩
  exact (good_nu_iff x _).1 h0

end Local

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}

attribute [local instance] host_isCMField

section Statements

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {A : NAut N}

def GoodSplitU {n : ℕ} (U : Submodule ℂ (UA H.E n → ℂ)) : Prop :=
  ∀ w : PlE H, IsSplitPl H w → ∀ σ : LocIrr w n,
    IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ → Good (GlobalTheory.BCSupport.clsOf σ)

end Statements

section Proof

variable {A : NAut N}

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end Proof

section Frozen

open Formalism.MainNotions

end Frozen

section LawsCore

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Formalism.ConjugateSelfDual ReciprocityTheory.Gal

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {ar : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h ar} {rc : IrrGL (k := w.adicCompletion E) → WD h}

end LawsCore

section LawsSpeh

open GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.NuShift

end LawsSpeh

section SatCore

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Formalism.ConjugateSelfDual ReciprocityTheory.Gal

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {ar : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h ar} {rc : IrrGL (k := w.adicCompletion E) → WD h}

end SatCore

section RecordLaws

open GlobalTheory.LocGL GlobalTheory.WeilDeligne Formalism.ConjugateSelfDual ReciprocityTheory.Gal

variable {A : NAut N} (T : GlobalTheory.RowTie.WDTie N A)
  {rec : ∀ w : PlE H, IrrGL (k := w.adicCompletion H.E) → WD (E := H.E) (A := N.plOm.1 w) (w := w) (N.plOm.2 w)}

open GlobalTheory.RecLaws GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Formalism.ConjugateSelfDual ReciprocityTheory.Gal

end RecordLaws

section Top

open GlobalTheory.LocGL GlobalTheory.WeilDeligne Formalism.ConjugateSelfDual ReciprocityTheory.Gal

end Top

section RecordLawsFam

open GlobalTheory.LocGL GlobalTheory.WeilDeligne Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.SmGL GlobalTheory.LocLanglands GlobalTheory.RecLaws

variable {A : NAut N} (T : GlobalTheory.RowTie.WDTie N A) {rc : GlobalTheory.RecT.RecFam}

end RecordLawsFam

end GlobalTheory.DefiniteBCGood

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InertFrames.InertB
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDegreeOnePrimeNotSplitsCompletely
open NumberField IsDedekindDomain GroundTheory.Global

namespace GlobalTheory.CompanionTheory.Density


open Filter Topology Set in
theorem exists_degreeOnePrime_not_splitsCompletely :
    ∀ (L F M : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] [Field M]
      [NumberField M] [Algebra F M] [IsGalois F M], 1 < Module.finrank F M →
      ∀ B : Set (HeightOneSpectrum (𝓞 F)), B.Finite →
        ∃ v ∈ degreeOnePrimes L F, v ∉ B ∧ ¬ SplitsCompletely M v := by
  intro L F M _ _ _ _ _ _ _ _ _ hdeg B hB
  by_contra hcon
  push Not at hcon
  have hfin : (degreeOnePrimes L F \ ({v : HeightOneSpectrum (𝓞 F) | SplitsCompletely M v} ∩ degreeOnePrimes L F)).Finite := by
    apply hB.subset
    intro v hv
    by_contra hvB
    exact hv.2 ⟨hcon v hv.1 hvB, hv.1⟩
  have hinter : ({v : HeightOneSpectrum (𝓞 F) | SplitsCompletely M v} ∩
      degreeOnePrimes L F).HasDirichletDensity 1 :=
    (GroundTheory.Global.hasDirichletDensity_iff_of_subset_of_isBoundedUnder
      Set.inter_subset_right
      (GroundTheory.Global.isBoundedUnder_primeIdealZetaSum_of_finite hfin) 1).mpr
      (GroundTheory.Global.hasDirichletDensity_degreeOnePrimes (K := L) (L := F))
  have hsplit : {v : HeightOneSpectrum (𝓞 F) | SplitsCompletely M v}.HasDirichletDensity 1 :=
    (GroundTheory.Global.hasDirichletDensity_inter_degreeOnePrimes_iff
      (K := L) _ 1).mp hinter
  have hSd := GroundTheory.Global.hasDirichletDensity_setOf_splitsCompletely (K := F) (L := M)
  have heq : (1 : ℝ) = 1 / Module.finrank F M :=
    hsplit.dirichletDensity_eq.symm.trans hSd.dirichletDensity_eq
  have h2 : 2 ≤ Module.finrank F M := hdeg
  have hfr : (2 : ℝ) ≤ Module.finrank F M := by exact_mod_cast h2
  have hq : (1 : ℝ) / Module.finrank F M ≤ 1 / 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hfr
  linarith

end GlobalTheory.CompanionTheory.Density
end

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Inert

namespace ExistsNonSplitPlace

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mem_of_not_isSplitAt {Sec : Set (Pl E)} (hS : IsSection Sec) {w : Pl E} (hw : ¬ IsSplitAt w) :
    w ∈ Sec := by
  obtain ⟨u, ⟨hu, hue⟩, -⟩ := hS w
  by_cases h : u = w
  · exact h ▸ hu
  · exact absurd ⟨u, h, hue⟩ hw

theorem exists_not_isSplitAt (B : Set (Pl E)) (hB : B.Finite) : ∃ w : Pl E, w ∉ B ∧ ¬ IsSplitAt w := by
  set F := maximalRealSubfield E
  have h2 : Module.finrank F E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two F E
  obtain ⟨v, -, hvB, hv⟩ := GlobalTheory.CompanionTheory.Density.exists_degreeOnePrime_not_splitsCompletely F F E
    (by omega) ((fun w : Pl E => w.under (𝓞 F)) '' B) (hB.image _)
  haveI := v.isMaximal
  obtain ⟨⟨P, hP⟩⟩ := v.asIdeal.nonempty_primesOver (S := 𝓞 E)
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver v.ne_bot hP
  let w : Pl E := ⟨P, hP.1, hP0⟩
  have hwv : w.under (𝓞 F) = v := HeightOneSpectrum.ext (hP.2.over).symm
  refine ⟨w, fun hw => hvB ⟨w, hw, hwv⟩, ?_⟩
  rintro ⟨u, hu, hue⟩
  apply hv
  rw [GroundTheory.Global.splitsCompletely_iff_ncard_primesOver, h2]
  haveI : NoZeroSMulDivisors (𝓞 F) (𝓞 E) := ⟨fun {c x} e => by
    rw [Algebra.smul_def, mul_eq_zero, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))] at e
    exact e⟩
  have hle : (v.asIdeal.primesOver (𝓞 E)).ncard ≤ 2 := by
    have h := Ideal.card_primesOverFinset_le_finrank (𝓞 E) F E v.ne_bot
    rw [← Set.ncard_coe_finset, IsDedekindDomain.coe_primesOverFinset v.ne_bot, h2] at h
    exact h
  have hmem : ∀ x : Pl E, x.under (𝓞 F) = v → x.asIdeal ∈ v.asIdeal.primesOver (𝓞 E) := fun x hx =>
    ⟨x.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hx).symm⟩⟩
  have hge : 2 ≤ (v.asIdeal.primesOver (𝓞 E)).ncard := by
    have hne : u.asIdeal ≠ w.asIdeal := fun e => hu (HeightOneSpectrum.ext e)
    rw [← Set.ncard_pair hne]
    refine Set.ncard_le_ncard ?_ (IsDedekindDomain.primesOver_finite _ _)
    rintro x (rfl | rfl)
    · exact hmem u (hue.trans hwv)
    · exact hmem w hwv
  omega

end ExistsNonSplitPlace

theorem inertPlaceEx : InertPlaceEx := by
  intro E _ _ _ _ n π hπ Sec hS X
  have hfin : {w : Pl E | ¬ IsUnramU π w}.Finite :=
    Filter.eventually_cofinite.1 (PositivityTheory.Rg.BcB.F.Rig.eventually_isUnramU hπ)
  obtain ⟨w, hwB, hw⟩ := ExistsNonSplitPlace.exists_not_isSplitAt ((X : Set (Pl E)) ∪ {w | ¬ IsUnramU π w})
    (X.finite_toSet.union hfin)
  refine ⟨w, ExistsNonSplitPlace.mem_of_not_isSplitAt hS hw, fun h => hwB (Or.inl h), hw, ?_⟩
  by_contra h
  exact hwB (Or.inr h)

end PositivityTheory.Rg.BcB.F.Inert

end
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
open PositivityTheory.Rg.BcN UpperTheory.BaseChangeIdentities UpperTheory.Zero.LLC GlobalTheory.PRep

namespace UpperTheory.One.M.Ud

attribute [local instance] GlobalTheory.CuspRep.host_isCMField

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def UnitaryReadS {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} (B : NBC A) (rc : RecMap A) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ R.m → ∀ π : B.AU j, ∃ U : Submodule ℂ (UA H.E R.nV → ℂ), IsAutRepU U ∧
    (∀ w : PlE H, IsSplitPl H w → ∀ σ : LocIrr w R.nV,
      IsCompAlong U (locU R.nV w) ((cLoc w).comp (locU R.nV w).subtype) σ.ρ → B.locAU j π w = rc w R.nV σ) ∧
    (∀ w : PlE H, ¬ IsSplitPl H w → B.sphAU j π w → GlobalTheory.DefiniteBCGood.GoodSplitU U ∧
      ∃ α, IsSatAt U w α ∧ B.satAU j π w = Finset.univ.val.map fun i => (α i : ℂ)) ∧
    ∀ τ : H.E →+* ℂ, ∃ lam, HasWeightAt U τ lam ∧ B.infW j (B.wtAU j π) τ = infOfWeight lam


open GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BCSupport in
theorem good_of_sph {E : Type} [Field E] [NumberField E] {c n : ℕ} {N : Fin c → ℕ} (h : ∑ i, N i = n) (w : HeightOneSpectrum (𝓞 E))
    (σ : ∀ i, SmIrr (GL (Fin (N i)) (w.adicCompletion E))) (h1 : GlobalTheory.LGrp.IsSpherical (locProd h w σ) (GlobalTheory.LFun.KGL w (n := n))) (i) :
    Good (clsOf (σ i)) := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  let e := prodIrrEquiv (k := w.adicCompletion E) h (fun i => (σ i).ρ) (fun i => (σ i).smooth) (fun i => (σ i).irred)
  have h1' : GlobalTheory.LGrp.IsSpherical (prodIrr (fun i => clsOf (σ i)) h) (GlobalTheory.LFun.KGL w (n := n)) := isSpherical_of_equiv e h1
  have h3 : GlobalTheory.SmGL.IsSpherical (prodIrr (fun i => clsOf (σ i)) h) :=
    isSphericalFor_of_eq (GlobalTheory.CohomologicalConjSelfDualTempered.UnrModel.kgl_eq_ko w n) ((GlobalTheory.LGrp.isSpherical_iff _ _).1 h1')
  exact (GlobalTheory.SphSupport.toral_and_good_of_isSpherical GlobalTheory.bernsteinZelevinskyFiniteness_holds _ _
    (GlobalTheory.LocLanglands.SphFac.isSpherical_factor _ c n _ h _ _ (IsSubquotient.refl _) h3 i)).2


end UpperTheory.One.M.Ud

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.UnitaryReadTrue
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC GlobalTheory.UnitaryReadTrue
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace UpperTheory.One.M

theorem noSplit (D : D7) (w : PlE D.host) (v) (hw : ¬ IsSplitPl D.host w) (hv : NG.OverPl w v) : NoSplit D.host.E v := by
  intro s hs
  by_cases e : s.w = w
  · exact hw (e ▸ GlobalTheory.SplitPlaceConj.isSplitPl_w D s)
  · refine not_isSplitAt D w hw ⟨s.w, e, HeightOneSpectrum.ext ?_⟩
    exact s.w_under.trans ((congrArg HeightOneSpectrum.asIdeal hs).trans hv.symm)

end UpperTheory.One.M
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.BaseChangeDefiniteOfCmDatumRecLaws
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.DefiniteBC
open PositivityTheory.Rg.BcN UpperTheory.BaseChangeIdentities UpperTheory.Zero.LLC

namespace UpperTheory.One.M.Ud

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

attribute [local instance] host_isCMField
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem part {rc : RecMap A} (hMW : DiscCsd H.E) (hS : RecSpeh rc) (hC : CuspReadG rc) {n : ℕ}
    (hn : 0 < n) {V : Submodule ℂ (Sm H.E n)} (hV : IsDiscrete V) (hc : CsdAsc V)
    (hG : ∀ w : PlE H, ∃ σ', IsLocCompGL V w σ' ∧ Good (GlobalTheory.BCSupport.clsOf σ')) :
    ∃ p : Part A.CG, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π ∧ p.a * p.d = n ∧
      (∀ w σ, IsLocCompGL V w σ → GlobalTheory.SmGL.IsUnitarisable σ.ρ ∧ rc w n σ = spehLoc N A p w) ∧
      ∀ τ m, HasInfCharGL V τ m → m = spehInf p.d (A.infG p.π τ) := by
  obtain ⟨a, d, h, P, h1, h2, h3⟩ := hMW n hn V hV hc
  have had : a * d = n := by simpa [mul_comm] using h
  have ha : 1 ≤ a := Nat.pos_of_mul_pos_right (had ▸ hn)
  have hPG : ∀ w σ, P.IsLocComp w σ → Good (GlobalTheory.BCSupport.clsOf σ) := fun w σ hσ => by
    obtain ⟨σ', hσ', hg⟩ := hG w
    obtain ⟨-, σ₀, l, -, q⟩ := h2 w σ' hσ'
    have e : GlobalTheory.BCSupport.clsOf σ = GlobalTheory.BCSupport.clsOf σ₀ :=
      GlobalTheory.LocGL.IrrGL.of_eq_of.2 (GlobalTheory.CuspRep.LocUniq.isLocComp_unique P w σ σ₀ hσ l)
    rw [e]
    exact GlobalTheory.DefiniteBCGood.good_of_isSpehQuot h σ₀ σ' (Nat.pos_of_mul_pos_left (had ▸ hn)) q hg
  obtain ⟨π, c1, c2, c3⟩ := hC a P ha h1 hPG
  refine ⟨⟨a, π, d⟩, ha, Nat.pos_of_mul_pos_left (had ▸ hn), c1, had, fun w σ' hσ' => ?_, fun τ m' hm' => ?_⟩
  · obtain ⟨u, σ, l, u', q⟩ := h2 w σ' hσ'
    refine ⟨u, ?_⟩
    rw [hS w a d n h P σ σ' l u' q, ← c2 w σ l, spehLoc_eq]
  · obtain ⟨m, hm, rfl⟩ := h3 τ m' hm'
    rw [c3 τ m hm]


attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
theorem parts {rc : RecMap A} (hNT : DefiniteN)
    (hMW : DiscCsd H.E)
    (hP : RecProd rc) (hS : RecSpeh rc) (hSat : RecSatake rc) (hC : CuspReadG rc)
    {n : ℕ} (hn : 1 ≤ n) {U : Submodule ℂ (UA H.E n → ℂ)} (hU : IsAutRepU U) (hGs : GlobalTheory.DefiniteBCGood.GoodSplitU U)
    (hSat' : ∀ w, ¬ IsSplitPl H w → ∃ α, IsSatAt U w α) :
    ∃ Pa : List (Part A.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) ∧ rankIso N A Pa = n ∧
      (∀ w, IsSplitPl H w → ∃ σ : LocIrr w n,
        IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ isoLoc N A Pa w = rc w n σ) ∧
      (∀ w α, IsSatAt U w α → A.unr (isoLoc N A Pa w) ∧
        A.frobEig (isoLoc N A Pa w) = ubc n (Finset.univ.val.map fun i => (α i : ℂ))) ∧
      ∀ τ lam, HasWeightAt U τ lam → Pa.Nodup ∧ isoInf N A Pa τ = infOfWeight lam ∧
        isoInf N A Pa (ComplexEmbedding.conjugate τ) = (infOfWeight lam).map (fun z => -z) := by
  obtain ⟨c, d, h, V, σ, m, bc⟩ := hNT H.E (host_unramified H) n hn U hU
  have hgood : ∀ i w, Good (GlobalTheory.BCSupport.clsOf (σ i w)) := fun i w => by
    by_cases hw : IsSplitPl H w
    · have hc := bc.split w (isSplitAt_of_isSplitPl hw)
      exact GlobalTheory.BCSupport.good_of_good_locProd h w (σ · w) hc.1
        (hGs w hw ⟨_, locProd h w (σ · w), GlobalTheory.SmGL.isSmooth_parInd _ _, hc.1⟩ hc) i
    · obtain ⟨α, s, ϖ, q, e1, e2, e3⟩ := hSat' w hw
      exact good_of_sph h w (σ · w) (bc.unram w (GlobalTheory.BcSpehCompare.isUnramU_of_hasSatAt e1 e2.2.1 e3)) i
  choose p p1 p2 p3 p4 p5 p6 using fun i =>
    Ud.part hMW hS hC (bc.pos i) (bc.discrete i) (bc.csd i) (fun w => ⟨σ i w, bc.loc i w, hgood i w⟩)
  let Q : ∀ w, LocIrr w n := fun w =>
    { V := _
      ρ := locProd h w (σ · w)
      smooth := GlobalTheory.SmGL.isSmooth_parInd _ _
      irred := UpperTheory.Lit.Mix.multiProd_at (@UpperTheory.Lit.Mix.twoAt_charZero _ _ _ _ _ (charZero_of_injective_algebraMap (algebraMap H.E _).injective)) _ (fun i => (σ i w).smooth) (fun i => (σ i w).irred)
        fun i => (p5 i w _ (bc.loc i w)).1 }
  have hloc : ∀ w, isoLoc N A (List.ofFn p) w = rc w n (Q w) := fun w => by
    rw [hP w c n d h (σ · w) (Q w) ⟨.refl _⟩]
    simp only [fun i => (p5 i w _ (bc.loc i w)).2]
    rw [lpSumList, ← Function.comp_def (fun q => spehLoc N A q w) p, ← List.map_ofFn, List.foldr_map]
    rfl
  have hinf : ∀ τ, isoInf N A (List.ofFn p) τ = ∑ i, m i τ := fun τ => by
    rw [isoInf_eq, List.map_ofFn, List.sum_ofFn]
    exact Finset.sum_congr rfl fun i _ => (p6 i τ _ (bc.inf i τ)).symm
  refine ⟨List.ofFn p, fun q hq => ?_, ?_, fun w hw => ⟨Q w, bc.split w (isSplitAt_of_isSplitPl hw), hloc w⟩,
    fun w α ⟨s, ϖ, q, e1, e2, e3⟩ => ?_, fun τ lam hl => ⟨List.nodup_ofFn.2 fun i j e => ?_, ?_, ?_⟩⟩
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hq
    exact ⟨p1 i, p2 i, p3 i⟩
  · rw [rankIso, List.map_ofFn, List.sum_ofFn, ← h]
    exact Finset.sum_congr rfl fun i _ => p4 i
  · rw [hloc, ← ubc_eq_map_inv]
    exact hSat w n (Q w) _ (bc.inert w s ϖ q e1 e2 α e3)
  · refine GlobalTheory.eq_of_nodup_sum_multiset_of_eq (Fin c) (m · τ) (bc.weight τ lam hl ▸ nodup_infOfWeight lam) i j
      (fun h0 => (bc.pos i).ne' ?_) ?_
    · rw [← (bc.inf i τ).1]
      exact Multiset.card_eq_zero.2 h0
    · rw [p6 i τ _ (bc.inf i τ), p6 j τ _ (bc.inf j τ), e]
  · rw [hinf, bc.weight τ lam hl]
  · rw [hinf, bc.weight _ _ (hasWeightAt_conjugate hn hl), infOfWeight_dual]

theorem bcAt (B : NBC A) (rc : RecMap A) (hNT : DefiniteN)
    (hMW : DiscCsd H.E)
    (hP : RecProd rc) (hS : RecSpeh rc) (hSat : RecSatake rc) (hC : CuspReadG rc) (hU : UnitaryReadS B rc) :
    GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeDistinctness.BaseChangeDefinite_at B := by
  intro j h1 h2 π hπ
  obtain ⟨U, u1, u2, u3, u4⟩ := hU j h1 h2 π
  obtain ⟨w₀, -, hw₀'⟩ := PositivityTheory.Rg.BcB.F.Inert.ExistsNonSplitPlace.exists_not_isSplitAt (E := H.E) ∅ Set.finite_empty
  have hw₀ : ¬ IsSplitPl H w₀ := fun h => hw₀' (isSplitAt_of_isSplitPl h)
  have hn : 1 ≤ R.nV := by
    have := R.rank_add_five_le
    simp only [Ranks.nV]
    omega
  obtain ⟨Pa, a1, a2, a3, a4, a5⟩ := Ud.parts hNT hMW hP hS hSat hC hn u1 (u3 w₀ hw₀ (hπ w₀ hw₀)).1
    fun w hw => (u3 w hw (hπ w hw)).2.imp fun _ h => h.1
  refine ⟨Pa, fun p hp => ⟨(a1 p hp).1, (a1 p hp).2.1⟩, fun p hp => (a1 p hp).2.2, ?_, a2, fun w hw => ?_,
    fun w hw => ?_, fun τ => ?_, fun τ _ => ?_⟩
  · obtain ⟨lam, hl, -⟩ := u4 H.φ₀
    exact (a5 _ lam hl).1
  · obtain ⟨σ, s1, s2⟩ := a3 w hw
    rw [s2, u2 w hw σ s1]
  · obtain ⟨α, s1, s2⟩ := (u3 w hw (hπ w hw)).2
    rw [s2]
    exact a4 w α s1
  · obtain ⟨lam, hl, e⟩ := u4 τ
    rw [e, (a5 τ lam hl).2.1]
  · obtain ⟨lam, hl, e⟩ := u4 τ
    rw [e, (a5 τ lam hl).2.2]

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions

theorem baseChangeDefinite_of_cmDatum_recLaws : ∀ (D : D7) (rc : RecMap D.naut), DefiniteN →
    DiscCsd D.host.E → RecProd rc → RecSpeh rc →
    RecSatake rc → CuspReadG rc → UnitaryReadS D.nbc rc → SphericalInertData.Conclusion1 D := by
  intro D rc hNT hMW hP hS hSat hC hU _ _ j h1 h2 _ _ π hπ
  obtain ⟨Pa, hPa⟩ := Ud.bcAt D.nbc rc hNT hMW hP hS hSat hC hU j h1 h2 π hπ
  exact ⟨Pa, GlobalTheory.DefiniteBCFrozen.isBC_of_isBaseChange hPa⟩

end UpperTheory.One.M.Ud

end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecT
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.DefiniteBC
namespace GlobalTheory.FormDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
def recT_alt {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} (T : GlobalTheory.RowTie.WDTie N A)
    (hL : _root_.UpperTheory.Zero.LLC.RecTExists) : RecMap A :=
  fun w _ σ => (T.e w).symm (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (N.plOm.2 w) (GlobalTheory.LocLanglands.cls (ParLaws.toRep σ)))
end GlobalTheory.FormDict
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnitaryReadTrue
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC GlobalTheory.UnitaryReadTrue
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace UpperTheory.One.M
theorem unitaryRead_true_alt (sw : _root_.UpperTheory.One.M.TrivialCondition) : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (A : _root_.GlobalTheory.HeightCounting.AUSideAlt D),
    _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL D T A → Ud.UnitaryReadS D.nbc (_root_.GlobalTheory.FormDict.recT_alt T hL) := by
  intro hL D T A hA j h1 h2 π
  obtain ⟨π₀, rfl⟩ := A.surj j h1 h2 π
  obtain ⟨F⟩ := GlobalTheory.T.unitaryFiniteAdeleIdentification_nonempty_presentations D.host.E D.R.nV
  obtain ⟨U, hU⟩ := GlobalTheory.T.exists_dictionary_cm_field_automorphic D.host.E D.R.nV F π₀
  refine ⟨U, hU.1, ?_, ?_, ?_⟩
  · intro w hw σ hσ
    obtain ⟨s, rfl⟩ := exists_splitPlace_w D w hw
    obtain ⟨τ, hτ, ⟨e⟩⟩ := GlobalTheory.T.localComponents_agree_splitPlace_dictionary _ _ F π₀ U hU s σ hσ
    have h := hA j h1 h2 π₀ s τ hτ
    show _ = (T.e s.w).symm _
    have hc : GlobalTheory.LocLanglands.cls τ = GlobalTheory.LocLanglands.cls (ParLaws.toRep σ) := by
      unfold GlobalTheory.LocLanglands.cls
      rw [(GlobalTheory.SmGL.IrrRep.cl_eq_iff (σ := τ) (τ := ParLaws.toRep σ)).2 ⟨e⟩]
    rw [Equiv.eq_symm_apply, h, hc]
  · intro w hw hsph
    let v := GlobalTheory.SplitConjPlace.belowE (D := D) w
    have hv : NG.OverPl w v := rfl
    have hsph0 := (A.sph j h1 h2 π₀ w v hw hv).1 hsph
    obtain ⟨s, ϖ, q, hs, hq⟩ :=
      GlobalTheory.InertPlaceConj.exists_conj_isUnramInv D.host.E w (host_unramified D.host w) (not_isSplitAt D w hw)
    obtain ⟨-, hI⟩ := _root_.UpperTheory.One.M.Sph.satAgree _ _ F π₀ U hU v w hv
    obtain ⟨⟨Dv, hDs, hDϖ⟩, hI2⟩ := hI s ϖ q hs hq
    obtain ⟨α, hα, hsat⟩ := A.sat j h1 h2 π₀ v w hv Dv (_root_.UpperTheory.One.M.Sph.exists_satAt_of_dict _ _ F π₀ U hU v w hv hsph0 Dv)
    obtain ⟨α', hα', hS⟩ := hI2 Dv α hDs hDϖ hα
    refine ⟨fun w' hw' σ hσ => ?_, α', ⟨s, ϖ, q, hs, hq, hS⟩, ?_⟩
    · obtain ⟨t, rfl⟩ := exists_splitPlace_w D w' hw'
      obtain ⟨τ, hτ, ⟨e⟩⟩ := GlobalTheory.T.localComponents_agree_splitPlace_dictionary _ _ F π₀ U hU t σ hσ
      have hc : GlobalTheory.LocLanglands.cls τ = GlobalTheory.LocLanglands.cls (ParLaws.toRep σ) := by
        unfold GlobalTheory.LocLanglands.cls
        rw [(GlobalTheory.SmGL.IrrRep.cl_eq_iff (σ := τ) (τ := ParLaws.toRep σ)).2 ⟨e⟩]
      have := _root_.UpperTheory.One.M.New.sphGood sw hsph0 (noSplit D w v hw hv) t τ hτ
      rwa [hc] at this
    · rw [hsat]
      congr 1
      funext i
      exact (hα' i).symm
  · intro τ
    obtain ⟨b, hb, -⟩ := GlobalTheory.algWt_contragredient _ _ π₀.toAlgWt
    obtain ⟨lam, hl, hhw⟩ := GlobalTheory.T.algebraicWeight_agrees_under_modularForm_dictionary _ _ F π₀ U hU b hb τ
    refine ⟨lam, hl, ?_⟩
    rw [A.wt j h1 h2 π₀ b hb, A.infW j h1 h2 b τ lam.w hhw, infOf_eq_infOfWeight]
theorem cusp_read_rec_t : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut),
    _root_.GlobalTheory.HeightCounting.CGTrueT hL D T → CuspReadG (_root_.GlobalTheory.FormDict.recT_alt T hL) := by
  intro hL D T C a P ha hP hg
  haveI := host_isCMField D.host
  have hu : (CG.mk P).IsUnitary := CsdUnitary.isUnitary_of_isCsd _ a (CG.mk P) hP
  obtain ⟨π, hπ⟩ := _root_.UpperTheory.One.M.New.cgSurj C a ha ⟨CG.mk P, hu⟩ fun w => by
    obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL D.host.E a P w
    exact (ParLawsT.cls_loc_eq_of_isLocComp hσ).symm ▸ hg w σ hσ
  refine ⟨π, (C.csd a _).2 (by rw [hπ]; exact hP), fun w σ hσ => ?_, fun τ m hm => ?_⟩
  · apply (T.e w).injective
    rw [C.loc, hπ]
    simp only [_root_.GlobalTheory.FormDict.recT_alt, Equiv.apply_symm_apply]
    exact _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL hσ _
  · rw [C.inf, hπ]
    exact CG.HasInfChar.infChar_eq (π := CG.mk P) hm
end UpperTheory.One.M
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BciNarrowAux
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnitaryOfLocalLanglands
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_of_local_langlands' : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (A : _root_.GlobalTheory.HeightCounting.AUSideAlt D), _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL D T A → _root_.UpperTheory.One.M.Ud.UnitaryReadS D.nbc (_root_.GlobalTheory.FormDict.recT_alt T hL) := by
  first | exact @_root_.UpperTheory.One.M.unitaryRead_true_alt trivial | exact (_root_.UpperTheory.One.M.unitaryRead_true_alt trivial) | (intros; apply (_root_.UpperTheory.One.M.unitaryRead_true_alt trivial) <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalOfLocalLanglands
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspReadG_recT_of_cgTrue : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), _root_.GlobalTheory.HeightCounting.CGTrueT hL D T → _root_.GlobalTheory.DefiniteBC.CuspReadG (_root_.GlobalTheory.FormDict.recT_alt T hL) := by
  first | exact @_root_.UpperTheory.One.M.cusp_read_rec_t | exact _root_.UpperTheory.One.M.cusp_read_rec_t | (intros; apply _root_.UpperTheory.One.M.cusp_read_rec_t <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecSatakeRecT
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MTwinB
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
namespace UpperTheory.One.M
section Core
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {rc : IrrGL (k := w.adicCompletion E) → WD h}
theorem locProd_eqG_alt (H : _root_.UpperTheory.Zero.LLC.IsRecT h rc) : ∀ {c n : ℕ} {d : Fin c → ℕ} (hd : ∑ i, d i = n)
    (σ : ∀ i, SmIrr (GL (Fin (d i)) (w.adicCompletion E))) (σ' : SmIrr (GL (Fin n) (w.adicCompletion E))),
    Nonempty (σ'.ρ.Equiv (GlobalTheory.UnitaryBC.locProd hd w σ)) →
      rc (cls (ParLaws.toRep σ')) = sumList (List.ofFn fun i => rc (cls (ParLaws.toRep (σ i)))) := by
  obtain ⟨a, ha, ε, L⟩ := UpperTheory.One.M.opn rc H
  intro c
  induction c with
  | zero =>
    intro n d hd σ σ' e
    obtain rfl : n = 0 := by simpa using hd.symm
    obtain ⟨e⟩ := e
    obtain ⟨φ⟩ := GlobalTheory.LocGL.SupportRing.nonempty_equiv_unit (k := w.adicCompletion E) (stdBlocks d hd) fun i => (σ i).ρ
    have h1 := L.det 0 1 isSmoothChar_one
    simp only [List.range_zero, List.map_nil] at h1
    rw [List.ofFn_zero]
    refine (congrArg rc (congrArg (Sigma.mk 0) (IrrRep.cl_eq_iff.2 ⟨e.trans φ⟩))).trans ?_
    exact h1
  | succ s ih =>
    intro n d hd σ σ' e
    obtain rfl : n = d 0 + ∑ i : Fin s, d i.succ := hd.symm.trans (Fin.sum_univ_succ d)
    obtain ⟨e⟩ := e
    obtain ⟨E₁⟩ := MultiIrr.nonempty_prod₂_equiv_multiProd_succ (k := w.adicCompletion E) d hd fun i => (σ i).ρ
    have hs : IsSmooth (multiProd (stdBlocks (fun i : Fin s => d i.succ) rfl) fun i : Fin s => (σ i.succ).ρ) :=
      isSmooth_parInd _ _
    have hi := GlobalTheory.T.isIrreducible_second_factor_of_irreducible_product _ _ _ _ _ _ (σ 0).ρ _ σ'.ρ (σ 0).smooth (σ 0).irred hs σ'.irred ⟨e.trans E₁.symm⟩
    let σ'' : SmIrr (GL (Fin (∑ i : Fin s, d i.succ)) (w.adicCompletion E)) := ⟨_, _, hs, hi⟩
    have h1 := L.prod (d 0) _ (ParLaws.toRep (σ 0)) (ParLaws.toRep σ'') (ParLaws.toRep σ') ⟨e.trans E₁.symm⟩
    have h2 := ih (d := fun i : Fin s => d i.succ) rfl (fun i => σ i.succ) σ'' ⟨.refl _⟩
    rw [List.ofFn_succ]
    exact h1.trans (congrArg _ h2)
end Core
end UpperTheory.One.M
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecSatakeRecT
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
namespace GlobalTheory.FormDict.RecTLaws
section Core
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {rc : IrrGL (k := w.adicCompletion E) → WD h}
theorem hasSatGL_rec_alt (H : _root_.UpperTheory.Zero.LLC.IsRecT h rc) {n : ℕ} (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (S : Multiset ℂˣ)
    (hS : GlobalTheory.LFun.HasSatGL w σ.ρ S) :
    (rc (cls (ParLaws.toRep σ))).unr ∧
      (rc (cls (ParLaws.toRep σ))).frobEig = S.map fun z => ((z⁻¹ : ℂˣ) : ℂ) := by
  have hsph : IsSpherical (ParLaws.toRep σ).ρ := by
    have := hS.1
    unfold IsSpherical IsSphericalFor
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
    exact this
  have hu : (rc (cls (ParLaws.toRep σ))).unr := (_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_unramified_iff_spherical H _).2 hsph
  obtain ⟨α, hα⟩ := _root_.UpperTheory.One.M.exists_hasSatake_of_unr_alt H hu
  have e : S = Finset.univ.val.map α := hS.unique (GlobalTheory.T.hasSatakeGL_of_hasSatakeParameters_principalSeries E w n _ σ.ρ α hα)
  refine ⟨hu, ?_⟩
  rw [_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_eq_diagonal_inv_of_has_satake H hα, WD.frobEig_diag, e, Multiset.map_map]
  rfl
end Core
section Record
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
  (T : GlobalTheory.RowTie.WDTie N A) (hL : _root_.UpperTheory.Zero.LLC.RecTExists)
theorem equiv_transported_reciprocity_eq_local_reciprocity (w : PlE H) {n : ℕ} (σ : LocIrr w n) :
    T.e w (_root_.GlobalTheory.FormDict.recT_alt T hL w n σ) = _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (N.plOm.2 w) (cls (ParLaws.toRep σ)) :=
  (T.e w).apply_symm_apply _
theorem transported_reciprocity_prod : RecProd (_root_.GlobalTheory.FormDict.recT_alt T hL) := by
  intro w c n d hd σ σ' e
  apply (T.e w).injective
  rw [_root_.GlobalTheory.FormDict.RecTLaws.equiv_transported_reciprocity_eq_local_reciprocity, e_lpSumList, _root_.UpperTheory.One.M.locProd_eqG_alt (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (N.plOm.2 w)) hd σ σ' e, List.map_ofFn]
  congr 2
  funext i
  exact (_root_.GlobalTheory.FormDict.RecTLaws.equiv_transported_reciprocity_eq_local_reciprocity T hL w (σ i)).symm
theorem transported_reciprocity_satake : RecSatake (_root_.GlobalTheory.FormDict.recT_alt T hL) := by
  intro w n σ S hS
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.FormDict.RecTLaws.hasSatGL_rec_alt (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (N.plOm.2 w)) σ S hS
  have hu : A.unr (_root_.GlobalTheory.FormDict.recT_alt T hL w n σ) := (T.unr w _).2 (by rw [_root_.GlobalTheory.FormDict.RecTLaws.equiv_transported_reciprocity_eq_local_reciprocity]; exact h1)
  exact ⟨hu, (T.frobEig w _ hu).trans (by rw [_root_.GlobalTheory.FormDict.RecTLaws.equiv_transported_reciprocity_eq_local_reciprocity]; exact h2)⟩
theorem transported_reciprocity_speh_of_generic_unitary_dual (hTZ : GlobalTheory.Published.GenericUnitaryDualGL) (hSC : GlobalTheory.Published.StandardCosocleGL) :
    RecSpeh (_root_.GlobalTheory.FormDict.recT_alt T hL) := by
  intro w a d n hd P σ σ' hP hu hq
  have hg : IsGeneric σ.ρ := GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp H.E a P w σ hP
  apply (T.e w).injective
  rw [_root_.GlobalTheory.FormDict.RecTLaws.equiv_transported_reciprocity_eq_local_reciprocity, e_lpSumList, _root_.GlobalTheory.T.local_langlands_speh_product' _ _ _ w _ _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (N.plOm.2 w)) hTZ hSC a d n hd σ σ'
    hu hg hq, List.map_map]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp_apply, T.tw, _root_.GlobalTheory.FormDict.RecTLaws.equiv_transported_reciprocity_eq_local_reciprocity]
end Record
theorem transported_reciprocity_prod_and_speh_and_satake : GlobalTheory.Published.GenericUnitaryDualGL → GlobalTheory.Published.StandardCosocleGL →
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
      (A : NAut N) (T : GlobalTheory.RowTie.WDTie N A), RecProd (_root_.GlobalTheory.FormDict.recT_alt T hL) ∧ RecSpeh (_root_.GlobalTheory.FormDict.recT_alt T hL) ∧ RecSatake (_root_.GlobalTheory.FormDict.recT_alt T hL) :=
  fun hTZ hSC hL _ _ _ _ _ T => ⟨_root_.GlobalTheory.FormDict.RecTLaws.transported_reciprocity_prod T hL, _root_.GlobalTheory.FormDict.RecTLaws.transported_reciprocity_speh_of_generic_unitary_dual T hL hTZ hSC, _root_.GlobalTheory.FormDict.RecTLaws.transported_reciprocity_satake T hL⟩
end GlobalTheory.FormDict.RecTLaws
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecSatakeRecTStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.recProd_recSpeh_recSatake : GlobalTheory.Published.GenericUnitaryDualGL → GlobalTheory.Published.StandardCosocleGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (T : GlobalTheory.RowTie.WDTie N A), RecProd (_root_.GlobalTheory.FormDict.recT_alt T hL) ∧ RecSpeh (_root_.GlobalTheory.FormDict.recT_alt T hL) ∧ RecSatake (_root_.GlobalTheory.FormDict.recT_alt T hL) := by
  first | exact @_root_.GlobalTheory.FormDict.RecTLaws.transported_reciprocity_prod_and_speh_and_satake | exact _root_.GlobalTheory.FormDict.RecTLaws.transported_reciprocity_prod_and_speh_and_satake | (intros; apply _root_.GlobalTheory.FormDict.RecTLaws.transported_reciprocity_prod_and_speh_and_satake <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
section Ud
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
open PositivityTheory.Rg.BcN
namespace UpperTheory.BaseChangeIdentities
attribute [local instance] GlobalTheory.CuspRep.host_isCMField
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
end UpperTheory.BaseChangeIdentities
end Ud
section Pr
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.DefiniteBC
open PositivityTheory.Rg.BcN
namespace UpperTheory.BaseChangeIdentities
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
attribute [local instance] host_isCMField
section Frozen
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions
end Frozen
section Closing
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField
  IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem aux_of_cgTrue_of_auTrue (hA : AscComp) : DefiniteN → GlobalTheory.Published.GenericUnitaryDualGL → GlobalTheory.Published.StandardCosocleGL →
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (A : _root_.GlobalTheory.HeightCounting.AUSideAlt D),
      _root_.GlobalTheory.HeightCounting.CGTrueT hL D T → _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL D T A → SphericalInertData.Conclusion1 D := by
  intro hNT hGU hSC hL D T A hCG hAU
  obtain ⟨hP, hS, hSat⟩ := _root_.GlobalTheory.T.recProd_recSpeh_recSatake hGU hSC hL D.nd D.naut T
  exact _root_.UpperTheory.One.M.Ud.baseChangeDefinite_of_cmDatum_recLaws D (_root_.GlobalTheory.FormDict.recT_alt T hL) hNT
    (discCsd_of hA D.host.E) hP hS hSat
    (_root_.GlobalTheory.T.cuspReadG_recT_of_cgTrue hL D T hCG) (_root_.GlobalTheory.T.unitary_of_local_langlands' hL D T A hAU)
end Closing
end UpperTheory.BaseChangeIdentities
end Pr
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.BaseChangeIdentities
theorem Conclusion1_alt_alt_alt : DefiniteN → GlobalTheory.Published.BernsteinUnitaryProductIrreducible →
    GlobalTheory.Published.GenericUnitaryDualGL → GlobalTheory.Published.StandardCosocleGL →
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (A : _root_.GlobalTheory.HeightCounting.AUSideAlt D),
      _root_.GlobalTheory.HeightCounting.CGTrueT hL D T → _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL D T A → SphericalInertData.Conclusion1 D :=
  fun h _ => _root_.UpperTheory.BaseChangeIdentities.aux_of_cgTrue_of_auTrue ascComp h
end UpperTheory.BaseChangeIdentities
end
end
end
