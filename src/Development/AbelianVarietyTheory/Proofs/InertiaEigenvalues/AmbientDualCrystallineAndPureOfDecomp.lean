module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSummandAndDualFromInverseCharacterTwi
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalObjectsEveryFamilyWild
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepERankOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientDualCrystallineAndPureOfDecomp
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientDualCrystallineAndPureOfDecomp
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Formalism.MainNotions.TruncatedSeriesCountingIdentities (Decl CoefExt locC chi1C)

namespace GlobalTheory.AmbWT

variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : CoefExt D i w hw)

def coef : D.nd.O i →+* ↥C.LL.1 := C.inc.comp (D.nbr i w hw).toLL

def grp (hw : w ∈ placesOver D.host.E (D.nd.l i)) : Br.G D.nbr i w hw →* GE D.nd :=
  (decS D.nd w).comp (Br.iota D.nbr i w hw)

theorem locC_apply {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) :
    locC C M g = (M (grp hw g)).map (coef C) := rfl

theorem localizedCoefficientChar_apply (g : Br.G D.nbr i w hw) :
    chi1C C g = Units.map (coef C : D.nd.O i →* ↥C.LL.1) (chiU D.nd i 1 (grp hw g)) := rfl

theorem locC_rTwO (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) :
    locC C (rTwO D.nd i r x) = twistM (locC C (rO D.nd i r x)) (chi1C C)⁻¹ := by
  refine MonoidHom.ext fun g => Matrix.ext fun a b => ?_
  rw [locC_apply]
  show coef C ((((chiU D.nd i 1)⁻¹ (grp hw g) : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (grp hw g) a b) =
    ((((chi1C C)⁻¹ g) : (↥C.LL.1)ˣ) : ↥C.LL.1) * (locC C (rO D.nd i r x) g) a b
  rw [map_mul, locC_apply, MonoidHom.inv_apply, MonoidHom.inv_apply, localizedCoefficientChar_apply]
  rfl


open Classical in
theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), TruncatedSeriesCountingIdentities.admG2 (D := D) i r ρ π → TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → EmbeddingTypes.ambW (D := D) i ρ π dc ∧ EmbeddingTypes.ambT2 (D := D) i ρ π dc := by
  intro D i r ρ π dc hG hd
  have hd' : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e := by
    obtain ⟨e, he⟩ := hd
    refine ⟨e, fun g u => ?_⟩
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.overK, GlobalTheory.SummandJumps.matRep_apply]
    exact he g u
  have hc : ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : CoefExt D i w hw),
      IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (locC C (WpO D.nd i ρ π))) ∧
        IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (locC C (T2O D.nd i ρ π))) := by
    intro w hw C
    have h1 := (hG w hw C).2 π
    rw [← locC_rTwO] at h1
    exact (GlobalTheory.SummandJumps.main D i w hw (D.locT _) C.LL C.le r ρ π hd').1 h1
  refine ⟨fun _ w hw _ C => (hc w hw C).1, fun _ w hw _ C => ⟨(hc w hw C).2, ?_, ?_⟩⟩
  · exact (GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT _) (D.nbr i w hw).Kw C.LL _ _ (hc w hw C).2).1
  · exact (hG w hw C).1.2.2.2.2.2.2

end GlobalTheory.AmbWT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientDualCrystallineAndPureOfDecompStatement
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ambientDual_crystalline_and_pure_of_decomp : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), TruncatedSeriesCountingIdentities.admG2 (D := D) i r ρ π → TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π → EmbeddingTypes.ambW (D := D) i ρ π dc ∧ EmbeddingTypes.ambT2 (D := D) i ρ π dc := by
  first | exact @GlobalTheory.AmbWT.main | exact GlobalTheory.AmbWT.main | (intros; apply GlobalTheory.AmbWT.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleAtGoodPointsOfCoefRingTakenAtLive
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleAtGoodPointsOfCoefRingTakenAtLive
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem GlobalTheory.AdmissibleCore.main : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (X : KillingConditions.HubData D), GlobalTheory.CoefDuty.TakenAll D → GlobalTheory.PtCore.ResAbsIrr D → GlobalTheory.PtCore.PtFam D X.r X.ρ → ∀ i : D.nd.Loc, ∀ π ∈ D.nd.Zgood i, LargeLevelLemmas.adm51 (D := D) i (X.r i) (X.ρ i) π := by
  intro hC D X hT hA hX i π hπ
  intro hZ
  obtain ⟨e, he⟩ := (hX.compl i π hZ).rho
  have hdec : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (X.r i π) (X.ρ i π) (D.nd.chi i) e := ⟨e, fun g u => he g u⟩
  have hHG : IsHeckeGalois D.nd i π (X.r i π) := hX.good i π
  have hpt : GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.IsRhoPt D i π (X.ρ i π) := ⟨hX.cont i π, X.r i π, hHG, e, fun g u => he g u⟩
  have hirr := hA i π hπ (X.ρ i π) hpt
  have hLive : GlobalTheory.CoefDuty.Live D.nd i := ⟨π, hZ, X.r i π, X.ρ i π, hHG, hdec, hirr⟩
  obtain ⟨r₀, ρ₀, hg₀, hw₀⟩ := hT i hLive
  obtain ⟨S, hS, -⟩ := GlobalTheory.T.exists_globalObjects_every_family_wild hC D.nd i r₀ ρ₀ hg₀ hw₀ (X.r i) (X.ρ i) (hX.good i) π hZ hdec
  exact ⟨S, hS⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleAtGoodPointsOfCoefRingTakenAtLiveStatement
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissibleAtGoodPoints_of_coefRing_taken_at_live : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (X : KillingConditions.HubData D), GlobalTheory.CoefDuty.TakenAll D → GlobalTheory.PtCore.ResAbsIrr D → GlobalTheory.PtCore.PtFam D X.r X.ρ → ∀ i : D.nd.Loc, ∀ π ∈ D.nd.Zgood i, LargeLevelLemmas.adm51 (D := D) i (X.r i) (X.ρ i) π := by
  first | exact @GlobalTheory.AdmissibleCore.main | exact GlobalTheory.AdmissibleCore.main | (intros; apply GlobalTheory.AdmissibleCore.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowFiveOneOfCoefRingTakenAtLiveLocalisations
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowFiveOneOfCoefRingTakenAtLiveLocalisations
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.DesignFromSize

theorem main : GlobalTheory.TwSys.Cheb → ∀ D : D7, TakenAll D → Formalism.MainNotions.N.K.Rows.AllDesignConditions D := by
  intro hC D hT i _ _ r ρ π dc lenRow e' cB hr hA hπ
  obtain ⟨_, _, hG3, _, _, _, _, _, _, _, _, _, _, hDec, _⟩ := hA
  have hdec : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e := hDec
  have hpos : 0 < D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have habs : AbsIrrSub (mapRep (IsLocalRing.residue (D.nd.O i)) (ρ π)) ⊤ :=
    GlobalTheory.Proof.AbsoluteIrreducibilitySpan.absIrr_of_span hpos _ _ (fun _ => 1) (fun g => by rw [one_smul]; rfl) hG3.2.2
  have hlive : Live D.nd i := ⟨π, hπ, r π, ρ π, hr π, hdec, habs⟩
  obtain ⟨r₀, ρ₀, hr₀, hw⟩ := hT i hlive
  obtain ⟨S, hS, _⟩ := GlobalTheory.T.exists_globalObjects_every_family_wild hC D.nd i r₀ ρ₀ hr₀ hw r ρ hr π hπ hdec
  exact ⟨S, hS⟩

end GlobalTheory.DesignFromSize
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowFiveOneOfCoefRingTakenAtLiveLocalisationsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.designConditionAll_of_cheb_of_takenAll : GlobalTheory.TwSys.Cheb → ∀ D : D7, TakenAll D → Formalism.MainNotions.N.K.Rows.AllDesignConditions D := by
  first | exact @GlobalTheory.DesignFromSize.main | exact GlobalTheory.DesignFromSize.main | (intros; apply GlobalTheory.DesignFromSize.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowFiveOneTypePrimeOfCoefRingTakenAtLive
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowFiveOneTypePrimeOfCoefRingTakenAtLive
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.OrthogonalDesignFromSize

theorem main : GlobalTheory.TwSys.Cheb → ∀ D : D7, AutomorphicSideWildInertia.ResidualIrreducibleGood D → TakenAll D → TypePrimeCongruences.TypePrimeWildIdempotentChoice D := by
  intro hC D hN9 hT i k hk hHG r ρ hr π hπ hd _
  have hdec : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e := hd
  have hcont : Continuous (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) :=
    GlobalTheory.BlockJumpsCompare.continuous_rho D.nd i r ρ π (hr π) hd
  have hrb : IsRhoBar D.nd i (redRep D.nd i (ρ π)) := by
    refine ⟨isOpen_ker_redRep D i (ρ π) hcont, ?_⟩
    intro x w hw B σ hB hσ
    have e2 := congrArg (Polynomial.map (IsLocalRing.residue (D.nd.O i)))
      (charpoly_of_decomp D i r ρ π hd σ)
    rw [Polynomial.map_mul, Polynomial.map_prod, ← Matrix.charpoly_map, ← Matrix.charpoly_map] at e2
    rw [heckePol_res D i x π w, ← (hr π).2.2 w hw B σ hB hσ, ← Matrix.charpoly_map]
    refine (e2.trans ?_).symm
    congr 1
    refine Finset.prod_congr rfl fun c _ => ?_
    simp
  have hirr := (hN9 i hHG _ hrb).1
  have hpos : 0 < D.R.r := by
    have := D.R.two_le_m
    unfold Ranks.r
    omega
  have habs : AbsIrrSub (mapRep (IsLocalRing.residue (D.nd.O i)) (ρ π)) ⊤ :=
    GlobalTheory.ResAbsIrrGood.absIrrSub_top_of_irred (D.naut.kFbar i) hpos _
      fun W hW => hirr W fun g _ x hx => hW g x hx
  have hlive : Live D.nd i := ⟨π, hπ, r π, ρ π, hr π, hdec, habs⟩
  obtain ⟨r₀, ρ₀, hr₀, hw⟩ := hT i hlive
  obtain ⟨S, hS, hg⟩ := GlobalTheory.T.exists_globalObjects_every_family_wild hC D.nd i r₀ ρ₀ hr₀ hw r ρ hr π hπ hdec
  exact ⟨S, hS, hg.2 ⟨k, hk⟩⟩

end GlobalTheory.OrthogonalDesignFromSize
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowFiveOneTypePrimeOfCoefRingTakenAtLiveStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowFiveOneTypePrime_of_coefRingTakenAtLive : GlobalTheory.TwSys.Cheb → ∀ D : D7, AutomorphicSideWildInertia.ResidualIrreducibleGood D → TakenAll D → TypePrimeCongruences.TypePrimeWildIdempotentChoice D := by
  first | exact @GlobalTheory.OrthogonalDesignFromSize.main | exact GlobalTheory.OrthogonalDesignFromSize.main | (intros; apply GlobalTheory.OrthogonalDesignFromSize.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineAndJumps
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.TateDualCrys

open GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation GlobalTheory.RegularRing

section Local

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem fracInv_of_tied (T : LocTied l P AI) (K : FinExt l) : FracInv (P.PD K) := by
  intro x y hx h
  refine GlobalTheory.Per.FracInv.tied_frac_invariant l P AI T K y x hx fun g hg => ?_
  have h1 := h ⟨g, hg⟩
  rw [P.PD_actB, P.PD_actB] at h1
  rw [mul_comm, h1, mul_comm]

theorem lineUnit_of_tied (T : LocTied l P AI) (K : FinExt l) : LineUnit (P.PD K) := by
  intro b hb h
  refine (GlobalTheory.T.periodRings_regular_phi_surjective_fil l P AI T).1 K b hb fun g hg => ?_
  obtain ⟨x, hx⟩ := h ⟨g, hg⟩
  exact ⟨x, by rw [← P.PD_actB K ⟨g, hg⟩, hx, Algebra.smul_def]⟩

theorem matRep_apply {L Γ : Type} [CommRing L] [Group Γ] {k : ℕ} (M : Γ →* Matrix (Fin k) (Fin k) L)
    (g : Γ) (x : Fin k → L) : matRep M g x = (M g).mulVec x := rfl

theorem dot_dual {L Γ : Type} [CommRing L] [Group Γ] {k : ℕ} (M : Γ →* Matrix (Fin k) (Fin k) L)
    (g : Γ) (x y : Fin k → L) : (M g).mulVec x ⬝ᵥ (M g⁻¹).transpose.mulVec y = x ⬝ᵥ y := by
  rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec, dotProduct_comm]

theorem tateDual (T : LocTied l P AI) (K LL : FinExt l)
    (hs : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1) {k : ℕ}
    (M M' : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)
    (hM : ∀ g, M' g = ((cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1) • (M g⁻¹).transpose)
    (hc : IsCrys (P.PD K) (matRep M)) :
    IsCrys (P.PD K) (matRep M') ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ),
      multV (P.PD K) (matRep M') τ a = multV (P.PD K) (matRep M) τ (-a - 1) := by
  have := LL.2
  have : IsDomain P.R.B := isDomain_of_tied T K
  have hf := fracInv_of_tied T K
  have hu := lineUnit_of_tied T K
  constructor
  · have h1 : IsCrys (P.PD K) (matRep (dualM M)) := by
      refine subCrys (P.PD K) ↥LL.1 hf _ _ _ _ (dotProductEquiv ↥LL.1 (Fin k)).toLinearMap ?_
        (dotProductEquiv ↥LL.1 (Fin k)).injective (dualCrys (P.PD K) ↥LL.1 hf hu _ _ hc)
      intro g x
      refine LinearMap.ext fun y => ?_
      change (M g⁻¹).transpose.mulVec x ⬝ᵥ y = x ⬝ᵥ (M g⁻¹).mulVec y
      rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]
    refine GlobalTheory.TwistCrys.isCrys_twist (P.PD K) (tensorCrys (P.PD K) ↥LL.1 hf hu)
      (quotCrys (P.PD K) ↥LL.1 hf hu) (matRep (dualM M)) (matRep M')
      (WeaklyAdmissibleFiltrations.charRep (cycLL (P.PD K) ↥LL.1 ^ (1 : ℤ))) (fun g => ((cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1))
      LinearMap.id 1 rfl (fun g x => ?_) (fun g x => ?_)
      (GlobalTheory.CycPow.cyc_zpow_crys_dR_jump l P AI T K LL 1).1 h1
    · rw [zpow_one]; rfl
    · rw [matRep_apply, hM, Matrix.smul_mulVec]; rfl
  · intro τ a
    have h := (GlobalTheory.DRDual.twisted_dual_deRham l P AI T K LL _ (matRep M) _ (matRep M')
      (dotProductEquiv ↥LL.1 (Fin k)).toLinearMap 1 (dotProductEquiv ↥LL.1 (Fin k)).bijective
      (fun g x y => by
        change (M g).mulVec x ⬝ᵥ (M' g).mulVec y = _ * (x ⬝ᵥ y)
        rw [hM, Matrix.smul_mulVec, dotProduct_smul, dot_dual, zpow_one, smul_eq_mul])
      (GlobalTheory.T.isDeRham_of_isCrystalline_span l P AI T K LL _ _ hc).1).2 τ (-a - 1) hs
    rwa [show -(-a - 1) - 1 = a by ring] at h

def sumRep {L Γ : Type} [CommRing L] [Group Γ] {m k : ℕ} (M : Fin m → (Γ →* Matrix (Fin k) (Fin k) L)) :
    Representation L Γ (Fin m → Fin k → L) where
  toFun g := LinearMap.pi fun a => matRep (M a) g ∘ₗ LinearMap.proj a
  map_one' := by
    refine LinearMap.ext fun v => funext fun a => ?_
    simp
  map_mul' g h := by
    refine LinearMap.ext fun v => funext fun a => ?_
    simp

theorem isCrys_of_isSubOfSums (T : LocTied l P AI) (K LL : FinExt l) {ι : Type} {k : ℕ}
    (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)) (hc : ∀ x, IsCrys (P.PD K) (matRep (Ms x)))
    (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V)
    (h : IsSubOfSums ρ (fun x g => Ms x g)) : IsCrys (P.PD K) ρ := by
  have := LL.2
  have : IsDomain P.R.B := isDomain_of_tied T K
  have hf := fracInv_of_tied T K
  have hu := lineUnit_of_tied T K
  obtain ⟨m, xs, j, hj, he⟩ := h
  refine subCrys (P.PD K) ↥LL.1 hf _ (sumRep fun a => Ms (xs a)) _ ρ j (fun g v => he g v) hj ?_
  rw [isCrys_iff_span (P.PD K) hf hu]
  refine eq_top_of_tmul _ fun b v => ?_
  rw [← Finset.univ_sum_single v, TensorProduct.tmul_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  refine tmul_mem_span (P.PD K) (ρ := matRep (Ms (xs a)))
    (f := LinearMap.single ↥LL.1 (fun _ : Fin m => Fin k → ↥LL.1) a) (fun g x => ?_)
    ((isCrys_iff_span (P.PD K) hf hu _).1 (hc _)) b (v a)
  funext a'
  change Pi.single (M := fun _ => Fin k → ↥LL.1) a (matRep (Ms (xs a)) g x) a' =
    matRep (Ms (xs a')) g (Pi.single (M := fun _ => Fin k → ↥LL.1) a x a')
  by_cases ha : a' = a
  · subst ha; simp
  · simp [ha]

end Local

theorem loc_rDuO (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (LL' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).LL.1 ≤ LL'.1)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) (g : Br.G D.nbr i w hw) :
    mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rDuO D.nd i r x)) g =
      ((cycLL (Br.PD D.loc D.nbr i w hw) ↥LL'.1 g : (↥LL'.1)ˣ) : ↥LL'.1) •
        (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r x)) g⁻¹).transpose := by
  have h1 : ((cycLL (Br.PD D.loc D.nbr i w hw) ↥LL'.1 g : (↥LL'.1)ˣ) : ↥LL'.1) =
      IntermediateField.inclusion h
        ((Br.locChi D.nbr i w hw (epsU D.nd i) g : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) := by
    rw [GlobalTheory.CycBridge.locChi_epsU]
    exact ((IntermediateField.inclusion h).commutes _).symm
  rw [h1]
  let F : D.nd.O i →+* ↥LL'.1 := (IntermediateField.inclusion h).toRingHom.comp
    ((algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw))).comp (D.nbr i w hw).eO.toRingHom)
  let γ : Br.G D.nbr i w hw →* GE D.nd := (decS D.nd w).comp (Br.ι (D.nbr i w hw))
  ext a b
  congr 1
  change F (((chiU D.nd i 1 (γ g) * epsU D.nd i (γ g) : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (γ g)⁻¹ b a) =
    F ((epsU D.nd i (γ g) : (D.nd.O i)ˣ) : D.nd.O i) *
      F ((((chiU D.nd i 1 (γ g⁻¹))⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (γ g⁻¹) b a)
  rw [map_inv γ, map_inv (chiU D.nd i 1), inv_inv, ← map_mul, Units.val_mul]
  congr 1
  ring

theorem crystalline_and_jumps : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), LocTied (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) → ∀ (LL' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).LL.1 ≤ LL'.1) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), (∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r x))))) → (∀ (V : Type) [AddCommGroup V] [Module ↥LL'.1 V] [Module ℚ_[D.nd.l i] V] [IsScalarTower ℚ_[D.nd.l i] ↥LL'.1 V] [FiniteDimensional ↥LL'.1 V] (ρ₁ : Representation ↥LL'.1 (Br.G D.nbr i w hw) V), IsSubOfSums ρ₁ (fun x g => mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rDuO D.nd i r x)) g) → IsCrys (Br.PD D.loc D.nbr i w hw) ρ₁ ∧ ∀ (τ' : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) (a : ℤ), IsJumpV (Br.PD D.loc D.nbr i w hw) ρ₁ τ' a → ∃ x, IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r x)))) τ' (-a - 1)) ∧ ∀ π, (∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e) → (∀ (τ' : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) (a : ℤ), multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r π)))) τ' a ≤ 1) → IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (T2O D.nd i ρ π)))) ∧ ∀ (τ' : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) (a : ℤ), ((IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r π)))) τ' (-a - 1) ∧ ¬ (0 ≤ -a - 1 ∧ -a - 1 < (D.R.t : ℤ))) → multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (T2O D.nd i ρ π)))) τ' a = 1) ∧ (¬ (IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r π)))) τ' (-a - 1) ∧ ¬ (0 ≤ -a - 1 ∧ -a - 1 < (D.R.t : ℤ))) → multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (T2O D.nd i ρ π)))) τ' a = 0) := by
  intro D i w hw T LL' h r ρ hc
  have hs : Nat.card (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) =
      Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 := by
    have := (D.nbr i w hw).Kw.2
    have := LL'.2
    have h1 := (GlobalTheory.splits_of_conjugates_mem _ (D.nbr i w hw).Kw LL' (fun τ x => h
      ((D.nbr i w hw).LL_split τ x)) inferInstance).2
    rw [Nat.card_eq_fintype_card, h1]
  have hd := fun x => tateDual T (D.nbr i w hw).Kw LL' hs _ _ (loc_rDuO D i w hw LL' h r x) (hc x)
  have hj := GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero _ _ _ T (D.nbr i w hw).Kw LL'
  refine ⟨fun V _ _ _ _ _ ρ₁ hsub => ⟨isCrys_of_isSubOfSums T (D.nbr i w hw).Kw LL' _
    (fun x => (hd x).1) V ρ₁ hsub, fun τ' a ha => ?_⟩, fun π hπ hle => ?_⟩
  · refine GlobalTheory.SubSumJumps.jumpsInV_of_isSubOfSums (Br.PD D.loc D.nbr i w hw) ρ₁ _ τ'
      {a | ∃ x, IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom
        (Br.loc D.nbr i w hw (rTwO D.nd i r x)))) τ' (-a - 1)} hsub (fun x b hb => ⟨x, ?_⟩) a ha
    refine (hj _ _ τ' _).2.2.2 ?_
    rw [← (hd x).2]
    exact (hj _ _ τ' _).2.2.1 hb
  · obtain ⟨h1, h2⟩ := GlobalTheory.T.crystalline_summand_and_dual_from_inverse_character_twist D i w hw T LL' h r ρ π hπ
    obtain ⟨-, -, h3⟩ := h2 (GlobalTheory.T.isDeRham_of_isCrystalline_span _ _ _ T (D.nbr i w hw).Kw LL' _ _ (hc π)).1
    refine ⟨(h1 (hc π)).2, fun τ' a => ?_⟩
    have e1 := (h3 τ' a).2
    have e2 := (h3 τ' (-a - 1)).1
    have e3 := hle τ' (-a - 1)
    have e4 : 0 ≤ multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom
      (Br.loc D.nbr i w hw (WpO D.nd i ρ π)))) τ' (-a - 1) := (hj _ _ τ' _).2.1
    have e5 : IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom
        (Br.loc D.nbr i w hw (rTwO D.nd i r π)))) τ' (-a - 1) ↔
      multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom
        (Br.loc D.nbr i w hw (rTwO D.nd i r π)))) τ' (-a - 1) ≠ 0 := (hj _ _ τ' _).2.2
    rw [e5, e1]
    split_ifs at e2 with hh <;> omega

end GlobalTheory.TateDualCrys
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateJumpsReadingRowAdm
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalTwistDual
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.TwistRead

theorem matRep_apply {F Γ : Type} [CommRing F] [Group Γ] {k : ℕ} (M : Γ →* Matrix (Fin k) (Fin k) F)
    (g : Γ) (v : Fin k → F) : matRep M g v = (M g).mulVec v := by
  simp [matRep, Matrix.toLinAlgEquiv'_apply]

theorem local_twist_dual (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : LocTied l P AI)
    (K LL : FinExt l) (hs : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1) {n : ℕ}
    (R T U : ↥(GK K) →* Matrix (Fin n) (Fin n) ↥LL.1)
    (ν : Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1)) (χ : ↥(GK K) → ↥LL.1)
    (hν : ∀ g x, ν g x = χ g • x) (hR : ∀ g, R g = χ g • T g)
    (hU : ∀ g, U g = ((cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1) • (T g⁻¹).transpose)
    (dR : IsDR (P.PD K) (matRep R)) (dν : IsDR (P.PD K) ν)
    (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (c : ℤ) (hc : ∀ a : ℤ, multV (P.PD K) ν τ a = if a = c then 1 else 0) :
    IsDR (P.PD K) (matRep T) ∧ IsDR (P.PD K) (matRep U) ∧
      ∀ a : ℤ, multV (P.PD K) (matRep T) τ a = multV (P.PD K) (matRep R) τ (a + c) ∧
        multV (P.PD K) (matRep U) τ a = multV (P.PD K) (matRep R) τ (c - a - 1) := by
  have hRT : ∀ g x, matRep R g x = χ g • matRep T g x := by
    intro g x
    rw [matRep_apply, matRep_apply, hR, Matrix.smul_mulVec]
  have dT : IsDR (P.PD K) (matRep T) :=
    (GlobalTheory.TwistDR.isDR_twist_iff l P AI hT K LL _ (matRep T) (matRep R) ν χ hν hRT dν).2 dR
  have jT : ∀ a : ℤ, multV (P.PD K) (matRep R) τ (a + c) = multV (P.PD K) (matRep T) τ a :=
    GlobalTheory.TwistJump.multV_twist_char l P AI hT K LL _ (matRep T) (matRep R) ν χ hν hRT dν τ c hc
  have hb : Function.Bijective (dotProductBilin ↥LL.1 ↥LL.1 :
      (Fin n → ↥LL.1) →ₗ[↥LL.1] (Fin n → ↥LL.1) →ₗ[↥LL.1] ↥LL.1) :=
    (dotProductEquiv ↥LL.1 (Fin n)).bijective
  have hd := GlobalTheory.T.galois_representation_hom_finite_dimensional l P AI hT K LL _ (matRep T) _ (matRep U) _ 1 hb (by
    intro g x y
    rw [matRep_apply, matRep_apply, hU, zpow_one]
    simp only [dotProductBilin_apply_apply, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec, dotProduct_comm]) dT
  refine ⟨dT, hd.1, fun a => ⟨(jT a).symm, ?_⟩⟩
  have h1 := hd.2 τ (-a - 1) hs
  have h2 := jT (-a - 1)
  rw [show -(-a - 1) - 1 = a by ring] at h1
  rw [show -a - 1 + c = c - a - 1 by ring] at h2
  rw [h1, h2]


set_option maxHeartbeats 1000000 in
theorem twist_dual_mult : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), LocTied (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) → ∀ (LL' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).LL.1 ≤ LL'.1) (τ' : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) (τ : D.host.E →+* Qbar (D.nd.l i)), (∀ x : D.host.E, τ x = ((τ' (Br.cEw D.nbr i w hw x) : ↥LL'.1) : Om (D.nd.l i))) → ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) (χ : GE D.nd →* GL (Fin 1) (D.nd.O i)) (c : ℤ), Continuous (fun g => rO D.nd i r x g) → (∀ g, (χ g : Matrix (Fin 1) (Fin 1) (D.nd.O i)) 0 0 = ((D.nd.chi i 1 g : (D.nd.O i)ˣ) : D.nd.O i)) → D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w → D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) χ) w → D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) χ) τ = {c} → IsDR (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r x)))) ∧ IsDR (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rDuO D.nd i r x)))) ∧ ∀ a : ℤ, multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r x)))) τ' a = (((D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (r x)) τ).count (a + c) : ℕ) : ℤ) ∧ multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rDuO D.nd i r x)))) τ' a = (((D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (r x)) τ).count (c - a - 1) : ℕ) : ℤ) := by
  intro D i w hw hT LL' h τ' τ hτ r x χ c hr hχ dr dχ hc
  have tie := D.loc_tie i w hw
  set f : D.nd.O i →+* ↥LL'.1 :=
    (IntermediateField.inclusion h).toRingHom.comp (D.nbr i w hw).toLL with hf
  have hfc : Continuous f := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.comp (continuous_subtype_val.comp (D.nbr i w hw).eO_cont)
  have hmap : ∀ (m : ℕ) (ρ : GE D.nd →* GL (Fin m) (D.nd.O i)),
      mapRep (algebraMap ↥LL'.1 (Qbar (D.nd.l i))) (mapRep f ρ) = mapRep (iotaOQ D.nd D.naut i) ρ := by
    intro m ρ
    ext g a b
    exact (tie.1 _).symm
  have cr : Continuous (fun g => ((mapRep f (r x) g : GL (Fin D.R.nV) ↥LL'.1) :
      Matrix (Fin D.R.nV) (Fin D.R.nV) ↥LL'.1)) := hr.matrix_map hfc
  have cχ : Continuous (fun g => ((mapRep f χ g : GL (Fin 1) ↥LL'.1) : Matrix (Fin 1) (Fin 1) ↥LL'.1)) := by
    refine Continuous.matrix_map (A := fun g => (χ g : Matrix (Fin 1) (Fin 1) (D.nd.O i))) ?_ hfc
    refine continuous_matrix fun a b => ?_
    rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
    simp only [hχ]
    exact D.nd.chi_cont i 1
  have tr := tie.2.2 LL' h _ _ cr
  have tχ := tie.2.2 LL' h _ _ cχ
  rw [hmap] at tr tχ
  have dr' := tr.2.1.1 dr
  have dχ' := tχ.2.1.1 dχ
  have jr := (tr.2.2.2 τ τ' hτ).2 dr'
  have jχ := (tχ.2.2.2 τ τ' hτ).2 dχ'
  have hs : Nat.card (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) =
      Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 := by
    haveI : FiniteDimensional ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 := (D.nbr i w hw).Kw.2
    have := (GlobalTheory.splits_of_conjugates_mem _ (D.nbr i w hw).Kw LL'
      (fun σ y => h ((D.nbr i w hw).LL_split σ y)) inferInstance).2
    rw [Nat.card_eq_fintype_card]
    exact this
  let ι : Br.G D.nbr i w hw →* GE D.nd := (decS D.nd w).comp (Br.iota D.nbr i w hw)
  have hrep : matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rO D.nd i r x))) =
      (D.nbr i w hw).repE LL' ((mapRep f (r x)).comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) := by
    refine MonoidHom.ext fun g => LinearMap.ext fun v => ?_
    rw [matRep_apply]
    rfl
  have key := local_twist_dual (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) hT (D.nbr i w hw).Kw LL' hs
    (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rO D.nd i r x)))
    (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r x)))
    (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rDuO D.nd i r x)))
    ((D.nbr i w hw).repE LL' ((mapRep f χ).comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype))
    (fun g => f (D.nd.chi i 1 (ι g) : (D.nd.O i)ˣ))
    (by
      intro g v
      funext a
      change Matrix.mulVec ((χ (ι g) : Matrix (Fin 1) (Fin 1) (D.nd.O i)).map f) v a = _
      rw [Subsingleton.elim a 0]
      simp [Matrix.mulVec, dotProduct, hχ])
    (by
      intro g
      ext a b
      congr 1
      change f (rO D.nd i r x (ι g) a b) = f (D.nd.chi i 1 (ι g) : (D.nd.O i)ˣ) *
        f ((((D.nd.chi i 1 (ι g))⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (ι g) a b)
      rw [← map_mul, Units.mul_inv_cancel_left])
    (by
      intro g
      have e := congrArg Units.val (GlobalTheory.CycBridge.locChi_epsU D i w hw g)
      have e' : f (epsU D.nd i (ι g) : (D.nd.O i)ˣ) =
          ((cycLL ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) ↥LL'.1 g : (↥LL'.1)ˣ) : ↥LL'.1) :=
        by
        have e2 := congrArg (IntermediateField.inclusion h) e
        exact e2.trans ((IntermediateField.inclusion h).commutes _)
      rw [← e']
      ext a b
      congr 1
      change f ((((D.nd.chi i 1 (ι g)) * epsU D.nd i (ι g) : (D.nd.O i)ˣ) : D.nd.O i) *
          rO D.nd i r x ((ι g)⁻¹ : GE D.nd) b a) = f (epsU D.nd i (ι g) : (D.nd.O i)ˣ) *
        f ((((D.nd.chi i 1 (ι g⁻¹))⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (ι g⁻¹) b a)
      rw [← map_mul, map_inv ι g, map_inv (D.nd.chi i 1), inv_inv, Units.val_mul]
      congr 1
      ring)
    (by
      rw [hrep]
      unfold IsDR
      rw [Module.finrank_fin_fun]
      exact dr')
    (by
      unfold IsDR
      rw [Module.finrank_fin_fun]
      exact dχ')
    τ' c
    (by
      intro a
      refine (jχ a).symm.trans ?_
      rw [hc, Multiset.count_singleton]
      split_ifs <;> rfl)
  rw [hrep] at key
  refine ⟨key.1, key.2.1, fun a => ⟨?_, ?_⟩⟩
  · exact (key.2.2 a).1.trans (jr (a + c)).symm
  · exact (key.2.2 a).2.trans (jr (c - a - 1)).symm

end GlobalTheory.TwistRead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateJumpsReadingRowAdm
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.AdmReadBridge


set_option maxHeartbeats 1000000 in
theorem main : ∀ D : D7, AdmissibleParameterJ.AdmRead D := by
  intro D i r hr w hw C τ
  have hτ : ∀ x : D.host.E, AdmissibleParameterJ.gEmb C τ x =
      ((τ (Br.cEw D.nbr i w hw x) : ↥C.LL.1) : Om (D.nd.l i)) := fun x => rfl
  have emb := GlobalTheory.LocalEmbedding.inducesW_and_exists_emb D i w hw C.LL τ (AdmissibleParameterJ.gEmb C τ) hτ
  refine ⟨emb.1, emb.2, ?_⟩
  intro x dr dχ c hc
  have hχ : ∀ g, ((PairedCharacterCondition.chiGL i g : GL (Fin 1) (D.nd.O i)) : Matrix (Fin 1) (Fin 1) (D.nd.O i)) 0 0 =
      ((D.nd.chi i 1 g : (D.nd.O i)ˣ) : D.nd.O i) := by
    intro g
    simp [PairedCharacterCondition.chiGL]
  have tw := GlobalTheory.TwistRead.twist_dual_mult D i w hw (D.locT _) C.LL C.le τ (AdmissibleParameterJ.gEmb C τ) hτ r x
    (PairedCharacterCondition.chiGL i) c ((hr x).1) hχ dr dχ hc
  have jm : ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (a : ℤ),
      (IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ a ↔
        multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ a ≠ 0) := by
    intro k M a
    exact (GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i))
      (D.locT _) (D.nbr i w hw).Kw C.LL (Fin k → ↥C.LL.1) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ a).2.2
  refine ⟨fun a => ⟨(tw.2.2 a).1, ?_⟩, fun M _ a => jm M a, ?_⟩
  · have h := (tw.2.2 a).2
    rw [show c - a - 1 = c - 1 - a by ring] at h
    exact h
  · intro ρπ _ hd a
    have hd' := (GlobalTheory.T.admDecomp_iff_decomp D i r ρπ x).1 hd
    have hw' := ((GlobalTheory.SummandJumps.main D i w hw (D.locT _) C.LL C.le r ρπ x hd').2 tw.1).2.2 τ a
    exact ⟨hw'.1, hw'.2, jm _ a, jm _ a⟩

end GlobalTheory.AdmReadBridge
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateJumpsReadingRowAdmStatement
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTateJumpsReading_rowAdm : ∀ D : D7, AdmissibleParameterJ.AdmRead D := by
  first | exact @GlobalTheory.AdmReadBridge.main | exact GlobalTheory.AdmReadBridge.main | (intros; apply GlobalTheory.AdmReadBridge.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorFundamentalExactSequenceCrystalline
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorFundamentalExactSequenceCrystalline
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.FundSeq

theorem tensor_fundamental_sequence :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V], (∀ (u : V ⊗[ℚ_[l]] P.R.B) (w : V ⊗[ℚ_[l]] P.R.BdR), ∃ (x : V ⊗[ℚ_[l]] P.R.B) (y : V ⊗[ℚ_[l]] P.R.BdR), y ∈ FilV (P.PD K) (LL := LL) (V := V) 0 ∧ x - φVB (P.PD K) (LL := LL) (V := V) x = u ∧ ιV (P.PD K) (LL := LL) (V := V) x - y = w) ∧ ∀ x : V ⊗[ℚ_[l]] P.R.B, φVB (P.PD K) (LL := LL) (V := V) x = x → ιV (P.PD K) (LL := LL) (V := V) x ∈ FilV (P.PD K) (LL := LL) (V := V) 0 → ∃ v : V, x = v ⊗ₜ[ℚ_[l]] (1 : P.R.B) := by
  intro l _ P AI hT K LL _ _ V _ _ _ _
  obtain ⟨-, h1, h2⟩ := GlobalTheory.MemLoc.tied_regular_and_onto l P AI hT
  have hA : ∀ u : V ⊗[ℚ_[l]] P.R.B, ∃ x : V ⊗[ℚ_[l]] P.R.B,
      x - φVB (P.PD K) (LL := LL) (V := V) x = u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul v b =>
      obtain ⟨x, hx⟩ := h1 b
      refine ⟨v ⊗ₜ x, ?_⟩
      have : φVB (P.PD K) (LL := LL) (V := V) (v ⊗ₜ x) = v ⊗ₜ (P.PD K).φ x := rfl
      rw [this, P.PD_φ, ← TensorProduct.tmul_sub, hx]
    | add u u' hu hu' =>
      obtain ⟨x, hx⟩ := hu
      obtain ⟨x', hx'⟩ := hu'
      refine ⟨x + x', ?_⟩
      rw [map_add (f := _), ← hx, ← hx']
      abel
  have hB : ∀ w : V ⊗[ℚ_[l]] P.R.BdR, ∃ x : V ⊗[ℚ_[l]] P.R.B,
      φVB (P.PD K) (LL := LL) (V := V) x = x ∧
        ιV (P.PD K) (LL := LL) (V := V) x - w ∈ FilV (P.PD K) (LL := LL) (V := V) 0 := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp, by simp⟩
    | tmul v b =>
      obtain ⟨x, hx, hx'⟩ := h2 K b
      refine ⟨v ⊗ₜ x, ?_, ?_⟩
      · have : φVB (P.PD K) (LL := LL) (V := V) (v ⊗ₜ x) = v ⊗ₜ (P.PD K).φ x := rfl
        rw [this, P.PD_φ, hx]
      · have : ιV (P.PD K) (LL := LL) (V := V) (v ⊗ₜ x) = v ⊗ₜ (P.PD K).ι x := rfl
        rw [this, P.PD_ι, ← TensorProduct.tmul_sub]
        exact ⟨v ⊗ₜ ⟨P.ιB x - b, hx'⟩, rfl⟩
    | add w w' hw hw' =>
      obtain ⟨x, hx, hy⟩ := hw
      obtain ⟨x', hx', hy'⟩ := hw'
      refine ⟨x + x', by rw [map_add (f := _), hx, hx'], ?_⟩
      have := Submodule.add_mem _ hy hy'
      rw [map_add (f := _)]
      convert this using 1
      abel
  refine ⟨fun u w => ?_, fun x hx hF =>
    GlobalTheory.exists_tmul_one_of_frob_fixed_of_mem_fil_zero (P.PD K) x hx hF⟩
  obtain ⟨x₀, hx₀⟩ := hA u
  obtain ⟨x₁, hx₁, hy⟩ := hB (w - ιV (P.PD K) (LL := LL) (V := V) x₀)
  refine ⟨x₀ + x₁, _, hy, ?_, ?_⟩
  · rw [map_add (f := _), hx₁, ← hx₀]
    abel
  · rw [map_add (f := _)]
    abel

end GlobalTheory.FundSeq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorFundamentalExactSequenceCrystallineStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_fundamental_exact_sequence_crystalline : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V], (∀ (u : V ⊗[ℚ_[l]] P.R.B) (w : V ⊗[ℚ_[l]] P.R.BdR), ∃ (x : V ⊗[ℚ_[l]] P.R.B) (y : V ⊗[ℚ_[l]] P.R.BdR), y ∈ FilV (P.PD K) (LL := LL) (V := V) 0 ∧ x - φVB (P.PD K) (LL := LL) (V := V) x = u ∧ ιV (P.PD K) (LL := LL) (V := V) x - y = w) ∧ ∀ x : V ⊗[ℚ_[l]] P.R.B, φVB (P.PD K) (LL := LL) (V := V) x = x → ιV (P.PD K) (LL := LL) (V := V) x ∈ FilV (P.PD K) (LL := LL) (V := V) 0 → ∃ v : V, x = v ⊗ₜ[ℚ_[l]] (1 : P.R.B) := by
  first | exact @GlobalTheory.FundSeq.tensor_fundamental_sequence | exact GlobalTheory.FundSeq.tensor_fundamental_sequence | (intros; apply GlobalTheory.FundSeq.tensor_fundamental_sequence <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesCentralIdempotentLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesCentralIdempotentLaws
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq

theorem finite_natDegree_eq {R : Type} [Semiring R] [Finite R] (n : ℕ) :
    {f : R[X] | f.natDegree = n}.Finite := by
  refine Set.Finite.of_finite_image (f := fun p : R[X] => fun i : Fin (n + 1) => p.coeff i)
    (Set.toFinite _) ?_
  intro p hp q hq hpq
  have hp' : p.natDegree = n := hp
  have hq' : q.natDegree = n := hq
  ext i
  by_cases hi : i ≤ n
  · exact congrFun hpq ⟨i, Nat.lt_succ_of_le hi⟩
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

theorem eSerC_eq_sum {g : ℕ} [Fact g.Prime] (L : LabelDatum g) (n : ℕ)
    (hfin : {χ : Gn g n → ℂ | IsIrr χ}.Finite) (f : (ZMod g)[X]) :
    eSerC L n f = ∑ χ ∈ hfin.toFinset.filter (fun χ => HasLabel L χ f), zOf χ := by
  have hset : {χ : Gn g n → ℂ | IsIrr χ ∧ HasLabel L χ f} =
      ↑(hfin.toFinset.filter (fun χ => HasLabel L χ f)) := by
    ext χ
    simp [Set.Finite.mem_toFinset]
  rw [eSerC, hset, finsum_mem_coe_finset]

theorem eSerC_laws : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → Green → ∀ n : ℕ, (∀ f, eSerC L n f * eSerC L n f = eSerC L n f) ∧ (∀ f a, eSerC L n f * a = a * eSerC L n f) ∧ (∀ f f', f ≠ f' → eSerC L n f * eSerC L n f' = 0) ∧ (∀ f, ¬ (f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0) → eSerC L n f = 0) ∧ ∃ S : Finset (ZMod g)[X], (∀ f, f ∈ S ↔ f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0) ∧ ∑ f ∈ S, eSerC L n f = 1 := by
  intro g _ L hg hG n
  obtain ⟨hfin, hsum⟩ := GlobalTheory.T.finite_irrCharacters_and_finsum_centralIdempotents_eq_one (Gn g n)
  obtain ⟨huniq, hprops, -⟩ := GlobalTheory.T.harishChandraSeriesLabel_exists_unique_GLn g L hg hG n
  have horth := GlobalTheory.T.centralIdempotentOfIrrCharacter_orthogonal_central (Gn g n)
  have he : ∀ f, eSerC L n f = ∑ χ ∈ hfin.toFinset.filter (fun χ => HasLabel L χ f), zOf χ :=
    fun f => eSerC_eq_sum L n hfin f
  have hmem : ∀ f χ, χ ∈ hfin.toFinset.filter (fun χ => HasLabel L χ f) ↔ IsIrr χ ∧ HasLabel L χ f := by
    intro f χ
    simp [Set.Finite.mem_toFinset]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f
    rw [he f, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    have hχi := ((hmem f χ).1 hχ).1
    rw [Finset.sum_congr rfl fun χ' hχ' => (horth χ χ' hχi ((hmem f χ').1 hχ').1).1,
      Finset.sum_ite_eq, if_pos hχ]
  · intro f a
    rw [he f, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun χ hχ =>
      (horth χ χ ((hmem f χ).1 hχ).1 ((hmem f χ).1 hχ).1).2.1 a
  · intro f f' hff'
    rw [he f, he f', Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun χ hχ => Finset.sum_eq_zero fun χ' hχ' => ?_
    obtain ⟨hi, hl⟩ := (hmem f χ).1 hχ
    obtain ⟨hi', hl'⟩ := (hmem f' χ').1 hχ'
    rw [(horth χ χ' hi hi').1, if_neg]
    rintro rfl
    exact hff' ((huniq χ hi).unique hl hl')
  · intro f hf
    rw [he f]
    exact Finset.sum_eq_zero fun χ hχ => absurd (hprops χ f ((hmem f χ).1 hχ).2) hf
  · have hS := finite_natDegree_eq (R := ZMod g) n
    have hSmem : ∀ f, f ∈ hS.toFinset.filter (fun f => f.Monic ∧ f.coeff 0 ≠ 0) ↔
        f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0 := by
      intro f
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      tauto
    refine ⟨_, hSmem, ?_⟩
    calc ∑ f ∈ hS.toFinset.filter (fun f => f.Monic ∧ f.coeff 0 ≠ 0), eSerC L n f
        = ∑ f ∈ hS.toFinset.filter (fun f => f.Monic ∧ f.coeff 0 ≠ 0),
            ∑ χ ∈ hfin.toFinset, if HasLabel L χ f then zOf χ else 0 := by
          refine Finset.sum_congr rfl fun f _ => ?_
          rw [he f, Finset.sum_filter]
      _ = ∑ χ ∈ hfin.toFinset, ∑ f ∈ hS.toFinset.filter (fun f => f.Monic ∧ f.coeff 0 ≠ 0),
            if HasLabel L χ f then zOf χ else 0 := Finset.sum_comm
      _ = ∑ χ ∈ hfin.toFinset, zOf χ := by
          refine Finset.sum_congr rfl fun χ hχ => ?_
          have hi : IsIrr χ := hfin.mem_toFinset.1 hχ
          obtain ⟨f0, hf0, hu⟩ := huniq χ hi
          rw [Finset.sum_eq_single f0]
          · rw [if_pos hf0]
          · intro b _ hb
            rw [if_neg]
            exact fun h => hb (hu b h)
          · intro h0
            exact absurd ((hSmem f0).2 (hprops χ f0 hf0)) h0
      _ = 1 := by
          rw [← finsum_mem_coe_finset, Set.Finite.coe_toFinset]
          exact hsum

end GlobalTheory.GLq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesCentralIdempotentLawsStatement
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraSeriesCentralIdempotent_laws : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g), 5 ≤ g → Green → ∀ n : ℕ, (∀ f, eSerC L n f * eSerC L n f = eSerC L n f) ∧ (∀ f a, eSerC L n f * a = a * eSerC L n f) ∧ (∀ f f', f ≠ f' → eSerC L n f * eSerC L n f' = 0) ∧ (∀ f, ¬ (f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0) → eSerC L n f = 0) ∧ ∃ S : Finset (ZMod g)[X], (∀ f, f ∈ S ↔ f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0) ∧ ∑ f ∈ S, eSerC L n f = 1 := by
  first | exact @GlobalTheory.GLq.eSerC_laws | exact GlobalTheory.GLq.eSerC_laws | (intros; apply GlobalTheory.GLq.eSerC_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableRowsCDAdmissible
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableRowsCDAdmissible
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLink.RowCDSize

open Classical

theorem ratIn_le {x y c : ℝ} (hy : y ≤ c) (hc : 0 ≤ c) : ((Formalism.MainNotions.N.ratIn x y : ℚ) : ℝ) ≤ c := by
  by_cases h : x < y
  · exact (RowBSize.ratIn_lt h).le.trans hy
  · rw [RowBSize.ratIn_of_not_lt h]; simpa using hc

theorem one_le_hB {D : D7} (L : SizeData₂ D) : 1 ≤ TwistedPlaces.hB L := by
  unfold TwistedPlaces.hB
  have := RowBSize.one_le_b' L
  have := L.Sc_pos
  have := L.etaSz_pos
  have : (0 : ℝ) ≤ D.R.t := by positivity
  linarith

theorem etaP_nonneg {D : D7} (L : SizeData₂ D) : 0 ≤ TwistedPlaces.eta₃ L := by
  unfold TwistedPlaces.eta₃
  have := L.etaSz_pos
  positivity

theorem placeWeight_nonneg {D : D7} (L : SizeData₂ D) : 0 ≤ TwistedPlaces.wP L := by
  have hb : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X'
    have := RowBSize.x_pos' L
    have := RowBSize.one_le_b' L
    positivity
  have h1 : 0 ≤ L.sc.w'' D.R.n := by
    unfold Scale.w''
    have := RowBSize.x_pos' L
    positivity
  unfold TwistedPlaces.wP TwistedPlaces.wB
  have h2 := L.etaSz_pos
  have h4 : L.sc.w'' D.R.n + L.etaSz ≤ max (L.sc.w'' D.R.n + L.etaSz)
      ((⨆ t : D.host.TT, (L.bT t : ℝ)) + L.sc.b' / L.sc.x + L.etaSz) := le_max_left _ _
  have h5 : (0:ℝ) ≤ D.R.t := by positivity
  linarith

theorem coreE_nonneg {D : D7} (L : SizeData₂ D) (l : ℕ) : 0 ≤ coreE L l := by
  unfold coreE
  have h1 : 0 ≤ TwistedPlaces.hB L / l := div_nonneg (by linarith [one_le_hB L]) (by positivity)
  have h2 : 0 ≤ Real.logb l (TwistedPlaces.hB L) := by
    unfold Real.logb
    exact div_nonneg (Real.log_nonneg (one_le_hB L)) (Real.log_natCast_nonneg l)
  linarith

theorem flat_nonneg {D : D7} (L : SizeData₂ D) (bd : Prop) (l : ℕ) : 0 ≤ flat L bd l := by
  unfold flat
  have := placeWeight_nonneg L
  have := etaP_nonneg L
  have := L.Sc_pos
  have := RowBSize.one_le_Lg L
  have h1 : 0 ≤ (TwistedPlaces.wP L + TwistedPlaces.eta₃ L) / l := by positivity
  have h2 : 0 ≤ TwistedPlaces.eta₃ L * (if bd then (1:ℝ) else 0) := by split_ifs <;> simp [*]
  linarith

theorem coreH_nonneg {D : D7} (L : SizeData₂ D) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    0 ≤ coreH L l lam := by
  unfold coreH
  have := RowBSize.hB_nonneg L
  positivity

theorem coreF_nonneg {D : D7} (L : SizeData₂ D) (bd : Prop) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    0 ≤ coreF L bd l lam := by
  unfold coreF
  have := flat_nonneg L bd l
  positivity

theorem coreM_nonneg {D : D7} (L : SizeData₂ D) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    0 ≤ coreM L l lam := by
  unfold coreM
  have := coreE_nonneg L l
  positivity

theorem len_le {D : D7} (L : SizeData₂ D) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ)
    (hD : KillingConditions.DataAD L HW X R) (hR : R.Le C) (i : D.nd.Loc) (hI : TwistedPlaces.InertK D (D.nd.l i))
    (hB : ¬ KillingConditions.IsRowB L (D.nd.l i)) (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    (tabX L X).len i lam ≤ C * coreH L (D.nd.l i) lam + C * coreF L (X.band i lam) (D.nd.l i) lam +
      C * C * coreM L (D.nd.l i) lam := by
  obtain ⟨-, -, -, -, hC1, -, h1, h2, h3, -⟩ := hR
  have hH := coreH_nonneg L (D.nd.l i) lam
  have hF := coreF_nonneg L (X.band i lam) (D.nd.l i) lam
  have hM := coreM_nonneg L (D.nd.l i) lam
  have hC0 : (0:ℝ) ≤ C := by linarith
  have h0 : 0 ≤ C * coreH L (D.nd.l i) lam + C * coreF L (X.band i lam) (D.nd.l i) lam +
      C * C * coreM L (D.nd.l i) lam := by positivity
  have key : (tabX L X).len i lam = KillingConditions.supZ i
      (fun _ => ((lenRowCD L (X.band i) R.K₁ R.K₂ R.K₃ (D.nd.l i) lam : ℚ) : ℝ)) := by
    show KillingConditions.lenR X.len0 i lam = _
    unfold KillingConditions.lenR
    congr 1
    funext π
    rw [hD.len0I i hI π lam, hD.rowCD i hI hB]
  rw [key]
  unfold KillingConditions.supZ
  split_ifs with hne
  · rw [Finset.sup'_const]
    unfold lenRowCD
    refine ratIn_le ?_ h0
    unfold bdCD
    have h4 : R.K₃ ≤ C * C := by nlinarith
    have := mul_le_mul_of_nonneg_right h1 hH
    have := mul_le_mul_of_nonneg_right h2 hF
    have := mul_le_mul_of_nonneg_right h4 hM
    linarith
  · exact h0

end GlobalTheory.NLink.RowCDSize

theorem GlobalTheory.NLink.localBoundTable_rowsCD_admissible : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ), KillingConditions.DataAD L HW X R → R.Le C → TwistedPlaces.MediumInertPrimeLengthBound L (tabX L X) C ∧ TwistedPlaces.SmallInertPrimeSmallOrderLengthBound L (tabX L X) C := by
  intro D L P HW X R C hD hR
  have hfl : ∀ i lam l, TwistedPlaces.flatCD L (tabX L X) i lam l = flat L (X.band i lam) l := fun _ _ _ => rfl
  have he : ∀ l, TwistedPlaces.eP L C l = C * coreE L l := fun _ => rfl
  constructor
  · rintro i - ⟨hI, hA, -, -⟩ lam -
    have h := GlobalTheory.NLink.RowCDSize.len_le L HW X R C hD hR i hI (fun h => absurd h.1 (not_lt.2 hA)) lam
    rw [hfl, he]
    refine h.trans (le_of_eq ?_)
    unfold coreH coreF coreM
    ring
  · rintro i - ⟨hI, -, hO, -⟩ lam -
    have h := GlobalTheory.NLink.RowCDSize.len_le L HW X R C hD hR i hI (fun h => absurd h.2 (not_lt.2 hO)) lam
    rw [hfl, he]
    refine h.trans (le_of_eq ?_)
    unfold coreH coreF coreM
    ring

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableRowsCDAdmissibleStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mediumInert_smallInert_lengthBound_tabX : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ), KillingConditions.DataAD L HW X R → R.Le C → TwistedPlaces.MediumInertPrimeLengthBound L (tabX L X) C ∧ TwistedPlaces.SmallInertPrimeSmallOrderLengthBound L (tabX L X) C := by
  first | exact @GlobalTheory.NLink.localBoundTable_rowsCD_admissible | exact GlobalTheory.NLink.localBoundTable_rowsCD_admissible | (intros; apply GlobalTheory.NLink.localBoundTable_rowsCD_admissible <;> assumption)
end
end
