module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTripleAtOfConj
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseLevelIsWhit

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsGalRepCast
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ResLoc
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal _root_.Formalism.L2 _root_.Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open GlobalTheory.EigTie (ResTied IsRowPar plRed resTied_of_plSide)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE OnW)
theorem exists_galRep_cast_alt {D : D7} {a p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) {ι : Qbar p ≃+* ℂ} {π : D.naut.CG a}
    {r : GalE D →* GL (Fin a) (Qbar p)} (hr : _root_.UpperTheory.GalS.IsGaloisRepOfN D π p ι r) : ∃ r', _root_.UpperTheory.GalS.IsGaloisRepOfN D π q (qCast h ι) r' := by
  subst h
  exact ⟨r, hr⟩
end GlobalTheory.ResLoc
namespace GlobalTheory.ResLoc
end GlobalTheory.ResLoc
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharpolyCConjRed
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.TripleResidual
open NumberField IsDedekindDomain Polynomial Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.TameLabels GlobalTheory.AntiRamConj GlobalTheory.TwistDet
open GlobalTheory.TypeLeaf (WildOne FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (OnW IsBaseChange IsGaloisRepOf IsReduction Zbar GaloisReps GalE toFb)
open scoped Pointwise
section Wild
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
end Wild
section Row
variable {D : D7} (Y : NTw D.R D.host D.what₂ D.LL0 D.nd)
theorem charpoly_cConj_eq_charpoly_inv_of_mem_ine (hD : FrobDense D) {n : ℕ} {π : D.naut.CG n} (hπ : D.naut.csd π) {l : ℕ} [Fact l.Prime]
    {ι : Qbar l ≃+* ℂ} {red : Zbar l →+* Formalism.CyclotomicNorms.Fbar l} {r : GalE D →* GL (Fin n) (Qbar l)}
    {ρ : GalE D →* GL (Fin n) (Formalism.CyclotomicNorms.Fbar l)} (hr : _root_.UpperTheory.GalS.IsGaloisRepOfN D π l ι r) (hρ : IsReduction D red r ρ)
    {v : PlE D.host} (hv : v ∉ placesOver D.host.E l) {A : ValuationSubring D.nd.Om} (hA : IsPlaceOver A v)
    {s : GalE D} (hs : s ∈ Ine (F := D.host.E) A) :
    ((ρ (cConj Y s) : GL _ _) : Matrix (Fin n) (Fin n) (Formalism.CyclotomicNorms.Fbar l)).charpoly =
      ((ρ s⁻¹ : GL _ _) : Matrix (Fin n) (Fin n) (Formalism.CyclotomicNorms.Fbar l)).charpoly := by
  have h := _root_.GlobalTheory.TripleResidual.charpoly_cConj_eq_charpoly_cyc_zpow_smul_inv Y hD hπ hr s
  rw [cyc_eq_one_of_mem_Ine hv hA hs, Units.val_one, one_zpow, one_smul] at h
  obtain ⟨p, p1, p2⟩ := hρ.2.2 (cConj Y s)
  obtain ⟨q, q1, q2⟩ := hρ.2.2 s⁻¹
  rw [← p2, ← q2, Polynomial.map_injective _ Subtype.val_injective (p1.trans (h.trans q1.symm))]
end Row
section Triples
end Triples
end GlobalTheory.TripleResidual
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ResTiedOfPlSide
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.EigTie
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.Triple (IsParam IsResidual FbAt)
open GlobalTheory.HeightCounting (RowSide PlSide IotaOk setTy factRes)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE OnW)
variable {D : D7}
theorem residual_ties_of_charpoly_reduction {Rw : RowSide D} {Pl : PlSide D} (h : IotaOk D Pl)
    (hr : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ σ π r, D.nd.goodRow σ → OnW D σ → IsRowPar Rw σ π →
      _root_.UpperTheory.GalS.IsGaloisRepOfN D π _ (Pl.ι w) r → IsSSRep (D.ntypes.rbar σ w) ∧ ∀ g, ∃ p : (Zbar (D.what₂.places.resChar w))[X],
        p.map (Zbar (D.what₂.places.resChar w)).subtype = ((r g : GL (Fin D.R.r) (Qbar (D.what₂.places.resChar w))) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.what₂.places.resChar w))).charpoly ∧
        p.map (plRed Pl w) =
          ((D.ntypes.rbar σ w g : GL (Fin D.R.r) (FbAt D w)) : Matrix (Fin D.R.r) (Fin D.R.r) (FbAt D w)).charpoly) :
    _root_.GlobalTheory.EigTie.ResTiedAlt D Rw := by
  intro w hw l _ e
  subst e
  exact ⟨Pl.ι w, plRed Pl w, Pl.ι_w w, teichAt_of_iotaOk h w, fun σ π r h1 h2 h3 h4 =>
    ⟨(hr w hw σ π r h1 h2 h3 h4).1, (hr w hw σ π r h1 h2 h3 h4).2, teichAt_of_iotaOk h w⟩⟩
end GlobalTheory.EigTie
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
section
section
namespace GlobalTheory.Triple
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Polynomial ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open _root_.Formalism.L2.Host (HChar CharFrame embLL0 eExp ValLL0)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
open GlobalTheory.GalChar (IsGal toQ block)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE toFb)
open GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary (embOver)
variable {D : D7}
section API
end API
end GlobalTheory.Triple
end
end
section
section
namespace GlobalTheory.Triple
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Polynomial ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open _root_.Formalism.L2.Host (HChar CharFrame embLL0 eExp ValLL0)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
open GlobalTheory.GalChar (IsGal toQ block)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE toFb)
open GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary (embOver)
variable {D : D7}
section API
variable {C : CharFrame D} {art : Ideles D.host.E →* Gab D.host.E D.nd.Om} {X : NTw D.R D.host D.what₂ D.LL0 D.nd}
  {i : X.Tw} {b : Bool} {ρ : Reading X i b} {s : X.Sig i} {σ : D.what₂.FT} {π : D.naut.CG D.R.r}
  {r : GalE D →* GL (Fin D.R.r) (Qbar (X.l i))} {ν : GalE D →* (X.O0 i)ˣ} {w : D.what₂.places.Pl}
  {red : Zbar (X.l i) →+* FbAt D w}
theorem IsGaloisTripleWithReduction.charpoly_frob_of_isTriple (ha : IsGlobalArtin art) (h : _root_.GlobalTheory.Triple.IsGaloisTripleWithReduction C art ρ s σ π r ν w red) {P : PlE D.host}
    (hl : P ∉ placesOver D.host.E (X.l i)) (hg : ∀ k, P ∉ placesOver D.host.E (D.host.g k))
    {B : ValuationSubring D.nd.Om} (hB : IsPlaceOver B P) {g : GalE D} (hF : IsFrob (F := D.host.E) B (normV P) g) :
    ((X.rhoS i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).charpoly.map ρ.toC =
      ((D.naut.frobEig (D.naut.locG π P)).map fun a => Polynomial.X - Polynomial.C
        (a * ((normV P : ℕ) : ℂ) ^ (((1 - (D.R.r : ℝ)) / 2 : ℝ) : ℂ) * (((shiftChar C).val P : ℂˣ) : ℂ)⁻¹)).prod := by
  have hu := h.param.unr P hg
  obtain ⟨n, hn⟩ := h.shift
  have e1 := ((_root_.UpperTheory.GalS.galW' h.gal).2.2 P hl).2.2 hu B g hB hF
  have e2 := hn.frob ha (Or.inl hl) (shiftChar_unr C P) hB hF
  rw [galPol, D.naut.frobEig_tw _ _ hu, ← Matrix.charpoly_map] at e1
  have e3 : ((X.rhoS i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map ρ.toC =
      (((shiftChar C).val P : ℂˣ) : ℂ)⁻¹ •
        ((r g : GL (Fin D.R.r) (Qbar (X.l i))) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (X.l i))).map ρ.ι.toRingHom := by
    ext x y
    have := congrArg ρ.ι (congrFun (congrFun (h.rho g) x) y)
    simpa [e2, Reading.toC_apply] using this
  rw [← Matrix.charpoly_map, e3, charpoly_smul_of_prod _ _ _ e1, Multiset.map_map]
  rfl
end API
end GlobalTheory.Triple
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section
namespace GlobalTheory.TripInhab
open GlobalTheory.Triple GlobalTheory.EigTie
open GlobalTheory.GalChar (IsGal toQ inQ)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf GalE)
open GlobalTheory.TwistAbove (twGL)
variable {D : D7} {C : CharFrame D} {art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om}
end GlobalTheory.TripInhab
end
end
section
section
namespace GlobalTheory.TripleAdm
open NumberField IsDedekindDomain Polynomial Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Formalism.CyclotomicNorms (Fbar rootsBar IsGood IrredOn BB primeToPart)
open GlobalTheory.TameLabels GlobalTheory.TripleResidual
open GlobalTheory.TypeLeaf (WildOne FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf IsReduction Zbar GalE toFb)
open GlobalTheory.Triple (IsParam IsResidual Reading IsChars IsTripleWith IsTripleFor IsTripleOf IsTriple muBase hframe jIdx)
open GlobalTheory.TwistDet GlobalTheory.GalChar _root_.Formalism.L2.Host
variable {D : D7}
section Row
variable {σ : D.what₂.FT} {π : D.naut.CG D.R.r} {w : D.what₂.places.Pl}
end Row
end GlobalTheory.TripleAdm
end
end
section
section
namespace GlobalTheory.ResLoc
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal _root_.Formalism.L2 _root_.Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open GlobalTheory.EigTie (ResTied IsRowPar plRed resTied_of_plSide)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE OnW)
end GlobalTheory.ResLoc
end
end
section
section
namespace GlobalTheory.ResLoc
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal _root_.Formalism.L2 _root_.Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open GlobalTheory.EigTie (ResTied IsRowPar plRed resTied_of_plSide)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE OnW)
theorem resTied_of_points_alt_alt {D : D7} (hC : GlobalTheory.RowTie.ChebSplit D.nd) (Rw : RowSide D) (Pl : PlSide D) (hI : IotaOk D Pl)
    (hι : ∀ i : D.nd.Loc, D.naut.iotaQC i = qCast (D.nd.w_l i) (Pl.ι (D.nd.w i)))
    (hk : ∀ (i : D.nd.Loc) (y : D.nd.O i), ∃ h : iotaO D.nd D.naut i y ∈ Pl.plB (D.nd.w i),
      fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out
        (Pl.plκ (D.nd.w i) (IsLocalRing.residue (Pl.plB (D.nd.w i)) ⟨_, h⟩)) =
        D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) y))
    (hW : ∀ i σ w, D.naut.locW i σ w = Rw.locR σ w) (hLaw : GlobalTheory.ThetaExh.ParamLaws D.nd D.naut) (hO : SumRepresentations.hypO D)
    (hXi : GlobalTheory.SplitRead.XiOverO D.nd D.naut) (hpair : ∀ i, GlobalTheory.RowTie.PairLift D.nd D.naut i)
    (hL : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 →
      ∃ (i : D.nd.Loc) (P : D.naut.AV i) (x : D.nd.X i), D.nd.w i = w ∧ GlobalTheory.ThetaExh.Pairs D.nd D.naut i σ P ∧
        D.naut.ptV i P = some x) : _root_.GlobalTheory.EigTie.ResTiedAlt D Rw := by
  refine _root_.GlobalTheory.EigTie.residual_ties_of_charpoly_reduction hI fun w hw σ π r hg ⟨j, h1, h2, hσ⟩ hπ hr => ?_
  obtain ⟨i, P, x, rfl, hPσ, hx⟩ := hL j h1 h2 σ hσ w hw
  obtain ⟨r', hr'⟩ := _root_.GlobalTheory.ResLoc.exists_galRep_cast_alt (D.nd.w_l i) hr
  rw [← hι i] at hr'
  replace hr' := _root_.UpperTheory.GalS.galW' hr'
  obtain ⟨ρ, hR⟩ := lattice_of_point D.nd D.naut hLaw hO hXi i x P hx π
    (fun v hv => by rw [hpair i σ P hPσ v hv, hW, hπ.2 v hv]) hπ.1.unr r' hr'.1 hr'.2.1
    (fun v hv hu B s hB hs => by rw [Matrix.charpoly_map]; exact (hr'.2.2 v hv).2.2 hu B s hB hs)
  have hr1 : 1 ≤ D.R.r := by
    have := D.R.m_add_three_le_k; have := D.R.two_le_m
    simp only [Ranks.r]; omega
  have hP : HasParamW D.nd D.naut i σ [⟨D.R.r, π, 1⟩] :=
    ⟨by simp [hr1], by simp [rankIso], fun v hv => by rw [GlobalTheory.RowRepOcc.isoLoc_one, hW, hπ.2 v hv]⟩
  obtain ⟨hss, hcp⟩ := D.rbar_tie i σ _ ρ hP hR
  refine ⟨hss, fun g => ?_⟩
  let φ : D.nd.O i →+* Zbar (D.what₂.places.resChar (D.nd.w i)) :=
    ((Pl.ι (D.nd.w i)).symm.toRingHom.comp (iotaO D.nd D.naut i)).codRestrict _
      fun y => (Pl.plB_eq _ _).1 (hk i y).1
  refine ⟨((ρ g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly.map φ, ?_, ?_⟩
  · rw [Polynomial.map_map]
    exact _root_.GlobalTheory.ResLoc.charpoly_lattice_alt hC i _ (hι i) (hW i σ) hP hR hπ hr g
  · apply Polynomial.map_injective
      (fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out).toRingHom (RingEquiv.injective _)
    rw [hcp g, Polynomial.map_map, Polynomial.map_map]
    congr 1
    ext y
    obtain ⟨h, e⟩ := hk i y
    refine Eq.trans ?_ e
    change fbCast _ _ _ (Pl.plκ (D.nd.w i) (IsLocalRing.residue (Pl.plB (D.nd.w i)) ⟨_, _⟩)) = _
    congr 4
    exact (Pl.ι (D.nd.w i)).apply_symm_apply _
end GlobalTheory.ResLoc
end
end
section
section
namespace GlobalTheory.TripleResidual
open NumberField IsDedekindDomain Polynomial Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.TameLabels GlobalTheory.AntiRamConj GlobalTheory.TwistDet
open GlobalTheory.TypeLeaf (WildOne FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (OnW IsBaseChange IsGaloisRepOf IsReduction Zbar GaloisReps GalE toFb)
open scoped Pointwise
section Row
variable {D : D7} (Y : NTw D.R D.host D.what₂ D.LL0 D.nd)
end Row
end GlobalTheory.TripleResidual
end
end
section
section
namespace GlobalTheory.Triple
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Polynomial ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction.Gen
open _root_.Formalism.L2.Host (HChar CharFrame)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
open GlobalTheory.GalChar (IsGal toQ)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE)
open GlobalTheory.TripleGal (UnrRho HkFrob)
variable {D : D7} {X : NTw D.R D.host D.what₂ D.LL0 D.nd} {i : X.Tw}
end GlobalTheory.Triple
end
end
section
namespace GlobalTheory.TripleAdm
open NumberField IsDedekindDomain Polynomial Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Formalism.CyclotomicNorms (Fbar rootsBar IsGood IrredOn BB primeToPart)
open GlobalTheory.TameLabels GlobalTheory.TripleResidual
open GlobalTheory.TypeLeaf (WildOne FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf IsReduction Zbar GalE toFb)
open GlobalTheory.Triple (IsParam IsResidual Reading IsChars IsTripleWith IsTripleFor IsTripleOf IsTriple muBase hframe jIdx)
open GlobalTheory.TwistDet GlobalTheory.GalChar _root_.Formalism.L2.Host
variable {D : D7}
section Row
variable {σ : D.what₂.FT} {π : D.naut.CG D.R.r} {w : D.what₂.places.Pl}
theorem irredOn_rbar_and_inertia_of_residual (Y : NTw D.R D.host D.what₂ D.LL0 D.nd) (hW : WildOne D) (hg : D.nd.goodRow σ) (hπ : IsParam σ π)
    {l : ℕ} [Fact l.Prime] (hl : D.what₂.places.resChar w = l) {ι : Qbar l ≃+* ℂ}
    {r : GalE D →* GL (Fin D.R.r) (Qbar l)} {red : Zbar l →+* FbAt D w} (hr : _root_.UpperTheory.GalS.IsGaloisRepOfN D π l ι r)
    (hρ : IsResidual ι r σ w red) :
    @IrredOn _ _ ⟨D.what₂.places.resChar_prime w⟩ _ _ (D.ntypes.rbar σ w) ⊤ ∧
    ∀ k, l ≠ D.host.g k → ∀ v : D.nd.PlG k,
      (∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)),
        ((D.ntypes.rbar σ w (cConj Y s) : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (FbAt D w)).charpoly =
          ((D.ntypes.rbar σ w s⁻¹ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (FbAt D w)).charpoly) ∧
      (∀ u, WildAt (D.nd.plOm.1 (D.naut.plGw k v)) u → D.ntypes.rbar σ w u = 1) ∧
      ∀ (j : Fin D.R.m) (u : (ZMod (D.host.g k))ˣ), u = D.nd.chiT k v j ∨ u = (D.nd.chiT k v j)⁻¹ →
        ¬ ((D.ntypes.rbar σ w (D.ntypes.tg k v) : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (FbAt D w)).charpoly.IsRoot
          (D.ntypes.iota k v w (toFb D k u)) := by
  subst hl
  have hr' := _root_.UpperTheory.GalS.galW' hr
  have hlp := D.what₂.places.resChar_prime w
  have hred : IsReduction D red r (D.ntypes.rbar σ w) := ⟨D.ntypes.rbar_open σ w, hρ.ss, hρ.charpoly⟩
  have hwild : ∀ k, D.what₂.places.resChar w ≠ D.host.g k → ∀ (v : D.nd.PlG k) u,
      WildAt (D.nd.plOm.1 (D.naut.plGw k v)) u → D.ntypes.rbar σ w u = 1 := fun k hk v u hu =>
    reduction_eq_one_of_wildAt hW (gw_fixed hW hg hπ k v) (by rw [← hπ.lab, (D.nd.lab_monic k σ v).2]) hk hr' hred hu
  refine ⟨?_, fun k hk v => ⟨fun s hs => ?_, hwild k hk v, fun j u hu h0 => ?_⟩⟩
  · obtain ⟨k, hk⟩ : ∃ k, D.what₂.places.resChar w ∉ BB D.R.r (D.host.g k) := by
      by_contra h
      push Not at h
      exact Set.disjoint_left.1 D.ntypes.BB_disj (h 0) (h 1)
    have hk' : D.what₂.places.resChar w ≠ D.host.g k := fun e => hk (Or.inl e)
    have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    obtain ⟨h0, h1, h2, -, h4, -⟩ := (hg k).1
    refine irredOn_of_labels (fun v => (h0 v).2.1) h1 h4 (fun v => D.ntypes.iota k v w)
      (fun v x hx y hy h => h2 _ hlp hk v x hx y hy (primeToPart_eq_of_eq _ (D.ntypes.iota_inj k v w)
        (root_ne_zero hg k v hx) (root_ne_zero hg k v hy) h)) _ (D.ntypes.tg k) (fun v => ?_)
      fun v => charpoly_rbar_tg_eq_prod_roots hW hg hπ hk' v hr' hρ
    obtain ⟨φ, hφ⟩ := exists_isFrob (D.nd.plOm.2 (D.naut.plGw k v))
    rw [normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) (D.naut.plGw_over k v)] at hφ
    have h3 := hwild k hk' v _ (wild_of_frob (D.ntypes.tg_mem k v) hφ)
    rw [map_mul, map_inv, inv_mul_eq_one, map_pow] at h3
    exact ⟨φ, h3.symm⟩
  · exact _root_.GlobalTheory.TripleResidual.charpoly_cConj_eq_charpoly_inv_of_mem_ine Y (GlobalTheory.SplitFrobDense.frobDense D GlobalTheory.Published.cheb_holds) hπ.csd hr hred
      (not_mem_of_ne hlp hk) (D.nd.plOm.2 _) hs
  · have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    rw [charpoly_rbar_tg_eq_prod_roots hW hg hπ hk v hr' hρ, IsRoot, eval_multiset_prod, Multiset.map_map, Multiset.prod_eq_zero_iff,
      Multiset.mem_map] at h0
    obtain ⟨x, hx, e⟩ := h0
    simp only [Function.comp_apply, eval_sub, eval_X, eval_C, sub_eq_zero] at e
    have h3 := primeToPart_eq_of_eq _ (D.ntypes.iota_inj k v w) (root_ne_zero hg k v hx) (toFb_ne_zero k u) e.symm
    rcases hu with rfl | rfl
    · exact (hg k).1.2.2.2.1 _ hlp hk v j x hx h3
    · exact (hg k).2.2.2.2.1 _ hlp hk v j x hx h3
end Row
end GlobalTheory.TripleAdm
end
end
end
