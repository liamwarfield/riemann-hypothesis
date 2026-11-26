module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.GalRead
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LambdaBoundFromMeasure
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ProportionalityPrincipleCompactification
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeometricWeakTies

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTripleAtOfConj
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.Triple
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Polynomial ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open _root_.Formalism.L2.Host (HChar CharFrame embLL0 eExp ValLL0)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
open GlobalTheory.GalChar (IsGal toQ block)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE toFb)
open GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary (embOver)
variable {D : D7}
section Reading
variable (X : NTw D.R D.host D.what₂ D.LL0 D.nd)
variable {X} {i : X.Tw} {b : Bool}
end Reading
section Comparison₂
variable (C : CharFrame D) (art : Ideles D.host.E →* Gab D.host.E D.nd.Om) {X : NTw D.R D.host D.what₂ D.LL0 D.nd}
structure IsGaloisTripleWithReduction {i : X.Tw} {b : Bool} (ρ : Reading X i b) (s : X.Sig i) (σ : D.what₂.FT) (π : D.naut.CG D.R.r)
    (r : GalE D →* GL (Fin D.R.r) (Qbar (X.l i))) (ν : GalE D →* (X.O0 i)ˣ) (w : D.what₂.places.Pl)
    (red : Zbar (X.l i) →+* FbAt D w) : Prop where
  good : D.nd.goodRow σ
  occurs : D.what₂.isot (X.jS i s) σ ≠ ⊥
  param : IsParam σ π
  gal : _root_.UpperTheory.GalS.IsGaloisRepOfN D π (X.l i) ρ.ι r
  shift : ∃ n, IsGal art ρ.κ ρ.ι (shiftChar C) n ν
  rho : ∀ g, ((X.rhoS i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (toQ ρ.κ) =
    toQ ρ.κ ((ν g : (X.O0 i)ˣ) : X.O0 i) •
      ((r g : GL (Fin D.R.r) (Qbar (X.l i))) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (X.l i)))
  hecke : ∀ k P, k ≤ D.R.r → IsSplitPl D.host P → P ∉ X.S0 i → ∃ x : X.O0 i,
    algebraMap (X.O0 i) (X.O i) x = X.hEig i s k P ∧ ρ.toC x = heckeVal (muBase C (X.l i) (jIdx s)) π k P
  induces : ρ.Induces w
  residual : IsResidual ρ.ι r σ w red
def IsGaloisTripleAtSignature {i : X.Tw} {b : Bool} (ρ : Reading X i b) (s : X.Sig i) : Prop :=
  ∃ σ π r ν w red, _root_.GlobalTheory.Triple.IsGaloisTripleWithReduction C art ρ s σ π r ν w red
structure IsGaloisTripleForExpansion (Y : NExp D.R D.host D.what₂ D.LL0 D.nd X) : Prop where
  artin : IsGlobalArtin art
  evidence : ∀ i, X.NonzeroIndexPlace i → ∀ b : Bool, ∃ ρ : Reading X i b, IsChars C art ρ ∧
    ∀ s : X.Sig i, X.side i s = b → _root_.GlobalTheory.Triple.IsGaloisTripleAtSignature C art ρ s
  vec : ∀ i, X.NonzeroIndexPlace i → ∀ s : X.Sig i, Formalism.MainNotions.BlochKatoReduction.Gen.goodE Y i s
  all : Y.sig_all
end Comparison₂
def IsGaloisTripleOfExpansion {X : NTw D.R D.host D.what₂ D.LL0 D.nd} (Y : NExp D.R D.host D.what₂ D.LL0 D.nd X) : Prop :=
  ∃ (C : CharFrame D) (art : Ideles D.host.E →* Gab D.host.E D.nd.Om), _root_.GlobalTheory.Triple.IsGaloisTripleForExpansion C art Y
def IsGaloisTriple (D : D7) : Prop := _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion D.nexp
section ReadingAPI
variable {X : NTw D.R D.host D.what₂ D.LL0 D.nd} {i : X.Tw} {b : Bool}
end ReadingAPI
section Chars
variable (C : CharFrame D)
variable {C} {X : NTw D.R D.host D.what₂ D.LL0 D.nd} {i : X.Tw} {b : Bool} {art : Ideles D.host.E →* Gab D.host.E D.nd.Om}
end Chars
section Values
variable (μ : HChar D.host.E) (π : D.naut.CG D.R.r) (P : PlE D.host)
end Values
section API
variable {C : CharFrame D} {art : Ideles D.host.E →* Gab D.host.E D.nd.Om} {X : NTw D.R D.host D.what₂ D.LL0 D.nd}
  {i : X.Tw} {b : Bool} {ρ : Reading X i b} {s : X.Sig i} {σ : D.what₂.FT} {π : D.naut.CG D.R.r}
  {r : GalE D →* GL (Fin D.R.r) (Qbar (X.l i))} {ν : GalE D →* (X.O0 i)ˣ} {w : D.what₂.places.Pl}
  {red : Zbar (X.l i) →+* FbAt D w}
theorem isTripleAt_of_conj_alt (good : D.nd.goodRow σ) (occurs : D.what₂.isot (X.jS i s) σ ≠ ⊥) (param : IsParam σ π)
    (gal : _root_.UpperTheory.GalS.IsGaloisRepOfN D π (X.l i) ρ.ι r) (shift : ∃ n, IsGal art ρ.κ ρ.ι (shiftChar C) n ν)
    (A : GL (Fin D.R.r) (Qbar (X.l i)))
    (rho : ∀ g, ((X.rhoS i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (toQ ρ.κ) =
      toQ ρ.κ ((ν g : (X.O0 i)ˣ) : X.O0 i) •
        ((A * r g * A⁻¹ : GL (Fin D.R.r) (Qbar (X.l i))) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (X.l i))))
    (hecke : ∀ k P, k ≤ D.R.r → IsSplitPl D.host P → P ∉ X.S0 i → ∃ x : X.O0 i,
      algebraMap (X.O0 i) (X.O i) x = X.hEig i s k P ∧ ρ.toC x = heckeVal (muBase C (X.l i) (jIdx s)) π k P)
    (induces : ρ.Induces w) (residual : IsResidual ρ.ι r σ w red) : _root_.GlobalTheory.Triple.IsGaloisTripleAtSignature C art ρ s := by
  refine ⟨σ, π, (MulAut.conj A).toMonoidHom.comp r, ν, w, red, good, occurs, param,
    _root_.GlobalTheory.Triple.isGaloisRepOfN_of_conj gal A fun _ => rfl, shift, rho, hecke, induces, residual.ss, fun g => ?_, residual.teich⟩
  obtain ⟨p, h1, h2⟩ := residual.charpoly g
  refine ⟨p, h1.trans ?_, h2⟩
  change _ = ((A * r g * A⁻¹ : GL (Fin D.R.r) (Qbar (X.l i))) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (X.l i))).charpoly
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
theorem IsGaloisTripleWithReduction.unr_of_notMem (h : _root_.GlobalTheory.Triple.IsGaloisTripleWithReduction C art ρ s σ π r ν w red) {P : PlE D.host} (hS : P ∉ X.S0 i) :
    D.naut.unr (D.naut.locG π P) := h.param.unr P fun k hk => hS (X.placesOver_subset_exceptional i k hk)
variable {Y : NExp D.R D.host D.what₂ D.LL0 D.nd X}
theorem IsGaloisTripleForExpansion.triple (h : _root_.GlobalTheory.Triple.IsGaloisTripleForExpansion C art Y) {i : X.Tw} (hi : X.NonzeroIndexPlace i) (s : X.Sig i) :
    ∃ ρ : Reading X i (X.side i s), IsChars C art ρ ∧ _root_.GlobalTheory.Triple.IsGaloisTripleAtSignature C art ρ s :=
  let ⟨ρ, h1, h2⟩ := h.evidence i hi (X.side i s)
  ⟨ρ, h1, h2 s rfl⟩
theorem IsGaloisTripleOfExpansion.allGood (h : _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion Y) : GlobalTheory.TwSys.AllGood Y := let ⟨_, _, h⟩ := h; h.vec
theorem IsGaloisTripleOfExpansion.sig_all (h : _root_.GlobalTheory.Triple.IsGaloisTripleOfExpansion Y) : Y.sig_all := let ⟨_, _, h⟩ := h; h.all
end API
end GlobalTheory.Triple
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringLambdaInvariantBound
set_option synthInstance.maxHeartbeats 200000

section
section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
namespace GlobalTheory.CovTop.LamAll
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
theorem covering_lambda_all_places_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.MeasureCondition → _root_.GlobalTheory.CovTop.LiftLambdaBound := by
  intro hP hG hM
  have hc : _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ A =>
      slopeMax_sq (nrmK p.fw i) (latW (p.T.U ((i : ℕ) + 1)) (Gk p i)) ≤
        (Fm.L x ι).sc.x ^ A * (Fm.L x ι).sc.b := by
    refine Closed.imp (Closed.and hG (Closed.and (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 1) _root_.GlobalTheory.T.lift_weight_numerator)) ?_
    rintro eps Fm CH - ⟨⟨_, -, h1⟩, ⟨A, hA, h2⟩, ⟨_, -, h3⟩⟩
    obtain ⟨x0, h⟩ := h1.and (h2.and h3)
    refine ⟨2 * A + 4, by linarith, x0, fun x hx hle ι p hp i => ?_⟩
    obtain ⟨a, b, c⟩ := h x hx hle ι p hp
    exact UpperTheory.Lit.Tam.slopeMax_sq_latW_le_pow_mul p i trivial hp.2 (a i) (b i) (c i)
  have hH : _root_.GlobalTheory.CovTop.HostNAlt 1 := _root_.GlobalTheory.CovTop.Sizes.hostN_alt 1
  have hW : _root_.GlobalTheory.CovTop.LiftWeightNumerator := _root_.GlobalTheory.T.lift_weight_numerator
  refine Closed.imp ((((hc.and hM).and hH).and hG).and hW) ?_
  intro eps Fm CH _ h
  obtain ⟨⟨⟨⟨⟨A1, hA1, hc⟩, ⟨Cm, hCm, hm⟩⟩, ⟨Ah, hAh, hh⟩⟩, ⟨Cg, -, hg⟩⟩, ⟨Cw, -, hw⟩⟩ := h
  refine ⟨A1 + (Ah + 1) + (⌈2 * Cm⌉₊ : ℝ), by have := Nat.cast_nonneg (α := ℝ) ⌈2 * Cm⌉₊; linarith, ?_⟩
  obtain ⟨x0, H⟩ := (((hc.and hm).and hh).and hg).and hw
  refine ⟨x0, fun x hx hle ι p hp i => ?_⟩
  obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ := H x hx hle ι p hp
  have hH1 := c i
  have hX : 10 ≤ (Fm.L x ι).sc.x := hH1.big.2.1.trans hH1.big.2.2.1
  have hb : 0 ≤ (Fm.L x ι).sc.b := le_trans (by positivity) hH1.room
  exact le_rpow_of_add hX hb hA1 (by linarith [hH1.poly.1]) hCm (unitE_le p i hH1 (e i))
    ((slopeMax_all_le p i Cm (d i) (b i)).trans (by linarith [a i]))
end GlobalTheory.CovTop.LamAll
end
end
section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftLambdaBound_of_gram_meas : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.MeasureCondition → _root_.GlobalTheory.CovTop.LiftLambdaBound := by
  first | exact @_root_.GlobalTheory.CovTop.LamAll.covering_lambda_all_places_alt | exact _root_.GlobalTheory.CovTop.LamAll.covering_lambda_all_places_alt | (intros; apply _root_.GlobalTheory.CovTop.LamAll.covering_lambda_all_places_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemberSizes
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ValSizesAt
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ValSizesAt
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.MemberData
theorem val_sizes_at_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p)
    (fun κ _ O _ _ => Std κ.C ∧ Val κ.C κ.cD κ.ch O.L ∧ SizesAt O.L) := by
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb he _ h52 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hC _ _ => ?_⟩⟩
  obtain ⟨c1, h1⟩ := szRow_sizesAt eps he h52 C hC
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, h2⟩ := h1 cD hcD
  refine ⟨c2, fun ch hch _ => ?_⟩
  obtain ⟨x0, h3⟩ := h2 ch hch
  refine ⟨x0, fun K hK hx β _ c b _ => ?_⟩
  obtain ⟨e1, e2, e3, e4, -⟩ := hK
  have hv : Val C cD ch β.O.L := val_congr e1 e2 e3 (β.p.pt_val β.val)
  have hs : β.O.L.sc = K.s := β.sc
  refine ⟨hC, hv, h3 β.D β.O.L ?_ ?_ hv⟩
  · rw [hs]; exact e4
  · rw [hs]; exact hx
theorem dataNW_of_isGoodE_of_isLinked : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL),
    GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => GlobalTheory.Core.Deg.DataNW D) := fun hL p =>
  ((_root_.GlobalTheory.Fam.MemberData.val_sizes_at_alt hL p).and (_root_.GlobalTheory.Fam.MemberCount.rankMu_of_good_linked hL p)).imp fun _ _ β _ _ _ _ _ H =>
    dataNW_of_val H.1.1 β.O.L H.1.2.1 H.1.2.2 H.2
end GlobalTheory.Fam.MemberData
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ValSizesAtStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dataNW_all_linked_good_members : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => GlobalTheory.Core.Deg.DataNW D) := by
  first | exact @_root_.GlobalTheory.Fam.MemberData.dataNW_of_isGoodE_of_isLinked | exact _root_.GlobalTheory.Fam.MemberData.dataNW_of_isGoodE_of_isLinked | (intros; apply _root_.GlobalTheory.Fam.MemberData.dataNW_of_isGoodE_of_isLinked <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmissibleRanksOfMass
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmissibleRanksOfMass
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.MemberFrame
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL)
theorem admissible_ranks_of_mass_alt : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => LocalBesselAndTopKernel.FamilyMidVolume D) :=
  RowE.of_all fun _ K β _ b _ _ _ =>
    admissible_ranks_of_mass_formula β.D β.O.ex.lev b.R.T.toTiedDataS.cols (Dstar_eq_mass K β.X β.c.isOver β.c.dsig_eq)
theorem three_mul_L_le_m_sub_one_and_cGam : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun κ D O _ _ =>
    3 * O.L.sc.L ≤ (D.R.m : ℝ) - 1 ∧ O.L.CGam = κ.C.CGam) := by
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb _ _ he _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C _ _ _ =>
    ⟨0, fun cD _ => ⟨0, fun ch _ _ => ⟨256, fun K hK hx β _ c b _ => ?_⟩⟩⟩⟩⟩
  have hs : β.O.L.sc = K.s := β.sc
  have hc : β.O.L.CGam = C.CGam := β.val.CGam_eq.trans (congrArg Inhab.FC.CGam hK.1)
  have he' : K.s.eps = eps := hK.2.2.2.1
  exact ⟨three_L_le β.val.ranks (by rw [hs, he']; exact he) (by rw [hs]; exact hx), hc⟩
theorem tFrameAt_at_linked : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p)
    (fun _ D _ _ _ => Formalism.L2.SG.RowsConc.TFrameAt D) := by
  have h := ((((_root_.GlobalTheory.Fam.MemberFrame.admissible_ranks_of_mass_alt hL p).and (_root_.GlobalTheory.T.degHypL_all_linked_good_members hL p (fun _ => 29) (fun _ => 0))).and (_root_.GlobalTheory.T.dataNW_all_linked_good_members hL p)).and
    (_root_.GlobalTheory.T.rankMu_all_linked_members hL p)).and (_root_.GlobalTheory.Fam.MemberFrame.three_mul_L_le_m_sub_one_and_cGam hL p)
  refine RowE.imp h ?_
  intro κ K β c b _ _ _ H0
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5, h6⟩ := H0
  have hH : Formalism.MainNotions.S.StandingHypotheses β.D β.O.L (max 29 (8 * κ.C.CGam)) (max 0 40) (κ.C.P.CYL + 1) (1 / 4) 3 (1 / 2) κ.C.CTu :=
    ⟨h6 ▸ le_max_right _ _, h2.2⟩
  exact member_frame_of_standing_hypotheses_window_three β.p.pt.xa.ties h1 ⟨hH, GlobalTheory.Core.Diag.standingNumericalData_three_of_dataNW_rankMu _ h3 h4, by norm_num⟩
    (le_max_left _ _) (le_max_right _ _) h5
theorem tFrameAt_at_linked_of_recT : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL),
    GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => Formalism.L2.SG.RowsConc.TFrameAt D) :=
  fun hL p => _root_.GlobalTheory.Fam.MemberFrame.tFrameAt_at_linked hL p
end GlobalTheory.Fam.MemberFrame
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmissibleRanksOfMassStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_frame_all_members' : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => Formalism.L2.SG.RowsConc.TFrameAt D) := by
  first | exact @_root_.GlobalTheory.Fam.MemberFrame.tFrameAt_at_linked_of_recT | exact _root_.GlobalTheory.Fam.MemberFrame.tFrameAt_at_linked_of_recT | (intros; apply _root_.GlobalTheory.Fam.MemberFrame.tFrameAt_at_linked_of_recT <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowEBigGap
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowEBigGap
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Core.Rk.GapAt
theorem rowE_bigGap_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL),
    GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => GlobalTheory.Core.Rk.BigGap D) := by
  intro hL p
  refine ⟨1, one_pos, fun _ _ _ _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ =>
    ⟨11311, fun ch hch _ => ⟨300000 * 4 ^ 30, fun K hK hx β _ _ _ _ => ?_⟩⟩⟩⟩⟩
  show BigGap β.X.toD7
  refine bigGap_of_val β.val ?_ ?_
  · rw [hK.2.2.1]; exact hch
  · rw [β.sc]; exact hx
end GlobalTheory.Core.Rk.GapAt
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowEBigGapStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bigGap_of_isGoodE_isLinked : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => GlobalTheory.Core.Rk.BigGap D) := by
  first | exact @_root_.GlobalTheory.Core.Rk.GapAt.rowE_bigGap_alt | exact _root_.GlobalTheory.Core.Rk.GapAt.rowE_bigGap_alt | (intros; apply _root_.GlobalTheory.Core.Rk.GapAt.rowE_bigGap_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmissibleRanksAtMember
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmissibleRanksAtMember
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.MemberRanks
theorem admissible_ranks_at_member_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL),
    GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D) := by
  intro hL p
  refine GlobalTheory.Fc.RowE.of_all fun κ K β c b h0 h1 h2 => ?_
  obtain ⟨hv, -⟩ :=
    GlobalTheory.Fc.built_val _root_.GlobalTheory.Fc.BundleCondition (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) κ β.D β.O c b (GlobalTheory.Fc.Built.intro h0 h1 h2)
  exact columnRowRanks_admissible_of_massFormula β.D β.O.lev b.R.T.cols (dstar_mass K β.X β.c.isOver β.c.dsig_eq)
    (GlobalTheory.Proof.ColumnStabilizerTrivialLocal.gBig_of_large (typePrimesLarge_of_val β.O.L hv)) (fun u => GlobalTheory.CollCompare.splits_level β.D u)
end GlobalTheory.MemberRanks
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmissibleRanksAtMemberStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.familyMidVolume_at_linked : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D) := by
  first | exact @_root_.GlobalTheory.MemberRanks.admissible_ranks_at_member_alt | exact _root_.GlobalTheory.MemberRanks.admissible_ranks_at_member_alt | (intros; apply _root_.GlobalTheory.MemberRanks.admissible_ranks_at_member_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemberSizes
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.MemberSizes
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL)
theorem ties_at_alt : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => Formalism.BasicNotions.Ties D) :=
  RowE.of_all fun _ _ β _ _ _ _ _ => β.p.pt.xa.ties
theorem linked_scale_ge_H_and_cgam_eq (H : Formalism.MainNotions.Inhab.FC → ℝ) : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun κ _ O _ _ =>
    H κ.C ≤ O.L.sc.L ∧ O.L.CGam = κ.C.CGam ∧ 1 ≤ κ.C.CGam) := by
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb he _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hC _ _ =>
    ⟨0, fun cD _ => ⟨0, fun ch _ _ => ⟨max 1 (max (H C) 1 ^ eps⁻¹), fun K hK hx β _ c b _ => ?_⟩⟩⟩⟩⟩
  have hG : 1 ≤ C.CGam := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [Inhab.FC.cMid])
  have hs : β.O.L.sc = K.s := β.sc
  have hc : β.O.L.CGam = C.CGam := β.val.CGam_eq.trans (congrArg Inhab.FC.CGam hK.1)
  refine ⟨?_, hc, hG⟩
  show H C ≤ β.O.L.sc.x ^ β.O.L.sc.eps
  rw [hs, hK.2.2.2.1]
  have h1 : 0 ≤ max (H C) 1 := le_trans zero_le_one (le_max_right _ _)
  calc H C ≤ max (H C) 1 := le_max_left _ _
    _ = (max (H C) 1 ^ eps⁻¹) ^ eps := (Real.rpow_inv_rpow h1 he.ne').symm
    _ ≤ K.s.x ^ eps := Real.rpow_le_rpow (Real.rpow_nonneg h1 _) (le_trans (le_max_right _ _) hx) he.le
theorem parameters_scale_rank_gap_bounds (F G H : ℝ → ℝ → ℝ) : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D O _ _ =>
    ∃ C' Cl Cg CT : ℝ, F Cg CT ≤ C' ∧ G Cg CT ≤ Cl ∧ H Cg CT ≤ O.L.sc.L ∧
      GlobalTheory.Core.Rk.HD D O.L.sc.L C' Cl Cg (1 / 4) 3 (1 / 2) CT ∧ GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D O.L.sc.L C' ∧
      (∀ u, GlobalTheory.Core.Rk.RankMu D u) ∧ GlobalTheory.Core.Rk.BigGap D ∧ 1 ≤ D.R.rS) := by
  have h := (((((((_root_.GlobalTheory.Fam.MemberSizes.ties_at_alt hL p).and (_root_.GlobalTheory.T.familyMidVolume_at_linked hL p)).and (_root_.GlobalTheory.T.degHypL_all_linked_good_members hL p (fun C => F (C.P.CYL + 1) C.CTu) (fun C => G (C.P.CYL + 1) C.CTu))).and (_root_.GlobalTheory.T.dataNW_all_linked_good_members hL p)).and (_root_.GlobalTheory.T.type_frame_all_members' hL p)).and (_root_.GlobalTheory.T.rankMu_all_linked_members hL p)).and (_root_.GlobalTheory.T.bigGap_of_isGoodE_isLinked hL p)).and (_root_.GlobalTheory.Fam.MemberSizes.linked_scale_ge_H_and_cgam_eq hL p (fun C => H (C.P.CYL + 1) C.CTu))
  refine RowE.imp h ?_
  intro κ K β c b _ _ _ H0
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8, h9, h10⟩ := H0
  have hm : max (G (κ.C.P.CYL + 1) κ.C.CTu) 40 ≤ (β.D.R.m : ℝ) :=
    h3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨max (F (κ.C.P.CYL + 1) κ.C.CTu) (8 * κ.C.CGam), max (G (κ.C.P.CYL + 1) κ.C.CTu) 40, κ.C.P.CYL + 1, κ.C.CTu,
    le_max_left _ _, le_max_left _ _, h8, ⟨h1, h2, h3, h4, h5⟩, ⟨β.O.L, rfl, h9 ▸ le_max_right _ _, h9 ▸ h10⟩, h6, h7, ?_⟩
  have h40 : (40 : ℝ) ≤ β.D.R.m := le_trans (le_max_right _ _) hm
  have : 40 ≤ β.D.R.m := by exact_mod_cast h40
  show 1 ≤ β.D.R.m / 2 - 1
  omega
theorem parameters_scale_size_bounds_of_member : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (F G H : ℝ → ℝ → ℝ),
    GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D O _ _ => ∃ C' Cl Cg CT : ℝ, F Cg CT ≤ C' ∧ G Cg CT ≤ Cl ∧
      H Cg CT ≤ O.L.sc.L ∧ GlobalTheory.Core.Rk.HD D O.L.sc.L C' Cl Cg (1 / 4) 3 (1 / 2) CT ∧ GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D O.L.sc.L C' ∧
      (∀ u, GlobalTheory.Core.Rk.RankMu D u) ∧ GlobalTheory.Core.Rk.BigGap D ∧ 1 ≤ D.R.rS) :=
  fun hL p F G H => _root_.GlobalTheory.Fam.MemberSizes.parameters_scale_rank_gap_bounds hL p F G H
end GlobalTheory.Fam.MemberSizes
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemberSizesStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_constants_for_parameters_scale_bundle : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (F G H : ℝ → ℝ → ℝ), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D O _ _ => ∃ C' Cl Cg CT : ℝ, F Cg CT ≤ C' ∧ G Cg CT ≤ Cl ∧ H Cg CT ≤ O.L.sc.L ∧ GlobalTheory.Core.Rk.HD D O.L.sc.L C' Cl Cg (1 / 4) 3 (1 / 2) CT ∧ GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D O.L.sc.L C' ∧ (∀ u, GlobalTheory.Core.Rk.RankMu D u) ∧ GlobalTheory.Core.Rk.BigGap D ∧ 1 ≤ D.R.rS) := by
  first | exact @_root_.GlobalTheory.Fam.MemberSizes.parameters_scale_size_bounds_of_member | exact _root_.GlobalTheory.Fam.MemberSizes.parameters_scale_size_bounds_of_member | (intros; apply _root_.GlobalTheory.Fam.MemberSizes.parameters_scale_size_bounds_of_member <;> assumption)
end
end
end
