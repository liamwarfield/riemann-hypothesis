module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspParameterAtMemberOfParallelCopy
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TiedConditionOfLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PointsOfTiedLattices

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LambdaPosOfTwistedMu
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.Mem.LamPosTw
theorem lambda_pos_of_twisted_mu_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∀ v, TwistedAt (w.D Z) v → ∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → ∀ σ, (w.D Z).what₂.isot j σ ≠ ⊥ → 0 < (w.D Z).what₂.lamP ((w.D Z).what₂.muTw v) j σ := by
  intro hP hL
  have e1 := evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev
  have e0 : EvLgG fun _ _ _ _ => True :=
    e1.imp fun K _ _ _ _ _ => ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp,
      fun _ _ _ _ _ _ _ => trivial⟩
  unfold _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint
  refine (e0.inter e1).imp fun K _ _ _ _ H => ?_
  obtain ⟨hK, hH⟩ := H
  refine hK.imp fun B f T hO _ _ w Z Wt p0 t nch n xd c _ _ _ v hTw j hj1 hjm σ hne => ?_
  letI : Algebra (↥t.r.z.core.Q.c.F) (w.D Z).what₂.LL := t.r.z.alg
  have host : Formalism.IndefR.Links.HostHyp (w.D Z) := (hH (w.st Z) hO).1
  obtain ⟨p, hp⟩ := GlobalTheory.Mem.LamPosTw.hasLab_exists hP.decay (w.D Z) _ _ _ _ _ _ t.r.z.R t.r.z.F t.r.z.cG p0
    t.r.Y t.r.Z t.r.z.pins t.r.intersectionNumber_baseChange host σ
  have hi : j - 1 < (w.D Z).R.m := by omega
  have hj' : ((⟨j - 1, hi⟩ : Fin (w.D Z).R.m) : ℕ) + 1 = j := by simp only; omega
  have hmu : (w.D Z).what₂.muTw v = t.r.Y.tup (t.r.z.R.mu ((w.D Z).plEq v)) := by
    rcases (w.D Z).what₂.muAt_or v with h | h
    · exact absurd h hTw
    · rw [← h]; exact t.r.Y.muAt v
  have key := GlobalTheory.Mem.LamPosTw.eigenvalue_eq_of_label (w.D Z) _ _ _ _ _ _ t.r.z.R t.r.z.F t.r.z.cG p0 t.r.Y t.r.Z t.r.z.pins
    t.r.intersectionNumber_baseChange host σ p ⟨j - 1, hi⟩ (t.r.z.R.mu ((w.D Z).plEq v)) hp (Or.inr ⟨v, (t.r.Y.muAt v).symm⟩) (by rw [hj']; exact hne)
  rw [hj'] at key
  rw [hmu, key]
  exact t.r.intersectionNumber_baseChange.prim.posScal.2 _ _ _ _
end GlobalTheory.Mem.LamPosTw
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lamP_muTw_pos_at_members : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∀ v, TwistedAt (w.D Z) v → ∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → ∀ σ, (w.D Z).what₂.isot j σ ≠ ⊥ → 0 < (w.D Z).what₂.lamP ((w.D Z).what₂.muTw v) j σ := by
  first | exact @_root_.GlobalTheory.Mem.LamPosTw.lambda_pos_of_twisted_mu_alt | exact _root_.GlobalTheory.Mem.LamPosTw.lambda_pos_of_twisted_mu_alt | (intros; apply _root_.GlobalTheory.Mem.LamPosTw.lambda_pos_of_twisted_mu_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsLocalizationAtMember
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemMono
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.HeightCounting.Up.LocEx
theorem atMem_mono {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p q : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL} (h : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL p)
    (hpq : ∀ K B f T w Z Wt p0 t nch n c, p K B f T w Z Wt p0 t nch n c → q K B f T w Z Wt p0 t nch n c) : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL q :=
  EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun B f T _ H kp w Z Wt p0 t nch n xd c a b d =>
    hpq _ B f T w Z Wt p0 t nch n c (H kp w Z Wt p0 t nch n xd c a b d)
end GlobalTheory.HeightCounting.Up.LocEx
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.HeightCounting.Up.LocEx
theorem exists_localization_at_member_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∀ v, TwistedAt (w.D Z) v → ∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → ∀ σ, (w.D Z).what₂.isot j σ ≠ ⊥ → ∃ i : (w.D Z).nd.Loc, (w.D Z).nd.w i = v ∧ (w.D Z).nd.j i = j :=
  fun hP hL => _root_.GlobalTheory.HeightCounting.Up.LocEx.atMem_mono (_root_.GlobalTheory.T.lamP_muTw_pos_at_members hP hL) fun _ _ _ _ w Z _ _ t _ _ c h v hv j h1 h2 σ hσ => by
    have hl := h v hv j h1 h2 σ hσ
    obtain ⟨f, -, hf⟩ := thetaT_ne_of_lamTr (D := w.D Z) (hl.trans_eq (t.r.Y.lam _ j h1 h2 σ hσ))
    exact exists_loc_of_thetaT c.a.all.cover hv h1 h2 ⟨f, hf⟩
end GlobalTheory.HeightCounting.Up.LocEx
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_loc_with_place_and_index_at_member : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∀ v, TwistedAt (w.D Z) v → ∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → ∀ σ, (w.D Z).what₂.isot j σ ≠ ⊥ → ∃ i : (w.D Z).nd.Loc, (w.D Z).nd.w i = v ∧ (w.D Z).nd.j i = j := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.LocEx.exists_localization_at_member_alt | exact _root_.GlobalTheory.HeightCounting.Up.LocEx.exists_localization_at_member_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.LocEx.exists_localization_at_member_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisReps
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting
open NumberField IsDedekindDomain Polynomial Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped TensorProduct
variable (D : D7)
def GaloisRepsAlt : Prop :=
  ∀ π : D.naut.CG D.R.r, D.naut.csd π → D.naut.ralg π →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), ∃ r, _root_.UpperTheory.GalS.IsGaloisRepOfN D π l ι r
end GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsLocalGaloisParameterAtPlace
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocWOfNTrue
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.GalLoc.RowParamAt
set_option maxHeartbeats 4000000 in
theorem locW_of_nTrue_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D' : D7} {cf' : CharFrame D'} {C' : NChoice D'}
    {tp' : TupTied D' cf' C'} (nt : _root_.GlobalTheory.HeightCounting.NormChoiceRealisation hL D' cf' C' tp') (Rw : RowSide D') (hRw : HEq Rw.locR nt.A.row.locR) :
    ∀ i σ w, D'.naut.locW i σ w = Rw.locR σ w := by
  obtain ⟨⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hk, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩, pack⟩ := nt
  subst eq
  have e1 : Rw.locR = A.row.locR := eq_of_heq hRw
  intro i σ w
  rw [e1]
  exact Au.locW i σ w
end GlobalTheory.GalLoc.RowParamAt
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedAtAtMem
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedAtAtMem
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.GalLoc
theorem twistedAt_atMem_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => ∃ v, TwistedAt (w.D Z) v := by
  intro hL
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c _ _ _ => ?_
  obtain ⟨v, hv⟩ := GlobalTheory.Survey.PeriodBoundOfPlaceBound.exists_place (w.D Z) (B.host.g 0) (B.host.g_prime 0)
  have hW := GlobalTheory.Mem.Top.Bl.Model3.type_mem t v 0 hv
  exact ⟨v, (GlobalTheory.Mem.Top.V4.Model.mem_iff t.mu v).1 hW⟩
end GlobalTheory.GalLoc
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedAtAtMemStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twisted_place_at_member : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => ∃ v, TwistedAt (w.D Z) v := by
  first | exact @_root_.GlobalTheory.GalLoc.twistedAt_atMem_alt | exact _root_.GlobalTheory.GalLoc.twistedAt_atMem_alt | (intros; apply _root_.GlobalTheory.GalLoc.twistedAt_atMem_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.GalLoc.RowParamAt
theorem localGalois_parameter_mem_at_place_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c =>
    ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.TwInputs.RowParam (w.D Z) Rw := by
  intro hN _ hL
  refine _root_.GlobalTheory.GalLoc.atMem_mono (_root_.GlobalTheory.GalLoc.atMem_and' (_root_.GlobalTheory.GalLoc.atMem_and' (_root_.GlobalTheory.T.good_cusp_param_at_member_of_heq_locR hN hL) (_root_.GlobalTheory.T.exists_loc_with_place_and_index_at_member hN hL))
    (_root_.GlobalTheory.T.exists_twisted_place_at_member hL)) ?_
  intro K B f T w Z Wt p0 t nch n xd c _ H Rw hRw
  obtain ⟨⟨hp, hl⟩, v, hv⟩ := H
  have hW := _root_.GlobalTheory.GalLoc.RowParamAt.locW_of_nTrue_alt c.a.nt Rw hRw
  refine GlobalTheory.TwInputs.rowParam_of_cuspParam (w.D Z) Rw (hp Rw hRw) ?_ (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw _)
  intro j h1 h2 σ hσ hg
  obtain ⟨i, -, -⟩ := hl v hv j h1 h2 σ hσ
  exact GlobalTheory.HeightCounting.CuspOfParam.goodRow_cuspidal (w.D Z) Rw ⟨i⟩ hW (hp Rw hRw) j h1 h2 σ hσ hg
end GlobalTheory.GalLoc.RowParamAt
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_param_at_member_of_serN : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c =>
    ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.TwInputs.RowParam (w.D Z) Rw := by
  first | exact @_root_.GlobalTheory.GalLoc.RowParamAt.localGalois_parameter_mem_at_place_alt | exact _root_.GlobalTheory.GalLoc.RowParamAt.localGalois_parameter_mem_at_place_alt | (intros; apply _root_.GlobalTheory.GalLoc.RowParamAt.localGalois_parameter_mem_at_place_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisResTied
set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
namespace GlobalTheory.ResLoc
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal _root_.Formalism.L2 _root_.Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open GlobalTheory.EigTie (ResTied IsRowPar plRed resTied_of_plSide)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE OnW)
set_option maxHeartbeats 1000000 in
theorem resTied_of_tied_alt (hP : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hH : GlobalTheory.Published.HarishChandraFinite) (hD : GlobalTheory.Published.CuspRapidDecay)
    {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D) (X : _root_.GlobalTheory.NRows.LinkedData hL D) (hO : SumRepresentations.hypO D) (hd : DV.LamDef D)
    (hpos : ∀ v, TwistedAt D v → ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → 0 < D.what₂.lamP (D.what₂.muTw v) j σ)
    (hloc : ∀ v, TwistedAt D v → ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → ∃ i : D.nd.Loc, D.nd.w i = v ∧ D.nd.j i = j)
    (Rw : RowSide D) (hRw : HEq Rw.locR b.A.row.locR) : _root_.GlobalTheory.EigTie.ResTiedAlt D Rw := by
  obtain ⟨a1, a2, a3, a4⟩ := _root_.GlobalTheory.ResLoc.exists_paired_point_of_thetaT_ne_zero hP hH hD X
  have hpt : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 →
      ∃ (i : D.nd.Loc) (P : D.naut.AV i) (x : D.nd.X i), D.nd.w i = w ∧ GlobalTheory.ThetaExh.Pairs D.nd D.naut i σ P ∧
        D.naut.ptV i P = some x := by
    intro j h1 h2 σ hσ w hw
    obtain ⟨i, rfl, rfl⟩ := hloc w hw j h1 h2 σ hσ
    obtain ⟨i', P, x, -, e, h⟩ := a4 i σ (exists_thetaT_ne hd h1 h2 hσ (by rw [D.nd.mu_w i]; exact hpos _ hw _ h1 h2 σ hσ))
    exact ⟨i', P, x, e, h⟩
  clear X hd hpos hloc a4
  obtain ⟨D₀, cf, jE, A, _, _, _, _, _, _, _, _, _, _, _, M, C, tp, _, _, big, L, Sp, Au, _, rfl⟩ := b
  exact _root_.GlobalTheory.ResLoc.resTied_of_points_alt_alt (D := withLoc L) (GlobalTheory.ChebSplitDense.chebSplit hP.cheb D₀.nd) Rw (plL L A.pl) A.iota Au.iotaQC Au.kFbar
    (fun i σ w => (Au.locW i σ w).trans (congrFun (congrFun (eq_of_heq hRw) σ) w).symm) a1 hO a2 a3 hpt
end GlobalTheory.ResLoc
namespace GlobalTheory.ResLoc
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem residual_ties_of_membership : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → _root_.GlobalTheory.EigTie.ResTiedAlt (w.D Z) Rw := by
  intro hP hL
  refine EvG.imp (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.exists_linked_data_pinned_at_layer hP hL) (_root_.GlobalTheory.T.lamP_muTw_pos_at_members hP hL)) (_root_.GlobalTheory.T.exists_loc_with_place_and_index_at_member hP hL))
    fun _ _ _ _ _ hK => large₂.imp hK fun B f T _ H kp w Z Wt p0 t nch n xd c hE hX hp Rw hRw => ?_
  obtain ⟨⟨⟨X, -⟩, hpos⟩, hloc⟩ := H kp w Z Wt p0 t nch n xd c hE hX hp
  obtain ⟨e⟩ := hE
  exact _root_.GlobalTheory.ResLoc.resTied_of_tied_alt hP.what₂ hP.hc hP.decay c.a.nt.toNBuilt X
    (e : _root_.GlobalTheory.HeightCounting.RealExpansionExtraData (D := (w.st Z).toD7) c.row t.r.z.geo xd).large.1 t.r.Y.lam hpos hloc Rw hRw
end GlobalTheory.ResLoc
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.non_galois_residual_ties : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → _root_.GlobalTheory.EigTie.ResTiedAlt (w.D Z) Rw := by
  first | exact @_root_.GlobalTheory.ResLoc.residual_ties_of_membership | exact _root_.GlobalTheory.ResLoc.residual_ties_of_membership | (intros; apply _root_.GlobalTheory.ResLoc.residual_ties_of_membership <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisRepDefinedOverCoefficientField
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.GalLoc.FieldAt
theorem galoisRep_field_of_definition_at_place_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c =>
    ValLL0 (w.D Z) (TC.cf w.I w.l Z) ∧ (∀ (k : Fin 2) (z : ℂ), z ^ ((w.D Z).host.g k * ((w.D Z).host.g k - 1)) = 1 → z ∈ (embLL0 (w.D Z)).fieldRange) ∧ (∀ x : (w.D Z).LL0, star (x : (w.D Z).what₂.LL) ∈ (w.D Z).LL0) := by
  intro hP _ hL
  have h1 := _root_.GlobalTheory.TwInputs.SmallField.fieldOk_and_exists_lamDat_ok_teich_valuesIn hP
  have h2 := (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev).inter (evG_of_ev GlobalTheory.Mem.StdSize.vstd_size_ev)
  refine (h1.inter h2).imp fun K _ _ _ _ hK => ?_
  obtain ⟨hF, hH, hV⟩ := hK
  refine hF.imp fun B f T hO hF' => ?_
  intro hKP w Z Wt p0 t nch n xd c _ _ _
  obtain ⟨hX, -⟩ := hF' hKP T w Z
  have hHH := (hH (w.st Z) hO).1
  obtain ⟨hVs, hs⟩ := hV (w.st Z) hO
  have F := hX (GlobalTheory.TwInputs.JoinModel.realOf t hHH hVs hs) t.r.z.lev.C
  refine ⟨?_, F.roots, F.star⟩
  have v : ValLL0 (w.D Z) t.r.z.R.C := F.vals
  have e : t.r.z.R.C = TC.cf w.I w.l Z := t.r.z.lev.C
  rw [← e]
  exact v
end GlobalTheory.GalLoc.FieldAt
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valLL0_roots_of_unity_mem_star_closed_at_members : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c =>
    ValLL0 (w.D Z) (TC.cf w.I w.l Z) ∧ (∀ (k : Fin 2) (z : ℂ), z ^ ((w.D Z).host.g k * ((w.D Z).host.g k - 1)) = 1 → z ∈ (embLL0 (w.D Z)).fieldRange) ∧ (∀ x : (w.D Z).LL0, star (x : (w.D Z).what₂.LL) ∈ (w.D Z).LL0) := by
  first | exact @_root_.GlobalTheory.GalLoc.FieldAt.galoisRep_field_of_definition_at_place_alt | exact _root_.GlobalTheory.GalLoc.FieldAt.galoisRep_field_of_definition_at_place_alt | (intros; apply _root_.GlobalTheory.GalLoc.FieldAt.galoisRep_field_of_definition_at_place_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrobeniusEigenvaluesAtPlace
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TransportAltAlt
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.GalLoc.EigLoc
set_option maxHeartbeats 4000000 in
theorem parIn_loc_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D' : D7} {cf' : CharFrame D'} {C' : NChoice D'}
    {tp' : TupTied D' cf' C'} (nt : _root_.GlobalTheory.HeightCounting.NormChoiceRealisation hL D' cf' C' tp') (rep' : D'.what₂.FT → NG.FinTyp D'.host.E D'.R.r)
    (hrep : HEq nt.rep rep') :
    ∃ Rw : RowSide D', HEq Rw.locR nt.A.row.locR ∧ Nonempty (_root_.GlobalTheory.HeightCounting.Up.ParityConditions hL D' cf' rep' Rw) := by
  obtain ⟨⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hk, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩, pack⟩ := nt
  subst eq
  obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.mp pack
  obtain ⟨hcf, -⟩ := Sigma.mk.inj_iff.mp (eq_of_heq h2)
  subst hcf
  have hr : rep = rep' := eq_of_heq hrep
  subst hr
  let T : GlobalTheory.RowTie.WDTie (withLoc L).nd (withLoc L).naut := { A.wdT with }
  let Rw : RowSide (withLoc L) := { A.row with }
  refine ⟨Rw, HEq.rfl, ⟨{ T := T, lab := A.lab, chr := { A.chr with }, cg := { cg with }, A := { A.au with }, au := au, row := row }⟩⟩
set_option maxHeartbeats 4000000 in
theorem transport_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D' : D7} {cf' : CharFrame D'} {C' : NChoice D'}
    {tp' : TupTied D' cf' C'} (nt : _root_.GlobalTheory.HeightCounting.NormChoiceRealisation hL D' cf' C' tp') (Sb : Finset (PlE D'.host)) (hS0 : ∀ i, Sb ⊆ D'.ntw.S0 i)
    (e : ℕ → D'.what₂.FT → ℕ → PlE D'.host → ↥D'.LL0) (he : HEq nt.eig e)
    (S' : RatDat D'.ntw) (hS : HEq (ratL nt.L nt.S) S')
    (hL' : ∀ j, ℕ → PlE D'.host → Module.End D'.what₂.LL (S'.WL j)) (hh : HEq nt.hL hL')
    (θ' : ∀ kk : Fin 2, Multiplicative (ZMod (D'.host.g kk)) →* (↥D'.LL0)ˣ) (hθ : HEq nt.θ θ')
    (Rw0 : RowSide D') (hR0 : HEq Rw0.locR nt.A.row.locR)
    (hT : GlobalTheory.TwInputs.EigTrue D' cf' Rw0 Sb e) (hO : GlobalTheory.TwInputs.EigOcc D' S' θ' hL' Sb e) :
    ∃ Sb : Finset (PlE nt.D.host), (∀ i, Sb ⊆ (withLoc nt.L).ntw.S0 i) ∧
      (∀ Rw : RowSide (withLoc nt.L), HEq Rw.locR nt.A.row.locR →
        GlobalTheory.TwInputs.EigTrue (withLoc nt.L) (cfL nt.L nt.cf) Rw Sb nt.eig) ∧
      GlobalTheory.TwInputs.EigOcc (withLoc nt.L) ({ nt.S with } : RatDat (withLoc nt.L).ntw) nt.θ nt.hL Sb nt.eig := by
  obtain ⟨⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hk, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩, pack⟩ := nt
  subst eq
  obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.mp pack
  obtain ⟨hcf, -⟩ := Sigma.mk.inj_iff.mp (eq_of_heq h2)
  subst hcf
  have e1 : ratL L S = S' := eq_of_heq hS
  subst e1
  have e2 : hk = hL' := eq_of_heq hh
  subst e2
  have e3 : θ = θ' := eq_of_heq hθ
  subst e3
  have e4 : eig = e := eq_of_heq he
  subst e4
  refine ⟨Sb, hS0, fun Rw hRw => ?_, hO⟩
  have e5 : Rw.locR = Rw0.locR := (eq_of_heq hRw).trans (eq_of_heq hR0).symm
  unfold GlobalTheory.TwInputs.EigTrue at hT ⊢
  rw [e5]
  exact hT
end GlobalTheory.GalLoc.EigLoc
namespace GlobalTheory.GalLoc.EigLoc
end GlobalTheory.GalLoc.EigLoc
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.GalLoc.EigLoc
end GlobalTheory.GalLoc.EigLoc
namespace GlobalTheory.GalLoc.EigLoc
set_option maxHeartbeats 4000000 in
theorem frobenius_eigenvalues_at_place_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c =>
    ∃ Sb : Finset (PlE c.a.nt.D.host), (∀ i, Sb ⊆ (withLoc c.a.nt.L).ntw.S0 i) ∧ (∀ Rw : RowSide (withLoc c.a.nt.L), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.TwInputs.EigTrue (withLoc c.a.nt.L) (cfL c.a.nt.L c.a.nt.cf) Rw Sb c.a.nt.eig) ∧ GlobalTheory.TwInputs.EigOcc (withLoc c.a.nt.L) ({ c.a.nt.S with } : RatDat (withLoc c.a.nt.L).ntw) c.a.nt.θ c.a.nt.hL Sb c.a.nt.eig := by
  intro hN hS hL
  have h2 : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c =>
    ∀ Sb : Finset (PlE (w.D Z).host), (∀ i, Sb ⊆ (w.D Z).ntw.S0 i) → ∃ Sb' : Finset (PlE (w.D Z).host), Sb ⊆ Sb' ∧
      (∀ i, Sb' ⊆ (w.D Z).ntw.S0 i) ∧ GlobalTheory.TwInputs.Eig.Low (w.D Z) Sb' ∧
      GlobalTheory.HeightCounting.RatSide.HeckeRd t.r.z.R t.r.z.cG c.row.kKs c.row.hk Sb' c.row.hecke.hL := _root_.GlobalTheory.T.exists_superset_low_heckeRd_of_subset_S0
  have h3 : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c =>
    ∃ θ : ∀ kk : Fin 2, Multiplicative (ZMod ((w.D Z).host.g kk)) →* (↥(w.D Z).LL0)ˣ, HEq θ c.a.nt.θ ∧
      GlobalTheory.HeightCounting.RatSide.LvlPsi t.r.z.R t.r.z.F t.r.z.cG θ := _root_.GlobalTheory.T.exists_theta_heq_lvlPsi_at_members
  refine _root_.GlobalTheory.GalLoc.atMem_mono (_root_.GlobalTheory.GalLoc.atMem_and' (h2 hN hS hL) (h3 hN hS hL)) ?_
  intro K B f T w Z Wt p0 t nch n xd c hE H
  obtain ⟨H2, H3⟩ := H
  obtain ⟨e⟩ := hE
  have e' : _root_.GlobalTheory.HeightCounting.RealExpansionExtraData (D := (w.st Z).toD7) c.row t.r.z.geo xd := e
  obtain ⟨Sb, eg, hSb, heq, hAd⟩ := e'.eig
  obtain ⟨Sb', hsub, hS0, hlow, hrd⟩ := H2 Sb hSb
  obtain ⟨θ, hθ, hψ⟩ := H3
  obtain ⟨Rw0, hRw0, ⟨hpar⟩⟩ := _root_.GlobalTheory.GalLoc.EigLoc.parIn_loc_alt c.a.nt _ c.row.rep_eq
  have hT := _root_.GlobalTheory.TwInputs.Eig.eigTrue_of_read hL t.r.Y t.r.z.pins.char.base.lev hpar.T Rw0 hpar.row hAd hsub hlow
  have hO := GlobalTheory.TwInputs.Eig.eigOcc t.r.Y t.r.z.pins.char.base.lev t.r.intersectionNumber_baseChange.prim.unif t.r.z.pins.char.base.models.HW
    t.r.z.good.2 hψ hAd hsub hlow hrd
  rw [t.r.z.lev.C] at hT
  exact _root_.GlobalTheory.GalLoc.EigLoc.transport_alt c.a.nt Sb' hS0 eg heq _ c.row.S_eq _ c.row.hL_eq θ hθ.symm Rw0 hRw0 hT hO
end GlobalTheory.GalLoc.EigLoc
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigTrue_and_eigOcc_withLoc : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c =>
    ∃ Sb : Finset (PlE c.a.nt.D.host), (∀ i, Sb ⊆ (withLoc c.a.nt.L).ntw.S0 i) ∧ (∀ Rw : RowSide (withLoc c.a.nt.L), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.TwInputs.EigTrue (withLoc c.a.nt.L) (cfL c.a.nt.L c.a.nt.cf) Rw Sb c.a.nt.eig) ∧ GlobalTheory.TwInputs.EigOcc (withLoc c.a.nt.L) ({ c.a.nt.S with } : RatDat (withLoc c.a.nt.L).ntw) c.a.nt.θ c.a.nt.hL Sb c.a.nt.eig := by
  first | exact @_root_.GlobalTheory.GalLoc.EigLoc.frobenius_eigenvalues_at_place_alt | exact _root_.GlobalTheory.GalLoc.EigLoc.frobenius_eigenvalues_at_place_alt | (intros; apply _root_.GlobalTheory.GalLoc.EigLoc.frobenius_eigenvalues_at_place_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisLayerCommutesOfFull
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CommFullLayer
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal _root_.Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.IndefR.Cx _root_.Formalism.L2.Pj
  GlobalTheory.TwInputs GlobalTheory.CommFullAll
open Formalism.MainNotions.IntegralHeckeForms (HkIdx)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
section Raw
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (Rl : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) {S : RatDat D.ntw}
  (YS : NExpRealS Rl cG S) (H : NExpRealH Rl cG S YS)
end Raw
theorem commAll_and_fullAll_at_members : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c =>
    GlobalTheory.TwInputs.CommAll (w.D Z) ∧ GlobalTheory.TwInputs.FullAll (w.D Z) := by
  intro _ _ hL
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C _ _ _ =>
    ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨0, fun K _ _ _ _ _ _ => ?_⟩⟩⟩⟩⟩
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp, fun B f T _ _ _ _ => ?_⟩
  intro _ w Z Wt p0 t nch n xd c ⟨e⟩ _ _
  have hS0b : ∀ i, ∀ Q ∈ t.r.z.R.Sb, Q ∈ (w.st Z).toD7.ntw.S0 i := by
    intro i P hP
    have hA : t.r.z.R.Sb = t.r.z.R.Pg := t.r.z.pins.char.allPl
    obtain ⟨k, hk⟩ := e.ser.ex.good.Pg i ⟨0, lt_of_lt_of_le two_pos B.R.two_le_m⟩ true P
      (by rw [e.ser.ex.pin.Pg]; exact hA ▸ hP)
    exact (w.st Z).toD7.ntw.placesOver_subset_exceptional i k hk
  exact commAll_fullAll_raw (D := (w.st Z).toD7) t.r.z.R t.r.z.F t.r.z.cG c.row.nexp c.row.hecke
    (RealDat3.characterisation_of_weak t.r.z.pins.char t.exAt) t.r.intersectionNumber_baseChange.prim.unif t.r.intersectionNumber_baseChange.aux.integral e.hecke
    (fun i P P' hP hc => e.ser.ex.good.goodSetup_badPlaces_conj i P hP P' hc) (fun i => e.ser.ex.good.goodSetup_placesOverTwo_subset i) hS0b
end GlobalTheory.CommFullLayer
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commAll_fullAll_at_members_of_serN : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c =>
    GlobalTheory.TwInputs.CommAll (w.D Z) ∧ GlobalTheory.TwInputs.FullAll (w.D Z) := by
  first | exact @_root_.GlobalTheory.CommFullLayer.commAll_and_fullAll_at_members | exact _root_.GlobalTheory.CommFullLayer.commAll_and_fullAll_at_members | (intros; apply _root_.GlobalTheory.CommFullLayer.commAll_and_fullAll_at_members <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisRepsOfCgTrue
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace UpperTheory.GalS
open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.WeilDeligne
section
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
variable {N A}
end
section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}
end
end UpperTheory.GalS
namespace GlobalTheory.TripleLocal
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open GlobalTheory.RowTie (WDTie)
open GlobalTheory.Pst GlobalTheory.GalOfCusp
variable (D : D7) (T : WDTie D.nd D.naut) {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (π : D.naut.CG a) (s : ℝ)
  (r : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))
variable {D T ι π s r}
end GlobalTheory.TripleLocal
namespace GlobalTheory.HodgeOfTrue
open GlobalTheory.TripleLocal
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial _root_.Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.HeightCounting
open GlobalTheory.RowTie (WDTie)
open Matrix (GeneralLinearGroup)
section G
variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}
end G
end GlobalTheory.HodgeOfTrue
namespace GlobalTheory.GalAway
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial _root_.Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.Pst
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.HeightCounting
theorem galoisReps_of_cgTrue_alt_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, GlobalTheory.Published.AutomorphicFormsFiniteGL → _root_.UpperTheory.GalS.CuspUAlt → ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), _root_.GlobalTheory.HeightCounting.CGTrueT hL D T → UpperTheory.GalS.GaloisRepsN D := by
  intro hL hF hG D T C π hc hr l _ ι
  have := host_isCMField D.host
  have ha : 1 ≤ D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have hr' : (C.e D.R.r π).1.IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff (C.e D.R.r π).1).2 fun τ => by
    have := (D.naut.ralg_def π).1 hr τ
    rwa [C.inf] at this
  obtain ⟨r, h1, h2, h3⟩ := _root_.UpperTheory.GalS.exists_aw_alt hL hF hG D.nd.Om ι ha (C.e _ π).1 ((C.csd _ π).1 hc) hr'
  refine ⟨r, h1, h2, fun w hw => ?_⟩
  have hl : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := hw
  have k : UpperTheory.GalS.Aw (wdOf (D.nd.plOm.2 w) hl ι r) (T.e w (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2))) := by
    rw [T.tw, C.loc]
    exact h3 w hl _ _
  refine ⟨fun hg s hs => ?_, fun hu => ?_, fun hu B s hB hs => ?_⟩
  · rw [T.inePol w _ s hs, inePol_wdOf (h := D.nd.plOm.2 w) hl ι h1 hs, WD.inePol_of_mem_Ine _ hs, WD.inePol_of_mem_Ine _ hs,
      k.ine (UpperTheory.GalS.ncW_of_nc T ((UpperTheory.GalS.nc_tw _ _).2 (hg.nc T))) _ (deg_ineIncl _)]
  · rw [← weilDeligneParam_monodromy_eq_zero_iff hl ι h1]
    exact k.mono (UpperTheory.GalS.ncW_of_nc T ((UpperTheory.GalS.nc_tw _ _).2 (.of_unr hu)))
  · have hu' := (D.naut.unr_tw _ ((1 - (D.R.r : ℝ)) / 2)).2 hu
    have e := (k.eq_unr ((T.unr w _).1 hu')).symm
    rw [galPol, T.frobEig w _ hu', e]
    exact frobEig_wdOf hl ι h1 (e ▸ (T.unr w _).1 hu') hB hs
end GlobalTheory.GalAway
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTripleOfSideB
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTripleOfSideB
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.TripInhab
open GlobalTheory.Triple GlobalTheory.EigTie
open GlobalTheory.GalChar (IsGal toQ inQ)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf GalE)
open GlobalTheory.TwistAbove (twGL)
variable {D : D7} {C : CharFrame D} {art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om}
end GlobalTheory.TripInhab
namespace GlobalTheory.TripInhab
open GlobalTheory.Triple GlobalTheory.EigTie
open GlobalTheory.GalChar (IsGal toQ inQ)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf GalE)
open GlobalTheory.TwistAbove (twGL)
theorem isTriple_of_sideB_alt : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ∀ Sb : Finset (PlE D.host), (∀ i, Sb ⊆ D.ntw.S0 i) → (∀ j, 1 ≤ j → j ≤ D.R.m → (S.A j).IsKsForm) → ChiTOk D cf → GrpSide D → CharSide D cf → ValLL0 D cf → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → EigTrue D cf Rw Sb eig → EigOcc D S θ hL Sb eig → RowParam D Rw → _root_.GlobalTheory.EigTie.ResTiedAlt D Rw → _root_.GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GaloisRepsAlt D → D.nexp.sig_all → _root_.GlobalTheory.Triple.IsGaloisTriple D := by
  intro hCheb hArt D cf Rw low Pq S hL eig θ Bs Sb hSb hks hT hG hCS hV hroot hstar hET hEO hRP hRT hGR hall
  obtain ⟨art, ha⟩ := hArt D.host.E D.nd.Om
  refine ⟨cf, art, ha, fun i hi b => ?_,
    fun i _ s => GlobalTheory.T.twistTriple_eigenvector_in_good_part D cf Rw low Pq S hL eig θ Bs Sb hSb hks hEO i s, hall⟩
  obtain ⟨ρ, w, red, hind, hres⟩ := hRT.exists_reading hstar hi b
  have hc : IsChars cf art ρ := GlobalTheory.T.firstTwistCharacters_eq_ladic_characters_allReadings hCheb hArt D cf Rw low Pq S hL eig θ Bs hT hG hCS hV hroot art ha i b ρ
  refine ⟨ρ, hc, fun s hs => ?_⟩
  subst hs
  obtain ⟨hocc, hgood, hspec⟩ := Bs.rhoS i s
  obtain ⟨π, hpar⟩ := hRP _ (D.ntw.jS_range i s).1 (D.ntw.jS_range i s).2 _ hocc hgood
  obtain ⟨r, hr⟩ := hGR π hpar.1.csd hpar.1.ralg (D.ntw.l i) ρ.ι
  obtain ⟨ν, n, hν⟩ := exists_shift ha hV ρ
  have hR1 := hspec π hpar.1.csd hpar.1.ralg hpar.2 ρ.κ ρ.ι ρ.κ_alg (fun x => ρ.read x)
  have hR2 := _root_.GlobalTheory.TripInhab.isRepOf_twGL_of_isGal ha hCS ρ hr hν
  obtain ⟨A, hA⟩ := GlobalTheory.HeightCounting.FitRho.conj_of_isRepOf D ρ.ι _ _ (GlobalTheory.ChebSplitDense.chebSplit_nd hCheb D) _ _ hR1 hR2
  have hhk := GlobalTheory.TwInputs.HEig.hEig_eq_heckeVal D cf Rw low Pq S hL eig θ Bs Sb hSb hET i s ρ π hpar
  refine _root_.GlobalTheory.Triple.isTripleAt_of_conj_alt hgood hocc hpar.1 hr ⟨n, hν⟩ A (fun g => ?_) hhk hind
    (hres.2.2 _ π r hgood ⟨_, (D.ntw.jS_range i s).1, (D.ntw.jS_range i s).2, hocc⟩ hpar hr)
  have := congrArg (fun M : GL (Fin D.R.r) (Qbar (D.ntw.l i)) => (M : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.ntw.l i)))) (hA g)
  simp only [Units.val_mul, GlobalTheory.TwistAbove.twGL_val, Matrix.mul_smul, Matrix.smul_mul] at this
  rw [Units.val_mul, Units.val_mul]
  exact this
end GlobalTheory.TripInhab
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTripleOfSideBStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_eigen_export_alt : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ∀ Sb : Finset (PlE D.host), (∀ i, Sb ⊆ D.ntw.S0 i) → (∀ j, 1 ≤ j → j ≤ D.R.m → (S.A j).IsKsForm) → ChiTOk D cf → GrpSide D → CharSide D cf → ValLL0 D cf → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → EigTrue D cf Rw Sb eig → EigOcc D S θ hL Sb eig → RowParam D Rw → _root_.GlobalTheory.EigTie.ResTiedAlt D Rw → _root_.GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GaloisRepsAlt D → D.nexp.sig_all → _root_.GlobalTheory.Triple.IsGaloisTriple D := by
  first | exact @_root_.GlobalTheory.TripInhab.isTriple_of_sideB_alt | exact _root_.GlobalTheory.TripInhab.isTriple_of_sideB_alt | (intros; apply _root_.GlobalTheory.TripInhab.isTriple_of_sideB_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.GalLoc
set_option maxHeartbeats 4000000 in
theorem galLoc_triple_with_localization_alt (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {D : D7} {cf : CharFrame D} {Rw : RowSide D} {low : Finset ℕ}
    {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {S : RatDat D.ntw}
    {hl : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0}
    {θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ}
    (Bs : SideB D cf Rw low Pq S hl eig θ) (L : LocAll (lay0 D))
    (ψ : (withLoc L).nd.Loc → NC.HC D.host.E)
    (hψ : ∀ a, NC.ReadC (withLoc L).nd.plOm.1 ((withLoc L).ntw.psiL a) (NC.iotaC (withLoc L) a) (ψ a) 0)
    (Sb : Finset (PlE D.host)) (hSb : ∀ i, Sb ⊆ (withLoc L).ntw.S0 i)
    (ks : ∀ j, 1 ≤ j → j ≤ D.R.m → (S.A j).IsKsForm)
    (chiT : ChiTOk (withLoc L) (cfL L cf)) (grp : GrpSide (withLoc L)) (chr : CharSide (withLoc L) (cfL L cf))
    (val : ValLL0 (withLoc L) (cfL L cf))
    (roots : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 (withLoc L)).fieldRange)
    (hstar : ∀ x : (withLoc L).LL0, star (x : (withLoc L).what₂.LL) ∈ (withLoc L).LL0)
    (T : GlobalTheory.RowTie.WDTie (withLoc L).nd (withLoc L).naut) (cg : _root_.GlobalTheory.HeightCounting.CGTrueT hL (withLoc L) T)
    (eT : ∀ Rw' : RowSide (withLoc L), HEq Rw'.locR Rw.locR → GlobalTheory.TwInputs.EigTrue (withLoc L) (cfL L cf) Rw' Sb eig)
    (eO : GlobalTheory.TwInputs.EigOcc (withLoc L) ({ S with } : RatDat (withLoc L).ntw) θ hl Sb eig)
    (rp : ∀ Rw' : RowSide (withLoc L), HEq Rw'.locR Rw.locR → GlobalTheory.TwInputs.RowParam (withLoc L) Rw')
    (rt : ∀ Rw' : RowSide (withLoc L), HEq Rw'.locR Rw.locR → _root_.GlobalTheory.EigTie.ResTiedAlt (withLoc L) Rw')
    (nf : GlobalTheory.TwInputs.NoFormsOff (withLoc L)) (exT : NExpTied (withLoc L)) (cm : GlobalTheory.TwInputs.CommAll (withLoc L))
    (fa : GlobalTheory.TwInputs.FullAll (withLoc L)) :
    _root_.GlobalTheory.Triple.IsGaloisTriple (withLoc L) := by
  obtain ⟨Rw', hR, Bs', -⟩ := GlobalTheory.T.twist_second_step_kept_with_localisations D cf Rw low Pq S hl eig θ Bs L ψ hψ
  have hg := _root_.GlobalTheory.GalAway.galoisReps_of_cgTrue_alt_alt hL hP.what₂.fin hP.what₂.gal _ T cg
  have hm := GlobalTheory.T.stableGoodForms_meet_generic_type hP.greenC _ exT grp
  have hs := GlobalTheory.T.good_part_eigensystem_is_triple_eigensystem _ _ _ _ _ _ _ _ _ Bs' nf hm cm fa
  exact _root_.GlobalTheory.T.side_eigen_export_alt hP.what₂.cheb hP.what₂.art _ _ _ _ _ _ _ _ _ Bs' Sb hSb ks chiT grp chr val roots hstar (eT Rw' hR) eO
    (rp Rw' hR) (rt Rw' hR) hg hs
end GlobalTheory.GalLoc
namespace GlobalTheory.GalLoc
set_option maxHeartbeats 4000000 in
theorem galLoc_triple_at_place_alt (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (hS : SerN) (hL : _root_.UpperTheory.Zero.LLC.RecTExists)
    (hE : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∃ Sb : Finset (PlE c.a.nt.D.host), (∀ i, Sb ⊆ (withLoc c.a.nt.L).ntw.S0 i) ∧ (∀ Rw : RowSide (withLoc c.a.nt.L), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.TwInputs.EigTrue (withLoc c.a.nt.L) (cfL c.a.nt.L c.a.nt.cf) Rw Sb c.a.nt.eig) ∧ GlobalTheory.TwInputs.EigOcc (withLoc c.a.nt.L) ({ c.a.nt.S with } : RatDat (withLoc c.a.nt.L).ntw) c.a.nt.θ c.a.nt.hL Sb c.a.nt.eig)
    (hF : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ValLL0 (w.D Z) (TC.cf w.I w.l Z) ∧ (∀ (k : Fin 2) (z : ℂ), z ^ ((w.D Z).host.g k * ((w.D Z).host.g k - 1)) = 1 → z ∈ (embLL0 (w.D Z)).fieldRange) ∧ (∀ x : (w.D Z).LL0, star (x : (w.D Z).what₂.LL) ∈ (w.D Z).LL0))
    (hR : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.TwInputs.RowParam (w.D Z) Rw)
    (hC : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => GlobalTheory.TwInputs.CommAll (w.D Z) ∧ GlobalTheory.TwInputs.FullAll (w.D Z)) :
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => _root_.GlobalTheory.Triple.IsGaloisTriple (w.D Z) := by
  have hT := _root_.GlobalTheory.T.non_galois_residual_ties hP hL
  refine _root_.GlobalTheory.GalLoc.atMem_mono (_root_.GlobalTheory.GalLoc.atMem_and' hE (_root_.GlobalTheory.GalLoc.atMem_and' hF (_root_.GlobalTheory.GalLoc.atMem_and' hR (_root_.GlobalTheory.GalLoc.atMem_and' hC hT)))) ?_
  intro K B f T w Z Wt p0 t nch n xd c hN H
  obtain ⟨⟨Sb, hSb, eT, eO⟩, ⟨val, roots, hstar⟩, rp, ⟨cm, fa⟩, rt⟩ := H
  obtain ⟨e⟩ := hN
  have eq := c.a.nt.eq
  have pk := c.a.nt.pack
  let L := c.a.nt.L
  have hψ : ∃ ψ : (withLoc L).nd.Loc → NC.HC (withLoc L).host.E,
      ∀ a, NC.ReadC (withLoc L).nd.plOm.1 ((withLoc L).ntw.psiL a) (NC.iotaC (withLoc L) a) (ψ a) 0 := by
    have h0 : ∃ ψ : (w.D Z).nd.Loc → NC.HC (w.D Z).host.E,
        ∀ a, NC.ReadC (w.D Z).nd.plOm.1 ((w.D Z).ntw.psiL a) (NC.iotaC (w.D Z) a) (ψ a) 0 :=
      ⟨c.a.all.chiD.psi, c.a.all.chi.psi⟩
    exact eq ▸ h0
  obtain ⟨ψ, hψ⟩ := hψ
  have cast2 : ∀ P : (D : D7) → CharFrame D → Prop, P (w.D Z) (TC.cf w.I w.l Z) → P (withLoc L) (cfL L c.a.nt.cf) :=
    fun P h => cast (congrArg (fun x : (Σ (D₁ : D7) (c₁ : CharFrame D₁) (C₁ : NChoice D₁), TupTied D₁ c₁ C₁) => P x.1 x.2.1) pk) h
  have chr : Nonempty (CharSide (withLoc L) (cfL L c.a.nt.cf)) :=
    cast2 (fun D cf => Nonempty (CharSide D cf)) ⟨{ c.a.chrN with }⟩
  obtain ⟨chr⟩ := chr
  have val' : ValLL0 (withLoc L) (cfL L c.a.nt.cf) := cast2 (fun D cf => ValLL0 D cf) val
  have roots' : ∀ (k : Fin 2) (z : ℂ), z ^ ((withLoc L).host.g k * ((withLoc L).host.g k - 1)) = 1 →
      z ∈ (embLL0 (withLoc L)).fieldRange := eq ▸ roots
  have star' : ∀ x : (withLoc L).LL0, star (x : (withLoc L).what₂.LL) ∈ (withLoc L).LL0 := eq ▸ hstar
  have grp : Nonempty (GrpSide (withLoc L)) := by
    have g0 : Nonempty (GrpSide (w.D Z)) := by
      let Ty := c.a.all.types
      exact ⟨⟨Ty.tA, Ty.tκ, Ty.teichC_def, Ty.ζ, Ty.ζ_gen, Ty.O, Ty.eSer_def, Ty.kv, Ty.tg_tame, Ty.O_equiv, Ty.O_tw⟩⟩
    exact eq ▸ g0
  obtain ⟨grp⟩ := grp
  have rp' : ∀ Rw : RowSide (withLoc L), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.TwInputs.RowParam (withLoc L) Rw := eq ▸ rp
  have rt' : ∀ Rw : RowSide (withLoc L), HEq Rw.locR c.a.nt.A.row.locR → _root_.GlobalTheory.EigTie.ResTiedAlt (withLoc L) Rw := eq ▸ rt
  have cm' : GlobalTheory.TwInputs.CommAll (withLoc L) := eq ▸ cm
  have fa' : GlobalTheory.TwInputs.FullAll (withLoc L) := eq ▸ fa
  have exT : NExpTied (withLoc L) := eq ▸ c.a.all.exp
  have nf : GlobalTheory.TwInputs.NoFormsOff (withLoc L) := by
    have h0 : GlobalTheory.TwInputs.NoFormsOff (w.D Z) := fun i j hj b => e.ser.off i j b fun h => hj (Finset.mem_Icc.2 h)
    exact eq ▸ h0
  rw [eq]
  exact _root_.GlobalTheory.GalLoc.galLoc_triple_with_localization_alt hP hL c.a.nt.Bs L ψ hψ Sb hSb c.a.ratIn.ks c.a.nt.A.chiT grp chr val' roots' star' { c.a.nt.A.wdT with } { c.a.nt.cg with }
    eT eO rp' rt' nf exT cm' fa'
end GlobalTheory.GalLoc
namespace GlobalTheory.GalLoc
set_option maxHeartbeats 4000000 in
theorem galois_side_at_place_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c =>
    ∃ G : _root_.GlobalTheory.TwInputs.GalSideAlt (w.st Z).toD7, G.cf = (TC.cf w.I w.l Z) ∧ G.lam.C = (TC.cf w.I w.l Z) ∧
      Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL _ G.wd) := by
  intro hP hS hL
  have htr : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => _root_.GlobalTheory.Triple.IsGaloisTriple (w.D Z) :=
    _root_.GlobalTheory.GalLoc.galLoc_triple_at_place_alt hP hS hL (_root_.GlobalTheory.T.eigTrue_and_eigOcc_withLoc hP hS hL) (_root_.GlobalTheory.T.valLL0_roots_of_unity_mem_star_closed_at_members hP hS hL) (_root_.GlobalTheory.T.local_param_at_member_of_serN hP hS hL) (_root_.GlobalTheory.T.commAll_fullAll_at_members_of_serN hP hS hL)
  refine (GlobalTheory.T.eventually_sizes_congruences_hostFacts_columnChoices.inter htr).imp fun K _ _ _ _ H => ?_
  refine (H.1.inter H.2).imp fun B f T _ H => ?_
  intro hK w Z Wt p0 t nch n xd c hE hX hC
  obtain ⟨e⟩ := hE
  have hs := H.1 hK T w Z
  exact _root_.GlobalTheory.TwInputs.JoinModel.exists_galSide_of_rank_ge_hundred e (H.2 hK w Z Wt p0 t nch n xd c ⟨e⟩ hX hC) hs.1 hs.2.1
end GlobalTheory.GalLoc
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galSide_cf_eq_cgTrue_at_members : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∃ G : _root_.GlobalTheory.TwInputs.GalSideAlt (w.st Z).toD7, G.cf = (TC.cf w.I w.l Z) ∧ G.lam.C = (TC.cf w.I w.l Z) ∧ Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL _ G.wd) := by
  first | exact @_root_.GlobalTheory.GalLoc.galois_side_at_place_alt | exact _root_.GlobalTheory.GalLoc.galois_side_at_place_alt | (intros; apply _root_.GlobalTheory.GalLoc.galois_side_at_place_alt <;> assumption)
end
end
