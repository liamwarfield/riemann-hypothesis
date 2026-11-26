module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlIsRecrecLaws
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MMvDmvAll

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTrueReading
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadAtExistsM
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TrueReading
open GlobalTheory.WeilDeligne GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem readAt_exists_m_alt (hAF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7)
    (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (hR : ∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) (i : D.nd.Loc)
    (s : SplitPlace D.host.E) :
    ∃ X : ReadAt P.T i s.w, X.rc = _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D s.w ∧
      (∀ σ, D.what₂.isot (D.nd.j i) σ ≠ ⊥ → IsLocS (P.rep σ).S s (X.row σ).toIrrRep) ∧
      (∀ Q, IsLocS (n := D.R.nV) (P.H.av.S i Q) s (X.rep Q).toIrrRep) ∧
      (∀ j : Fin D.R.m, j.1 + 1 = D.nd.j i → IsComp (P.tp.tup (D.nd.mu i) j) s.w X.mu) ∧
      IsComp P.cf.eta s.w X.eta := by
  classical
  haveI := GlobalTheory.CuspRep.host_isCMField D.host
  have HR := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 s.w)
  have hlaws : _root_.UpperTheory.One.M.RecLawsH (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D s.w) := HR.recLaws
  have hrow : ∀ σ, ∃ τ : Irr (s.w.adicCompletion D.host.E) D.R.r,
      D.what₂.isot (D.nd.j i) σ ≠ ⊥ → IsLocS (P.rep σ).S s τ.toIrrRep := by
    intro σ
    by_cases hσ : D.what₂.isot (D.nd.j i) σ ≠ ⊥
    · obtain ⟨τ, hτ⟩ := GlobalTheory.T.isotypic_row_local_split_exists D P.rep (D.nd.j i) (hR i).some σ hσ s
      exact ⟨Irr.ofIrrRep τ, fun _ => hτ⟩
    · exact ⟨default, fun h => absurd h hσ⟩
  choose row hrow using hrow
  have hrep : ∀ Q : D.naut.AV i, ∃ τ : Irr (s.w.adicCompletion D.host.E) (D.R.r + D.R.t),
      IsLocS (n := D.R.nV) (P.H.av.S i Q) s τ.toIrrRep := by
    intro Q
    obtain ⟨τ, hτ, -⟩ := GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class D.host.E D.R.nV (P.H.av.rep i Q) s
    exact ⟨Irr.ofIrrRep τ, hτ⟩
  choose rep hrep using hrep
  have hjr := D.nd.j_range i
  let j0 : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hj0 : j0.1 + 1 = D.nd.j i := by simp only [j0]; omega
  have hmuC := P.chr.muC i j0 hj0
  obtain ⟨μ, hμ, -, hμu⟩ := GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary D.host.E (P.tp.tup (D.nd.mu i) j0) s.w
  have hμU : GlobalTheory.SmGL.IsUnitaryChar μ := hμu (hmuC ▸ (P.chr.e1 (D.naut.muC i)).2)
  have hμP : IsComp (P.chr.e1 (D.naut.muC i)).1 s.w μ := hmuC ▸ hμ
  have eμ := _root_.GlobalTheory.T.T_e_locG_eq_rcAt_ofDet hAF hL D P (D.naut.muC i) s.w μ hμP
  obtain ⟨η, hη, -, -⟩ := GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary D.host.E P.cf.eta⁻¹ s.w
  have hηP : IsComp (P.chr.e1 D.naut.etaTinv).1 s.w η := P.chr.etaTinv ▸ hη
  have eη := _root_.GlobalTheory.T.T_e_locG_eq_rcAt_ofDet hAF hL D P D.naut.etaTinv s.w η hηP
  have hun : GlobalTheory.SplitWeil.IsUnram η := by
    have := (hlaws.sph 1 (Irr.ofDet 1 η hηP.1)).1
      (by rw [← eη]; exact (P.T.unr s.w _).1 (D.naut.etaTinv_def s.w).1)
    intro x hx
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 this
    have hI : (fun _ : Fin 1 => x) ∈ torusO (s.w.adicCompletion D.host.E) (Fin 1) := fun _ => hx
    have h2 := hv ⟨_, iwahori_le_KO _ _ (diagT_mem_iwahori hI)⟩
    have h3 : Matrix.GeneralLinearGroup.det (diagT (s.w.adicCompletion D.host.E) (Fin 1) fun _ => x) = x := by
      ext; simp [val_diagT]
    have h4 : (η x : ℂ) * (show ℂ from v) = (show ℂ from v) := by
      have h5 : detRep (Fin 1) η (diagT (s.w.adicCompletion D.host.E) (Fin 1) fun _ => x) v = (show ℂ from v) := by
        exact h2.trans (by simp)
      have h6 := (ofChar_apply (detChar (Fin 1) η) (diagT (s.w.adicCompletion D.host.E) (Fin 1) fun _ => x)
        (show ℂ from v)).symm.trans h5
      rw [detChar_apply, h3] at h6
      exact h6
    ext
    exact (mul_eq_right₀ hv0).1 h4
  refine ⟨⟨_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D s.w, row, rep, μ, η⁻¹, ⟨hμ.1, hμU⟩, ⟨hηP.1.inv, fun x hx => by simp [hun x hx]⟩,
    fun σ hσ => (P.row i).1 σ s _ (hrow σ hσ), fun Q => ?_, fun c hc => ?_, fun c hc => ?_⟩,
    rfl, hrow, hrep, fun j hj => ?_, ⟨hη.1.inv, fun x => ?_⟩⟩
  · rw [D.nbc.embAV_loc, P.H.emb]
    exact P.au _ _ _ _ s _ (hrep Q)
  · rw [eμ]; exact (_root_.UpperTheory.One.M.RecLawsH.isoMp hlaws 1 c (Irr.ofDet 1 μ hμP.1) hc).symm
  · rw [inv_inv] at hc
    rw [eη]; exact (_root_.UpperTheory.One.M.RecLawsH.isoMp hlaws 1 c (Irr.ofDet 1 η hηP.1) hc).symm
  · have : j = j0 := Fin.ext (by simp only [j0]; omega)
    subst this
    exact hμ
  · rw [MonoidHom.inv_apply, hη.2 x]
    exact inv_inv _
end GlobalTheory.TrueReading
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTrueReading
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TrueReading
open GlobalTheory.WeilDeligne GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem exists_true_reading_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D),
    (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) →
    ∃ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S ∧ _root_.GlobalTheory.SplitRead.LawsAlt S ∧ SuppLaws S := by
  intro hAF hL D P hR
  classical
  haveI := GlobalTheory.CuspRep.host_isCMField D.host
  have hex : ∀ w : PlE D.host, IsSplitPl D.host w → ∃ s : SplitPlace D.host.E, s.w = w := by
    intro w hw
    obtain ⟨w', hw'⟩ := GlobalTheory.ToricFactor.exists_isConjPl w
    obtain ⟨s, -, hs, -⟩ :=
      GlobalTheory.SplitConjPlace.splitEx_all D w' (GlobalTheory.ConjugatePlaceSplitting.isSplitPl_of_isConjPl hw hw')
    exact ⟨s, GlobalTheory.ToricFactor.isConjPl_unique hs (GlobalTheory.ToricFactor.isConjPl_symm hw')⟩
  have key : ∀ i (w : PlE D.host), IsSplitPl D.host w → ∃ X : ReadAt P.T i w, X.rc = _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D w ∧
      ∀ (s : SplitPlace D.host.E), s.w = w → ∀ Y : ReadAt P.T i s.w, HEq Y X →
        (∀ σ, D.what₂.isot (D.nd.j i) σ ≠ ⊥ → IsLocS (P.rep σ).S s (Y.row σ).toIrrRep) ∧
        (∀ Q, IsLocS (n := D.R.nV) (P.H.av.S i Q) s (Y.rep Q).toIrrRep) ∧
        (∀ j : Fin D.R.m, j.1 + 1 = D.nd.j i → IsComp (P.tp.tup (D.nd.mu i) j) s.w Y.mu) ∧
        IsComp P.cf.eta s.w Y.eta := by
    intro i w hw
    obtain ⟨s₀, rfl⟩ := hex w hw
    obtain ⟨X, h1, h2⟩ := _root_.GlobalTheory.TrueReading.readAt_exists_m_alt hAF hL D P hR i s₀
    refine ⟨X, h1, fun s hs Y hY => ?_⟩
    obtain rfl := GlobalTheory.SplitUniq.splitPlace_eq_of_w_eq D.host.E s s₀ hs
    obtain rfl := eq_of_heq hY
    exact h2
  choose S hS using key
  refine ⟨S, ⟨fun i w hw => (hS i w hw).1, fun i s hw σ hσ => ((hS i s.w hw).2 s rfl _ HEq.rfl).1 σ hσ,
    fun i s hw Q => ((hS i s.w hw).2 s rfl _ HEq.rfl).2.1 Q,
    fun i w hw j hj => ?_, fun i w hw => ?_⟩, fun i w hw => ?_, fun i w hw => ?_⟩
  · obtain ⟨s, rfl⟩ := hex w hw
    exact ((hS i s.w hw).2 s rfl _ HEq.rfl).2.2.1 j hj
  · obtain ⟨s, rfl⟩ := hex w hw
    exact ((hS i s.w hw).2 s rfl _ HEq.rfl).2.2.2
  · rw [(hS i w hw).1]
    exact (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w)).recLaws
  · rw [(hS i w hw).1]
    exact _root_.UpperTheory.Zero.LLC.IsRecT.recSupp (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w))
end GlobalTheory.TrueReading
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTrueReadingStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_true_reading_with_laws_suppLaws : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → ∃ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S ∧ _root_.GlobalTheory.SplitRead.LawsAlt S ∧ SuppLaws S := by
  first | exact @_root_.GlobalTheory.TrueReading.exists_true_reading_alt | exact _root_.GlobalTheory.TrueReading.exists_true_reading_alt | (intros; apply _root_.GlobalTheory.TrueReading.exists_true_reading_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalExOfCgTrue
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal _root_.Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.WeilDeligne NumberField IsDedekindDomain Polynomial
theorem galEx_of_cgTrue_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, GlobalTheory.Published.AutomorphicFormsFiniteGL →
    _root_.UpperTheory.GalS.CuspUAlt → ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut),
      Nonempty (_root_.GlobalTheory.HeightCounting.CGTrueT hL D T) → GalEx D :=
  fun hL hF hG _ _ ⟨C⟩ => C.galEx hL hF hG
end GlobalTheory.HeightCounting
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtSame
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
def AtSameAltAlt {cf : CharFrame D} {C : NChoice D} {tp : TupTied D cf C} (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D cf C tp) {D' : D7} {cf' : CharFrame D'}
    {C' : NChoice D'} {tp' : TupTied D' cf' C'} (a' : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL D' cf' C' tp') : Prop :=
  HEq a'.all ((_root_.UpperTheory.One.M.mvAll_alt trivial) m a.all) ∧ HEq a'.Pq a.Pq ∧ HEq (ratL a'.nt.L a'.nt.S) (ratL a.nt.L a.nt.S) ∧ HEq a'.nt.hL a.nt.hL ∧
    HEq a'.nt.rep a.nt.rep ∧ HEq a'.nt.eig a.nt.eig ∧ (_root_.GlobalTheory.LayerMove.InnerAlt a.nt → _root_.GlobalTheory.LayerMove.InnerAlt a'.nt)
section
end
end GlobalTheory.LayerMove
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RestageCopy
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RestageCopy
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem.R3.Tr
theorem restage_copy_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) (N : TwNew (Dof x)), ∃ (x' : St P) (l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x'), x'.o = oTw x N ∧ HEq x'.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x.o.Z) (oTw x N).Z x.m.z.R.toRealDat.toLevCh) ∧ HEq l'.a.A.row (N.row l.a.A.row) ∧ HEq l'.Pq l.Pq ∧ HEq l'.rat.S (N.rat l.rat.S) ∧ HEq l'.rat.In.Sb l.rat.In.Sb ∧ HEq l'.rat.In.hL l.rat.In.hL ∧ HEq l'.rat.In.eig l.rat.In.eig ∧ HEq l'.rat.In.θ l.rat.In.θ := by
  intro hL K B f T w P x l N
  obtain ⟨m, hm, hc, hh⟩ := GlobalTheory.T.exists_movedData_laterStagesWithNewTwist x N
  obtain ⟨r, hp, hrep, hj, he⟩ := GlobalTheory.T.exists_normalisedReading_transported_newTwist x N m hm hc hh
  obtain ⟨l', h1, h2, h3, h4, h5, h6, h7⟩ := _root_.GlobalTheory.T.read_package_twist_heq_alt hL x l N m hm hc hh r hp hrep hj he
  refine ⟨stTw x N m hc hh r hp, l', rfl, ?_, h1, h2, h3, h4, h5, h6, h7⟩
  show HEq m.z.R.toRealDat.toLevCh _
  rw [hm]
  exact (by with_unfolding_all exact ((HEq.refl (datTw x N).R.toRealDat.toLevCh) :))
end GlobalTheory.HeightCounting.Up
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RestageCopyStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_state_transport_heq' : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) (N : TwNew (Dof x)), ∃ (x' : St P) (l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x'), x'.o = oTw x N ∧ HEq x'.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x.o.Z) (oTw x N).Z x.m.z.R.toRealDat.toLevCh) ∧ HEq l'.a.A.row (N.row l.a.A.row) ∧ HEq l'.Pq l.Pq ∧ HEq l'.rat.S (N.rat l.rat.S) ∧ HEq l'.rat.In.Sb l.rat.In.Sb ∧ HEq l'.rat.In.hL l.rat.In.hL ∧ HEq l'.rat.In.eig l.rat.In.eig ∧ HEq l'.rat.In.θ l.rat.In.θ := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.restage_copy_alt | exact _root_.GlobalTheory.HeightCounting.Up.restage_copy_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.restage_copy_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InertialTypeOfTameM
section -- merged from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.PotentialCrystallinity.InertialTypeOfTameM
noncomputable section

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.SplitRead GlobalTheory.CuspRep in
theorem UpperTheory.One.M.goodI_of_sph {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (π : Irr k n) (h : IsSpherical π.π) : UpperTheory.One.M.GoodI π :=
  (GlobalTheory.SphSupport.toral_and_good_of_isSpherical UpperTheory.Zero.LLC.Pr.bz k (cls (⟨π.V, π.π, π.smooth, π.irr⟩ : IrrRep (GL (Fin n) k)))
    (fixed_ne_bot_of_equiv (IrrRep.nonempty_equiv_rep (⟨π.V, π.π, π.smooth, π.irr⟩ : IrrRep (GL (Fin n) k))).some.symm h)).2

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.TameType

theorem inertialType_of_tame_m : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (T : WDTie N A) (S : Reading T) (i : N.Loc) (w : PlE H) (hw : IsSplitPl H w), TameSplitAll H.E → Laws S → TypeTame S i w hw → (∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol (A.locG (A.muC i) w) σ = X - C (iotaO N A i (chi1 N i σ))) → ∀ P : A.AV i, A.mono0 (A.locV i P w) ∧ ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol (A.locV i P w) σ = (X - 1) ^ R.r * (X - C (iotaO N A i (chi1 N i σ))) ^ R.t := by
  intro R H what₂ N A T S i w hw hTS hL hT hmu P
  obtain ⟨htame, hram, hv⟩ := hT
  obtain ⟨v, hv0, hv⟩ := hv P
  have L := hL i w hw
  have hs := (S i w hw).mu_ok.1
  obtain ⟨π₁, π₂, h1, h2, he⟩ := hTS w _ _ _ _ v hs htame hram hv0 hv
  let c : Irr (w.adicCompletion H.E) 1 :=
    { V := ℂ, π := detRep (Fin 1) (S i w hw).mu, smooth := (isSmooth_ofChar_iff _).2 hs.detChar,
      irr := isIrreducible_ofChar _ }
  let τ : Irr (w.adicCompletion H.E) R.t :=
    { V := π₂.V, π := GlobalTheory.SmGL.twist π₂.π (detChar (Fin R.t) (S i w hw).mu), smooth := isSmooth_twist π₂.smooth hs.detChar,
      irr := irreducible_twist π₂.irr _ }
  have hc : Nonempty (c.π.Equiv (detRep (Fin 1) (S i w hw).mu)) := ⟨Representation.Equiv.refl _⟩
  have e1 := L.prod _ _ π₁ τ _ he
  have e2 := UpperTheory.One.M.Old.rlTwist L _ _ c π₂ τ (UpperTheory.One.M.goodI_of_sph π₂ h2) hc ⟨Representation.Equiv.refl _⟩
  have u1 := (L.sph _ π₁).2 h1
  have u2 := (L.sph _ π₂).2 h2
  have eV := (S i w hw).locV P
  have eM := (S i w hw).locMu c hc
  rw [e1, e2] at eV
  refine ⟨?_, fun σ hσ => ?_⟩
  · rw [T.mono0, eV, WeilDeligne.WD.monomial_sum_iff, WeilDeligne.WD.monomial_char_iff _ _ (L.dim 1 c)]
    exact ⟨weilDeligneParameter_monodromy_zero_of_unramified u1, weilDeligneParameter_monodromy_zero_of_unramified u2⟩
  · have hz := hmu σ hσ
    rw [T.inePol _ _ _ hσ, eM] at hz
    rw [T.inePol _ _ _ hσ, eV, WeilDeligne.WD.inePol_sum, inePol_of_unr u1 hσ,
      inePol_char_of_unr u2 (L.dim 1 c) hσ hz, L.dim, L.dim]

end GlobalTheory.TameType
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf

namespace GlobalTheory.DepthZeroAssembly
open GlobalTheory.WeilDeligne (WD)
open GlobalTheory.SplitRead.BlockParam (twistIrr)

theorem locDZ_of_split_reg_m : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7), SplitLoc hL D → RegLoc hL D → LocDZ hL D := by
  intro hL D hS hR k v χ hχ u π ρ f ht hlab hser hsq hnr hx
  obtain ⟨π₁, π₂, hsph, e, y, hy1, hy2⟩ := hS k v χ hχ u π ρ f ht hlab hser hnr hx
  obtain ⟨hm1, hl1⟩ := hR k v π₁ ρ f hser hsq ⟨y, hy1, hy2⟩
  have L : RecLaws (rcAt hL D (D.naut.plGw k v)) :=
    (GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 (D.naut.plGw k v))).recLaws
  have e' : Nonempty (π.π.Equiv (GlobalTheory.SmGL.prod₂ π₁.π (twistIrr π₂ χ hχ).π)) := e
  have e1 := L.prod D.R.r D.R.t π₁ (twistIrr π₂ χ hχ) π e'
  have e2 := UpperTheory.One.M.Old.rlTwist L D.R.t χ (Irr.ofDet 1 χ hχ) π₂ (twistIrr π₂ χ hχ) (UpperTheory.One.M.goodI_of_sph π₂ hsph) ⟨.refl _⟩ ⟨.refl _⟩
  have hu := (L.sph _ π₂).2 hsph
  refine ⟨?_, ?_⟩
  · rw [e1, WD.monomial_sum_iff, e2, WD.monomial_char_iff _ _ (L.dim _ _)]
    exact ⟨hm1, WD.unr_mono0 _ hu⟩
  · unfold labAt at hl1 hlab ⊢
    rw [e1, WD.lab_lpSum, e2, lab_lpChar_of_unr _ _ _ _ hu (L.dim _ _) u hlab, hl1, L.dim]

end GlobalTheory.DepthZeroAssembly
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
namespace GlobalTheory.TameType
theorem inertialType_of_tame_m_alt : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (T : WDTie N A) (S : Reading T) (i : N.Loc) (w : PlE H) (hw : IsSplitPl H w), TameSplitAll H.E → _root_.GlobalTheory.SplitRead.LawsAlt S → TypeTame S i w hw → (∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol (A.locG (A.muC i) w) σ = X - C (iotaO N A i (chi1 N i σ))) → ∀ P : A.AV i, A.mono0 (A.locV i P w) ∧ ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol (A.locV i P w) σ = (X - 1) ^ R.r * (X - C (iotaO N A i (chi1 N i σ))) ^ R.t := by
  intro R H what₂ N A T S i w hw hTS hL hT hmu P
  obtain ⟨htame, hram, hv⟩ := hT
  obtain ⟨v, hv0, hv⟩ := hv P
  have L := hL i w hw
  have hs := (S i w hw).mu_ok.1
  obtain ⟨π₁, π₂, h1, h2, he⟩ := hTS w _ _ _ _ v hs htame hram hv0 hv
  let c : Irr (w.adicCompletion H.E) 1 :=
    { V := ℂ, π := detRep (Fin 1) (S i w hw).mu, smooth := (isSmooth_ofChar_iff _).2 hs.detChar,
      irr := isIrreducible_ofChar _ }
  let τ : Irr (w.adicCompletion H.E) R.t :=
    { V := π₂.V, π := GlobalTheory.SmGL.twist π₂.π (detChar (Fin R.t) (S i w hw).mu), smooth := isSmooth_twist π₂.smooth hs.detChar,
      irr := irreducible_twist π₂.irr _ }
  have hc : Nonempty (c.π.Equiv (detRep (Fin 1) (S i w hw).mu)) := ⟨Representation.Equiv.refl _⟩
  have e1 := L.prod _ _ π₁ τ _ he
  have e2 := _root_.UpperTheory.One.M.RecLawsH.twist L _ _ c π₂ τ (UpperTheory.One.M.goodI_of_sph π₂ h2) hc ⟨Representation.Equiv.refl _⟩
  have u1 := (L.sph _ π₁).2 h1
  have u2 := (L.sph _ π₂).2 h2
  have eV := (S i w hw).locV P
  have eM := (S i w hw).locMu c hc
  rw [e1, e2] at eV
  refine ⟨?_, fun σ hσ => ?_⟩
  · rw [T.mono0, eV, WeilDeligne.WD.monomial_sum_iff, WeilDeligne.WD.monomial_char_iff _ _ (L.dim 1 c)]
    exact ⟨weilDeligneParameter_monodromy_zero_of_unramified u1, weilDeligneParameter_monodromy_zero_of_unramified u2⟩
  · have hz := hmu σ hσ
    rw [T.inePol _ _ _ hσ, eM] at hz
    rw [T.inePol _ _ _ hσ, eV, WeilDeligne.WD.inePol_sum, inePol_of_unr u1 hσ,
      inePol_char_of_unr u2 (L.dim 1 c) hσ hz, L.dim, L.dim]
end GlobalTheory.TameType
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
namespace GlobalTheory.DepthZeroAssembly
open GlobalTheory.WeilDeligne (WD)
open GlobalTheory.SplitRead.BlockParam (twistIrr)
theorem locDZ_of_split_reg_m_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7), _root_.GlobalTheory.PendOf.SplitLocalCondition hL D → _root_.GlobalTheory.PendOf.RegularLocalCondition hL D → _root_.GlobalTheory.PendOf.LocalDatumCondition hL D := by
  intro hL D hS hR k v χ hχ u π ρ f ht hlab hser hsq hnr hx
  obtain ⟨π₁, π₂, hsph, e, y, hy1, hy2⟩ := hS k v χ hχ u π ρ f ht hlab hser hnr hx
  obtain ⟨hm1, hl1⟩ := hR k v π₁ ρ f hser hsq ⟨y, hy1, hy2⟩
  have L : _root_.UpperTheory.One.M.RecLawsH (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v)) :=
    (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))).recLaws
  have e' : Nonempty (π.π.Equiv (GlobalTheory.SmGL.prod₂ π₁.π (twistIrr π₂ χ hχ).π)) := e
  have e1 := L.prod D.R.r D.R.t π₁ (twistIrr π₂ χ hχ) π e'
  have e2 := _root_.UpperTheory.One.M.RecLawsH.twist L D.R.t χ (Irr.ofDet 1 χ hχ) π₂ (twistIrr π₂ χ hχ) (UpperTheory.One.M.goodI_of_sph π₂ hsph) ⟨.refl _⟩ ⟨.refl _⟩
  have hu := (L.sph _ π₂).2 hsph
  refine ⟨?_, ?_⟩
  · rw [e1, WD.monomial_sum_iff, e2, WD.monomial_char_iff _ _ (L.dim _ _)]
    exact ⟨hm1, WD.unr_mono0 _ hu⟩
  · unfold _root_.GlobalTheory.PendOf.localLabelPolynomial at hl1 hlab ⊢
    rw [e1, WD.lab_lpSum, e2, lab_lpChar_of_unr _ _ _ _ hu (L.dim _ _) u hlab, hl1, L.dim]
end GlobalTheory.DepthZeroAssembly
end
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RayPrimeHostIntegral
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FixedFieldIsStableUnderStar
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.HeightCounting.Up
theorem fixedField_isStable_under_star_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ∀ y : (Dof x).LL0, star (y : (Dof x).what₂.LL) ∈ (Dof x).LL0 := by
  intro _
  refine StepW.of_all fun K B f T w _ _ _ P x y => ?_
  exact (IntermediateField.normal_iff_forall_map_le.1 B.coeffGaloisSubfield_isGalois.to_normal
    (starRingEnd (Dof x).what₂.LL).toRatAlgHom) ⟨_, y.2, rfl⟩
end GlobalTheory.HeightCounting.Up
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.star_mem_LL0 : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ∀ y : (Dof x).LL0, star (y : (Dof x).what₂.LL) ∈ (Dof x).LL0 := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.fixedField_isStable_under_star_alt | exact _root_.GlobalTheory.HeightCounting.Up.fixedField_isStable_under_star_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.fixedField_isStable_under_star_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GlobalNormConditionAtMember
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.HeightCounting.Up
theorem globalNorm_all_stages_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ∀ i, ((Dof x).host.g i).Prime ∧ ∃ π : 𝓞 (Dof x).host.E, (π : (Dof x).host.E) ∈ (Dof x).host.K ∧ (π : (Dof x).host.E) * (Dof x).host.conj (π : (Dof x).host.E) = ((Dof x).host.g i : (Dof x).host.E) ∧ (π - 1) ∈ Ideal.span {(((Dof x).host.QS * (Dof x).host.q * (Dof x).host.d : ℕ) : 𝓞 (Dof x).host.E)} := by
  intro _
  have aux : ∀ (K : Ctx) (Q : Pre), K.Over Q → ∀ i, (Q.host.g i).Prime ∧ ∃ π : 𝓞 Q.host.E, (π : Q.host.E) ∈ Q.host.K ∧
      (π : Q.host.E) * Q.host.conj (π : Q.host.E) = (Q.host.g i : Q.host.E) ∧
      (π - 1) ∈ Ideal.span {((Q.host.QS * Q.host.q * Q.host.d : ℕ) : 𝓞 Q.host.E)} := by
    rintro K Q ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ i
    exact ⟨K.P.H.g_prime i, K.ok.gnorm i⟩
  refine StepW.of_all fun K B f T w hO _ _ => ?_
  intro P x i
  exact aux K B.toPre hO i
end GlobalTheory.HeightCounting.Up
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_norm_element_congruent_one_at_member : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ∀ i, ((Dof x).host.g i).Prime ∧ ∃ π : 𝓞 (Dof x).host.E, (π : (Dof x).host.E) ∈ (Dof x).host.K ∧ (π : (Dof x).host.E) * (Dof x).host.conj (π : (Dof x).host.E) = ((Dof x).host.g i : (Dof x).host.E) ∧ (π - 1) ∈ Ideal.span {(((Dof x).host.QS * (Dof x).host.q * (Dof x).host.d : ℕ) : 𝓞 (Dof x).host.E)} := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.globalNorm_all_stages_alt | exact _root_.GlobalTheory.HeightCounting.Up.globalNorm_all_stages_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.globalNorm_all_stages_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigenExponentIsIntegralAllStages
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.HeightCounting.Up
theorem eigenExponent_isIntegral_all_stages_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ∀ (j : Fin (Dof x).R.m) (g : ↥((Dof x).R.Psi)), ∃ z : ℤ, eExp (Dof x) j g = (z : ℚ) := by
  intro _
  refine StepW.of_all fun K B f T w _ _ _ P x j g => ?_
  exact ((Dof x).hc ((Dof x).eTau.symm g)).e_int j
end GlobalTheory.HeightCounting.Up
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eExp_integral_at_member : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ∀ (j : Fin (Dof x).R.m) (g : ↥((Dof x).R.Psi)), ∃ z : ℤ, eExp (Dof x) j g = (z : ℚ) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.eigenExponent_isIntegral_all_stages_alt | exact _root_.GlobalTheory.HeightCounting.Up.eigenExponent_isIntegral_all_stages_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.eigenExponent_isIntegral_all_stages_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MatrixRowsIntegralAtMember
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.HeightCounting.Up
theorem rows_mem_ringOfIntegers_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => Function.Injective (Dof x).what₂.OtoLL ∧
    ∃ F : Subfield (Dof x).what₂.LL, ∀ y, y ∈ (Dof x).what₂.OtoLL.range ↔ y ∈ F ∧ IsIntegral ℤ y := by
  intro _
  refine Step.of_all fun K B f T _ _ _ _ w _ P x => ?_
  refine ⟨B.OtoLL_injective, B.Ks.toSubfield, fun y => ?_⟩
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨((show B.O from z) : B.Ks).2, B.O_int z⟩
  · rintro ⟨hy, hi⟩
    exact B.O_full y hy hi
end GlobalTheory.HeightCounting.Up
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integer_embedding_injective_range_integral_of_inputs : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => Function.Injective (Dof x).what₂.OtoLL ∧ ∃ F : Subfield (Dof x).what₂.LL, ∀ y, y ∈ (Dof x).what₂.OtoLL.range ↔ y ∈ F ∧ IsIntegral ℤ y := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.rows_mem_ringOfIntegers_alt | exact _root_.GlobalTheory.HeightCounting.Up.rows_mem_ringOfIntegers_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.rows_mem_ringOfIntegers_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitsAtAllStages
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.HeightCounting.Up
theorem splits_at_all_stages_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ∀ v : HeightOneSpectrum (𝓞 (Dof x).host.E), v ∈ placesOver (Dof x).host.E (Dof x).host.pde ∨ v ∈ placesOver (Dof x).host.E (Dof x).host.pde' → IsSplitPl (Dof x).host v := by
  intro _
  refine StepW.of_all fun K B f T w _ _ _ P x v hv => ?_
  have hc : ∀ p ∈ (Dof x).host.levelPrimes, p.Prime ∧ p % ((Dof x).host.QS * (Dof x).host.q * (Dof x).host.d) = 1 :=
    (w.st x.o.Z).B.level_cond
  rcases hv with hv | hv
  · exact isSplitPl_of_mem_levelPrimes _ hc (Dof x).host.pde_level.1 v hv
  · exact isSplitPl_of_mem_levelPrimes _ hc (Dof x).host.pde_level.2 v hv
end GlobalTheory.HeightCounting.Up
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.is_split_pl_of_places_over_pde : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ∀ v : HeightOneSpectrum (𝓞 (Dof x).host.E), v ∈ placesOver (Dof x).host.E (Dof x).host.pde ∨ v ∈ placesOver (Dof x).host.E (Dof x).host.pde' → IsSplitPl (Dof x).host v := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.splits_at_all_stages_alt | exact _root_.GlobalTheory.HeightCounting.Up.splits_at_all_stages_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.splits_at_all_stages_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.ElemAtStates
theorem elem_all_alt_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => Elem (Dof x) ∧ ValLL0 (Dof x) (cfOf x) ∧ (Function.Injective (Dof x).what₂.OtoLL ∧ ∃ F : Subfield (Dof x).what₂.LL, ∀ y, y ∈ (Dof x).what₂.OtoLL.range ↔ y ∈ F ∧ IsIntegral ℤ y) ∧ ∃ (h : HostTied (Dof x)) (jE : (Dof x).host.E →+* Qb), (∀ y, jE y = h.fr.j y) ∧ ∀ k, IsRayPrime (GlobalTheory.HeightCounting.KQbar (Dof x) jE) ((Dof x).host.QS * (Dof x).host.q * (Dof x).host.d) ((Dof x).host.g k) := by
  intro hP
  have h := allSt_and (allSt_and (allSt_and (_root_.GlobalTheory.T.star_mem_LL0 hP) (_root_.GlobalTheory.T.eExp_integral_at_member hP)) (allSt_and (_root_.GlobalTheory.T.is_split_pl_of_places_over_pde hP) (_root_.GlobalTheory.T.valLL0_cfOf_at_states hP)))
    (allSt_and (_root_.GlobalTheory.T.integer_embedding_injective_range_integral_of_inputs hP) (_root_.GlobalTheory.T.exists_norm_element_congruent_one_at_member hP))
  refine allSt_mono h ?_
  rintro K B f T w P x ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5, h6⟩
  refine ⟨⟨h1, h2, h3⟩, h4, h5, ?_⟩
  obtain ⟨hT⟩ := HostTied.exists (Dof x)
  exact ⟨hT, hT.fr.j.toRingHom, fun y => rfl, fun k => GlobalTheory.T.isRayPrime_of_norm_integer_congruent_one (Dof x) k _ (h6 k).1 (h6 k).2⟩
end GlobalTheory.ElemAtStates
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRayPrime_g_and_integral_range : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => Elem (Dof x) ∧ ValLL0 (Dof x) (cfOf x) ∧ (Function.Injective (Dof x).what₂.OtoLL ∧ ∃ F : Subfield (Dof x).what₂.LL, ∀ y, y ∈ (Dof x).what₂.OtoLL.range ↔ y ∈ F ∧ IsIntegral ℤ y) ∧ ∃ (h : HostTied (Dof x)) (jE : (Dof x).host.E →+* Qb), (∀ y, jE y = h.fr.j y) ∧ ∀ k, IsRayPrime (GlobalTheory.HeightCounting.KQbar (Dof x) jE) ((Dof x).host.QS * (Dof x).host.q * (Dof x).host.d) ((Dof x).host.g k) := by
  first | exact @_root_.GlobalTheory.ElemAtStates.elem_all_alt_alt | exact _root_.GlobalTheory.ElemAtStates.elem_all_alt_alt | (intros; apply _root_.GlobalTheory.ElemAtStates.elem_all_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TauTrue
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
variable {D : D7} (m : Mv D) {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
section
variable {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE} {M : Formalism.L2.MtFam D} {C : NChoice D} {tp : TupTied D cf C}
end
section
variable {cf : CharFrame D} {C : NChoice D} {tp : TupTied D cf C}
theorem Mv.tauTrue_alt {a : _root_.GlobalTheory.HeightCounting.NAllCAlt D C} (x : TauTrue a.exp) : TauTrue ((_root_.UpperTheory.One.M.mvAll_alt trivial) m a).exp := (by with_unfolding_all exact (x :))
end
end GlobalTheory.LayerMove
end
end
end
