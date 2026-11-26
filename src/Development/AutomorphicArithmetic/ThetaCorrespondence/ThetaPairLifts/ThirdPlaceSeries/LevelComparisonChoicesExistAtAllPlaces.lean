module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisExistsChoice
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParahoricShapeTransferOfCmDatum

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CellWeightsAdmissibleOfCmDatum
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
noncomputable section
namespace GlobalTheory.LevCmp
open _root_.Formalism.L2.DIV GlobalTheory.CoefModel
section Gen2
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
end Gen2
set_option maxHeartbeats 4000000 in
theorem cellWt_of_sideRead_of_admTw : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ e, SideRead i b (T.k v) e → CellWt (D := Dof x) (mtAt (D := Dof x) l.mt.M v j) l.b.Bs.exp b hA j e := by
  intro hN hL
  refine StepW.of_all fun K B f T w _ _ _ P x l v i b ψ hA j hTw hl hok e hSR => ?_
  have hemb : ∀ t, Formalism.L2.embT (Dof x) t = Formalism.BasicNotions.TH.tauE (Dof x) t := fun t => rfl
  have hinj : Function.Injective (Formalism.L2.embT (Dof x)) := GlobalTheory.StdRat.tauE_injective (Dof x)
  have hcm : ∀ t t', Formalism.L2.embT (Dof x) t ≠ ComplexEmbedding.conjugate (Formalism.L2.embT (Dof x) t') := by
    intro t t' h
    have h1 := (GlobalTheory.StdRat.tauE_cm (Dof x) (Formalism.L2.embT (Dof x) t')).1 ⟨t', rfl⟩
    exact h1 ⟨t, h⟩
  have hcov : ∀ σ : (Dof x).host.E →+* ℂ, ∃ t, σ = Formalism.L2.embT (Dof x) t ∨
      σ = ComplexEmbedding.conjugate (Formalism.L2.embT (Dof x) t) := by
    intro σ
    by_cases h : ∃ t, Formalism.BasicNotions.TH.tauE (Dof x) t = σ
    · obtain ⟨t, ht⟩ := h
      exact ⟨t, Or.inl ht.symm⟩
    · have h2 : ¬ ¬ ∃ t, Formalism.BasicNotions.TH.tauE (Dof x) t = ComplexEmbedding.conjugate σ :=
        fun h' => h ((GlobalTheory.StdRat.tauE_cm (Dof x) σ).2 h')
      obtain ⟨t, ht⟩ := not_not.1 h2
      refine ⟨t, Or.inr ?_⟩
      rw [hemb, ht]
      simp
  have hcj : ∀ y, NX.cE (Dof x) y = IsCMField.complexConj (Dof x).host.E y := by
    intro y
    show (Dof x).host.conj y = _
    symm
    apply (Dof x).host.φ₀.injective
    rw [IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
  have hke : ∀ t, (e.comp (NX.toKk (Dof x) i (T.k v))).comp (NX.kEmb (Dof x) i b t) = Formalism.L2.embT (Dof x) t := by
    intro t
    ext y
    have h1 := hSR (NX.embEL0 (Dof x) (((Dof x).host.sigmaOf ((Dof x).eTau t : (Dof x).R.GG)) y))
    refine Eq.trans ?_ (h1.trans (NX.embLL_embEL0 (Dof x) t y))
    rfl
  obtain ⟨lamC, T', hT'⟩ := GlobalTheory.T.algebraic_weight_dominant_iso_exists (Dof x).host.E (Dof x).R.nV (Dof x).what₂.Tau (Formalism.L2.embT (Dof x)) hinj hcm hcov
    (mtAt l.mt.M v j).wt
  have hT'r : ∀ γ y, T' ((mtAt l.mt.M v j).wt.ρ γ y) =
      rhoVr (Formalism.L2.embT (Dof x)) lamC (Formalism.L2.Col.mtwRat.toFun γ) (T' y) :=
    fun γ y => hT' γ _ (match_mtwRat γ) y
  have hinj' : Function.Injective (Formalism.L2.Col.mtwConj (Formalism.L2.embT (Dof x))) := by
    intro t t' h
    apply hinj
    have := congrArg ComplexEmbedding.conjugate h
    simpa [Formalism.L2.Col.mtwConj] using this
  have hcm' : ∀ t t', Formalism.L2.Col.mtwConj (Formalism.L2.embT (Dof x)) t ≠
      ComplexEmbedding.conjugate (Formalism.L2.Col.mtwConj (Formalism.L2.embT (Dof x)) t') := by
    intro t t' h
    have h2 : ComplexEmbedding.conjugate (Formalism.L2.embT (Dof x) t) = Formalism.L2.embT (Dof x) t' := by
      simpa [Formalism.L2.Col.mtwConj] using h
    exact hcm t' t (by rw [← h2])
  have hten := Formalism.L2.Col.tenIrr_of' highest_weight_fixed_exists highest_weight_fixed_line
    (Formalism.L2.embT (Dof x)) hinj hcm lamC
  have hten' := Formalism.L2.Col.tenIrr_of' highest_weight_fixed_exists highest_weight_fixed_line _ hinj' hcm' lamC
  have hiso : (Formalism.L2.Col.mtWt (Formalism.L2.embT (Dof x)) lamC hten).Iso (mtAt l.mt.M v j).wt :=
    ⟨T'.symm, fun γ y => by
      apply T'.injective
      have hs : ∀ z, T' (T'.symm z) = z := fun z => T'.apply_symm_apply z
      erw [hT'r, hs, hs]
      rfl⟩
  have hdual := GlobalTheory.WtDual.isDual_of_iso hiso (Formalism.L2.Col.mtWt_isDual _ lamC hten hten')
  have hC : ∀ t, NG.infOf (lamC t).w = NG.paramV (Dof x).R ((Dof x).hc t) j (1 / 2) := fun t =>
    l.mt.mt.wt _ j t _ _ hdual (Formalism.L2.Col.tenWt_hwAt _ hinj hcm lamC hten' t)
  have hj1 : 1 ≤ j.1 + 1 := by omega
  have hj2 : j.1 + 1 ≤ (Dof x).R.m := by omega
  choose lam0 hlam0 using fun t => l.b.Bs.exp.rhoW_hw i (j.1 + 1) b t hj1 hj2
  obtain ⟨lamK, hlamK, TK, hTK⟩ := GlobalTheory.T.irreducible_weight_descends_to_polynomial_module (Dof x).host.E (Dof x).R.nV (Dof x).what₂.Tau
    (FractionRing ((Dof x).ntw.O i)) (e.comp (NX.toKk (Dof x) i (T.k v))) (NX.kEmb (Dof x) i b)
    (by intro t t' h; beta_reduce at h; rw [hke, hke] at h; exact hinj h)
    (by intro t t'; beta_reduce; rw [hke, hke]; exact hcm t t')
    (by intro σ; beta_reduce; simp only [hke]; exact hcov σ)
    (NX.cE (Dof x)) hcj _ (l.b.Bs.exp.rhoW i (j.1 + 1) b) (l.b.Bs.exp.rhoW_irr i (j.1 + 1) b hj1 hj2) lam0 hlam0
  have hK : ∀ t, NG.infOf (lam0 t) = NG.paramV (Dof x).R ((Dof x).hc t) j (1 / 2) := by
    intro t
    rw [l.b.Bs.exp.rhoW_wt i (j.1 + 1) b t hj1 hj2 _ (lam0 t) (GlobalTheory.FitHecke.infG_etaT l.a.A.chr t) (hlam0 t)]
    congr 1
    push_cast
    ring
  have hlam : lamK = lamC := by
    funext t
    apply domWeight_ext
    apply GlobalTheory.MtRead.eq_of_infOf_eq (lamK t).anti (lamC t).anti
    rw [hlamK t, hK t, hC t]
  subst hlam
  have hTK' : ∀ γ y, TK (l.b.Bs.exp.rhoW i (j.1 + 1) b γ y) =
      rhoVr (NX.kEmb (Dof x) i b) lamK (Formalism.L2.Col.mtwRat.toFun γ) (TK y) := fun γ y => hTK γ _ (match_mtwRat γ) y
  have hfun : (fun t => (e.comp (NX.toKk (Dof x) i (T.k v))).comp (NX.kEmb (Dof x) i b t)) = Formalism.L2.embT (Dof x) :=
    funext hke
  have h1 := GlobalTheory.T.weightMatrices_match_of_coeffSpace_iso (e.comp (NX.toKk (Dof x) i (T.k v))) (NX.kEmb (Dof x) i b) lamK _ (mtAt l.mt.M v j).wt.ρ TK hTK'
    T' (by rw [hfun]; exact hT'r)
  unfold CellWt
  letI := (GlobalTheory.LevCmp.cell l.b.Bs.exp b hA j).acg
  letI := (GlobalTheory.LevCmp.cell l.b.Bs.exp b hA j).mod
  exact GlobalTheory.T.matchingMatrices_of_baseChange_representation (NX.toKk (Dof x) i (T.k v)) e (l.b.Bs.exp.rhoW i (j.1 + 1) b) (GlobalTheory.LevCmp.cell l.b.Bs.exp b hA j).ρ
    (mtAt l.mt.M v j).wt.ρ (GlobalTheory.LevCmp.cell l.b.Bs.exp b hA j).bc h1
end GlobalTheory.LevCmp
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cellWt_of_sideRead_of_twOK : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ e, SideRead i b (T.k v) e → CellWt (D := Dof x) (mtAt (D := Dof x) l.mt.M v j) l.b.Bs.exp b hA j e := by
  first | exact @_root_.GlobalTheory.LevCmp.cellWt_of_sideRead_of_admTw | exact _root_.GlobalTheory.LevCmp.cellWt_of_sideRead_of_admTw | (intros; apply _root_.GlobalTheory.LevCmp.cellWt_of_sideRead_of_admTw <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsJointLevelOfCmDatum
set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
namespace GlobalTheory.JointLevel
open scoped TensorProduct
open Formalism.IndefR Formalism.BasicNotions.TH GlobalTheory.MtRead GlobalTheory.MtLev
open _root_.Formalism.L2.DIV (redFn rTup levFn kP blockTri blk2 blkOf dBlk upperLeftBlock ext1 G0 Pl)
section Loc
variable {D : D7} {V : HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E} {P : principalLevelFrame.RowPsi V n}
end Loc
variable {D : D7}
section Dat
variable {iso : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), ZMod (D.host.g kv.1) ≃+* kP (NX.pG D kv)}
  {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {f : Formalism.IndefR.NX.U D.nd → ℂ}
end Dat
section Shape
variable {iso : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), ZMod (D.host.g kv.1) ≃+* kP (NX.pG D kv)}
  {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {f : Formalism.IndefR.NX.U D.nd → ℂ}
  {V : HSp D} {hF : D.host.F = maximalRealSubfield D.host.E} {P : principalLevelFrame.RowPsi V D.R.nV}
end Shape
section Rows
open Formalism.IndefR.Links Formalism.IndefR.RecTie _root_.Formalism.L2.DIV
variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  {cG : G0 R.Pg D.R.r ≃* G0g D.nd}
end Rows
theorem joint_level_of_twOK_at_twisted : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → Joint (D := Dof x) (eta (D := Dof x) (cfOf x) w.I.xi v j) (mtAt (D := Dof x) l.mt.M v j) l.b.Bs.exp b hA j := by
  intro _ hL
  refine StepW.of_all ?_
  intro K B f T w _ _ _ P x l v i b ψ hA j hv _ hT
  have hon : (Dof x).what₂.muTw v = (Dof x).what₂.muAt v := (P.q.mu.on v (GlobalTheory.HeightCounting.Up.Model.mem_of_twisted x v hv)).symm
  have hμ : Formalism.IndefR.RecTie.Used0 (Dof x) ((Dof x).what₂.muTw v) := Or.inr ⟨v, hon⟩
  refine joint_of (D := Dof x) l.mt.ad l.rat.rat l.b.Bs l.b.ser x.m.z.lev.is x.m.z.pins.keep l.Pq_over l.a.elem (fun t PP hPP => ?_)
    hμ j ?_ b hA hT
  · rw [x.m.z.lev.Q] at hPP
    rw [l.sel]
    obtain ⟨u, -, e⟩ := (Formalism.L2.Col.mem_QE _ _ _).1 hPP
    exact ⟨u, e⟩
  · have e1 := x.m.z.lev.xiH (x.r.Y.tupT ((Dof x).what₂.muTw v))
    have e2 := x.m.tup (x.r.Y.tupT ((Dof x).what₂.muTw v))
    rw [← x.r.tup, x.r.Y.tupTie _ hμ] at e2
    rw [e1, ← e2, x.m.z.lev.C]
    rfl
end GlobalTheory.JointLevel
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.joint_level_of_cm_datum_twOK : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → Joint (D := Dof x) (eta (D := Dof x) (cfOf x) w.I.xi v j) (mtAt (D := Dof x) l.mt.M v j) l.b.Bs.exp b hA j := by
  first | exact @_root_.GlobalTheory.JointLevel.joint_level_of_twOK_at_twisted | exact _root_.GlobalTheory.JointLevel.joint_level_of_twOK_at_twisted | (intros; apply _root_.GlobalTheory.JointLevel.joint_level_of_twOK_at_twisted <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BadPlacesSubsetRamifiedPlacesOfCmDatum
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
namespace GlobalTheory.LevCmp.BadV
theorem bad_places_subset_ramified_places_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → NX.badV (Dof x) i (QOf P v) ⊆ gPl (Dof x) ∪ qPl (Dof x) (eta (D := Dof x) (cfOf x) w.I.xi v j) := by
  intro _ hL
  refine GlobalTheory.Mem.Top.Bl.StepW.of_all ?_
  intro K B f T w _ _ _ P x l v i b ψ hA j htw hl hok
  have hQ : QOf P v = T.Q v := GlobalTheory.HeightCounting.Up.Model.qOf_eq v
  have h2 := P.q.mu.tw v
  intro u hu
  obtain ⟨w', hw'u, hw'⟩ := hu
  by_cases hg : u ∈ gPl (Dof x)
  · exact Or.inl hg
  refine Or.inr ⟨hg, w', hw'u, ?_⟩
  have hmu : ((cfOf x).mu0 j).UnrAt w' :=
    ((cfOf x).isMu0 j).unr w' fun k hk => hg ⟨w', hw'u, k, hk⟩
  intro hun
  have hxi : (T.xiTw f v).UnrAt w' := by
    have hx : (w.I.xi (P.q.W₀.muTw v)).UnrAt w' := unr_of_mul_left hmu hun
    rwa [h2] at hx
  unfold TwDat.xiTw at hxi
  have hpde : B.host.pde ∈ offSet B.toPre := by simp [offSet]
  have hpde' : B.host.pde' ∈ offSet B.toPre := by simp [offSet]
  rcases hw' with hq | hG | hp
  · rw [hQ] at hq
    have hψ : ¬ (T.psi v).UnrAt w' := fun h => ((T.psi_is v).ram w').1 h hq
    have hd : (if B.places.resChar v = B.host.pde then f.del' else f.del).UnrAt w' := by
      split_ifs
      · exact f.isDel'.unr w' fun ho => hψ (unr_of_twist (T.psi_tw v) B.host.pde'_prime hpde' w' ho)
      · exact f.isDel.unr w' fun ho => hψ (unr_of_twist (T.psi_tw v) B.host.pde_prime hpde w' ho)
    exact hψ (unr_of_mul_left hd hxi)
  · exact hg ⟨w', hw'u, hG⟩
  · have hp' : w' ∈ placesOver (Dof x).host.E (if (Dof x).ntw.l i = (Dof x).host.pde then (Dof x).host.pde' else (Dof x).host.pde) := by
      rw [← (Dof x).ntw.pD_eq i]; exact hp
    rw [hl] at hp'
    change w' ∈ placesOver B.host.E (if B.places.resChar v = B.host.pde then B.host.pde' else B.host.pde) at hp'
    split_ifs at hp' hxi
    · exact not_unr_of_delta f.isDel' w' hp'
        (unr_of_mul_right (unr_of_twist (T.psi_tw v) B.host.pde'_prime hpde' w' hp') hxi)
    · exact not_unr_of_delta f.isDel w' hp'
        (unr_of_mul_right (unr_of_twist (T.psi_tw v) B.host.pde_prime hpde w' hp') hxi)
end GlobalTheory.LevCmp.BadV
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.badV_subset_gPl_union_qPl_of_admTw : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → NX.badV (Dof x) i (QOf P v) ⊆ gPl (Dof x) ∪ qPl (Dof x) (eta (D := Dof x) (cfOf x) w.I.xi v j) := by
  first | exact @_root_.GlobalTheory.LevCmp.BadV.bad_places_subset_ramified_places_alt | exact _root_.GlobalTheory.LevCmp.BadV.bad_places_subset_ramified_places_alt | (intros; apply _root_.GlobalTheory.LevCmp.BadV.bad_places_subset_ramified_places_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisRepOfTwistExistsWithProperties
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
noncomputable section
namespace GlobalTheory.GalTwist
theorem galoisRep_of_twist_properties_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ (D : D7) (l : ℕ) (Q : Finset (PlE D.host)) (χ : HChar D.host.E) (ψ₀ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.what₂.LL)ˣ), l.Prime → IsPsi (H := D.host) l Q χ → GalOf D χ ψ₀ → AntiHom D.ntw.cc ψ₀ ∧ RamExactly ψ₀ (↑Q : Set (PlE D.host)) ∧ BlochKatoReduction.Gen.TrivAbove ψ₀ l := by
  intro _ D l Q χ ψ₀ _ hψ hG
  classical
  obtain ⟨hker, art, ha, h⟩ := hG
  generalize hr : (Units.map D.what₂.embLL.toMonoidHom).comp ψ₀ = r at h
  have hinj : ∀ g, r g = 1 ↔ ψ₀ g = 1 := fun g => by
    rw [← hr, MonoidHom.comp_apply]
    exact map_eq_one_iff _ (Units.map_injective (f := D.what₂.embLL.toMonoidHom) D.what₂.embLL.injective)
  have hrker : IsOpen (r.ker : Set (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)) := by
    convert hker using 1
    ext g
    exact hinj g
  have hrc : Continuous r := GlobalTheory.HeckeGal.continuous_of_isOpen_ker' r hrker
  have : Algebra.IsAlgebraic D.host.E D.nd.Om := IsAlgClosure.isAlgebraic
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨c, hc1, hcm, hrr, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
    obtain ⟨j, hj⟩ := D.ntw.cc_cm.1
    have h1 : ∀ x : D.host.E, D.ntw.cc (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (c x) := fun x => by
      apply j.injective
      rw [hj, hc1]
      exact (D.host.conjE_apply (j.comp (algebraMap D.host.E D.nd.Om)) x).symm
    have h2 : ∀ x, D.ntw.cc (D.ntw.cc x) = x := fun x => j.injective (by rw [hj, hj, Complex.conj_conj])
    have hinv : ∀ x, c (c x) = x := fun x => (algebraMap D.host.E D.nd.Om).injective (by rw [← h1, ← h1, h2])
    have hc : ∀ x : D.host.E, ∃ y : D.host.E, D.ntw.cc.symm (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om y :=
      fun x => ⟨c x, by rw [RingEquiv.symm_apply_eq, h1, hinv]⟩
    choose bar hbar using fun v => (GlobalTheory.Mem.Chr.existsUnique_conjPl c.toRingEquiv v).exists
    have hbb : ∀ v, bar (bar v) = v := fun v =>
      (GlobalTheory.Mem.Chr.existsUnique_conjPl c.toRingEquiv (bar v)).unique (hbar _) (GlobalTheory.AntiLAdic.conjPl_symm hinv (hbar v))
    let T := (GlobalTheory.Mem.UnrAe.finite_ramified χ).toFinset
    have key : r * r.comp (GlobalTheory.AntiLAdic.conjHom D.ntw.cc hc) = 1 := by
      refine GlobalTheory.FrobDense.eq_one_of_frob D.host.E D.nd.Om art ha ℂˣ _
        (hrc.mul (hrc.comp (GlobalTheory.AntiLAdic.continuous_conjHom D.ntw.cc hc))) (T ∪ T.image bar) fun v hv A hA σ hσ => ?_
      rw [Finset.mem_union, not_or] at hv
      have a2 : χ.UnrAt v := by simpa [T] using hv.1
      have b2 : χ.UnrAt (bar v) := by
        by_contra hn
        exact hv.2 (Finset.mem_image.2 ⟨bar v, by simpa [T] using hn, hbb v⟩)
      have hA' := GlobalTheory.AntiLAdic.isPlaceOver_moveVal_conjPl (c := c.toRingEquiv) h1 (hbar v) hA
      have hσ' := GlobalTheory.AntiLAdic.isFrob_conjHom D.ntw.cc hc hσ
      rw [← GlobalTheory.AntiLAdic.normV_conjPl (hbar v)] at hσ'
      have e3 := GlobalTheory.AntiLAdic.val_mul_val_conj c hcm.rank hcm.ne hrr χ hψ.triv (hbar v) a2 b2
      rw [h.val_eq ha a2 hA hσ, h.val_eq ha b2 hA' hσ', ← mul_inv, inv_eq_one] at e3
      show r σ * r (GlobalTheory.AntiLAdic.conjHom D.ntw.cc hc σ) = 1
      exact e3
    intro g g' hg
    have e : g' = GlobalTheory.AntiLAdic.conjHom D.ntw.cc hc g := AlgEquiv.ext hg
    have k : r g * r (GlobalTheory.AntiLAdic.conjHom D.ntw.cc hc g) = 1 := DFunLike.congr_fun key g
    rw [← map_mul, hinj, map_mul, ← e] at k
    exact eq_inv_of_mul_eq_one_right k
  · intro v A hA
    rw [← not_iff_not, not_exists]
    simp only [not_and, not_not]
    rw [Finset.mem_coe, ← hψ.ram v, h.unr_iff ha hA]
    exact forall₂_congr fun σ _ => (hinj σ).symm
  · intro v hv A hA σ hσ
    rw [← hinj]
    have hcl : IsClosed ((GlobalTheory.HeckeGal.liftAb r hrc).ker : Set (Gab D.host.E D.nd.Om)) :=
      isClosed_singleton.preimage (GlobalTheory.HeckeGal.continuous_liftAb r hrc)
    have hle : (art.comp (Neutral.B1.localIdele D.host.E v)).range ≤ (GlobalTheory.HeckeGal.liftAb r hrc).ker := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨τ, hτ⟩ := GlobalTheory.HeckeGal.toAb_surjective (art (Neutral.B1.localIdele D.host.E v x))
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← hτ, GlobalTheory.HeckeGal.liftAb_toAb, ← h _ τ hτ.symm]
      exact hψ.atl v hv x
    have hm : GlobalTheory.HeckeGal.toAb D.host.E D.nd.Om σ ∈ (GlobalTheory.HeckeGal.liftAb r hrc).ker := by
      refine Subgroup.topologicalClosure_minimal _ hle hcl ?_
      rw [ha.dec v A hA]
      exact ⟨σ, hσ, rfl⟩
    rwa [MonoidHom.mem_ker, GlobalTheory.HeckeGal.liftAb_toAb] at hm
end GlobalTheory.GalTwist
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galoisRep_of_twist_of_prime : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ (D : D7) (l : ℕ) (Q : Finset (PlE D.host)) (χ : HChar D.host.E) (ψ₀ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.what₂.LL)ˣ), l.Prime → IsPsi (H := D.host) l Q χ → GalOf D χ ψ₀ → AntiHom D.ntw.cc ψ₀ ∧ RamExactly ψ₀ (↑Q : Set (PlE D.host)) ∧ BlochKatoReduction.Gen.TrivAbove ψ₀ l := by
  first | exact @_root_.GlobalTheory.GalTwist.galoisRep_of_twist_properties_alt | exact _root_.GlobalTheory.GalTwist.galoisRep_of_twist_properties_alt | (intros; apply _root_.GlobalTheory.GalTwist.galoisRep_of_twist_properties_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelUniformityOfCmDatum
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
noncomputable section
namespace GlobalTheory.XUni
theorem level_uniformity_transfer_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ kk u (s : SplitPlace (Dof x).host.E), s.w = (Dof x).naut.plGw kk u → ∃ (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield (Dof x).host.E)) ℂ) (ξ : (s.v.adicCompletion (maximalRealSubfield (Dof x).host.E))ˣ →* ℂˣ), NG.IsPsi0 s ψ₀ ∧ NG.IsCompAt (eta (D := Dof x) (cfOf x) w.I.xi v j) s ξ ∧ ∀ e, SideRead i b (T.k v) e → NG.LevelUni (cell (D := Dof x) l.b.Bs.exp b hA j).J (cx e (cell (D := Dof x) l.b.Bs.exp b hA j).χ) s (Dof x).R.r ψ₀ ξ := by
  intro hP hL
  refine StepW.of_all fun K B f T w hK hF _ P x l v i b ψ hA j htw hl hok kk u s hs => ?_
  obtain ⟨τ', hτ'⟩ := l.b.tau
  let kv0 : Σ k : Fin 2, (Dof x).nd.PlG k := ⟨kk, u⟩
  have hsw : ((cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) kv0)).w = s.w := by
    rw [(cell (D := Dof x) l.b.Bs.exp b hA j).sp_w _ (Or.inr (Or.inr ⟨kv0, rfl⟩)), hs]
  obtain rfl := GlobalTheory.T.splitPlace_eq_of_cmFieldPlace_eq _ _ _ hsw
  have hg : (((Dof x).host.g kk : ℕ) : 𝓞 (Dof x).host.E) ∈
      ((cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) kv0)).w.asIdeal := by
    rw [hsw, hs]; exact (Dof x).naut.plGw_over kk u
  have hoffkv : ∀ kv, kv ≠ kv0 → ((cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) kv)).v ≠
      ((cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) kv0)).v := fun kv hne heq =>
    hne (GlobalTheory.PlaceInj.splitPlace_v_injective (Dof x)
      (fun k v => (cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) ⟨k, v⟩))
      (fun k v => (cell (D := Dof x) l.b.Bs.exp b hA j).sp_w _ (Or.inr (Or.inr ⟨⟨k, v⟩, rfl⟩))) heq)
  have hoffQ : ∀ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP, ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').v ≠
      ((cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) kv0)).v := fun P' hP' heq => by
    have h1 := GlobalTheory.T.splitPlaces_same_realPlace_natCast_mem _ _ _ _ heq.symm hg
    rw [(cell (D := Dof x) l.b.Bs.exp b hA j).sp_w P' (Or.inl hP')] at h1
    exact (hA.2.1 P' ((cell (D := Dof x) l.b.Bs.exp b hA j).QP_sub hP')).2 kk h1
  have hoffD : ∀ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP, ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').v ≠
      ((cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) kv0)).v := fun P' hP' heq => by
    have h1 := GlobalTheory.T.splitPlaces_same_realPlace_natCast_mem _ _ _ _ heq.symm hg
    rw [(cell (D := Dof x) l.b.Bs.exp b hA j).sp_w P' (Or.inr (Or.inl hP'))] at h1
    exact GlobalTheory.T.generator_not_mem_twist_place _ _ _ kk ((cell (D := Dof x) l.b.Bs.exp b hA j).DP_sub hP') h1
  haveI : Fact ((Dof x).host.g kv0.1).Prime := ⟨(Dof x).host.g_prime kk⟩
  let φ : AddChar (ZMod ((Dof x).host.g kv0.1)) ℂ :=
    { toFun := fun y => embLL0 (Dof x) ((l.rat.In.θ kv0.1 (Multiplicative.ofAdd (NX.xiRed (Dof x) kv0 * y)) : (↥(Dof x).LL0)ˣ) : ↥(Dof x).LL0)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun a c => by rw [mul_add, ofAdd_add, map_mul, Units.val_mul, map_mul] }
  have hφ : 2 ≤ (Dof x).R.r → φ ≠ 1 := fun hr h1 => by
    have e1 := congrArg (fun χ : AddChar (ZMod ((Dof x).host.g kv0.1)) ℂ => χ 1) h1
    have hne := GlobalTheory.T.rationalDatum_characters_ne_one_at_fixedElement_residues _ _ _ _ _ _ _ _ _ l.b.Bs hr i kv0
    apply hne
    simp only [φ, AddChar.coe_mk, AddChar.one_apply, mul_one] at e1
    exact Units.ext ((embLL0 (Dof x)).injective (by rw [e1, Units.val_one, map_one]))
  have hex := GlobalTheory.T.exists_nontrivial_addChar_zmod_eq_of_ne_one ((Dof x).host.g kv0.1) (2 ≤ (Dof x).R.r) φ hφ
  let ψ' := hex.choose
  have hψ'1 : ψ' ≠ 1 := hex.choose_spec.1
  have hψ'φ : 2 ≤ (Dof x).R.r → ψ' = φ := hex.choose_spec.2
  have hex0 := GlobalTheory.T.exists_addChar_completion_of_residue_addChar (maximalRealSubfield (Dof x).host.E)
    ((cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) kv0)).v ((Dof x).host.g kv0.1)
    ((cell (D := Dof x) l.b.Bs.exp b hA j).redG kv0) ψ' hψ'1
  let ψ₀ := hex0.choose
  have hψ₀m := hex0.choose_spec.1
  have hψ₀n := hex0.choose_spec.2.1
  have hψ₀r := hex0.choose_spec.2.2
  have hunr : (w.I.xi ((Dof x).what₂.muTw v)).UnrAt ((cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) kv0)).w := by
    have e2 : w.I.xi ((Dof x).what₂.muTw v) = T.xiTw f v := P.q.mu.tw v
    rw [e2]
    refine GlobalTheory.T.twistedTuple_finiteOrderPart_unramified_at_typePrimes B f T v _ kk hg fun hQ => ?_
    rw [← Model.qOf_eq (P := P) v] at hQ
    exact (hA.2.1 _ hQ).2 kk hg
  have hexξ := GlobalTheory.T.compAt_baseCharacter_mul_unramified_eq_typeCharacter hP.what₂.art _ _ _ _ _ _ _ _ _ l.b.Bs l.a.val τ' hτ' j kv0 _ hs
    _ hunr ((cell (D := Dof x) l.b.Bs.exp b hA j).redG kv0)
  let ξ := hexξ.choose
  have hξc := hexξ.choose_spec.1
  have hξv := hexξ.choose_spec.2
  refine ⟨ψ₀, ξ, ⟨hψ₀m, hψ₀n⟩, hξc, fun e he => ⟨fun κ hκ => GlobalTheory.T.mem_level_iff_unipotent_at_typePlace _ _ _ _ _ _ _ _ _ _ _ _ kv0 hoffkv hoffQ hoffD κ hκ, ?_⟩⟩
  intro κ h hκ uu huu
  have hc := GlobalTheory.T.levelCharacter_eq_localFactor_at_typePlace _ _ _ _ _ _ _ _ _ _ _ (cell (D := Dof x) l.b.Bs.exp b hA j) kv0 hoffkv hoffQ hoffD κ h hκ
  have hU := (GlobalTheory.T.mem_level_iff_unipotent_at_typePlace _ _ _ _ _ _ _ _ _ _ _ (cell (D := Dof x) l.b.Bs.exp b hA j) kv0 hoffkv hoffQ hoffD κ hκ).1 h
  have hr := GlobalTheory.T.complex_typePlaceCharacter_eq_superdiag_addChar_mul_lowerDet _ l.b.Bs.exp i _ b kv0 _ _ l.rat.In.θ (fun u hu hu' => l.b.Bs.psiU i b u hu hu') _ (τ' (j.1 + 1) kv0)
    (fun y => hτ' i (j.1 + 1) b kv0 y (Nat.le_add_left 1 j.1) j.2) e he ψ₀ (fun hr y => (hψ₀r y).trans (congrArg (fun χ : AddChar (ZMod ((Dof x).host.g kv0.1)) ℂ => χ ((cell (D := Dof x) l.b.Bs.exp b hA j).redG kv0 y)) (hψ'φ hr))) ξ hξv _ hU uu huu
  exact (cx_apply e _ ⟨κ, h⟩).trans ((congrArg e hc).trans hr)
end GlobalTheory.XUni
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_uniformity_of_cmDatum_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ kk u (s : SplitPlace (Dof x).host.E), s.w = (Dof x).naut.plGw kk u → ∃ (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield (Dof x).host.E)) ℂ) (ξ : (s.v.adicCompletion (maximalRealSubfield (Dof x).host.E))ˣ →* ℂˣ), NG.IsPsi0 s ψ₀ ∧ NG.IsCompAt (eta (D := Dof x) (cfOf x) w.I.xi v j) s ξ ∧ ∀ e, SideRead i b (T.k v) e → NG.LevelUni (cell (D := Dof x) l.b.Bs.exp b hA j).J (cx e (cell (D := Dof x) l.b.Bs.exp b hA j).χ) s (Dof x).R.r ψ₀ ξ := by
  first | exact @_root_.GlobalTheory.XUni.level_uniformity_transfer_alt | exact _root_.GlobalTheory.XUni.level_uniformity_transfer_alt | (intros; apply _root_.GlobalTheory.XUni.level_uniformity_transfer_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypePlacesCover
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypePlacesCover
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
noncomputable section
namespace GlobalTheory.TypePlacesCover
variable {D : D7}
end GlobalTheory.TypePlacesCover
open GlobalTheory.TypePlacesCover in
theorem GlobalTheory.TypePlacesCover.gPlaces_all_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x => _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → GPlaces (Dof x) :=
  fun _ => StepW.of_all fun _ _ _ _ _ _ _ _ _ x _ => gPlaces (Dof x)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypePlacesCoverStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gPlaces_of_levelA : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x => _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → GPlaces (Dof x) :=
  _root_.GlobalTheory.TypePlacesCover.gPlaces_all_alt
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
noncomputable section
namespace GlobalTheory.LevCmp
variable {D : D7}
theorem exists_level_comparison_choice_alt (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (hG : IsGalois ℚ ↥D.LL0) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (M : MtFam D) (X : NExpTied D)
    (F : TwFrameC D) (xi : D.what₂.Tup → HChar D.host.E) (χ : D.what₂.places.Pl → HChar D.host.E)
    (Q : D.what₂.places.Pl → Finset (PlE D.host)) (k : D.what₂.places.Pl → ℕ) (s : D.what₂.places.Pl → D.ntw.Tw)
    (hs : ∀ v, ∃ b, ReadsAt (s v) b v) (c1 : ∀ v, s (D.what₂.places.conj v) = s v)
    (htp : ∀ C : NChoice D, C.Q = Q → ∃ tp : TupTied D cf C, tp.xi = xi ∧ tp.psi = χ)
    (h1 : ∀ v, IsPsi (H := D.host) (D.what₂.places.resChar v) (Q v) (χ v))
    (h2 : ∀ v, (χ v).OrderDvd (D.what₂.places.resChar v ^ k v))
    (h3 : ∀ v, ∃ z : D.what₂.LL, IsPrimitiveRoot z (D.what₂.places.resChar v ^ k v))
    (h4 : ∀ v, ¬ TwistedAt D v → Q v = ∅) (h5 : ∀ v, Disjoint (Q v) (D.ntw.S0 (s v)))
    (h6 : ∀ v v', (∀ x ∈ D.LL0, 0 ≤ D.what₂.places.val v x ↔ 0 ≤ D.what₂.places.val v' x) → k v = k v' ∧ χ v = χ v')
    (h7 : ∀ v, χ (D.what₂.places.conj v) = χ v ∧ k (D.what₂.places.conj v) = k v)
    (h8 : ∀ v b (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok (s v) (k v))ˣ) (hA : NX.AdmTw D (s v) (k v) (Q v) ψ) (j : Fin D.R.m),
      TwistedAt D v → D.ntw.l (s v) = D.what₂.places.resChar v → IntegralHeckeForms.TwOK (s v) (k v) (Q v) ψ → ∀ e, SideRead (s v) b (k v) e →
      ReadsHecke e ψ (χ v) →
      LevEq (mtAt M v j).J (mtAt M v j).χ (cell X b hA j).J (cx e (cell X b hA j).χ) ∧ CellWt (mtAt M v j) X b hA j e) :
    ∃ (C : NChoice D) (tp : TupTied D cf C), tp.xi = xi ∧ tp.psi = χ ∧ C.Q = Q ∧ C.k' = k ∧ ChoiceSide D cf M X C tp ∧
      (∀ v, IntegralHeckeForms.TwOK (C.twI v) (C.k' v) (C.Q v) ((C.psi' v).comp (D.ntw.art (C.twI v) (C.Q v)))) ∧ C.twI = s := by
  classical
  have hl : ∀ v, D.ntw.l (s v) = D.what₂.places.resChar v := fun v => let ⟨_, h⟩ := hs v; h.l_eq
  have hQ : ∀ v v', χ v = χ v' → Q v = Q v' := fun v v' e => Finset.ext fun u =>
    not_iff_not.1 (((h1 v).ram u).symm.trans (e ▸ (h1 v').ram u))
  let g : HChar D.host.E → ℕ → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.what₂.LL)ˣ) := fun c n =>
    @Classical.epsilon _ ⟨1⟩ fun ψ₀ => GalOf D c ψ₀ ∧ ∀ g, ψ₀ g ^ n = 1
  let ψ₀ := fun v => g (χ v) (D.ntw.l (s v) ^ k v)
  have hψ : ∀ v, GalOf D (χ v) (ψ₀ v) ∧ ∀ g, ψ₀ v g ^ (D.ntw.l (s v) ^ k v) = 1 := fun v =>
    Classical.epsilon_spec (GlobalTheory.T.exists_galoisCharacter_of_finiteOrder_heckeCharacter hP.what₂.art D (χ v) _ (pow_pos (D.ntw.lPrime _).out.pos _) (hl v ▸ h2 v) (hl v ▸ h3 v))
  have c4 : ∀ v, ψ₀ (D.what₂.places.conj v) = ψ₀ v := fun v => by simp only [ψ₀, c1, (h7 v).1, (h7 v).2]
  have hd := fun v b (ρ : Reading (s v) (k v) b v) =>
    let ⟨a1, a2, a3⟩ := _root_.GlobalTheory.T.exists_galoisRep_of_twist_of_prime hP D _ (Q v) (χ v) (ψ₀ v) (D.ntw.lPrime (s v)).out (hl v ▸ h1 v) (hψ v).1
    GlobalTheory.T.exists_ringClassGroup_descent_of_coeffFieldTwist D (s v) (k v) b v ρ (Q v) (ψ₀ v) (h1 v).split (h5 v) (hψ v).1.1 a1 (hψ v).2 a2 a3
  obtain ⟨b, ρ, ψ, hr, hp, hb, hc⟩ := exists_data hG s Q k ψ₀ hs c1 (fun v => hQ _ _ (h7 v).1) (fun v => (h7 v).2) c4
    fun v b ρ => (hd v b ρ).1
  have hok := fun v => (hd v _ (ρ v)).2 _ (hp v)
  choose ι hι using fun v => GlobalTheory.T.exists_complexEmbedding_readingFractionRing_over_coeffField D F (s v) (k v) (b v) v (ρ v)
  have hlev := fun v hA j (hv : TwistedAt D v) =>
    let ⟨a1, a2⟩ := reads_of_pulls (ρ v) (hp v) (hψ v).1 (hι v)
    h8 v (b v) _ hA j hv (hl v) (hok v) _ a1 a2
  have hrk : ∀ v, TwistedAt D v → GlobalTheory.TwistChoice.RankEq (s v) (b v) (Q v) (k v) (ψ v) v := fun v hv j j1 j2 => by
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    obtain ⟨a1, a2⟩ := hlev v (GlobalTheory.MtRead.admissible_twist_of_twisting_character (hok v)) ⟨j, j2⟩ hv
    exact rank_of_levEq _ X _ _ ⟨j, j2⟩ _ a1 a2
  let C := GlobalTheory.TwistChoice.choiceOf s b Q k ψ hr ρ hrk
  obtain ⟨tp, t1, t2⟩ := htp C rfl
  refine ⟨C, tp, t1, t2, rfl, rfl, ⟨⟨fun a => hE.elim a, fun a => hE.elim a, fun a => hE.elim a,
    ⟨ψ₀, c4, hp, fun a => hE.elim a⟩, fun v x y z _ hx => (ρ v).emb_side x y z hx⟩,
    ⟨c1, fun v _ => (GlobalTheory.T.twistReading_induces_sideEmbedding_fixedField D _ _ _ _ (ρ v)).1, fun v _ x => (GlobalTheory.T.twistReading_induces_sideEmbedding_fixedField D _ _ _ _ (ρ v)).2.2 _ x, fun v _ => hb v,
      fun v v' _ _ e => ?_, fun v _ => hc v⟩, h4, fun v _ => GlobalTheory.MtRead.admissible_twist_of_twisting_character (hok v), ?_, ?_⟩, hok, rfl⟩
  · have e' : s v' = s v := e
    have key : k v' = k v ∧ χ v' = χ v := by
      have a1 := (GlobalTheory.T.twistReading_induces_sideEmbedding_fixedField D _ _ _ _ (ρ v)).1
      have a2 := (GlobalTheory.T.twistReading_induces_sideEmbedding_fixedField D _ _ _ _ (ρ v')).1
      have a3 := (GlobalTheory.T.twistReading_induces_sideEmbedding_fixedField D _ _ _ _ ((ρ v').conj hG)).1
      rw [e'] at a2 a3
      by_cases hbb : b v' = b v
      · rw [hbb] at a2
        exact h6 _ _ fun x hx => (a2 ⟨x, hx⟩).trans (a1 ⟨x, hx⟩).symm
      · have : (!b v') = b v := by revert hbb; cases b v <;> cases b v' <;> simp
        rw [this] at a3
        have a4 := h6 _ _ fun x hx => (a3 ⟨x, hx⟩).trans (a1 ⟨x, hx⟩).symm
        exact ⟨(h7 v').2.symm.trans a4.1, (h7 v').1.symm.trans a4.2⟩
    exact pack_pow (ρ v) (ρ v') e' (hQ _ _ key.2) key.1 (by simp only [ψ₀, e', key.1, key.2]) (hl v ▸ h3 v) (hψ v).2 (hp v) (hp v')
  · intro v _ u hu _ A σ hA hσ y hy
    obtain ⟨-, art, ha, h⟩ := (hψ v).1
    have a1 := h.val_eq ha (((h1 v).ram u).2 hu) hA hσ
    have a2 : y = (ψ₀ v σ : D.what₂.LLˣ) := D.what₂.embLL.injective (by rw [hy, t2, a1, inv_inv]; rfl)
    rw [a2]
    exact hp v σ
  · intro v j j1 j2 hv hA
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    obtain ⟨⟨a1, a2⟩, -⟩ := hlev v hA ⟨j, j2⟩ hv
    exact ⟨ι v, hι v, a1, fun κ h h' => congrArg Units.val (a2 κ h h')⟩
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
theorem stageCExists_of_harishChandra_serN : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.ThirdStageExists hL := by
  intro hCo hCW hHM hP hS hL
  refine ((_root_.GlobalTheory.T.nonGalois_exists_choice_alt hCo hCW hHM hP hS hL).and ((_root_.GlobalTheory.T.gPlaces_of_levelA hL).and (GlobalTheory.T.twistConductors_avoid_excludedPrimes.and ((_root_.GlobalTheory.T.badV_subset_gPl_union_qPl_of_admTw hP hL).and ((_root_.GlobalTheory.T.paraShape_of_twisted_sideRead_readsHecke hP hL).and ((_root_.GlobalTheory.T.level_uniformity_of_cmDatum_alt hP hL).and
    ((_root_.GlobalTheory.T.joint_level_of_cm_datum_twOK hP hL).and (_root_.GlobalTheory.T.cellWt_of_sideRead_of_twOK hP hL)))))))).trans (StepW.of_all ?_)
  rintro K B f T w - - ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ P x l s hs c1
  have hl : ∀ v, (Dof x).ntw.l (s v) = B.places.resChar v := fun v => let ⟨_, h⟩ := hs v; h.l_eq
  obtain ⟨C, tp, b1, b2, b3, b4, b5, b6, b7⟩ := _root_.GlobalTheory.LevCmp.exists_level_comparison_choice_alt (D := Dof x) hP B.coeffGaloisSubfield_isGalois l.a.A.bare (cfOf x) l.mt.M l.b.Bs.exp
    l.b.Bs.twF w.I.xi T.psi (QOf P) T.k s hs c1 (exists_tp x) (fun v => Model.qOf_eq (P := P) v ▸ T.psi_is v) T.psi_ord P.coh.roots
    (fun v hv => Model.qOf_off v fun h => hv ((Model.twisted_iff x v).2 h))
    (fun v => disjoint_conductorPlaces_excludedSet (l.b.rootsOfUnityRing_le_wittIntegers (s v)) (fun u hu h => T.Q_l v u (Model.qOf_eq (P := P) v ▸ hu) (hl v ▸ h))
      fun u hu => a2 P x v u (Model.qOf_eq (P := P) v ▸ hu))
    (fun v v' h => (P.coh.same v v' h).2) T.conj fun v b ψ hA j hv hl' hok e he hr => by
      have hg := TupTie.good_set f T (w.xi_range ▸ Set.mem_range_self ((Dof x).what₂.muTw v))
      exact ⟨levEq _ _ b hA j e he (a1 P x l.toLA)
        (fun s' ξ => GlobalTheory.T.exists_local_unit_character_nontrivial (Dof x) (cfOf x) j _ s' ξ hg.2.1 hg.2.2) (l.mt.mt.prod v j) (l.mt.mt.para v j) (l.mt.mt.uni v j)
        (l.mt.mt.hyp v j) (a3 P x l v _ b ψ hA j hv hl' hok) (a4 P x l v _ b ψ hA j hv hl' hok e he hr)
        (a5 P x l v _ b ψ hA j hv hl' hok) (a6 P x l v _ b ψ hA j hv hl' hok), a7 P x l v _ b ψ hA j hv hl' hok e he⟩
  obtain ⟨c, hc⟩ := a0 P x l C tp b1 b2 b3 (fun v _ => congrFun b4 v) b5 fun v _ => b6 v
  exact ⟨c, hc.trans b7⟩
end GlobalTheory.LevCmp
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stageCExists_of_casselmanWallach : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.ThirdStageExists hL := by
  first | exact @_root_.GlobalTheory.LevCmp.stageCExists_of_harishChandra_serN | exact _root_.GlobalTheory.LevCmp.stageCExists_of_harishChandra_serN | (intros; apply _root_.GlobalTheory.LevCmp.stageCExists_of_harishChandra_serN <;> assumption)
end
end
