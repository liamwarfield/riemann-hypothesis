module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KloostermanDiagonalOfConditions
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupOrb
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIC

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXVolH
noncomputable section

namespace Formalism.L2.SG.Pf.MassDataX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Measures Formalism.L2.SG.Volumes MeasureTheory MassDataVolumesW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem covolH_eq_volG (hSW : PI.VolStabS.MassDataS.SWXS) {D : D7} (X : HidaSetting D)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (hψ : IsCharAF X.B.I.F ψ) (hC : MeasCompatψ X ψ)
    (w : D.what₂.Word) :
    covol (X.measW w).μH = covolBy (G := HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) (HFinIn (AF X.B.I.F) X.B.I.cm.sig X.B.I.J)
      X.measG.μG := by
  have hs := stepSizeW X
  obtain ⟨⟨hT1, νH, hνH, hcH⟩, -⟩ := hC.1 w
  exact covol_eq_covolBy_w (PI.VolStabS.MassDataS.volStabXS_of hSW X) (stepHerm X) (a := D.R.rS + 1 + D.R.rS)
    (by omega) (by omega) _ hT1 (stepGramH_of MassDataLevelSSteps.frameStd_holds X w hT1) hψ X.measG_norm.1 hνH
    (X.measW_norm w).1 hcH

section MassData

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem volHa'_eq (hSW : PI.VolStabS.MassDataS.SWXS) (hψ : IsCharAF X.B.I.F ψ) (hC : MeasCompatψ X ψ) :
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volHa' =
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volG :=
  covolH_eq_volG hSW X ψ hψ hC u'

end MassData

end Formalism.L2.SG.Pf.MassDataX
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfF
noncomputable section

open ValuativeRel

namespace Formalism.MainNotions.S.Loc.HermSp.CohU

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V}

theorem gdet_ne_of_ratio {r : ℕ} {f f₁ f₂ : Fin (r + 1) → V} {T T' : F} (h1G : H.Gdet f f₁ T T' ≠ 0)
    (h2u : IsUnit (H.Dl f f₂ (r + 1)))
    (hrat : H.Dl f f₁ r * H.Dl f f₂ (r + 1) = H.Dl f f₂ r * H.Dl f f₁ (r + 1)) : H.Gdet f f₂ T T' ≠ 0 := by
  intro h0
  apply h1G
  have hr' := congrArg M.L.cj hrat
  simp only [map_mul] at hr'
  have key : H.normE (H.Dl f f₁ (r + 1)) * H.Gdet f f₂ T T' =
      H.normE (H.Dl f f₂ (r + 1)) * H.Gdet f f₁ T T' := by
    unfold HermSp.Gdet HermSp.normE
    linear_combination (algebraMap F E (T * T') * (M.L.cj (H.Dl f f₁ r) * M.L.cj (H.Dl f f₂ (r + 1)))) * hrat +
      (algebraMap F E (T * T') * H.Dl f f₂ r * H.Dl f f₁ (r + 1)) * hr'
  rw [h0, mul_zero] at key
  have hu : IsUnit (H.normE (H.Dl f f₂ (r + 1))) := h2u.mul (h2u.map M.L.cj)
  exact (hu.mul_right_eq_zero).1 key.symm

end Formalism.MainNotions.S.Loc.HermSp.CohU

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open CohCut

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem gdl_full (x y : Fin (D.R.rS + 1) → (VS D).V) :
    Formalism.L2.SG.Pf.ScalarFramePf.GDl x y (D.R.rS + 1) = (Formalism.L2.SG.Pf.ScalarFramePf.GZ x y).det := by
  unfold Formalism.L2.SG.Pf.ScalarFramePf.GDl
  rw [dite_eq_left le_rfl]
  have hc : (Fin.castLE (le_refl (D.R.rS + 1)) : Fin (D.R.rS + 1) → Fin (D.R.rS + 1)) = id :=
    funext fun i => Fin.ext rfl
  rw [hc, Matrix.submatrix_id_id]

theorem local_discriminant_unit_of_det (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (hZ : ZhatL (lf D F0) F'₂ = Z) (hdet : Z.det ≠ 0) :
    IsUnit ((locH Zd p).Dl (tLoc Zd p γ).f (locF' Zd p F'₂) (D.R.rS + 1)) := by
  have e : (locH Zd p).Dl (tLoc Zd p γ).f (locF' Zd p F'₂) (D.R.rS + 1) =
      (∏ i : Fin (D.R.rS + 1), (Zd.M p).L.cj (sgnP D p (Fin.castLE le_rfl i) * frFac Zd.δ p (Fin.castLE le_rfl i))) *
        (∏ i : Fin (D.R.rS + 1), (sgnP' D p (Fin.castLE le_rfl i) * frFac Zd.δ p (Fin.castLE le_rfl i))) *
        (D.s.atP p).ιE (Formalism.L2.SG.Pf.ScalarFramePf.GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1)) :=
    Formalism.L2.SG.Pf.ScalarFramePf.dl_loc (Z := Zd) (p := p) (frame (lf D F0)) (frame F'₂)
      (fun a => sgnP D p a * frFac Zd.δ p a) (fun b => sgnP' D p b * frFac Zd.δ p b) (D.R.rS + 1) le_rfl
  rw [e]
  have hGZ : Formalism.L2.SG.Pf.ScalarFramePf.GZ (frame (lf D F0)) (frame F'₂) = Z := by
    rw [← hZ]; ext a b; rfl
  have hne : Formalism.L2.SG.Pf.ScalarFramePf.GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1) ≠ 0 := by
    rw [gdl_full, hGZ]; exact hdet
  refine IsUnit.mul (IsUnit.mul ?_ ?_) (Formalism.L2.SG.Pf.BBTie.bt_iota_unit p hne)
  · exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
      (fun i _ => (Formalism.L2.SG.Pf.ScalarFramePf.isUnit_sF Zd p _).map (Zd.M p).L.cj)
  · exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
      (fun i _ => Formalism.L2.SG.Pf.ScalarFramePf.isUnit_sF' Zd p _)

theorem cohDG_holds : CohDG Zd u u' F0 what₂ := by
  intro _ γ Z F'₂ φ' hH
  refine Set.finite_empty.subset fun p hp => ?_
  have hdet : Z.det ≠ 0 := (starMinors_holds u u' F0 what₂ γ Z hH.1).1
  have hu := local_discriminant_unit_of_det Zd p γ Z F'₂ hH.2.1 hdet
  have T1 := hH.2.2.2 p
  exact absurd ⟨hu, Formalism.MainNotions.S.Loc.HermSp.CohU.gdet_ne_of_ratio T1.1.1.2.2.2.2.1 hu T1.2.2.2.1.2.2.2.2.2⟩ hp

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefPhase
noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Steps

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def PhaseAtRep : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : PairVal.MatR D),
    γ.relevant → γ.generic → PairVal.NormRep γ w F' L U →
    (Function.mulSupport fun p => phL M δ (D.mem u).A.T (D.mem u').A.T p w
      (CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p)).Finite ∧
    PairVal.phasePair (gS D) L U = ∏ᶠ p, phL M δ (D.mem u).A.T (D.mem u').A.T p w
      (CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p)

def PhaseLoc : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : PairVal.MatR D),
    γ.relevant → γ.generic → PairVal.NormRep γ w F' L U → ∀ p : PlF D,
    phL M δ (D.mem u).A.T (D.mem u').A.T p w (CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p) =
      (D.s.atP p).psiE ((D.s.atP p).ιE (-((PairVal.sgLo L + PairVal.sgUp U) / ((gS D : ℕ) : D.host.E))))

end Steps


variable (D : Formalism.BasicNotions.D7) in
def PsiProdE : Prop :=
  ∀ x : D.host.E,
    (Function.mulSupport fun p : PlF D => (D.s.atP p).psiE ((D.s.atP p).ιE x)).Finite ∧
    ∏ᶠ p : PlF D, (D.s.atP p).psiE ((D.s.atP p).ιE x) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ D.host.E x : ℚ) : ℂ))

section Assembly

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
  {δ : ∀ p : PlF D, (D.s.atP p).Fp} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem trace_neg_div (E : Type) [Field E] [NumberField E] (s : E) (g : ℕ) :
    Algebra.trace ℚ E (-(s / (g : E))) = -(Algebra.trace ℚ E s / (g : ℚ)) := by
  have hg : ((g : ℕ) : E) = algebraMap ℚ E (g : ℚ) := by simp
  rw [hg, div_eq_mul_inv, ← map_inv₀, mul_comm, ← Algebra.smul_def, map_neg, LinearMap.map_smul, smul_eq_mul]
  ring

theorem phaseAtRep_of (hL : PhaseLoc M δ u u' F0 what₂) (hP : PsiProdE D) : PhaseAtRep M δ u u' F0 what₂ := by
  intro γ w F' L U hrel hgen hN
  have hfun : (fun p => phL M δ (D.mem u).A.T (D.mem u').A.T p w
      (CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * sgnP p)) = fun p =>
      (D.s.atP p).psiE ((D.s.atP p).ιE (-((PairVal.sgLo L + PairVal.sgUp U) / ((gS D : ℕ) : D.host.E)))) :=
    funext (hL γ w F' L U hrel hgen hN)
  rw [hfun]
  obtain ⟨hf, hp⟩ := hP (-((PairVal.sgLo L + PairVal.sgUp U) / ((gS D : ℕ) : D.host.E)))
  refine ⟨hf, ?_⟩
  rw [hp, trace_neg_div, map_add (f := _)]
  unfold PairVal.phasePair PairVal.psiInf
  rw [← Complex.exp_neg, ← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phaseProd_of (hrows : IsRowReps D F0 what₂) (hN : PairVal.NormRepExists D u u' F0 what₂)
    (hW : PairVal.PhaseWellDef D u u' F0 what₂) (hR : PhaseAtRep M δ u u' F0 what₂) : PhaseProd M δ u u' F0 what₂ := by
  intro γ w hγ
  have hrel := PCount.eligRel_holds γ w hγ
  have hex := normRepElig_of hN γ w hγ
  have hz : zT γ = ZhatL (lf D F0) hex.choose.2.1 := by
    unfold zT nrep
    rw [dite_eq_left hex]
  have hpt : ptT γ = hex.choose.1 := by
    unfold ptT nrep
    rw [dite_eq_left hex]
  have hw : hex.choose.1 = w := hpt.symm.trans (FCount.ptT_eq hN hrows hγ hrel)
  have h0 : PairVal.NormRep γ w hex.choose.2.1 hex.choose.2.2.1 hex.choose.2.2.2 := by
    have := hex.choose_spec
    rw [hw] at this
    exact this
  obtain ⟨hf, hp⟩ := hR γ w _ _ _ hrel hγ.1.1 h0
  have hyT : ∀ p, yT M δ u u' F0 what₂ γ p =
      CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) hex.choose.2.1) * sgnP p := fun p => by
    unfold yT; rw [hz]
  simp only [hyT]
  refine ⟨hf, ?_⟩
  refine Eq.trans ?_ hp
  have hex1 : ∃ x : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E) × PairVal.MatR D × PairVal.MatR D,
      PairVal.NormRep γ w x.1 x.2.1 x.2.2 := ⟨(hex.choose.2.1, hex.choose.2.2.1, hex.choose.2.2.2), h0⟩
  unfold PairVal.phaseAt
  rw [dite_eq_left hex1]
  exact hW γ w hrel _ _ _ _ _ _ hex1.choose_spec h0

end Assembly

end Formalism.L2.SG.Pf.Coef
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupLift
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.TupLift

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.Pf.TupOrb

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem frame_li {T : E} (F : LFlag S r T) (hT : T ≠ 0) : LinearIndependent E (frame F) := by
  show LinearIndependent E (Fin.snoc (α := fun _ => S.V) F.fl.e F.fl.z)
  rw [linearIndependent_finSnoc]
  refine ⟨F.fl.e_indep, fun hz => ?_⟩
  have h0 : ∀ x ∈ Submodule.span E (Set.range F.fl.e), S.hT x F.fl.z = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      exact F.fl.z_orth a
    | zero => simp
    | add x y _ _ hx hy => simp [map_add (f := _), hx, hy]
    | smul c x _ hx => simp [hx]
  have := h0 _ hz
  rw [F.fl.z_norm] at this
  exact hT (neg_eq_zero.1 this)

theorem nlam_frame_locP {g : ℕ} {Λ : Submodule (𝓞 E) S.V} {T' : E} {F₁ : LFlag S r T'}
    (hL : IsLift Λ F₁) (hC : IsFixedConv Λ g F₁) {m : S.V ≃ₗ[E] S.V} (hm : m ∈ NLam Λ F₁)
    (P : HeightOneSpectrum (𝓞 E)) (hg : (g : 𝓞 E) ∈ P.asIdeal) (b : Fin (r + 1)) :
    m (frame F₁ b) ∈
      (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 E) (Set.range (frame F₁)))) := by
  have := P.isPrime
  have hA : Formalism.L2.SG.Pf.Apart Λ F₁ ≤
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 E) (Set.range (frame F₁))) := by
    refine sup_le ?_ ?_
    · exact Formalism.L2.SG.Pf.Act.xlam_le_locP Λ g hC P hg (fun a =>
        Formalism.L2.SG.Pf.le_locP' _ _ (Submodule.subset_span ⟨a.castSucc, Formalism.L2.SG.Pf.frame_castSucc_td F₁ a⟩))
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Formalism.L2.SG.Pf.le_locP' _ _
        (Submodule.subset_span ⟨Fin.last _, (Formalism.L2.SG.Pf.frame_last_td F₁).trans hL.2.symm⟩)
  have h0 := Formalism.L2.SG.Pf.frame_mem_locP_Apart hL hC P hg b
  have h1' : m (frame F₁ b) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.L2.SG.Pf.Apart Λ F₁) := by
    rw [← Formalism.L2.SG.Pf.NLam_Apart hm hL, Formalism.L2.SG.Pf.gmap_locP]
    exact (Formalism.L2.SG.Pf.gmap_apply_mem m _ _).2 h0
  exact Formalism.L2.SG.Pf.locP_le_locP' hA h1'

theorem coef_int {g : ℕ} {Λ : Submodule (𝓞 E) S.V} {T' : E} {F₁ : LFlag S r T'} (hT : T' ≠ 0)
    (hL : IsLift Λ F₁) (hC : IsFixedConv Λ g F₁) {m : S.V ≃ₗ[E] S.V} (hm : m ∈ NLam Λ F₁)
    {U : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hU : ∀ b, m (frame F₁ b) = ∑ c, U c b • frame F₁ c)
    (P : HeightOneSpectrum (𝓞 E)) (hg : (g : 𝓞 E) ∈ P.asIdeal) (b : Fin (r + 1)) :
    ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∀ c, ∃ o : 𝓞 E, (s : E) * U c b = (o : E) := by
  have := P.isPrime
  obtain ⟨s, hs, hsm⟩ := nlam_frame_locP hL hC hm P hg b
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 hsm
  refine ⟨s, hs, fun c => ⟨o c, ?_⟩⟩
  have hli := frame_li F₁ hT
  have h1 : ∑ c, ((s : E) * U c b) • frame F₁ c = (s : E) • m (frame F₁ b) := by
    rw [hU b, Finset.smul_sum]
    simp only [mul_smul]
  have h2 : ∑ c, ((o c : 𝓞 E) : E) • frame F₁ c = (s : E) • m (frame F₁ b) := by
    rw [← Formalism.L2.SG.Pf.smul_O, ← ho]
    simp only [Formalism.L2.SG.Pf.smul_O]
  have hsum : ∑ c, ((s : E) * U c b - (o c : E)) • frame F₁ c = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, h1, h2, sub_self]
  exact sub_eq_zero.1 ((Fintype.linearIndependent_iff.1 hli) _ hsum c)

theorem modG_lift {g : ℕ} {Λ : Submodule (𝓞 E) S.V} {T T' : E} {F : LFlag S r T} {F₁ : LFlag S r T'}
    (hT : T' ≠ 0) (hL : IsLift Λ F₁) (hC : IsFixedConv Λ g F₁) (hFΛ : ∀ c, frame F c ∈ Λ)
    {ν m : S.V ≃ₗ[E] S.V} (hν : IsAutLam S Λ ν) (hm : m ∈ NLam Λ F₁)
    {U U' : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hνF : ∀ b, ν (frame F b) = ∑ c, U c b • frame F c) (hmF : ∀ b, m (frame F₁ b) = ∑ c, U' c b • frame F₁ c)
    (hTie : ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ c b, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧
      ∃ o : 𝓞 E, (s : E) * (U c b - U' c b) = (g : E) * o)
    (h1 : ∀ c, ModG S Λ g (frame F₁ c - frame F c)) (b : Fin (r + 1)) :
    ModG S Λ g (ν⁻¹ (m (frame F₁ b)) - frame F b) := by
  intro P hg
  have := P.isPrime
  have key : m (frame F₁ b) - ν (frame F b) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ) := by
    rw [hmF b, hνF b, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ (fun c _ => ?_)
    have e : U' c b • frame F₁ c - U c b • frame F c =
        U' c b • (frame F₁ c - frame F c) + (U' c b - U c b) • frame F c := by
      rw [smul_sub, sub_smul]; abel
    rw [e]
    refine Submodule.add_mem _ ?_ ?_
    · obtain ⟨s, hs, ho⟩ := coef_int hT hL hC hm hmF P hg b
      obtain ⟨o, hoc⟩ := ho c
      obtain ⟨t, ht, htx⟩ := h1 c P hg
      refine ⟨t * s, P.asIdeal.primeCompl.mul_mem ht hs, ?_⟩
      have eq : (t * s) • (U' c b • (frame F₁ c - frame F c)) = o • (t • (frame F₁ c - frame F c)) := by
        rw [Formalism.L2.SG.Pf.smul_O, Formalism.L2.SG.Pf.smul_O, Formalism.L2.SG.Pf.smul_O, smul_smul, smul_smul]
        congr 1
        push_cast
        rw [← hoc]
        ring
      rw [eq]
      exact Submodule.smul_mem _ o htx
    · obtain ⟨s, hs, o, ho⟩ := hTie P hg c b
      refine ⟨s, hs, ?_⟩
      have eq : s • ((U' c b - U c b) • frame F c) = -(o • ((g : 𝓞 E) • frame F c)) := by
        rw [Formalism.L2.SG.Pf.smul_O, Formalism.L2.SG.Pf.smul_O, Formalism.L2.SG.Pf.smul_O, smul_smul, smul_smul, ← neg_smul]
        congr 1
        have : (s : E) * (U' c b - U c b) = -((s : E) * (U c b - U' c b)) := by ring
        rw [this, ho]
        push_cast
        ring
      rw [eq]
      exact Submodule.neg_mem _ (Submodule.smul_mem _ o
        (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (hFΛ c)))
  have hinv : IsAutLam S Λ ν⁻¹ := Formalism.L2.SG.Pf.isAutLam_inv hν
  have e : ν⁻¹ (m (frame F₁ b)) - frame F b = ν⁻¹ (m (frame F₁ b) - ν (frame F b)) := by
    rw [map_sub]
    simp [LinearEquiv.coe_inv]
  rw [e]
  have eN : Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ) =
      Formalism.HermitianLatticesTheory.gmap ν⁻¹ (Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ)) := by
    rw [← Formalism.L2.SG.Pf.gmap_locP, Formalism.L2.SG.Pf.gmap_ideal_smul, hinv.2]
  rw [eN]
  exact (Formalism.L2.SG.Pf.gmap_apply_mem ν⁻¹ _ _).2 key

theorem zhat_lift {T T' : E} (F : LFlag S r T) (F₁ : LFlag S r T') {ν m : S.V ≃ₗ[E] S.V}
    (hiso : ∀ x y, S.hT (ν x) (ν y) = S.hT x y) {U U' : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hνF : ∀ b, ν (frame F b) = ∑ c, U c b • frame F c) (hmF : ∀ b, m (frame F₁ b) = ∑ c, U' c b • frame F₁ c)
    (a b : Fin (r + 1)) :
    S.hT (frame F a) (ν⁻¹ (m (frame F₁ b))) = (U.conjTranspose * ZhatL F F₁ * U') a b := by
  have e : S.hT (frame F a) (ν⁻¹ (m (frame F₁ b))) = S.hT (ν (frame F a)) (m (frame F₁ b)) := by
    rw [← hiso (frame F a) (ν⁻¹ (m (frame F₁ b)))]
    simp [LinearEquiv.coe_inv]
  rw [e, hνF a, hmF b]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, ZhatL, Zhat, brS, map_sum, map_smulₛₗ,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, starRingEnd_apply]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  simp only [RingHom.id_apply]
  ring

end Gen

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def NLamOnto : Prop :=
  ∀ (D : D7) (w : D.what₂.Word) (G : FlagG (VS D) D.R.rS ((Tu D w : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D G Λ → Tu D w ≠ 0 → ∀ U : PairVal.MatR D, IsUpUni U → TupGlob.IntFr U →
      ∃ ν ∈ NLam Λ (lf D G), ∀ b, ν (frame (lf D G) b) = ∑ c, U c b • frame (lf D G) c

variable {D : D7}

theorem isRowLat_of_pd {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : IsRowLat D F0 Λ)
    {F₁ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)} (hp : PD D Λ (lf D F0) u' F₁) :
    IsRowLat D F₁.fl Λ :=
  ⟨hΛ.1, ⟨hΛ.2.1.1, hΛ.2.1.2.1, ⟨hp.1.1, rfl⟩, hp.2.2.1⟩, hp.2.2.2⟩

theorem repAtTup_of (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
    (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
    (hG : TupGlob.GlobMove D M δ u u') (hO : NLamOnto) : FibPart.RepAtTup M δ u u' F0 what₂ := by
  intro hpre γ w hGw Z hZ hel htup
  have hΛ : IsRowLat D F0 γ.lam := hpre.2.2.2.2.1.1 γ.lam γ.mem
  have hrel : γ.relevant := hpre.2.2.2.2.2 γ w hel
  obtain ⟨x, hx⟩ := hpre.2.2.2.1 γ w hel.2 hrel hel.1.1
  have hex : ∃ y : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) ×
      PairVal.MatR D × PairVal.MatR D, PairVal.NormRep γ y.1 y.2.1 y.2.2.1 y.2.2.2 :=
    ⟨(w, x.1, x.2.1, x.2.2), hx⟩
  have hz : LsDatumB.zT γ = ZhatL (lf D F0) hex.choose.2.1 := by
    simp only [LsDatumB.zT, LsDatumB.nrep, dif_pos hex]
  have hspec := hex.choose_spec
  generalize hex.choose = y at hz hspec
  obtain ⟨w₁, F₁, L₁, U₁⟩ := y
  obtain ⟨⟨p₁, e₁⟩, hadm₁, -⟩ := hspec
  simp only at hz
  have hEq := Formalism.L2.SG.Closed.TermEqIff_holds D u u' F0 γ.lam hΛ
  have hFun := Formalism.L2.SG.Closed.TermFun_holds D u u' F0 γ.lam hΛ
  obtain ⟨Fa, ⟨pa, ea⟩, hGa, hcell⟩ := hel.2
  have hdca := (hEq ⟨Fa, pa⟩ ⟨F₁, p₁⟩).1 (ea.trans e₁.symm)
  change DCRel γ.lam (lf D F0) Fa F₁ at hdca
  have hG₁ : Gval (lf D F0) F₁ ≠ 0 := fun h =>
    hGa ((Formalism.L2.SG.Pf.gval_rel (lf D F0) hdca).symm.trans h)
  have hcell₁ : IsInCell (ZhatOM (ZhatL (lf D F0) F₁)) w := (hFun.2.1 ⟨Fa, pa⟩ ⟨F₁, p₁⟩ hdca w).1 hcell
  obtain ⟨Fg, ⟨pg, eg⟩, hgen⟩ := hel.1.1
  have hgen₁ : IsGeneric γ.lam (gS D) (lf D F0) F₁ :=
    (hFun.2.2.2.1 ⟨Fg, pg⟩ ⟨F₁, p₁⟩ ((hEq ⟨Fg, pg⟩ ⟨F₁, p₁⟩).1 (eg.trans e₁.symm))).1 hgen
  have hAt₁ : PCount.AtMat w (ZhatL (lf D F0) F₁) := hcell₁
  have htup' : ∀ p, PCount.tupZ M δ u u' (ZhatL (lf D F0) F₁) p = PCount.tupZ M δ u u' Z p := fun p => by
    rw [← hz]; exact congrFun htup p
  obtain ⟨U, U', hU, hU', hiU, hiU', htie, hZeq⟩ := hG w _ Z hGw hAt₁ hZ htup'
  obtain ⟨ν, hν, hνF⟩ := hO D u F0 γ.lam hΛ hpre.2.2.1.1.ne_zero U hU hiU
  obtain ⟨m, hm, hmF⟩ := hO D u' F₁.fl γ.lam (isRowLat_of_pd hΛ p₁) hpre.2.2.1.2.2.1.ne_zero U' hU' hiU'
  have hm' : m ∈ NLam γ.lam F₁ := hm
  have hmF' : ∀ b, m (frame F₁ b) = ∑ c, U' c b • frame F₁ c := hmF
  have hAut : IsAutLam (VS D) γ.lam (ν⁻¹ * m) :=
    Formalism.L2.SG.Pf.isAutLam_mul (Formalism.L2.SG.Pf.isAutLam_inv hν.1) hm.1
  let F2 := Formalism.L2.SG.Saturated.mapL (ν⁻¹ * m) hAut.1 F₁
  have hf2 : ∀ b, frame F2 b = ν⁻¹ (m (frame F₁ b)) := fun b => by
    rw [Formalism.L2.SG.Saturated.frame_mapL]; rfl
  have hdc : DCRel γ.lam (lf D F0) F₁ F2 :=
    ⟨ν⁻¹, Formalism.L2.SG.Pf.nlamPf_inv hν, m, hm', hf2, rfl⟩
  have pd2 : PD D γ.lam (lf D F0) u' F2 :=
    Formalism.L2.SG.Closed.TermStable_holds D u u' F0 γ.lam hΛ ⟨F₁, p₁⟩ F2 hdc
  have hT' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hpre.2.2.1.2.2.1.ne_zero
  have hFΛ : ∀ c, frame (lf D F0) c ∈ γ.lam := by
    intro c
    refine Fin.lastCases ?_ (fun a => ?_) c
    · rw [Formalism.L2.SG.Pf.frame_last_td]; exact hΛ.2.1.2.2.1.1
    · rw [Formalism.L2.SG.Pf.frame_castSucc_td]; exact PI.NRL.e_mem_lam D F0 γ.lam hΛ a
  have hiso : ∀ x y, (VS D).hT (ν x) (ν y) = (VS D).hT x y :=
    ((Formalism.L2.SG.Pf.isAutLam_iff γ.lam ν).1 hν.1).1
  have hent : ∀ a b, (VS D).hT (frame (lf D F0) a) (frame F2 b) =
      (U.conjTranspose * ZhatL (lf D F0) F₁ * U') a b := fun a b => by
    rw [hf2 b]; exact zhat_lift (lf D F0) F₁ hiso hνF hmF' a b
  refine ⟨F2, ⟨⟨pd2.1, pd2.2.1, ?_⟩, ?_, ?_, pd2.2.2, ?_⟩,
    pd2, (Quot.sound (show TermDef.Rel γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') ⟨F₁, p₁⟩ ⟨F2, pd2⟩ from hdc)).symm.trans e₁⟩
  · rw [Formalism.L2.SG.Pf.gval_rel (lf D F0) hdc]; exact hG₁
  · refine ⟨fun a b hab => Matrix.one_apply_ne (ne_of_lt hab).symm, fun a => Matrix.one_apply_eq a, fun b => ?_⟩
    rw [frameAct_one', hf2 b]
    exact modG_lift hT' p₁.1 p₁.2.2.1 hFΛ hν.1 hm' hνF hmF' htie
      (fun c => by have := hadm₁.2.2 c; rwa [frameAct_one'] at this) b
  · exact (hFun.2.2.2.1 ⟨F₁, p₁⟩ ⟨F2, pd2⟩ hdc).1 hgen₁
  · have hZZ : ZhatL (lf D F0) F2 = U.conjTranspose * ZhatL (lf D F0) F₁ * U' := by
      funext a b
      exact hent a b
    rw [hZeq]
    exact hZZ

end D7

end Formalism.L2.SG.Pf.TupLift
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaID
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : Formalism.BasicNotions.D7)

def SpanOm : Prop :=
  ∀ {T T' : D.host.E} (F : FlagG (VS D) D.R.rS T) (F' : FlagG (VS D) D.R.rS T'),
    (Zhat F F').det ≠ 0 → Gflag F F' ≠ 0 →
    ∀ m ∈ orth (VS D) F'.X, ∃ x' ∈ F'.X, ∃ w ∈ orth (VS D) (F.Xplus ⊔ F'.Xplus), ∃ a b : D.host.E,
      m = x' + w + a • F'.z + b • Gom F.fvec F'.fvec

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end
