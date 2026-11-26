module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaK
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXLeaves

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIB
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIA
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BetaI

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdNP

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

section Frame

variable (p : PlF D) {T' : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T')

theorem locF'_eq (b : Fin (D.R.rS + 1)) : locF' Zd p G b = sF' Zd p b • baseChange₂ D p (frame G b) := rfl

theorem bcP_frameG (b : Fin (D.R.rS + 1)) :
    baseChange₂ D p (frame G b) = (((isUnit_sF' Zd p b).unit⁻¹ : ((D.s.atP p).Ep)ˣ) : (D.s.atP p).Ep) • locF' Zd p G b := by
  rw [locF'_eq, smul_smul, (isUnit_sF' Zd p b).val_inv_mul, one_smul]

theorem frame_csG (i : Fin D.R.rS) : frame G i.castSucc = G.fl.e i := by
  simp [frame, FlagG.fvec]

theorem frame_lastG : frame G (Fin.last D.R.rS) = G.fl.z := by
  simp [frame, FlagG.fvec]

theorem sF'_last : sF' Zd p (Fin.last D.R.rS) = 1 := by
  unfold sF'
  rw [frFac_last' Zd p, mul_one]
  unfold TermLoc.sgnP'
  split
  · exact sgnP_last p
  · simp

theorem locF'_last : locF' Zd p G (Fin.last D.R.rS) = baseChange₂ D p G.fl.z := by
  rw [locF'_eq, sF'_last, one_smul, frame_lastG]

theorem bcP_X' {x : (VS D).V} (hx : x ∈ Xsp G) : baseChange₂ D p x ∈ (locH Zd p).X (locF' Zd p G) := by
  change x ∈ Submodule.span D.host.E (Set.range G.fl.e) at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [← frame_csG, bcP_frameG Zd p G]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c x _ hx => rw [Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]; exact Submodule.smul_mem _ _ hx

theorem baseChangeAt_perp' {m : (VS D).V} (hm : m ∈ orth (VS D) (Xsp G)) :
    baseChange₂ D p m ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p G)) := by
  show ∀ w ∈ (locH Zd p).X (locF' Zd p G), (locH Zd p).h (baseChange₂ D p m) w = 0
  intro w hw
  rw [h_eq]
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    simp only
    rw [locF'_eq, frame_csG, LocFacts.localForm_smul_right, ← h_eq, localForm_baseChange,
      (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hm _ (Submodule.subset_span ⟨i, rfl⟩), map_zero, mul_zero]
  | zero => exact LocFacts.localForm_zero_right Zd p _
  | add a b _ _ ha hb => rw [LocFacts.localForm_add_right, ha, hb, add_zero]
  | smul c w _ hw => rw [LocFacts.localForm_smul_right, hw, mul_zero]

end Frame

theorem coef_intG {T' : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T') {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hprim : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ) (locF' Zd p G)) (c : Fin (D.R.rS + 1) → D.host.E)
    (hc : ∑ a, c a • frame G a ∈ Λ) : IsIntegral ℤ (c (Fin.last D.R.rS)) := by
  refine int_of_loc Zd fun p => ?_
  set m := ∑ a, c a • frame G a with hm
  have hbm : baseChange₂ D p m = ∑ a, ((D.s.atP p).ιE (c a) *
      ((((isUnit_sF' Zd p a).unit⁻¹ : ((D.s.atP p).Ep)ˣ)) : (D.s.atP p).Ep)) • locF' Zd p G a := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hm, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂, bcP_frameG Zd p G, smul_smul]
  have hspan : baseChange₂ D p m ∈ Submodule.span (D.s.atP p).Ep (Set.range (locF' Zd p G)) := by
    rw [hbm]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have h2 := (hprim p).2.2 _ (baseChange_mem_localLattice Zd hc p) hspan
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h2
  have hli := (hprim p).2.1
  have hz : ∑ a, (((o a : (Zd.M p).L.O) : (D.s.atP p).Ep) -
      (D.s.atP p).ιE (c a) * ((((isUnit_sF' Zd p a).unit⁻¹ : ((D.s.atP p).Ep)ˣ)) : (D.s.atP p).Ep)) •
        locF' Zd p G a = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← hbm, ← ho]
    simp only [sub_eq_zero]
    rfl
  have h3 := Fintype.linearIndependent_iff.1 hli _ hz (Fin.last D.R.rS)
  have key : ∀ {a : (D.s.atP p).Ep} (h : IsUnit a), a = 1 →
      (((h.unit⁻¹ : ((D.s.atP p).Ep)ˣ)) : (D.s.atP p).Ep) = 1 := by
    intro a h ha
    subst ha
    have : h.unit = 1 := Units.ext (IsUnit.unit_spec h)
    rw [this, inv_one, Units.val_one]
  have hone := key (isUnit_sF' Zd p (Fin.last D.R.rS)) (sF'_last Zd p)
  rw [hone, mul_one, sub_eq_zero] at h3
  rw [← h3]
  exact (o (Fin.last D.R.rS)).2

theorem exists_yG {T' : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T') {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ : Submodule.IsLattice D.host.E Λ) (hSD : BwdNA.SD (VS D) Λ)
    (hprim : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ) (locF' Zd p G)) (hzX : G.fl.z ∉ Xsp G) :
    ∃ y ∈ Λ, y ∈ orth (VS D) (Xsp G) ∧ (VS D).hT y G.fl.z = 1 := by
  obtain ⟨f, hfz, hfX⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hzX inferInstance
  let ρ : Module.Dual D.host.E (VS D).V := (f G.fl.z)⁻¹ • f
  have hρz : ρ G.fl.z = 1 := by
    simp only [ρ, LinearMap.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hfz
  have hρX : ∀ x ∈ Xsp G, ρ x = 0 := fun x hx => by
    have h1 : f x ∈ (Xsp G).map f := ⟨x, hx, rfl⟩
    rw [hfX, Submodule.mem_bot] at h1
    simp only [ρ, LinearMap.smul_apply, smul_eq_mul, h1, mul_zero]
  have hρe : ∀ i : Fin D.R.rS, ρ (frame G i.castSucc) = 0 := fun i => by
    rw [frame_csG]; exact hρX _ (Submodule.subset_span ⟨i, rfl⟩)
  have hρl : ρ (frame G (Fin.last D.R.rS)) = 1 := by
    rw [frame_lastG, hρz]
  obtain ⟨v, hv⟩ := BwdNA.riesz (VS D) ρ
  let U : Submodule D.host.E (VS D).V := Submodule.span D.host.E (Set.range (frame G))
  have hint : ∀ m ∈ Λ, m ∈ U → IsIntegral ℤ ((VS D).hT m v) := fun m hm hmU => by
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hmU
    have hρm : ρ m = c (Fin.last D.R.rS) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hc, map_sum, Fin.sum_univ_castSucc]
      simp only [map_smul, smul_eq_mul, hρe, mul_zero, Finset.sum_const_zero, zero_add, hρl, mul_one]
    rw [BwdNA.hsw (VS D) v m, hv, hρm]
    exact BwdNA.isInt_star (coef_intG Zd G hprim c (by rw [hc]; exact hm))
  obtain ⟨w, hwΛ, hvw⟩ := BwdNA.dual_sum (VS D) Λ hΛ hSD U v hint
  have hw : ∀ a, (VS D).hT w (frame G a) = ρ (frame G a) := fun a => by
    have h0 := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hvw _ (Submodule.subset_span ⟨a, rfl⟩)
    rw [map_sub, sub_eq_zero] at h0
    rw [BwdNA.hsw (VS D) (frame G a) w, ← h0, ← BwdNA.hsw (VS D) (frame G a) v, hv]
  refine ⟨w, hwΛ, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => ?_, ?_⟩
  · change x ∈ Submodule.span D.host.E (Set.range G.fl.e) at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [BwdNA.hsw (VS D) w (G.fl.e i), ← frame_csG, hw, hρe, star_zero]
    | zero => simp
    | add a b _ _ ha hb => rw [map_add (f := _), LinearMap.add_apply, ha, hb, add_zero]
    | smul c x _ hx => rw [BwdNA.hT_smulL, hx, mul_zero]
  · rw [← frame_lastG, hw, hρl]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BetaI
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut BwdBetaCut BwdNP BetaI

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

def LsetB : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), BHyp Zd u u' F0 what₂ γ Z F'₂ φ φ' Λ₂ →
    ∀ β₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V, β₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
      (∀ b, β₀ (frame (repF γ) b) = frame (liftF F'₂) b) →
      W0₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) β₀ → OmB (lf D F0) (repF γ) (liftF F'₂) β₀ →
      ∀ (p : PlF D) (m : (VS D).V), m ∈ γ.lam → m ∈ orth (VS D) (Xsp (repF γ)) →
        ∃ x ∈ lattice₂ D Zd.M p Λ₂, baseChange₂ D p (β₀ m) - x ∈ (locH Zd p).X (locF' Zd p F'₂)

def IotaB : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), BHyp Zd u u' F0 what₂ γ Z F'₂ φ φ' Λ₂ →
    ∀ β₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V, β₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
      (∀ b, β₀ (frame (repF γ) b) = frame (liftF F'₂) b) →
      W0₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) β₀ → OmB (lf D F0) (repF γ) (liftF F'₂) β₀ →
      ∀ v : (VS D).V ≃ₗ[D.host.E] (VS D).V, v ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
        (∀ b, v (frame (liftF F'₂) b) = frame (liftF F'₂) b) →
        (∀ y ∈ orth (VS D) (Xsp (liftF F'₂)), v y - y ∈ Xsp (liftF F'₂)) →
        Formalism.HermitianLatticesTheory.gmap (v * β₀) γ.lam = Λ₂ → IotaC₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) (v * β₀)

variable {u u' F0 what₂}

namespace BetaI

theorem isLattice_gmap' (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) {L : Submodule (𝓞 D.host.E) (VS D).V}
    (hL : Submodule.IsLattice D.host.E L) : Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap g L) := by
  refine ⟨hL.fg.map _, ?_⟩
  have e : ((Formalism.HermitianLatticesTheory.gmap g L : Submodule (𝓞 D.host.E) (VS D).V) : Set (VS D).V) =
      (g : (VS D).V →ₗ[D.host.E] (VS D).V) '' (L : Set (VS D).V) := rfl
  exact fun _ _ hli => (LinearIndependent.iff_fractionRing _ _).mp hli

theorem sd_gmap (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hSD : BwdNA.SD (VS D) Λ) : BwdNA.SD (VS D) (Formalism.HermitianLatticesTheory.gmap β Λ) := by
  intro x
  rw [Formalism.L2.SG.Saturated.mem_gmap_iff]
  constructor
  · intro hx y hy
    rw [Formalism.L2.SG.Saturated.mem_gmap_iff] at hy
    have h1 := (hSD _).1 hx _ hy
    have e := hβ (β.symm y) (β.symm x)
    simp only [LinearEquiv.apply_symm_apply] at e
    rwa [e]
  · intro h
    refine (hSD _).2 fun y hy => ?_
    have h1 := h (β y) (by rw [Formalism.L2.SG.Saturated.mem_gmap_iff]; simpa using hy)
    have e := hβ y (β.symm x)
    simp only [LinearEquiv.apply_symm_apply] at e
    rwa [e] at h1

end BetaI

theorem betaInt_of (hLs : LsetB Zd u u' F0 what₂) (hIo : IotaB Zd u u' F0 what₂) : BetaInt Zd u u' F0 what₂ := by
  intro γ Z F'₂ φ φ' Λ₂ hB β₀ hiso hfr hW hO
  have hB0 := hB
  obtain ⟨hC, -, hS, hΛ₂, -, hT, hPD, -⟩ := hB
  obtain ⟨hΛ₂full, hloc₂⟩ := hΛ₂
  obtain ⟨-, hT2, -⟩ := hS
  have hrow := hC.2.1.1 γ.lam γ.mem
  have hΛfull : Submodule.IsFullLattice D.host.E γ.lam := hrow.1.1
  have hΛlat := hΛfull.toIsLattice
  have hΛ₂lat := hΛ₂full.toIsLattice
  have hSDl : ∀ p, (locH Zd p).IsSelfDual (lattice₂ D Zd.M p γ.lam) := fun p => (hT2 p).1.1.1
  have hSDl₂ : ∀ p, (locH Zd p).IsSelfDual (lattice₂ D Zd.M p Λ₂) := fun p => (hloc₂ p).1.1.1
  have hpr₂ : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ₂) (locF' Zd p F'₂) := fun p => (hloc₂ p).1.1.2.2.1.1
  have hSD := sd_of_loc Zd hΛfull hSDl
  have hSD₂ := sd_of_loc Zd hΛ₂full hSDl₂
  have hXiso : ∀ x ∈ Xsp (liftF F'₂), ∀ y ∈ Xsp (liftF F'₂), (VS D).hT x y = 0 :=
    fun x hx y hy => NMoveP.hT_X_X F'₂.fl hx hy
  have hzX : F'₂.fl.z ∈ orth (VS D) (Xsp (liftF F'₂)) := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => by
    rw [BwdNA.hsw (VS D) F'₂.fl.z x]
    have h := NMoveP.hT_f_X F'₂.fl (Fin.last D.R.rS) hx
    rw [NMoveP.fvecL] at h
    rw [h, star_zero]
  have hznot : F'₂.fl.z ∉ Xsp (liftF F'₂) := by
    intro h
    have h0 := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hzX F'₂.fl.z h
    rw [F'₂.fl.z_norm, neg_eq_zero] at h0
    exact (D.mem u').A.T_prime.ne_zero (Nat.cast_eq_zero.1 h0)
  have hXo := BwdNA.X_le_orth (VS D) (Xsp (liftF F'₂)) hXiso
  have hXX : ∀ {w : (VS D).V}, w ∈ orth (VS D) (orth (VS D) (Xsp (liftF F'₂))) → w ∈ Xsp (liftF F'₂) :=
    fun {w} hw => BwdNA.mem_of_orth_orth (VS D) _ fun v hv => by
      rw [BwdNA.hsw (VS D) v w, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hw v hv, star_zero]
  have hXX' : ∀ {w : (VS D).V}, w ∈ orth (VS D) (orth (VS D) (Xsp (repF γ))) → w ∈ Xsp (repF γ) :=
    fun {w} hw => BwdNA.mem_of_orth_orth (VS D) _ fun v hv => by
      rw [BwdNA.hsw (VS D) v w, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hw v hv, star_zero]
  have hXmap : (Xsp (repF γ)).map (β₀ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp (liftF F'₂) :=
    BwdBetaCut.Xsp_of_frame β₀ _ _ hfr
  have hsymmX : ∀ x ∈ Xsp (liftF F'₂), β₀.symm x ∈ Xsp (repF γ) := fun x hx => by
    rw [← hXmap] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hy
  have hmapX : ∀ x ∈ Xsp (repF γ), β₀ x ∈ Xsp (liftF F'₂) := fun x hx => by
    rw [← hXmap]; exact Submodule.mem_map_of_mem hx

  have hΛ₁lat := BetaI.isLattice_gmap' β₀ hΛlat
  have hSD₁ := BetaI.sd_gmap β₀ hiso hSD

  have he : ∀ a, β₀ ((repF γ).fl.e a) = F'₂.fl.e a := BwdBetaCut.e_of_frame β₀ (repF γ) (liftF F'₂) hfr
  have hXS : Formalism.HermitianLatticesTheory.gmap β₀ (XS D (repF γ).fl) = XS D F'₂.fl := by
    unfold Formalism.HermitianLatticesTheory.gmap XS
    rw [Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨w, ⟨a, x, hx, rfl⟩, rfl⟩
      exact ⟨a, x, hx, by simp [he]⟩
    · rintro ⟨a, x, hx, rfl⟩
      exact ⟨x • (repF γ).fl.e a, ⟨a, x, hx, rfl⟩, by simp [he]⟩
  have hFO₂ : XLam Λ₂ (liftF F'₂) = XS D F'₂.fl := hT.2.2.2.2
  have hFO : XLam γ.lam (repF γ) = XS D (repF γ).fl := hPD.2.2.2
  have hXm : ∀ x ∈ Xsp (liftF F'₂), x ∈ Λ₂ ↔ x ∈ Formalism.HermitianLatticesTheory.gmap β₀ γ.lam := fun x hx => by
    have h1 : x ∈ Λ₂ ↔ x ∈ XLam Λ₂ (liftF F'₂) :=
      ⟨fun h => Submodule.mem_inf.2 ⟨h, hx⟩, fun h => (Submodule.mem_inf.1 h).1⟩
    have h2 : x ∈ Formalism.HermitianLatticesTheory.gmap β₀ γ.lam ↔ β₀.symm x ∈ XLam γ.lam (repF γ) := by
      rw [Formalism.L2.SG.Saturated.mem_gmap_iff]
      exact ⟨fun h => Submodule.mem_inf.2 ⟨h, hsymmX x hx⟩, fun h => (Submodule.mem_inf.1 h).1⟩
    rw [h1, h2, hFO₂, hFO, ← hXS, Formalism.L2.SG.Saturated.mem_gmap_iff]

  have hzβ : β₀ (repF γ).fl.z = F'₂.fl.z := by
    have := hfr (Fin.last _)
    rwa [BwdBetaCut.fvec_last', BwdBetaCut.fvec_last'] at this
  have hz₁ : F'₂.fl.z ∈ Formalism.HermitianLatticesTheory.gmap β₀ γ.lam := by
    rw [Formalism.L2.SG.Saturated.mem_gmap_iff, ← hzβ, LinearEquiv.symm_apply_apply]
    exact hPD.1.1
  have hz₂ : F'₂.fl.z ∈ Λ₂ := hT.1.1.1

  have hL : ∀ x ∈ Λ₂, x ∈ orth (VS D) (Xsp (liftF F'₂)) →
      ∃ y ∈ Formalism.HermitianLatticesTheory.gmap β₀ γ.lam, y - x ∈ Xsp (liftF F'₂) := fun x hx hxo => by
    obtain ⟨w, hw, hxw⟩ := BwdNA.dual_sum (VS D) γ.lam hΛlat hSD (orth (VS D) (Xsp (repF γ))) (β₀.symm x)
      (fun m hm hmo => by
        have e := hiso m (β₀.symm x)
        rw [LinearEquiv.apply_symm_apply] at e
        rw [← e]
        refine int_of_loc Zd fun p => ?_
        rw [← localForm_baseChange]
        obtain ⟨x₁, hx₁, hd⟩ := hLs γ Z F'₂ φ φ' Λ₂ hB0 β₀ hiso hfr hW hO p m hm hmo
        have e2 : baseChange₂ D p (β₀ m) = x₁ + (baseChange₂ D p (β₀ m) - x₁) := by abel
        rw [e2, Formalism.L2.SG.Pf.ScalarFramePf.h_add_right (locH Zd p),
          (show (locH Zd p).h (baseChange₂ D p x) (baseChange₂ D p (β₀ m) - x₁) = 0 from baseChangeAt_perp' Zd p F'₂ hxo _ hd), add_zero]
        exact ((hSDl₂ p).2.2 (baseChange₂ D p x)).1 (baseChange_mem_localLattice Zd hx p) x₁ hx₁)
    refine ⟨β₀ w, (Formalism.L2.SG.Saturated.mem_gmap_iff _ _ _).2 (by simpa using hw), ?_⟩
    have h2 := hmapX _ (hXX' hxw)
    have e : β₀ w - x = -(β₀ (β₀.symm x - w)) := by
      rw [map_sub, LinearEquiv.apply_symm_apply]; abel
    rw [e]
    exact (Xsp (liftF F'₂)).neg_mem h2
  have hL' : ∀ y ∈ Formalism.HermitianLatticesTheory.gmap β₀ γ.lam, y ∈ orth (VS D) (Xsp (liftF F'₂)) →
      ∃ x ∈ Λ₂, x ∈ orth (VS D) (Xsp (liftF F'₂)) ∧ y - x ∈ Xsp (liftF F'₂) := fun y hy hyo => by
    rw [Formalism.L2.SG.Saturated.mem_gmap_iff] at hy
    have hmo : β₀.symm y ∈ orth (VS D) (Xsp (repF γ)) := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => by
      have e := hiso x (β₀.symm y)
      rw [LinearEquiv.apply_symm_apply] at e
      rw [← e]
      exact (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hyo _ (hmapX x hx)
    obtain ⟨w, hw, hyw⟩ := BwdNA.dual_sum (VS D) Λ₂ hΛ₂lat hSD₂ (orth (VS D) (Xsp (liftF F'₂))) y
      (fun m₂ hm₂ hm₂o => by
        refine int_of_loc Zd fun p => ?_
        rw [← localForm_baseChange]
        obtain ⟨x₁, hx₁, hd⟩ := hLs γ Z F'₂ φ φ' Λ₂ hB0 β₀ hiso hfr hW hO p _ hy hmo
        rw [LinearEquiv.apply_symm_apply] at hd
        have e2 : baseChange₂ D p y = x₁ + (baseChange₂ D p y - x₁) := by abel
        rw [e2, (locH Zd p).h_add_left]
        have h0 : (locH Zd p).h (baseChange₂ D p y - x₁) (baseChange₂ D p m₂) = 0 := by
          rw [(locH Zd p).h_herm, (show (locH Zd p).h (baseChange₂ D p m₂) (baseChange₂ D p y - x₁) = 0 from
            baseChangeAt_perp' Zd p F'₂ hm₂o _ hd), map_zero]
        rw [h0, add_zero]
        exact ((hSDl₂ p).2.2 x₁).1 hx₁ (baseChange₂ D p m₂) (baseChange_mem_localLattice Zd hm₂ p))
    have hX1 := hXX hyw
    refine ⟨w, hw, ?_, hX1⟩
    have e : w = y - (y - w) := by abel
    rw [e]
    exact (orth (VS D) (Xsp (liftF F'₂))).sub_mem hyo (hXo hX1)
  have hy := exists_yG Zd F'₂ hΛ₂lat hSD₂ hpr₂ hznot
  have htr : ∃ c : D.host.E, IsIntegral ℤ c ∧ c + star c = 1 := by
    obtain ⟨c, hc⟩ := D.host.exists_trace_one
    refine ⟨(c : D.host.E), RingOfIntegers.isIntegral_coe c, ?_⟩
    rw [Formalism.BasicNotions.Examples₂.star_eq_conj (H := D.host)]
    exact hc
  obtain ⟨n, hniso, hnX, hnz, hno, himg⟩ := BwdNA.main (VS D) (Xsp (liftF F'₂)) hXiso F'₂.fl.z hzX
    (Formalism.HermitianLatticesTheory.gmap β₀ γ.lam) Λ₂ hΛ₁lat hΛ₂lat hSD₁ hSD₂ hXm hz₁ hz₂ hL hL' hy htr
  have hnI : n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hniso
  have hvI : n.symm ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := (Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hnI
  have hvf : ∀ b, n.symm (frame (liftF F'₂) b) = frame (liftF F'₂) b := by
    intro b
    rw [LinearEquiv.symm_apply_eq]
    refine Fin.lastCases ?_ (fun i => ?_) b
    · rw [BwdBetaCut.fvec_last']; exact hnz.symm
    · rw [BwdBetaCut.fvec_cs']; exact (hnX _ (Submodule.subset_span ⟨i, rfl⟩)).symm
  have hvX : ∀ y ∈ orth (VS D) (Xsp (liftF F'₂)), n.symm y - y ∈ Xsp (liftF F'₂) := by
    intro y hy
    have hy'o : n.symm y ∈ orth (VS D) (Xsp (liftF F'₂)) := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => by
      have e := hniso x (n.symm y)
      rw [hnX x hx, LinearEquiv.apply_symm_apply] at e
      rw [← e]
      exact (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hy x hx
    have h1 := hno _ hy'o
    rw [LinearEquiv.apply_symm_apply] at h1
    have e : n.symm y - y = -(y - n.symm y) := by abel
    rw [e]
    exact (Xsp (liftF F'₂)).neg_mem h1
  have hgm : Formalism.HermitianLatticesTheory.gmap (n.symm * β₀) γ.lam = Λ₂ := by
    ext x
    rw [Formalism.L2.SG.Saturated.mem_gmap_iff]
    have e : (n.symm * β₀).symm x = β₀.symm (n x) := by
      rw [LinearEquiv.symm_apply_eq]
      show x = n.symm (β₀ (β₀.symm (n x)))
      simp
    rw [e, ← Formalism.L2.SG.Saturated.mem_gmap_iff]
    constructor
    · intro h
      have h' : n x ∈ (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) := by rw [himg]; exact h
      obtain ⟨y, hy, hyx⟩ := h'
      rw [← n.injective hyx]
      exact hy
    · intro h
      have h' : n x ∈ (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) := ⟨x, h, rfl⟩
      rw [himg] at h'
      exact h'
  exact ⟨n.symm, hvI, hvf, hvX, hgm, hIo γ Z F'₂ φ φ' Λ₂ hB0 β₀ hiso hfr hW hO n.symm hvI hvf hvX hgm⟩

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut BwdBetaCut BwdNP BetaI

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

namespace BetaI

theorem xi_inv_last (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)
    (F' : LFlag (D.sp.Y 0) D.R.rS T') (i : Fin D.R.rS) :
    (admXi D Λ F F')⁻¹ (Fin.last D.R.rS) i.castSucc = 0 := by
  obtain ⟨h1, h2⟩ := admissibility_witness_unitriangular Λ F F'
  have hbt : (admXi D Λ F F').BlockTriangular id := fun i j hij => h1 i j hij
  have hdet : (admXi D Λ F F').det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hbt]; simp [h2]
  haveI : Invertible (admXi D Λ F F') := Matrix.invertibleOfIsUnitDet _ (by rw [hdet]; exact isUnit_one)
  exact Matrix.blockTriangular_inv_of_blockTriangular hbt (Fin.castSucc_lt_last i)

theorem frameAct_mem {T' : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T')
    (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)) (i : Fin D.R.rS)
    (h : ξ (Fin.last D.R.rS) i.castSucc = 0) : frameAct (frame G) ξ i.castSucc ∈ Xsp G := by
  show ∑ a, ((ξ a i.castSucc : 𝓞 D.host.E) : D.host.E) • frame G a ∈ Xsp G
  rw [Fin.sum_univ_castSucc, h]
  refine add_mem (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_) (by simp)
  rw [frame_csG]
  exact Submodule.subset_span ⟨j, rfl⟩

theorem tf' (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) (b : Fin (D.R.rS + 1)) :
    (tLoc Zd p γ).f' b = (TermLoc.sgnP' D p b * frFac Zd.δ p b) •
      baseChange₂ D p (frameAct (frame (repF γ)) (admXi D γ.lam (lf D F0) (repF γ))⁻¹ b) := rfl

theorem bcP_perp_f' (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) {m : (VS D).V}
    (hm : m ∈ orth (VS D) (Xsp (repF γ))) :
    baseChange₂ D p m ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f') := by
  show ∀ w ∈ (locH Zd p).X (tLoc Zd p γ).f', (locH Zd p).h (baseChange₂ D p m) w = 0
  intro w hw
  rw [h_eq]
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    simp only
    rw [tf', LocFacts.localForm_smul_right, ← h_eq, localForm_baseChange,
      (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hm _
        (frameAct_mem _ _ i (xi_inv_last γ.lam (lf D F0) (repF γ) i)), map_zero, mul_zero]
  | zero => exact LocFacts.localForm_zero_right Zd p _
  | add a b _ _ ha hb => rw [LocFacts.localForm_add_right, ha, hb, add_zero]
  | smul c w _ hw => rw [LocFacts.localForm_smul_right, hw, mul_zero]

end BetaI

variable (u u' F0 what₂)

def PinB : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), BHyp Zd u u' F0 what₂ γ Z F'₂ φ φ' Λ₂ →
    ∀ β₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V, β₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
      (∀ b, β₀ (frame (repF γ) b) = frame (liftF F'₂) b) →
      W0₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) β₀ → OmB (lf D F0) (repF γ) (liftF F'₂) β₀ →
      ∀ (p : PlF D) (m : (VS D).V) (hm : baseChange₂ D p m ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f'))
        (hm₂ : baseChange₂ D p (β₀ m) ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂))),
        m ∈ orth (VS D) (Xsp (repF γ)) →
        φ' p ((locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p m, hm⟩) =
          (locH Zd p).mkW (locF' Zd p F'₂) ⟨baseChange₂ D p (β₀ m), hm₂⟩

variable {u u' F0 what₂}

theorem lsetB_of (hP : PinB Zd u u' F0 what₂) : LsetB Zd u u' F0 what₂ := by
  intro γ Z F'₂ φ φ' Λ₂ hB β₀ hiso hfr hW hO p m hm hmo
  have hloc := hB.2.2.2.1.2 p
  have hL' := hloc.2.2.2.1
  have hmp := bcP_perp_f' Zd p γ hmo
  have hXmap := BwdBetaCut.Xsp_of_frame β₀ _ _ hfr
  have hmo₂ : β₀ m ∈ orth (VS D) (Xsp (liftF F'₂)) := by
    rw [← hXmap, Formalism.L2.SG.Pf.orth_map_sat β₀ hiso]
    exact Submodule.mem_map_of_mem hmo
  have hmp₂ := baseChangeAt_perp' Zd p F'₂ hmo₂
  have hin : (locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p m, hmp⟩ ∈
      (locH Zd p).Lset (tLoc Zd p γ).abelian₂ (tLoc Zd p γ).f' := ⟨⟨_, hmp⟩, baseChange_mem_localLattice Zd hm p, rfl⟩
  obtain ⟨x, hxΛ, hxe⟩ := hL'.subset ⟨_, hin, rfl⟩
  rw [hP γ Z F'₂ φ φ' Λ₂ hB β₀ hiso hfr hW hO p m hmp hmp₂ hmo] at hxe
  refine ⟨(x : Vp D p), hxΛ, ?_⟩
  have := (Submodule.Quotient.eq _).1 hxe.symm
  simpa using this

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
