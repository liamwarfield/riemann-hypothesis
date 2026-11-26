module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelGroupTransportUniformisationComponent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UsedRunUniformisationComponentsShareCmData
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UsedRunUniformisationComponentsShareCmData
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem comps_share : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∀ k k' : (uAt r v i).Comp, ((uAt r v i).X k).Ψ = ((uAt r v i).X k').Ψ ∧ ((uAt r v i).X k).p0 = ((uAt r v i).X k').p0 ∧ ((uAt r v i).X k).Gm = ((uAt r v i).X k').Gm ∧ ((uAt r v i).X k).ξ0 = ((uAt r v i).X k').ξ0 := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ r h _ i v k k'
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hL := (h.laws v).j
  have hg := (r.used v).full.toCore.good_σ₀
  have hU := hL.unf _ hj _ hg
  obtain ⟨hr, hm⟩ := hL.modelW _ hj _ hg
  refine ⟨?_, ((hU.2.1 k).1.trans (hU.2.1 k').1.symm), ((hm k).1.trans (hm k').1.symm),
    ((hm k).2.trans (hm k').2.symm)⟩
  ext τ
  exact ((hU.2.1 k).2 τ).trans ((hU.2.1 k').2 τ).symm

end GlobalTheory.ShareOn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UsedRunUniformisationComponentsShareCmDataStatement
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_components_share_cmData : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∀ k k' : (uAt r v i).Comp, ((uAt r v i).X k).Ψ = ((uAt r v i).X k').Ψ ∧ ((uAt r v i).X k).p0 = ((uAt r v i).X k').p0 ∧ ((uAt r v i).X k).Gm = ((uAt r v i).X k').Gm ∧ ((uAt r v i).X k).ξ0 = ((uAt r v i).X k').ξ0 := by
  first | exact @GlobalTheory.ShareOn.comps_share | exact GlobalTheory.ShareOn.comps_share | (intros; apply GlobalTheory.ShareOn.comps_share <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UsedRunUniformisationCharacterTrivialArithmeticG
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UsedRunUniformisationCharacterTrivialArithmeticG
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem uAt_chi_eq_one : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∀ (k : (uAt r v i).Comp) (la : Wt ((uAt r v i).X k).Ψ D.R.r), ∀ γ ∈ ((uAt r v i).X k).Γ, ((uAt r v i).X k).χ la γ = 1 := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ r h _ i v k la γ hγ
  exact GlobalTheory.OneEmbeddingProbe.chi_eq_one (uAt r v i)
    (fun a n hd k γ hγ => (h.laws v).p.chiTriv ((i : ℕ) + 1) ⟨Nat.le_add_left _ _, i.2⟩ _
      (r.used v).full.toCore.good_σ₀ a n hd k γ hγ) k la γ hγ

end GlobalTheory.ShareOn

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UsedRunUniformisationCharacterTrivialArithmeticGStatement
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_character_trivial_arithmeticGroup : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∀ (k : (uAt r v i).Comp) (la : Wt ((uAt r v i).X k).Ψ D.R.r), ∀ γ ∈ ((uAt r v i).X k).Γ, ((uAt r v i).X k).χ la γ = 1 := by
  first | exact @GlobalTheory.ShareOn.uAt_chi_eq_one | exact GlobalTheory.ShareOn.uAt_chi_eq_one | (intros; apply GlobalTheory.ShareOn.uAt_chi_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePreservedByComponentStabilizer
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePreservedByComponentStabilizer
set_option autoImplicit false

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

theorem natCast_mem_half {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) : (l.M : 𝓞 E) ∈ l.Mb := by
  have h2 : (l.M : 𝓞 E) ∈ Ideal.span {(l.M : 𝓞 E)} := Ideal.mem_span_singleton_self _
  rw [← l.prod] at h2
  exact Ideal.mul_le_left (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) h2

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cong

variable {E : Type} [Field E] {r : ℕ} {Ψ : Finset (E →+* ℂ)}

theorem lact_mul_lact (a b : GL (Fin r) E) (x : Frame Ψ r) : lact (a * b) x = lact a (lact b x) := by
  funext τ
  simp only [lact, Units.val_mul, Matrix.map_mul]
  exact Matrix.mul_assoc _ _ _

theorem lact_rmul_comm (a : GL (Fin r) E) (x b : Frame Ψ r) : lact a (rmul x b) = rmul (lact a x) b := by
  funext τ
  show (a : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ) =
    ((a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) * mat b τ
  rw [Matrix.mul_assoc]

theorem lact_one_frame (x : Frame Ψ r) : lact (1 : GL (Fin r) E) x = x := by
  funext τ
  simp only [lact, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  rfl

end Cong


set_option maxHeartbeats 1000000 in
theorem sub_mem_half_smul_latP : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∀ (k : (uAt r v i).Comp), ∀ γ ∈ ((uAt r v i).X k).Γ, ∀ w ∈ lattice₂ D ((uAt r v i).X k).Λ, Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w - w ∈ p.T.Q.l.Mb • lattice₂ D ((uAt r v i).X k).Λ := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ r h _ i v k γ hγ w hw
  have hL := (h.laws v).p.toLawsCore
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hσ := (r.used v).full.toCore.good_σ₀
  obtain ⟨-, hA, -, -, -, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D _ hL.pins
  have hU := (Formalism.L2.PjFree.isUnf_ofPj _).2 (hL.unf _ hj _ hσ)
  obtain ⟨th, hrk, hth, hD⟩ := hL.dictU _ hj _ hσ
  obtain ⟨⟨x0, hx0, -⟩, -⟩ := hD.2.2
  obtain ⟨η, hηU, hηc, b, hb, hx⟩ := GlobalTheory.T.exists_principal_congruence_back_triangular_frame _ _ _ _ _ _ _ _ _ hσ hU hA (hnum _ hj).2.1 k γ hγ (x0 k) (hx0 k).1
  have hηΓ : η ∈ ((uAt r v i).X k).Γ :=
    GlobalTheory.PrincCore.hasPrinc_core D _ hL _ hj _ hσ k η hηU hηc
  have hmem : (η * γ)⁻¹ ∈ ((uAt r v i).X k).Γ := inv_mem (mul_mem hηΓ hγ)
  have hfix : lact (η * γ)⁻¹ (x0 k) = rmul (x0 k) b := by
    calc lact (η * γ)⁻¹ (x0 k) = lact (η * γ)⁻¹ (rmul (lact η (lact γ (x0 k))) b) := congrArg _ hx
      _ = rmul (lact (η * γ)⁻¹ (lact η (lact γ (x0 k)))) b := lact_rmul_comm _ _ _
      _ = rmul (lact ((η * γ)⁻¹ * (η * γ)) (x0 k)) b := by
        rw [lact_mul_lact ((η * γ)⁻¹) (η * γ), lact_mul_lact η γ]
      _ = rmul (x0 k) b := by rw [inv_mul_cancel, lact_one_frame]
  have h1 := ((uAt r v i).X k).Γ_free _ hmem (x0 k) (hx0 k).1 b hb hfix
  have hγη : γ = η⁻¹ := by
    rw [inv_eq_one] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hγU := ((uAt r v i).X k).Γ_stab γ hγ

  have hcong : ∀ u ∈ ((uAt r v i).X k).Λ, ∃ y ∈ ((uAt r v i).X k).Λ,
      Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) u - u = ((r.used v).full.Q.l.M : D.host.E) • y := by
    intro u hu
    obtain ⟨y, hy, he⟩ := hηc (Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) u) ((hγU.2 u).1 hu)
    have hηγ : Matrix.mulVec (η : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E)
        (Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) u) = u := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, hγη, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    refine ⟨-y, ((uAt r v i).X k).Λ.neg_mem hy, ?_⟩
    rw [hηγ] at he
    rw [smul_neg, ← he]
    abel

  have hM0 : ((r.used v).full.Q.l.M : D.host.E) ≠ 0 := by
    have := (r.used v).full.Q.l.three_le
    exact_mod_cast (show (r.used v).full.Q.l.M ≠ 0 by omega)
  obtain ⟨z, hz⟩ : ∃ z : Fin D.R.r → D.host.E, z = ((r.used v).full.Q.l.M : D.host.E)⁻¹ •
      (Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w - w) := ⟨_, rfl⟩
  have hzP : z ∈ lattice₂ D ((uAt r v i).X k).Λ := by
    refine mem_latP.2 fun a ha => ?_
    obtain ⟨y, hy, he⟩ := hcong (a • w) (mem_latP.1 hw a ha)
    have : a • z = y := by
      rw [hz, smul_comm, smul_sub, ← Matrix.mulVec_smul, he, smul_smul, inv_mul_cancel₀ hM0, one_smul]
    rw [this]
    exact hy
  have hMmem : ((r.used v).full.Q.l.M : 𝓞 D.host.E) ∈ (r.used v).full.Q.l.Mb := natCast_mem_half _
  have hfin : Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w - w =
      ((r.used v).full.Q.l.M : 𝓞 D.host.E) • z := by
    rw [hz, ← algebraMap_smul D.host.E, smul_smul, map_natCast, mul_inv_cancel₀ hM0, one_smul]
  rw [hfin]
  exact Submodule.smul_mem_smul hMmem hzP

end GlobalTheory.ShareOn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePreservedByComponentStabilizerStatement
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_preserved_by_component_stabilizer : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∀ (k : (uAt r v i).Comp), ∀ γ ∈ ((uAt r v i).X k).Γ, ∀ w ∈ lattice₂ D ((uAt r v i).X k).Λ, Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w - w ∈ p.T.Q.l.Mb • lattice₂ D ((uAt r v i).X k).Λ := by
  first | exact @GlobalTheory.ShareOn.sub_mem_half_smul_latP | exact GlobalTheory.ShareOn.sub_mem_half_smul_latP | (intros; apply GlobalTheory.ShareOn.sub_mem_half_smul_latP <;> assumption)
end
end

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Build

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem exists_runModel (p : PtAt ex Csz) (hm : More p) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (ho : OwnPin r)
    (i : Fin D.R.m) : ∃ (C : Type) (_ : Finite C) (_ : MulAction p.P.Gp C) (M : TwoLevels D.host.E D.R.r p.P.Gp C)
      (ka : Wt M.Ψ D.R.r), RunModel p r h i M ka := by
  classical
  obtain ⟨v⟩ := nonempty_place D
  have hne : Nonempty (uAt r v i).Comp := GlobalTheory.ModelLatticeCheck.comp_nonempty _ _ _
  have hcom := GlobalTheory.T.uniformisation_components_share_cmData p hm r h ho i v
  have hchi := GlobalTheory.T.uniformisation_character_trivial_arithmeticGroup p hm r h ho i v
  have hcong := GlobalTheory.T.lattice_preserved_by_component_stabilizer p hm r h ho i v
  obtain ⟨act, tr, h1, hmul, hmt, hconj, hcoc, hfaith, ⟨a, ha⟩, hd2⟩ := GlobalTheory.T.exists_levelGroup_transport_uniformisation_components p hm r h ho i v
  choose Xx hXd hXL using exists_dataX_latP p r h i v
  have hΓ : ∀ c, (Xx c).Γ = ((uAt r v i).X c).Γ := fun c => congrArg Data.Γ (hXd c)
  have hΛ : ∀ c, (Xx c).Λ = ((uAt r v i).X c).Λ := fun c => congrArg Data.Λ (hXd c)
  let k0 : (uAt r v i).Comp := hne.some
  letI inst : MulAction p.P.Gp (uAt r v i).Comp := { smul := act, one_smul := h1, mul_smul := hmul }
  let M : TwoLevels D.host.E D.R.r p.P.Gp (uAt r v i).Comp :=
    { Ψ := ((uAt r v i).X k0).Ψ
      Gm := ((uAt r v i).X k0).Gm
      p0 := ((uAt r v i).X k0).p0
      ξ0 := ((uAt r v i).X k0).ξ0
      comp := Xx
      comp_Ψ := fun c => (congrArg Data.Ψ (hXd c)).trans (hcom c k0).1
      comp_Gm := fun c => (congrArg Data.Gm (hXd c)).trans (hcom c k0).2.2.1
      comp_basePoint := fun c => (congrArg Data.p0 (hXd c)).trans (hcom c k0).2.1
      comp_ξ0 := fun c => (congrArg Data.ξ0 (hXd c)).trans (hcom c k0).2.2.2
      χ_one := fun c => chi_one_of_toData (Xx c) _ (hXd c) (hchi c)
      Γ_L' := fun c γ hγ w => by
        rw [hXL c]
        rw [hΓ c] at hγ
        exact mem_localLattice_iff_mulVec D _ (((uAt r v i).X c).Γ_stab γ hγ).2 w
      tr := tr
      tr_herm := fun u c w w' => by
        have e := (hmt u c).iso w w'
        rw [(hcom (act u c) k0).2.2.1, (hcom c k0).2.2.1] at e
        exact e
      tr_Λ := fun u c w => by
        rw [hΛ c, hΛ (u • c)]
        exact (hmt u c).lat w
      tr_L' := fun u c w => by
        rw [hXL c, hXL (u • c)]
        exact mem_localLattice_iff_mulVec D _ (hmt u c).lat w
      tr_conj := fun u c γ => by
        rw [hΓ c, hΓ (u • c)]
        exact hconj u c γ
      tr_mul := fun u u' c => by
        rw [hΓ]
        exact hcoc u u' c
      tr_faithful := fun u c hu ht => hfaith u c hu (by rw [hΓ c] at ht; exact ht) }
  let ka : Wt M.Ψ D.R.r := fun τ j => laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) k0 τ j
  refine ⟨(uAt r v i).Comp, inferInstance, inst, M, ka, v, Equiv.refl _, fun c => hXd c, ?_, ⟨a, ?_⟩, ?_, ?_⟩
  · intro c τ h1 h2 j
    show laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) k0 ⟨τ, h1⟩ j = laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) c ⟨τ, h2⟩ j
    unfold laR laU
    rw [(hcom c k0).2.1]
  · intro F g c x hx h1 h2
    have hx' : castFrame h1 x ∈ ((uAt r v i).X c).dom := by
      show castFrame h1 x ∈ GG ((uAt r v i).X c).Ψ ((uAt r v i).X c).Gm ((uAt r v i).X c).p0
      rw [(hcom c k0).2.2.1, (hcom c k0).2.1]
      exact fun τ => hx ⟨τ.1, by rw [h1]; exact τ.2⟩
    have e := ha F g c (castFrame h1 x) hx' (h1.symm.trans h2)
    exact e
  · intro c γ hγ w hw
    rw [hXL c] at hw ⊢
    rw [hΓ c] at hγ
    exact hcong c γ hγ w hw
  · exact hd2 (fun c => (Xx c).L') hXL

end Build

end GlobalTheory.ShareOn

end
