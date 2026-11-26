module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarGlob
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfH

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohLp
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarIdentPf
noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLoc

section Generic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)

theorem ident_generic {r : ℕ} (Lam₁ Lam₂ : Submodule M.L.O V) (f₀ f₁ f₂ : Fin (r + 1) → V) (T T' : F)
    (e : V ≃ₗ[E] V) (hiso : ∀ v w, H.h (e v) (e w) = H.h v w)
    (h12 : ∀ x ∈ H.X f₁, e x ∈ H.X f₂) (h21 : ∀ y ∈ H.X f₂, e.symm y ∈ H.X f₁)
    (hX0 : ∀ a ∈ H.X f₀, ∀ b ∈ H.X f₀, H.h a b = 0) (hX2 : ∀ a ∈ H.X f₂, ∀ b ∈ H.X f₂, H.h a b = 0)
    (hW0 : ∀ w ∈ H.W0 f₀ f₁, ∃ w₂ ∈ H.W0 f₀ f₂, w - w₂ ∈ H.X f₀ ∧ e w - w₂ ∈ H.X f₂)
    (homp : H.Dl f₀ f₂ (r + 1) • H.om' f₀ f₁ - H.Dl f₀ f₁ (r + 1) • H.om' f₀ f₂ ∈ H.X f₀)
    (hom : M.L.cj (H.Dl f₀ f₂ (r + 1)) • e (H.om f₀ f₁) - M.L.cj (H.Dl f₀ f₁ (r + 1)) • H.om f₀ f₂ ∈ H.X f₂)
    (hrat : H.Dl f₀ f₁ r * H.Dl f₀ f₂ (r + 1) = H.Dl f₀ f₂ r * H.Dl f₀ f₁ (r + 1))
    (hz : e (f₁ (Fin.last r)) - f₂ (Fin.last r) ∈ H.X f₂) :
    H.Ident (⟨Lam₁, f₀, f₁, T, T'⟩ : Loc.Term V M r) ⟨Lam₂, f₀, f₂, T, T'⟩ (LinearEquiv.refl _ _)
        (Formalism.L2.SG.Pf.ScalarFramePf.qEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21) ∧
      H.SendsTo (Formalism.L2.SG.Pf.ScalarFramePf.qEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21).toLinearMap 1 1 (f₁ (Fin.last r)) (f₂ (Fin.last r)) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, hrat⟩, ?_⟩
  · intro x y x₂ y₂ hx hy
    exact h_eq_of_sub_mem H _ hX0 x.2 y.2 ((mk_eq_iff H _ x x₂).1 hx) ((mk_eq_iff H _ y y₂).1 hy)
  · intro x y x₂ y₂ hx hy
    have hx' : e x - x₂ ∈ H.X f₂ := (mk_eq_iff H _ _ x₂).1 hx
    have hy' : e y - y₂ ∈ H.X f₂ := (mk_eq_iff H _ _ y₂).1 hy
    rw [h_eq_of_sub_mem H _ hX2 (perp_map H e hiso _ _ h21 x.2) (perp_map H e hiso _ _ h21 y.2) hx' hy',
      hiso]
  · intro w hw
    obtain ⟨w₂, hw₂, h1, h2⟩ := hW0 w hw
    refine ⟨w₂, hw₂, ?_, ?_⟩
    · intro x x₂ hx hx₂
      apply smul_mk_eq H
      rw [one_smul, one_smul, hx, hx₂]
      exact h1
    · intro x x₂ hx hx₂
      apply smul_mk_eq H
      show (1 : E) • e x - (1 : E) • (x₂ : V) ∈ H.X f₂
      rw [one_smul, one_smul, hx, hx₂]
      exact h2
  · intro x x₂ hx hx₂
    apply smul_mk_eq H
    rw [hx, hx₂]
    exact homp
  · intro x x₂ hx hx₂
    apply smul_mk_eq H
    show M.L.cj (H.Dl f₀ f₂ (r + 1)) • e x - M.L.cj (H.Dl f₀ f₁ (r + 1)) • (x₂ : V) ∈ H.X f₂
    rw [hx, hx₂]
    exact hom
  · intro x x₂ hx hx₂
    apply smul_mk_eq H
    show (1 : E) • e x - (1 : E) • (x₂ : V) ∈ H.X f₂
    rw [one_smul, one_smul, hx, hx₂]
    exact hz

end Generic

section Concrete

variable {D : D7} (Zd : LocDat D) (p : PlF D)

theorem omp_combine' (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V) (P K : (D.s.atP p).Ep) :
    (P * (D.s.atP p).ιE (GDl f g2 (D.R.rS + 1))) • (K • baseChange₂ D p (Gom' f g1)) -
      (P * (D.s.atP p).ιE (GDl f g1 (D.R.rS + 1))) • (K • baseChange₂ D p (Gom' f g2)) =
    (P * K) • baseChange₂ D p (GDl f g2 (D.R.rS + 1) • Gom' f g1 - GDl f g1 (D.R.rS + 1) • Gom' f g2) := by
  rw [map_sub, baseChange_smul₂, baseChange_smul₂, smul_sub, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 2 <;> ring

theorem om_combine' (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V) (β : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (P K : (D.s.atP p).Ep) :
    (Zd.M p).L.cj (P * (D.s.atP p).ιE (GDl f g2 (D.R.rS + 1))) • (K • baseChange₂ D p (β (Gom f g1))) -
      (Zd.M p).L.cj (P * (D.s.atP p).ιE (GDl f g1 (D.R.rS + 1))) • (K • baseChange₂ D p (Gom f g2)) =
    ((Zd.M p).L.cj P * K) • baseChange₂ D p (star (GDl f g2 (D.R.rS + 1)) • β (Gom f g1) -
      star (GDl f g1 (D.R.rS + 1)) • Gom f g2) := by
  rw [map_sub, baseChange_smul₂, baseChange_smul₂, smul_sub, smul_smul, smul_smul, smul_smul, smul_smul, map_mul, map_mul,
    cj_iota (Zd.hcj p), cj_iota (Zd.hcj p)]
  congr 2 <;> ring

theorem betaP_fix {ι : Type} [Fintype ι] (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (u y : ι → (VS D).V)
    (hform : ∀ v, g v = v + ∑ k, (VS D).hT (u k) v • y k) (w : Vp D p)
    (hw : ∀ k, (locH Zd p).h w (baseChange₂ D p (u k)) = 0) : betaP p g w = w := by
  have hk : ∀ k, ∑ i, w i * (D.s.atP p).ιE ((VS D).hT (u k) ((VS D).frame i)) = 0 := by
    intro k
    have e := hw k
    conv_lhs at e => rw [vp_eq_sum p w]
    rw [h_sum_left] at e
    rw [← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hermitian_base_change_smul Zd p]
    rfl
  conv_lhs => rw [vp_eq_sum p w]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul, betaP_bc, hform, map_add (f := _), baseChangeAt_sum, smul_add, Finset.sum_add_distrib, Finset.smul_sum,
    smul_smul]
  rw [← vp_eq_sum p w, Finset.sum_comm]
  simp only [← Finset.sum_smul, hk, zero_smul, Finset.sum_const_zero, add_zero]

theorem gdl_eq (f g : Fin (D.R.rS + 1) → (VS D).V) (l : ℕ) : GDl f g l = leadMinorE (starZh f g) l := by
  unfold GDl leadMinorE
  split_ifs <;> rfl

theorem xspan_eq {T : D.host.E} (F : FlagG (VS D) D.R.rS T) :
    Submodule.span D.host.E (Set.range fun a : Fin D.R.rS => F.fvec a.castSucc) = F.X := by
  have : (fun a : Fin D.R.rS => F.fvec a.castSucc) = F.e := funext fun a => by simp [FlagG.fvec]
  rw [this]; rfl

end Concrete

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLoc

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

def StarIdentU : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    (∀ p, (locH Zd p).IsGeneric (tLoc Zd p γ)) →
    ∀ F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), ZhatL (lf D F0) F'₂ = Z → starCompat γ F'₂ →
      starInU γ F'₂ →
      ∀ p, ∃ φ' : (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂),
        LsDatumA.LocalCountHypotheses (locH Zd p) (tLoc Zd p γ) (tLoc Zd p γ).f (locF' Zd p F'₂) (LinearEquiv.refl _ _) φ'

def StarFrameU : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∃ F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), ZhatL (lf D F0) F'₂ = Z ∧ starCompat γ F'₂ ∧
      starInU γ F'₂

variable {u u' F0 what₂}

theorem starFrameU_holds : StarFrameU u u' F0 what₂ := by
  intro γ Z hC
  obtain ⟨hZ, hZ₁, hx⟩ := starMinors_holds u u' F0 what₂ γ Z hC
  obtain ⟨h1, h2⟩ := star_frame_orthogonal γ
  obtain ⟨F₂, hZh, hom, hsp⟩ := FsLA.frame_la F0 (starFrame γ) h1 h2 Z hZ hZ₁ hx
  refine ⟨⟨F₂, F₂.z⟩, hZh, ⟨?_, ?_⟩, fun b => hsp b⟩
  · have e : starZh (frame (lf D F0)) (frame (⟨F₂, F₂.z⟩ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))) = Z := hZh
    rw [e, FsLA.leadMinorE_full, FsLA.leadMinorE_full]
    exact hx
  · have e : starZh (frame (lf D F0)) (frame (⟨F₂, F₂.z⟩ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))) = Z := hZh
    rw [FsLA.leadMinorE_full, FsLA.leadMinorE_full, e]
    exact hom

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Zd : LocDat D)

theorem localLattice_preserves_cofinite (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ : Submodule.IsFullLattice D.host.E Λ) :
    {p : PlF D | ¬ ∀ x ∈ lattice₂ D Zd.M p Λ, betaP p g x ∈ lattice₂ D Zd.M p Λ}.Finite := by
  letI := hΛ
  obtain ⟨s, hs⟩ := hΛ.toIsLattice.fg
  refine (s.finite_toSet.biUnion fun v _ => CohIntPf.bcP_mem_cof Zd hΛ (g v)).subset ?_
  intro p hp
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  by_contra hall
  push_neg at hall
  apply hp
  have hloc : ∀ v ∈ Λ, g v ∈ Formalism.HermitianLattices.Ext.L3.locF p.asIdeal Λ := by
    intro v hv
    rw [← hs] at hv
    induction hv using Submodule.span_induction with
    | mem v hv => exact (Formalism.L2.SG.Pf.LocalDenominators.baseChangeAt_mem_localLattice_iff Zd p (Λ := Λ) (by infer_instance) _).1 (hall v hv)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul o x _ hx =>
      rw [show g (o • x) = o • g x from (g : (VS D).V →ₗ[D.host.E] (VS D).V).map_smul_of_tower o x]
      exact Submodule.smul_mem _ _ hx
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    rw [betaP_bc]
    exact (Formalism.L2.SG.Pf.LocalDenominators.baseChangeAt_mem_localLattice_iff Zd p (Λ := Λ) (by infer_instance) _).2 (hloc v hv)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx =>
    rw [Subring.smul_def, map_smul, ← Subring.smul_def]
    exact Submodule.smul_mem _ _ hx

theorem localLattice_preserves_cofinite_symm (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ : Submodule.IsFullLattice D.host.E Λ) :
    {p : PlF D | ¬ ∀ x ∈ lattice₂ D Zd.M p Λ, (betaP p g).symm x ∈ lattice₂ D Zd.M p Λ}.Finite := by
  letI := hΛ
  obtain ⟨s, hs⟩ := hΛ.toIsLattice.fg
  refine (s.finite_toSet.biUnion fun v _ => CohIntPf.bcP_mem_cof Zd hΛ (g.symm v)).subset ?_
  intro p hp
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  by_contra hall
  push_neg at hall
  apply hp
  have hloc : ∀ v ∈ Λ, g.symm v ∈ Formalism.HermitianLattices.Ext.L3.locF p.asIdeal Λ := by
    intro v hv
    rw [← hs] at hv
    induction hv using Submodule.span_induction with
    | mem v hv => exact (Formalism.L2.SG.Pf.LocalDenominators.baseChangeAt_mem_localLattice_iff Zd p (Λ := Λ) (by infer_instance) _).1 (hall v hv)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul o x _ hx =>
      rw [show g.symm (o • x) = o • g.symm x from
        (g.symm : (VS D).V →ₗ[D.host.E] (VS D).V).map_smul_of_tower o x]
      exact Submodule.smul_mem _ _ hx
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    rw [betaP_symm_bc]
    exact (Formalism.L2.SG.Pf.LocalDenominators.baseChangeAt_mem_localLattice_iff Zd p (Λ := Λ) (by infer_instance) _).2 (hloc v hv)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx =>
    rw [Subring.smul_def, map_smul, ← Subring.smul_def]
    exact Submodule.smul_mem _ _ hx

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLoc

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLoc

section Generic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)

theorem lset_map {r : ℕ} (f₁ f₂ : Fin (r + 1) → V) (e : V ≃ₗ[E] V) (hiso : ∀ v w, H.h (e v) (e w) = H.h v w)
    (h12 : ∀ x ∈ H.X f₁, e x ∈ H.X f₂) (h21 : ∀ y ∈ H.X f₂, e.symm y ∈ H.X f₁) (abelian₂ : Submodule M.L.O V)
    (hL : ∀ x ∈ abelian₂, e x ∈ abelian₂) (hL' : ∀ x ∈ abelian₂, e.symm x ∈ abelian₂) :
    ⇑(Formalism.L2.SG.Pf.ScalarFramePf.qEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21) '' H.Lset abelian₂ f₁ = H.Lset abelian₂ f₂ := by
  ext w
  simp only [Set.mem_image]
  constructor
  · rintro ⟨w0, ⟨x, hxL, rfl⟩, rfl⟩
    refine ⟨perpEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21 x, hL _ hxL, ?_⟩
    exact (Formalism.L2.SG.Pf.ScalarFramePf.qEquiv_mk H e hiso _ _ h12 h21 x).symm
  · rintro ⟨y, hyL, rfl⟩
    refine ⟨H.mkW f₁ ((perpEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21).symm y),
      ⟨(perpEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21).symm y, ?_, rfl⟩, ?_⟩
    · have hy : (((perpEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21).symm y : ↥(H.perp (H.X f₁))) : V) =
          e.symm y := by
        simp [perpEquiv, LinearEquiv.ofSubmodules_symm_apply]
      rw [hy]
      exact hL' _ hyL
    · show Formalism.L2.SG.Pf.ScalarFramePf.qEquiv H e hiso _ _ h12 h21
          (Submodule.Quotient.mk ((perpEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21).symm y)) =
        Submodule.Quotient.mk y
      rw [Formalism.L2.SG.Pf.ScalarFramePf.qEquiv_mk, LinearEquiv.apply_symm_apply]

end Generic

section Concrete

variable {D : D7} (Zd : LocDat D) (p : PlF D)

theorem local_beta_mem_x (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (f₁ f₂ : Fin (D.R.rS + 1) → (VS D).V)
    (hg1 : ∀ b, g (f₁ b) = f₂ b) :
    ∀ x ∈ (locH Zd p).X (fun b => sF' Zd p b • baseChange₂ D p (f₁ b)),
      betaP p g x ∈ (locH Zd p).X (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)) := by
  intro x hx
  refine betaP_mem_X (Z := Zd) (p := p) g f₁ f₂ (sF' Zd p) (isUnit_sF' Zd p) ?_ hx
  intro a
  rw [hg1]
  exact Submodule.subset_span ⟨a, rfl⟩

theorem local_beta_symm_mem_x (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (f₁ f₂ : Fin (D.R.rS + 1) → (VS D).V)
    (hg1 : ∀ b, g (f₁ b) = f₂ b) :
    ∀ x ∈ (locH Zd p).X (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)),
      (betaP p g).symm x ∈ (locH Zd p).X (fun b => sF' Zd p b • baseChange₂ D p (f₁ b)) := by
  intro x hx
  refine betaP_symm_mem_X (Z := Zd) (p := p) g f₁ f₂ (sF' Zd p) (isUnit_sF' Zd p) ?_ hx
  intro a
  rw [← hg1, LinearEquiv.symm_apply_apply]
  exact Submodule.subset_span ⟨a, rfl⟩

def starPhi (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hiso : ∀ x y, (VS D).hT (g x) (g y) = (VS D).hT x y)
    (f₁ f₂ : Fin (D.R.rS + 1) → (VS D).V) (hg1 : ∀ b, g (f₁ b) = f₂ b) :
    (locH Zd p).Wb (fun b => sF' Zd p b • baseChange₂ D p (f₁ b)) ≃ₗ[(D.s.atP p).Ep]
      (locH Zd p).Wb (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)) :=
  Formalism.L2.SG.Pf.ScalarFramePf.qEquiv (locH Zd p) (betaP p g) (betaP_iso Zd p g hiso) _ _ (local_beta_mem_x Zd p g f₁ f₂ hg1) (local_beta_symm_mem_x Zd p g f₁ f₂ hg1)

end Concrete

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLoc

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}


set_option maxHeartbeats 1000000 in
theorem starIdentG (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (hC : Ctx γ Z)
    (hgen : ∀ p, (locH Zd p).IsGeneric (tLoc Zd p γ)) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (hZ : ZhatL (lf D F0) F'₂ = Z) (hc : starCompat γ F'₂) (hU : starInU γ F'₂)
    (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (y : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → (VS D).V)
    (hiso : ∀ x x', (VS D).hT (g x) (g x') = (VS D).hT x x') (hg1 : ∀ b, g (starFrame γ b) = frame F'₂ b)
    (hform : ∀ v, g v = v + ∑ k, (VS D).hT (Sum.elim (frame (lf D F0)) (starFrame γ) k) v • y k)
    (hom : star (starZh (frame (lf D F0)) (starFrame γ)).det • starOmL (frame (lf D F0)) (frame F'₂) -
        star Z.det • g (starOmL (frame (lf D F0)) (starFrame γ)) ∈ Xsp F'₂) (p : PlF D) :
    LsDatumA.LocalCountHypotheses (locH Zd p) (tLoc Zd p γ) (tLoc Zd p γ).f (locF' Zd p F'₂) (LinearEquiv.refl _ _)
      (FsLoc.starPhi Zd p g hiso (starFrame γ) (frame F'₂) hg1) := by
  set f := frame (lf D F0) with hf
  set f₁ := starFrame γ with hf₁
  set f₂ := frame F'₂ with hf₂
  set H := locH Zd p with hH
  set e := betaP p g with he
  have hisoL : ∀ v w, H.h (e v) (e w) = H.h v w := betaP_iso Zd p g hiso
  have hgs : ∀ b, g.symm (f₂ b) = f₁ b := fun b => by rw [← hg1 b, LinearEquiv.symm_apply_apply]
  have h12 : ∀ x ∈ H.X (fun b => sF' Zd p b • baseChange₂ D p (f₁ b)), e x ∈ H.X (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)) :=
    fun x hx => betaP_mem_X Zd p g f₁ f₂ (sF' Zd p) (isUnit_sF' Zd p)
      (fun a => by rw [hg1]; exact Submodule.subset_span ⟨a, rfl⟩) hx
  have h21 : ∀ x ∈ H.X (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)), e.symm x ∈ H.X (fun b => sF' Zd p b • baseChange₂ D p (f₁ b)) :=
    fun x hx => betaP_symm_mem_X Zd p g f₁ f₂ (sF' Zd p) (isUnit_sF' Zd p)
      (fun a => by rw [hgs]; exact Submodule.subset_span ⟨a, rfl⟩) hx
  have hX0 : ∀ a ∈ H.X (fun a => sF Zd p a • baseChange₂ D p (f a)), ∀ b ∈ H.X (fun a => sF Zd p a • baseChange₂ D p (f a)),
      H.h a b = 0 := by
    apply iso_span
    intro i j
    rw [h_bcP, brS, show (VS D).hT (f j.castSucc) (f i.castSucc) = 0 from
      FsLA.gram_fvec_zero F0 _ _ (Or.inl (Fin.castSucc_lt_last j).ne), map_zero, mul_zero]
  have hX2 : ∀ a ∈ H.X (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)), ∀ b ∈ H.X (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)),
      H.h a b = 0 := by
    apply iso_span
    intro i j
    rw [h_bcP, brS, show (VS D).hT (f₂ j.castSucc) (f₂ i.castSucc) = 0 from
      FsLA.gram_fvec_zero F'₂.fl _ _ (Or.inl (Fin.castSucc_lt_last j).ne), map_zero, mul_zero]
  have hW0 : ∀ w ∈ H.W0 (fun a => sF Zd p a • baseChange₂ D p (f a)) (fun b => sF' Zd p b • baseChange₂ D p (f₁ b)),
      ∃ w₂ ∈ H.W0 (fun a => sF Zd p a • baseChange₂ D p (f a)) (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)),
        w - w₂ ∈ H.X (fun a => sF Zd p a • baseChange₂ D p (f a)) ∧
        e w - w₂ ∈ H.X (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)) := by
    intro w hw
    rw [mem_orthogonal_frame_iff] at hw
    have hperp : ∀ k, H.h w (baseChange₂ D p (Sum.elim f f₁ k)) = 0 := by
      rintro (a | b)
      · exact h_zero_of_smul Zd p (isUnit_sF Zd p a) (hw.1 a)
      · exact h_zero_of_smul Zd p (isUnit_sF' Zd p b) (hw.2 b)
    have hew : e w = w := FsLoc.betaP_fix Zd p g _ y hform w hperp
    refine ⟨w, ?_, by rw [sub_self]; exact Submodule.zero_mem _, by rw [hew, sub_self]; exact Submodule.zero_mem _⟩
    rw [mem_orthogonal_frame_iff]
    refine ⟨hw.1, fun b => ?_⟩
    have hb : baseChange₂ D p (f₂ b) ∈ Submodule.span (D.s.atP p).Ep (Set.range fun k => baseChange₂ D p (Sum.elim f f₁ k)) :=
      baseChange_mem_span p _ (hU b)
    have hwp : w ∈ H.perp (Submodule.span (D.s.atP p).Ep (Set.range fun k => baseChange₂ D p (Sum.elim f f₁ k))) := by
      rw [mem_perp_span]; rintro _ ⟨k, rfl⟩; exact hperp k
    show H.h w (sF' Zd p b • baseChange₂ D p (f₂ b)) = 0
    rw [h_smul_right, hwp _ hb, mul_zero]
  have hglob : GDl f f₂ (D.R.rS + 1) • Gom' f f₁ - GDl f f₁ (D.R.rS + 1) • Gom' f f₂ ∈
      Submodule.span D.host.E (Set.range fun a : Fin D.R.rS => f a.castSucc) := by
    rw [FsLoc.gdl_eq, FsLoc.gdl_eq, FsLoc.xspan_eq F0]
    exact hc.2
  have homp : H.Dl (fun a => sF Zd p a • baseChange₂ D p (f a)) (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)) (D.R.rS + 1) •
        H.om' (fun a => sF Zd p a • baseChange₂ D p (f a)) (fun b => sF' Zd p b • baseChange₂ D p (f₁ b)) -
      H.Dl (fun a => sF Zd p a • baseChange₂ D p (f a)) (fun b => sF' Zd p b • baseChange₂ D p (f₁ b)) (D.R.rS + 1) •
        H.om' (fun a => sF Zd p a • baseChange₂ D p (f a)) (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)) ∈
      H.X (fun a => sF Zd p a • baseChange₂ D p (f a)) := by
    rw [om'_loc, om'_loc, dl_loc Zd p f f₂ (sF Zd p) (sF' Zd p) _ le_rfl,
      dl_loc Zd p f f₁ (sF Zd p) (sF' Zd p) _ le_rfl, FsLoc.omp_combine' p]
    exact Submodule.smul_mem _ _ (bcP_mem_X Zd p f (sF Zd p) (isUnit_sF Zd p) hglob)
  have hglob2 : star (GDl f f₂ (D.R.rS + 1)) • g (Gom f f₁) - star (GDl f f₁ (D.R.rS + 1)) • Gom f f₂ ∈
      Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => f₂ b.castSucc) := by
    rw [FsLoc.gdl_eq, FsLoc.gdl_eq, FsLoc.xspan_eq F'₂.fl, FsLA.leadMinorE_full, FsLA.leadMinorE_full]
    have hn := Submodule.neg_mem _ hom
    rw [neg_sub] at hn
    have hZe : starZh f f₂ = Z := hZ
    rw [hZe]
    exact hn
  have hom' : (Zd.M p).L.cj (H.Dl (fun a => sF Zd p a • baseChange₂ D p (f a)) (fun b => sF' Zd p b • baseChange₂ D p (f₂ b))
        (D.R.rS + 1)) • e (H.om (fun a => sF Zd p a • baseChange₂ D p (f a)) (fun b => sF' Zd p b • baseChange₂ D p (f₁ b))) -
      (Zd.M p).L.cj (H.Dl (fun a => sF Zd p a • baseChange₂ D p (f a)) (fun b => sF' Zd p b • baseChange₂ D p (f₁ b))
        (D.R.rS + 1)) • H.om (fun a => sF Zd p a • baseChange₂ D p (f a)) (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)) ∈
      H.X (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)) := by
    rw [om_loc, om_loc, dl_loc Zd p f f₂ (sF Zd p) (sF' Zd p) _ le_rfl,
      dl_loc Zd p f f₁ (sF Zd p) (sF' Zd p) _ le_rfl, map_smul, betaP_bc, FsLoc.om_combine' Zd p]
    exact Submodule.smul_mem _ _ (bcP_mem_X Zd p f₂ (sF' Zd p) (isUnit_sF' Zd p) hglob2)
  have hrat : H.Dl (fun a => sF Zd p a • baseChange₂ D p (f a)) (fun b => sF' Zd p b • baseChange₂ D p (f₁ b)) D.R.rS *
        H.Dl (fun a => sF Zd p a • baseChange₂ D p (f a)) (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)) (D.R.rS + 1) =
      H.Dl (fun a => sF Zd p a • baseChange₂ D p (f a)) (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)) D.R.rS *
        H.Dl (fun a => sF Zd p a • baseChange₂ D p (f a)) (fun b => sF' Zd p b • baseChange₂ D p (f₁ b)) (D.R.rS + 1) := by
    have hr := hc.1
    rw [← FsLoc.gdl_eq, ← FsLoc.gdl_eq, ← FsLoc.gdl_eq, ← FsLoc.gdl_eq] at hr
    rw [dl_loc Zd p f f₁ (sF Zd p) (sF' Zd p) _ (Nat.le_succ _), dl_loc Zd p f f₂ (sF Zd p) (sF' Zd p) _ le_rfl,
      dl_loc Zd p f f₂ (sF Zd p) (sF' Zd p) _ (Nat.le_succ _), dl_loc Zd p f f₁ (sF Zd p) (sF' Zd p) _ le_rfl]
    have h := congrArg (D.s.atP p).ιE hr
    rw [map_mul, map_mul] at h
    linear_combination ((∏ i : Fin D.R.rS, (Zd.M p).L.cj (sF Zd p (Fin.castLE (Nat.le_succ _) i))) *
      (∏ i : Fin D.R.rS, sF' Zd p (Fin.castLE (Nat.le_succ _) i)) *
      ((∏ i : Fin (D.R.rS + 1), (Zd.M p).L.cj (sF Zd p (Fin.castLE le_rfl i))) *
      (∏ i : Fin (D.R.rS + 1), sF' Zd p (Fin.castLE le_rfl i)))) * h
  have hef : ∀ b, e (sF' Zd p b • baseChange₂ D p (f₁ b)) = sF' Zd p b • baseChange₂ D p (f₂ b) := fun b => by
    rw [map_smul, he, betaP_bc, hg1]
  have hz : e (sF' Zd p (Fin.last D.R.rS) • baseChange₂ D p (f₁ (Fin.last D.R.rS))) -
      sF' Zd p (Fin.last D.R.rS) • baseChange₂ D p (f₂ (Fin.last D.R.rS)) ∈ H.X (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)) := by
    rw [hef, sub_self]; exact Submodule.zero_mem _
  obtain ⟨hI, hzS⟩ := FsLoc.ident_generic H (tLoc Zd p γ).abelian₂ ⊥ (fun a => sF Zd p a • baseChange₂ D p (f a))
    (fun b => sF' Zd p b • baseChange₂ D p (f₁ b)) (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)) (tLoc Zd p γ).T (tLoc Zd p γ).T'
    e hisoL h12 h21 hX0 hX2 hW0 homp hom' hrat hz
  have hG := hgen p
  have hfr1 := hG.1.2.1
  have hfr2 := hG.1.2.2.1
  refine ⟨hG, ⟨hfr1.2.1, hfr1.2.2.1⟩, ⟨fun a b hab => ?_, ?_⟩, hI, ?_, hzS⟩
  · show H.h (sF' Zd p a • baseChange₂ D p (f₂ a)) (sF' Zd p b • baseChange₂ D p (f₂ b)) = 0
    rw [← hef, ← hef, hisoL]
    exact hfr2.2.1 a b hab
  · show H.h (sF' Zd p (Fin.last _) • baseChange₂ D p (f₂ (Fin.last _))) (sF' Zd p (Fin.last _) • baseChange₂ D p (f₂ (Fin.last _))) = _
    rw [← hef, hisoL]
    exact hfr2.2.2.1
  · intro x x₂ hx hx₂
    have : x = x₂ := Subtype.ext (hx.trans hx₂.symm)
    rw [this]
    rfl

variable (u u' F0 what₂)


set_option maxHeartbeats 1000000 in
theorem starExists2_of_parts (hP : CtxP u u' F0 what₂) (hGen : CohGen Zd u u' F0 what₂)
    (hIo : CohIota Zd u u' F0 what₂) (hGood : CohGood Zd u u' F0 what₂) : StarExists2 Zd u u' F0 what₂ := by
  intro γ Z hC
  obtain ⟨w, hγ, -⟩ := id hC
  obtain ⟨F'₂, hZ, hc, hU⟩ := starFrameU_holds γ Z hC
  obtain ⟨g, y, hiso, hg1, hform, hom⟩ := starGlob γ Z hC F'₂ hZ hU
  let φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂) :=
    fun p => FsLoc.starPhi Zd p g hiso (starFrame γ) (frame F'₂) hg1
  have hφ' : ∀ p, LsDatumA.LocalCountHypotheses (locH Zd p) (tLoc Zd p γ) (tLoc Zd p γ).f (locF' Zd p F'₂)
      (LinearEquiv.refl _ _) (φ' p) :=
    fun p => starIdentG Zd γ Z hC (starGenLoc_of_P Zd hP γ w hγ) F'₂ hZ hc hU g y hiso hg1 hform hom p
  have hH : CohHyp Zd γ Z F'₂ φ' := ⟨hC, hZ, hc, hφ'⟩
  have hlat : Submodule.IsFullLattice D.host.E γ.lam := (hP.2.1.1 γ.lam γ.mem).1.1
  have hLp : {p | ⇑(φ' p) '' (locH Zd p).Lset (lattice₂ D Zd.M p γ.lam) (tLoc Zd p γ).f' ≠
      (locH Zd p).Lset (lattice₂ D Zd.M p γ.lam) (locF' Zd p F'₂)}.Finite := by
    refine ((FsLoc.localLattice_preserves_cofinite Zd g hlat).union (FsLoc.localLattice_preserves_cofinite_symm Zd g hlat)).subset ?_
    intro p hp
    by_contra hn
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hn
    exact hp (FsLoc.lset_map (locH Zd p) _ _ (betaP p g) (betaP_iso Zd p g hiso) _ _ _ hn.1 hn.2)
  have hResp : {p | ¬ (locH Zd p).Respects (tLoc Zd p γ) (CohCut.t2 Zd p γ F'₂ (lattice₂ D Zd.M p γ.lam))
      (LinearEquiv.refl _ _) (φ' p)}.Finite := by
    refine (hLp.union (hIo hP γ Z F'₂ φ' hH)).subset ?_
    intro p hp
    by_contra hn
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, ne_eq] at hn
    obtain ⟨h3, h5⟩ := hn
    apply hp
    refine ⟨?_, ?_, h3, (hH.2.2.2 p).2.2.2.2.2, h5⟩
    · exact Set.image_id _
    · intro x x₂ hx hx₂
      rw [one_smul, one_smul]
      show (locH Zd p).mkW _ x = (locH Zd p).mkW _ x₂
      exact congrArg _ (Subtype.ext (hx.trans hx₂.symm))
  refine ⟨F'₂, fun _ => LinearEquiv.refl _ _, φ', ⟨hZ, hφ', fun _ => rfl⟩, γ.lam, hlat, ?_⟩
  refine (((hGen hP γ Z F'₂ φ' hH).union hResp).union (hGood hP γ Z F'₂ φ' hH)).subset ?_
  intro p hp
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hn
  obtain ⟨⟨hg, hr⟩, hN⟩ := hn
  exact hp (locSet_eq_single Zd ⟨hg, hr⟩ hN)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem starExists2_of_good (hP : CtxP u u' F0 what₂) (hGood : CohGood Zd u u' F0 what₂) :
    StarExists2 Zd u u' F0 what₂ :=
  starExists2_of_parts Zd u u' F0 what₂ hP (cohGen_of Zd (cohInt_holds Zd) (cohDG_holds Zd) hGood)
    (cohIota_holds Zd) hGood

theorem starExists2_holds (hP : CtxP u u' F0 what₂) : StarExists2 Zd u u' F0 what₂ :=
  starExists2_of_good Zd u u' F0 what₂ hP (cohGood_of Zd globGramNe_holds)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
