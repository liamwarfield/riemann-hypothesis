module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AdmissibleLocalPartner

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIIotaB
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIIotaA
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.IotaBP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (p : PlF D)

theorem gS_typed (g : Loc.SplitG (Zd.M p).L) (hs : (Zd.M p).split = some g) :
    ∃ w ∈ (D.s.atP p).O, ∃ w' ∈ (D.s.atP p).O,
      (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * w ∧
        w * w' = 1 := by
  obtain ⟨sg, hsg, hq, -⟩ := typed_data Zd p g hs
  refine ⟨(D.s.atP p).ιE ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E), ?_, (D.s.atP p).ιE (uP p : D.host.E),
    Formalism.L2.SG.Pf.LocFacts.unitPart_mem₂ p, ?_, ?_⟩
  · rw [map_natCast]; exact natCast_mem _ _
  · rw [hq, sg.q_eq, ← Formalism.MainNotions.BridgeLemma.gpart_mul_oth p, Formalism.MainNotions.BridgeLemma.gpart_some p sg hsg]
    simp only [Nat.cast_mul, map_mul, map_natCast]
  · rw [← map_mul, Formalism.MainNotions.BridgeLemma.unitAt_eq p]
    have h0 : ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E) ≠ 0 := by
      exact_mod_cast Formalism.MainNotions.BridgeLemma.oth_ne_zero p
    push_cast
    rw [mul_inv_cancel₀ h0, map_one]

theorem localLattice_mono {A B : Submodule (𝓞 D.host.E) (VS D).V} (h : A ≤ B) : lattice₂ D Zd.M p A ≤ lattice₂ D Zd.M p B :=
  Submodule.span_mono (Set.image_mono h)

theorem mem_O_M {a : (D.s.atP p).Ep} (ha : a ∈ (D.s.atP p).O) : a ∈ (Zd.M p).L.O := by
  rw [Formalism.L2.SG.Pf.LocalDenominators.hO Zd p]; exact ha

theorem smul_gS_mem {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)
    (F' : LFlag (D.sp.Y 0) D.R.rS T') {v : Vp D p} (hv : v ∈ lattice₂ D Zd.M p Λ) :
    (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v ∈ lattice₂ D Zd.M p (NgX Λ (gS D) F F') := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨y, hy, rfl⟩ := hv
    rw [← Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]
    refine Submodule.subset_span ⟨_, ?_, rfl⟩
    have h1 : ((gS D : ℕ) : D.host.E) • y = ((gS D : ℕ) : 𝓞 D.host.E) • y := by
      rw [← algebraMap_smul D.host.E ((gS D : ℕ) : 𝓞 D.host.E) y, map_natCast]
    rw [SetLike.mem_coe, h1]
    refine Submodule.mem_sup_left (Submodule.mem_sup_left ?_)
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hy
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul o v _ hv =>
    have e : (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • (o • v) = o • ((D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v) := by
      show _ • ((o : (D.s.atP p).Ep) • v) = (o : (D.s.atP p).Ep) • _
      rw [smul_smul, smul_smul, mul_comm]
    rw [e]; exact Submodule.smul_mem _ _ hv

theorem untyped_mem (hs : (Zd.M p).split = none) {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T T' : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') {v : Vp D p} (hv : v ∈ lattice₂ D Zd.M p Λ) :
    v ∈ lattice₂ D Zd.M p (NgX Λ (gS D) F F') := by
  have e := Formalism.L2.SG.Pf.StabIntSh.gS_mul_uP Zd.δ Zd.M Zd.agree p hs
  have hv' : v = (D.s.atP p).ιE (uP p : D.host.E) • ((D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • v) := by
    rw [smul_smul, mul_comm, e, one_smul]
  rw [hv']
  exact Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Zd p (Formalism.L2.SG.Pf.LocFacts.unitPart_mem₂ p) (smul_gS_mem Zd p F F' hv)

theorem typed_q_mem (g : Loc.SplitG (Zd.M p).L) (hs : (Zd.M p).split = some g) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') {v : Vp D p}
    (hv : v ∈ lattice₂ D Zd.M p Λ) :
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) • v ∈ lattice₂ D Zd.M p (NgX Λ (gS D) F F') := by
  obtain ⟨w, -, w', hw', he, hww⟩ := gS_typed Zd p g hs
  have e : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) • v =
      (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) • (w' • v) := by
    rw [he, smul_smul, mul_assoc, hww, mul_one]
  rw [e]
  exact smul_gS_mem Zd p F F' (Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Zd p hw' hv)

theorem l1 {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T' : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T')
    (f : Fin (D.R.rS + 1) → Vp D p) (s : Fin (D.R.rS + 1) → (D.s.atP p).Ep) (hs : ∀ a, s a ∈ (D.s.atP p).O)
    (hf : ∀ i : Fin D.R.rS, f i.castSucc = (s i.castSucc * frFac Zd.δ p i.castSucc) • baseChange₂ D p (G.fl.e i))
    (hprim : (locH Zd p).Prim (lattice₂ D Zd.M p Λ) f) (hXS : XLam Λ G = XS D G.fl) {v : Vp D p}
    (hv : v ∈ lattice₂ D Zd.M p Λ) (hvX : v ∈ (locH Zd p).X f) : v ∈ lattice₂ D Zd.M p (XLam Λ G) := by
  have hvE : v ∈ Submodule.span (D.s.atP p).Ep (Set.range f) :=
    Submodule.span_mono (Set.range_comp_subset_range _ _) hvX
  have hvO := hprim.2.2 v hv hvE
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (Zd.M p).L.O).1 hvO
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun (D.s.atP p).Ep).1 hvX
  have key : (c (Fin.last D.R.rS) : (D.s.atP p).Ep) = 0 := by
    have h0 : ∑ a, ((c a : (D.s.atP p).Ep) - Fin.snoc (α := fun _ => (D.s.atP p).Ep) e 0 a) • f a = 0 := by
      simp_rw [sub_smul]
      rw [Finset.sum_sub_distrib, Fin.sum_univ_castSucc (f := fun a => Fin.snoc (α := fun _ => (D.s.atP p).Ep) e 0 a • f a)]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, zero_smul, add_zero]
      rw [he, ← hc, sub_eq_zero]
      rfl
    have := Fintype.linearIndependent_iff.1 hprim.2.1 _ h0 (Fin.last D.R.rS)
    simpa using this
  rw [← hc, Fin.sum_univ_castSucc]
  refine add_mem (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_) ?_
  · rw [hf, hXS, Formalism.L2.SG.Pf.BBTie.bt_latP_XS Zd p (Formalism.L2.SG.Pf.locDiffC_holds D Zd) G.fl, mul_smul]
    have hm : frFac Zd.δ p i.castSucc • baseChange₂ D p (G.fl.e i) ∈ Submodule.span (Zd.M p).L.O
        (Set.range fun a : Fin D.R.rS => frFac Zd.δ p a.castSucc • baseChange₂ D p (G.fl.e a)) := Submodule.subset_span ⟨i, rfl⟩
    exact Submodule.smul_mem _ (⟨s i.castSucc, mem_O_M Zd p (hs _)⟩ : (Zd.M p).L.O) hm
  · have : c (Fin.last D.R.rS) • f (Fin.last D.R.rS) = 0 := by
      rw [Subring.smul_def, key, zero_smul]
    rw [this]; exact zero_mem _

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.IotaBP
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.IotaBP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (p : PlF D)

theorem xi_mem {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T : D.host.E} {F : LFlag (D.sp.Y 0) D.R.rS T} {x : (VS D).V}
    (hx : x ∈ XLam Λ F) : x ∈ Λ := (Submodule.mem_inf.1 hx).1

theorem g1 {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)
    (F' : LFlag (D.sp.Y 0) D.R.rS T') (t : Loc.Term (Vp D p) (Zd.M p) D.R.rS) (hLam : t.abelian₂ = lattice₂ D Zd.M p Λ)
    (g : Loc.SplitG (Zd.M p).L) (hs : (Zd.M p).split = some g) {y y' l ξ ξ' : (VS D).V} (hy : y ∈ Λ) (hy' : y' ∈ Λ)
    (hl : l ∈ Λ) (hξ : ξ ∈ XLam Λ F) (hξ' : ξ' ∈ XLam Λ F')
    (heq : y - y' = ((gS D : ℕ) : D.host.E) • l + ξ + ξ')
    (hp1 : baseChange₂ D p (y - ξ) ∈ (locH Zd p).perp ((locH Zd p).X t.f))
    (hp2 : baseChange₂ D p (y' + ξ') ∈ (locH Zd p).perp ((locH Zd p).X t.f')) :
    ((locH Zd p).mkW t.f' ⟨baseChange₂ D p (y' + ξ'), hp2⟩, (locH Zd p).mkW t.f ⟨baseChange₂ D p (y - ξ), hp1⟩) ∈
      (locH Zd p).iotaGraph g t := by
  obtain ⟨w, hw, w', -, he, -⟩ := gS_typed Zd p g hs
  refine ⟨⟨_, hp2⟩, ⟨_, hp1⟩, ?_, ?_, ?_, rfl⟩
  · rw [hLam]; exact BwdNP.baseChange_mem_localLattice Zd (add_mem hy' (xi_mem hξ')) p
  · rw [hLam]; exact BwdNP.baseChange_mem_localLattice Zd (sub_mem hy (xi_mem hξ)) p
  · have hv : y - ξ - (y' + ξ') = ((gS D : ℕ) : D.host.E) • l := by
      rw [show y - ξ - (y' + ξ') = (y - y') - ξ - ξ' by abel, heq]; abel
    have e : baseChange₂ D p (y - ξ) - baseChange₂ D p (y' + ξ') =
        algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) • (w • baseChange₂ D p l) := by
      rw [← map_sub, hv, Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂, he, mul_smul]
    show baseChange₂ D p (y - ξ) - baseChange₂ D p (y' + ξ') ∈ _
    rw [e, hLam]
    exact Submodule.subset_span ⟨w • baseChange₂ D p l, Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Zd p hw (BwdNP.baseChange_mem_localLattice Zd hl p), rfl⟩

theorem g2 {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)
    (F' : LFlag (D.sp.Y 0) D.R.rS T') (t : Loc.Term (Vp D p) (Zd.M p) D.R.rS) (hLam : t.abelian₂ = lattice₂ D Zd.M p Λ)
    (g : Loc.SplitG (Zd.M p).L) (hs : (Zd.M p).split = some g) {y y' : (VS D).V} (hy : y ∈ Λ) (hy' : y' ∈ Λ)
    (hp1 : baseChange₂ D p y ∈ (locH Zd p).perp ((locH Zd p).X t.f))
    (hp2 : baseChange₂ D p y' ∈ (locH Zd p).perp ((locH Zd p).X t.f'))
    (hmem : ((locH Zd p).mkW t.f' ⟨baseChange₂ D p y', hp2⟩, (locH Zd p).mkW t.f ⟨baseChange₂ D p y, hp1⟩) ∈
      (locH Zd p).iotaGraph g t)
    (hA : ∀ v ∈ lattice₂ D Zd.M p Λ, v ∈ (locH Zd p).X t.f → v ∈ lattice₂ D Zd.M p (XLam Λ F))
    (hB : ∀ v ∈ lattice₂ D Zd.M p Λ, v ∈ (locH Zd p).X t.f' → v ∈ lattice₂ D Zd.M p (XLam Λ F')) :
    baseChange₂ D p (y - y') ∈ lattice₂ D Zd.M p (NgX Λ (gS D) F F') := by
  obtain ⟨x'', x, hx''Λ, hxΛ, hdiff, heq⟩ := hmem
  obtain ⟨h1, h2⟩ := Prod.mk.inj heq
  rw [hLam] at hx''Λ hxΛ hdiff
  have d1 : baseChange₂ D p y' - (x'' : Vp D p) ∈ (locH Zd p).X t.f' := by
    have := (Submodule.Quotient.eq _).1 h1
    simpa using this
  have d2 : baseChange₂ D p y - (x : Vp D p) ∈ (locH Zd p).X t.f := by
    have := (Submodule.Quotient.eq _).1 h2
    simpa using this
  have hXA : XLam Λ F ≤ NgX Λ (gS D) F F' := le_sup_right.trans le_sup_left
  have hXB : XLam Λ F' ≤ NgX Λ (gS D) F F' := le_sup_right
  have a1 := localLattice_mono Zd p hXA (hA _ (sub_mem (BwdNP.baseChange_mem_localLattice Zd hy p) hxΛ) d2)
  have a2 := localLattice_mono Zd p hXB (hB _ (sub_mem (BwdNP.baseChange_mem_localLattice Zd hy' p) hx''Λ) d1)
  have a3 : (x : Vp D p) - x'' ∈ lattice₂ D Zd.M p (NgX Λ (gS D) F F') := by
    refine (Submodule.span_le.2 ?_) hdiff
    rintro _ ⟨v, hv, rfl⟩
    exact typed_q_mem Zd p g hs F F' hv
  have e : baseChange₂ D p (y - y') = (baseChange₂ D p y - x) + ((x : Vp D p) - x'') - (baseChange₂ D p y' - x'') := by
    rw [map_sub]; abel
  rw [e]
  exact sub_mem (add_mem a1 a3) a2

theorem Xle_tLoc {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (γ : TermDef.Term D u u' F0 what₂) :
    (locH Zd p).X (tLoc Zd p γ).f' ≤ (locH Zd p).X (locF' Zd p (repF γ)) := by
  obtain ⟨hξ1, hξ2⟩ := inv_unitri _ (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).1 (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).2
  obtain ⟨hC0, -, -⟩ := Cm_props Zd p (admXi D γ.lam (lf D F0) (repF γ))⁻¹ hξ1 hξ2
  have hf : ∀ b, (tLoc Zd p γ).f' b = GeneratorChange.comb (Cm Zd p (admXi D γ.lam (lf D F0) (repF γ))⁻¹) (locF' Zd p (repF γ)) b :=
    fun b => (comb_Cm Zd p (repF γ) _ b).symm
  rw [Loc.HermSp.X, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  simp only
  rw [hf, GeneratorChange.comb, Fin.sum_univ_castSucc]
  refine add_mem (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)) ?_
  rw [hC0 _ _ (Fin.castSucc_lt_last i), zero_smul]
  exact zero_mem _

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.IotaBP
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut BwdBetaCut BwdNP BetaI IotaBP

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

namespace IotaBP

theorem isLattice_NgX_aux {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsLattice D.host.E Λ) {T T' : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') :
    Submodule.IsLattice D.host.E (NgX Λ (gS D) F F') := by
  have hle : NgX Λ (gS D) F F' ≤ Λ := by
    refine sup_le (sup_le ?_ inf_le_left) inf_le_left
    exact Submodule.smul_le_right
  exact ⟨hΛ.fg.of_le hle, fun s hs hli => (LinearIndependent.iff_fractionRing _ _).mp hli⟩

theorem isLattice_NgX {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsFullLattice D.host.E Λ) {T T' : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') :
    Submodule.IsFullLattice D.host.E (NgX Λ (gS D) F F') := by
  have hle : NgX Λ (gS D) F F' ≤ Λ := by
    refine sup_le (sup_le ?_ inf_le_left) inf_le_left
    exact Submodule.smul_le_right
  letI := Submodule.IsLattice.of_fg D.host.E (hΛ.toIsLattice.fg.of_le hle)
  refine ⟨top_unique ?_⟩
  rw [← hΛ.span_eq_top]
  apply Submodule.span_le.2
  intro x hx
  rw [SetLike.mem_coe]
  rw [SetLike.mem_coe] at hx
  have hscaled : ((gS D : ℕ) : D.host.E) • x ∈ NgX Λ (gS D) F F' := by
    have hle' : Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ≤ NgX Λ (gS D) F F' :=
      le_sup_left.trans le_sup_left
    apply hle'
    rw [Submodule.ideal_span_singleton_smul]
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨x, hx, by simp [Formalism.L2.SG.Pf.LocalDenominators.oE_smul]⟩
  have hg : ((gS D : ℕ) : D.host.E) ≠ 0 := by
    exact_mod_cast Formalism.L2.SG.Pf.Cnt.DualityBasisChange.gS_ne (D := D)
  have h := (Submodule.span D.host.E (NgX Λ (gS D) F F' : Set (VS D).V)).smul_mem
    ((gS D : ℕ) : D.host.E)⁻¹ (Submodule.subset_span hscaled)
  change x ∈ Submodule.span D.host.E (NgX Λ (gS D) F F' : Set (VS D).V)
  simpa only [smul_smul, inv_mul_cancel₀ hg, one_smul] using h
theorem NgX_dec {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T T' : D.host.E} {F : LFlag (D.sp.Y 0) D.R.rS T}
    {F' : LFlag (D.sp.Y 0) D.R.rS T'} {x : (VS D).V} (hx : x ∈ NgX Λ (gS D) F F') :
    ∃ l ∈ Λ, ∃ ξ ∈ XLam Λ F, ∃ ξ' ∈ XLam Λ F', x = ((gS D : ℕ) : D.host.E) • l + ξ + ξ' := by
  obtain ⟨a, ha, ξ', hξ', rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨b, hb, ξ, hξ, rfl⟩ := Submodule.mem_sup.1 ha
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hb
  obtain ⟨l, hl, rfl⟩ := hb
  refine ⟨l, hl, ξ, hξ, ξ', hξ', ?_⟩
  rw [← algebraMap_smul D.host.E ((gS D : ℕ) : 𝓞 D.host.E) l, map_natCast]

theorem representative_admissible_one (hC : CtxP u u' F0 what₂) {γ : TermDef.Term D u u' F0 what₂} {Z : PairVal.MatR D} (hZ : Ctx γ Z) :
    AdmWit γ.lam (gS D) (lf D F0) (repF γ) 1 := by
  obtain ⟨w, hγ, -⟩ := hZ
  have hN := normRepExists_ctx hC
  obtain ⟨⟨hgen, hG⟩, hat⟩ := hγ
  obtain ⟨y, hy⟩ := hN γ w hat (eligRel_holds γ w ⟨⟨hgen, hG⟩, hat⟩) hgen
  have hex : ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × PairVal.MatR D ×
      PairVal.MatR D, PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2 := ⟨(w, y), hy⟩
  have hn : nrep γ = some hex.choose := dif_pos hex
  have hrep : repF γ = hex.choose.2.1 := by unfold repF; rw [hn]
  rw [hrep]
  exact hex.choose_spec.2.1

abbrev t2 (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) : Loc.Term (Vp D p) (Zd.M p) D.R.rS :=
  ⟨lattice₂ D Zd.M p Λ₂, (tLoc Zd p γ).f, locF' Zd p F'₂, (tLoc Zd p γ).T, (tLoc Zd p γ).T'⟩


set_option maxHeartbeats 1000000 in
theorem fwd_typed (p : PlF D) (g : Loc.SplitG (Zd.M p).L) (hsp : (Zd.M p).split = some g)
    (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V)
    (φ' : (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (hR : Prod.map φ' (LinearEquiv.refl (D.s.atP p).Ep ((locH Zd p).Wb (tLoc Zd p γ).f)) ''
      (locH Zd p).iotaGraph g (tLoc Zd p γ) = (locH Zd p).iotaGraph g (t2 Zd p γ F'₂ Λ₂))
    (β₀ β : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hPin : ∀ (m : (VS D).V) (hm : baseChange₂ D p m ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f'))
      (hm₂ : baseChange₂ D p (β₀ m) ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂))),
      m ∈ orth (VS D) (Xsp (repF γ)) →
      φ' ((locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p m, hm⟩) = (locH Zd p).mkW (locF' Zd p F'₂) ⟨baseChange₂ D p (β₀ m), hm₂⟩)
    (hβ₀o : ∀ m ∈ orth (VS D) (Xsp (repF γ)), β₀ m ∈ orth (VS D) (Xsp (liftF F'₂)))
    (hβo : ∀ m ∈ orth (VS D) (Xsp (repF γ)), β m ∈ orth (VS D) (Xsp (liftF F'₂)))
    (hβd : ∀ m ∈ orth (VS D) (Xsp (repF γ)), β₀ m - β m ∈ Xsp (liftF F'₂))
    (hβX : ∀ y ∈ Xsp (repF γ), β y ∈ Xsp (liftF F'₂)) (hβΛ : ∀ y ∈ γ.lam, β y ∈ Λ₂)
    (hu : ∀ a, IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a))
    (hXo : Xsp (lf D F0) ≤ orth (VS D) (Xsp (lf D F0))) (hXo' : Xsp (repF γ) ≤ orth (VS D) (Xsp (repF γ)))
    (hA2 : ∀ w ∈ lattice₂ D Zd.M p Λ₂, w ∈ (locH Zd p).X (tLoc Zd p γ).f → w ∈ lattice₂ D Zd.M p (XLam Λ₂ (lf D F0)))
    (hB2 : ∀ w ∈ lattice₂ D Zd.M p Λ₂, w ∈ (locH Zd p).X (locF' Zd p F'₂) →
      w ∈ lattice₂ D Zd.M p (XLam Λ₂ (liftF F'₂)))
    {x' l l₂ μ ξ ξ' : (VS D).V} (hx'Λ : x' ∈ γ.lam) (hx'o : x' ∈ orth (VS D) (Xsp (repF γ))) (hlΛ : l ∈ γ.lam)
    (hlo : l ∈ orth (VS D) (Xsp (lf D F0))) (hl₂Λ : l₂ ∈ Λ₂) (hl₂o : l₂ ∈ orth (VS D) (Xsp (lf D F0)))
    (hll₂ : l - l₂ ∈ Xsp (lf D F0)) (hμ : μ ∈ γ.lam) (hξ : ξ ∈ XLam γ.lam (lf D F0)) (hξ' : ξ' ∈ XLam γ.lam (repF γ))
    (heq : l - x' = ((gS D : ℕ) : D.host.E) • μ + ξ + ξ') :
    baseChange₂ D p (l₂ - β x') ∈ lattice₂ D Zd.M p (NgX Λ₂ (gS D) (lf D F0) (liftF F'₂)) := by
  have hξX : ξ ∈ Xsp (lf D F0) := (Submodule.mem_inf.1 hξ).2
  have hξ'X : ξ' ∈ Xsp (repF γ) := (Submodule.mem_inf.1 hξ').2
  have hm : x' + ξ' ∈ orth (VS D) (Xsp (repF γ)) := add_mem hx'o (hXo' hξ'X)
  have hp1 := BwdNP.baseChange_mem_perp_sup Zd p γ (sub_mem hlo (hXo hξX))
  have hp2 := BetaI.bcP_perp_f' Zd p γ hm
  have hG1 := g1 Zd p (lf D F0) (repF γ) (tLoc Zd p γ) rfl g hsp hlΛ hx'Λ hμ hξ hξ' heq hp1 hp2
  have hm₂ := BetaI.baseChangeAt_perp' Zd p F'₂ (hβ₀o _ hm)
  have hq₂ := BetaI.baseChangeAt_perp' Zd p F'₂ (hβo _ hm)
  have hp₂ := BwdNP.baseChange_mem_perp_sup Zd p γ hl₂o
  have e1 : φ' ((locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p (x' + ξ'), hp2⟩) =
      (locH Zd p).mkW (locF' Zd p F'₂) ⟨baseChange₂ D p (β (x' + ξ')), hq₂⟩ := by
    rw [hPin (x' + ξ') hp2 hm₂ hm]
    refine (Submodule.Quotient.eq _).2 ?_
    show baseChange₂ D p (β₀ (x' + ξ')) - baseChange₂ D p (β (x' + ξ')) ∈ (locH Zd p).X (locF' Zd p F'₂)
    rw [← map_sub]
    exact BetaI.bcP_X' Zd p F'₂ (hβd _ hm)
  have e2 : (locH Zd p).mkW (tLoc Zd p γ).f ⟨baseChange₂ D p (l - ξ), hp1⟩ =
      (locH Zd p).mkW (tLoc Zd p γ).f ⟨baseChange₂ D p l₂, hp₂⟩ := by
    refine (Submodule.Quotient.eq _).2 ?_
    show baseChange₂ D p (l - ξ) - baseChange₂ D p l₂ ∈ (locH Zd p).X (tLoc Zd p γ).f
    rw [← map_sub]
    refine BwdNP.bcP_X Zd p γ hu ?_
    have e : l - ξ - l₂ = (l - l₂) - ξ := by abel
    rw [e]; exact sub_mem hll₂ hξX
  have hG2 := Set.mem_image_of_mem (Prod.map φ' (LinearEquiv.refl (D.s.atP p).Ep ((locH Zd p).Wb (tLoc Zd p γ).f))) hG1
  rw [hR] at hG2
  simp only [Prod.map, LinearEquiv.refl_apply, e1, e2] at hG2
  have hfin := g2 Zd p (lf D F0) (liftF F'₂) (t2 Zd p γ F'₂ Λ₂) rfl g hsp hl₂Λ
    (hβΛ _ (add_mem hx'Λ (xi_mem hξ'))) hp₂ hq₂ hG2 hA2 hB2
  have hβξ : β ξ' ∈ NgX Λ₂ (gS D) (lf D F0) (liftF F'₂) :=
    Submodule.mem_sup_right (Submodule.mem_inf.2 ⟨hβΛ _ (xi_mem hξ'), hβX _ hξ'X⟩)
  have e : l₂ - β x' = (l₂ - β (x' + ξ')) + β ξ' := by rw [map_add (f := _)]; abel
  rw [e, map_add (f := _)]
  exact add_mem hfin (Submodule.subset_span ⟨_, hβξ, rfl⟩)


set_option maxHeartbeats 1000000 in
theorem bwd_typed (p : PlF D) (g : Loc.SplitG (Zd.M p).L) (hsp : (Zd.M p).split = some g)
    (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V)
    (φ' : (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (hR : Prod.map φ' (LinearEquiv.refl (D.s.atP p).Ep ((locH Zd p).Wb (tLoc Zd p γ).f)) ''
      (locH Zd p).iotaGraph g (tLoc Zd p γ) = (locH Zd p).iotaGraph g (t2 Zd p γ F'₂ Λ₂))
    (β₀ β : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hPin : ∀ (m : (VS D).V) (hm : baseChange₂ D p m ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f'))
      (hm₂ : baseChange₂ D p (β₀ m) ∈ (locH Zd p).perp ((locH Zd p).X (locF' Zd p F'₂))),
      m ∈ orth (VS D) (Xsp (repF γ)) →
      φ' ((locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p m, hm⟩) = (locH Zd p).mkW (locF' Zd p F'₂) ⟨baseChange₂ D p (β₀ m), hm₂⟩)
    (hβ₀o : ∀ m ∈ orth (VS D) (Xsp (repF γ)), β₀ m ∈ orth (VS D) (Xsp (liftF F'₂)))
    (hβo : ∀ m ∈ orth (VS D) (Xsp (repF γ)), β m ∈ orth (VS D) (Xsp (liftF F'₂)))
    (hβd : ∀ m ∈ orth (VS D) (Xsp (repF γ)), β₀ m - β m ∈ Xsp (liftF F'₂)) (hβΛ : ∀ y ∈ γ.lam, β y ∈ Λ₂)
    (hu : ∀ a, IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a))
    (hXo : Xsp (lf D F0) ≤ orth (VS D) (Xsp (lf D F0)))
    (hXo₂ : Xsp (liftF F'₂) ≤ orth (VS D) (Xsp (liftF F'₂)))
    (hA1 : ∀ w ∈ lattice₂ D Zd.M p γ.lam, w ∈ (locH Zd p).X (tLoc Zd p γ).f → w ∈ lattice₂ D Zd.M p (XLam γ.lam (lf D F0)))
    (hB1 : ∀ w ∈ lattice₂ D Zd.M p γ.lam, w ∈ (locH Zd p).X (tLoc Zd p γ).f' →
      w ∈ lattice₂ D Zd.M p (XLam γ.lam (repF γ)))
    {x' l l₂ μ ξ ξ' : (VS D).V} (hx'Λ : x' ∈ γ.lam) (hx'o : x' ∈ orth (VS D) (Xsp (repF γ))) (hlΛ : l ∈ γ.lam)
    (hlo : l ∈ orth (VS D) (Xsp (lf D F0))) (hl₂Λ : l₂ ∈ Λ₂) (hl₂o : l₂ ∈ orth (VS D) (Xsp (lf D F0)))
    (hll₂ : l - l₂ ∈ Xsp (lf D F0)) (hμ : μ ∈ Λ₂) (hξ : ξ ∈ XLam Λ₂ (lf D F0)) (hξ' : ξ' ∈ XLam Λ₂ (liftF F'₂))
    (heq : l₂ - β x' = ((gS D : ℕ) : D.host.E) • μ + ξ + ξ') :
    baseChange₂ D p (l - x') ∈ lattice₂ D Zd.M p (NgX γ.lam (gS D) (lf D F0) (repF γ)) := by
  have hξX : ξ ∈ Xsp (lf D F0) := (Submodule.mem_inf.1 hξ).2
  have hξ'X : ξ' ∈ Xsp (liftF F'₂) := (Submodule.mem_inf.1 hξ').2
  have hp1 := BwdNP.baseChange_mem_perp_sup Zd p γ (sub_mem hl₂o (hXo hξX))
  have hp2 := BetaI.baseChangeAt_perp' Zd p F'₂ (add_mem (hβo _ hx'o) (hXo₂ hξ'X))
  have hG1 := g1 Zd p (lf D F0) (liftF F'₂) (t2 Zd p γ F'₂ Λ₂) rfl g hsp hl₂Λ (hβΛ _ hx'Λ) hμ hξ hξ' heq hp1 hp2
  rw [← hR] at hG1
  obtain ⟨⟨a', a⟩, ha, hpair⟩ := hG1
  obtain ⟨ha', haa⟩ := Prod.mk.inj hpair
  have hp₁' := BetaI.bcP_perp_f' Zd p γ hx'o
  have hm₂ := BetaI.baseChangeAt_perp' Zd p F'₂ (hβ₀o _ hx'o)
  have hpl := BwdNP.baseChange_mem_perp_sup Zd p γ hlo
  have ea' : a' = (locH Zd p).mkW (tLoc Zd p γ).f' ⟨baseChange₂ D p x', hp₁'⟩ := by
    apply φ'.injective
    rw [ha', hPin x' hp₁' hm₂ hx'o]
    refine (Submodule.Quotient.eq _).2 ?_
    show baseChange₂ D p (β x' + ξ') - baseChange₂ D p (β₀ x') ∈ (locH Zd p).X (locF' Zd p F'₂)
    rw [← map_sub]
    refine BetaI.bcP_X' Zd p F'₂ ?_
    have e : β x' + ξ' - β₀ x' = ξ' - (β₀ x' - β x') := by abel
    rw [e]; exact sub_mem hξ'X (hβd _ hx'o)
  have ea : a = (locH Zd p).mkW (tLoc Zd p γ).f ⟨baseChange₂ D p l, hpl⟩ := by
    refine (show a = (locH Zd p).mkW (tLoc Zd p γ).f ⟨baseChange₂ D p (l₂ - ξ), hp1⟩ from haa).trans ?_
    refine (Submodule.Quotient.eq _).2 ?_
    show baseChange₂ D p (l₂ - ξ) - baseChange₂ D p l ∈ (locH Zd p).X (tLoc Zd p γ).f
    rw [← map_sub]
    refine BwdNP.bcP_X Zd p γ hu ?_
    have e : l₂ - ξ - l = -((l - l₂) + ξ) := by abel
    rw [e]; exact neg_mem (add_mem hll₂ hξX)
  rw [ea', ea] at ha
  exact g2 Zd p (lf D F0) (repF γ) (tLoc Zd p γ) rfl g hsp hlΛ hx'Λ hpl hp₁' ha hA1 hB1

end IotaBP


set_option maxHeartbeats 1000000 in
theorem iotaB_of (hP : PinB Zd u u' F0 what₂) : IotaB Zd u u' F0 what₂ := by
  intro γ Z F'₂ φ φ' Λ₂ hB β₀ hiso hfr hW hO v hv hvf hvX hgm
  have hB0 := hB
  obtain ⟨hC, hZ, hS, hΛ₂, -, hT, hPD, -⟩ := hB
  obtain ⟨hΛ₂full, hloc₂⟩ := hΛ₂
  obtain ⟨-, hT2, hφ⟩ := hS
  have hrow := hC.2.1.1 γ.lam γ.mem
  have hΛfull : Submodule.IsFullLattice D.host.E γ.lam := hrow.1.1
  have hXS1 : XLam γ.lam (lf D F0) = XS D F0 := hrow.2.2
  have hXSx : XLam γ.lam (repF γ) = XS D (repF γ).fl := hPD.2.2.2
  have hXS2' : XLam Λ₂ (liftF F'₂) = XS D (liftF F'₂).fl := hT.2.2.2.2

  have hpr1 : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p γ.lam) (tLoc Zd p γ).f := fun p => (hT2 p).1.1.2.1.1
  have hpr2 : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f := fun p => (hloc₂ p).1.1.2.1.1
  have hpr2' : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ₂) (locF' Zd p F'₂) := fun p => (hloc₂ p).1.1.2.2.1.1
  have hadm1 := IotaBP.representative_admissible_one hC hZ
  have hpr1' : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p γ.lam) (locF' Zd p (repF γ)) := fun p =>
    (genXi_holds Zd hC.2.1 γ (repF γ) p hadm1 hPD.1 (hT2 p).1).1.2.2.1.1
  have hu : ∀ p a, IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a) := fun p a =>
    unit_of_frame Zd p γ (hT2 p).1.1.2.1 a
  have hXS2 : XLam Λ₂ (lf D F0) = XS D F0 := by
    rw [← hXS1]
    ext x
    simp only [XLam, Submodule.mem_inf]
    constructor
    · rintro ⟨h1, h2⟩; refine ⟨?_, h2⟩
      first | exact memX Zd γ hpr2 hpr1 hΛfull hu h2 h1 | exact memX Zd γ hpr2 hpr1 hΛfull.toIsLattice hu h2 h1
    · rintro ⟨h1, h2⟩; refine ⟨?_, h2⟩
      first | exact memX Zd γ hpr1 hpr2 hΛ₂full hu h2 h1 | exact memX Zd γ hpr1 hpr2 hΛ₂full.toIsLattice hu h2 h1

  have hXmap : (Xsp (repF γ)).map (β₀ : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp (liftF F'₂) :=
    BwdBetaCut.Xsp_of_frame β₀ _ _ hfr
  have hvXX : ∀ y ∈ Xsp (liftF F'₂), v y ∈ Xsp (liftF F'₂) := fun y hy => by
    rw [← BwdBetaCut.Xsp_of_frame v (liftF F'₂) (liftF F'₂) hvf]; exact Submodule.mem_map_of_mem hy
  have hβ₀o : ∀ m ∈ orth (VS D) (Xsp (repF γ)), β₀ m ∈ orth (VS D) (Xsp (liftF F'₂)) := fun m hm => by
    rw [← hXmap, Formalism.L2.SG.Pf.orth_map_sat β₀ hiso]; exact Submodule.mem_map_of_mem hm
  have hβX : ∀ y ∈ Xsp (repF γ), (v * β₀) y ∈ Xsp (liftF F'₂) := fun y hy =>
    hvXX _ (by rw [← hXmap]; exact Submodule.mem_map_of_mem hy)
  have hβΛ : ∀ y ∈ γ.lam, (v * β₀) y ∈ Λ₂ := fun y hy => by
    rw [← hgm]; exact (gmap_apply_mem (v * β₀) γ.lam y).2 hy
  have hβo : ∀ m ∈ orth (VS D) (Xsp (repF γ)), (v * β₀) m ∈ orth (VS D) (Xsp (liftF F'₂)) := fun m hm => by
    have h1 := hβ₀o m hm
    have h2 := hvX _ h1
    have e : (v * β₀) m = (v (β₀ m) - β₀ m) + β₀ m := by show v (β₀ m) = _; abel
    rw [e]
    exact add_mem (BwdNA.X_le_orth (VS D) (Xsp (liftF F'₂)) (fun x hx y hy => NMoveP.hT_X_X F'₂.fl hx hy) h2) h1
  have hXo : Xsp (lf D F0) ≤ orth (VS D) (Xsp (lf D F0)) :=
    BwdNA.X_le_orth (VS D) (Xsp (lf D F0)) (fun x hx y hy => NMoveP.hT_X_X F0 hx hy)
  have hXo' : Xsp (repF γ) ≤ orth (VS D) (Xsp (repF γ)) :=
    BwdNA.X_le_orth (VS D) (Xsp (repF γ)) (fun x hx y hy => NMoveP.hT_X_X (repF γ).fl hx hy)

  have hA1 : ∀ p, ∀ w ∈ lattice₂ D Zd.M p γ.lam, w ∈ (locH Zd p).X (tLoc Zd p γ).f →
      w ∈ lattice₂ D Zd.M p (XLam γ.lam (lf D F0)) := fun p w hw hwX =>
    l1 Zd p (lf D F0) _ (TermLoc.sgnP D p) (sgnP_mem p) (fun i => by rw [tf, frame_cs]) (hpr1 p) hXS1 hw hwX
  have hA2 : ∀ p, ∀ w ∈ lattice₂ D Zd.M p Λ₂, w ∈ (locH Zd p).X (tLoc Zd p γ).f →
      w ∈ lattice₂ D Zd.M p (XLam Λ₂ (lf D F0)) := fun p w hw hwX =>
    l1 Zd p (lf D F0) _ (TermLoc.sgnP D p) (sgnP_mem p) (fun i => by rw [tf, frame_cs]) (hpr2 p) hXS2 hw hwX
  have hB1 : ∀ p, ∀ w ∈ lattice₂ D Zd.M p γ.lam, w ∈ (locH Zd p).X (tLoc Zd p γ).f' →
      w ∈ lattice₂ D Zd.M p (XLam γ.lam (repF γ)) := fun p w hw hwX =>
    l1 Zd p (repF γ) _ (sgnP' D p) (sgnP'_mem p) (fun i => by rw [BetaI.locF'_eq, frame_csG]; rfl) (hpr1' p) hXSx hw
      (Xle_tLoc Zd p γ hwX)
  have hB2 : ∀ p, ∀ w ∈ lattice₂ D Zd.M p Λ₂, w ∈ (locH Zd p).X (locF' Zd p F'₂) →
      w ∈ lattice₂ D Zd.M p (XLam Λ₂ (liftF F'₂)) := fun p w hw hwX =>
    l1 Zd p (liftF F'₂) _ (sgnP' D p) (sgnP'_mem p) (fun i => by rw [BetaI.locF'_eq, frame_csG]; rfl) (hpr2' p) hXS2'
      hw hwX
  intro x' hx' l hl l₂ hl₂ hll₂
  have hx'Λ := (Submodule.mem_inf.1 hx').1
  have hx'o : x' ∈ orth (VS D) (Xsp (repF γ)) := (Submodule.mem_inf.1 hx').2
  have hlΛ := (Submodule.mem_inf.1 hl).1
  have hlo : l ∈ orth (VS D) (Xsp (lf D F0)) := (Submodule.mem_inf.1 hl).2
  have hl₂Λ := (Submodule.mem_inf.1 hl₂).1
  have hl₂o : l₂ ∈ orth (VS D) (Xsp (lf D F0)) := (Submodule.mem_inf.1 hl₂).2
  have hβd : ∀ m ∈ orth (VS D) (Xsp (repF γ)), β₀ m - (v * β₀) m ∈ Xsp (liftF F'₂) := fun m hm => by
    have h := hvX _ (hβ₀o _ hm)
    have e : β₀ m - (v * β₀) m = -(v (β₀ m) - β₀ m) := by show _ - v _ = _; abel
    rw [e]; exact neg_mem h
  have hXo₂ : Xsp (liftF F'₂) ≤ orth (VS D) (Xsp (liftF F'₂)) :=
    BwdNA.X_le_orth (VS D) (Xsp (liftF F'₂)) (fun x hx y hy => NMoveP.hT_X_X F'₂.fl hx hy)
  have hRp : ∀ p (g : Loc.SplitG (Zd.M p).L), (Zd.M p).split = some g →
      Prod.map (φ' p) (LinearEquiv.refl (D.s.atP p).Ep ((locH Zd p).Wb (tLoc Zd p γ).f)) ''
        (locH Zd p).iotaGraph g (tLoc Zd p γ) = (locH Zd p).iotaGraph g (IotaBP.t2 Zd p γ F'₂ Λ₂) := fun p g hsp => by
    have := (hloc₂ p).2.2.2.2.2 g hsp
    rw [hφ p] at this
    exact this
  constructor
  · intro hmem
    obtain ⟨μ, hμ, ξ, hξ, ξ', hξ', heq⟩ := NgX_dec hmem
    first
    | refine mem_of_bcP Zd (IotaBP.isLattice_NgX hΛ₂full _ _) fun p => ?_
    | refine mem_of_bcP Zd (IotaBP.isLattice_NgX_aux hΛ₂full _ _) fun p => ?_
    rcases hsp : (Zd.M p).split with _ | g
    · exact untyped_mem Zd p hsp _ _ (BwdNP.baseChange_mem_localLattice Zd (sub_mem hl₂Λ (hβΛ _ hx'Λ)) p)
    · exact IotaBP.fwd_typed Zd p g hsp γ F'₂ Λ₂ (φ' p) (hRp p g hsp) β₀ (v * β₀)
        (hP γ Z F'₂ φ φ' Λ₂ hB0 β₀ hiso hfr hW hO p) hβ₀o hβo hβd hβX hβΛ (hu p) hXo hXo' (hA2 p) (hB2 p)
        hx'Λ hx'o hlΛ hlo hl₂Λ hl₂o hll₂ hμ hξ hξ' heq
  · intro hmem
    obtain ⟨μ, hμ, ξ, hξ, ξ', hξ', heq⟩ := NgX_dec hmem
    first
    | refine mem_of_bcP Zd (IotaBP.isLattice_NgX hΛfull _ _) fun p => ?_
    | refine mem_of_bcP Zd (IotaBP.isLattice_NgX_aux hΛfull.toIsLattice _ _) fun p => ?_
    rcases hsp : (Zd.M p).split with _ | g
    · exact untyped_mem Zd p hsp _ _ (BwdNP.baseChange_mem_localLattice Zd (sub_mem hlΛ hx'Λ) p)
    · exact IotaBP.bwd_typed Zd p g hsp γ F'₂ Λ₂ (φ' p) (hRp p g hsp) β₀ (v * β₀)
        (hP γ Z F'₂ φ φ' Λ₂ hB0 β₀ hiso hfr hW hO p) hβ₀o hβo hβd hβΛ (hu p) hXo hXo₂ (hA1 p) (hB1 p)
        hx'Λ hx'o hlΛ hlo hl₂Λ hl₂o hll₂ hμ hξ hξ' heq

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
