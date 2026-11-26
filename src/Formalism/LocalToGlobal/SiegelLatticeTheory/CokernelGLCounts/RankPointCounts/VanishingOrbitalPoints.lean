module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepNormOneOfLeaves
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LeadingMinors
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GflagSwap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PSurjF
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfQ
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarMinors

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.VanishingOrbitalPoints
noncomputable section

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.NGCut.VanishingOrbitalPoints

theorem stepNormOne_of_ooVanish
    (hOV : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X)) :
    Formalism.L2.SG.NGCut.StepNormOne :=
  Formalism.L2.SG.NGCut.LeadingMinorIntegrality.stepNormOne_of hOV fun D X Y u u' => Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u'

theorem stepPoints_of_ooVanish
    (hOV : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X)) :
    Formalism.L2.SG.NGCut.StepPoints :=
  Formalism.L2.SG.NGCut.PtPf.stepPoints_of hOV fun D X Y u u' => Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u'



end Formalism.L2.SG.NGCut.VanishingOrbitalPoints
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeadingMinorEqPointMinor
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem leadingMinor_eq_pointMinor {D : D7} {n : ℕ} (w : Point D.host.E n) (l : ℕ) (hl : l ≤ n) :
    Formalism.HermitianLatticeCounting.ExpansionTerms.leadingPrincipalMinor (ptMat w) l = Formalism.MainNotions.S.LocalSplitGroups.Dmin w l := by
  unfold Formalism.HermitianLatticeCounting.ExpansionTerms.leadingPrincipalMinor Formalism.MainNotions.S.LocalSplitGroups.Dmin
  rw [dite_eq_left hl]
  let e : Fin l ≃ {i : Fin n // (i : ℕ) < l} :=
    { toFun := fun j => ⟨Fin.castLE hl j, by simp⟩
      invFun := fun i => ⟨i.1, i.2⟩
      left_inv := fun j => by ext; simp
      right_inv := fun i => by ext; simp }
  rw [← Matrix.det_submatrix_equiv_self e]
  rfl

theorem conjF_star' {D : D7} (x : D.host.E) : D.conjF x = star x :=
  (D.conjF_eq x).trans (Formalism.BasicNotions.Examples₂.star_eq_conj (H := D.host) x).symm

theorem GPt_junk (D : D7) (u u' : D.what₂.Word) :
    GPt ((Tu D u : ℕ) * (Tu D u' : ℕ)) (toPts (Formalism.L2.SG.PairVal.junkPoint D u u')) = 0 := by
  have h := (Formalism.MainNotions.S.Inh.zero_of_gram_point_exists D u u').choose_spec
  unfold Formalism.MainNotions.S.LocalSplitGroups.Gpt at h
  unfold Formalism.L2.SG.PairVal.junkPoint GPt
  rw [LeadingMinorIntegrality.dlast_eq, LeadingMinorIntegrality.dr_eq, leadingMinor_eq_pointMinor _ _ le_rfl, leadingMinor_eq_pointMinor _ _ (Nat.le_succ _),
    ← conjF_star', ← conjF_star']
  convert h using 3
  all_goals first
    | rfl
    | (push_cast; rfl)
    | norm_cast

theorem GPt_ne_of_NGPt {D : D7} (TT : ℕ) (γ : PN.Pts D.host.E D.R.rS) (h : 1 ≤ NGPt D.host.rdE TT γ) :
    GPt TT γ ≠ 0 := by
  unfold NGPt at h
  intro h0
  rw [h0] at h
  simp [Fintype.card_ne_zero] at h
  linarith

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem gval_occ (t : TauC Y u u')
    (hG : 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) (ptPN t)) :
    Gval (lf D (X.Fu u)) t.frame = GPt ((Tu D u : ℕ) * (Tu D u' : ℕ)) (ptPN t) := by
  have hne := GPt_ne_of_NGPt _ _ hG
  by_cases h : ∃ w, t.toTerm.atPt w ∧ t.toTerm.relevant
  · obtain ⟨F', ⟨hP, hmk⟩, -, hcell⟩ := Formalism.L2.SG.PairVal.ptOf_spec t.toTerm h
    have h1 := LeadingMinorIntegrality.gpt_eq (T := Tu D u) (T' := Tu D u') (lf D (X.Fu u)) F' _ hcell
    rw [show ptPN t = toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm) from rfl, h1, ← Formalism.L2.SG.Pf.SatGram.gterm_G Y t]
    have hΛ := (Y.rowsOK u).1 t.lam t.mem
    show Formalism.L2.SG.TermDef.Gt _ _ _ t.toTerm.cls = _
    rw [← hmk]
    exact Formalism.L2.SG.TermDef.Gt_mk ((Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) t.lam hΛ).1) _
  · exfalso
    apply hne
    show GPt _ (toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm)) = 0
    unfold Formalism.L2.SG.PairVal.ptOf
    rw [dite_eq_right h]
    exact GPt_junk D u u'

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfD
noncomputable section

open ValuativeRel Matrix

namespace Formalism.MainNotions.S.Loc.HermSp.CohU

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V}

theorem coef_zero {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} (hN : GramInv H v) {c : ι → E}
    (h0 : ∀ i, H.h (∑ j, c j • v j) (v i) = 0) : c = 0 := by
  obtain ⟨N, -, hNG⟩ := hN
  have hG : H.gram v *ᵥ c = 0 := by
    funext i
    have h := h0 i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hL_apply, map_sum] at h
    simp only [map_smul, hL_apply, smul_eq_mul] at h
    simp only [Matrix.mulVec, dotProduct, HermSp.gram, Matrix.of_apply, Pi.zero_apply]
    rw [← h]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have h := congrArg (fun x => N *ᵥ x) hG
  simp only [Matrix.mulVec_mulVec, hNG, Matrix.one_mulVec, Matrix.mulVec_zero] at h
  exact h

theorem linInd_of_gramInv {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} (hN : GramInv H v) :
    LinearIndependent E v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h := coef_zero hN (c := g) (fun k => by rw [hg]; exact H.h_zero_left _)
  exact congrFun h i

theorem prim_of_gramInv {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} (hN : GramInv H v)
    {Λ : Submodule M.L.O V} (hI : ∀ x ∈ Λ, ∀ y ∈ Λ, H.h x y ∈ M.L.O) (hv : ∀ i, v i ∈ Λ) : H.Prim Λ v := by
  refine ⟨hv, linInd_of_gramInv hN, fun x hx hxs => ?_⟩
  obtain ⟨c, hc, hw⟩ := decomp hN hI hv hx
  have hw0 : x - ∑ j, c j • v j = 0 := eq_zero_of_orth hN (Submodule.sub_mem _ hxs (comb_mem_span v c)) hw
  rw [sub_eq_zero.1 hw0]
  exact Submodule.sum_mem _ fun j _ =>
    (Submodule.span M.L.O (Set.range v)).smul_mem (⟨c j, hc j⟩ : M.L.O) (Submodule.subset_span ⟨j, rfl⟩)

theorem prim_inr {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] {a : ι₁ → V}
    {b : ι₂ → V} (hN : GramInv H (Sum.elim a b)) {Λ : Submodule M.L.O V}
    (hI : ∀ x ∈ Λ, ∀ y ∈ Λ, H.h x y ∈ M.L.O) (hv : ∀ k, Sum.elim a b k ∈ Λ) : H.Prim Λ b := by
  refine ⟨fun j => hv (Sum.inr j), (linInd_of_gramInv hN).comp Sum.inr Sum.inr_injective, fun x hx hxs => ?_⟩
  obtain ⟨c, hc, hw⟩ := decomp hN hI hv hx
  have hsp : Submodule.span E (Set.range b) ≤ Submodule.span E (Set.range (Sum.elim a b)) :=
    Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨Sum.inr j, rfl⟩)
  have hw0 : x - ∑ k, c k • Sum.elim a b k = 0 :=
    eq_zero_of_orth hN (Submodule.sub_mem _ (hsp hxs) (comb_mem_span _ c)) hw
  have hx' : x = ∑ k, c k • Sum.elim a b k := sub_eq_zero.1 hw0
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hxs
  have hsum : ∑ k, Sum.elim (0 : ι₁ → E) e k • Sum.elim a b k = x := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_smul, Finset.sum_const_zero, zero_add]
    exact he
  have hz : ∑ k, (c k - Sum.elim (0 : ι₁ → E) e k) • Sum.elim a b k = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [hsum, ← hx', sub_self]
  have hce := Fintype.linearIndependent_iff.1 (linInd_of_gramInv hN) _ hz
  have hl : ∀ i, c (Sum.inl i) = 0 := fun i => by
    have h := hce (Sum.inl i)
    simpa using h
  have hx2 : x = ∑ j, c (Sum.inr j) • b j := by
    conv_lhs => rw [hx']
    rw [Fintype.sum_sum_type]
    simp [hl]
  rw [hx2]
  exact Submodule.sum_mem _ fun j _ =>
    (Submodule.span M.L.O (Set.range b)).smul_mem (⟨c (Sum.inr j), hc _⟩ : M.L.O) (Submodule.subset_span ⟨j, rfl⟩)

end Formalism.MainNotions.S.Loc.HermSp.CohU

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open CohCut

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem vP_eq {p : PlF D} (γ : TermDef.Term D u u' F0 what₂) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (hs : (Zd.M p).split = none) : vP Zd p γ F'₂ = Sum.elim (tLoc Zd p γ).f (locF' Zd p F'₂) := by
  unfold vP Formalism.MainNotions.S.Loc.HermSp.MMfam
  rw [hs]
  rfl

variable (u u' F0 what₂)

def CohInt : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    CohHyp Zd γ Z F'₂ φ' →
    {p | ¬ ∀ b, locF' Zd p F'₂ b ∈ lattice₂ D Zd.M p γ.lam}.Finite

def CohDG : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    CohHyp Zd γ Z F'₂ φ' →
    {p | ¬ (IsUnit ((locH Zd p).Dl (tLoc Zd p γ).f (locF' Zd p F'₂) (D.R.rS + 1)) ∧
      (locH Zd p).Gdet (tLoc Zd p γ).f (locF' Zd p F'₂) (tLoc Zd p γ).T (tLoc Zd p γ).T' ≠ 0)}.Finite

variable {u u' F0 what₂}

theorem cohGen_of (hInt : CohInt Zd u u' F0 what₂) (hDG : CohDG Zd u u' F0 what₂) (hGood : CohGood Zd u u' F0 what₂) :
    CohGen Zd u u' F0 what₂ := by
  intro hP γ Z F'₂ φ' hH
  refine (((hInt hP γ Z F'₂ φ' hH).union (hDG hP γ Z F'₂ φ' hH)).union
    ((hGood hP γ Z F'₂ φ' hH).union (split_finite Zd))).subset ?_
  intro p hp
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hn
  obtain ⟨⟨hi, hdg⟩, hN, hs⟩ := hn
  have hsn : (Zd.M p).split = none := Option.not_isSome_iff_eq_none.1 hs
  apply hp
  have T1 := hH.2.2.2 p
  have sd := T1.1.1.1
  have frf := T1.1.1.2.1
  have frf' := T1.1.1.2.2.1
  have hI : ∀ x ∈ lattice₂ D Zd.M p γ.lam, ∀ y ∈ lattice₂ D Zd.M p γ.lam, (locH Zd p).h x y ∈ (Zd.M p).L.O :=
    fun x hx => (sd.2.2 x).1 hx
  have hv' : ∀ k, Sum.elim (tLoc Zd p γ).f (locF' Zd p F'₂) k ∈ lattice₂ D Zd.M p γ.lam := by
    intro k
    cases k with
    | inl a => exact frf.1.1 a
    | inr b => exact hi b
  have hN' := hN
  rw [vP_eq Zd γ F'₂ hsn] at hN'
  have hv : ∀ k, vP Zd p γ F'₂ k ∈ lattice₂ D Zd.M p γ.lam := by
    rw [vP_eq Zd γ F'₂ hsn]
    exact hv'
  have hfr2 : (locH Zd p).IsFrame (lattice₂ D Zd.M p γ.lam) D.R.rS (locF' Zd p F'₂) (tLoc Zd p γ).T' :=
    ⟨Formalism.MainNotions.S.Loc.HermSp.CohU.prim_inr hN' hI hv', T1.2.2.1.1, T1.2.2.1.2, frf'.2.2.2.1, frf'.2.2.2.2⟩
  refine ⟨⟨sd, frf, hfr2, hdg.1, hdg.2, fun g hg => ?_⟩, ?_⟩
  · rw [hsn] at hg
    cases hg
  · exact Formalism.MainNotions.S.Loc.HermSp.CohU.prim_of_gramInv hN hI hv

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocEqOfLocFEq
noncomputable section

open scoped Classical
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.FrameGlobalPatching

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LatPatch : Prop :=
  ∀ (D : D7) (Zd : LocDat D) (Λ₀ : Submodule (𝓞 D.host.E) (VS D).V), Submodule.IsFullLattice D.host.E Λ₀ →
    ∀ Mf : ∀ p : PlF D, Submodule (Zd.M p).L.O (Vp D p),
      (∀ p, ∃ Λ' : Submodule (𝓞 D.host.E) (VS D).V, Submodule.IsFullLattice D.host.E Λ' ∧ Mf p = lattice₂ D Zd.M p Λ') →
      {p | Mf p ≠ lattice₂ D Zd.M p Λ₀}.Finite →
      ∃! Λ : Submodule (𝓞 D.host.E) (VS D).V, Submodule.IsFullLattice D.host.E Λ ∧ ∀ p, lattice₂ D Zd.M p Λ = Mf p

end Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.LocalDenominators

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem localLattice_eq_iff (Zd : LocDat D) (p : PlF D) {Λ₁ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V}
    (h₁ : Submodule.IsFullLattice D.host.E Λ₁) (h₂ : Submodule.IsFullLattice D.host.E Λ₂) :
    lattice₂ D Zd.M p Λ₁ = lattice₂ D Zd.M p Λ₂ ↔
      Formalism.HermitianLattices.Ext.L3.locF p.asIdeal Λ₁ = Formalism.HermitianLattices.Ext.L3.locF p.asIdeal Λ₂ := by
  haveI := p.isPrime
  letI := h₁
  letI := h₂
  have mem_iff {Λ : Submodule (𝓞 D.host.E) (VS D).V} [Submodule.IsFullLattice D.host.E Λ] (x : (VS D).V) :
      baseChange₂ D p x ∈ lattice₂ D Zd.M p Λ ↔ x ∈ Formalism.HermitianLattices.Ext.L3.locF p.asIdeal Λ :=
    baseChangeAt_mem_localLattice_iff Zd p (by infer_instance) x
  constructor
  · intro h
    ext x
    rw [← mem_iff (Λ := Λ₁), ← mem_iff (Λ := Λ₂), h]
  · intro h
    have key {A B : Submodule (𝓞 D.host.E) (VS D).V} [Submodule.IsFullLattice D.host.E B]
        (hAB : Formalism.HermitianLattices.Ext.L3.locF p.asIdeal A = Formalism.HermitianLattices.Ext.L3.locF p.asIdeal B) :
        lattice₂ D Zd.M p A ≤ lattice₂ D Zd.M p B := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, mem_iff, ← hAB]
      exact (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal A y).2
        ⟨1, fun h1 => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), by simpa using hy⟩
    exact le_antisymm (key h) (key h.symm)

section Loc

variable {V : Type} [AddCommGroup V] [Module (𝓞 D.host.E) V]

theorem loc_of_locF (p : PlF D) {P : Ideal (𝓞 D.host.E)} (hP : P.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal)
    (B : Submodule (𝓞 D.host.E) V) {x : V} (hx : x ∈ Formalism.HermitianLattices.Ext.L3.locF p.asIdeal B) :
    x ∈ PI.LatLocGlob.loc P B := by
  haveI := p.isPrime
  obtain ⟨t, ht, htx⟩ := (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal B x).1 hx
  refine ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t, fun h => ht ?_, htx⟩
  rw [← hP]; exact h

theorem locF_of_loc (p : PlF D) (B : Submodule (𝓞 D.host.E) V) {x : V}
    (hx : ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal → P.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal →
      x ∈ PI.LatLocGlob.loc P B) :
    x ∈ Formalism.HermitianLattices.Ext.L3.locF p.asIdeal B := by
  haveI := p.isPrime
  let I : Ideal (𝓞 D.host.E) :=
    { carrier := {a | a • x ∈ B}
      add_mem' := fun {a c} ha hc => by simp only [Set.mem_setOf_eq, add_smul] at *; exact B.add_mem ha hc
      zero_mem' := by simp
      smul_mem' := fun c a ha => by simp only [Set.mem_setOf_eq, smul_eq_mul, mul_smul] at *; exact B.smul_mem c ha }
  by_contra hnot
  have hle : I.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ p.asIdeal := by
    intro t ht
    by_contra htp
    exact hnot ((Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal B x).2 ⟨t, htp, ht⟩)
  obtain ⟨Q, hIQ, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal I hle
  have hQm : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := 𝓞 D.host.F) Q (by rw [hQp]; exact p.isMaximal)
  obtain ⟨s, hs, hsx⟩ := hx Q hQm hQp
  exact hs (hIQ hsx)

end Loc

section Patch

variable {V : Type} [AddCommGroup V] [Module (𝓞 D.host.E) V]

theorem loc_locF (p : PlF D) {P : Ideal (𝓞 D.host.E)} (hPp : P.IsPrime)
    (hP : P.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal) (A : Submodule (𝓞 D.host.E) V) {x : V}
    (hx : x ∈ PI.LatLocGlob.loc P (Formalism.HermitianLattices.Ext.L3.locF p.asIdeal A)) : x ∈ PI.LatLocGlob.loc P A := by
  haveI := p.isPrime
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨t, ht, htx⟩ := (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal A _).1 hsx
  refine ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t * s, fun h => (hPp.mem_or_mem h).elim (fun h1 => ht ?_) hs, ?_⟩
  · rw [← hP]; exact h1
  · rw [mul_smul]; exact htx

theorem loc_eq_of_locF_eq (p : PlF D) {P : Ideal (𝓞 D.host.E)} (hPp : P.IsPrime)
    (hP : P.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal) {A B : Submodule (𝓞 D.host.E) V}
    (h : Formalism.HermitianLattices.Ext.L3.locF p.asIdeal A = Formalism.HermitianLattices.Ext.L3.locF p.asIdeal B) :
    PI.LatLocGlob.loc P A = PI.LatLocGlob.loc P B := by
  haveI := p.isPrime
  have sub : ∀ {A B : Submodule (𝓞 D.host.E) V}, Formalism.HermitianLattices.Ext.L3.locF p.asIdeal A = Formalism.HermitianLattices.Ext.L3.locF p.asIdeal B →
      PI.LatLocGlob.loc P A ⊆ PI.LatLocGlob.loc P B := by
    intro A B hAB x hx
    obtain ⟨s, hs, hsx⟩ := hx
    have h1 : s • x ∈ Formalism.HermitianLattices.Ext.L3.locF p.asIdeal B := by
      rw [← hAB]
      exact (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal A _).2
        ⟨1, fun h1 => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), by simpa using hsx⟩
    exact loc_locF p hPp hP B ⟨s, hs, h1⟩
  exact Set.Subset.antisymm (sub h) (sub h.symm)

theorem comap_ne_bot {P : Ideal (𝓞 D.host.E)} (hP : P.IsMaximal) :
    P.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≠ ⊥ := by
  have hne : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField D.host.E)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact Ideal.comap_ne_bot_of_integral_mem ha0 ha (Algebra.IsIntegral.isIntegral (R := 𝓞 D.host.F) a)

def plOf (P : Ideal (𝓞 D.host.E)) (hP : P.IsMaximal) : PlF D :=
  ⟨P.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)), Ideal.comap_isPrime _ _, comap_ne_bot hP⟩

theorem finite_over (p : PlF D) :
    {P : Ideal (𝓞 D.host.E) | P.IsMaximal ∧ P.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal}.Finite := by
  have hmap : p.asIdeal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
    exact p.ne_bot
  refine ((Ideal.finite_factors hmap).image HeightOneSpectrum.asIdeal).subset ?_
  rintro P ⟨hPm, hPp⟩
  have hne : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hPm (RingOfIntegers.not_isField D.host.E)
  refine ⟨⟨P, hPm.isPrime, hne⟩, ?_, rfl⟩
  show P ∣ _
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, hPp]

end Patch

theorem latPatch_holds : Formalism.L2.SG.Pf.FrameGlobalPatching.LatPatch := by
  intro D Zd Λ₀ hΛ₀ Mf hMf hfin
  choose Λ' hΛ' hMΛ' using hMf
  have hfullΛ (L : Submodule (𝓞 D.host.E) (VS D).V) (hL : Submodule.IsFullLattice D.host.E L) :
      PI.LatLocGlob.IsFullLat D.host.E L := ⟨hL.toIsLattice.fg, hL.span_eq_top⟩
  let M : Ideal (𝓞 D.host.E) → Set (VS D).V := fun P =>
    if hP : P.IsMaximal then PI.LatLocGlob.loc P (Λ' (plOf P hP)) else ∅
  have hMP : ∀ P (hP : P.IsMaximal), M P = PI.LatLocGlob.loc P (Λ' (plOf P hP)) := fun P hP => by
    simp only [M, dif_pos hP]
  have hexc : {P : Ideal (𝓞 D.host.E) | P.IsMaximal ∧ M P ≠ PI.LatLocGlob.loc P Λ₀}.Finite := by
    refine (hfin.biUnion fun p _ => finite_over p).subset ?_
    rintro P ⟨hPm, hne⟩
    refine Set.mem_biUnion (x := plOf P hPm) ?_ ⟨hPm, rfl⟩
    intro heq
    apply hne
    rw [hMP P hPm]
    have h1 : lattice₂ D Zd.M (plOf P hPm) (Λ' (plOf P hPm)) = lattice₂ D Zd.M (plOf P hPm) Λ₀ := by
      rw [← hMΛ']; by_contra h; exact h (by simpa using heq) |>.elim
    exact loc_eq_of_locF_eq (plOf P hPm) hPm.isPrime rfl ((localLattice_eq_iff Zd _ (hΛ' _) hΛ₀).1 h1)
  obtain ⟨L, ⟨hLfull, hLloc⟩, huniq⟩ := latLocGlob (𝓞 D.host.E) D.host.E (VS D).V Λ₀ (hfullΛ Λ₀ hΛ₀) M
    (fun P hP => ⟨Λ' (plOf P hP), hfullΛ _ (hΛ' _), hMP P hP⟩) hexc
  have hL : Submodule.IsFullLattice D.host.E L := by
    letI := Submodule.IsLattice.of_fg D.host.E hLfull.1
    exact ⟨hLfull.2⟩
  have hlocP : ∀ (p : PlF D) (P : Ideal (𝓞 D.host.E)), P.IsMaximal →
      P.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal →
      PI.LatLocGlob.loc P L = PI.LatLocGlob.loc P (Λ' p) := by
    intro p P hPm hPp
    rw [hLloc P hPm, hMP P hPm]
    have : plOf P hPm = p := HeightOneSpectrum.ext hPp
    rw [this]
  have hlocF : ∀ p : PlF D, Formalism.HermitianLattices.Ext.L3.locF p.asIdeal L = Formalism.HermitianLattices.Ext.L3.locF p.asIdeal (Λ' p) := by
    intro p
    ext x
    constructor
    · intro hx
      refine locF_of_loc p _ fun P hPm hPp => ?_
      rw [← hlocP p P hPm hPp]
      exact loc_of_locF p hPp L hx
    · intro hx
      refine locF_of_loc p _ fun P hPm hPp => ?_
      rw [hlocP p P hPm hPp]
      exact loc_of_locF p hPp _ hx
  refine ⟨L, ⟨hL, fun p => ?_⟩, ?_⟩
  · rw [hMΛ' p]
    exact (localLattice_eq_iff Zd p hL (hΛ' p)).2 (hlocF p)
  · rintro Λ ⟨hΛ, hΛp⟩
    have h1 : ∀ p : PlF D, Formalism.HermitianLattices.Ext.L3.locF p.asIdeal Λ = Formalism.HermitianLattices.Ext.L3.locF p.asIdeal L := fun p =>
      ((localLattice_eq_iff Zd p hΛ (hΛ' p)).1 ((hΛp p).trans (hMΛ' p))).trans (hlocF p).symm
    have sub : ∀ {A B : Submodule (𝓞 D.host.E) (VS D).V}, Submodule.IsLattice D.host.E B →
        (∀ p : PlF D, Formalism.HermitianLattices.Ext.L3.locF p.asIdeal A = Formalism.HermitianLattices.Ext.L3.locF p.asIdeal B) → A ≤ B := by
      intro A B hB hAB x hx
      refine PI.UnitaryGroupMassFormula.UJClassMass.interLocF (F := D.host.F) B hB x fun v => ?_
      haveI := v.isPrime
      have h2 : x ∈ Formalism.HermitianLattices.Ext.L3.locF v.asIdeal B := by
        rw [← hAB v]
        exact (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF v.asIdeal A x).2
          ⟨1, fun h1 => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), by simpa using hx⟩
      exact (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF v.asIdeal B x).1 h2
    exact le_antisymm (sub hL.toIsLattice h1) (sub hΛ.toIsLattice fun p => (h1 p).symm)

end Formalism.L2.SG.Pf.LocalDenominators
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPf
namespace Formalism.L2.SG.Pf.StabIntSh

theorem stabIntShape (D : Formalism.BasicNotions.D7) : StabIntShapeC D :=
  stabIntShape_of locShapeL locShapeG locGlob shapeNZ

end Formalism.L2.SG.Pf.StabIntSh
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarGenLoc
noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem starGenLoc_of_P (hP : CtxP u u' F0 what₂) : StarGenLoc Zd u u' F0 what₂ := by
  intro γ w hγ p
  have hR : IsRowLat D F0 γ.lam := hP.2.1.1 γ.lam γ.mem
  obtain ⟨hgen, hG⟩ := hγ.1
  obtain ⟨h2, h2e⟩ := starRepF_rep γ
  obtain ⟨F', ⟨h1, h1e⟩, hF'⟩ := hgen
  have hrel := (Formalism.L2.SG.Pf.double_coset_equivalence γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') ⟨F', h1⟩ ⟨repF γ, h2⟩).1
    (h1e.trans h2e.symm)
  have hgenR : IsGeneric γ.lam (gS D) (lf D F0) (repF γ) :=
    (PI.TermAttrConst.UnitaryGroupMassFormula.genericity_constant_double_cosets D u u' F0 γ.lam hR ⟨F', h1⟩ ⟨repF γ, h2⟩ hrel).1 hF'
  have hrel2 := (Formalism.L2.SG.Pf.double_coset_equivalence γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') (Quot.out γ.cls)
    ⟨repF γ, h2⟩).1 ((Quot.out_eq γ.cls).trans h2e.symm)
  have hGv : Gval (lf D F0) (repF γ) ≠ 0 := by
    intro hz
    apply hG
    exact (Formalism.L2.SG.Pf.gval_rel (lf D F0) hrel2).symm.trans hz
  exact (Formalism.L2.SG.Pf.frameGenLoc_holds D Zd F0 γ.lam (repF γ) hR h2
    (Formalism.L2.SG.Pf.m_plus_independent _ _ _ _) hGv).1 hgenR p

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBeta
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

namespace BwdBetaCut

def TermHyp (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) : Prop :=
  IsTerm Λ₂ (gS D) (lf D F0) (liftF F'₂) ∧ AdmWit Λ₂ (gS D) (lf D F0) (liftF F'₂) 1 ∧
    IsGeneric Λ₂ (gS D) (lf D F0) (liftF F'₂) ∧ FrameOK D Λ₂ (liftF F'₂)

end BwdBetaCut

open BwdBetaCut

variable (u u' F0 what₂)

def BwdBeta' : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' →
      ∀ Λ₂ ∈ GlobSet Zd γ F'₂ φ φ', ∀ (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ unipotentFrameFixers F0),
        (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V) →
        TermHyp (F0 := F0) Λ₂ F'₂ →
        ∃ x : Carrier (PD D γ.lam (lf D F0) u'), TermDef.mk _ _ _ x = γ.cls ∧ Gval (lf D F0) x.1 ≠ 0 ∧
          ∃ β : (VS D).V ≃ₗ[D.host.E] (VS D).V,
            IsPair γ.lam (lf D F0) x.1 (mapL n (isom_of_N0F hn) (liftF F'₂)) β (gS D) ∧
            Lat.s0 γ.lam (lf D F0) x.1 (mapL n (isom_of_N0F hn) (liftF F'₂)) β D.R.k = 1 ∧
            IsScalar γ.lam (lf D F0) x.1 (mapL n (isom_of_N0F hn) (liftF F'₂)) β

def RepG : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∃ x : Carrier (PD D γ.lam (lf D F0) u'), x.1 = repF γ ∧ TermDef.mk _ _ _ x = γ.cls ∧ Gval (lf D F0) x.1 ≠ 0

def BetaCore : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' →
      ∀ Λ₂ ∈ GlobSet Zd γ F'₂ φ φ', ∀ (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ unipotentFrameFixers F0),
        (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V) →
        TermHyp (F0 := F0) Λ₂ F'₂ → PD D γ.lam (lf D F0) u' (repF γ) → Gval (lf D F0) (repF γ) ≠ 0 →
        ∃ β : (VS D).V ≃ₗ[D.host.E] (VS D).V,
          IsPair γ.lam (lf D F0) (repF γ) (mapL n (isom_of_N0F hn) (liftF F'₂)) β (gS D) ∧
          Hp γ.lam (lf D F0) (repF γ) ≤ Th γ.lam (lf D F0) (repF γ) (mapL n (isom_of_N0F hn) (liftF F'₂)) β ∧
          IsScalar γ.lam (lf D F0) (repF γ) (mapL n (isom_of_N0F hn) (liftF F'₂)) β

variable {u u' F0 what₂}

theorem bwdBeta'_of_core (hR : RepG u u' F0 what₂) (hB : BetaCore Zd u u' F0 what₂) : BwdBeta' Zd u u' F0 what₂ := by
  intro hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ n hn himg hT
  obtain ⟨x, hx, hmk, hG⟩ := hR hC γ Z hZ
  have hPD : PD D γ.lam (lf D F0) u' (repF γ) := hx ▸ x.2
  have hG' : Gval (lf D F0) (repF γ) ≠ 0 := hx ▸ hG
  obtain ⟨β, hP, hle, hsc⟩ := hB hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ n hn himg hT hPD hG'
  have hrow := hC.2.1.1 γ.lam γ.mem
  have hfix := hrow.2.1
  refine ⟨x, hmk, hG, β, hx ▸ hP, ?_, hx ▸ hsc⟩
  rw [hx]
  refine (Formalism.L2.SG.NGCut.CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k (Corank.finrank_VS D) γ.lam hrow.1.1 (lf D F0) (repF γ) _ β
    hfix.2.2.1 hPD.1 hG').2 ?_
  exact le_antisymm (PI.PairCorankPos.W.Th_le_Hp _ _ _ _ _) hle

theorem bwdPair_of'' (h2 : BwdTerm' Zd u u' F0 what₂) (h4 : BwdBeta' Zd u u' F0 what₂) : BwdPair Zd u u' F0 what₂ := by
  intro hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ n hn himg
  have hT := h2 hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ ⟨n, hn, himg⟩
  obtain ⟨hT1, hA, hG, hO⟩ := hT
  have hE := mem_EZ_of hn γ.lam Λ₂ (gmap_eq_of_image himg) (liftF F'₂) Z hT1 hA hG hO hS.1
  obtain ⟨x, hx, hGx, β, hP, hs0, hsc⟩ := h4 hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ n hn himg ⟨hT1, hA, hG, hO⟩
  have hPD : PD D γ.lam (lf D F0) u' (mapL n (isom_of_N0F hn) (liftF F'₂)) := ⟨hE.1.1, hE.1.2.1, hE.2.2.2.1⟩
  let pr : Corank.Pair D u u' F0 what₂ :=
    ⟨γ.lam, γ.mem, x, ⟨_, hPD⟩, hGx, hE.1.2.2, β, hP⟩
  refine ⟨⟨γ.lam, γ.mem, TermDef.mk _ _ _ ⟨_, hPD⟩⟩, ⟨pr, ?_, rfl, hs0, hsc⟩, hPD, rfl⟩
  exact congrArg (fun c => (⟨γ.lam, γ.mem, c⟩ : TermDef.Term D u u' F0 what₂)) hx

theorem bwdC_of''' (hC : CtxP u u' F0 what₂) (h1 : BwdN Zd u u' F0 what₂) (h2 : BwdTerm' Zd u u' F0 what₂)
    (h4 : BwdBeta' Zd u u' F0 what₂) : BwdC Zd u u' F0 what₂ := by
  intro γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂
  obtain ⟨n, hn, himg⟩ := h1 hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂
  obtain ⟨hT, hA, hG, hO⟩ := h2 hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ ⟨n, hn, himg⟩
  refine ⟨mapL n (isom_of_N0F hn) (liftF F'₂),
    ⟨?_, bwdPair_of'' Zd h2 h4 hC γ Z hZ F'₂ φ φ' hS Λ₂ hΛ₂ n hn himg⟩, n, hn, ⟨fun a => rfl, rfl⟩, himg⟩
  exact mem_EZ_of hn γ.lam Λ₂ (gmap_eq_of_image himg) (liftF F'₂) Z hT hA hG hO hS.1

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NegOnePowSq
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.InvAlgCf
noncomputable section

open scoped Classical
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
  Formalism.L2.SG.Pf.AtPt

namespace Formalism.L2.SG.Pf.FibD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (p : PlF D)

theorem frFac_cf (a : Fin (D.R.rS + 1)) :
    frFac Zd.δ p a = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a) := by
  rw [frFac_eq]; rfl

theorem inv_alg_cf (a : Fin (D.R.rS + 1)) :
    Ring.inverse (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a) := by
  have h1 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a) *
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a) = 1 := by
    rw [← map_mul, cf_cfi, map_one]
  have hu : IsUnit (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) := ⟨Units.mkOfMulEqOne _ _ h1, rfl⟩
  calc Ring.inverse (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a))
      = Ring.inverse (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) *
          (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) := by
        rw [h1, mul_one]
    _ = _ := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]

theorem lOf_eq (A B : Formalism.L2.SG.PairVal.MatR D) :
    Formalism.L2.SG.Pf.StabShape.lOf Zd.δ Zd.M p A B = Formalism.L2.SG.Pf.TupGlob.locL Zd p A B := by
  unfold Formalism.L2.SG.Pf.StabShape.lOf Formalism.L2.SG.Pf.TupGlob.locL
  cases hs : (Zd.M p).split with
  | none =>
    ext i j
    simp only [Formalism.L2.SG.Pf.StabShape.lL, Matrix.of_apply, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.map_apply,
      ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [frFac_cf, frFac_cf, RingHom.coe_coe, AlgEquiv.commutes, AlgEquiv.commutes, inv_alg_cf]
  | some g =>
    ext i j
    apply g.e.injective
    simp only [Formalism.L2.SG.Pf.StabShape.lG, glue, Matrix.of_apply, AlgEquiv.apply_symm_apply]
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.map_apply, Matrix.transpose_apply, Sg,
      ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      RingHom.comp_apply, adeleInfiniteComponent_apply, adele_ext_components, frFac_cf, AlgEquiv.commutes, Prod.algebraMap_apply, map_mul, map_pow,
      map_neg, map_one, Prod.fst_mul, Prod.snd_mul, Prod.pow_fst, Prod.pow_snd, Prod.fst_neg, Prod.snd_neg,
      Prod.fst_one, Prod.snd_one, Algebra.algebraMap_self, RingHom.id_apply]
    have h1 : ∀ a, cf Zd p a ≠ 0 := fun a => left_ne_zero_of_mul_eq_one (cf_cfi Zd p a)
    have h2 : ∀ a, cfi Zd p a = (cf Zd p a)⁻¹ := fun a => eq_inv_of_mul_eq_one_right (cf_cfi Zd p a)
    ext
    all_goals (simp only [h2, div_eq_mul_inv]; try ring)

end Formalism.L2.SG.Pf.FibD
end
end

noncomputable section

open scoped Classical
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
  Formalism.L2.SG.Pf.AtPt

namespace Formalism.L2.SG.Pf.FibD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (p : PlF D)

theorem neg_one_pow_sq {R : Type*} [CommRing R] (k : ℕ) : (-1 : R) ^ k * (-1) ^ k = 1 := by
  rw [← mul_pow]; simp

theorem ρOf_eq (A B : Formalism.L2.SG.PairVal.MatR D) :
    Formalism.L2.SG.Pf.StabShape.ρOf Zd.δ Zd.M p A B =
      Formalism.L2.SG.LsDatumB.sgnP p * Formalism.L2.SG.Pf.TupGlob.locR Zd p A B * Formalism.L2.SG.LsDatumB.sgnP p := by
  unfold Formalism.L2.SG.Pf.StabShape.ρOf Formalism.L2.SG.Pf.TupGlob.locR
  cases hs : (Zd.M p).split with
  | none =>
    ext i j
    simp only [Formalism.L2.SG.Pf.StabShape.ρL, Formalism.L2.SG.LsDatumB.sgnP, Matrix.of_apply, Matrix.mul_apply,
      Matrix.diagonal_apply, Matrix.map_apply, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul, map_pow, map_neg, map_one]
    rw [frFac_cf, frFac_cf, inv_alg_cf]
    ring
  | some g =>
    ext i j
    apply g.e.injective
    simp only [Formalism.L2.SG.Pf.StabShape.ρG, glue, Formalism.L2.SG.LsDatumB.sgnP, Matrix.of_apply, Matrix.mul_apply,
      Matrix.diagonal_apply, Matrix.map_apply, Matrix.transpose_apply, Sg, ite_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul, map_pow, map_neg, map_one,
      AlgEquiv.apply_symm_apply, RingHom.comp_apply, adeleInfiniteComponent_apply, adele_ext_components, frFac_cf, AlgEquiv.commutes,
      Prod.algebraMap_apply, Prod.fst_mul, Prod.snd_mul, Prod.pow_fst, Prod.pow_snd, Prod.fst_neg, Prod.snd_neg,
      Prod.fst_one, Prod.snd_one, Algebra.algebraMap_self, RingHom.id_apply]
    have h2 : ∀ a, cfi Zd p a = (cf Zd p a)⁻¹ := fun a => eq_inv_of_mul_eq_one_right (cf_cfi Zd p a)
    have hs2 : ∀ k : ℕ, ((-1 : (D.s.atP p).Fp) ^ k) * (-1) ^ k = 1 := neg_one_pow_sq
    ext
    · simp only [Prod.fst_mul, Prod.pow_fst, Prod.fst_neg, Prod.fst_one, h2, div_eq_mul_inv]; ring
    · simp only [Prod.snd_mul, Prod.pow_snd, Prod.snd_neg, Prod.snd_one, h2, div_eq_mul_inv]
      linear_combination (-((g.e ((D.s.atP p).ιE (A j i))).2 * cf Zd p j * (cf Zd p i)⁻¹)) *
          hs2 (D.R.rS - i.val) +
        (-((g.e ((D.s.atP p).ιE (A j i))).2 * cf Zd p j * (cf Zd p i)⁻¹) *
          ((-1 : (D.s.atP p).Fp) ^ (D.R.rS - i.val) * (-1) ^ (D.R.rS - i.val))) * hs2 (D.R.rS - j.val)

end Formalism.L2.SG.Pf.FibD
end
end
