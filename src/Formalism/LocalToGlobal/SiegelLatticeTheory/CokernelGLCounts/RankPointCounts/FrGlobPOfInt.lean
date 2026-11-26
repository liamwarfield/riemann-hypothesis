module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprPfD
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StarExists2OfGood
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AdmissibleLocalPartner
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFrameIota
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaRat
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BwdTermHolds

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprClose
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaF
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarOmPartPf
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarOmDetPf
noncomputable section

open scoped Classical
open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Matrix

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

open OmP OmL

namespace OmD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (p : PlF D)

theorem mat_frameAct {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)) :
    (Matrix.of fun a b => (VS D).hT (F0.fvec a) (frameAct (frame F') ξ b)) =
      Zhat F0 F'.fl * ξ.map (algebraMap (𝓞 D.host.E) D.host.E) := by
  exact Matrix.ext fun a b => Formalism.L2.SG.Pf.AtPt.brS_frameAct (lf D F0) F' ξ a b

theorem map_det_eq {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (G : Fin (D.R.rS + 1) → (VS D).V) :
    ((Matrix.of fun a b => (VS D).hT (F0.fvec a) (G b)).map (D.s.atP p).ιE).det =
      (D.s.atP p).ιE (Matrix.of fun a b => (VS D).hT (F0.fvec a) (G b)).det := (RingHom.map_det _ _).symm

theorem det_ne_of_unit {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (G : Fin (D.R.rS + 1) → (VS D).V)
    (h : IsUnit ((locH Zd p).Zhat (fL Zd p F0) (gL Zd p G)).det) :
    (Matrix.of fun a b => (VS D).hT (F0.fvec a) (G b)).det ≠ 0 := by
  intro h0
  rw [zhat_fg, Matrix.det_mul, Matrix.det_mul, map_det_eq, h0, map_zero, mul_zero, zero_mul] at h
  exact not_isUnit_zero h

theorem gdl_eq {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : FlagG (VS D) D.R.rS T') (l : ℕ) :
    Formalism.L2.SG.Pf.ScalarFramePf.GDl F0.fvec F'.fvec l = Formalism.MainNotions.S.Dl F0 F' l := by
  unfold Formalism.L2.SG.Pf.ScalarFramePf.GDl Formalism.MainNotions.S.Dl leadMinorE
  split_ifs <;> rfl

end OmD

open OmD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

theorem modeMatrixDet_eq_adjointDet : OmDet Zd u u' F0 what₂ := by
  intro _ γ Z _ F'₂ φ φ' hS F' hP
  obtain ⟨p⟩ := Formalism.L2.SG.Pf.LocModel.plF_nonempty D
  have hT2 := hS.2.1 p
  have hunγ := hT2.1.1.2.2.2.1
  rw [dl_last] at hunγ
  have hdγ : (ZhatL (lf D F0) (repF γ)).det ≠ 0 := by
    have h1 := det_ne_of_unit Zd p F0
      (frameAct (frame (repF γ)) (admXi D γ.lam (lf D F0) (repF γ))⁻¹) hunγ
    rw [mat_frameAct, Matrix.det_mul] at h1
    exact left_ne_zero_of_mul h1
  refine ⟨hdγ, fun hZ => ?_⟩
  have hZ2 : (Matrix.of fun a b => (VS D).hT (F0.fvec a) (F'₂.fl.fvec b)) = Z := hS.1
  have hD2 : (locH Zd p).Dl (fL Zd p F0) (gL Zd p F'₂.fl.fvec) (D.R.rS + 1) = 0 := by
    rw [dl_last, zhat_fg, Matrix.det_mul, Matrix.det_mul, map_det_eq, hZ2, hZ, map_zero, mul_zero, zero_mul]
  have hId : (locH Zd p).Dl (tLoc Zd p γ).f (tLoc Zd p γ).f' D.R.rS *
      (locH Zd p).Dl (fL Zd p F0) (gL Zd p F'₂.fl.fvec) (D.R.rS + 1) =
      (locH Zd p).Dl (fL Zd p F0) (gL Zd p F'₂.fl.fvec) D.R.rS *
        (locH Zd p).Dl (tLoc Zd p γ).f (tLoc Zd p γ).f' (D.R.rS + 1) := hT2.2.2.2.1.2.2.2.2.2
  rw [hD2, mul_zero] at hId
  obtain ⟨uγ, huγ⟩ := hT2.1.1.2.2.2.1
  rw [← huγ] at hId
  have hDr := (Units.mul_left_eq_zero uγ).1 hId.symm
  have e := Formalism.L2.SG.Pf.ScalarFramePf.dl_loc Zd p F0.fvec F'₂.fl.fvec (Formalism.L2.SG.Pf.ScalarFramePf.sF Zd p)
    (Formalism.L2.SG.Pf.ScalarFramePf.sF' Zd p) D.R.rS (Nat.le_succ _)
  rw [show (locH Zd p).Dl (fL Zd p F0) (gL Zd p F'₂.fl.fvec) D.R.rS = _ from e] at hDr
  have hu1 : IsUnit (∏ i : Fin D.R.rS, (Zd.M p).L.cj
      (Formalism.L2.SG.Pf.ScalarFramePf.sF Zd p (Fin.castLE (Nat.le_succ _) i))) :=
    IsUnit.prod_univ_iff.2 fun i => (Formalism.L2.SG.Pf.ScalarFramePf.isUnit_sF Zd p _).map _
  have hu2 : IsUnit (∏ i : Fin D.R.rS, Formalism.L2.SG.Pf.ScalarFramePf.sF' Zd p (Fin.castLE (Nat.le_succ _) i)) :=
    IsUnit.prod_univ_iff.2 fun i => Formalism.L2.SG.Pf.ScalarFramePf.isUnit_sF' Zd p _
  have hg := (hu1.mul hu2).mul_right_eq_zero.1 hDr
  rw [map_eq_zero_iff _ (D.s.atP p).ιE.injective, gdl_eq] at hg
  have hG := hP.1.1.2.2
  apply hG
  apply Eq.trans (fwdCut_gval_congr (lf D F0) F' F'₂ (hP.1.2.2.2.2.trans hS.1.symm))
  show Formalism.MainNotions.S.Gflag F0 F'₂.fl = 0
  unfold Formalism.MainNotions.S.Gflag
  rw [PI.UnitaryGroupMassFormula.BetaLUniq.GN.Dl_succ, hg, show Zhat F0 F'₂.fl = Z from hS.1, hZ]
  simp

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarOmRepPf
noncomputable section

open scoped Classical
open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Matrix

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

open OmP

namespace OmR

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem mem_orth' {U : Submodule E S.V} {v : S.V} : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 :=
  PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S

theorem hswap (x y : S.V) : S.hT y x = star (S.hT x y) := NMoveP.hsw S x y

theorem orthX_of {T : E} (F : FlagG S r T) {v : S.V} (h : ∀ i, S.hT (F.e i) v = 0) : v ∈ orth S F.X :=
  mem_orth'.2 fun x hx => NMoveP.spanL S F.e v h x hx

theorem orthX_of_f {T : E} (F : FlagG S r T) {v : S.V} (h : ∀ a, S.hT (F.fvec a) v = 0) : v ∈ orth S F.X :=
  orthX_of F fun i => by rw [← fvec_cs]; exact h _

theorem om_orthX {T T' : E} {F : FlagG S r T} {F' : FlagG S r T'} {v : S.V} (h : OmV F F' v) :
    v ∈ orth S F.X :=
  orthX_of F fun i => by rw [← fvec_cs, h.2]; simp [Fin.castSucc_ne_last]

theorem z_orthX {T : E} (F : FlagG S r T) : F.z ∈ orth S F.X := orthX_of F F.z_orth

theorem X_le_sp {T : E} (F : FlagG S r T) : F.X ≤ Submodule.span E (Set.range F.fvec) := by
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨i.castSucc, fvec_cs F i⟩

section NL

variable {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V}

theorem nl_isom (hn : n ∈ NLam Λ F) (x y : S.V) : S.hT (n x) (n y) = S.hT x y := hn.1.1 x y

theorem e_mem_flag (F : LFlag S r T) (i : Fin r) : F.fl.e i ∈ Xflag F (i.1 + 1) :=
  Submodule.subset_span ⟨i, show i.1 < i.1 + 1 from Nat.lt_succ_self _, rfl⟩

theorem flag_le_X (F : LFlag S r T) (j : ℕ) : Xflag F j ≤ Xsp F :=
  Submodule.span_mono (Set.image_subset_range _ _)

theorem nl_e (hn : n ∈ NLam Λ F) (i : Fin r) : n (F.fl.e i) - F.fl.e i ∈ Xsp F :=
  flag_le_X F i.1 (hn.2.1 i.1 _ (e_mem_flag F i))

theorem nl_X (hn : n ∈ NLam Λ F) {x : S.V} (hx : x ∈ Xsp F) : n x ∈ Xsp F := by
  have : Xsp F ≤ (Xsp F).comap (n : S.V →ₗ[E] S.V) := by
    show Submodule.span E (Set.range F.fl.e) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show n (F.fl.e i) ∈ Xsp F
    have h := nl_e hn i
    have e : n (F.fl.e i) = (n (F.fl.e i) - F.fl.e i) + F.fl.e i := by abel
    rw [e]
    exact Submodule.add_mem _ h (Submodule.subset_span ⟨i, rfl⟩)
  exact this hx

theorem nl_orth (hn : n ∈ NLam Λ F) {v : S.V} (hv : v ∈ orth S (Xsp F)) : n v - v ∈ Xsp F := hn.2.2 v hv

theorem nl_symm_orth (hn : n ∈ NLam Λ F) {v : S.V} (hv : v ∈ orth S (Xsp F)) : n.symm v ∈ orth S (Xsp F) := by
  refine mem_orth'.2 fun x hx => ?_
  rw [← nl_isom hn x, LinearEquiv.apply_symm_apply]
  exact mem_orth'.1 hv _ (nl_X hn hx)

theorem sp_map_eq (hn : n ∈ NLam Λ F) :
    (Submodule.span E (Set.range F.fl.fvec)).map (n : S.V →ₗ[E] S.V) = Submodule.span E (Set.range F.fl.fvec) := by
  apply Submodule.eq_of_le_of_finrank_eq _ (LinearEquiv.finrank_map_eq n _)
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
  have hX := X_le_sp F.fl
  have e : (n : S.V →ₗ[E] S.V) (F.fl.fvec b) = F.fl.fvec b + (n (F.fl.fvec b) - F.fl.fvec b) := by
    simp
  rw [e]
  refine Submodule.add_mem _ (Submodule.subset_span ⟨b, rfl⟩) (hX ?_)
  refine Fin.lastCases ?_ (fun i => ?_) b
  · rw [fvec_last]; exact nl_orth hn (z_orthX F.fl)
  · rw [fvec_cs]; exact nl_e hn i

end NL

section DC

variable {Λ : Submodule (𝓞 E) S.V} {T T' : E} (F : LFlag S r T)

def Inv (Ωγ : S.V) (F₁ : LFlag S r T') : Prop := ∃ v, OmV F.fl F₁.fl v ∧ v - Ωγ ∈ Xsp F

def QU (F₁ : LFlag S r T') : Prop :=
  ∀ d ∈ Submodule.span E (Set.range F₁.fl.fvec), (∀ a, S.hT (F.fl.fvec a) d = 0) → d = 0

theorem qu_of_det (F₁ : LFlag S r T') (h : (Zhat F.fl F₁.fl).det ≠ 0) : QU F F₁ :=
  fun _ hd h0 => eq_zero_of_orth F.fl F₁.fl h hd h0

variable {F}

theorem sp_dc {F₁ F₂ : LFlag S r T'} {n m : S.V ≃ₗ[E] S.V} (hm : m ∈ NLam Λ F₁)
    (h : ∀ a, frame F₂ a = n (m (frame F₁ a))) :
    Submodule.span E (Set.range F₂.fl.fvec) = (Submodule.span E (Set.range F₁.fl.fvec)).map (n : S.V →ₗ[E] S.V) := by
  have e : F₂.fl.fvec = ((n : S.V →ₗ[E] S.V) ∘ₗ (m : S.V →ₗ[E] S.V)) ∘ F₁.fl.fvec := funext h
  rw [e, Set.range_comp, ← Submodule.map_span, Submodule.map_comp, sp_map_eq hm]

theorem inv_dc {Ωγ : S.V} {F₁ F₂ : LFlag S r T'} (h : DCRel Λ F F₁ F₂) : Inv F Ωγ F₁ ↔ Inv F Ωγ F₂ := by
  obtain ⟨n, hn, m, hm, hf, -⟩ := h
  have hsp := sp_dc hm hf
  constructor
  · rintro ⟨v, hv, hvγ⟩
    have hd := nl_orth hn (om_orthX hv)
    refine ⟨n v, ⟨?_, fun a => ?_⟩, ?_⟩
    · rw [hsp, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]; exact hv.1
    · have e : n v = v + (n v - v) := by abel
      rw [e, map_add (f := _), NMoveP.hT_f_X F.fl a hd, add_zero, hv.2]
    · have e : n v - Ωγ = (n v - v) + (v - Ωγ) := by abel
      rw [e]; exact Submodule.add_mem _ hd hvγ
  · rintro ⟨v, hv, hvγ⟩
    have ho := nl_symm_orth hn (om_orthX hv)
    have hd := nl_orth hn ho
    rw [LinearEquiv.apply_symm_apply] at hd
    refine ⟨n.symm v, ⟨?_, fun a => ?_⟩, ?_⟩
    · have h1 := hv.1
      rw [hsp, Submodule.mem_map_equiv] at h1
      exact h1
    · have e : n.symm v = v - (v - n.symm v) := by abel
      rw [e, map_sub, NMoveP.hT_f_X F.fl a hd, sub_zero, hv.2]
    · have e : n.symm v - Ωγ = (v - Ωγ) - (v - n.symm v) := by abel
      rw [e]; exact Submodule.sub_mem _ hvγ hd

theorem qu_dc {F₁ F₂ : LFlag S r T'} (h : DCRel Λ F F₁ F₂) : QU F F₁ ↔ QU F F₂ := by
  obtain ⟨n, hn, m, hm, hf, -⟩ := h
  have hsp := sp_dc hm hf
  constructor
  · intro hq d hd h0
    have ho : d ∈ orth S (Xsp F) := orthX_of_f F.fl h0
    have ho' := nl_symm_orth hn ho
    have hdd := nl_orth hn ho'
    rw [LinearEquiv.apply_symm_apply] at hdd
    rw [hsp, Submodule.mem_map_equiv] at hd
    have : n.symm d = 0 := hq _ hd fun a => by
      have e : n.symm d = d - (d - n.symm d) := by abel
      rw [e, map_sub, NMoveP.hT_f_X F.fl a hdd, sub_zero, h0]
    simpa using congrArg n this
  · intro hq d hd h0
    have ho : d ∈ orth S (Xsp F) := orthX_of_f F.fl h0
    have hdd := nl_orth hn ho
    have hnd : n d ∈ Submodule.span E (Set.range F₂.fl.fvec) := by
      rw [hsp, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]; exact hd
    have : n d = 0 := hq _ hnd fun a => by
      have e : n d = d + (n d - d) := by abel
      rw [e, map_add (f := _), NMoveP.hT_f_X F.fl a hdd, add_zero, h0]
    simpa using this

theorem inv_eqv {P : LFlag S r T' → Prop} {x y : Carrier P} (h : Relation.EqvGen (Rel Λ F P) x y)
    (I : LFlag S r T' → Prop) (hI : ∀ F₁ F₂, DCRel Λ F F₁ F₂ → (I F₁ ↔ I F₂)) : I x.1 ↔ I y.1 := by
  induction h with
  | rel a b hab => exact hI _ _ hab
  | refl => exact Iff.rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

end DC

section Pair

variable {Λ : Submodule (𝓞 E) S.V} {T T' : E}

theorem orth_orth (U : Submodule E S.V) : orth S (orth S U) = U := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · intro u hu
    refine mem_orth'.2 fun x hx => ?_
    rw [hswap, mem_orth'.1 hx u hu, star_zero]
  · have h1 := PI.UnitaryGroupMassFormula.BetaLUniq.finrank_orth_add S U
    have h2 := PI.UnitaryGroupMassFormula.BetaLUniq.finrank_orth_add S (orth S U)
    omega

theorem z_mem_UUE (F : LFlag S r T) (F' : LFlag S r T') (hF : IsLift Λ F) : F.fl.z ∈ UUE Λ F F' := by
  refine Submodule.subset_span ?_
  show F.fl.z ∈ (UU Λ F F' : Set S.V)
  rw [← hF.2]
  exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right
    (Submodule.mem_span_singleton_self _)))

theorem z'_mem_UUE (F : LFlag S r T) (F' : LFlag S r T') (hF' : IsLift Λ F') : F'.fl.z ∈ UUE Λ F F' := by
  refine Submodule.subset_span ?_
  show F'.fl.z ∈ (UU Λ F F' : Set S.V)
  rw [← hF'.2]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

theorem sp_le_UUE (hΛ : Submodule.IsFullLattice E Λ) (F : LFlag S r T) (F' : LFlag S r T') (hF' : IsLift Λ F') :
    Submodule.span E (Set.range F'.fl.fvec) ≤ UUE Λ F F' := by
  rw [Submodule.span_le]
  rintro _ ⟨b, rfl⟩
  refine Fin.lastCases ?_ (fun i => ?_) b
  · rw [fvec_last]; exact z'_mem_UUE F F' hF'
  · rw [fvec_cs]
    exact PI.UnitaryGroupMassFormula.BetaLUniq.Xsp_le_UUE' S Λ hΛ F F' (Submodule.subset_span ⟨i, rfl⟩)

theorem pair_core (hΛ : Submodule.IsFullLattice E Λ) (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V)
    (k : ℕ) (hLF : IsLift Λ F) (hL' : IsLift Λ F') (hL'' : IsLift Λ F'') (hG' : Gval F F' ≠ 0)
    (hdim : finrank E S.V = k + 2 * r + 1) (hT : T ≠ 0) (hs : s0 Λ F F' F'' β k = 1)
    (hsc : IsScalar Λ F F' F'' β) {Ω'' : S.V} (hΩ : OmV F.fl F''.fl Ω'') :
    ∃ w, OmV F.fl F'.fl w ∧ Ω'' - w ∈ Xsp F := by
  have n' := PI.UnitaryGroupMassFormula.BetaLUniq.gram_matrix_nondegenerate S Λ F F' hΛ hLF hL' hG'
  have hHp : finrank E (Hp Λ F F') + (2 * r + 2) = finrank E S.V := by
    have := PI.UnitaryGroupMassFormula.BetaLUniq.finrank_orth_add S (UUE Λ F F')
    rw [n'.1] at this
    exact this
  have hle : Th Λ F F' F'' β ≤ Hp Λ F F' := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hy
    simp only [ThPairs, Submodule.mem_inf, Submodule.mem_prod] at hp
    exact hp.1.1.1
  have hTh : Th Λ F F' F'' β = Hp Λ F F' := by
    apply Submodule.eq_of_le_of_finrank_le hle
    simp only [s0] at hs
    omega
  set ν : S.V := Ω'' + T⁻¹ • F.fl.z with hν
  have hzX : F.fl.z ∈ orth S (Xsp F) := z_orthX F.fl
  clear_value ν
  have hνX : ν ∈ orth S (Xsp F) := by
    rw [hν]; exact Submodule.add_mem _ (om_orthX hΩ) (Submodule.smul_mem _ _ hzX)
  have hνU'' : ν ∈ UUE Λ F F'' := by
    rw [hν]; exact Submodule.add_mem _ (sp_le_UUE hΛ F F'' hL'' hΩ.1) (Submodule.smul_mem _ _ (z_mem_UUE F F'' hLF))
  have hνH : ν ∈ orth S (Hp Λ F F') := by
    refine mem_orth'.2 fun x hx => ?_
    rw [← hTh] at hx
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
    simp only [ThPairs, Submodule.mem_inf, Submodule.mem_prod, Submodule.mem_comap, LinearMap.sub_apply,
      LinearMap.fst_apply, LinearMap.snd_apply] at hp
    have e : p.1 = p.2 + (p.1 - p.2) := by abel
    simp only [LinearMap.fst_apply]
    rw [e, LinearMap.map_add₂, mem_orth'.1 hνX _ hp.1.2]
    have h2 : S.hT ν p.2 = 0 := mem_orth'.1 hp.1.1.2 ν hνU''
    rw [hswap, h2, star_zero, add_zero]
  have hνU' : ν ∈ UUE Λ F F' := by
    have := hνH
    rw [show Hp Λ F F' = orth S (UUE Λ F F') from rfl, orth_orth] at this
    exact this
  have hzz : S.hT F.fl.z ν = 0 := by
    have h1 : S.hT F.fl.z Ω'' = 1 := by rw [← fvec_last, hΩ.2]; simp
    rw [hν, map_add (f := _), map_smul, h1, F.fl.z_norm, smul_eq_mul]
    field_simp
    ring
  have hνXp : ν ∈ orth S (Xplus F) := by
    refine mem_orth'.2 fun x hx => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hb
    rw [LinearMap.map_add₂, mem_orth'.1 hνX a ha, NMoveP.hT_smulL, hzz, mul_zero, add_zero]
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hΩ.1
  have hSg'' : SgRel F F'' ν 0 T⁻¹ (c (Fin.last r)) := by
    refine ⟨0, Submodule.zero_mem _, ∑ i : Fin r, c i.castSucc • F''.fl.e i,
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), ?_⟩
    rw [hLF.2, hL''.2, hν, ← hc, Fin.sum_univ_castSucc, fvec_last]
    simp only [fvec_cs, sub_zero, add_zero]
    abel
  have hY : ∀ {F₁ : LFlag S r T'}, ν ∈ UUE Λ F F₁ → ν ∈ Ylift Λ F F₁ := fun h => Submodule.mem_inf.2 ⟨h, hνXp⟩
  obtain ⟨x, hx, x', hx', hE⟩ := (hsc ν (hY hνU') ν (hY hνU'') 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _)
    (by simp) (by simp) T⁻¹ (c (Fin.last r))).2 hSg''
  refine ⟨Ω'' - x, ⟨?_, fun a => ?_⟩, by simpa using hx⟩
  · have e : Ω'' - x = c (Fin.last r) • F'.fl.z + x' := by
      rw [hLF.2, hL'.2, sub_zero, hν] at hE
      have := congrArg (fun v => v - T⁻¹ • F.fl.z - x) hE
      rw [show Ω'' - x = Ω'' + T⁻¹ • F.fl.z - T⁻¹ • F.fl.z - x by abel, this]
      abel
    rw [e]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.last r, fvec_last _⟩))
      (X_le_sp F'.fl hx')
  · rw [map_sub, NMoveP.hT_f_X F.fl a hx, sub_zero, hΩ.2]

end Pair

end OmR

open OmR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem omRep_repF (γ : TermDef.Term D u u' F0 what₂) :
    Rep γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') γ.cls (repF γ) := by
  unfold repF
  split
  · rename_i x hx
    unfold nrep at hx
    split_ifs at hx with h
    cases hx
    exact h.choose_spec.1
  · exact ⟨(Quot.out γ.cls).2, Quot.out_eq _⟩

variable (u u' F0 what₂)

theorem omega_representative_holds : OmRep u u' F0 what₂ := by
  intro hrows γ Z _ hdγ _ F' hP Ω' Ωγ h' hγ
  obtain ⟨-, γ', ⟨p, hp1, hp2, hpS⟩, hrep⟩ := hP
  have hrepγ := omRep_repF γ
  obtain ⟨lam, mem, cls⟩ := γ
  obtain ⟨lam', mem', cls'⟩ := γ'
  simp only [Corank.Pair.pfst] at hp1
  simp only [Corank.Pair.psnd] at hp2
  cases hp1
  cases hp2
  obtain ⟨hPγ, eγ⟩ := hrepγ
  obtain ⟨hP', e'⟩ := hrep
  have r1 := Quot.eqvGen_exact eγ
  have r2 := Quot.eqvGen_exact e'
  have hRL := hrows.1 p.lam p.mem
  have hΛ : Submodule.IsFullLattice D.host.E p.lam := hRL.1.1
  have hLF : IsLift p.lam (lf D F0) := hRL.2.1.2.2.1

  have i1 := (inv_eqv r1 (Inv (lf D F0) Ωγ) fun _ _ h => inv_dc h).1 ⟨Ωγ, hγ, by simp⟩
  have q1 := (inv_eqv r1 (QU (lf D F0)) fun _ _ h => qu_dc h).1 (qu_of_det _ _ hdγ)

  have i2 := (inv_eqv r2 (Inv (lf D F0) Ω') fun _ _ h => inv_dc h).1 ⟨Ω', h', by simp⟩
  obtain ⟨v', hv', hv'γ⟩ := i1
  obtain ⟨v'', hv'', hv''Ω⟩ := i2
  obtain ⟨w, hw, hw''⟩ := pair_core hΛ (lf D F0) p.fst.1 p.snd.1 p.beta D.R.k hLF p.fst.2.1 p.snd.2.1 p.G_fst
    (Corank.finrank_VS D) (Corank.tu_ne_zero u) hpS.1 hpS.2 hv''
  have e : v' = w := sub_eq_zero.1 (q1 _ (Submodule.sub_mem _ hv'.1 hw.1) fun a => by
    rw [map_sub, hv'.2, hw.2, sub_self])
  subst e
  have : Ω' - Ωγ = (v' - Ωγ) + (v'' - v') - (v'' - Ω') := by abel
  rw [this]
  exact Submodule.sub_mem _ (Submodule.add_mem _ hv'γ hw'') hv''Ω

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem omega_part_holds : OmPart Zd u u' F0 what₂ :=
  omPart_of Zd (modeMatrixDet_eq_adjointDet Zd u u' F0 what₂) (omega_local_holds Zd u u' F0 what₂) (omega_representative_holds u u' F0 what₂)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem bwdBeta'_of_leaves (hRat : BetaRat Zd u u' F0 what₂) (hInt : BetaInt Zd u u' F0 what₂) :
    BwdBeta' Zd u u' F0 what₂ :=
  bwdBeta'_of_core Zd repG_holds (betaCore_of₂ Zd (betaCore₂_of Zd hRat (scalarOf_holds Zd) hInt))

theorem fStarC_of_leaves' (hC : CtxP u u' F0 what₂) (hLP : LprPart Zd u u' F0 what₂)
    (hRat : BetaRat Zd u u' F0 what₂) (hInt : BetaInt Zd u u' F0 what₂) : FStarC Zd u u' F0 what₂ :=
  fStarC_of_route2 Zd (starExists2_holds Zd u u' F0 what₂ hC)
    (fwdC_of_loc Zd hC.2.1 (omega_part_holds Zd u u' F0 what₂) (genXi_holds Zd) hLP)
    (bwdC_of''' Zd hC (bwdN_holds Zd u u' F0 what₂) (bwdTerm'_holds Zd u u' F0 what₂) (bwdBeta'_of_leaves Zd hRat hInt))
    (Uniq.uniqC_holds Zd u u' F0 what₂)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprExist
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprExistB
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.LprEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}

theorem LprExistB_equiv {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : IsRowLat D F0 Λ) :
    Equivalence (Formalism.L2.SG.Corank.ScalRelD D u' F0 Λ) :=
  Formalism.L2.SG.Corank.scalarEquiv_of_G scalar_equiv_general u u' F0 Λ hΛ

theorem LprExistB_repFree : Formalism.L2.SG.Corank.ScalarRepFree D u u' :=
  scalar_rep_free D u u'

theorem scal_move {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : IsRowLat D F0 Λ)
    (x1 x2 y1 y2 : {x : Carrier (PD D Λ (lf D F0) u') // Gval (lf D F0) x.1 ≠ 0})
    (h1 : TermDef.mk Λ (lf D F0) (PD D Λ (lf D F0) u') x1.1 = TermDef.mk Λ (lf D F0) (PD D Λ (lf D F0) u') y1.1)
    (h2 : TermDef.mk Λ (lf D F0) (PD D Λ (lf D F0) u') x2.1 = TermDef.mk Λ (lf D F0) (PD D Λ (lf D F0) u') y2.1)
    (a : Formalism.L2.SG.Corank.ScalRelD D u' F0 Λ x1 x2) : Formalism.L2.SG.Corank.ScalRelD D u' F0 Λ y1 y2 := by
  have hEq := LprExistB_equiv (u := u) (u' := u') hΛ
  have hRF := LprExistB_repFree (D := D) (u := u) (u' := u') F0 Λ hΛ
  have r2 := (Formalism.L2.SG.Pf.double_coset_equivalence Λ (lf D F0) (PD D Λ (lf D F0) u') x2.1 y2.1).1 h2
  have a2 : Formalism.L2.SG.Corank.ScalRelD D u' F0 Λ x1 y2 := hRF x1 x2 y2 r2 a
  have r1 := (Formalism.L2.SG.Pf.double_coset_equivalence Λ (lf D F0) (PD D Λ (lf D F0) u') x1.1 y1.1).1 h1
  have a3 : Formalism.L2.SG.Corank.ScalRelD D u' F0 Λ y2 y1 := hRF y2 x1 y1 r1 (hEq.symm a2)
  exact hEq.symm a3

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.LprEx
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarLprExistA
noncomputable section

open scoped Classical
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel
  Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.LprEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Glob

variable {D : D7}

theorem LprExistA_iso_span {s : Set (VS D).V} (h : ∀ x ∈ s, ∀ y ∈ s, (VS D).hT x y = 0) :
    ∀ x ∈ Submodule.span D.host.E s, ∀ y ∈ Submodule.span D.host.E s, (VS D).hT x y = 0 := by
  have h1 : ∀ x ∈ s, ∀ y ∈ Submodule.span D.host.E s, (VS D).hT x y = 0 := by
    intro x hx y hy
    have hle : Submodule.span D.host.E s ≤ LinearMap.ker ((VS D).hT x) := by
      rw [Submodule.span_le]
      intro y' hy'
      exact h x hx y' hy'
    exact hle hy
  intro x hx y hy
  have hle : Submodule.span D.host.E s ≤ LinearMap.ker ((VS D).hT.flip y) := by
    rw [Submodule.span_le]
    intro x' hx'
    show (VS D).hT.flip y x' = 0
    rw [LinearMap.flip_apply]
    exact h1 x' hx' y hy
  have := hle hx
  rw [LinearMap.mem_ker, LinearMap.flip_apply] at this
  exact this

theorem LprExistA_orth_span {s : Set (VS D).V} {x : (VS D).V} (h : ∀ v ∈ s, (VS D).hT v x = 0) :
    ∀ v ∈ Submodule.span D.host.E s, (VS D).hT v x = 0 := by
  intro v hv
  have hle : Submodule.span D.host.E s ≤ LinearMap.ker ((VS D).hT.flip x) := by
    rw [Submodule.span_le]
    intro v' hv'
    show (VS D).hT.flip x v' = 0
    rw [LinearMap.flip_apply]
    exact h v' hv'
  have := hle hv
  rw [LinearMap.mem_ker, LinearMap.flip_apply] at this
  exact this

theorem gfacts_move {Λ : Submodule (𝓞 D.host.E) (VS D).V} {f g1 g2 g2' : Fin (D.R.rS + 1) → (VS D).V}
    {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hG : GFacts Λ f g1 g2' β)
    (hX : Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2' b.castSucc) =
      Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2 b.castSucc))
    (hsp : Submodule.span D.host.E (Set.range g2') = Submodule.span D.host.E (Set.range g2))
    (hz : g2' (Fin.last _) - g2 (Fin.last _) ∈
      Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2 b.castSucc))
    (ht : GDl f g2' (D.R.rS + 1) = GDl f g2 (D.R.rS + 1)) (hr : GDl f g2' D.R.rS = GDl f g2 D.R.rS)
    (ho' : Gom' f g2' = Gom' f g2) (ho : Gom f g2' = Gom f g2) : GFacts Λ f g1 g2 β := by
  have hmap : Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2' b.castSucc) ≤
      (Submodule.span D.host.E (Set.range fun a : Fin D.R.rS => g1 a.castSucc)).comap
        β.symm.toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    exact hG.xmap' b
  refine
    { iso := hG.iso
      lam := hG.lam
      lam' := hG.lam'
      xmap := fun a => hX ▸ hG.xmap a
      xmap' := fun a => ?_
      zmap := ?_
      fiso := hG.fiso
      g2iso := fun a b => ?_
      proj := hG.proj
      gram := hG.gram
      theta := fun x1 hx1 => ?_
      ratio := ?_
      omp := ?_
      om := ?_ }
  · have h : g2 a.castSucc ∈ Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2' b.castSucc) := by
      rw [hX]; exact Submodule.subset_span ⟨a, rfl⟩
    exact hmap h
  · have h1 := hG.zmap
    rw [hX] at h1
    have h3 := Submodule.add_mem _ h1 hz
    rwa [sub_add_sub_cancel] at h3
  · have hiso : ∀ x ∈ Set.range (fun b : Fin D.R.rS => g2' b.castSucc),
        ∀ y ∈ Set.range (fun b : Fin D.R.rS => g2' b.castSucc), (VS D).hT x y = 0 := by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      exact hG.g2iso i j
    have ha : g2 a.castSucc ∈ Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2' b.castSucc) := by
      rw [hX]; exact Submodule.subset_span ⟨a, rfl⟩
    have hb : g2 b.castSucc ∈ Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2' b.castSucc) := by
      rw [hX]; exact Submodule.subset_span ⟨b, rfl⟩
    exact LprExistA_iso_span hiso _ ha _ hb
  · obtain ⟨x2, h1, h2, h3⟩ := hG.theta x1 hx1
    refine ⟨x2, fun i => ?_, h2, hX ▸ h3⟩
    rcases i with a | b
    · exact h1 (Sum.inl a)
    · have horth : ∀ v ∈ Set.range g2', (VS D).hT v x2 = 0 := by
        rintro _ ⟨c, rfl⟩
        exact h1 (Sum.inr c)
      have hb : g2 b ∈ Submodule.span D.host.E (Set.range g2') := by
        rw [hsp]; exact Submodule.subset_span ⟨b, rfl⟩
      exact LprExistA_orth_span horth _ hb
  · rw [← ht, ← hr]; exact hG.ratio
  · rw [← ht, ← ho']; exact hG.omp
  · rw [← ht, ← ho, ← hX]; exact hG.om

theorem gfacts_frameAct {Λ : Submodule (𝓞 D.host.E) (VS D).V} {f g1 h : Fin (D.R.rS + 1) → (VS D).V}
    {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) (hG : GFacts Λ f g1 (frameAct h ξ⁻¹) β) :
    GFacts Λ f g1 h β := by
  have hη := inv_unitri ξ h1 h2
  refine gfacts_move hG (Xs_frameAct_inv h ξ h1 h2) (span_frameAct_inv h ξ h1 h2) ?_
    (GDl_frameAct_top f h ξ⁻¹ hη.1 hη.2) (GDl_frameAct_r f h ξ⁻¹ hη.1 hη.2)
    (Gom'_frameAct f h ξ⁻¹ hη.1 hη.2) (Gom_frameAct f h ξ⁻¹ hη.1 hη.2)
  exact frameAct_last_sub h ξ⁻¹ (hη.2 _)

end Glob

section LocIota

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)

theorem iotaG_congr {q : E} {abelian₂ : Submodule M.L.O V} {r : ℕ} {f₀ f₁ f₂ f₂' : Fin (r + 1) → V} {e : V ≃ₗ[E] V}
    (hX : H.X f₂ = H.X f₂') (h : IotaG H q abelian₂ f₀ f₁ f₂ e) : IotaG H q abelian₂ f₀ f₁ f₂' e := by
  unfold IotaG at h ⊢
  rw [← hX]
  exact h

end LocIota

section Loc

variable {D : D7} (Z : LocDat D) (p : PlF D)

theorem locX_eq {g2 g2' : Fin (D.R.rS + 1) → (VS D).V}
    (hX : Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2' b.castSucc) =
      Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2 b.castSucc)) :
    (locH Z p).X (fun b => sF' Z p b • baseChange₂ D p (g2' b)) = (locH Z p).X (fun b => sF' Z p b • baseChange₂ D p (g2 b)) := by
  apply le_antisymm
  · unfold Loc.HermSp.X
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have hm : g2' a.castSucc ∈ Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2 b.castSucc) := by
      rw [← hX]; exact Submodule.subset_span ⟨a, rfl⟩
    exact Submodule.smul_mem _ _ (bcP_mem_X Z p g2 (sF' Z p) (isUnit_sF' Z p) hm)
  · unfold Loc.HermSp.X
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have hm : g2 a.castSucc ∈ Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2' b.castSucc) := by
      rw [hX]; exact Submodule.subset_span ⟨a, rfl⟩
    exact Submodule.smul_mem _ _ (bcP_mem_X Z p g2' (sF' Z p) (isUnit_sF' Z p) hm)

theorem iotaEl_frameAct {Λ : Submodule (𝓞 D.host.E) (VS D).V} {f g1 h : Fin (D.R.rS + 1) → (VS D).V}
    {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) (hI : IotaEl Z p Λ f g1 (frameAct h ξ⁻¹) β) :
    IotaEl Z p Λ f g1 h β := by
  intro gg hgg
  exact iotaG_congr (locH Z p) (locX_eq Z p (Xs_frameAct_inv h ξ h1 h2)) (hI gg hgg)

end Loc

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.LprEx
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace LprEx

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem scal_rep (hrows : IsRowReps D F0 what₂) (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F'' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (hP : IsPartner γ Z F'')
    (hGr : Gval (lf D F0) (repF γ) ≠ 0) :
    ∃ β, IsPair γ.lam (lf D F0) (repF γ) F'' β (gS D) ∧ s0 γ.lam (lf D F0) (repF γ) F'' β D.R.k = 1 ∧
      IsScalar γ.lam (lf D F0) (repF γ) F'' β := by
  obtain ⟨hE, γ', ⟨pr, hp1, hp2, hps, hpsc⟩, h3, h3e⟩ := hP
  obtain ⟨h2, h2e⟩ := starRepF_rep γ
  have hGF : Gval (lf D F0) F'' ≠ 0 := hE.1.2.2
  obtain ⟨lam, mem, cls⟩ := γ
  obtain ⟨lam', mem', cls'⟩ := γ'
  obtain ⟨lp, mp, p1, p2, gp1, gp2, bp, ip⟩ := pr
  simp only [Formalism.L2.SG.Corank.Pair.pfst, Formalism.L2.SG.Corank.Pair.psnd] at hp1 hp2
  obtain ⟨rfl, hc1⟩ := hp1
  obtain ⟨rfl, hc2⟩ := hp2
  exact scal_move (hrows.1 _ mp) ⟨p1, gp1⟩ ⟨p2, gp2⟩ ⟨⟨repF _, h2⟩, hGr⟩ ⟨⟨F'', h3⟩, hGF⟩ h2e.symm h3e.symm
    ⟨bp, ip, hps, hpsc⟩

variable (Zd : LocDat D)


set_option maxHeartbeats 1000000 in
theorem lprExist_of (hI : Formalism.L2.SG.Pf.ScalarFramePf.IotaStep) : LprExist Zd u u' F0 what₂ := by
  intro hrows γ Z hC F'' hP p
  obtain ⟨w, hγ, -⟩ := hC
  have hR : IsRowLat D F0 γ.lam := hrows.1 γ.lam γ.mem
  have hF : FixedHyp D γ.lam (lf D F0) := hR.2.1
  obtain ⟨h2, h2e⟩ := starRepF_rep γ
  have hGr : Gval (lf D F0) (repF γ) ≠ 0 := gval_repF γ w hγ
  have hgenR : IsGeneric γ.lam (gS D) (lf D F0) (repF γ) := by
    obtain ⟨hgen, -⟩ := hγ.1
    obtain ⟨F', ⟨h1, h1e⟩, hF'⟩ := hgen
    have hrel := (Formalism.L2.SG.Pf.double_coset_equivalence γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') ⟨F', h1⟩ ⟨repF γ, h2⟩).1
      (h1e.trans h2e.symm)
    exact (PI.TermAttrConst.UnitaryGroupMassFormula.genericity_constant_double_cosets D u u' F0 γ.lam hR ⟨F', h1⟩ ⟨repF γ, h2⟩ hrel).1 hF'
  have hE := hP.1
  obtain ⟨β, hPair, hs, hsc⟩ := scal_rep hrows γ Z F'' hP hGr
  have hT : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Formalism.L2.SG.Corank.tu_ne_zero u
  have hT' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Formalism.L2.SG.Corank.tu_ne_zero u'
  have hG := Formalism.L2.SG.Pf.ScalarFramePf.gfacts_of γ.lam (lf D F0) (repF γ) F'' β hF h2.1 hE.1.1 h2.2.2.1
    hE.2.2.2.1.1 hPair hs hsc hGr hE.1.2.2 hT hT'
  have hIo := hI D Zd γ.lam (lf D F0) (repF γ) F'' β hF h2.1 hE.1.1 h2.2.2.1 hE.2.2.2.1.1 h2.2.1 hE.1.2.1 hPair
    hgenR hE.2.2.1 hs hsc hGr hE.1.2.2 hT hT' p
  have hξ := admissibility_witness_unitriangular γ.lam (lf D F0) F''
  have hG2 := gfacts_frameAct (admXi D γ.lam (lf D F0) F'') hξ.1 hξ.2 hG
  have hI2 := iotaEl_frameAct Zd p (admXi D γ.lam (lf D F0) F'') hξ.1 hξ.2 hIo
  obtain ⟨hId, hRe⟩ := Formalism.L2.SG.Pf.ScalarFramePf.identResp_lt Zd p γ.lam (frame (lf D F0)) _ (frame F'') β
    (Tu D u) (Tu D u') hG2 hI2
  exact ⟨Formalism.L2.SG.Pf.ScalarFramePf.phiP Zd p γ.lam (frame (lf D F0)) _ (frame F'') β hG2, hId, hRe.2.2.2.1,
    hRe.2.2.1, hRe.2.2.2.2⟩

theorem lprPart_of_iota (hI : Formalism.L2.SG.Pf.ScalarFramePf.IotaStep) : LprPart Zd u u' F0 what₂ :=
  lprPart_of' Zd (lprExist_of Zd hI)

end LprEx

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem lprPart_holds : LprPart Zd u u' F0 what₂ :=
  LprEx.lprPart_of_iota Zd Formalism.L2.SG.Pf.iotaStep_holds

theorem fStarC_of_beta (hC : CtxP u u' F0 what₂) (hRat : BetaRat Zd u u' F0 what₂) (hInt : BetaInt Zd u u' F0 what₂) :
    FStarC Zd u u' F0 what₂ :=
  fStarC_of_leaves' Zd hC (lprPart_holds Zd) hRat hInt

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem fStarC_of_int (hC : CtxP u u' F0 what₂) (hInt : BetaInt Zd u u' F0 what₂) : FStarC Zd u u' F0 what₂ :=
  fStarC_of_beta Zd hC (betaRat_holds Zd u u' F0 what₂) hInt

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
