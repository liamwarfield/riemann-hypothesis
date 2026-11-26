module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestSupportFamiliesStaircaseCosets
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplitting

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameLatticePointsEqIntegralMatricesLargeDepth
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameLatticePointsEqIntegralMatricesLargeDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.FlatPlace

variable {D : D7}

theorem isIdemSum_of_isPlc {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) : IsIdemSum p.e {w} :=
  ⟨⟨fun _ => p.e, fun PP h => by rw [Finset.mem_singleton] at h; subst h; exact hp.1, by simp⟩, p.split.2.1⟩


open Classical in
theorem cpt_up {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y]
    [Fintype Y'] [DecidableEq Y'] (FS : Frame (Kw w) S.rank Y') (FT : Frame (Kw w) T.rank Y) (x : Matrix Y Y' (Kw w))
    (Q : Pl D.host.E) :
    (((p.up FS FT x : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D)).map (cpt Q) =
      (FT.β * x * FS.γ).map (fun z => (Pi.single w z : ∀ Q, Kw Q) Q) := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply, Place.up]
  rw [hp.2.2]
  exact (atPl_spec w _).2 Q

theorem up_mem_latO_iff {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)} (fS : IsFrame βS ΛS) (fT : IsFrame βT ΛT)
    {w : Pl D.host.E} (hw : ((GlobalTheory.HalfCompare.badInt D : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) {p : Place D (Kw w)} (hp : IsPlc w p)
    {NS NT : ℕ} (hNS : NS = S.rank) (hNT : NT = T.rank) (x : Matrix (Fin NT) (Fin NS) (Kw w)) :
    p.up (frOf hNS βS w) (frOf hNT βT w) x ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) ↔
      ∀ a b, x a b ∈ Valuation.integer (ValuativeRel.valuation (Kw w)) := by
  classical
  subst hNS hNT
  rw [GlobalTheory.HalfOInt.mem_latO_iff_frMapO_int D S T ΛS ΛT βS βT hS hT fS fT {w} p.e (isIdemSum_of_isPlc hp)
    (by simpa using hw) _ (Witness.up_half p _ _ x)]
  set FS := frOf rfl βS w
  set FT := frOf rfl βT w
  have hmap : ∀ Q, (frMapO S T βS βT (p.up FS FT x)).map (cpt (D := D) Q) =
      (loc Q βT⁻¹).val * (FT.β * x * FS.γ).map (fun z => (Pi.single w z : ∀ Q, Kw Q) Q) * (loc Q βS).val := by
    intro Q
    rw [← cpt_up hp FS FT x Q]
    unfold frMapO
    rw [Matrix.map_mul, Matrix.map_mul]
    rfl
  have hw' : (loc w βT⁻¹).val * (FT.β * x * FS.γ) * (loc w βS).val = x := by
    have e1 : (loc w βT⁻¹).val = FT.γ := by
      rw [map_inv]; exact (Matrix.submatrix_id_id _).symm
    have e2 : (loc w βS).val = FS.β := (Matrix.submatrix_id_id _).symm
    rw [e1, e2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, FT.γβ, Matrix.one_mul, Matrix.mul_assoc, FS.γβ, Matrix.mul_one]
  have hval : ∀ Q i j, cpt (D := D) Q (frMapO S T βS βT (p.up FS FT x) i j) = if h : Q = w then h ▸ x i j else 0 := by
    intro Q i j
    have := congrFun (congrFun (hmap Q) i) j
    rw [Matrix.map_apply] at this
    rw [this]
    split_ifs with h
    · subst h
      simp only [Pi.single_eq_same, Matrix.map_id']
      rw [hw']
    · have h0 : (FT.β * x * FS.γ).map (fun z => (Pi.single w z : ∀ Q, Kw Q) Q) = 0 :=
        Matrix.ext fun _ _ => by simp [Pi.single_eq_of_ne h]
      rw [h0, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply]
  unfold IsIntM
  refine ⟨fun h a b => ?_, fun h a b => ?_⟩
  · have := (mem_OA_iff _).1 (h a b) w
    rw [hval, dite_eq_left rfl] at this
    rw [Valuation.mem_integer_iff, (Good.isEquiv_Kw w).le_one_iff_le_one]
    exact this
  · refine (mem_OA_iff _).2 fun Q => ?_
    rw [hval]
    split_ifs with hQ
    · subst hQ
      have := h a b
      rw [Valuation.mem_integer_iff, (Good.isEquiv_Kw Q).le_one_iff_le_one] at this
      exact this
    · exact zero_mem _

theorem big_latP : Big fun ch => LatP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hde := GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s
  intro t w hw p hp j hj
  have hc : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := hch.guard t
  have hb := Good.badInt_notMem hL hde hc hw
  have hm : D.R.m ≠ 0 := by have := D.R.two_le_m; omega
  refine ⟨fun x => up_mem_latO_iff ?_ ?_ (ch.S.B.isFrame_β hL le_rfl hj.le) (ch.S.B.isFrame_β hL le_rfl hj) hb hp _ _ x,
    fun x => up_mem_latO_iff ?_ ?_ (ch.S.βp_is j hj.le) (ch.S.βp_is (j + 1) hj) hb hp _ _ x⟩
  · exact (ch.G.isV (X := .grid D.R.m j) ⟨le_rfl, hj.le⟩ fun _ e => by injection e with h; exact hm h).sd
  · exact (ch.G.isV (X := .grid D.R.m (j + 1)) ⟨le_rfl, hj⟩ fun _ e => by injection e with h; exact hm h).sd
  · exact (ch.G.isV (X := .top j) hj.le fun _ e => by cases e).sd
  · exact (ch.G.isV (X := .top (j + 1)) hj fun _ e => by cases e).sd

end GlobalTheory.FlatPlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameLatticePointsEqIntegralMatricesLargeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameLattice_points_eq_integralMatrices_largeDepth : Big fun ch => LatP ch := by
  first | exact @GlobalTheory.FlatPlace.big_latP | exact GlobalTheory.FlatPlace.big_latP | (intros; apply GlobalTheory.FlatPlace.big_latP <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalCharacterComponentsLargeDepth
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalCharacterComponentsLargeDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

open scoped TensorProduct

namespace GlobalTheory.FlatPlace

theorem finComp_eq_toAd {D : D7} (z : AE D) :
    GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E z = GlobalTheory.StdFrames.toAd D (Formalism.IndefR.Datum.toEAf D z) := by
  have key : ∀ y : Af D.host.F ⊗[D.host.F] D.host.E,
      GlobalTheory.LFun.toFinAd D.host.F D.host.E y = GlobalTheory.StdFrames.toAd D (Formalism.IndefR.Lev.swapAE D y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x =>
      rw [GlobalTheory.LFun.toFinAd_tmul, mul_comm]
      exact (GlobalTheory.StdFrames.toAd_spec D x a).symm
    | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb]
  exact key _

theorem iota_add_eq_locIdele {D : D7} {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) (x : (Kw w)ˣ) :
    p.ι x + (1 - p.e) = (GlobalTheory.LFun.locIdele D.host.F w x : AE D) := by
  classical
  have e_ι : ∀ y, p.e * p.ι y = p.ι y := fun y => by rw [← p.ι_π, p.π_ι]
  have he1 : p.e = atPl w 1 := by
    rw [← hp.2.2 1]
    have := p.ι_π 1
    rw [map_one, mul_one] at this
    exact this.symm
  have hfc : ∀ z Q, GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E z Q = GlobalTheory.StdFrames.cpt Q (Formalism.IndefR.Datum.toEAf D z) :=
    fun z Q => by rw [finComp_eq_toAd]; rfl
  have hδ : GlobalTheory.CMPrimeIdele.IsDelta (GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E) w p.e := by
    refine ⟨by rw [he1]; exact (atPl_spec w 1).1, by rw [hfc, he1, (atPl_spec w 1).2, Pi.single_eq_same], fun Q hQ => ?_⟩
    rw [hfc, he1, (atPl_spec w 1).2, Pi.single_eq_of_ne hQ]
  have := GlobalTheory.LFun.EulerTie.glue_eq_locIdele hδ (a := p.ι x) (u := x)
    (by rw [hfc, hp.2.2, (atPl_spec w _).2, Pi.single_eq_same])
  rwa [e_ι] at this

theorem isComp_attChr {D : D7} {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) (c η : (AE D)ˣ →* Circle)
    (μ e : (Kw w)ˣ →* ℂˣ) (hc : ∀ y, ((c (GlobalTheory.LFun.locIdele D.host.F w y) : Circle) : ℂ) = ((μ y : ℂˣ) : ℂ))
    (he : ∀ y, ((η (GlobalTheory.LFun.locIdele D.host.F w y) : Circle) : ℂ) = ((e y : ℂˣ) : ℂ)) (n k : ℕ)
    (hk : (k + 1) % 2 = if Odd n then 1 else 0) :
    p.IsComp (Formalism.IndefR.Lift.attChr c η n) (μ / e ^ ((k + 1) % 2)) := by
  intro x a ha
  have ha' : a = GlobalTheory.LFun.locIdele D.host.F w x := Units.ext (ha.trans (iota_add_eq_locIdele hp x))
  subst ha'
  rw [hk]
  unfold Formalism.IndefR.Lift.attChr
  split_ifs with h
  · simp only [pow_one, MonoidHom.div_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_div_eq_div_val,
      Circle.coe_mul, Circle.coe_inv, hc, he, div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  · simp only [pow_zero, div_one, hc]

end GlobalTheory.FlatPlace

namespace GlobalTheory.FlatPlace

theorem chrP_big : Big fun ch => ChrP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t w hw p hp
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hde := GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s
  have hc : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := hch.guard t
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  refine ⟨fun x => ?_, (((Good.locGrid_isGood hL ch.G ch.W t hde hc).1 w hw).square 0 hm 0 hm).cond, fun j hj => ?_⟩
  · rw [hp.2.2 x] <;> rfl
  have hE : ChrEq (R.toLevCh.mu t (j + 1)) (muBase R.toLevCh (j + 1) * R.toLevCh.xiH t) := by
    have h1 : muBase R.toLevCh (j + 1) = R.toLevCh.C.mu0 ⟨j, hj⟩ := dif_pos hj
    rw [h1]
    exact GlobalTheory.TowerCharRead.chrEq_mul (hL.mu0 ⟨j, hj⟩) (hL.xi t)
  have hmu : ∀ y, ((R.toLevCh.mu t (j + 1) (GlobalTheory.LFun.locIdele D.host.F w y) : Circle) : ℂ) =
      (((locGrid ch.G t w).mu (j + 1) y : ℂˣ) : ℂ) :=
    fun y => congrArg (fun f => ((f y : ℂˣ) : ℂ)) (GlobalTheory.LFun.locChar_eq_of_chrEq hE w)
  have heta : ∀ y, ((R.toLevCh.eta (GlobalTheory.LFun.locIdele D.host.F w y) : Circle) : ℂ) =
      (((locGrid ch.G t w).eta y : ℂˣ) : ℂ) :=
    fun y => congrArg (fun f => ((f y : ℂˣ) : ℂ)) (GlobalTheory.LFun.locChar_eq_of_chrEq hL.eta w)
  have r0 := (rank_vertex ch.G t w (X := (D.R.m, j)) ⟨le_rfl, hj.le⟩).symm
  have r1 := (rank_vertex ch.G t w (X := (D.R.m, j + 1)) ⟨le_rfl, hj⟩).symm
  have hstep : (locGrid ch.G t w).rank (D.R.m, j + 1) = (locGrid ch.G t w).rank (D.R.m, j) + D.R.t := by
    show D.R.r + (j + 1) * D.R.t + D.R.m * sLen D = D.R.r + j * D.R.t + D.R.m * sLen D + D.R.t
    ring
  obtain ⟨c, hc'⟩ := D.R.t_odd
  refine ⟨?_, ?_⟩
  · refine isComp_attChr hp _ _ _ _ hmu heta _ _ ?_
    rw [r0, hstep, hc']
    split_ifs with h
    · obtain ⟨d, hd⟩ := h; omega
    · rw [Nat.not_odd_iff_even] at h; obtain ⟨d, hd⟩ := h; omega
  · refine isComp_attChr hp _ _ _ _ hmu heta _ _ ?_
    rw [r1, hstep, hc']
    split_ifs with h
    · obtain ⟨d, hd⟩ := h; omega
    · rw [Nat.not_odd_iff_even] at h; obtain ⟨d, hd⟩ := h; omega

end GlobalTheory.FlatPlace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalCharacterComponentsLargeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localCharacterComponents_largeDepth : Big fun ch => ChrP ch := by
  first | exact @GlobalTheory.FlatPlace.chrP_big | exact GlobalTheory.FlatPlace.chrP_big | (intros; apply GlobalTheory.FlatPlace.chrP_big <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselDepthLatticeCoreSplitsAlongTargetWitt
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselDepthLatticeCoreSplitsAlongTargetWitt
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TgtCoreSplit

variable {D : D7}

theorem one_mem_intAf : (1 : Af D.host.F) ∈ intAf D.host.F := fun v => by
  rw [map_one]; exact one_mem _

theorem finPart_pure (α : Af D.host.F) (e : D.host.E) :
    finPart D ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] e) = α ⊗ₜ[D.host.F] e := by
  unfold finPart
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
  rfl

theorem toEAf_pure (e : D.host.E) :
    toEAf D ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] e) =
      Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) e := by
  unfold toEAf
  rw [RingHom.comp_apply, finPart_pure]
  rfl

theorem rat_mulVec_pure {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (α : Af D.host.F) (t : Fin n → D.host.E) :
    rat M *ᵥ (fun i => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] t i) =
      fun i => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (M *ᵥ t) i := by
  funext i
  simp only [Matrix.mulVec, dotProduct, rat, Matrix.map_apply, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show ((1 : AF D.host.F) ⊗ₜ[D.host.F] M i k) * _ = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem proj_mem {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀}
    (hL : Submodule.IsLattice D.host.E L) (hL₀ : Submodule.IsLattice D.host.E L₀) (hm : ∀ v, MonoAt d L L₀ v)
    {t : Fin S.rank → D.host.E} (ht : t ∈ L) : (d.i₀ * d.q0) *ᵥ t ∈ L := by
  have hy : (fun i => (pairA D.host.F 0 1) ⊗ₜ[D.host.F] t i) ∈ latV S L (fun _ => True) :=
    AddSubgroup.subset_closure ⟨1, one_mem_intAf, fun v hv => (hv trivial).elim, 1, rfl, t, ht, by
      funext i; rw [one_mul]⟩
  have h2 := GlobalTheory.FinPl.ExtZeroAt.wittCoreInclusion_mem_latticeCompletionAtPlace d hL (fun v _ => hm v)
    (GlobalTheory.FinPl.ExtZeroAt.wittProjectionZero_mem_latticeCompletion_of_splits d hL₀ (fun v _ => hm v) hy)
  have e : d.j0 *ᵥ (d.p0 *ᵥ (fun i => (pairA D.host.F 0 1) ⊗ₜ[D.host.F] t i)) =
      fun i => (pairA D.host.F 0 1) ⊗ₜ[D.host.F] ((d.i₀ * d.q0) *ᵥ t) i := by
    rw [Matrix.mulVec_mulVec, show d.j0 * d.p0 = rat (d.i₀ * d.q0) by rw [rat_mul]; rfl]
    exact rat_mulVec_pure _ _ _
  rw [e] at h2
  have h3 := (GlobalTheory.Core.Mi.LatMatch.TraceX.latV_iff_hatL S L _ _ (GlobalTheory.FinPlLoc.latV_idAt h2)).1 h2
  simp only [toEAf_pure] at h3
  exact (GlobalTheory.Mem.Col2.PtUniq.mem_iff_hatL (F := D.host.F) hL _).2 h3

theorem mul_mem_latO {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Lat T} {P : GlobalTheory.FinPl.Pl D → Prop}
    (M : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (hM : ∀ t ∈ LT, M *ᵥ t ∈ LT) {u : WO S T}
    (hu : u ∈ latO S T LS (LT : Set _) P) : rat M * u ∈ latO S T LS (LT : Set _) P := by
  induction hu using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, hαP, a, ha, s, hs, t, ht, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨α, hα, hαP, a, ha, s, hs, M *ᵥ t, hM t ht, ?_⟩
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply]
    generalize (∑ k, star (s k) * S.gram k j) = c
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show ((1 : AF D.host.F) ⊗ₜ[D.host.F] M i k) * _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    ring
  | zero => rw [Matrix.mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg]; exact neg_mem hx

theorem mul_mem_smul_homLat {m n : ℕ} (I : Ideal (𝓞 D.host.E)) {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (M : Matrix (Fin m) (Fin m) D.host.E)
    (hM : ∀ t ∈ Λ', M *ᵥ t ∈ Λ') {x : Matrix (Fin m) (Fin n) D.host.E} (hx : x ∈ I • homLat Λ Λ') :
    M * x ∈ I • homLat Λ Λ' := by
  refine Submodule.smul_induction_on hx (fun r hr y hy => ?_) (fun a b ha hb => ?_)
  · rw [Matrix.mul_smul]
    refine Submodule.smul_mem_smul hr fun z hz => ?_
    rw [← Matrix.mulVec_mulVec]
    exact hM _ (hy z hz)
  · rw [Matrix.mul_add]; exact add_mem ha hb

theorem mul_mem_hatMx {m n : ℕ} (N : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E))
    (M : Matrix (Fin m) (Fin m) D.host.E) (hM : ∀ x ∈ N, M * x ∈ N) {u : Mx D m n} (hu : u ∈ hatMx N) :
    rat M * u ∈ hatMx N := by
  induction hu using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨α, hα, M * x, hM x hx, ?_⟩
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show ((1 : AF D.host.F) ⊗ₜ[D.host.F] M i k) * _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [Matrix.mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg]; exact neg_mem hx

end GlobalTheory.TgtCoreSplit


open GlobalTheory.TgtCoreSplit in
theorem GlobalTheory.AscFin.latRow_bessel_core_split : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ w : WO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)), (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w ∈ latRow G (2 * ρ + 1) → (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).inc0 (F.V₀ ρ) ((F.dJ ρ h).p0 ⬝ w)) ∈ latRow G (2 * ρ + 1) := by
  intro D hD T L μ0 hL sc G W M hM F hF ρ h w hw
  have hI := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hD T L μ0 hL sc G W M hM F hF
  have hm : ∀ v, MonoAt (F.dJ ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) (G.Λ (.core (2 * ρ + 1))) v :=
    fun v => ((hI.2.1 ρ h).2.1 v).2
  have hL1 : Submodule.IsLattice D.host.E (G.Λ (.grid (2 * ρ + 1) 0)) :=
    (node_isV G hL (X := .grid (2 * ρ + 1) 0) ⟨by omega, Nat.zero_le _⟩).sd.1
  have hL0 : Submodule.IsLattice D.host.E (G.Λ (.core (2 * ρ + 1))) :=
    (node_isV G hL (X := .core (2 * ρ + 1)) (show 2 * ρ + 1 ≤ D.R.m by omega)).sd.1
  have hP : ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0), ((F.dJ ρ h).i₀ * (F.dJ ρ h).q0) *ᵥ t ∈ G.Λ (.grid (2 * ρ + 1) 0) :=
    fun t ht => proj_mem _ hL1 hL0 hm ht
  have e : (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).inc0 (F.V₀ ρ) ((F.dJ ρ h).p0 * w)) =
      rat ((F.dJ ρ h).i₀ * (F.dJ ρ h).q0) * (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, rat_mul]
    show (F.dJ ρ h).j0 * ((F.dJ ρ h).p0 * w) * (F.dB ρ h).p0 = (F.dJ ρ h).j0 * (F.dJ ρ h).p0 * (w * (F.dB ρ h).p0)
    simp only [Matrix.mul_assoc]
  have hw' : (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w ∈ latO (G.pS (.chi (2 * ρ + 1) 0 : Pair T)) (G.pT (.chi (2 * ρ + 1) 0 : Pair T)) (G.latS (.chi (2 * ρ + 1) 0 : Pair T) : Set _) (G.latT (.chi (2 * ρ + 1) 0 : Pair T) : Set _) (fun _ => True) ∧
      ∀ a : AE D, IsIdemSum a G.pl.W0 → a • (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w ∈ hatMx (G.modul • homLat (G.latS (.chi (2 * ρ + 1) 0 : Pair T)) (G.latT (.chi (2 * ρ + 1) 0 : Pair T))) := hw
  rw [e]
  show (rat ((F.dJ ρ h).i₀ * (F.dJ ρ h).q0) * (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w) ∈ latO (G.pS (.chi (2 * ρ + 1) 0 : Pair T)) (G.pT (.chi (2 * ρ + 1) 0 : Pair T)) (G.latS (.chi (2 * ρ + 1) 0 : Pair T) : Set _) (G.latT (.chi (2 * ρ + 1) 0 : Pair T) : Set _) (fun _ => True) ∧
      ∀ a : AE D, IsIdemSum a G.pl.W0 → a • (rat ((F.dJ ρ h).i₀ * (F.dJ ρ h).q0) * (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w) ∈ hatMx (G.modul • homLat (G.latS (.chi (2 * ρ + 1) 0 : Pair T)) (G.latT (.chi (2 * ρ + 1) 0 : Pair T)))
  refine ⟨mul_mem_latO _ hP hw'.1, fun a ha => ?_⟩
  rw [← Matrix.mul_smul]
  exact mul_mem_hatMx _ _ (fun x hx => mul_mem_smul_homLat _ _ hP hx) (hw'.2 a ha)

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselDepthLatticeCoreSplitsAlongTargetWittStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_depth_lattice_core_splits_along_target_witt : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ w : WO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)), (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w ∈ latRow G (2 * ρ + 1) → (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).inc0 (F.V₀ ρ) ((F.dJ ρ h).p0 ⬝ w)) ∈ latRow G (2 * ρ + 1) := by
  first | exact @GlobalTheory.AscFin.latRow_bessel_core_split | exact GlobalTheory.AscFin.latRow_bessel_core_split | (intros; apply GlobalTheory.AscFin.latRow_bessel_core_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselDepthLatticeSplitsAlongSourceWitt
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselDepthLatticeSplitsAlongSourceWitt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.SrcSplit

open GlobalTheory.FinPl.LatMem

variable {D : D7}

theorem tmul_mul_rat {m n k : ℕ} (c : AF D.host.F) (x : Matrix (Fin m) (Fin n) D.host.E) (π : Matrix (Fin n) (Fin k) D.host.E) :
    (Matrix.of fun i j => c ⊗ₜ[D.host.F] x i j : Mx D m n) * rat π = Matrix.of fun i j => c ⊗ₜ[D.host.F] (x * π) i j := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  show (c ⊗ₜ[D.host.F] x i l) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] π l j) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem rat_mulVec_tmul {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (c : AF D.host.F) (z : Fin n → D.host.E) :
    rat M *ᵥ (fun i => c ⊗ₜ[D.host.F] z i) = fun k => c ⊗ₜ[D.host.F] (M *ᵥ z) k := by
  funext k
  simp only [Matrix.mulVec, dotProduct, rat, Matrix.map_apply, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show ((1 : AF D.host.F) ⊗ₜ[D.host.F] M k j) * (c ⊗ₜ[D.host.F] z j) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem mul_rat_mem_hatMx {m n : ℕ} (M : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E))
    (π : Matrix (Fin n) (Fin n) D.host.E) (hM : ∀ x ∈ M, x * π ∈ M) {w : Mx D m n} (hw : w ∈ hatMx M) :
    w ⬝ rat π ∈ hatMx M := by
  let g : Mx D m n →+ Mx D m n :=
    { toFun := fun w => w ⬝ rat π, map_zero' := Matrix.zero_mul _, map_add' := fun a b => Matrix.add_mul a b _ }
  have hle : hatMx M ≤ (hatMx M).comap g := by
    refine (AddSubgroup.closure_le _).2 fun w hw => ?_
    obtain ⟨α, hα, x, hx, rfl⟩ := hw
    show (_ : Mx D m n) ⬝ rat π ∈ hatMx M
    rw [tmul_mul_rat]
    exact AddSubgroup.subset_closure ⟨α, hα, x * π, hM x hx, rfl⟩
  exact hle hw

theorem mul_mem_smul_homLat {m n : ℕ} (I : Ideal (𝓞 D.host.E)) (LS : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (LT : Submodule (𝓞 D.host.E) (Fin m → D.host.E)) (π : Matrix (Fin n) (Fin n) D.host.E)
    (hπ : ∀ y ∈ LS, π *ᵥ y ∈ LS) : ∀ x ∈ I • homLat LS LT, x * π ∈ I • homLat LS LT := by
  let f : Matrix (Fin m) (Fin n) D.host.E →ₗ[𝓞 D.host.E] Matrix (Fin m) (Fin n) D.host.E :=
    { toFun := (· * π), map_add' := fun a b => Matrix.add_mul a b π, map_smul' := fun r a => Matrix.smul_mul r a π }
  have hH : (homLat LS LT).map f ≤ homLat LS LT := by
    rintro _ ⟨x, hx, rfl⟩ y hy
    show (x * π) *ᵥ y ∈ LT
    rw [← Matrix.mulVec_mulVec]
    exact hx _ (hπ y hy)
  intro x hx
  have h1 : f x ∈ (I • homLat LS LT).map f := ⟨x, hx, rfl⟩
  rw [Submodule.map_smul''] at h1
  exact Submodule.smul_mono le_rfl hH h1

theorem mul_rat_mem_latO (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : GlobalTheory.FinPl.Pl D → Prop) (π π' : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (hadj : S.gram * π = π'ᴴ * S.gram)
    (hπ' : ∀ s ∈ LS, π' *ᵥ s ∈ LS) {u : Mx D T.rank S.rank} (hu : u ∈ latO S T LS LT P) :
    u ⬝ rat π ∈ latO S T LS LT P := by
  let g : Mx D T.rank S.rank →+ Mx D T.rank S.rank :=
    { toFun := fun w => w ⬝ rat π, map_zero' := Matrix.zero_mul _, map_add' := fun a b => Matrix.add_mul a b _ }
  have hle : latO S T LS LT P ≤ (latO S T LS LT P).comap g := by
    refine (AddSubgroup.closure_le _).2 fun w hw => ?_
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    show (_ : Mx D T.rank S.rank) ⬝ rat π ∈ latO S T LS LT P
    refine AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, π' *ᵥ s, hπ' s hs, t, ht, ?_⟩
    have e := tmul_mul_rat (pairA D.host.F 0 α) (Matrix.of fun i j => a * t i * ∑ k, star (s k) * S.gram k j) π
    simp only [Matrix.of_apply] at e
    rw [e]
    ext i j
    simp only [Matrix.of_apply]
    congr 1
    have e1 : ∀ v : Fin S.rank → D.host.E, ∀ l, ∑ k, star (v k) * S.gram k l = (star v ᵥ* S.gram) l := fun v l => rfl
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, e1]
    rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, ← hadj, ← Matrix.vecMul_vecMul]
    simp only [Matrix.vecMul, dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact hle hu

end GlobalTheory.AscFin.SrcSplit

namespace GlobalTheory.AscFin.SrcSplit

open GlobalTheory.FinPl.LatMem

variable {D : D7}

theorem proj_mem {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀}
    (hL : ∀ z : Fin S.rank → D.host.E, (∀ v : GlobalTheory.FinPl.Pl D,
      (fun i => pairA D.host.F 0 (indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈ latV S L (· = v)) → z ∈ L)
    (hmono : ∀ v, MonoAt d L L₀ v) (s : Fin S.rank → D.host.E) (hs : s ∈ L) :
    (d.e * d.qX) *ᵥ s ∈ L ∧ (d.e' * d.qY) *ᵥ s ∈ L := by
  have key : ∀ v, (fun i => pairA D.host.F 0 (indP D.host.F (· = v)) ⊗ₜ[D.host.F] s i) ∈ latV S L (· = v) := fun v =>
    AddSubgroup.subset_closure ⟨indP D.host.F (· = v), indicatorAdele_mem_integralAdeles' _ _, indicatorAdele_supported _ _, 1, rfl, s, hs,
      by funext k; rw [one_mul]⟩
  have split : ∀ (c : AF D.host.F) {k : ℕ} (e : Matrix (Fin S.rank) (Fin k) D.host.E)
      (q : Matrix (Fin k) (Fin S.rank) D.host.E),
      (fun i => c ⊗ₜ[D.host.F] ((e * q) *ᵥ s) i) =
        ∑ i, GlobalTheory.FinPl.colMul (rat e) i ((rat q *ᵥ (fun i => c ⊗ₜ[D.host.F] s i)) i) := by
    intro c k e q
    rw [← rat_mulVec_tmul, rat_mul, ← Matrix.mulVec_mulVec]
    generalize rat q *ᵥ (fun i => c ⊗ₜ[D.host.F] s i) = w
    funext l
    rw [Finset.sum_apply]
    simp only [Matrix.mulVec, dotProduct, GlobalTheory.FinPl.colMul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  constructor
  · refine hL _ fun v => ?_
    rw [split]
    exact sum_mem fun i _ => ((hmono v _).1 (key v)).1 i
  · refine hL _ fun v => ?_
    rw [split]
    exact sum_mem fun i _ => ((hmono v _).1 (key v)).2.1 i

theorem mem_of_proj {m : ℕ} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (A : AddSubgroup (Mx D m S.rank))
    (hA : ∀ w ∈ A, w ⬝ rat (d.e * d.qX) ∈ A ∧ w ⬝ rat (d.e' * d.qY) ∈ A) (u : Mx D m S.rank) (hu : u ∈ A) :
    u ⬝ d.jX ⬝ d.pX ∈ A ∧ u ⬝ d.jY ⬝ d.pY ∈ A ∧ u ⬝ d.j0 ⬝ d.p0 ∈ A := by
  have eX : d.jX ⬝ d.pX = rat (d.e * d.qX) := by rw [rat_mul]; rfl
  have eY : d.jY ⬝ d.pY = rat (d.e' * d.qY) := by rw [rat_mul]; rfl
  have e0 : d.j0 ⬝ d.p0 = 1 - d.jX ⬝ d.pX - d.jY ⬝ d.pY := by
    rw [← d.sum_eq_one]; abel
  obtain ⟨hX, hY⟩ := hA u hu
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, eX]; exact hX
  · rw [Matrix.mul_assoc, eY]; exact hY
  · rw [Matrix.mul_assoc, e0, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, eX, eY]
    exact sub_mem (sub_mem hu hX) hY

theorem adj_X {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) :
    (negSp S).gram * (d.e * d.qX) = (d.e' * d.qY)ᴴ * (negSp S).gram := by
  have hG : S.gramᴴ = S.gram := Matrix.ext fun i j => S.herm.eq _ _
  show -S.gram * (d.e * (d.e'ᴴ * S.gram)) = (d.e' * (d.eᴴ * S.gram))ᴴ * -S.gram
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]

theorem adj_Y {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) :
    (negSp S).gram * (d.e' * d.qY) = (d.e * d.qX)ᴴ * (negSp S).gram := by
  have hG : S.gramᴴ = S.gram := Matrix.ext fun i j => S.herm.eq _ _
  show -S.gram * (d.e' * (d.eᴴ * S.gram)) = (d.e * (d.e'ᴴ * S.gram))ᴴ * -S.gram
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]

end GlobalTheory.AscFin.SrcSplit


open GlobalTheory.AscFin.SrcSplit in
theorem GlobalTheory.AscFin.srcSplit_pcBF : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * ρ + 1), (F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jX) ∈ latRow G (2 * ρ + 1) ∧ (F.dB ρ h).extY (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jY) ∈ latRow G (2 * ρ + 1) ∧ (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).j0) ∈ latRow G (2 * ρ + 1) := by
  intro D hD T L μ0 hLμ sc G W M hM F hF ρ h u hu
  obtain ⟨-, H2, -⟩ := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hD T L μ0 hLμ sc G W M hM F hF
  have hmono : ∀ v, MonoAt (F.dB ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (lat0 F ρ h) v := fun v => ((H2 ρ h).2.1 v).1
  have hin : Node.InRange D.R.m (.grid (2 * ρ + 2) 0) := ⟨h, Nat.zero_le _⟩
  have hsd : IsSelfDualC (G.V (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 2) 0)) :=
    (G.isV hin (fun j hj => by injection hj with h1; omega)).sd
  have hP := proj_mem (F.dB ρ h) (GlobalTheory.T.mem_selfDualLattice_of_mem_all_latticeCompletions hsd) hmono
  have memR : ∀ w : Mx D (G.V (.grid (2 * ρ + 1) 0)).rank (G.V (.grid (2 * ρ + 2) 0)).rank, w ∈ latRow G (2 * ρ + 1) → ∀ π π' : Matrix (Fin (G.V (.grid (2 * ρ + 2) 0)).rank) (Fin (G.V (.grid (2 * ρ + 2) 0)).rank) D.host.E,
      (negSp (G.V (.grid (2 * ρ + 2) 0))).gram * π = π'ᴴ * (negSp (G.V (.grid (2 * ρ + 2) 0))).gram →
      (∀ s ∈ G.Λ (.grid (2 * ρ + 2) 0), π' *ᵥ s ∈ G.Λ (.grid (2 * ρ + 2) 0)) →
      (∀ s ∈ G.Λ (.grid (2 * ρ + 2) 0), π *ᵥ s ∈ G.Λ (.grid (2 * ρ + 2) 0)) →
      w ⬝ rat π ∈ latRow G (2 * ρ + 1) := by
    intro w hw π π' hadj hπ' hπ
    obtain ⟨hw1, hw2⟩ := hw
    refine ⟨mul_rat_mem_latO (negSp (G.V (.grid (2 * ρ + 2) 0))) _ _ _ _ π π' hadj hπ' hw1, fun e he => ?_⟩
    rw [← Matrix.smul_mul]
    exact mul_rat_mem_hatMx _ π (mul_mem_smul_homLat _ _ _ π hπ) (hw2 e he)
  exact mem_of_proj (F.dB ρ h) (latRow G (2 * ρ + 1))
    (fun w hw => ⟨memR w hw _ _ (adj_X (F.dB ρ h)) (fun s hs => (hP s hs).2) (fun s hs => (hP s hs).1),
      memR w hw _ _ (adj_Y (F.dB ρ h)) (fun s hs => (hP s hs).1) (fun s hs => (hP s hs).2)⟩) u hu
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselDepthLatticeSplitsAlongSourceWittStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_depth_lattice_splits_along_source_witt : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * ρ + 1), (F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jX) ∈ latRow G (2 * ρ + 1) ∧ (F.dB ρ h).extY (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jY) ∈ latRow G (2 * ρ + 1) ∧ (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).j0) ∈ latRow G (2 * ρ + 1) := by
  first | exact @GlobalTheory.AscFin.srcSplit_pcBF | exact GlobalTheory.AscFin.srcSplit_pcBF | (intros; apply GlobalTheory.AscFin.srcSplit_pcBF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeCorePartsMemSelfDualLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeCorePartsMemSelfDualLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.BigProj

variable {D : D7}

theorem idLat_one {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : idLat 1 Λ = Λ := by
  apply le_antisymm
  · rw [idLat, Submodule.span_le]
    rintro z ⟨s, hs, y, hy, rfl⟩
    obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hs
    rw [algebraMap_smul]
    exact Λ.smul_mem r hy
  · intro y hy
    exact Submodule.subset_span ⟨1, FractionalIdeal.one_mem_one _, y, hy, (one_smul _ _).symm⟩

theorem idLat_mulVec {n : ℕ} (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (M : Matrix (Fin n) (Fin n) D.host.E) (hM : ∀ x ∈ Λ, M *ᵥ x ∈ Λ) : ∀ x ∈ idLat I Λ, M *ᵥ x ∈ idLat I Λ := by
  intro x hx
  have hle : idLat I Λ ≤ (idLat I Λ).comap ((Matrix.mulVecLin M).restrictScalars (𝓞 D.host.E)) := by
    rw [idLat, Submodule.span_le]
    rintro z ⟨s, hs, y, hy, rfl⟩
    change M *ᵥ (s • y) ∈ Submodule.span (𝓞 D.host.E) {z | ∃ s ∈ I, ∃ y ∈ Λ, z = s • y}
    rw [Matrix.mulVec_smul]
    exact Submodule.subset_span ⟨s, hs, M *ᵥ y, hM y hy, rfl⟩
  exact hle hx

theorem latO_negSp_le (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO (negSp S) T LS LT P ≤ latO S T LS LT P := by
  unfold latO
  rw [AddSubgroup.closure_le]
  rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  rw [← neg_neg (Matrix.of _)]
  refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
  funext i j
  simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

section Witt

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem qX_e : d.qX * d.e = 1 := rat_injective (by rw [rat_mul, rat_one]; exact d.pX_jX)
theorem qX_e' : d.qX * d.e' = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.pX_jY)
theorem qX_i₀ : d.qX * d.i₀ = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.pX_j0)
theorem qY_e : d.qY * d.e = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.pY_jX)
theorem qY_e' : d.qY * d.e' = 1 := rat_injective (by rw [rat_mul, rat_one]; exact d.pY_jY)
theorem qY_i₀ : d.qY * d.i₀ = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.pY_j0)

end Witt

end GlobalTheory.AscFin.BigProj

namespace GlobalTheory.AscFin.BigProj

variable {D : D7}

theorem mul_col {m n r c : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (a : Matrix (Fin n) (Fin c) D.host.E)
    (Bm : Matrix (Fin n) (Fin r) D.host.E) (q : Fin c) (p : Fin r) (κ : D.host.E) (h : ∀ l, a l q = κ * Bm l p)
    (k : Fin m) : (M * a) k q = κ * (M * Bm) k p := by
  simp only [Matrix.mul_apply, h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

section SlopeTestRemainingChoices

variable {A B : HSp D} {c ρ : ℕ} (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B A ρ)

theorem auxiliary_vector_multiple_of_witt_basis_vector (hd : IsAuxiliaryVectorWittDec a d) (hc : c = 2 * ρ) (q : Fin c) :
    (q.1 < ρ → ∃ p : Fin ρ, ∃ κ : D.host.E, ∀ l, a.a l q = κ * d.e l p) ∧
    (¬ q.1 < ρ → ∃ p : Fin ρ, ∃ κ : D.host.E, ∀ l, a.a l q = κ * d.e' l p) := by
  obtain ⟨h2, he, s, he'⟩ := hd
  have hq2 := q.2
  refine ⟨fun hq => ⟨⟨q.1, hq⟩, ((-D.host.xi0) ^ (q.1 + 1))⁻¹, fun l => ?_⟩, fun hq => ?_⟩
  · rw [he]
    simp only [colsOf]
    rw [inv_mul_cancel_left₀ (pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero))]
    rfl
  · have hp : c - 1 - q.1 < ρ := by omega
    have hs : s ⟨c - 1 - q.1, hp⟩ ≠ 0 := by
      intro h0
      have := congrFun (congrFun (qY_e' d) ⟨c - 1 - q.1, hp⟩) ⟨c - 1 - q.1, hp⟩
      rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
      simp [he', colsOf, h0] at this
    refine ⟨⟨c - 1 - q.1, hp⟩, (s ⟨c - 1 - q.1, hp⟩)⁻¹, fun l => ?_⟩
    rw [he']
    simp only [colsOf]
    rw [inv_mul_cancel_left₀ hs]
    congr 1
    ext
    simp only [Fin.val_rev, Fin.val_castLE]
    omega

theorem wittHyperbolic_projX_auxiliary_vectors (hd : IsAuxiliaryVectorWittDec a d) (hc : c = 2 * ρ) :
    d.e * d.qX * a.a = a.a * Matrix.diagonal (fun q : Fin c => if q.1 < ρ then (1 : D.host.E) else 0) := by
  ext k q
  rw [Matrix.mul_diagonal]
  by_cases hq : q.1 < ρ
  · obtain ⟨p, κ, h⟩ := (auxiliary_vector_multiple_of_witt_basis_vector a d hd hc q).1 hq
    rw [mul_col _ _ _ q p κ h, Matrix.mul_assoc, qX_e, Matrix.mul_one, if_pos hq, mul_one, h]
  · obtain ⟨p, κ, h⟩ := (auxiliary_vector_multiple_of_witt_basis_vector a d hd hc q).2 hq
    rw [mul_col _ _ _ q p κ h]
    simp [Matrix.mul_assoc, qX_e', hq]

theorem wittHyperbolic_projY_auxiliary_vectors (hd : IsAuxiliaryVectorWittDec a d) (hc : c = 2 * ρ) :
    d.e' * d.qY * a.a = a.a * Matrix.diagonal (fun q : Fin c => if q.1 < ρ then (0 : D.host.E) else 1) := by
  ext k q
  rw [Matrix.mul_diagonal]
  by_cases hq : q.1 < ρ
  · obtain ⟨p, κ, h⟩ := (auxiliary_vector_multiple_of_witt_basis_vector a d hd hc q).1 hq
    rw [mul_col _ _ _ q p κ h]
    simp [Matrix.mul_assoc, qY_e, hq]
  · obtain ⟨p, κ, h⟩ := (auxiliary_vector_multiple_of_witt_basis_vector a d hd hc q).2 hq
    rw [mul_col _ _ _ q p κ h, Matrix.mul_assoc, qY_e', Matrix.mul_one, if_neg hq, mul_one, h]

theorem proj_lat (hd : IsAuxiliaryVectorWittDec a d) (hc : c = 2 * ρ) (hi : d.i₀ = frameMat B A a.ι)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
    ∀ x ∈ a.lat Λ 𝔟, (d.e * d.qX) *ᵥ x ∈ a.lat Λ 𝔟 ∧ (d.e' * d.qY) *ᵥ x ∈ a.lat Λ 𝔟 := by
  rintro x ⟨y, hy, u, hu, rfl⟩
  have k1 : d.e * d.qX * frameMat B A a.ι = 0 := by rw [← hi, Matrix.mul_assoc, qX_i₀, Matrix.mul_zero]
  have k2 : d.e' * d.qY * frameMat B A a.ι = 0 := by rw [← hi, Matrix.mul_assoc, qY_i₀, Matrix.mul_zero]
  refine ⟨⟨0, Λ.zero_mem, Matrix.diagonal (fun q : Fin c => if q.1 < ρ then (1 : D.host.E) else 0) *ᵥ u, fun p => ?_, ?_⟩,
    ⟨0, Λ.zero_mem, Matrix.diagonal (fun q : Fin c => if q.1 < ρ then (0 : D.host.E) else 1) *ᵥ u, fun p => ?_, ?_⟩⟩
  · rw [Matrix.mulVec_diagonal]
    split_ifs
    · rw [one_mul]; exact hu p
    · rw [zero_mul]; exact (𝔟 p).zero_mem
  · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, k1, wittHyperbolic_projX_auxiliary_vectors a d hd hc, ← Matrix.mulVec_mulVec,
      Matrix.zero_mulVec, Matrix.mulVec_zero, zero_add]
  · rw [Matrix.mulVec_diagonal]
    split_ifs
    · rw [zero_mul]; exact (𝔟 p).zero_mem
    · rw [one_mul]; exact hu p
  · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, k2, wittHyperbolic_projY_auxiliary_vectors a d hd hc, ← Matrix.mulVec_mulVec,
      Matrix.zero_mulVec, Matrix.mulVec_zero, zero_add]

end SlopeTestRemainingChoices

end GlobalTheory.AscFin.BigProj

namespace GlobalTheory.AscFin


open GlobalTheory.AscFin.BigProj in
theorem pcBF_big_core : OnStd fun {D} _ _ {sc} {G} W F =>
    ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ w : WO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)),
      (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w ∈ latRow G (2 * ρ + 1) →
      (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).incX (F.V₀ ρ) ((F.dJ ρ h).pX ⬝ w)) ∈ latBig G (2 * ρ + 1) ∧
      (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).incY (F.V₀ ρ) ((F.dJ ρ h).pY ⬝ w)) ∈ latBig G (2 * ρ + 1) := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h w hw
  have sdS : IsSelfDualC (G.V (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 2) 0)) :=
    (G.isV (X := .grid (2 * ρ + 2) 0) (by simp [Node.InRange]; omega) (fun j e => by simp at e)).sd
  have sdT : IsSelfDualC (G.V (.grid (2 * ρ + 1) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) :=
    (G.isV (X := .grid (2 * ρ + 1) 0) (by simp [Node.InRange]; omega) (fun j e => by simp at e)).sd
  have sdB := ((GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hq T L μ0 hL sc G W M hM F hF).1 (2 * ρ + 1) (by omega)).2.2.2
  obtain ⟨e, he, -⟩ := W.cosVec_is
  have big : (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w ∈ latO (G.V (.grid (2 * ρ + 1 + 1) 0)) (G.V (.grid (2 * ρ + 1) 0))
      (G.Λ (.grid (2 * ρ + 1 + 1) 0) : Set _) (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0)) : Set _) (fun _ => True) := by
    have key := GlobalTheory.T.completedHomLattice_modulus_depth_mem_shift hq μ0 hL G (S := G.V (.grid (2 * ρ + 2) 0)) (B := G.V (.grid (2 * ρ + 1) 0))
      (G.Λ (.grid (2 * ρ + 2) 0)) 1 (G.Λ (.grid (2 * ρ + 1) 0)) sdS (by rw [idLat_one]; exact sdT)
      (by rw [one_mul]; exact sdB) _ (by rw [idLat_one]; exact latO_negSp_le _ _ _ _ _ hw.1)
      ⟨e, he, by rw [idLat_one]; exact hw.2 e he⟩
    rw [one_mul] at key
    exact key
  have h1 : 1 ≤ 2 * ρ + 1 := by omega
  have h2 : 2 * ρ + 1 ≤ D.R.m := by omega
  have hlat : ∀ x ∈ G.Λ (.grid (2 * ρ + 1) 0), ((F.dJ ρ h).e * (F.dJ ρ h).qX) *ᵥ x ∈ G.Λ (.grid (2 * ρ + 1) 0) ∧
      ((F.dJ ρ h).e' * (F.dJ ρ h).qY) *ᵥ x ∈ G.Λ (.grid (2 * ρ + 1) 0) := by
    have e1 : G.Λ (.grid (2 * ρ + 1) 0) = (G.colDec (2 * ρ + 1) h1 h2).lat (G.sp.P (2 * ρ + 1)).lat
        (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1)) := G.sp.colLat (2 * ρ + 1) h1 h2
    rw [e1]
    exact proj_lat _ _ (hF.hJ ρ h) (by omega) (hF.aJ ρ h) _ _
  have sdS' : IsSelfDualC (G.V (.grid (2 * ρ + 1 + 1) 0)) (G.Λ (.grid (2 * ρ + 1 + 1) 0)) := sdS
  have hx := GlobalTheory.T.rationalMatrix_sandwich_mem_completed_homLattice_selfDual sdS' sdS' sdB 1 ((F.dJ ρ h).e * (F.dJ ρ h).qX)
    (fun y hy => by rw [Matrix.one_mulVec]; exact hy) (idLat_mulVec _ _ _ fun x hx => (hlat x hx).1) _ big
  have hy := GlobalTheory.T.rationalMatrix_sandwich_mem_completed_homLattice_selfDual sdS' sdS' sdB 1 ((F.dJ ρ h).e' * (F.dJ ρ h).qY)
    (fun y hy => by rw [Matrix.one_mulVec]; exact hy) (idLat_mulVec _ _ _ fun x hx => (hlat x hx).2) _ big
  have hr1 : ∀ x : Mx D (G.V (.grid (2 * ρ + 1) 0)).rank (G.V (.grid (2 * ρ + 2) 0)).rank, x ⬝ rat 1 = x := fun x => by
    rw [rat_one]; exact Matrix.mul_one x
  have ex : (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).incX (F.V₀ ρ) ((F.dJ ρ h).pX ⬝ w)) =
      (rat ((F.dJ ρ h).e * (F.dJ ρ h).qX) ⬝ (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w) ⬝ rat 1 := by
    rw [hr1, rat_mul]
    simp only [HypDec.matrixExtendByZero_apply, HypDec.incX_apply, Matrix.mul_assoc]
    rfl
  have ey : (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).incY (F.V₀ ρ) ((F.dJ ρ h).pY ⬝ w)) =
      (rat ((F.dJ ρ h).e' * (F.dJ ρ h).qY) ⬝ (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w) ⬝ rat 1 := by
    rw [hr1, rat_mul]
    simp only [HypDec.matrixExtendByZero_apply, HypDec.incY_apply, Matrix.mul_assoc]
    rfl
  exact ⟨ex ▸ hx, ey ▸ hy⟩

end GlobalTheory.AscFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeCorePartsMemSelfDualLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depth_lattice_core_parts_mem_selfDual_lattice : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ w : WO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)), (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w ∈ latRow G (2 * ρ + 1) → (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).incX (F.V₀ ρ) ((F.dJ ρ h).pX ⬝ w)) ∈ latBig G (2 * ρ + 1) ∧ (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).incY (F.V₀ ρ) ((F.dJ ρ h).pY ⬝ w)) ∈ latBig G (2 * ρ + 1) := by
  first | exact @GlobalTheory.AscFin.pcBF_big_core | exact GlobalTheory.AscFin.pcBF_big_core | (intros; apply GlobalTheory.AscFin.pcBF_big_core <;> assumption)
end
end
