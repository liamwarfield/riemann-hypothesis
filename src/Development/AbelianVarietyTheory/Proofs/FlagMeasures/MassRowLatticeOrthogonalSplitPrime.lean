module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassGenusCyclicDiscriminantSplitPrime
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeMassRatio
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FormulaCOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaIIota

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassRowLatticeOrthogonalSplitPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassRowLatticeOrthogonalSplitPrime
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical

namespace GlobalTheory.Mass.RowPerpMass

theorem main : ∀ (D : D7) (u : D.what₂.Word), letI := D.host.cmStar; ∀ F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → (Lat.Tu D u).Prime → Lat.SplitsCompletely (E := D.host.E) (Lat.Tu D u) → ∀ Λ : Cnt.LatV D, IsRowLat D F0 Λ → mass (D.sp.X 0).hT (Lat.L0X D Λ (lf D F0)) = Cnt.massS D D.R.k * ((((Lat.Tu D u : ℕ) : ℝ) ^ D.R.k - 1) / (((Lat.Tu D u : ℕ) : ℝ) - 1)) ^ D.R.f ∧ Cnt.massS D D.R.k * Cnt.NT D u ^ (D.R.k - 1) ≤ mass (D.sp.X 0).hT (Lat.L0X D Λ (lf D F0)) := by
  intro D u F0 he hz hp hs Λ hΛ
  let := D.host.cmStar
  obtain ⟨⟨hPD, hrk⟩, hL⟩ := GlobalTheory.Mass.RowPerp.main D u F0 he hz
  obtain ⟨hInt, hdisc⟩ := hL Λ hΛ
  obtain ⟨hsym, hortho, hpos, -, -⟩ := GlobalTheory.T.stdLat_isOrthoLattice_and_mass_properties D.host.E D.sp.cm.cmUnram D.R.k
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega

  have hf : fDeg D.host.E = D.R.f := by
    have : NumberField.IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
    have h1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank D.host.E
    have h2 := Formalism.HC.HostAx.finrank_cmField D.host.toHostAx
    have h3 : NumberField.InfinitePlace.nrRealPlaces D.host.E = 0 :=
      NumberField.IsTotallyComplex.nrRealPlaces_eq_zero D.host.E
    have h4 : fDeg D.host.E = NumberField.InfinitePlace.nrRealPlaces D.host.E +
        NumberField.InfinitePlace.nrComplexPlaces D.host.E :=
      NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces D.host.E
    show _ = 2 * D.R.ord
    omega
  have hmass := GlobalTheory.Mass.CyclicDisc.main GlobalTheory.T.maximalHermitianLattice_massRatio D.host.E (D.sp.X 0).V (D.sp.X 0).hT
    D.sp.cm.cmUnram (D.sp.X 0).herm hPD (by rw [hrk]; exact hk) (Fin D.R.k → D.host.E)
    (Cnt.stdH D.host.E D.R.k) hsym (Cnt.stdLat D.host.E D.R.k) (by rw [hrk]; exact hortho)
    (Lat.Tu D u) hp hs _ hInt hdisc
  rw [hrk, hf] at hmass
  have hS : mass (Cnt.stdH D.host.E D.R.k) (Cnt.stdLat D.host.E D.R.k) = Cnt.massS D D.R.k := rfl
  rw [hS] at hmass
  refine ⟨hmass, ?_⟩
  rw [hmass]

  have hT2 : (2 : ℝ) ≤ (Lat.Tu D u : ℝ) := by exact_mod_cast hp.two_le
  have hgeom : (Lat.Tu D u : ℝ) ^ (D.R.k - 1) ≤ ((Lat.Tu D u : ℝ) ^ D.R.k - 1) / ((Lat.Tu D u : ℝ) - 1) := by
    rw [le_div_iff₀ (by linarith)]
    have e : (Lat.Tu D u : ℝ) ^ D.R.k = (Lat.Tu D u : ℝ) * (Lat.Tu D u : ℝ) ^ (D.R.k - 1) := by
      rw [← pow_succ']; congr 1; omega
    have h1 : (1 : ℝ) ≤ (Lat.Tu D u : ℝ) ^ (D.R.k - 1) := one_le_pow₀ (by linarith)
    rw [e]; nlinarith
  have hNT : Cnt.NT D u ^ (D.R.k - 1) = ((Lat.Tu D u : ℝ) ^ (D.R.k - 1)) ^ D.R.f := by
    show (((D.mem u).A.T : ℝ) ^ D.R.f) ^ (D.R.k - 1) = _
    rw [← pow_mul, ← pow_mul, mul_comm]; rfl
  rw [hNT]
  have hm : 0 ≤ Cnt.massS D D.R.k := hpos.le
  gcongr

end GlobalTheory.Mass.RowPerpMass
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassRowLatticeOrthogonalSplitPrimeStatement
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mass_rowLattice_orthogonal_split_prime : ∀ (D : D7) (u : D.what₂.Word), letI := D.host.cmStar; ∀ F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → (Lat.Tu D u).Prime → Lat.SplitsCompletely (E := D.host.E) (Lat.Tu D u) → ∀ Λ : Cnt.LatV D, IsRowLat D F0 Λ → mass (D.sp.X 0).hT (Lat.L0X D Λ (lf D F0)) = Cnt.massS D D.R.k * ((((Lat.Tu D u : ℕ) : ℝ) ^ D.R.k - 1) / (((Lat.Tu D u : ℕ) : ℝ) - 1)) ^ D.R.f ∧ Cnt.massS D D.R.k * Cnt.NT D u ^ (D.R.k - 1) ≤ mass (D.sp.X 0).hT (Lat.L0X D Λ (lf D F0)) := by
  first | exact @GlobalTheory.Mass.RowPerpMass.main | exact GlobalTheory.Mass.RowPerpMass.main | (intros; apply GlobalTheory.Mass.RowPerpMass.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointsBaseLatticeStabilizerFixedFrameUnipote
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointsBaseLatticeStabilizerFixedFrameUnipote
open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TypeAsm.GLinkPf

section Gen
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem inN_of_nlam (F : FlagG S r T) (hT : T ≠ 0) {n : S.V ≃ₗ[E] S.V} {Λ : Submodule (𝓞 E) S.V}
    (h : n ∈ NLam Λ (⟨F, F.z⟩ : LFlag S r T)) : (frF F hT).InN (n : S.V →ₗ[E] S.V) := by
  obtain ⟨⟨hiso, -⟩, hXa, hperp⟩ := h
  refine ⟨fun x y => hiso y x, n.bijective, fun a => ?_, fun y hy => ?_⟩
  · rw [GlobalTheory.TypeAsm.FibProof.frF_e, fv_cast, GlobalTheory.TypeAsm.FibProof.frF_Xa]
    exact hXa a.val (F.e a) (Submodule.subset_span ⟨a, Nat.lt_succ_self _, rfl⟩)
  · rw [GlobalTheory.TypeAsm.FibProof.frF_X]
    apply hperp
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
    intro x hx
    change x ∈ F.X at hx
    rw [← GlobalTheory.TypeAsm.FibProof.frF_X F hT] at hx
    have hle : (frF F hT).X ≤ LinearMap.ker (S.hT.flip y) := by
      unfold Formalism.HermitianLatticeCounting.S6.FlagD.X Formalism.HermitianLatticeCounting.S6.FlagD.Xa
      rw [Submodule.span_le]
      rintro _ ⟨a, -, rfl⟩
      have := hy a
      rw [GlobalTheory.TypeAsm.FibProof.spH_B] at this
      exact p_symm_zero S this
    exact hle hx

end Gen

variable {D : D7} {X : HidaSetting D}

theorem smul_top (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    n • (⊤ : Submodule (𝓞 D.host.E) (VS D).V) = ⊤ := by
  rw [← GlobalTheory.TypeAsm.FibProof.gmap_eq_smul]
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.map_top]
  exact LinearMap.range_eq_top.2 n.surjective

theorem mem_gam_iff (u : D.what₂.Word) (N : GlobalTheory.DegCnt.NF (HV D) D.R.rS) (hF : N.F = F0 X u)
    (hF' : N.F' = F0 X u) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    n ∈ N.Gam (VS D).L0 ↔ n ∈ NLam (VS D).L0 (lf D (X.Fu u)) := by
  unfold GlobalTheory.DegCnt.NF.Gam GlobalTheory.DegCnt.NF.R
  rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  constructor
  · rintro ⟨hR, hst⟩
    have hT : n ∈ NLam ⊤ (lf D (X.Fu u)) := by
      clear hst
      induction hR using Subgroup.closure_induction with
      | mem s hs =>
        have h1 := hs.1
        rw [hF] at h1
        exact GlobalTheory.TypeAsm.FibProof.nlam_of_inN (lf D (X.Fu u)).fl (tu_ne D u) h1 (smul_top s)
      | one => exact GlobalTheory.LoopC.FrEqv.one_mem_NLam
      | mul x y _ _ hx hy => exact GlobalTheory.LoopC.FrEqv.mul_mem_NLam hy hx
      | inv x _ hx => exact GlobalTheory.LoopC.FrEqv.symm_mem_NLam hx
    exact ⟨⟨hT.1.1, by rw [GlobalTheory.TypeAsm.FibProof.gmap_eq_smul]; exact hst⟩, hT.2.1, hT.2.2⟩
  · intro h
    refine ⟨Subgroup.subset_closure ?_, ?_⟩
    · have h1 : (F0 X u).InN (n : (VS D).V →ₗ[D.host.E] (VS D).V) := inN_of_nlam (lf D (X.Fu u)).fl (tu_ne D u) h
      rw [hF, hF']
      exact ⟨h1, h1⟩
    · rw [← GlobalTheory.TypeAsm.FibProof.gmap_eq_smul]; exact h.1.2

theorem trI_act (C : Choice X 1) {x : X.B.I.GA} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x n)
    (τ : D.what₂.Tau) (y : (VS D).V) :
    Matrix.of (trI C x.1 τ) *ᵥ phiV C τ y = phiV C τ (n y) := by
  obtain ⟨_, hQQi, _, _⟩ := C.isT τ
  obtain ⟨M, _, hM1, _, hM3⟩ := hx
  have hM1' : uMat (x.1 (vOf X τ)) = (X.B.I.P (vOf X τ))⁻¹ *
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ (vOf X τ)) * X.B.I.P (vOf X τ) := hM1 _
  have hM3' : X.crd (n y) = (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y := hM3 y
  have e : Matrix.of (trI C x.1 τ) = Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x.1 (vOf X τ)) := by
    unfold trI; exact Matrix.of.apply_symm_apply _
  rw [e]
  unfold GlobalTheory.TypeAsm.phiV Formalism.L2.SG.RealObj.trG
  rw [hM3', ← Formalism.L2.SG.Pf.rv_mulVec X (vOf X τ), ← hM1']
  have hQ : ∀ w, C.Q τ *ᵥ (C.Qi τ *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]
  simp only [← Matrix.mulVec_mulVec]
  rw [hQ]

theorem eq_of_act (C : Choice X 1) {m m' : D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS}
    {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (h : ∀ τ y, Matrix.of (m τ) *ᵥ phiV C τ y = phiV C τ (n y))
    (h' : ∀ τ y, Matrix.of (m' τ) *ᵥ phiV C τ y = phiV C τ (n y)) : m = m' := by
  funext τ
  have hL : Matrix.mulVecLin (Matrix.of (m τ)) = Matrix.mulVecLin (Matrix.of (m' τ)) :=
    LinearMap.ext_on_range (GlobalTheory.TypeAsm.GramPf.phiV_span C τ) (fun y => by
      rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, h τ y, h' τ y])
  apply Matrix.of.injective
  ext i j
  have := congrFun (LinearMap.congr_fun hL (Pi.single j 1)) i
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single_one] using this

end GlobalTheory.TypeAsm.GLinkPf

namespace GlobalTheory.TypeAsm

theorem realPts_Gam_eq_trI_image_NOinf : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (C : Choice X 1), Std D large₂ →
    ∀ N : GlobalTheory.DegCnt.NF (HV D) D.R.rS, N.F = F0 X u → N.F' = F0 X u →
      GlobalTheory.DegVol.realPts (fun τ => phiV C τ) (N.Gam (VS D).L0 : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)) =
        trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u := by
  intro D _ X _ u C _ N hF hF'
  ext m
  constructor
  · rintro ⟨n, hn, hm⟩
    have hL := (GLinkPf.mem_gam_iff u N hF hF' n).1 hn
    obtain ⟨x, hx⟩ := Formalism.L2.SG.Pf.ratPt_holds D X n hL.1.1
    refine ⟨x.1, (Formalism.L2.SG.Pf.NcReal.JX.NOf.noratC_holds X u x.1).2 ⟨x, n, hx, rfl, hL⟩, ?_⟩
    exact GLinkPf.eq_of_act C (GLinkPf.trI_act C hx) (fun τ y => hm τ y)
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨x, n, hx, rfl, hL⟩ := (Formalism.L2.SG.Pf.NcReal.JX.NOf.noratC_holds X u s).1 hs
    exact ⟨n, (GLinkPf.mem_gam_iff u N hF hF' n).2 hL, fun τ y => GLinkPf.trI_act C hx τ y⟩

end GlobalTheory.TypeAsm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointsBaseLatticeStabilizerFixedFrameUnipoteStatement
open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_points_base_lattice_stabilizer_fixed_frame_unipotent : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (C : Choice X 1), Std D large₂ →
    ∀ N : GlobalTheory.DegCnt.NF (HV D) D.R.rS, N.F = F0 X u → N.F' = F0 X u →
      GlobalTheory.DegVol.realPts (fun τ => phiV C τ) (N.Gam (VS D).L0 : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)) =
        trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u := by
  first | exact @GlobalTheory.TypeAsm.realPts_Gam_eq_trI_image_NOinf | exact GlobalTheory.TypeAsm.realPts_Gam_eq_trI_image_NOinf | (intros; apply GlobalTheory.TypeAsm.realPts_Gam_eq_trI_image_NOinf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalCompatibilityOfLocalIdentifications
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalCompatibilityOfLocalIdentifications
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IotaLocConv

open Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

variable {D : D7}

theorem locH_add_right (Z : LocDat D) (p : PlF D) (x y y' : Vp D p) :
    (locH Z p).h x (y + y') = (locH Z p).h x y + (locH Z p).h x y' := by
  rw [(locH Z p).h_herm (y + y') x, (locH Z p).h_add_left, map_add (f := _), ← (locH Z p).h_herm,
    ← (locH Z p).h_herm]

theorem locH_smul_right (Z : LocDat D) (p : PlF D) (c : (D.s.atP p).Ep) (x y : Vp D p) :
    (locH Z p).h x (c • y) = (Z.M p).L.cj c * (locH Z p).h x y := by
  rw [(locH Z p).h_herm (c • y) x, (locH Z p).h_smul_left, map_mul, ← (locH Z p).h_herm]

theorem baseChange_mem_perp_sup (Z : LocDat D) (p : PlF D) {T : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T) {m : (VS D).V}
    (hm : m ∈ orth (VS D) (Xsp G)) :
    baseChange₂ D p m ∈ (locH Z p).perp ((locH Z p).X (scaled Z p (frame G))) := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hm
  show ∀ y ∈ (locH Z p).X (scaled Z p (frame G)), (locH Z p).h (baseChange₂ D p m) y = 0
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    show (locH Z p).h (baseChange₂ D p m) (frFac Z.δ p a.castSucc • baseChange₂ D p (frame G a.castSucc)) = 0
    rw [locH_smul_right, BwdNP.localForm_baseChange, GlobalTheory.LocExt.frame_castSucc,
      hm (G.fl.e a) (Submodule.subset_span ⟨a, rfl⟩), map_zero, mul_zero]
  | zero =>
    have h2 := locH_add_right Z p (baseChange₂ D p m) 0 0
    rw [add_zero] at h2
    linear_combination -h2
  | add y y' _ _ hy hy' => rw [locH_add_right, hy, hy', add_zero]
  | smul c y _ hy => rw [locH_smul_right, hy, mul_zero]

theorem theta_of_split (Z : LocDat D) (p : PlF D) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L)
    (hs : (Z.M p).split = some g) : Formalism.MainNotions.S.LocNG.theta (Z.M p) = (g.q : (D.s.atP p).Fp) := by
  unfold Formalism.MainNotions.S.LocNG.theta
  rw [hs]

theorem cong_of_mem (Z : LocDat D) (p : PlF D) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L) (hs : (Z.M p).split = some g)
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)
    (F' : LFlag (D.sp.Y 0) D.R.rS T') {v : (VS D).V} (hv : v ∈ NgX Λ (gS D) F F') :
    Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame F)) (scaled Z p (frame F')) (baseChange₂ D p v) := by
  obtain ⟨l, hl, ξ, hξ, ξ', hξ', rfl⟩ := IotaBP.NgX_dec hv
  obtain ⟨w, hw, -, -, he, -⟩ := IotaBP.gS_typed Z p g hs
  have hξX : ξ ∈ Xsp F := (Submodule.mem_inf.1 hξ).2
  have hξ'X : ξ' ∈ Xsp F' := (Submodule.mem_inf.1 hξ').2
  refine ⟨algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) • (w • baseChange₂ D p l), ?_,
    baseChange₂ D p ξ, BwdNP.baseChange_mem_localLattice Z (Submodule.mem_inf.1 hξ).1 p, baseChange₂ D p ξ', BwdNP.baseChange_mem_localLattice Z (Submodule.mem_inf.1 hξ').1 p,
    GlobalTheory.LocExt.bcP_Xsp_mem Z p F hξX, GlobalTheory.LocExt.bcP_Xsp_mem Z p F' hξ'X, ?_⟩
  · rw [theta_of_split Z p g hs]
    exact Submodule.subset_span ⟨_, Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Z p hw (BwdNP.baseChange_mem_localLattice Z hl p), rfl⟩
  · rw [map_add (f := _), map_add (f := _), baseChange_smul₂, he, mul_smul]

theorem mem_localLattice_of_cong (Z : LocDat D) (p : PlF D) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L)
    (hs : (Z.M p).split = some g) {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Λ.FG) {T T' : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') {w : Vp D p}
    (hw : Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame F)) (scaled Z p (frame F')) w) :
    w ∈ lattice₂ D Z.M p (NgX Λ (gS D) F F') := by
  obtain ⟨a, ha, b, hb, c, hc, hbX, hcX, rfl⟩ := hw
  have hX : ∀ {T₁ : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T₁) {y : Vp D p}, y ∈ lattice₂ D Z.M p Λ →
      y ∈ (locH Z p).X (scaled Z p (frame G)) → y ∈ lattice₂ D Z.M p (XLam Λ G) := by
    intro T₁ G y hy hyX
    have hsp : y ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (Xsp G : Set (VS D).V)) := by
      refine Submodule.span_le.2 ?_ hyX
      rintro _ ⟨i, rfl⟩
      show frFac Z.δ p i.castSucc • baseChange₂ D p (frame G i.castSucc) ∈ _
      rw [GlobalTheory.LocExt.frame_castSucc]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨G.fl.e i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩)
    have h := Formalism.L2.SG.Pf.locSatC_holds D Z p Λ (Xsp G) hΛ
    have h2 : y ∈ (lattice₂ D Z.M p (Λ ⊓ toO (VS D) (Xsp G)) : Set (Vp D p)) := by
      rw [h]; exact ⟨hy, hsp⟩
    exact h2
  refine add_mem (add_mem ?_ ?_) ?_
  · rw [theta_of_split Z p g hs] at ha
    unfold Formalism.MainNotions.S.Loc.HermSp.smulLat at ha
    refine (Submodule.span_le.2 ?_) ha
    rintro _ ⟨y, hy, rfl⟩
    exact IotaBP.typed_q_mem Z p g hs F F' hy
  · exact IotaBP.localLattice_mono Z p (le_sup_right.trans le_sup_left) (hX F hb hbX)
  · exact IotaBP.localLattice_mono Z p le_sup_right (hX F' hc hcX)

theorem mem_NgX_of_local (Z : LocDat D) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ : Submodule.IsFullLattice D.host.E Λ) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)
    (F' : LFlag (D.sp.Y 0) D.R.rS T') {v : (VS D).V} (hv : v ∈ Λ)
    (h : ∀ p : PlF D, (Z.M p).split ≠ none →
      Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame F)) (scaled Z p (frame F')) (baseChange₂ D p v)) :
    v ∈ NgX Λ (gS D) F F' := by
  refine BwdNP.mem_of_bcP Z (IotaBP.isLattice_NgX hΛ F F') fun p => ?_
  match hs : (Z.M p).split with
  | none => exact IotaBP.untyped_mem Z p hs F F' (BwdNP.baseChange_mem_localLattice Z hv p)
  | some g => exact mem_localLattice_of_cong Z p g hs hΛ.toIsLattice.fg F F' (h p (by rw [hs]; exact Option.some_ne_none g))

theorem iotaCompat_of_local : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (t₀ t : TauC Y u u'),
    t.lam = t₀.lam → t.lam' = t₀.lam' →
    (∀ p : PlF D, (Y.M p).split ≠ none → ∀ gβ, Ext p (t.lin * t₀.lin⁻¹) gβ →
      ∀ x' ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam,
      ∀ x ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam,
      x' ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X
        (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t₀.frame))) →
      x ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X
        (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u))))) →
      (Cong (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) (lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam)
          (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u))))
          (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t₀.frame)) (x - x') ↔
        Cong (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) (lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam)
          (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u))))
          (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t.frame)) (x - gβ x'))) →
    IotaCompat t₀.lam (lf D (X.Fu u)) t₀.frame t.frame (t.lin * t₀.lin⁻¹) (gS D) := by
  intro D X Y u u' t₀ t hl hl' hloc
  set Z : LocDat D := ⟨Y.δ, Y.M, Y.agree⟩ with hZ
  have hγ0 : t₀.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₀.rep.2.2.1
  have hγ1 : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hβ : t.lin * t₀.lin⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := mul_mem hγ1 (inv_mem hγ0)
  have hg0 : Formalism.HermitianLatticesTheory.gmap t₀.lin t₀.lam' = t₀.lam := t₀.rep.2.2.2.1
  have hg1 : Formalism.HermitianLatticesTheory.gmap t.lin t₀.lam' = t₀.lam := by
    have h : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := t.rep.2.2.2.1
    rw [hl, hl'] at h
    exact h
  have hβΛ : ∀ y ∈ t₀.lam, (t.lin * t₀.lin⁻¹) y ∈ t₀.lam := by
    intro y hy
    rw [← hg0] at hy
    obtain ⟨y', hy', rfl⟩ := Submodule.mem_map.1 hy
    rw [← hg1]
    refine Submodule.mem_map.2 ⟨y', hy', ?_⟩
    show t.lin y' = t.lin (t₀.lin.symm (t₀.lin y'))
    rw [LinearEquiv.symm_apply_apply]
  have hLat : Submodule.IsFullLattice D.host.E t₀.lam := ((Y.rowsOK u).1 t₀.lam t₀.mem).1.1
  unfold Formalism.MainNotions.S.Lat.IotaCompat
  intro x' hx' l hlr
  have hx'Λ : x' ∈ t₀.lam := (Submodule.mem_inf.1 hx').1
  have hx'o : x' ∈ orth (VS D) (Xsp t₀.frame) := (Submodule.mem_inf.1 hx').2
  have hlΛ : l ∈ t₀.lam := (Submodule.mem_inf.1 hlr).1
  have hlo : l ∈ orth (VS D) (Xsp (lf D (X.Fu u))) := (Submodule.mem_inf.1 hlr).2
  have hβx' : (t.lin * t₀.lin⁻¹) x' ∈ t₀.lam := hβΛ x' hx'Λ
  have key : ∀ p : PlF D, (Z.M p).split ≠ none →
      (Cong (locH Z p) (lattice₂ D Z.M p t₀.lam) (scaled Z p (frame (lf D (X.Fu u)))) (scaled Z p (frame t₀.frame))
          (baseChange₂ D p (l - x')) ↔
        Cong (locH Z p) (lattice₂ D Z.M p t₀.lam) (scaled Z p (frame (lf D (X.Fu u)))) (scaled Z p (frame t.frame))
          (baseChange₂ D p (l - (t.lin * t₀.lin⁻¹) x'))) := by
    intro p hp
    obtain ⟨gβ, hext, -⟩ := GlobalTheory.LocExt.ext_isometry D Z p _ hβ
    have h := hloc p hp gβ hext (baseChange₂ D p x') (BwdNP.baseChange_mem_localLattice Z hx'Λ p) (baseChange₂ D p l) (BwdNP.baseChange_mem_localLattice Z hlΛ p)
      (baseChange_mem_perp_sup Z p _ hx'o) (baseChange_mem_perp_sup Z p _ hlo)
    rw [map_sub, map_sub, ← hext x']
    exact h
  constructor
  · intro h1
    refine mem_NgX_of_local Z hLat _ _ (sub_mem hlΛ hβx') fun p hp => ?_
    obtain ⟨g, hg⟩ := Option.ne_none_iff_exists'.1 hp
    exact (key p hp).1 (cong_of_mem Z p g hg _ _ h1)
  · intro h2
    refine mem_NgX_of_local Z hLat _ _ (sub_mem hlΛ hx'Λ) fun p hp => ?_
    obtain ⟨g, hg⟩ := Option.ne_none_iff_exists'.1 hp
    exact (key p hp).2 (cong_of_mem Z p g hg _ _ h2)

end GlobalTheory.IotaLocConv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalCompatibilityOfLocalIdentificationsStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalCompatibility_of_local_identifications : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (t₀ t : TauC Y u u'), t.lam = t₀.lam → t.lam' = t₀.lam' → (∀ p : PlF D, (Y.M p).split ≠ none → ∀ gβ, Ext p (t.lin * t₀.lin⁻¹) gβ → ∀ x' ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, ∀ x ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam, x' ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t₀.frame))) → x ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u))))) → (Cong (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) (lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u)))) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t₀.frame)) (x - x') ↔ Cong (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) (lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p t₀.lam) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u)))) (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame t.frame)) (x - gβ x'))) → IotaCompat t₀.lam (lf D (X.Fu u)) t₀.frame t.frame (t.lin * t₀.lin⁻¹) (gS D) := by
  first | exact @GlobalTheory.IotaLocConv.iotaCompat_of_local | exact GlobalTheory.IotaLocConv.iotaCompat_of_local | (intros; apply GlobalTheory.IotaLocConv.iotaCompat_of_local <;> assumption)
end
end
