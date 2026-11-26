module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LettersPassPartialBessel
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ProperDomP

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.Side0PosOf
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.LeftFubiniLemmas

theorem side0Pos_of (hW : PartialBesselProperness.PbWords) (hPr : ProperLeftVariablesDomain) (hPts : CutHB.Pts) : CutHB.Side0Pos := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh γ hj1 hF hw hγ hΩ e τ hτ
  have hPt := hPts Wp Wq P p j hj h hh γ hγ hΩ
  obtain ⟨hab, rfl⟩ := hh
  have hjr : D.ptSize h ≤ P.r := by omega
  have e0 : D.ptSize h + (P.r - D.ptSize h) = P.r := by omega
  have hd : ∀ q, D.ptDiag h q ≠ 0 := fun q => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne h hab q q.2
  have hT := p.hT
  obtain ⟨R, hR⟩ := hF.2.1

  have hOm : LevelPointCoordinates.mLev P (D.ptSize h) hj τ γ ∈
      JF.Om P.k (P.r - D.ptSize h) (p.T.bs (D.ptSize h)).z (p.T.bs (D.ptSize h)).z' := by
    have h2 := Formalism.FourierDecayAlt.P.PBH.om_cast (by omega : P.r - (D.ptSize h + 1) + 1 = P.r - D.ptSize h) _ _ _
      (Formalism.FourierDecayAlt.P.PBH.mcOm P.k (P.r - (D.ptSize h + 1)) (p.T.bs (D.ptSize h + 1)).z (p.T.bs (D.ptSize h + 1)).z'
        (p.T.bs (D.ptSize h + 1)).z_mem (p.T.bs (D.ptSize h + 1)).z'_mem τ hτ γ hγ hΩ)
    rw [Formalism.FourierDecayAlt.P.PBH.asm_castM_castM, Formalism.FourierDecayAlt.P.PBH.asm_castV_castV, Formalism.FourierDecayAlt.P.PBH.asm_castV_castV] at h2
    rw [Formalism.FourierDecayAlt.P.PBH.levTower_bs_z_eq_castV_liftVec p.T _ hj, Formalism.FourierDecayAlt.P.PBH.levTower_bs_z'_eq_castV_liftVec p.T _ hj]
    exact h2
  have hHc : ContinuousOn (D.uwG P.k P.r p.T.base.z p.T.base.z' F (D.ptSize h) hjr w e)
      {x | x ∈ B.GV P.k P.r ∧ Dmin P.k P.r p.T.base.z p.T.base.z' x ⟨D.ptSize h, by omega⟩ ≠ 0} :=
    Formalism.FourierDecayAlt.P.PBG.contOn_of_loc (S := Formalism.FourierDecayAlt.P.PBG.Sd p.T.base.z p.T.base.z' (D.ptSize h) hjr)
      (fun x hx hxG => Formalism.FourierDecayAlt.P.PBG.uwG_mem (E := Wq →L[ℂ] Wp) p.T.base.z p.T.base.z' (D.ptSize h) hjr hF.1 w e
        x hx hxG)
  have hR' := Formalism.FourierDecayAlt.P.PBG.uwG_supp p.T.base.z p.T.base.z' F R hR (D.ptSize h) hjr w e
  have key := jfSliceIntN e0 hj1 (D.ptPerm h) (D.ptDiag h) hd (p.T.bs (D.ptSize h)) p.T.base
    (p.T.z_lev _ hjr) (p.T.z'_lev _ hjr) (p.T.π'_lev _ hjr) (hT _ hjr).2.1
    (Formalism.FourierDecayAlt.P.PBM.tower_haarW' p.T hT _ hjr e0) (hT _ hjr).2.2 (hT 0 (Nat.zero_le _)).2.2
    (LevelPointCoordinates.mLev P (D.ptSize h) hj τ γ) hOm _ hHc R hR'
  have hs := slice_eq p.T.base.z p.T.base.z' (D.uwG P.k P.r p.T.base.z p.T.base.z' F (D.ptSize h) hjr w e) h hjr
    rfl e0
  show B.JF (p.T.bs (D.ptSize h)) (D.castF _ (D.sliceAt P.k P.r p.T.base.z p.T.base.z'
    (D.uwG P.k P.r p.T.base.z p.T.base.z' F (D.ptSize h) hjr w e) h)) (LevelPointCoordinates.mLev P (D.ptSize h) hj τ γ) = _
  rw [hs, key]
  congr 1
  funext v
  have hZ : IsUnit (lhOf (D.ptPerm h) v * U.hMat (D.ptPerm h) (D.ptDiag h)).det := by
    rw [Matrix.det_mul]
    exact (lh_unit _ v).mul (Ne.isUnit (Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne _ _ hd))
  have hz : PBQ.zxH h (D.ptSize h) rfl v = lhOf (D.ptPerm h) v * U.hMat (D.ptPerm h) (D.ptDiag h) := by
    simp only [PBQ.zxH, finCongr_refl, Matrix.reindex_refl_refl]
  have hpt : D.castM e0 (U.mMap P.k (D.ptSize h) (P.r - D.ptSize h)
      (lhOf (D.ptPerm h) v * U.hMat (D.ptPerm h) (D.ptDiag h)) (LevelPointCoordinates.mLev P (D.ptSize h) hj τ γ)) =
      LevelPointCoordinates.x0 P.k P.r (D.ptSize h) hj (PBQ.zxH h (D.ptSize h) rfl v) τ γ := by
    rw [hz]
    exact pt_eq hj _ hZ τ hτ γ e0 _
  rw [hpt]
  have hy := (hPt v).2 τ hτ
  have hyG : LevelPointCoordinates.x0 P.k P.r (D.ptSize h) hj (PBQ.zxH h (D.ptSize h) rfl v) τ γ ∈ B.GV P.k P.r :=
    LevelPointCoordinates.x0_GV hj (hPt v).1 hτ hγ
  have hpw := hW P.k (D.ptSize h) (P.r - D.ptSize h) P.r Wp Wq (p.T.bs (D.ptSize h)) p.T.base e0
    (p.T.z_lev _ hjr).symm (D.ptSize h) hjr F {g | B.gN g ≤ R} (fun g hg _ => hF.1 g hg)
    (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le _ _ R) (fun g hg hgC => by
      by_contra hne
      exact hgC (hR g hg hne))
    (PBQ.domP P.k P.r (D.ptSize h) p.T.base.z p.T.base.z') (PBQ.isOpen_domP _ _ _ _ _)
    (fun g hg => hg.1 ⟨D.ptSize h, by omega⟩ le_rfl hjr)
    (hPr Wp Wq P p (D.ptSize h) hjr _ (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le _ _ R)) w e _ hy hyG
  unfold PBQ.ellH CutHB.phf
  rw [_root_.smul_apply, ContinuousLinearMap.id_apply, ← hpw]
  rfl

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

theorem side0Pos_of'' (hPr : ProperLeftVariablesDomain) : CutHB.Side0Pos :=
  side0Pos_of Formalism.FourierDecayAlt.P.letters_pass_partial_bessel hPr CutHB.pts

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.DetLowW
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBQ

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem kr_agree {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (l : Fin (r + 2)) (a : ℂ) (H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp))
    (hH : ∀ g ∈ B.GV k r, Dmin k r Bs.z Bs.z' g l = a → H₁ g = H₂ g) (y : B.Mat k r) (hy : y ∈ B.GV k r)
    (hya : Dmin k r Bs.z Bs.z' y l = a) : PBG.Kr Bs H₁ y = PBG.Kr Bs H₂ y := by
  unfold PBG.Kr
  refine integral_congr_ae ?_
  filter_upwards [PBG.ae_inR Bs] with ξ hξ
  have hg : y * Matrix.of ξ.2 * Matrix.of ξ.1 ∈ B.GV k r :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hy hξ.2.1) hξ.1.1
  rw [hH _ hg (by rw [PBG.dmin_pR Bs hξ y l, hya])]

theorem pbT_agree (P : M.Par) (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j + 1 ≤ P.r) (a : ℂ)
    (H₁ H₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hH : ∀ g ∈ B.GV P.k P.r, Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩ = a → H₁ g = H₂ g)
    (g : B.Mat P.k P.r) (hg : g ∈ B.GV P.k P.r)
    (hga : Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩ = a) :
    pbT p j (by omega) H₁ g = pbT p j (by omega) H₂ g := by
  unfold pbT
  have e : j + (P.r - j) = P.r := by omega
  rw [PartialBesselProperness.pbF_eq_TI, PartialBesselProperness.pbF_eq_TI]
  unfold PartialBesselProperness.TI
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [PartialBesselProperness.gI]
  split_ifs with hx
  · have hs : PartialBesselProperness.sE (p.T.bs j) e x ∈ Sset P.k P.r p.T.base.z := by
      have := PartialBesselProperness.sE_mem_S (p.T.bs j) e x
      rwa [p.T.z_lev j (by omega)] at this
    have hyG : PartialBesselProperness.sE (p.T.bs j) e x * g ∈ B.GV P.k P.r := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (PartialBesselProperness.sE_GV _ e x) hg
    have hyD : Dmin P.k P.r p.T.base.z p.T.base.z' (PartialBesselProperness.sE (p.T.bs j) e x * g) ⟨j + 1, by omega⟩ = a := by
      have := Formalism.QuantumDeterminants.diagonal_inverse_holds P.k P.r p.T.base.z p.T.base.z' p.T.base.z_mem p.T.base.z'_mem _ hs 1
        (Formalism.FourierDecayAlt.P.PBG.one_mem_Sset P.k P.r _) g ⟨j + 1, by omega⟩
      rw [Matrix.mul_one] at this
      rw [this, hga]
    rw [kr_agree p.T.base ⟨j + 1, by omega⟩ a H₁ H₂ hH _ hyG hyD]
  · rfl

def aVal (h : C.LPt) (t : ℂ) : ℂ := (U.hMat (D.ptPerm h) (D.ptDiag h)).det * t

def CutOffStep : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j)
    (γ : B.Mat P.k (P.r - (j + 1))),
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w → γ ∈ B.GV P.k (P.r - (j + 1)) →
    γ ∈ Q.OmPlus P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' →
    ∀ (t : ℂ) (ht : D.IsLocPt (h ++ [(1, t)]) (j + 1)) (e : Wd.Ix (Fin w.length)) (Fc : B.Mat P.k P.r → (Wq →L[ℂ] Wp)),
    KB.CptCoef p.T.base Fc →
    (∀ g, Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩ = aVal h t →
      Fc g = D.uwG P.k P.r p.T.base.z p.T.base.z' F (j + 1) hj w e g) →
    B.JF (p.T.bs (j + 1)) (KB.slv p.T F (j + 1) hj w (h ++ [(1, t)]) ht.2 e) γ =
      B.JF (p.T.bs j) (KB.slv p.T Fc j (by omega) [] h hh.2 fun a => a.elim0) (mLev P j hj t γ)

def CutOffExists : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j),
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w →
    ∀ (t : ℂ), D.IsLocPt (h ++ [(1, t)]) (j + 1) → ∀ e : Wd.Ix (Fin w.length),
    ∃ Fc : B.Mat P.k P.r → (Wq →L[ℂ] Wp), KB.CptCoef p.T.base Fc ∧
      ∀ g, Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩ = aVal h t →
        Fc g = D.uwG P.k P.r p.T.base.z p.T.base.z' F (j + 1) hj w e g

theorem det_lowW {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : U.LW σ → ℂ) : (U.lowW σ v).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp [U.lowW]
  · intro a b hab
    simp only [U.lowW, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply]
    have hab' : a < b := hab
    rw [if_neg (ne_of_lt hab'), dite_eq_right (fun h => absurd h.1 (not_lt.mpr hab'.le)), add_zero]

theorem zxH_det (h : C.LPt) (j : ℕ) (hh : D.IsLocPt h j) (v : XH h) :
    (zxH h j hh.2 v).det = (U.hMat (D.ptPerm h) (D.ptDiag h)).det := by
  have hH : (U.hMat (D.ptPerm h) (D.ptDiag h)).det ≠ 0 :=
    Formalism.FourierDecayAlt.P.PBM.hMat_det_ne _ _ (CutHB.ptDiag_ne hh)
  have hw : IsUnit (U.wP (D.ptPerm h)) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro h0
    apply hH
    rw [U.hMat, Matrix.det_mul, h0, zero_mul]
  unfold zxH LeftFubiniLemmas.lhOf
  rw [Matrix.det_reindex_self, Matrix.det_mul, Matrix.det_conj hw, det_lowW, one_mul]

end Formalism.FourierDecayAlt.P.LevelPointCoordinates
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPolyProp
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem rdsp_opApply_vanish (Θ : B.DiffOp k r Wp Wq) {O : Set (B.Mat k r)} (hO : IsOpen O)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hz : ∀ g ∈ B.GV k r, g ∈ O → F g = 0) :
    ∀ g ∈ B.GV k r, g ∈ O → B.opApply Θ F g = 0 := by
  intro g hg hgO
  unfold B.opApply
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hx
  rw [Formalism.FourierDecayAlt.P.BetaSesquilinearity.Rw_vanish hO T.word_lie hz g hg hgO, map_zero]

theorem rdsp_adjFn_vanish (T : B.DTerm k r Wp Wq) {O : Set (B.Mat k r)}
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hz : ∀ g ∈ B.GV k r, g ∈ O → F g = 0) :
    ∀ g ∈ B.GV k r, g ∈ O → ap T.coefAdj F g = 0 := by
  intro g hg hgO
  simp only [Formalism.FourierDecayAlt.P.BetaSesquilinearity.ap]
  rw [hz g hg hgO, map_zero]

theorem rdsp_lie_rev (T : B.DTerm k r Wp Wq) : ∀ X ∈ T.word.reverse, inLie k r X := by
  intro X hX
  exact T.word_lie X (List.mem_reverse.mp hX)

theorem rdsp_opAdj_eq (Θ : B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) :
    B.opAdj Θ F = fun g => (Θ.map fun T => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (ap T.coefAdj F) g).sum := rfl

theorem rdsp_opAdj_vanish (Θ : B.DiffOp k r Wp Wq) {O : Set (B.Mat k r)} (hO : IsOpen O)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hz : ∀ g ∈ B.GV k r, g ∈ O → F g = 0) :
    ∀ g ∈ B.GV k r, g ∈ O → B.opAdj Θ F g = 0 := by
  intro g hg hgO
  rw [rdsp_opAdj_eq]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hx
  rw [Formalism.FourierDecayAlt.P.BetaSesquilinearity.Rw_vanish hO (rdsp_lie_rev T) (rdsp_adjFn_vanish T hz) g hg hgO, smul_zero]

theorem rdsp_opAdj_cc (Θ : B.DiffOp k r Wp Wq) (d : ℝ) (hG : CutMP.GlobCoef Θ d) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (hF : B.CkOn ⊤ (B.GV k r) F) (A : ℝ) (hFA : ∀ m : ℕ, B.InCC (A + d) m F) :
    B.CkOn ⊤ (B.GV k r) (B.opAdj Θ F) ∧ ∀ m : ℕ, B.InCC A m (B.opAdj Θ F) := by
  have hO : IsOpen (∅ : Set (B.Mat k r)) := isOpen_empty
  have hcov : ∀ g ∈ B.GV k r, g ∈ (∅ : Set (B.Mat k r)) ∨ g ∈ B.GV k r := fun g hg => Or.inr hg
  have hz0 : ∀ g ∈ B.GV k r, g ∈ (∅ : Set (B.Mat k r)) → F g = 0 := fun g _ hg => by simp at hg
  have hapck : ∀ T ∈ Θ, B.CkOn ⊤ (B.GV k r) (ap T.coefAdj F) := fun T hT =>
    Pr.ck hO hcov ⟨(hG T hT).2.1, hF, hz0⟩
  have hRck : ∀ T ∈ Θ, B.CkOn ⊤ (B.GV k r) (B.Rw T.word.reverse (ap T.coefAdj F)) := by
    intro T hT
    rw [← Dw_wR]
    apply CkOn_Dw (fun x hx => lie_LR (u := []) (by simp) (rdsp_lie_rev T) x (by simpa [wL] using hx))
    simpa using hapck T hT
  have hapcc : ∀ T ∈ Θ, ∀ m : ℕ, B.InCC A m (ap T.coefAdj F) := by
    intro T hT m
    obtain ⟨hc1, hc2, hcb⟩ := hG T hT
    obtain ⟨C, hC⟩ := hcb m
    obtain ⟨c, hc⟩ := hFA m
    exact ⟨_, prodBound hO hcov (sCkOn_mono le_top hc2)
      (fun u v hu hv hl g hg _ => (hC u v hu hv hl g hg).2) hc hz0⟩
  rw [rdsp_opAdj_eq]
  refine ⟨?_, fun m => ?_⟩
  · clear hapcc
    induction Θ with
    | nil => simpa using (CkOn_zero : B.CkOn ⊤ (B.GV k r) (fun _ => (0 : Wq →L[ℂ] Wp)))
    | cons T Θ ih =>
      have h1 : B.CkOn ⊤ (B.GV k r) (fun g => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (ap T.coefAdj F) g) :=
        CkOn_smul _ (hRck T (by simp))
      have h2 := ih (fun S hS => hG S (by simp [hS])) (fun S hS => hapck S (by simp [hS]))
        (fun S hS => hRck S (by simp [hS]))
      simpa using CkOn_add h1 h2
  · refine InCC_opsum Θ (fun T g => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (ap T.coefAdj F) g) ?_
    intro T hT
    obtain ⟨c, hc⟩ : B.InCC A m (B.Rw T.word.reverse (ap T.coefAdj F)) :=
      InCC_Rw (rdsp_lie_rev T) (hapcc T hT _)
    exact ⟨_, CCle_smul _ hc⟩

end

theorem spectral_polynomial_property : RDSPolyProp := by
  intro k r Wp Wq _ _ _ _ _ _ D o κ Θ hΘ hC
  obtain ⟨hS, hGl, -⟩ := CutMP.polynomial_decay_admissible k r Wp Wq o κ Θ hΘ
  have hG : CutMP.GlobCoef Θ (κ : ℝ) := hGl κ le_rfl
  have hκ : (0 : ℝ) ≤ κ := Nat.cast_nonneg κ
  refine ⟨hS _, hC, fun ε _ => ⟨κ, hκ, fun T hT => ?_⟩, fun F hF => ?_⟩
  · obtain ⟨-, -, hb⟩ := hG T hT
    obtain ⟨Cb, hCb⟩ := hb (B.opOrder Θ + 5)
    exact ⟨Cb, fun u v hu hv hl g hg _ => hCb u v hu hv hl g hg⟩
  obtain ⟨ε, hε, hFck, hFcc, hFs⟩ := hF
  have hO : IsOpen {g : B.Mat k r | Gf k r D.z D.z' g < ε} := isOpen_lt (Gf_cont _ _) continuous_const
  have hz : ∀ g ∈ B.GV k r, g ∈ {g : B.Mat k r | Gf k r D.z D.z' g < ε} → F g = 0 := by
    intro g hg hgO
    by_contra hne
    have := hFs g hg hne
    exact absurd hgO (not_lt.2 this)
  refine ⟨⟨ε, hε, ?_, ?_, ?_⟩, ⟨ε, hε, ?_, ?_, ?_⟩⟩
  · exact (CutMP.class_lower_decay_holds k r Wp Wq Θ κ 0 hκ hG F hFck (fun m => hFcc _ m)).1
  · intro A' m'
    have h := (CutMP.class_lower_decay_holds k r Wp Wq Θ κ (A' + κ) hκ hG F hFck (fun m => hFcc _ m)).2 m'
    rwa [add_sub_cancel_right] at h
  · intro g hg hne
    by_contra hlt
    exact hne (rdsp_opApply_vanish Θ hO hz g hg (not_le.1 hlt))
  · exact (rdsp_opAdj_cc Θ κ hG F hFck 0 (fun m => hFcc _ m)).1
  · intro A' m'
    exact (rdsp_opAdj_cc Θ κ hG F hFck A' (fun m => hFcc _ m)).2 m'
  · intro g hg hne
    by_contra hlt
    exact hne (rdsp_opAdj_vanish Θ hO hz g hg (not_le.1 hlt))

end Formalism.FourierDecayAlt.P.CutSE
end
end
