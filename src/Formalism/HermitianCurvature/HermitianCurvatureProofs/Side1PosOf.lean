module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Side0PosOf

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.Side1PosOf
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBQ

theorem side1Pos_of (hC : CutOffStep) (hE : CutOffExists) (h0 : CutHB.Side0Pos) (hW : PartialBesselProperness.PbWords)
    (hPr : PBQ.ProperDomP) : CutHB.Side1Pos := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh γ hj1 hF hw hγ hΩ t ht e
  have ht0 : t ≠ 0 := (ht.1 (1, t) (List.mem_append_right _ (List.mem_singleton_self _))).2
  obtain ⟨Fc, hFc, hag⟩ := hE Wp Wq P p F j hj w h hh hF hw t ht e
  rw [hC Wp Wq P p F j hj w h hh γ hF hw hγ hΩ t ht e Fc hFc hag]
  rw [h0 Wp Wq P p Fc j hj [] h hh γ hj1 hFc ⟨fun a => a.elim0, fun a => a.elim0⟩ hγ hΩ (fun a => a.elim0) t ht0]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  show ellH h v (CutHB.phf p Fc j hj [] h hh.2 γ v (fun a => a.elim0) t) = ellH h v _
  congr 1
  have hpt := CutHB.pts Wp Wq P p j hj h hh γ hγ hΩ v
  have hyD := hpt.2 t ht0
  have hyG := x0_GV hj hpt.1 ht0 hγ

  obtain ⟨R, hR⟩ := hF.2.1
  set Cs : Set (B.Mat P.k P.r) := {g | B.gN g ≤ R} with hCs
  have hCc : IsCompact Cs := Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le P.k P.r R
  have e' : j + (P.r - j) = P.r := by omega
  have hz : p.T.base.z = D.castV e' (liftVec P.k j (P.r - j) (p.T.bs j).z) := (p.T.z_lev j (by omega)).symm
  have hPW := hW P.k j (P.r - j) P.r Wp Wq (p.T.bs j) p.T.base e' hz (j + 1) hj F Cs (fun g hg _ => hF.1 g hg) hCc
    (fun g hg hgC => by
      by_contra hne
      exact hgC (hR g hg hne))
    (domP P.k P.r j p.T.base.z p.T.base.z') (isOpen_domP _ _ _ _ _)
    (fun g hg => hg.1 ⟨j + 1, by omega⟩ (show j ≤ j + 1 by omega) (show j + 1 ≤ P.r by omega))
    (hPr Wp Wq P p j (by omega) Cs hCc) w e _ hyD hyG
  show pbT p j (by omega) Fc (x0 P.k P.r j hj (zxH h j hh.2 v) t γ) =
    D.uwG P.k P.r p.T.base.z p.T.base.z' (pbT p j (by omega) F) (j + 1) hj w e (x0 P.k P.r j hj (zxH h j hh.2 v) t γ)
  unfold pbT
  rw [hPW]
  have hDv : Dmin P.k P.r p.T.base.z p.T.base.z' (x0 P.k P.r j hj (zxH h j hh.2 v) t γ) ⟨j + 1, by omega⟩ = aVal h t := by
    rw [(CutHL.leading_minors_at_base_point P.k P.r j hj p.T.base.z p.T.base.z' (zxH h j hh.2 v) t γ hpt.1 ht0 hγ).2, zxH_det h j hh v]
    rfl
  exact pbT_agree P p j hj (aVal h t) Fc _ (fun g _ hg => hag g hg) _ hyG hDv

end Formalism.FourierDecayAlt.P.LevelPointCoordinates
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothTruncationInduction
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHBCutOff
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.PBQ

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def CutOffStep : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j)
    (γ : B.Mat P.k (P.r - (j + 1))),
    γ ∈ B.GV P.k (P.r - (j + 1)) →
    γ ∈ Q.OmPlus P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' →
    ∀ (t : ℂ) (ht : D.IsLocPt (h ++ [(1, t)]) (j + 1)) (e : Wd.Ix (Fin w.length))
      (Fc : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base Fc →
      (∀ g, Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩ = (U.hMat (D.ptPerm h) (D.ptDiag h)).det * t →
        Fc g = D.uwG P.k P.r p.T.base.z p.T.base.z' F (j + 1) hj w e g) →
      B.JF (p.T.bs (j + 1)) (KB.slv p.T F (j + 1) hj w (h ++ [(1, t)]) ht.2 e) γ =
        B.JF (p.T.bs j) (KB.slv p.T Fc j (by omega) [] h hh.2 (fun a => a.elim0)) (mLev P j hj t γ)

def CutOffExists : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j),
    KB.CptCoef p.T.base F →
    ∀ (t : ℂ) (ht : D.IsLocPt (h ++ [(1, t)]) (j + 1)) (e : Wd.Ix (Fin w.length)),
      ∃ Fc : B.Mat P.k P.r → (Wq →L[ℂ] Wp), KB.CptCoef p.T.base Fc ∧
        ∀ g, Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩ = (U.hMat (D.ptPerm h) (D.ptDiag h)).det * t →
          Fc g = D.uwG P.k P.r p.T.base.z p.T.base.z' F (j + 1) hj w e g

section proofs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem det_hMat_app (h : C.LPt) (t : ℂ) :
    (U.hMat (D.ptPerm (h ++ [(1, t)])) (D.ptDiag (h ++ [(1, t)]))).det =
      (U.hMat (D.ptPerm h) (D.ptDiag h)).det * t := by
  rw [Formalism.FourierDecayAlt.P.PBI.det_hMat_pt, Formalism.FourierDecayAlt.P.PBI.det_hMat_pt h]
  have hsz : D.ptSize (h ++ [(1, t)]) = D.ptSize h + 1 := by
    simp [D.ptSize]
  rw [hsz, (Formalism.FourierDecayAlt.P.PBD.det_ptMatN_app t h (D.ptSize h) rfl).1, mul_comm]

theorem uwG_zero_of_G {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (ε : ℝ)
    (hε : ∀ g ∈ B.GV k r, F g ≠ 0 → ε ≤ Gf k r z z' g) (i : ℕ) (hi : i ≤ r) :
    ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)), ∀ g ∈ B.GV k r,
      D.uwG k r z z' F i hi w e g ≠ 0 → ε ≤ Gf k r z z' g
  | [], _, g, hg, hne => hε g hg hne
  | l :: w, e, g, hg, hne => by
    by_contra hlt
    push Not at hlt
    apply hne
    show D.vLet k r z z' i hi l (e 0) (D.uwG k r z z' F i hi w fun a => e a.succ) g = 0
    refine Formalism.FourierDecayAlt.P.PBG.vLet_zero_near z z' i hi l (e 0) _ (V := {x | Gf k r z z' x < ε})
      (isOpen_lt (Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.gf_cont k r z z') continuous_const) (fun x hx hxG => ?_) g hlt hg
    by_contra h0
    exact absurd (uwG_zero_of_G z z' F ε hε i hi w _ x hxG h0) (not_le.2 hx)

def cutW {P : M.Par} (Bs : B.RealPlaceData P.k P.r Wp Wq) (χ : ℂ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (i : ℕ)
    (hi : i ≤ P.r) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) : B.Mat P.k P.r → (Wq →L[ℂ] Wp) :=
  fun g => χ (Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩) • D.uwG P.k P.r Bs.z Bs.z' F i hi w e g

theorem cutW_exists {P : M.Par} (Bs : B.RealPlaceData P.k P.r Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hF : KB.CptCoef Bs F) (i : ℕ) (hi : i ≤ P.r) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) (a : ℂ)
    (ha : a ≠ 0) :
    ∃ Fc : B.Mat P.k P.r → (Wq →L[ℂ] Wp), KB.CptCoef Bs Fc ∧
      ∀ g, Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩ = a → Fc g = D.uwG P.k P.r Bs.z Bs.z' F i hi w e g := by
  obtain ⟨hck, ⟨R, hR⟩, ε, hε, hεG⟩ := hF
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha
  let b : ContDiffBump a := ⟨‖a‖ / 4, ‖a‖ / 2, by positivity, by linarith⟩
  have hD : ContDiff ℝ (⊤ : ℕ∞) (fun g : B.Mat P.k P.r => Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩) :=
    Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin Bs.z Bs.z' _
  have hbD : ContDiff ℝ (⊤ : ℕ∞) (fun g : B.Mat P.k P.r => b (Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩)) :=
    b.contDiff.comp hD
  have hne : ∀ g, cutW Bs b F i hi w e g ≠ 0 → D.uwG P.k P.r Bs.z Bs.z' F i hi w e g ≠ 0 := by
    intro g hg h0
    apply hg
    simp [cutW, h0]
  refine ⟨cutW Bs b F i hi w e, ⟨?_, ⟨R, fun g hg h1 => Formalism.FourierDecayAlt.P.PBG.uwG_supp Bs.z Bs.z' F R hR i hi w e g hg
      (hne g h1)⟩, ε, hε, fun g hg h1 => uwG_zero_of_G Bs.z Bs.z' F ε hεG i hi w e g hg (hne g h1)⟩, ?_⟩
  · intro g₀ hg₀
    by_cases h0 : Dmin P.k P.r Bs.z Bs.z' g₀ ⟨i, by omega⟩ = 0
    · refine ⟨{g | ‖Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩‖ < ‖a‖ / 2}, fun _ => 0,
        isOpen_lt (continuous_norm.comp hD.continuous) continuous_const, by simp [h0]; positivity,
        contDiffOn_const, fun g hg _ => ?_⟩
      have hb0 : b (Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩) = 0 := by
        apply Function.notMem_support.1
        rw [b.support_eq, Metric.mem_ball, dist_eq_norm]
        intro hlt
        have h1 : ‖a‖ ≤ ‖Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩ - a‖ + ‖Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩‖ := by
          have := norm_sub_le (Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩) (Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩ - a)
          simp at this
          linarith
        have h2 : b.rOut = ‖a‖ / 2 := rfl
        have h3 : ‖Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩‖ < ‖a‖ / 2 := hg
        linarith
      simp [cutW, hb0]
    · obtain ⟨U, f', hU, hgU, hf', hE⟩ :=
        Formalism.FourierDecayAlt.P.PBG.uwG_mem Bs.z Bs.z' i hi hck w e g₀ h0 hg₀
      refine ⟨U, fun g => b (Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩) • f' g, hU, hgU,
        (hbD.contDiffOn.of_le le_rfl).smul hf', fun g hg hgG => ?_⟩
      simp only [cutW]
      rw [hE g hg hgG]
  · intro g hg
    simp only [cutW]
    rw [hg, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le), one_smul]

end proofs

theorem truncation_off_exists_formula : CutOffExists := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh hF t ht e
  have ht0 : t ≠ 0 := (ht.1 (1, t) (List.mem_append_right _ (List.mem_singleton_self _))).2
  have hH : (U.hMat (D.ptPerm h) (D.ptDiag h)).det ≠ 0 := by
    rw [Formalism.FourierDecayAlt.P.PBI.det_hMat_pt, hh.2]
    exact Formalism.FourierDecayAlt.P.PBI.det_ptMatN_ne h j hh
  exact cutW_exists p.T.base F hF (j + 1) hj w e _ (mul_ne_zero hH ht0)

theorem truncation_off_induction : CutOffStep := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh γ hγ hΩ t ht e Fc hFc hag
  have hs : KB.slv p.T F (j + 1) hj w (h ++ [(1, t)]) ht.2 e =
      KB.slv p.T Fc (j + 1) hj [] (h ++ [(1, t)]) ht.2 (fun a => a.elim0) := by
    unfold KB.slv
    congr 1
    apply Formalism.FourierDecayAlt.P.PBI.sliceAt_congr_Dr _ _ _ (by rw [ht.2]; exact hj)
    intro x hx
    symm
    show Fc x = _
    apply hag
    have e1 : (⟨j + 1, by omega⟩ : Fin (P.r + 2)) = ⟨D.ptSize (h ++ [(1, t)]), by rw [ht.2]; omega⟩ :=
      Fin.ext ht.2.symm
    rw [e1, hx, det_hMat_app]
  rw [hs, Formalism.FourierDecayAlt.P.slice_induction_level Wp Wq P p Fc j hj h t hh ht hFc γ hγ hΩ]
  rfl

end Formalism.FourierDecayAlt.P.CutHB
end
end

namespace Formalism.FourierDecayAlt.P

theorem smooth_truncation_induction : Formalism.FourierDecayAlt.P.LevelPointCoordinates.CutOffStep := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh γ _ _ hγ hΩ t ht e Fc hFc hag
  exact Formalism.FourierDecayAlt.P.CutHB.truncation_off_induction Wp Wq P p F j hj w h hh γ hγ hΩ t ht e Fc hFc hag

theorem smooth_truncation_exists : Formalism.FourierDecayAlt.P.LevelPointCoordinates.CutOffExists := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh hF _ t ht e
  exact Formalism.FourierDecayAlt.P.CutHB.truncation_off_exists_formula Wp Wq P p F j hj w h hh hF t ht e

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXSliceTop
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceTopZero
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutEXSl0

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem om_zero {k ρ : ℕ} (hρ : ρ = 0) (z z' : Fin (2 * ρ + k + 1) → ℂ) (γ : B.Mat k ρ) (hγ : γ ∈ B.GV k ρ)
    (hG : 0 < Q.GGl k ρ z z' γ) : γ ∈ JF.Om k ρ z z' := by
  subst hρ
  refine ⟨hγ, fun l hl => ?_, ?_⟩
  · have hl0 : l = (⟨0, by norm_num⟩ : Fin (0 + 2)) := Fin.ext (by simp only; omega)
    subst hl0
    unfold Dmin
    rw [Matrix.det_fin_zero]
    exact one_ne_zero
  · have e : Gf k 0 z z' γ = Q.GGl k 0 z z' γ := by
      unfold Gf Q.GGl Dmin
      rw [Matrix.det_fin_zero, Matrix.det_fin_one]
      simp only [Complex.normSq_one, mul_one]
      rfl
    rw [e]
    exact hG

theorem sliceTop_zero (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (hr : P.r = 0) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hG : CutEX.TopCls p.T.base G)
    (h : C.LPt) (hh : D.IsLocPt h P.r) (γ : B.Mat P.k (P.r - P.r)) (hγ : γ ∈ B.GV P.k (P.r - P.r))
    (hGG : 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ) :
    Integrable (fun v : PBQ.XH h => PBQ.ellH h v (CutEX.pbTop p G (PBQ.zxH h P.r hh.2 v) γ)) ∧
      B.JF (p.T.bs P.r) (D.castF (by rw [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h)) γ =
        ∫ v, PBQ.ellH h v (CutEX.pbTop p G (PBQ.zxH h P.r hh.2 v) γ) := by
  have hOm := om_zero (by omega : P.r - P.r = 0) _ _ γ hγ hGG
  rcases P with ⟨k, r, T, T', u, u'⟩
  dsimp only at hr
  subst hr
  have hnil : h = [] := by
    cases h with
    | nil => rfl
    | cons b t =>
      exfalso
      have h1 := (hh.1 b (List.mem_cons.2 (Or.inl rfl))).1
      have h2 := hh.2
      simp only [D.ptSize, List.map_cons, List.sum_cons] at h2
      omega
  subst hnil
  have hE : IsEmpty (U.LW (D.ptPerm ([] : C.LPt))) := ⟨fun q => Fin.elim0 (q.1.1 : Fin 0)⟩
  set x₀ : PBQ.XH ([] : C.LPt) := fun q => (hE.false q).elim with hx₀
  have hvol : (volume : Measure (PBQ.XH ([] : C.LPt))) = Measure.dirac x₀ := by
    rw [volume_pi, Measure.pi_of_empty (fun _ => volume) x₀]
  have hxe : ∀ v : PBQ.XH ([] : C.LPt), v = x₀ := fun v => funext fun q => (hE.false q).elim
  refine ⟨?_, ?_⟩
  · rw [hvol]
    refine (integrable_const (PBQ.ellH ([] : C.LPt) x₀ (CutEX.pbTop p G (PBQ.zxH [] _ hh.2 x₀) γ))).congr
      (Filter.Eventually.of_forall fun v => ?_)
    simp only [hxe v]
  · have hone : ∫ v, PBQ.ellH ([] : C.LPt) v (CutEX.pbTop p G (PBQ.zxH [] _ hh.2 v) γ) =
        CutEX.pbTop p G (PBQ.zxH [] _ hh.2 x₀) γ := by
      rw [hvol, integral_dirac]
      unfold PBQ.ellH
      have hF0 : IsEmpty (Fin (D.ptSize ([] : C.LPt))) := ⟨fun i => Fin.elim0 (i : Fin 0)⟩
      have hs : U.subS (LeftFubiniLemmas.lhOf (D.ptPerm ([] : C.LPt)) x₀) = 0 := by
        unfold U.subS
        exact Finset.sum_of_isEmpty _
      rw [hs]
      simp [Formalism.FourierDecayAlt.G.psi]
    rw [hone]
    have e3 : D.castF (by simp) (D.sliceAt k 0 p.T.base.z p.T.base.z' G []) = G := by
      funext y
      simp only [D.castF]
      refine (Formalism.FourierDecayAlt.P.Dx1.SN.sliceAt_nil k 0 _ _ p.T.base.z_mem p.T.base.z'_mem G _).trans ?_
      exact congrArg G (Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl y)
    have hCpt : KB.CptCoef (p.T.bs 0) G := hG.1
    have hL := SliceIntegralLemmas.jf_left (p.T.bs 0) G (Formalism.FourierDecayAlt.P.PBH.asm_contOn_of_ckOn hCpt.1) γ hγ
      (Formalism.FourierDecayAlt.P.PBH.rhs_int (p.T.bs 0) G hCpt γ hOm)
    have hx : CutEX.xT k 0 (PBQ.zxH [] _ hh.2 x₀) γ = γ := by
      unfold CutEX.xT U.mMap
      rw [SliceIntegralLemmas.block_three_zero_size_eq]
      exact Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl γ
    rw [e3, hL]
    unfold CutEX.pbTop PBQ.pbT
    rw [hx, SliceIntegralLemmas.pbF_zero]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    beta_reduce
    rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
    rfl

end Formalism.FourierDecayAlt.P.CutEXSl0
end
end

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutEXSlice

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.LeftFubiniLemmas

section gen

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem slice_integral_level_reduction (e : p + ρ = n) (hp : 1 ≤ p) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq)
    (hz : D.castV e (liftVec k p ρ Bj.z) = B0.z) (hz' : D.castV e (liftVec k p ρ Bj.z') = B0.z')
    (hπ' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (D.castM e (ιLev k p ρ y)))
    (hW' : Bj.μW' Set.univ = 1) (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ e))
    (hNj : Bj.μN = D.muN k ρ) (hN0 : B0.μN = D.muN k n)
    (g : B.Mat k ρ) (hg : g ∈ JF.Om k ρ Bj.z Bj.z') (H : B.Mat k n → (Wq →L[ℂ] Wp))
    (hHc : ContinuousOn H {x | x ∈ B.GV k n ∧ Dmin k n B0.z B0.z' x ⟨p, by omega⟩ ≠ 0}) (R : ℝ)
    (hR : ∀ x ∈ B.GV k n, H x ≠ 0 → B.gN x ≤ R) :
    Integrable (fun v : U.LW σ → ℂ =>
        SliceIntegralLemmas.psiH σ v • PBQ.pbF Bj B0 e H (D.castM e (U.mMap k p ρ (lhOf σ v * U.hMat σ d) g))) volume ∧
    B.JF Bj (U.PhiFun (s := 0) k ρ σ d (D.castV e.symm B0.z) (D.castV e.symm B0.z') (D.castF e H)
        (fun a => a.elim0)) g =
      ∫ v : U.LW σ → ℂ, SliceIntegralLemmas.psiH σ v • PBQ.pbF Bj B0 e H (D.castM e (U.mMap k p ρ (lhOf σ v * U.hMat σ d) g)) := by
  subst e
  have hz1 : B0.z = liftVec k p ρ Bj.z := by rw [← hz, JCTx5.castV_rfl]
  have hz1' : B0.z' = liftVec k p ρ Bj.z' := by rw [← hz', JCTx5.castV_rfl]
  have hπ1 : ∀ y, Bj.π' y = B0.π' (U.embG k p ρ y) := fun y => by
    rw [hπ' y, Dx2.MN.castM_rfl, Dx2.Tower.lev_eq_embG]
  have hHc' : ContinuousOn H {x | x ∈ B.GV k (p + ρ) ∧ U.DjU k p ρ x ≠ 0} := by
    refine hHc.mono ?_
    intro x hx
    refine ⟨hx.1, ?_⟩
    rw [Ux3.zhDmin]
    exact hx.2
  obtain ⟨hi, heq⟩ := SliceIntegralLemmas.jfSliceInt hp σ d hd Bj B0 hz1' hπ1 hW' hW0' hNj hN0 g hg H hHc' R hR
  refine ⟨?_, ?_⟩
  · simpa only [Dx2.MN.castM_rfl] using hi
  · rw [JCTx5.castV_rfl, JCTx5.castV_rfl, hz1, hz1']
    simp only [Dx2.MN.castM_rfl]
    exact heq

end gen

section top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem slice_gen (P : M.Par) (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hG : B.CkOn ⊤ (B.GV P.k P.r) G) (R : ℝ) (hR : ∀ x ∈ B.GV P.k P.r, G x ≠ 0 → B.gN x ≤ R)
    (h : C.LPt) (j : ℕ) (hjr : j ≤ P.r) (hh : D.IsLocPt h j) (hj1 : 1 ≤ j) (γ : B.Mat P.k (P.r - j))
    (hOm : γ ∈ JF.Om P.k (P.r - j) (p.T.bs j).z (p.T.bs j).z') :
    Integrable (fun v : PBQ.XH h => PBQ.ellH h v (PBQ.pbF (p.T.bs j) p.T.base (by omega : j + (P.r - j) = P.r) G
        (D.castM (by omega : j + (P.r - j) = P.r) (U.mMap P.k j (P.r - j) (PBQ.zxH h j hh.2 v) γ)))) ∧
    B.JF (p.T.bs j) (D.castF (by rw [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h)) γ =
      ∫ v, PBQ.ellH h v (PBQ.pbF (p.T.bs j) p.T.base (by omega : j + (P.r - j) = P.r) G
        (D.castM (by omega : j + (P.r - j) = P.r) (U.mMap P.k j (P.r - j) (PBQ.zxH h j hh.2 v) γ))) := by
  obtain ⟨hh1, rfl⟩ := hh
  have e : D.ptSize h + (P.r - D.ptSize h) = P.r := by omega
  have hzj := p.T.z_lev (D.ptSize h) hjr
  have hzj' := p.T.z'_lev (D.ptSize h) hjr
  have hπj : ∀ y, (p.T.bs (D.ptSize h)).π' y = p.T.base.π' (D.castM e (ιLev P.k _ _ y)) :=
    fun y => p.T.π'_lev _ hjr y
  obtain ⟨hWj, hW'j, hNj⟩ := p.hT (D.ptSize h) hjr
  obtain ⟨hW0, hW'0, hN0⟩ := p.hT 0 (Nat.zero_le _)
  have hW0' : p.T.base.μW' = (p.T.bs (D.ptSize h)).μW'.map (PBM.levMt (D.ptSize h) (P.r - D.ptSize h) e) :=
    PBM.haar_lev _ _ e _ _ hzj' _ _ p.T.base.haarW' (p.T.bs _).haarW' hW'0 hW'j
  have hGc : ContinuousOn G {x | x ∈ B.GV P.k P.r ∧
      Dmin P.k P.r p.T.base.z p.T.base.z' x ⟨D.ptSize h, by omega⟩ ≠ 0} :=
    (PBE.ckOn_continuousOn' subset_rfl hG).mono fun x hx => hx.1
  obtain ⟨H1i, H1e⟩ := slice_integral_level_reduction e hj1 (D.ptPerm h) (D.ptDiag h) (CutHB.ptDiag_ne ⟨hh1, rfl⟩)
    (p.T.bs (D.ptSize h)) p.T.base hzj hzj' hπj hW'j hW0' hNj hN0 γ hOm G hGc R hR
  have hcf : ∀ (e' : P.r - D.ptSize h = P.r - D.ptSize h) (F : B.Mat P.k (P.r - D.ptSize h) → (Wq →L[ℂ] Wp)),
      D.castF e' F = F := fun e' F => by
    funext x
    simp only [D.castF, Dx2.MN.castM_rfl]
  refine ⟨?_, ?_⟩
  · simp only [PBQ.ellH, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
    simp only [SliceIntegralLemmas.psiH] at H1i
    exact H1i
  · rw [hcf, D.sliceAt, dite_eq_left hjr]
    simp only [PBQ.ellH, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
    exact H1e

theorem om_zero {k ρ : ℕ} (hρ : ρ = 0) (z z' : Fin (2 * ρ + k + 1) → ℂ) (γ : B.Mat k ρ) (hγ : γ ∈ B.GV k ρ)
    (hG : 0 < Q.GGl k ρ z z' γ) : γ ∈ JF.Om k ρ z z' := by
  subst hρ
  have h0 : ∀ (hl : 0 < 0 + 2), Dmin k 0 z z' γ ⟨0, hl⟩ = 1 := by
    intro hl
    simp [Dmin]
  have h1 : Dmin k 0 z z' γ (Fin.last (0 + 1)) = Q.zetaL k 0 z z' (Fin.last 0) γ := by
    rw [PBI.zetaL_eq_zhat]
    simp [Dmin, Matrix.det_unique]
  refine ⟨hγ, ?_, ?_⟩
  · intro l hl
    have hl0 : l = ⟨0, by omega⟩ := Fin.ext (by simpa using hl)
    rw [hl0, h0]
    exact one_ne_zero
  · unfold Gf
    rw [h1, h0]
    simpa [Q.GGl] using hG

end top

end Formalism.FourierDecayAlt.P.CutEXSlice

namespace Formalism.FourierDecayAlt.P.CutEXSlice

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem sliceTop_pos (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (hr : 1 ≤ P.r) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hG : CutEX.TopCls p.T.base G)
    (h : C.LPt) (hh : D.IsLocPt h P.r) (γ : B.Mat P.k (P.r - P.r)) (hγ : γ ∈ B.GV P.k (P.r - P.r))
    (hGG : 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ) :
    Integrable (fun v : PBQ.XH h => PBQ.ellH h v (CutEX.pbTop p G (PBQ.zxH h P.r hh.2 v) γ)) ∧
      B.JF (p.T.bs P.r) (D.castF (by rw [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h)) γ =
        ∫ v, PBQ.ellH h v (CutEX.pbTop p G (PBQ.zxH h P.r hh.2 v) γ) := by
  have hOm : γ ∈ JF.Om P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' :=
    om_zero (Nat.sub_self _) _ _ γ hγ hGG
  obtain ⟨R, hR⟩ := hG.1.2.1
  exact slice_gen P p G hG.1.1 R hR h P.r le_rfl hh hr γ hOm

end Formalism.FourierDecayAlt.P.CutEXSlice

namespace Formalism.FourierDecayAlt.P

theorem slice_top_exhaustion : CutEX.SliceTop := by
  intro Wp Wq _ _ _ _ _ _ P p G hG h hh γ hγ hGG
  rcases Nat.eq_zero_or_pos P.r with h0 | h1
  · exact CutEXSl0.sliceTop_zero Wp Wq P p h0 G hG h hh γ hγ hGG
  · exact CutEXSlice.sliceTop_pos Wp Wq P p h1 G hG h hh γ hγ hGG

end Formalism.FourierDecayAlt.P
end
end
