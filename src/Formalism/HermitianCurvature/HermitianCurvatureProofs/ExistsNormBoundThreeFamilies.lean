module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelTransport
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftFubiniNormalizedTower
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BuiltBoundsCompactOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKap
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomAtGq
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerMatrixBlockThreeMul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftLocalBuiltPlaces

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsNormBoundThreeFamilies
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt NumberField MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBD
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

def FormPosCpt : Prop :=
  P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter), KB.CutWord P p.l0 w → ∀ x, (∀ e, KB.CptCoef (p.T.bs j) (x e)) →
    0 ≤ p.form j hj w x x

section cv

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def CV {S : Type} (Bs : B.RealPlaceData k ρ Wp Wq) (x : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ e, KB.CptCoef Bs (x e)

variable {S : Type} {Bs : B.RealPlaceData k ρ Wp Wq}

theorem cpt_zero : KB.CptCoef Bs (fun _ : B.Mat k ρ => (0 : Wq →L[ℂ] Wp)) :=
  ⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_zero, ⟨0, fun g _ h => (h rfl).elim⟩, ⟨1, one_pos, fun g _ h => (h rfl).elim⟩⟩

theorem cpt_add {F G : B.Mat k ρ → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef Bs F) (hG : KB.CptCoef Bs G) :
    KB.CptCoef Bs (fun g => F g + G g) := by
  obtain ⟨h1, ⟨R, hR⟩, ⟨ε, hε, hGε⟩⟩ := hF
  obtain ⟨h1', ⟨R', hR'⟩, ⟨ε', hε', hGε'⟩⟩ := hG
  refine ⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add h1 h1', ⟨max R R', fun g hg hne => ?_⟩, ⟨min ε ε', lt_min hε hε', fun g hg hne => ?_⟩⟩
  · by_cases h0 : F g = 0
    · exact (hR' g hg (by simpa [h0] using hne)).trans (le_max_right _ _)
    · exact (hR g hg h0).trans (le_max_left _ _)
  · by_cases h0 : F g = 0
    · exact (min_le_right _ _).trans (hGε' g hg (by simpa [h0] using hne))
    · exact (min_le_left _ _).trans (hGε g hg h0)

theorem cpt_smul (c : ℂ) {F : B.Mat k ρ → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef Bs F) :
    KB.CptCoef Bs (fun g => c • F g) := by
  obtain ⟨h1, ⟨R, hR⟩, ⟨ε, hε, hGε⟩⟩ := hF
  refine ⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_smul c h1, ⟨R, fun g hg hne => hR g hg fun h0 => hne (by simp [h0])⟩,
    ⟨ε, hε, fun g hg hne => hGε g hg fun h0 => hne (by simp [h0])⟩⟩

theorem cv_zero : CV (S := S) Bs 0 := fun _ => cpt_zero

theorem cv_add {x y : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)} (hx : CV Bs x) (hy : CV Bs y) : CV Bs (x + y) :=
  fun e => cpt_add (hx e) (hy e)

theorem cv_smul (c : ℂ) {x : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)} (hx : CV Bs x) : CV Bs (c • x) :=
  fun e => cpt_smul c (hx e)

theorem nv_of_cv [Fintype (Wd.Ix S)] {x : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)} (hx : CV Bs x) :
    ∃ ε, 0 < ε ∧ NV Bs ε x :=
  common_eps (fun e ε => JC.NiceCoef Bs ε (x e)) (fun e ε ε' h _ h' => nice_mono h h') fun e => nice_of_cpt (hx e)

theorem exists_norm_bound_three_families [Fintype (Wd.Ix S)] {S' S'' : Type} [Fintype (Wd.Ix S')] [Fintype (Wd.Ix S'')]
    {x : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)} {y : Wd.Ix S' → B.Mat k ρ → (Wq →L[ℂ] Wp)}
    {z : Wd.Ix S'' → B.Mat k ρ → (Wq →L[ℂ] Wp)} (hx : CV Bs x) (hy : CV Bs y) (hz : CV Bs z) :
    ∃ ε, 0 < ε ∧ NV Bs ε x ∧ NV Bs ε y ∧ NV Bs ε z := by
  obtain ⟨a, ha, hxa⟩ := nv_of_cv hx
  obtain ⟨b, hb, hyb⟩ := nv_of_cv hy
  obtain ⟨c, hc, hzc⟩ := nv_of_cv hz
  refine ⟨min a (min b c), lt_min ha (lt_min hb hc), nv_mono hxa (min_le_left _ _),
    nv_mono hyb ((min_le_right _ _).trans (min_le_left _ _)), nv_mono hzc ((min_le_right _ _).trans (min_le_right _ _))⟩

end cv

section formsC

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
  (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter)

theorem form_slC (x₁ x₂ y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (h₁ : CV (p.T.bs j) x₁) (h₂ : CV (p.T.bs j) x₂) (hy : CV (p.T.bs j) y) :
    p.form j hj w (x₁ + c • x₂) y = p.form j hj w x₁ y + c * p.form j hj w x₂ y := by
  obtain ⟨ε, -, a, b, d⟩ := exists_norm_bound_three_families h₁ h₂ hy
  exact form_sl p j hj w x₁ x₂ y c a b d

theorem form_srC (x y₁ y₂ : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : CV (p.T.bs j) x) (h₁ : CV (p.T.bs j) y₁) (h₂ : CV (p.T.bs j) y₂) :
    p.form j hj w x (y₁ + c • y₂) = p.form j hj w x y₁ + conj c * p.form j hj w x y₂ := by
  obtain ⟨ε, -, a, b, d⟩ := exists_norm_bound_three_families hx h₁ h₂
  exact form_sr p j hj w x y₁ y₂ c a b d

variable (ys : List ℝ)

theorem pj_slC (x₁ x₂ : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (y : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (h₁ : CV (p.T.bs j) x₁) (h₂ : CV (p.T.bs j) x₂) (hy : CV (p.T.bs j) y) :
    KB.pairJ (p.form j hj w) ys (x₁ + c • x₂) y =
      KB.pairJ (p.form j hj w) ys x₁ y + c * KB.pairJ (p.form j hj w) ys x₂ y := by
  obtain ⟨ε, -, a, b, d⟩ := exists_norm_bound_three_families h₁ h₂ hy
  exact pj_sl p j hj w ys x₁ x₂ y c a b d

theorem pj_srC (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (y₁ y₂ : Wd.Ix (Fin (KB.minusW ys w).length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : CV (p.T.bs j) x) (h₁ : CV (p.T.bs j) y₁) (h₂ : CV (p.T.bs j) y₂) :
    KB.pairJ (p.form j hj w) ys x (y₁ + c • y₂) =
      KB.pairJ (p.form j hj w) ys x y₁ + conj c * KB.pairJ (p.form j hj w) ys x y₂ := by
  obtain ⟨ε, -, a, b, d⟩ := exists_norm_bound_three_families hx h₁ h₂
  exact pj_sr p j hj w ys x y₁ y₂ c a b d

end formsC

section hatC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem hatB_setC_C (hPSC : StandardPairingDecay.PStdC) {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq}
    {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε))
    (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ) (hj : j ≤ S.G.r) (w : List C.Letter)
    (hw : KB.CutWord (D.parOf S v) (S.l + 1) w) (l : ℂ) (h h' : C.LPt) (hh : D.IsLocPt h j)
    (hh' : D.IsLocPt h' j) :
    KB.hatB (setC S p F) v ε (j + 1) 1 w l h h' =
      ((dW S v j w h h' : ℝ) : ℂ) * (p v).form j hj w
        (KB.waveG ((p v).T.bs j) (sW S j l) w
          (KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2)))
        (KB.slv (p v).T (F v ε) j hj w (stdS S h') ((stdS_size S h').trans hh'.2)) := by
  have hgpos := g_pos_of_built hB
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, hInD, -, -, -⟩ := hv v
  have hH : D.IsLocPt (stdS S h) j := (isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh
  have hH' : D.IsLocPt (stdS S h') j := (isLocPt_toStd_iff _ _ hgpos h' 1 j).2 hh'
  obtain ⟨φ, -, -, hφ, hφint⟩ := hPSC (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (F v ε) j hj w
    (stdS S h) (stdS S h') hH hH' Cb (by rw [hl0]; exact hInD) (hF v ε hε) (by rw [hl0]; exact hw)
  have hlam_pos := lamS_pos S hgpos j
  obtain ⟨g, hgdef⟩ : ∃ g : ℂ → ℂ, g = fun c' => P5.fsv (sW S j l) c' * φ c' := ⟨_, rfl⟩
  have hae : (fun c : ℂ => KB.gN (setC S p F) v ε (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)]) *
      KB.psiL (setC S p F) l c) =ᵐ[volume]
      fun c => ((Kc S v j w h h' : ℝ) : ℂ) * g (lamS S j • c) := by
    filter_upwards [ae_ne_zero_complex] with c hc
    have hlc : (lamS S j : ℂ) * c ≠ 0 := mul_ne_zero (by exact_mod_cast hlam_pos.ne') hc
    simp only [hgdef, Complex.real_smul]
    rw [gN_setC_app hB F v ε j hj w h h' hh.2 hh'.2 c hc, hφ _ hlc]
    have : KB.psiL (setC S p F) l c = KB.psiL S l c := rfl
    rw [this, psiL_eq_fsv S hgpos j l c]
    ring
  have hint : KB.hatB (setC S p F) v ε (j + 1) 1 w l h h' = ((KB.dlB S (j + 1) 1 : ℝ) : ℂ)⁻¹ *
      ∫ c, ((Kc S v j w h h' : ℝ) : ℂ) * g (lamS S j • c) := by
    unfold KB.hatB
    rw [show j + 1 + 1 - 1 = j + 1 by omega, integral_congr_ae hae]
    rfl
  have hcs : ∫ c, ((Kc S v j w h h' : ℝ) : ℂ) * g (lamS S j • c) =
      ((Kc S v j w h h' : ℝ) : ℂ) * (((|(lamS S j ^ 2)⁻¹| : ℝ) : ℂ) * ∫ c, P5.fsv (sW S j l) c * φ c) := by
    rw [integral_const_mul, Measure.integral_comp_smul, Complex.finrank_real_complex, Complex.real_smul, hgdef]
  have gen : ∀ X : ℂ, ((KB.dlB S (j + 1) 1 : ℝ) : ℂ)⁻¹ *
      (((Kc S v j w h h' : ℝ) : ℂ) * (((|(lamS S j ^ 2)⁻¹| : ℝ) : ℂ) * X)) = ((dW S v j w h h' : ℝ) : ℂ) * X := by
    intro X
    rw [← kc_scal hB v j hj w h h']
    push_cast
    ring
  exact (hint.trans ((congrArg (fun Z => ((KB.dlB S (j + 1) 1 : ℝ) : ℂ)⁻¹ * Z) hcs).trans (gen _))).trans
    (congrArg (fun X => ((dW S v j w h h' : ℝ) : ℂ) * X) (hφint (sW S j l)))

end hatC

section hatUC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem hatB_uB_C (hPSC : StandardPairingDecay.PStdC) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (hw : KB.CutWord (D.parOf S v) (S.l + 1) w) (l : ℂ) (h h' : C.LPt)
    (hsz : D.ptSize h = j) (hsz' : D.ptSize h' = j) :
    KB.hatB (setC S p F) v ε (j + 1) 1 w l h h' =
      ((1 / (ΓS S j * S.sizeAt v w) : ℝ) : ℂ) * (p v).form j hj w
        (KB.waveG ((p v).T.bs j) (sW S j l) w (uB S p F v ε j hj w h)) (uB S p F v ε j hj w h') := by
  have hgpos := g_pos_of_built hB
  obtain ⟨ε1, hε1, hx, hx'⟩ := nv_pair (uB_nv hB F hF v ε hε j hj w h) (uB_nv hB F hF v ε hε j hj w h')
  have hwx := PBFV.waveG_nice ((p v).T.bs j) ε1 (sW S j l) w _ hx
  by_cases hloc : D.IsLocPt h j ∧ D.IsLocPt h' j
  · obtain ⟨hh, hh'⟩ := hloc
    have hH : D.IsLocPt (stdS S h) j := (PBD.isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh
    have hH' : D.IsLocPt (stdS S h') j := (PBD.isLocPt_toStd_iff _ _ hgpos h' 1 j).2 hh'
    obtain ⟨ε2, hε2, hs, hs'⟩ := nv_pair (slv_nv (p v) (hF v ε hε) j hj w (stdS S h) hH)
      (slv_nv (p v) (hF v ε hε) j hj w (stdS S h') hH')
    rw [hatB_setC_C hPSC hB F hF v ε hε j hj w hw l h h' hh hh']
    have e1 : uB S p F v ε j hj w h = (((√(nnS S h) / bS S h : ℝ) : ℂ)) •
        KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2) := by
      unfold uB; rw [dite_eq_left hh]
    have e2 : uB S p F v ε j hj w h' = (((√(nnS S h') / bS S h' : ℝ) : ℂ)) •
        KB.slv (p v).T (F v ε) j hj w (stdS S h') ((stdS_size S h').trans hh'.2) := by
      unfold uB; rw [dite_eq_left hh']
    have hws := PBFV.waveG_nice ((p v).T.bs j) ε2 (sW S j l) w _ hs
    have ew : KB.waveG ((p v).T.bs j) (sW S j l) w ((((√(nnS S h) / bS S h : ℝ) : ℂ)) •
        KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2)) =
        (((√(nnS S h) / bS S h : ℝ) : ℂ)) • KB.waveG ((p v).T.bs j) (sW S j l) w
          (KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2)) := by
      have := PBG.waveG_add_smul ((p v).T.bs j) (sW S j l) w 0
        (KB.slv (p v).T (F v ε) j hj w (stdS S h) ((stdS_size S h).trans hh.2)) (((√(nnS S h) / bS S h : ℝ) : ℂ))
      rw [zero_add, PBG.waveG_zero, zero_add] at this
      exact this
    rw [e1, e2, ew, form_smul_l (p v) j hj w _ _ _ hws (nv_smul _ hs'), form_smul_r (p v) j hj w _ _ _ hws hs',
      Complex.conj_ofReal, dW_split]
    push_cast
    ring
  · rw [hatB_setC_zero hB F v ε j w l h h' hsz hsz' hloc]
    have : uB S p F v ε j hj w h = 0 ∨ uB S p F v ε j hj w h' = 0 := by
      by_cases hh : D.IsLocPt h j
      · right; unfold uB; rw [dite_eq_right (fun hh' => hloc ⟨hh, hh'⟩)]
      · left; unfold uB; rw [dite_eq_right hh]
    rcases this with h0 | h0
    · rw [h0, PBG.waveG_zero, form_zero_l (p v) j hj w _ hx', mul_zero]
    · rw [h0, form_zero_r (p v) j hj w _ hwx, mul_zero]

theorem uB_cv (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (h : C.LPt) : CV ((p v).T.bs j) (uB S p F v ε j hj w h) := by
  have hgpos := g_pos_of_built hB
  by_cases hh : D.IsLocPt h j
  · rw [uB_pos S p F v ε j hj w h hh]
    have hH : D.IsLocPt (stdS S h) j := (PBD.isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh
    exact cv_smul _ fun e => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient _ _ (D.parOf S v) (p v) (F v ε) j hj w (stdS S h) hH
      (hF v ε hε) e
  · rw [uB_neg S p F v ε j hj w h hh]; exact cv_zero

theorem uY_cv (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (Y : Finset C.LPt) (h : C.LPt) :
    CV ((p v).T.bs j) (uY S p F v ε j hj w Y h) := by
  unfold uY
  split_ifs
  · exact uB_cv hB F hF v ε hε j hj w h
  · exact cv_zero

end hatUC

end

end Formalism.FourierDecayAlt.P.PBL
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralBoundOfParts
namespace Formalism.FourierDecayAlt.P.PBASM

open Formalism.FourierDecayAlt NumberField MeasureTheory Filter Topology Formalism.QuantumDeterminants
open scoped ComplexConjugate

noncomputable section

open Classical

theorem uInv_zero_eq_self {X : Type} [AddCommGroup X] [Module ℂ X] :
    ∀ (w : List C.Letter) (x : Wd.Ix (Fin w.length) → X), KB.uInv (0 : ℂ) w x = x
  | [], _ => rfl
  | l :: w, x => by
    funext e
    have he : (Fin.cons (e 0) (fun a => e a.succ) : Wd.Ix (Fin (w.length + 1))) = e := Fin.cons_self_tail e
    unfold KB.uInv
    simp only [map_zero, ite_self, zero_smul, add_zero, uInv_zero_eq_self w]
    by_cases h0 : e 0 = 0
    · rw [ite_eq_left h0]
      conv_rhs => rw [← he]
      rw [h0]
    · have h1 : e 0 = 1 := by
        rcases Fin.exists_fin_two.1 ⟨e 0, rfl⟩ with h | h
        · exact absurd h h0
        · exact h
      rw [ite_eq_right h0]
      conv_rhs => rw [← he]
      rw [h1]

theorem waveG_zero_eq_self {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k r → (Wq →L[ℂ] Wp)) : KB.waveG Bs 0 w x = x := by
  funext e g
  simp only [KB.waveG, uInv_zero_eq_self, P5.fsv, zero_mul, map_zero, sub_zero, Complex.exp_zero, one_smul]

theorem psiL_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
    [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (c : ℂ) : KB.psiL S 0 c = 1 := by
  simp [KB.psiL]

theorem intB_of (hPS : StandardPairingDecay.PStdC) (hD : DecayUnif) : IntB := by
  intro Cb
  obtain ⟨c1, h1⟩ := limit_of_module_forms Cb
  obtain ⟨c7, h7⟩ := hD Cb
  refine ⟨max c1 c7, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB n
  have hB7 := PBJoint.built_setting_to_model_place (le_max_right c1 c7) hB
  have hB' := hB
  obtain ⟨-, -, -, hcut, -, -, -, -, -, -, hGo, -, -, -, hA, hv⟩ := hB'
  have hCI : KB.CutInside S := PBCut.cutInside_of_built hB
  have hgpos := PBL.g_pos_of_built hB
  have hcpt : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (cutSeq S p f χ n v ε) := by
    intro v ε hε
    obtain ⟨hl0, hInD, -, hCk, hCC⟩ := hv v
    refine (h1 (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (f v) χ ε A₀ S.Ntop cutN (by rw [hl0]; exact hInD)
      hcut hε hCk hCC (le_trans ?_ hA) (fun n g => rfl)).1 n
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (by positivity)
  intro v ε hε i hi1 hi2 w h h' hsz hsz'
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hj : j ≤ S.G.r := Nat.le_of_succ_le_succ hi2
  have hsz1 : D.ptSize h = j := hsz.trans (Nat.add_sub_cancel j 1)
  have hsz1' : D.ptSize h' = j := hsz'.trans (Nat.add_sub_cancel j 1)
  rw [Nat.add_sub_cancel]
  obtain ⟨hl0, hInD, -, -, -⟩ := hv v
  have hw : KB.CutWord (D.parOf S v) (S.l + 1) (w.1 v) := PBD.cutWord_of_adm S hGo hCI w v
  have hi2' : j + 1 ≤ S.G.r + 1 := Nat.succ_le_succ hj
  have hadm : D.AdmAt S v (w.1 v) := ⟨w, rfl⟩
  have h7' := h7 E Wp Wq S p f χ A₀ hB7 v ε hε (j + 1) hi1 hi2' (w.1 v) hadm h h' hsz hsz'
  refine h7'.elim fun Cd hC => ?_
  have hdec := (hC n).1
  have hloc_app : ∀ (H : C.LPt) (c : ℂ), D.ptSize H = j → D.IsLocPt (H ++ [(1, c)]) (j + 1) → D.IsLocPt H j :=
    fun H c hH hl => ⟨fun b hb => hl.1 b (List.mem_append_left _ hb), hH⟩
  by_cases hloc : D.IsLocPt h j ∧ D.IsLocPt h' j
  · obtain ⟨hh, hh'⟩ := hloc
    have hH : D.IsLocPt (PBL.stdS S h) j := (PBD.isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh
    have hH' : D.IsLocPt (PBL.stdS S h') j := (PBD.isLocPt_toStd_iff _ _ hgpos h' 1 j).2 hh'
    have hPS' := hPS (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (cutSeq S p f χ n v ε) j hj (w.1 v)
      (PBL.stdS S h) (PBL.stdS S h') hH hH' Cb (by rw [hl0]; exact hInD) (hcpt v ε hε) (by rw [hl0]; exact hw)
    refine hPS'.elim fun φ0 hφ0all => ?_
    obtain ⟨hφ0c, -, hφ0, -⟩ := hφ0all
    have hlam := PBL.lamS_pos S hgpos j
    set φ : ℂ → ℂ := fun c => ((StandardPairingDecay.Kg S j h h' : ℝ) : ℂ) * φ0 ((PBL.lamS S j : ℂ) * c) with hφdef
    have hφc : Continuous φ := continuous_const.mul (hφ0c.comp (continuous_const.mul continuous_id))
    have hφeq : ∀ c : ℂ, c ≠ 0 → φ c = (PBL.setC S p (cutSeq S p f χ n)).gramLoc v ε (j + 1) (w.1 v)
        (h ++ [(1, c)]) (h' ++ [(1, c)]) := by
      intro c hc
      have hlc : (PBL.lamS S j : ℂ) * c ≠ 0 := mul_ne_zero (by exact_mod_cast hlam.ne') hc
      rw [StandardPairingDecay.gramLoc_setC_app hB (cutSeq S p f χ n) v ε j hj (w.1 v) h h' hh.2 hh'.2 c hc, hφdef]
      simp only
      rw [hφ0 _ hlc]
      ring
    refine ⟨φ, hφc, hφeq, ⟨Cd, fun c => ?_⟩, ?_⟩
    · exact PBB.K8.bound_all hφc (fun c hc => by rw [hφeq c hc]; exact hdec c hc) c
    · have hae : (fun c => φ c) =ᵐ[volume] fun c => (PBL.setC S p (cutSeq S p f χ n)).gramLoc v ε (j + 1) (w.1 v)
          (h ++ [(1, c)]) (h' ++ [(1, c)]) * KB.psiL S 0 c := by
        filter_upwards [PBL.ae_ne_zero_complex] with c hc
        rw [psiL_zero, mul_one, hφeq c hc]
      rw [integral_congr_ae hae, StandardPairingDecay.int_gramLoc_setC hPS hB (cutSeq S p f χ n) v ε (hcpt v ε hε) j hj (w.1 v) hw 0
        h h' hh hh']
      have hs0 : PBL.sW S j 0 = 0 := by simp [PBL.sW]
      rw [hs0, waveG_zero_eq_self, ← PBL.rr_eq_form (p v) _ j hj (w.1 v) _ _ hH hH']
      erw [PBL.gramLoc_setC hB]
      have hsA := PBL.sizeAt_pos S hGo v (w.1 v) hadm
      have hk := PBL.kc_scal hB v j hj (w.1 v) h h'
      have hrd := PBD.rd_pos' E
      have hδ : 0 < D.deG (S.g : ℝ) (S6.rd E) := by unfold D.deG; positivity
      have hdl : 0 < KB.dlB S (j + 1) 1 := by unfold KB.dlB; exact div_pos (zpow_pos hrd _) hδ
      have key : StandardPairingDecay.Kg S j h h' * |(PBL.lamS S j ^ 2)⁻¹| =
          KB.dlB S (j + 1) 1 * (√(PBL.nnS S h) * √(PBL.nnS S h') * (1 / (PBL.bS S h * PBL.bS S h' * PBL.ΓS S j))) := by
        unfold PBL.Kc PBL.dW at hk
        unfold StandardPairingDecay.Kg
        field_simp at hk ⊢
        linear_combination hk
      show ((StandardPairingDecay.Kg S j h h' * |(PBL.lamS S j ^ 2)⁻¹| : ℝ) : ℂ) * _ = ((KB.dlB S (j + 1) 1 : ℝ) : ℂ) * _
      rw [key]
      push_cast
      ring
  · have hz : ∀ c : ℂ, (PBL.setC S p (cutSeq S p f χ n)).gramLoc v ε (j + 1) (w.1 v) (h ++ [(1, c)]) (h' ++ [(1, c)]) = 0 := by
      intro c
      erw [PBL.gramLoc_setC hB, PBL.rr_zero_of_not, mul_zero]
      rintro ⟨h1, h2⟩
      refine hloc ⟨hloc_app h c hsz1 ((PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).1 h1),
        hloc_app h' c hsz1' ((PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).1 h2)⟩
    have hz0 : (PBL.setC S p (cutSeq S p f χ n)).gramLoc v ε j (w.1 v) h h' = 0 := by
      erw [PBL.gramLoc_setC hB, PBL.rr_zero_of_not, mul_zero]
      rintro ⟨h1, h2⟩
      exact hloc ⟨(PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).1 h1, (PBD.isLocPt_toStd_iff _ _ hgpos _ 1 _).1 h2⟩
    refine ⟨fun _ => 0, continuous_const, fun c _ => (hz c).symm, ⟨0, fun c => by simp⟩, ?_⟩
    rw [hz0, integral_zero, mul_zero]

def IntBOfParts : Prop := StandardPairingDecay.PStdC → DecayUnif → IntB

theorem intBOfParts : IntBOfParts := intB_of

end

end Formalism.FourierDecayAlt.P.PBASM

namespace Formalism.FourierDecayAlt.P

theorem integral_bound_of_parts : PBASM.IntBOfParts := PBASM.intBOfParts

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKapTP
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField PI.UnitaryGroupMassFormula.GsFr
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def kcut (t : ℝ) : ℝ := Real.smoothTransition (6 * t - 2)

theorem kcut_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) kcut :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

theorem kcut_zero {t : ℝ} (ht : t ≤ 1 / 3) : kcut t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem kcut_one {t : ℝ} (ht : 1 / 2 ≤ t) : kcut t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

def NrmWFacts : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a => PRho.nrmW k r z a) ∧
    ∀ h ∈ UWset k r z, ∀ a, PRho.nrmW k r z (h *ᵥ a) = PRho.nrmW k r z a

theorem nrmW_smul {k r : ℕ} (z a : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    PRho.nrmW k r z (c • a) = Complex.normSq c * PRho.nrmW k r z a := by
  unfold PRho.nrmW
  rw [SSn.Geom.prWv_eq, SSn.Geom.prW_smul, ← SSn.Geom.prWv_eq]
  rw [hm_smul_l, hm_smul_r, ← mul_assoc, Complex.star_def, Complex.mul_conj, Complex.re_ofReal_mul]

section lm

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def lmul (A : Wp →L[ℂ] Wp) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) := ContinuousLinearMap.compL ℂ Wq Wp Wp A

theorem lmul_apply (A : Wp →L[ℂ] Wp) (X : Wq →L[ℂ] Wp) : lmul A X = A.comp X := rfl

theorem hsInner_lmul (A : Wp →L[ℂ] Wp) (hA : ∀ x y, inner ℂ (A x) y = inner ℂ x (A y)) (X Y : Wq →L[ℂ] Wp) :
    B.hsInner (lmul A X) Y = B.hsInner X (lmul A Y) := by
  simp only [B.hsInner, B.hsVec, lmul_apply, PiLp.inner_apply, ContinuousLinearMap.comp_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hA]

end lm

theorem typeProj_of (hPE : PRho.PRhoExists) (hGL : PRho.GaugeLines) (hDU : SSn.Rep.DatumUnit)
    (hNW : NrmWFacts) : TypeProj := by
  refine ⟨0, le_rfl, ?_⟩
  intro Cc _ E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  by_cases hk : 2 ≤ S.G.k
  · obtain ⟨Pr, hs, heqv, hrest⟩ := hPE (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hPl hk
    obtain ⟨hnc, hninv⟩ := hNW S.G.k S.G.r (T v).base.z (T v).base.z_mem (T v).base.T_pos
    refine ⟨fun σ a => ((kcut (PRho.nrmW S.G.k S.G.r (T v).base.z a) : ℝ) : ℂ) • lmul (Pr σ a), ?_, ?_, ?_, ?_⟩
    ·
      intro σ
      rw [contDiff_iff_contDiffAt]
      intro a₀
      by_cases h : 1 / 4 < PRho.nrmW S.G.k S.G.r (T v).base.z a₀
      · have hO : IsOpen {a | 1 / 4 < PRho.nrmW S.G.k S.G.r (T v).base.z a} :=
          isOpen_lt continuous_const hnc.continuous
        have hl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun A : Wp (S.pl v) →L[ℂ] Wp (S.pl v) => (lmul A : (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) →L[ℂ] _)) :=
          (ContinuousLinearMap.compL ℂ (Wq (S.pl v)) (Wp (S.pl v)) (Wp (S.pl v))).contDiff.restrict_scalars ℝ
        have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun a => ((kcut (PRho.nrmW S.G.k S.G.r (T v).base.z a) : ℝ) : ℂ) • lmul (Pr σ a))
            {a | 1 / 4 < PRho.nrmW S.G.k S.G.r (T v).base.z a} :=
          ((Complex.ofRealCLM.contDiff.comp (kcut_contDiff.comp hnc)).contDiffOn).smul
            (hl.comp_contDiffOn (hs σ))
        exact h1.contDiffAt (hO.mem_nhds h)
      · have hO : IsOpen {a | PRho.nrmW S.G.k S.G.r (T v).base.z a < 1 / 3} :=
          isOpen_lt hnc.continuous continuous_const
        have hmem : a₀ ∈ {a | PRho.nrmW S.G.k S.G.r (T v).base.z a < 1 / 3} := by
          simp only [Set.mem_setOf_eq]; linarith [not_lt.1 h]
        refine (contDiffAt_const (c := (0 : (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) →L[ℂ] (Wq (S.pl v) →L[ℂ] Wp (S.pl v))))).congr_of_eventuallyEq ?_
        filter_upwards [hO.mem_nhds hmem] with a ha
        simp [kcut_zero (le_of_lt ha)]
    ·
      intro σ a A B'
      dsimp only
      by_cases h : 0 < PRho.nrmW S.G.k S.G.r (T v).base.z a
      · rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, kap_hsInner_smul_left,
          kap_hsInner_smul_right, Complex.conj_ofReal, hsInner_lmul _ ((hrest a h).2.1 σ)]
      · have h0 : kcut (PRho.nrmW S.G.k S.G.r (T v).base.z a) = 0 := kcut_zero (by linarith [not_lt.1 h])
        simp [h0, B.hsInner, kap_hsVec_zero]
    ·
      intro σ h hh h' hh' a X
      have hinv : h⁻¹ ∈ UWset S.G.k S.G.r (T v).base.z := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh
      have hu := WeylGroupFacts.isUnit_of_uh hh.1
      have hh1 : h⁻¹ * h = 1 := by
        first
          | exact Matrix.nonsing_inv_mul _ hu
          | exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)
      have key : ∀ y, (T v).base.π h⁻¹ ((T v).base.π h y) = y := by
        intro y
        rw [← ContinuousLinearMap.comp_apply, ← (T v).base.π_rep.2 _ hinv _ hh, hh1, (T v).base.π_rep.1]
        rfl
      dsimp only
      rw [hninv h hh a, heqv h hh σ a]
      ext y
      simp [lmul_apply, key]
    ·
      intro x hx σ ρ
      dsimp only
      obtain ⟨hP1, hH1, -, -⟩ := hDU Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v x.2 hx.2
      set n0 := SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec x.2 with hn0
      have hN0 : PRho.nrmW S.G.k S.G.r (T v).base.z n0 = 1 := by
        unfold PRho.nrmW; rw [hP1, hH1]; simp
      have hph : SSn.phD x.1 ≠ 0 := by
        intro h0
        have := SSn.Geom.phD_norm hx.1
        rw [h0, norm_zero] at this
        exact zero_ne_one this
      have hN : PRho.nrmW S.G.k S.G.r (T v).base.z (SSn.phD x.1 • n0) = 1 := by
        rw [nrmW_smul, hN0, mul_one, Complex.normSq_eq_norm_sq, SSn.Geom.phD_norm hx.1]; norm_num
      have hscale : ∀ τ, Pr τ (SSn.phD x.1 • n0) = Pr τ n0 :=
        fun τ => (hrest n0 (by rw [hN0]; norm_num)).1 τ _ hph
      have hfix : ∀ y, Pr ρ n0 (e ρ x.2 y) = e ρ x.2 y := by
        intro y
        refine ((hrest n0 (by rw [hN0]; norm_num)).2.2.2 ρ (e ρ x.2 y)).2 ?_
        intro Fr hFrm w
        rw [hP1] at hFrm
        exact hGL Cc E Wp Wq S T f χ ν' m₀ top A₀ v e ⟨hB, hFr, hGa, hQQ⟩ hk x.2 hx.2 ρ Fr hFrm w y
      rw [ContinuousLinearMap.smul_apply, hN, kcut_one (by norm_num), lmul_apply, hscale]
      simp only [Complex.ofReal_one, one_smul]
      by_cases hσ : σ = ρ
      · subst hσ
        rw [if_pos rfl]
        ext y
        exact hfix y
      · rw [if_neg hσ]
        ext y
        have horth := (hrest n0 (by rw [hN0]; norm_num)).2.2.1 σ ρ
        rw [if_neg hσ] at horth
        rw [ContinuousLinearMap.comp_apply, ← hfix y, ← ContinuousLinearMap.comp_apply (Pr σ n0), horth]
        rfl
  ·
    have hk1 : (D.parOf S v).k - 1 = 0 := by
      have : (D.parOf S v).k = S.G.k := rfl
      omega
    have hsub : ∀ σ ρ : M.Ty (D.parOf S v), σ = ρ := by
      intro σ ρ
      funext i
      exact absurd i.2 (by omega)
    refine ⟨fun _ _ => ContinuousLinearMap.id ℂ _, fun σ => contDiff_const, fun σ a A B' => rfl,
      fun σ h _ h' _ a X => rfl, ?_⟩
    intro x _ σ ρ
    rw [if_pos (hsub σ ρ)]
    rfl

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveLocBOf
namespace Formalism.FourierDecayAlt.P.PBASM

open Formalism.FourierDecayAlt NumberField

noncomputable section

def GermPartsC : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    ∀ n v, GermRealisation.GermFibres (PBL.setC S p (cutSeq S p f χ n)) v ∧ GermRealisation.GermCont (PBL.setC S p (cutSeq S p f χ n)) v

theorem germLocB_of (hI : IntB) (hG : GermPartsC) : GermLocB := by
  intro Cb
  obtain ⟨c1, h1⟩ := hI Cb
  obtain ⟨c2, h2⟩ := hG Cb
  refine ⟨max c1 c2, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB n v
  have hI' := h1 E Wp Wq S p f χ A₀ (PBJoint.built_setting_to_model_place (le_max_left _ _) hB) n v
  obtain ⟨hF, hC⟩ := h2 E Wp Wq S p f χ A₀ (PBJoint.built_setting_to_model_place (le_max_right _ _) hB) n v
  exact GermRealisation.germLoc_of_fibres hI' hB.1 hB.2.1 hF hC

end

end Formalism.FourierDecayAlt.P.PBASM
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveDiffFormOf
noncomputable section

namespace Formalism.FourierDecayAlt.P.StandardPairingDecay

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Matrix Filter Topology

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def OnOldBound : Prop :=
  ∀ (k ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k ρ Wp Wq) (w : List C.Letter) (m : ℕ),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ : ℂ, ‖σ‖ ≤ 2 → ∀ (ys : List ℝ) (A : ℝ)
      (x : Wd.Ix (Fin (KB.plusW ys w).length) → B.Mat k ρ → (Wq →L[ℂ] Wp)) (c : ℝ),
      (∀ e, B.CCle (A + 3 * ((m + 1 : ℕ) : ℝ)) m (x e) c) →
      ∀ e, B.CCle A m (KB.onOld (PBO.mDiff Bs σ w) ys x e) (K * ‖σ‖ ^ 3 * c)

theorem plusW_length (ys : List ℝ) (w : List C.Letter) : (KB.plusW ys w).length = ys.length + w.length := by
  rw [Formalism.FourierDecayAlt.P.PBD.plusW_eq]
  simp

theorem waveDiffForm_of (hO : OnOldBound) : PBO.WaveDiffForm := by
  intro _hP Cb
  obtain ⟨Cs, hCs0, hSQ⟩ := Formalism.FourierDecayAlt.P.PBE.sliceQ
  refine ⟨2 * Cs + 2, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f χ ε A N cut _hInD hχ hε hf hfA hA hcut j hj w hw hwN h hh ys hys hcw
  have hk2 : 2 ≤ P.k := p.hl.2.2
  set N₂ : ℕ := 2 * N + 6 with hN₂
  set R : ℝ := ((P.r : ℝ) + 1) ^ 4 with hRdef
  have hR1 : 1 ≤ R := one_le_pow₀ (by have : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _; linarith)
  set n0 : ℝ := 2 * (P.r : ℝ) + P.k + 1 with hn0
  have hn01 : 1 ≤ n0 := by
    have : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
    rw [hn0]; linarith
  set X : ℝ := ((N + 3 : ℕ) : ℝ) * n0 ^ 2 + n0 ^ 3 with hXdef
  have hX1 : 1 ≤ X := by
    have h1 : 1 ≤ n0 ^ 3 := one_le_pow₀ hn01
    have : 0 ≤ ((N + 3 : ℕ) : ℝ) * n0 ^ 2 := by positivity
    rw [hXdef]; linarith
  have hA' : Cs * ((P.r : ℝ) + 1) ^ 4 * ((N₂ : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 +
      (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A - 1 := by
    have hX2 : (N₂ : ℝ) * n0 ^ 2 + n0 ^ 3 ≤ 2 * X := by
      rw [hXdef, hN₂]
      push_cast
      have : 0 ≤ n0 ^ 3 := by positivity
      nlinarith
    have hRX : 1 ≤ R * X := by nlinarith
    have h0 : (2 * Cs + 2) * R * X ≤ A := hA
    calc Cs * R * ((N₂ : ℝ) * n0 ^ 2 + n0 ^ 3) ≤ Cs * R * (2 * X) :=
          mul_le_mul_of_nonneg_left hX2 (by positivity)
      _ = (2 * Cs + 2) * R * X - 2 * (R * X) := by ring
      _ ≤ A - 1 := by linarith
  set MM := 3 * (11 * (N₂ * (2 * P.r + P.k + 1) ^ 2 + (2 * P.r + P.k + 1) ^ 3) + 5) with hMM
  obtain ⟨bf, hbf⟩ := hfA MM
  have hbf0 : 0 ≤ bf := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hbf
  have hbf' : B.CCle (A - 1) MM f bf := Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by linarith) hbf
  obtain ⟨Kp, hKp0, hKp⟩ := Formalism.FourierDecayAlt.P.JCx2.pd_cut_ccle (k := P.k) (r := P.r) (E := Wq →L[ℂ] Wp) MM
  have hψ : ∀ n : ℕ, B.CCle (A - 1) MM (fun g => Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g • f g)
      (Kp * bf / ((n : ℝ) + 1)) := fun n => hKp _ (by positivity) A f bf hbf
  have hψs : ∀ n : ℕ, B.CkOn ⊤ (B.GV P.k P.r) (fun g => Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g • f g) :=
    fun n => Formalism.FourierDecayAlt.P.JCx2.pd_smooth_smul (Formalism.FourierDecayAlt.P.JCx2.pd_psi_cd _) hf
  set hn : ℕ → B.Mat P.k P.r → (Wq →L[ℂ] Wp) := fun n g => cut n g • f g with hhn
  have hneq : ∀ n, hn n = fun g => f g + (-1 : ℂ) • (Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g • f g) := by
    intro n; funext g
    simp only [hhn, Formalism.FourierDecayAlt.P.PBE.cut_eq cut hcut n g, sub_smul, one_smul]
    simp [sub_eq_add_neg]
  have hnC : ∀ n, B.CCle (A - 1) MM (hn n) (bf + Kp * bf) := by
    intro n
    rw [hneq n]
    refine Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hbf' (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul (-1) (hψ n))) ?_
    have h1 : Kp * bf / ((n : ℝ) + 1) ≤ Kp * bf := div_le_self (by positivity) (by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    simp only [norm_neg, norm_one, one_mul]
    linarith
  have hns : ∀ n, B.CkOn ⊤ (B.GV P.k P.r) (hn n) := by
    intro n
    rw [hneq n]
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add hf (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_smul (-1) (hψs n))
  have hFn : ∀ n, (fun g => cut n g • D.cutF p.T.base χ f ε g) = D.cutF p.T.base χ (hn n) ε := by
    intro n; funext g
    simp only [D.cutF, hhn]
    rw [smul_comm]
  set w' := KB.plusW ys w with hw'
  have hw'len : w'.length ≤ N + 3 := by rw [hw', plusW_length]; omega
  have hN₂w : w'.length ≤ N₂ := by omega
  have hc : P.r - j = P.r - D.ptSize h := by rw [hh.2]
  have hQ := fun e => hSQ Cs le_rfl P.k P.r Wp Wq p.T χ (A - 1) N₂ P rfl rfl hk2 hχ hA' ε hε j hj w' hN₂w h hc hh e
  choose εa Ka hεa hKa hQ1 _hQ2 using hQ
  set KK : ℝ := ∑ e, Ka e with hKK
  have hKa' : ∀ e, Ka e ≤ KK := fun e =>
    Finset.single_le_sum (f := Ka) (fun e _ => hKa e) (Finset.mem_univ e)
  have hKK0 : 0 ≤ KK := Finset.sum_nonneg fun e _ => hKa e
  set cs : ℝ := KK * (bf + Kp * bf) with hcs
  have hcs0 : 0 ≤ cs := by positivity
  have hsl : ∀ n e, B.CCle (P5.Auser P N₂ + 1) (P5.mmUser P N₂) (Formalism.FourierDecayAlt.P.PBE.xs p.T χ ε j hj w' h hc (hn n) e) cs := by
    intro n e
    obtain ⟨-, h2⟩ := hQ1 e (hn n) _ (hns n) (hnC n)
    exact Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c h2 (mul_le_mul_of_nonneg_right (hKa' e) (by positivity))
  have hxs : ∀ n, KB.slv p.T (D.cutF p.T.base χ (hn n) ε) j hj w' h hh.2 =
      Formalism.FourierDecayAlt.P.PBE.xs p.T χ ε j hj w' h hc (hn n) := fun n => rfl
  set mo : ℕ := 5 + (2 * (P.r - j) + P.k + 1) * w'.length with hmo
  obtain ⟨K3, hK30, hK3⟩ := hO P.k (P.r - j) Wp Wq (p.T.bs j) w mo
  set Af : ℝ := P5.Auser P w'.length + 1 with hAf
  obtain ⟨Cf, hCf0, hCf⟩ := Formalism.FourierDecayAlt.P.JCx4.formLev_bound_mm P p.T (M.sgn P p.l0) ⟨j, by omega⟩ w' Af le_rfl
  have hq : ((2 * (P.r - j) + P.k + 1 : ℕ) : ℝ) ≤ n0 := by
    rw [hn0]
    have : P.r - j ≤ P.r := Nat.sub_le _ _
    have : ((P.r - j : ℕ) : ℝ) ≤ P.r := by exact_mod_cast this
    push_cast
    linarith
  have hL : (w'.length : ℝ) ≤ (N : ℝ) + 3 := by exact_mod_cast hw'len
  have hdec : Af - 1 + 3 * ((mo + 1 : ℕ) : ℝ) ≤ P5.Auser P N₂ + 1 := by
    have hmo' : ((mo + 1 : ℕ) : ℝ) = 6 + ((2 * (P.r - j) + P.k + 1 : ℕ) : ℝ) * (w'.length : ℝ) := by
      rw [hmo]; push_cast; ring
    have hnV : ((P5.nV P : ℕ) : ℝ) = n0 := by rw [hn0]; unfold P5.nV; push_cast; ring
    have hR3 : 1 ≤ ((P.r : ℝ) + 1) ^ 3 := one_le_pow₀ (by have : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _; linarith)
    have hdiff : P5.Auser P N₂ - P5.Auser P w'.length =
        127 * ((P.r : ℝ) + 1) ^ 3 * (n0 ^ 2 * ((N₂ : ℝ) - w'.length)) := by
      unfold P5.Auser; rw [hnV]; ring
    have hgap : (N : ℝ) + 3 ≤ (N₂ : ℝ) - w'.length := by rw [hN₂]; push_cast; linarith
    have hN3 : (3 : ℝ) ≤ (N : ℝ) + 3 := by have : (0 : ℝ) ≤ N := Nat.cast_nonneg _; linarith
    have h1 : 127 * (n0 ^ 2 * ((N : ℝ) + 3)) ≤ P5.Auser P N₂ - P5.Auser P w'.length := by
      rw [hdiff]
      have hb : n0 ^ 2 * ((N : ℝ) + 3) ≤ n0 ^ 2 * ((N₂ : ℝ) - w'.length) :=
        mul_le_mul_of_nonneg_left hgap (by positivity)
      have hpos : 0 ≤ n0 ^ 2 * ((N : ℝ) + 3) := by positivity
      have hY : 0 ≤ n0 ^ 2 * ((N₂ : ℝ) - w'.length) := le_trans hpos hb
      have hR : n0 ^ 2 * ((N₂ : ℝ) - w'.length) ≤ ((P.r : ℝ) + 1) ^ 3 * (n0 ^ 2 * ((N₂ : ℝ) - w'.length)) :=
        le_mul_of_one_le_left hY hR3
      calc 127 * (n0 ^ 2 * ((N : ℝ) + 3)) ≤ 127 * (((P.r : ℝ) + 1) ^ 3 * (n0 ^ 2 * ((N₂ : ℝ) - w'.length))) := by
            linarith
        _ = 127 * ((P.r : ℝ) + 1) ^ 3 * (n0 ^ 2 * ((N₂ : ℝ) - w'.length)) := by ring
    have h2 : ((2 * (P.r - j) + P.k + 1 : ℕ) : ℝ) * (w'.length : ℝ) ≤ n0 * ((N : ℝ) + 3) :=
      mul_le_mul hq hL (Nat.cast_nonneg _) (by linarith)
    have ha3 : 3 ≤ n0 * ((N : ℝ) + 3) := by
      calc (3 : ℝ) ≤ (N : ℝ) + 3 := hN3
        _ = 1 * ((N : ℝ) + 3) := by ring
        _ ≤ n0 * ((N : ℝ) + 3) := mul_le_mul_of_nonneg_right hn01 (by linarith)
    have hb2 : n0 * ((N : ℝ) + 3) ≤ n0 ^ 2 * ((N : ℝ) + 3) := by
      have e : n0 ^ 2 * ((N : ℝ) + 3) = n0 * (n0 * ((N : ℝ) + 3)) := by ring
      rw [e]
      exact le_mul_of_one_le_left (by linarith) hn01
    have h3 : 3 * (n0 * ((N : ℝ) + 3)) + 17 ≤ 127 * (n0 ^ 2 * ((N : ℝ) + 3)) := by linarith
    rw [hAf, hmo']
    linarith
  have hord : mo ≤ P5.mmUser P N₂ := by
    have h1 : 2 * (P.r - j) + P.k + 1 ≤ P5.nV P := by unfold P5.nV; omega
    have h2 : w'.length ≤ 3 * (P.r + 1) * (N₂ + 2) := by
      have : N + 3 ≤ 3 * (P.r + 1) * (N₂ + 2) := by
        have : 1 ≤ 3 * (P.r + 1) := by omega
        nlinarith
      omega
    have h3 : (2 * (P.r - j) + P.k + 1) * w'.length ≤ P5.nV P * (3 * (P.r + 1) * (N₂ + 2)) :=
      Nat.mul_le_mul h1 h2
    have e : P5.mmUser P N₂ = 5 + 3 * (P.r + 1) * (N₂ + 2) * P5.nV P + N₂ * P.r := rfl
    have e2 : P5.nV P * (3 * (P.r + 1) * (N₂ + 2)) = 3 * (P.r + 1) * (N₂ + 2) * P5.nV P := by ring
    rw [e, hmo]
    rw [e2] at h3
    exact le_trans (Nat.add_le_add_left h3 5) (Nat.le_add_right _ _)
  refine ⟨Cf * (K3 * cs) * (K3 * cs), fun n σ hσ => ?_⟩
  rw [hFn n, hxs n]
  have hx : ∀ e, B.CCle (Af - 1 + 3 * ((mo + 1 : ℕ) : ℝ)) mo (Formalism.FourierDecayAlt.P.PBE.xs p.T χ ε j hj w' h hc (hn n) e) cs :=
    fun e => Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A hdec (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m hord (hsl n e))
  have hu := hK3 σ hσ ys (Af - 1) _ cs hx
  have hv : ∀ e, B.CCle (Af - 1 - 2 * (w'.length : ℝ)) 5
      (KB.onOld (PBO.mDiff (p.T.bs j) σ w) ys (Formalism.FourierDecayAlt.P.PBE.xs p.T χ ε j hj w' h hc (hn n)) e)
      (K3 * ‖σ‖ ^ 3 * cs) := fun e =>
    Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by have : (0 : ℝ) ≤ w'.length := Nat.cast_nonneg _; linarith)
      (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m (by rw [hmo]; omega) (hu e))
  have hb := hCf _ _ _ _ hu hv
  show ‖D.formLev p.T (M.sgn P p.l0) ⟨j, by omega⟩ w' _ _‖ ≤ _
  refine hb.trans (le_of_eq ?_)
  ring

end Formalism.FourierDecayAlt.P.StandardPairingDecay
end
end
