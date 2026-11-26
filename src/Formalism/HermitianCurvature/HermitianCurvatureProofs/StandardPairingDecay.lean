module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftDegreeLemmas
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MemLevelZeroOfMemGroup

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardPairingDecay
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

theorem hsInner_zero_left' {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) : B.hsInner (0 : Wq →L[ℂ] Wp) A = 0 := by
  unfold B.hsInner B.hsVec
  have : (WithLp.toLp 2 fun i : Fin (Module.finrank ℂ Wq) => (0 : Wq →L[ℂ] Wp) (stdOrthonormalBasis ℂ Wq i)) = 0 := by
    simp; rfl
  rw [this, inner_zero_right]

section vec

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem vecV_zero_small (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    {G : B.Mat k r → (Wq →L[ℂ] Wp)} {ε : ℝ} (hG : ∀ g ∈ B.GV k r, G g ≠ 0 → ε ≤ Gf k r Bs.z Bs.z' g)
    (q : C.LPt) (hq : D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q < ε) : D.vecV Bs ν' m₀ G q = 0 := by
  unfold D.vecV
  by_cases hq' : D.IsLocPt q (r + 1) ∧ 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q
  · simp only [dif_pos hq']
    by_cases h' : ∃ γ ∈ B.GV k r, Zhat k r Bs.z Bs.z' γ = D.ptMatN q (r + 1) ∧ D.IsDFrame Bs ν' m₀ γ
    · simp only [dif_pos h']
      have hγ := h'.choose_spec.1
      have hGq := Formalism.FourierDecayAlt.P.ptG_spec k r Bs.z Bs.z' q h'.choose hq'.1 h'.choose_spec.2.1
      have e := Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_smul_of_ae Bs h'.choose
        (D.muR Bs h'.choose (hq'.1.2 ▸ D.ptPerm q)) G (fun _ => 0) 0 (by
        filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
        have hz : G (B.sgs p h'.choose) = 0 := by
          by_contra hne
          have h1 := hG _ (Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ) hne
          rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp, ← hGq] at h1
          linarith
        simp [D.orbIntegrand, B.rho, hz])
      rw [e, zero_smul]
    · simp only [dif_neg h']
  · simp only [dif_neg hq']

end vec

theorem rr_top_small {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (h h' : C.LPt) (hh : D.IsLocPt h P.r)
    (Cb : ℝ) (hθ : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hF : KB.CptCoef p.T.base F) (hw : KB.CutWord P p.l0 w) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c : ℂ, Complex.normSq c - P.T * P.T' < δ →
      p.RR F (P.r + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)]) = 0 := by
  classical

  have hθc := fun e => Formalism.FourierDecayAlt.P.theta_compact_support Wp Wq P p F w e Cb hθ hF hw
  choose F' hF'c hF'd hF'v using hθc
  obtain ⟨εF, hεF, hGF⟩ := hF.2.2
  choose εe hεe hGe using fun e => (hF'c e).2.2
  let Sε : Finset ℝ := insert εF (Finset.univ.image εe)
  have hne : Sε.Nonempty := ⟨εF, Finset.mem_insert_self _ _⟩
  set ε := Sε.min' hne with hεdef
  have hε : 0 < ε := by
    rw [hεdef, Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hεF
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hy
      exact hεe a
  have hεF' : ε ≤ εF := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  have hεe' : ∀ e, ε ≤ εe e := fun e =>
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ e)))
  set Dh := Complex.normSq (D.ptMatN h P.r).det with hDh
  have hD0 : 0 ≤ Dh := Complex.normSq_nonneg _
  have hD1 : 0 < Dh + 1 := by linarith
  refine ⟨ε / (Dh + 1), div_pos hε hD1, fun c hc => ?_⟩
  have hTT : Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' = P.T * P.T' := by
    rw [p.hP.2.2.2.1, p.hP.2.2.2.2.1]
  have hpt : D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r (h ++ [(1, c)]) < ε := by
    rw [hTT, Formalism.FourierDecayAlt.P.PBD.ptG_app _ c h P.r hh.2]
    by_cases hs : Complex.normSq c - P.T * P.T' ≤ 0
    · have : Dh * (Complex.normSq c - P.T * P.T') ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hD0 hs
      linarith
    · push Not at hs
      have h1 : Dh * (Complex.normSq c - P.T * P.T') ≤ (Dh + 1) * (Complex.normSq c - P.T * P.T') := by nlinarith
      have h2 : (Dh + 1) * (Complex.normSq c - P.T * P.T') < (Dh + 1) * (ε / (Dh + 1)) :=
        mul_lt_mul_of_pos_left hc hD1
      rw [mul_div_cancel₀ _ hD1.ne'] at h2
      linarith
  unfold KB.Pl.RR D.RRplace
  split_ifs with hloc hi hi2 hw0
  · omega
  · have hv : D.vecV p.T.base p.ν' p.m₀ F (h ++ [(1, c)]) = 0 :=
      vecV_zero_small p.T.base p.ν' p.m₀ (fun g hg h0 => le_trans hεF' (hGF g hg h0)) _ hpt
    rw [hv, hsInner_zero_left']
  · unfold Top.topOf
    refine Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun ρ _ => ?_
    have hv : D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e F) (h ++ [(1, c)]) = 0 := by
      have := hF'v e (h ++ [(1, c)])
      unfold KB.Pl.V at this
      rw [this]
      exact vecV_zero_small p.T.base p.ν' p.m₀ (fun g hg h0 => le_trans (hεe' e) (hGe e g hg h0)) _ hpt
    rw [hv, ContinuousLinearMap.comp_zero, hsInner_zero_left', mul_zero]
  · omega
  · rfl

section law

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem zetaNorm_map {Bs : B.RealPlaceData k r Wp Wq} {μ : Measure (Mt k r)} (hμ : KB.ZetaNorm Bs μ) :
    μ.map (fun g : Mt k r => Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of g)) =
      (volume : Measure ℂ).withDensity (Formalism.FourierDecayAlt.P.JCx2.rbW k (Tz k r Bs.z) (Tz k r Bs.z')) := by
  have hf : Measurable fun g : Mt k r => Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of g) :=
    (Formalism.FourierDecayAlt.P.PBH.continuous_zetaL r Bs.z Bs.z').measurable
  refine Measure.ext_of_lintegral _ fun ψ hψ => ?_
  rw [lintegral_map hψ hf, hμ.2 ψ hψ, lintegral_withDensity_eq_lintegral_mul _ (Formalism.FourierDecayAlt.P.JCx2.measurable_radial_weight k _ _) hψ]
  rfl

theorem zetaNorm_integral {Bs : B.RealPlaceData k r Wp Wq} {μ : Measure (Mt k r)} (hμ : KB.ZetaNorm Bs μ)
    (ψ : ℂ → ℂ) (hψ : Measurable ψ) :
    ∫ g, ψ (Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of g)) ∂μ =
      ∫ ζ, (B2.zWeight k (Tz k r Bs.z) (Tz k r Bs.z') ζ : ℂ) * ψ ζ := by
  have hf : Measurable fun g : Mt k r => Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of g) :=
    (Formalism.FourierDecayAlt.P.PBH.continuous_zetaL r Bs.z Bs.z').measurable
  rw [← integral_map hf.aemeasurable hψ.aestronglyMeasurable, zetaNorm_map hμ,
    integral_withDensity_eq_integral_toReal_smul (Formalism.FourierDecayAlt.P.JCx2.measurable_radial_weight k _ _)
      (Filter.Eventually.of_forall fun ζ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
  simp only [Formalism.FourierDecayAlt.P.JCx2.rbW]
  rw [ENNReal.toReal_ofReal (Formalism.FourierDecayAlt.P.JCx2.rb_zWeight_nonneg k _ _ ζ), Complex.real_smul]

theorem zetaNorm_integrable {Bs : B.RealPlaceData k r Wp Wq} {μ : Measure (Mt k r)} (hμ : KB.ZetaNorm Bs μ)
    (ψ : ℂ → ℂ) (hψ : Measurable ψ)
    (hi : Integrable (fun g => ψ (Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of g))) μ) :
    Integrable (fun ζ => (B2.zWeight k (Tz k r Bs.z) (Tz k r Bs.z') ζ : ℂ) * ψ ζ) := by
  have hf : Measurable fun g : Mt k r => Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of g) :=
    (Formalism.FourierDecayAlt.P.PBH.continuous_zetaL r Bs.z Bs.z').measurable
  have h1 : Integrable ψ (μ.map fun g : Mt k r => Q.zetaL k r Bs.z Bs.z' (Fin.last r) (Matrix.of g)) :=
    (integrable_map_measure hψ.aestronglyMeasurable hf.aemeasurable).2 hi
  rw [zetaNorm_map hμ, integrable_withDensity_iff_integrable_smul' (Formalism.FourierDecayAlt.P.JCx2.measurable_radial_weight k _ _)
    (Filter.Eventually.of_forall fun ζ => ENNReal.ofReal_lt_top)] at h1
  refine h1.congr (Filter.Eventually.of_forall fun ζ => ?_)
  simp only [Formalism.FourierDecayAlt.P.JCx2.rbW]
  rw [ENNReal.toReal_ofReal (Formalism.FourierDecayAlt.P.JCx2.rb_zWeight_nonneg k _ _ ζ), Complex.real_smul]

end law

section pic

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem pic_cpt {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (K0 : Submodule ℂ (RadSp k r Bs.z Bs.z' Bs.π Bs.π'))
    (hJ : ∀ (F : Mx k r → (Wq →L[ℂ] Wp)) (ε : ℝ), 0 < ε → (∀ (A' : ℝ) (m' : ℕ), B.InCC A' m' F) →
      HasCompactSupport F → (∀ g ∈ B.GV k r, F g ≠ 0 → ε ≤ Gf k r Bs.z Bs.z' g) →
      ∃ Φ ∈ K0, ∀ x ∈ DomR k r Bs.z Bs.z',
        (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = resG k r (Fin.last r) (B.JF Bs F) x.1 x.2)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef Bs F) :
    ∃ Φ ∈ K0, ∀ x ∈ DomR k r Bs.z Bs.z',
      (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = resG k r (Fin.last r) (B.JF Bs F) x.1 x.2 := by
  classical
  obtain ⟨hs, ⟨R, hR⟩, ⟨ε, hε, hG⟩⟩ := hF
  set F₂ : B.Mat k r → (Wq →L[ℂ] Wp) := fun g => if g ∈ B.GV k r then F g else 0 with hF₂
  have he : ∀ g ∈ B.GV k r, F₂ g = F g := fun g hg => by simp [hF₂, hg]
  have hs₂ : B.CkOn ⊤ (B.GV k r) F₂ := by
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hs g₀ hg₀
    exact ⟨U, f', hU, hgU, hf', fun g hg hgG => by rw [he g hgG, hfe g hg hgG]⟩
  have hz : ∀ g, g ∉ {g : B.Mat k r | B.gN g ≤ R} → F₂ g = 0 := by
    intro g hg
    by_cases hgG : g ∈ B.GV k r
    · rw [he g hgG]
      by_contra h0
      exact hg (hR g hgG h0)
    · simp [hF₂, hgG]
  have hC := Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k r R
  obtain ⟨Φ, hΦK, hΦ⟩ := hJ F₂ ε hε
    (fun A m => Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hs₂ hC (fun g _ hgC => hz g hgC) A m)
    (HasCompactSupport.intro hC hz)
    (fun g hg h0 => hG g hg (by rwa [he g hg] at h0))
  refine ⟨Φ, hΦK, fun x hx => ?_⟩
  rw [hΦ x hx]
  have hGV : Q.wCell k r (Fin.last r) x.1 * x.2 ∈ B.GV k r := by
    rw [Rad.wCell_last_eq]
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (big_cell_mem_holds _ _ _ 1 hx.1 (by simp)) hx.2.1.1
  simp only [resG]
  rw [Formalism.FourierDecayAlt.P.Qx8.JF_congr Bs (a := 1) (fun g hg => by rw [he g hg, one_smul]) hGV, one_smul]

end pic

def TopContOn : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (h h' : C.LPt) (hh : D.IsLocPt h P.r)
    (hh' : D.IsLocPt h' P.r) (Cb : ℝ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F →
    KB.CutWord P p.l0 w →
    ContinuousOn (fun c : ℂ => p.RR F (P.r + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)]))
      {c : ℂ | P.T * P.T' < Complex.normSq c}

end Formalism.FourierDecayAlt.P.PBO
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.AsmCastMCastM
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableSliceAppendSingle
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem point_size_append_single (h : C.LPt) (c : ℂ) : D.ptSize (h ++ [(1, c)]) = D.ptSize h + (0 + 1) := by
  rw [Dx2.SL.ptSize_append]

theorem integrable_slice_append_single {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → E) (h : C.LPt) (c : ℂ)
    (hle : D.ptSize (h ++ [(1, c)]) ≤ r) (hloc : D.IsLocPt (h ++ [(1, c)]) (D.ptSize (h ++ [(1, c)])))
    (γ' : B.Mat k (r - D.ptSize (h ++ [(1, c)])))
    (hI : Integrable (JCTx6.gInt k (D.ptSize h) 0 (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm h) (D.ptDiag h) c
        (D.castV (by have := point_size_append_single h c; omega) z) (D.castV (by have := point_size_append_single h c; omega) z')
        (D.castF (by have := point_size_append_single h c; omega) F) γ')
      (JCTx6.muG k (D.ptSize h) 0 (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm h))) :
    Integrable (fun ξ : U.Xi k (D.ptSize (h ++ [(1, c)])) 0 (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm (h ++ [(1, c)])) =>
        U.psiStar k (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm (h ++ [(1, c)])) (D.castV (by omega) z)
            (D.castV (by omega) z') ξ •
          D.castF (by omega) F (U.gaXi k (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm (h ++ [(1, c)]))
            (D.ptDiag (h ++ [(1, c)])) ξ (fun a => a.elim0) γ'))
      (U.muXi k (D.ptSize (h ++ [(1, c)])) 0 (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm (h ++ [(1, c)]))) := by
  have hP : D.ptSize (h ++ [(1, c)]) = D.ptSize h + (0 + 1) := point_size_append_single h c
  have hspec := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hloc).1
  have hspec' := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ (Dx2.SL.isLocPt_head hloc)).1
  have hσ : ∀ a : Fin (D.ptSize (h ++ [(1, c)])),
      ((Dx2.SL.sigP (n := 0) (D.ptPerm h)) (Fin.cast hP a)).val = (D.ptPerm (h ++ [(1, c)]) a).val := by
    intro a
    rw [hspec a, Dx2.SL.partner_append 1 c h a.val (by have := a.isLt; omega)]
    by_cases h1 : a.val < D.ptSize h
    · rw [if_pos h1]
      have e : Fin.cast hP a = Fin.castAdd (0 + 1) ⟨a.val, h1⟩ := Fin.ext rfl
      rw [e, Dx2.SL.blockPerm_castAdd]
      exact hspec' ⟨a.val, h1⟩
    · rw [if_neg h1]
      have e : Fin.cast hP a = Fin.natAdd (D.ptSize h) ⟨a.val - D.ptSize h, by have := a.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, Dx2.SL.blockPerm_natAdd]
      simp only [Fin.val_natAdd, Fin.val_rev]
      omega
  have hd : ∀ a : Fin (D.ptSize (h ++ [(1, c)])),
      Dx2.SL.dP (n := 0) (D.ptDiag h) c (Fin.cast hP a) = D.ptDiag (h ++ [(1, c)]) a := by
    intro a
    simp only [D.ptDiag]
    rw [Dx2.SL.scal_append 1 c h a.val (by have := a.isLt; omega)]
    by_cases h1 : a.val < D.ptSize h
    · rw [if_pos h1]
      have e : Fin.cast hP a = Fin.castAdd (0 + 1) ⟨a.val, h1⟩ := Fin.ext rfl
      rw [e, Dx2.SL.dP, Fin.addCases_left]; rfl
    · rw [if_neg h1]
      have e : Fin.cast hP a = Fin.natAdd (D.ptSize h) ⟨a.val - D.ptSize h, by have := a.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, Dx2.SL.dP, Fin.addCases_right]

  have hσ' : ∀ b : Fin (D.ptSize h + (0 + 1)),
      (D.ptPerm (h ++ [(1, c)]) (Fin.cast hP.symm b)).val = ((Dx2.SL.sigP (n := 0) (D.ptPerm h)) b).val := by
    intro b
    have := hσ (Fin.cast hP.symm b)
    rw [show Fin.cast hP (Fin.cast hP.symm b) = b from Fin.ext rfl] at this
    exact this.symm
  have hd' : ∀ b : Fin (D.ptSize h + (0 + 1)),
      D.ptDiag (h ++ [(1, c)]) (Fin.cast hP.symm b) = Dx2.SL.dP (n := 0) (D.ptDiag h) c b := by
    intro b
    have := hd (Fin.cast hP.symm b)
    rw [show Fin.cast hP (Fin.cast hP.symm b) = b from Fin.ext rfl] at this
    exact this.symm
  have h1 := JCTx6.Int.orbit_slice_integrable k (D.ptSize h) 0 (r - D.ptSize (h ++ [(1, c)])) (D.ptPerm h) (D.ptDiag h) c
    (D.castV (by have := point_size_append_single h c; omega) z) (D.castV (by have := point_size_append_single h c; omega) z') E
    (D.castF (by have := point_size_append_single h c; omega) F) γ' hI
  have h2 := (Dx2.SL.phi_transport (k := k) (ρ := r - D.ptSize (h ++ [(1, c)])) hP.symm _ _ hσ' _ _ hd'
    (D.castV (by have := point_size_append_single h c; omega) z) (D.castV (by have := point_size_append_single h c; omega) z')
    (D.castF (by have := point_size_append_single h c; omega) F) γ').1 h1
  simpa only [Dx2.SL.castV_castV, Dx2.SL.castF_castF] using h2

end Formalism.FourierDecayAlt.P.PBH
end
end

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k : ℕ}

theorem asm_omLong_zero {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (β : ℂ) (Φ : G.Mat 1 → V) (z : ℂ) :
    G.OmLong β 0 Φ z = Φ (fun _ _ => z) := by
  unfold G.OmLong
  have : IsEmpty (G.UT (0 + 1)) := ⟨fun q => by have h := q.2; rw [Fin.lt_def] at h; omega⟩
  have hμ : G.muPi β (G.UT (0 + 1)) = Measure.dirac (fun q => isEmptyElim q) := Measure.pi_of_empty _ _
  rw [hμ, integral_dirac]
  have h1 : G.superSum (G.upper (fun q : G.UT (0 + 1) => isEmptyElim q)) = 0 := by
    simp [G.superSum]
  have h2 : (G.ptLong (0 + 1) z * G.upper (fun q : G.UT (0 + 1) => isEmptyElim q) : Matrix (Fin 1) (Fin 1) ℂ) =
      Matrix.of fun _ _ => z := by
    ext i j
    have hi : i = 0 := Fin.ext (by have := i.isLt; simp)
    have hj : j = 0 := Fin.ext (by have := j.isLt; simp)
    subst hi hj
    simp [G.ptLong, G.wMat, G.upper, G.strictUpper, Matrix.mul_apply]
  rw [h1, h2]
  simp [G.psi]
  rfl

theorem asm_psi_cast {a b : ℕ} (h : a = b) (z : Fin (2 * a + k + 1) → ℂ) (cc : ℂ) (g : B.Mat k a) :
    psi k b (D.castV h z) cc (D.castM h g) = psi k a z cc g := by
  subst h; rw [P.JCTx5.castV_rfl, P.JCTx5.castM_rfl]

theorem asm_castM_mul {a b : ℕ} (h : a = b) (g g' : B.Mat k a) : D.castM h (g * g') = D.castM h g * D.castM h g' := by
  subst h; simp only [P.JCTx5.castM_rfl]

theorem asm_castM_inv {a b : ℕ} (h : a = b) (g : B.Mat k a) : D.castM h g⁻¹ = (D.castM h g)⁻¹ := by
  subst h; simp only [P.JCTx5.castM_rfl]

theorem asm_castM_castM {a b d : ℕ} (h1 : a = b) (h2 : b = d) (g : B.Mat k a) :
    D.castM h2 (D.castM h1 g) = D.castM (h1.trans h2) g := by
  subst h1; subst h2; rfl

theorem asm_castM_symm {a b : ℕ} (h : a = b) (g : B.Mat k a) : D.castM h.symm (D.castM h g) = g := by
  subst h; simp only [P.JCTx5.castM_rfl]

theorem asm_lowV_lift (a ρ m r : ℕ) (hm : 1 + ρ = m) (h1 : a + m = r) (h5 : a + 1 + ρ = a + (1 + ρ))
    (er : r = a + 1 + ρ) (zj : Fin (2 * m + k + 1) → ℂ) :
    U.lowV k a (1 + ρ) (D.castV h5 (D.castV er (D.castV h1 (liftVec k a m zj)))) = D.castV hm.symm zj := by
  subst hm; subst h1
  funext i
  simp only [U.lowV, D.castV, liftVec, Fin.val_cast]
  rw [dite_eq_left (by omega)]
  congr 1; ext; simp

theorem asm_phiFun_lev {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {a r ρa ρb : ℕ} (e : ρa = ρb)
    (ha : r = a + 0 + ρa) (hb : r = a + 0 + ρb) (σ : Equiv.Perm (Fin a)) (d : Fin a → ℂ)
    (z0 z0' : Fin (2 * r + k + 1) → ℂ) (F0 : B.Mat k r → E) (g : B.Mat k ρa) :
    U.PhiFun (s := 0) k ρa σ d (D.castV ha z0) (D.castV ha z0') (D.castF ha.symm F0) (fun q => q.elim0) g =
      U.PhiFun (s := 0) k ρb σ d (D.castV hb z0) (D.castV hb z0') (D.castF hb.symm F0) (fun q => q.elim0)
        (D.castM e g) := by
  subst e; rw [P.JCTx5.castM_rfl]

theorem asm_bridge {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (a ρ1 ρ2 m r : ℕ) (e12 : ρ1 = ρ2) (e : ρ2 + 1 = m) (er : r = a + 1 + ρ1)
    (σ : Equiv.Perm (Fin a)) (d : Fin a → ℂ)
    (zb zb' : Fin (2 * r + k + 1) → ℂ) (zj zj' : Fin (2 * m + k + 1) → ℂ)
    (hzj : D.castV (show a + m = r by omega) (liftVec k a m zj) = zb)
    (hzj' : D.castV (show a + m = r by omega) (liftVec k a m zj') = zb')
    (Fb : B.Mat k r → E) (c : ℂ) (γ : B.Mat k ρ2)
    (zA zA' : Fin (2 * (a + 1 + ρ1) + k + 1) → ℂ) (hzA : zA = D.castV er zb) (hzA' : zA' = D.castV er zb')
    (FA : B.Mat k (a + 1 + ρ1) → E) (hFA : FA = D.castF er.symm Fb) (γ1 : B.Mat k ρ1)
    (hγ1 : γ1 = D.castM e12.symm γ) :
    ∫ yy : U.RC k 1 ρ1 × U.RC k 1 ρ1,
        (psi k (1 + ρ1) (U.lowV k a (1 + ρ1) (D.castV (by omega : a + 1 + ρ1 = a + (1 + ρ1)) zA)) cStd
            (U.Rn k 1 ρ1 yy.1) *
          star (psi k (1 + ρ1) (U.lowV k a (1 + ρ1) (D.castV (by omega : a + 1 + ρ1 = a + (1 + ρ1)) zA')) cStd
            (U.Rn k 1 ρ1 yy.2))) •
        U.PhiFun (p := a) (s := 0) k (1 + ρ1) σ d (D.castV (by omega : a + 1 + ρ1 = a + (1 + ρ1)) zA)
          (D.castV (by omega : a + 1 + ρ1 = a + (1 + ρ1)) zA') (D.castF (by omega : a + (1 + ρ1) = a + 1 + ρ1) FA)
          (fun q => q.elim0)
          ((U.Rn k 1 ρ1 yy.1)⁻¹ * U.mMap k 1 ρ1 (Matrix.of fun _ _ => c) γ1 * U.Rn k 1 ρ1 yy.2)
        ∂((U.muRC k 1 ρ1).prod (U.muRC k 1 ρ1)) =
      ∫ xx : U.RC k 1 ρ2 × U.RC k 1 ρ2,
        (psi k m zj cStd (rn1 e xx.1) * star (psi k m zj' cStd (rn1 e xx.2))) •
          U.PhiFun (p := a) (s := 0) k (r - a) σ d (D.castV (by omega : r = a + 0 + (r - a)) zb)
            (D.castV (by omega : r = a + 0 + (r - a)) zb') (D.castF (by omega : a + 0 + (r - a) = r) Fb)
            (fun q => q.elim0)
            (D.castM (by omega : m = r - a) ((rn1 e xx.1)⁻¹ * mc e c γ * rn1 e xx.2))
        ∂((U.muRC k 1 ρ2).prod (U.muRC k 1 ρ2)) := by
  subst e12; subst e; subst hzA; subst hzA'; subst hFA; subst hγ1; subst er
  rw [P.JCTx5.castM_rfl]
  refine integral_congr_ae (Filter.Eventually.of_forall fun xx => ?_)
  simp only [rn1, mc, P.JCTx5.castM_rfl]
  have hl := asm_lowV_lift (k := k) a ρ1 (ρ1 + 1) (a + 1 + ρ1) (by omega) (by omega) (by omega) rfl zj
  have hl' := asm_lowV_lift (k := k) a ρ1 (ρ1 + 1) (a + 1 + ρ1) (by omega) (by omega) (by omega) rfl zj'
  subst hzj; subst hzj'
  rw [hl, hl', ← asm_psi_cast (Nat.add_comm 1 ρ1) _ _ (U.Rn k 1 ρ1 xx.1),
    ← asm_psi_cast (Nat.add_comm 1 ρ1) _ _ (U.Rn k 1 ρ1 xx.2)]
  congr 1
  rw [← asm_castM_inv, ← asm_castM_mul, ← asm_castM_mul, asm_castM_castM]
  exact asm_phiFun_lev (by omega) _ _ σ d _ _ _ _

theorem asm_pointStepT (hPS : PointStep) : PointStepT := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj h c hh hc hF γ hγ
  obtain ⟨hhb, rfl⟩ := hh
  have hc0 : c ≠ 0 := (hc.1 (1, c) (List.mem_append_right _ (List.mem_singleton_self _))).2
  have hP' : D.ptSize (h ++ [(1, c)]) = D.ptSize h + 1 := Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append h 1 c
  have hloc : D.IsLocPt (h ++ [(1, c)]) (D.ptSize (h ++ [(1, c)])) := ⟨hc.1, rfl⟩
  have hlocH : D.IsLocPt h (D.ptSize h) := ⟨hhb, rfl⟩
  have hle : D.ptSize (h ++ [(1, c)]) ≤ P.r := by omega
  have e2 : D.ptSize h + (0 + 1) + (P.r - D.ptSize (h ++ [(1, c)])) = P.r := by omega
  have hFs : B.CkOn ⊤ (B.GV P.k (D.ptSize h + (0 + 1) + (P.r - D.ptSize (h ++ [(1, c)])))) (D.castF e2 F) :=
    Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_castF e2 hF.1
  obtain ⟨R, hR⟩ := hF.2.1
  have hRs : ∀ g ∈ B.GV P.k (D.ptSize h + (0 + 1) + (P.r - D.ptSize (h ++ [(1, c)]))), D.castF e2 F g ≠ 0 →
      B.gN g ≤ R := fun g hg hne => by
    have := hR _ (Formalism.FourierDecayAlt.P.PBE.castM_GV e2 hg) hne
    rwa [Formalism.FourierDecayAlt.P.PBE.gN_castM] at this
  have hγ' : D.castM (by omega : P.r - (D.ptSize h + 1) = P.r - D.ptSize (h ++ [(1, c)])) γ ∈
      B.GV P.k (P.r - D.ptSize (h ++ [(1, c)])) := Formalism.FourierDecayAlt.P.PBE.castM_GV _ hγ
  have hd0 : ∀ q, D.ptDiag h q ≠ 0 := fun q => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne h hlocH.1 q q.2
  have hI := asm_gInt_int (k := P.k) (D.ptSize h) (P.r - D.ptSize (h ++ [(1, c)])) (D.ptPerm h) (D.ptDiag h) c hd0 hc0
    (D.castV e2.symm p.T.base.z) (D.castV e2.symm p.T.base.z') (D.castF e2 F) hFs R hRs _ hγ'
  have hS := Formalism.FourierDecayAlt.P.slice_measure_identity P.k P.r (Wq →L[ℂ] Wp) p.T.base.z p.T.base.z' F h (h ++ [(1, c)]) 0 c rfl hle
    (D.castM (by omega : P.r - (D.ptSize h + 1) = P.r - D.ptSize (h ++ [(1, c)])) γ) hloc
    (integrable_slice_append_single p.T.base.z p.T.base.z' F h c hle hloc _ hI)
  rw [asm_omLong_zero] at hS
  have hPS' := hPS P.k (D.ptSize h) (P.r - D.ptSize (h ++ [(1, c)])) (D.ptPerm h) (D.ptDiag h) hd0 c hc0
    (D.castV (by omega) p.T.base.z) (D.castV (by omega) p.T.base.z')
    (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb _ _ p.T.base.z_mem) (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb _ _ p.T.base.z'_mem)
    (Wq →L[ℂ] Wp) (D.castF (by omega) F)
    (D.castM (by omega : P.r - (D.ptSize h + 1) = P.r - D.ptSize (h ++ [(1, c)])) γ)
    (integrable_unipotent_rank_one (k := P.k) (D.ptSize h) (P.r - D.ptSize (h ++ [(1, c)])) (D.ptPerm h) (D.ptDiag h) c _ _ _ _ hI)
  have hB := asm_bridge (k := P.k) (D.ptSize h) (P.r - D.ptSize (h ++ [(1, c)])) (P.r - (D.ptSize h + 1))
    (P.r - D.ptSize h) P.r (by omega) (by omega) (by omega) (D.ptPerm h) (D.ptDiag h) p.T.base.z p.T.base.z'
    (p.T.bs (D.ptSize h)).z (p.T.bs (D.ptSize h)).z' (p.T.z_lev _ (by omega)) (p.T.z'_lev _ (by omega)) F c γ
    _ _ rfl rfl _ rfl _ rfl
  have hπ : ((Real.pi ^ ((0 + 1) * 0 / 2) : ℝ) : ℂ) = 1 := by norm_num
  rw [hπ, one_smul] at hS
  refine ((show KB.slv p.T F (D.ptSize h + 1) hj [] (h ++ [(1, c)]) hc.2 (fun a => a.elim0) γ =
      D.sliceAt P.k P.r p.T.base.z p.T.base.z' F (h ++ [(1, c)])
        (D.castM (by omega : P.r - (D.ptSize h + 1) = P.r - D.ptSize (h ++ [(1, c)])) γ) from rfl).trans
    (hS.trans (hPS'.trans (hB.trans ?_))))
  refine integral_congr_ae (Filter.Eventually.of_forall fun xx => ?_)
  dsimp only
  congr 1
  show _ = D.sliceAt P.k P.r p.T.base.z p.T.base.z' F h (D.castM _ _)
  unfold D.sliceAt
  rw [dite_eq_left (by omega)]

end Formalism.FourierDecayAlt.P.PBH
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACProper
open Matrix MeasureTheory Topology
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem averaging_properness_holds : ACProper := by
  intro k r Wp Wq _ _ _ _ D C C' hC hC' hC'O
  have hW : IsCompact (UWset k r D.z) := Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r D.z D.z_mem D.T_pos
  have hW' : IsCompact (UWset k r D.z') := Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r D.z' D.z'_mem D.T'_pos
  have hgc : Continuous (B.gN : B.Mat k r → ℝ) := Formalism.FourierDecayAlt.P.B6.gN_continuous
  obtain ⟨MW, hMW⟩ := hW.exists_bound_of_continuousOn hgc.continuousOn
  obtain ⟨MW', hMW'⟩ := hW'.exists_bound_of_continuousOn hgc.continuousOn
  obtain ⟨MC, hMC⟩ := hC.exists_bound_of_continuousOn hgc.continuousOn
  obtain ⟨Co, hCo0, hCo⟩ := Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.orbit D.z D.z' C' hC' hC'O
  have gN_nn : ∀ M : B.Mat k r, 0 ≤ B.gN M := fun M => Real.sqrt_nonneg _
  have bnd : ∀ {s : Set (B.Mat k r)} {M : ℝ}, (∀ x ∈ s, ‖B.gN x‖ ≤ M) → ∀ x ∈ s, B.gN x ≤ M :=
    fun h x hx => (le_abs_self _).trans (h x hx)
  set Bd : ℝ := max MW 0 * max MC 0 * max MW' 0 with hBd
  set R : ℝ := max (max MW MW') (Co * Bd ^ (2 * r + 1)) with hR
  refine ⟨Metric.closedBall 0 (max R 0), isCompact_closedBall _ _, ?_⟩
  intro p hp g hg hsg
  obtain ⟨hh, hn, hh', hn'⟩ := hp
  set h : B.Mat k r := Matrix.of p.1.1
  set n : B.Mat k r := Matrix.of p.1.2
  set h' : B.Mat k r := Matrix.of p.2.1
  set n' : B.Mat k r := Matrix.of p.2.2
  have hdet : IsUnit h.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh.1
  have hdet' : IsUnit h'.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh'.1
  have hx : n⁻¹ * g * n' = h * B.sgs p g * h'⁻¹ := by
    have e1 : h * h⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
    have e2 : h' * h'⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet'
    calc n⁻¹ * g * n' = (h * h⁻¹) * (n⁻¹ * g * n') * (h' * h'⁻¹) := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]
      _ = h * (h⁻¹ * n⁻¹ * g * n' * h') * h'⁻¹ := by simp only [Matrix.mul_assoc]
  have hb : B.gN (n⁻¹ * g * n') ≤ Bd := by
    rw [hx]
    have h1 := bnd hMW h hh
    have h2 := bnd hMC _ hsg
    have h3 := bnd hMW' _ (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh')
    calc B.gN (h * B.sgs p g * h'⁻¹) ≤ B.gN (h * B.sgs p g) * B.gN h'⁻¹ := Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _
      _ ≤ B.gN h * B.gN (B.sgs p g) * B.gN h'⁻¹ :=
        mul_le_mul_of_nonneg_right (Formalism.FourierDecayAlt.P.B6.gN_mul_le _ _) (gN_nn _)
      _ ≤ max MW 0 * max MC 0 * max MW' 0 :=
        mul_le_mul (mul_le_mul (h1.trans (le_max_left _ _)) (h2.trans (le_max_left _ _)) (gN_nn _) (le_max_right _ _))
          (h3.trans (le_max_left _ _)) (gN_nn _) (mul_nonneg (le_max_right _ _) (le_max_right _ _))
  have hBd0 : 0 ≤ Bd := by positivity
  have hpow : B.gN (n⁻¹ * g * n') ^ (2 * r + 1) ≤ Bd ^ (2 * r + 1) := pow_le_pow_left₀ (gN_nn _) hb _
  obtain ⟨hon, hon'⟩ := hCo g hg n hn n' hn'
  have hnR : B.gN n ≤ max R 0 :=
    (hon.trans (mul_le_mul_of_nonneg_left hpow hCo0)).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hn'R : B.gN n' ≤ max R 0 :=
    (hon'.trans (mul_le_mul_of_nonneg_left hpow hCo0)).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hhR : B.gN h ≤ max R 0 :=
    (bnd hMW h hh).trans ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
  have hh'R : B.gN h' ≤ max R 0 :=
    (bnd hMW' h' hh').trans ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
  have sup : ∀ x : Mt k r, ‖x‖ ≤ B.gN (Matrix.of x) := fun x => Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm.sup_le_gN (Matrix.of x)
  rw [mem_closedBall_zero_iff]
  refine norm_prod_le_iff.2 ⟨norm_prod_le_iff.2 ⟨?_, ?_⟩, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩
  · exact (sup _).trans hhR
  · exact (sup _).trans hnR
  · exact (sup _).trans hh'R
  · exact (sup _).trans hn'R

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACHaarPos
open MeasureTheory
open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

variable {k r : ℕ}

theorem haar_pos_nhds_one {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ)
    (hinv : ∀ u ∈ U, u⁻¹ ∈ U) (hunit : ∀ u ∈ U, IsUnit u.det) {V : Set (Mt k r)} (hV : IsOpen V)
    (h1 : ((1 : B.Mat k r) : Mt k r) ∈ V) : 0 < μ V := by
  rw [pos_iff_ne_zero]
  intro h0
  let W : B.Mat k r → Set (Mt k r) := fun u => lmulM u⁻¹ ⁻¹' V
  have hWo : ∀ u ∈ U, IsOpen (W u) := fun u _ => hV.preimage (Formalism.FourierDecayAlt.P.B2x1.lmulM_cont _)
  have hW0 : ∀ u ∈ U, μ (W u) = 0 := by
    intro u hu
    have e := h.left u⁻¹ (hinv u hu)
    have := Measure.map_apply (μ := μ) (Formalism.FourierDecayAlt.P.B2x1.lmulM_cont (k := k) (r := r) u⁻¹).measurable hV.measurableSet
    rw [e] at this
    show μ (lmulM u⁻¹ ⁻¹' V) = 0
    rw [← this]; exact h0
  have hcov : (U : Set (Mt k r)) ⊆ ⋃ u ∈ U, W u := by
    intro x hx
    refine Set.mem_iUnion₂.2 ⟨x, hx, ?_⟩
    have e : (lmulM x⁻¹ x : Mt k r) = ((1 : B.Mat k r) : Mt k r) := by
      show x⁻¹ * x = 1
      exact Matrix.nonsing_inv_mul x (hunit x hx)
    show lmulM x⁻¹ x ∈ V
    rw [e]; exact h1
  obtain ⟨T, hTU, hTc, hTeq⟩ := TopologicalSpace.isOpen_biUnion_countable U W hWo
  have hU0 : μ (U : Set (Mt k r)) = 0 := by
    refine measure_mono_null (hcov.trans hTeq.symm.le) ?_
    exact (measure_biUnion_null_iff hTc).2 fun u hu => hW0 u (hTU hu)
  have huniv : μ Set.univ = 0 := by
    refine measure_mono_null ?_ (measure_union_null hU0 h.conc)
    intro x _
    by_cases hx : x ∈ (U : Set (Mt k r))
    · exact Or.inl hx
    · exact Or.inr hx
  exact h.ne_zero (Measure.measure_univ_eq_zero.1 huniv)

theorem averaging_haar_positivity : ACHaarPos := by
  intro k r Wp Wq _ _ _ _ D O hO h1
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarW'
  obtain ⟨A, B', hA, hB, hoA, hoB, hAB⟩ := isOpen_prod_iff.1 hO oneP.1 oneP.2 h1
  obtain ⟨V1, V2, hV1, hV2, ho1, ho2, h12⟩ := isOpen_prod_iff.1 hA oneP.1.1 oneP.1.2 hoA
  obtain ⟨V3, V4, hV3, hV4, ho3, ho4, h34⟩ := isOpen_prod_iff.1 hB oneP.2.1 oneP.2.2 hoB
  have hsub : (V1 ×ˢ V2) ×ˢ (V3 ×ˢ V4) ⊆ O :=
    (Set.prod_mono h12 h34).trans hAB
  have uwI : ∀ (w : Fin (2 * r + k + 1) → ℂ), ∀ u ∈ UWset k r w, u⁻¹ ∈ UWset k r w :=
    fun w u hu => Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hu
  have uwU : ∀ (w : Fin (2 * r + k + 1) → ℂ), ∀ u ∈ UWset k r w, IsUnit u.det :=
    fun w u hu => WeylGroupFacts.isUnit_of_uh hu.1
  have nI : ∀ u ∈ Nset k r, u⁻¹ ∈ Nset k r := fun u hu => WeylGroupFacts.mem_n_inv hu
  have nU : ∀ u ∈ Nset k r, IsUnit u.det := fun u hu => WeylGroupFacts.isUnit_of_uh hu.1
  have p1 := haar_pos_nhds_one D.haarW (uwI _) (uwU _) hV1 ho1
  have p2 := haar_pos_nhds_one D.haarN nI nU hV2 ho2
  have p3 := haar_pos_nhds_one D.haarW' (uwI _) (uwU _) hV3 ho3
  have p4 := haar_pos_nhds_one D.haarN nI nU hV4 ho4
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  show 0 < ((D.μW.prod D.μN).prod (D.μW'.prod D.μN)) ((V1 ×ˢ V2) ×ˢ (V3 ×ˢ V4))
  rw [Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
  rw [pos_iff_ne_zero] at p1 p2 p3 p4 ⊢
  exact mul_ne_zero (mul_ne_zero p1 p2) (mul_ne_zero p3 p4)

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadTopOfRadialExhaustion
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadTopOfParts
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadVectorOfParts
noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.PBI

def Exh : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (w : List C.Letter)
    (X : Q.ActualOps (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π')
    (μ : Measure (Mt P.k (P.r - P.r)))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π')) (JC.parLev P P.r).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π'))) (Cb : ℝ),
    P5.IsData (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' X μ L st p.l0 →
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → KB.CutWord P p.l0 w →
    ∀ (e : Wd.Ix (Fin w.length)) (h : C.LPt) (hh : D.IsLocPt h P.r),
      ∃ F₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp), KB.CptCoef p.T.base F₂ ∧
      (∀ ζ : ℂ, p.V (p.Θ.Θ w e F) (h ++ [(1, ζ)]) = p.V F₂ (h ++ [(1, ζ)])) ∧
      ∀ (Φ : Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
          (p.T.bs P.r).π (p.T.bs P.r).π'),
        (∀ e', Top.IsRadOf (JC.parLev P P.r) (p.T.bs P.r) (Φ e') (KB.slv p.T F P.r le_rfl w h hh.2 e')) →
        ∀ (c : Fin (JC.parLev P P.r).r → ℂ) (γ : B.Mat P.k (P.r - P.r)), γ ∈ B.GV P.k (P.r - P.r) →
          0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ →
          B.JF (p.T.bs P.r) (D.castF (by simp [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' F₂ h)) γ =
            (P5.act (Fr.ofWord L st (D.positionted w)).F Φ e :
              Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c γ

def HeadVecOfParts : Prop := HighestUnipotentIntegral → Exh → HeadVec

end Formalism.FourierDecayAlt.P.PBI

namespace Formalism.FourierDecayAlt.P

theorem head_vector_of_parts : PBI.HeadVecOfParts := by
  intro hU5 hExh Wp Wq _ _ _ _ _ _ P p F w X μ L st Cb ν'r m₀r hD hdd hF hcut hLev x hx γ₀ hγG hζ hγF h hh Φ hΦ e
  obtain ⟨F₂, hF₂, hV, hJ⟩ := hExh Wp Wq P p F w X μ L st Cb hD hdd hF hcut e h hh
  set ζ := Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2 with hζdef
  have hr : P.r - P.r = 0 := by omega
  have hGx : 0 < Complex.normSq ζ - Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z' :=
    hx.2.2
  have hζ0 : ζ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hGx
    nlinarith [mul_pos (p.T.bs P.r).T_pos (p.T.bs P.r).T'_pos]
  have hZ : Zhat P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ₀ = D.ptMatN [(1, ζ)] (P.r - P.r + 1) := by
    ext a b
    have ha : a = Fin.last _ := Fin.ext (by have := a.isLt; simp only [Fin.val_last]; omega)
    have hb : b = Fin.last _ := Fin.ext (by have := b.isLt; simp only [Fin.val_last]; omega)
    subst ha hb
    rw [← PBI.zetaL_eq_zhat, hζ]
    simp [D.ptMatN, D.ptEntry, hr]
  have hγGG : 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ₀ := by
    show 0 < Complex.normSq (Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀) -
      Tz P.k (P.r - P.r) (p.T.bs P.r).z * Tz P.k (P.r - P.r) (p.T.bs P.r).z'
    rw [hζ]; exact hGx
  show p.V (p.Θ.Θ w e F) (h ++ [(1, ζ)]) = _
  rw [hV, hU5 Wp Wq P p F₂ h ζ hh ν'r m₀r hF₂ hζ0 hLev.1 hLev.2.1,
    PBM.vector_level_zero_eq_jacquet hr (p.T.bs P.r) ν'r m₀r hLev.2.2 _ ζ (by linarith) γ₀ hγG hZ hγF]
  exact hJ Φ hΦ x.1 γ₀ hγG hγGG

end Formalism.FourierDecayAlt.P
end
end

namespace Formalism.FourierDecayAlt.P

def PBI.HeadTopOfParts : Prop := PBI.HighestUnipotentIntegral → PBI.Exh → PBI.HeadWeightAt → KB.HeadTop

theorem head_top_of_parts : PBI.HeadTopOfParts := fun hU5 hExh hW =>
  head_top_of_correspondence (head_correspondence_of_parts levFrameExists_statement (head_vector_of_parts hU5 hExh)
    (head_types_of_types_at (head_types_at_of_weight hW)))

end Formalism.FourierDecayAlt.P
end

noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.PBI

def ExhPic : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (w : List C.Letter)
    (X : Q.ActualOps (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π')
    (μ : Measure (Mt P.k (P.r - P.r)))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π')) (JC.parLev P P.r).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π'))) (Cb : ℝ)
    (X₀ : Q.ActualOps P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π') (μ₀ : Measure (Mt P.k P.r))
    (L₀ : R.LevelData (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π')) P.r)
    (st₀ : Fr.Start (Q.Pr (Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π'))),
    P5.IsData (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' X μ L st p.l0 →
    P5.IsData P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' X₀ μ₀ L₀ st₀ p.l0 →
    KB.IsTopLift2 P p.l0 p.T.base L₀ st₀ p.Θ →
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → KB.CutWord P p.l0 w →
    ∀ (e : Wd.Ix (Fin w.length)) (h : C.LPt) (hh : D.IsLocPt h P.r),
      ∃ F₁ F₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp), KB.CptCoef p.T.base F₁ ∧ KB.CptCoef p.T.base F₂ ∧
      (∀ ζ : ℂ, p.V (p.Θ.Θ w e F) (h ++ [(1, ζ)]) = p.V (p.Θ.Θ w e F₁) (h ++ [(1, ζ)])) ∧
      (∀ Φ₁ : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π', Top.IsRadOf P p.T.base Φ₁ F₁ →
        Top.IsRadOf P p.T.base
          (P5.act ((Fr.ofWord L₀ st₀ (D.positionted w)).F * P5.bTall L₀ (D.positionted w)) (Top.firstStateVector Φ₁) e) F₂) ∧
      ∀ (Φ : Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
          (p.T.bs P.r).π (p.T.bs P.r).π'),
        (∀ e', Top.IsRadOf (JC.parLev P P.r) (p.T.bs P.r) (Φ e') (KB.slv p.T F P.r le_rfl w h hh.2 e')) →
        ∀ (c : Fin (JC.parLev P P.r).r → ℂ) (γ : B.Mat P.k (P.r - P.r)), γ ∈ B.GV P.k (P.r - P.r) →
          0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ →
          B.JF (p.T.bs P.r) (D.castF (by simp [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' F₂ h)) γ =
            (P5.act (Fr.ofWord L st (D.positionted w)).F Φ e :
              Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c γ

end Formalism.FourierDecayAlt.P.PBI

namespace Formalism.FourierDecayAlt.P

theorem exhaustion_of_radial_form : PBI.ExhPic → PBI.Exh := by
  intro hPic Wp Wq _ _ _ _ _ _ P p F w X μ L st Cb hD hdd hF hcut e h hh
  obtain ⟨X₀, μ₀, L₀, st₀, hD₀, hTL⟩ := p.hΘ
  obtain ⟨F₁, F₂, hF₁, hF₂, hloc, hpic, hii⟩ :=
    hPic Wp Wq P p F w X μ L st Cb X₀ μ₀ L₀ st₀ hD hD₀ hTL hdd hF hcut e h hh
  obtain ⟨F', hF', hagree, hVeq⟩ := theta_compact_support Wp Wq P p F₁ w e Cb hdd hF₁ hcut
  refine ⟨F₂, hF₂, fun ζ => ?_, hii⟩
  obtain ⟨Φ₁, hΦ₁⟩ := PBN.radExists p hF₁
  have hΘpic := hTL w hcut F₁ hF₁ Φ₁ hΦ₁ e
  have hF'pic := PBN.isRadOf_congr p.T.base hΘpic hagree
  rw [hloc ζ, hVeq]
  exact PBN.vecV_eq_of_rad density_constant p hF' hF₂ hF'pic (hpic Φ₁ hΦ₁) _

theorem head_top_of_radial_exhaustion (hU5 : PBI.HighestUnipotentIntegral) (hPic : PBI.ExhPic) (hW : PBI.HeadWeightAt) : KB.HeadTop :=
  head_top_of_parts hU5 (exhaustion_of_radial_form hPic) hW

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeAction0
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def cay {k r : ℕ} (X : B.Mat k r) : B.Mat k r := (1 + X) * (1 - X)⁻¹

def cayInv {k r : ℕ} (g : B.Mat k r) : B.Mat k r := (g - 1) * (g + 1)⁻¹

def LieBasis : Prop :=
  ∀ k r : ℕ, ∃ (d : ℕ) (L : (Fin d → ℝ) →L[ℝ] B.Mat k r) (M : B.Mat k r →L[ℝ] (Fin d → ℝ)),
    (∀ x, B.inLie k r (L x)) ∧ (∀ x, M (L x) = x) ∧ ∀ X, B.inLie k r X → L (M X) = X

def CayAlg : Prop :=
  ∀ k r : ℕ,
    (∀ X : B.Mat k r, B.inLie k r X → IsUnit (1 - X) → cay X ∈ B.GV k r ∧ IsUnit (cay X + 1) ∧ cayInv (cay X) = X) ∧
    ∀ g ∈ B.GV k r, IsUnit (g + 1) → B.inLie k r (cayInv g) ∧ IsUnit (1 - cayInv g) ∧ cay (cayInv g) = g

def GVGrp : Prop :=
  ∀ k r : ℕ, IsUnit ((1 : B.Mat k r) + 1) ∧ ∀ g₀ ∈ B.GV k r, g₀⁻¹ * g₀ = 1 ∧
    ∀ h ∈ B.GV k r, g₀ * h ∈ B.GV k r ∧ g₀⁻¹ * h ∈ B.GV k r ∧ g₀ * (g₀⁻¹ * h) = h

def CaySmooth : Prop :=
  ∀ (k r : ℕ) (g₀ : B.Mat k r),
    IsOpen {X : B.Mat k r | IsUnit (1 - X)} ∧ IsOpen {m : B.Mat k r | IsUnit (g₀⁻¹ * m + 1)} ∧
    ContDiffOn ℝ ∞ (fun X : B.Mat k r => g₀ * cay X) {X | IsUnit (1 - X)} ∧
    ContDiffOn ℝ ∞ (fun m : B.Mat k r => cayInv (g₀⁻¹ * m)) {m | IsUnit (g₀⁻¹ * m + 1)}

theorem gChart_of (hB : LieBasis) (hA : CayAlg) (hG : GVGrp) (hS : CaySmooth) : GChart := by
  intro k r
  obtain ⟨d, L, M, hL, hML, hLM⟩ := hB k r
  refine ⟨d, fun g₀ hg₀ => ?_⟩
  obtain ⟨hA1, hA2⟩ := hA k r
  obtain ⟨hOne, hGg⟩ := hG k r
  obtain ⟨hinv, hmul⟩ := hGg g₀ hg₀
  obtain ⟨hO1, hU1, hκs, hΦs⟩ := hS k r g₀
  refine ⟨{x | IsUnit (1 - L x)}, {m | IsUnit (g₀⁻¹ * m + 1)}, fun x => g₀ * cay (L x),
    fun m => M (cayInv (g₀⁻¹ * m)), hO1.preimage L.continuous, hU1, ?_, ?_, ?_, ?_, ?_⟩
  · show IsUnit (g₀⁻¹ * g₀ + 1)
    rw [hinv]; exact hOne
  · exact hκs.comp L.contDiff.contDiffOn (fun x hx => hx)
  · exact M.contDiff.comp_contDiffOn hΦs
  · intro x hx
    obtain ⟨hc, hc1, hci⟩ := hA1 (L x) (hL x) hx
    have e : g₀⁻¹ * (g₀ * cay (L x)) = cay (L x) := by
      rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
    refine ⟨(hmul _ hc).1, ?_, ?_⟩
    · show IsUnit (g₀⁻¹ * (g₀ * cay (L x)) + 1)
      rw [e]; exact hc1
    · show M (cayInv (g₀⁻¹ * (g₀ * cay (L x)))) = x
      rw [e, hci, hML]
  · intro g hg hgG
    obtain ⟨-, hh, hgh⟩ := hmul g hgG
    obtain ⟨hl, hu, hc⟩ := hA2 _ hh hg
    refine ⟨?_, ?_⟩
    · show IsUnit (1 - L (M (cayInv (g₀⁻¹ * g))))
      rw [hLM _ hl]; exact hu
    · show g₀ * cay (L (M (cayInv (g₀⁻¹ * g)))) = g
      rw [hLM _ hl, hc, hgh]

def IsDomOmPlus : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), inWb k r z → inWb k r z' →
    Q.IsDom k r z z' 0 (Q.OmPlus k r z z')

def RightTypeAction0 : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    [FiniteDimensional ℂ Wq]
    (k r m : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (mm : ℕ∞), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    IsCRepOn (UWset k r z') π' → ContinuousOn π' (UWset k r z') →
    ∀ J ∈ Gr.FFlM mm k r z z' π π' 0 D, ∀ g ∈ Q.Glev k r 0 ∩ D,
    ∀ Bs : Fin m → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [z'] Bs → ∀ (w : ℂ) (v : Wq),
      Q.capR k r Bs w J g v = J g (Q.capRep k r π' Bs w v)

def LeftTypeAction0 : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    [FiniteDimensional ℂ Wp]
    (k r m : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (mm : ℕ∞), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    IsCRepOn (UWset k r z) π → ContinuousOn π (UWset k r z) →
    ∀ J ∈ Gr.FFlM mm k r z z' π π' 0 D, ∀ g ∈ Q.Glev k r 0 ∩ D,
    ∀ Bs : Fin m → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [z] Bs → ∀ (w : ℂ) (v : Wq),
      Q.capLft k r Bs w J g v = Q.capRep k r π Bs w (J g v)

theorem uCap_of (h0 : IsDomOmPlus) (hR : RightTypeAction0) (hL : LeftTypeAction0) : UCap := by
  intro k r Wp Wq _ _ _ _ _ _ D u u' J hT hT' hF
  have hD := h0 k r D.z D.z' D.z_mem D.z'_mem
  have hg0 : ∀ g ∈ JF.Om k r D.z D.z', g ∈ Q.Glev k r 0 ∩ Q.OmPlus k r D.z D.z' :=
    fun g hg => ⟨⟨hg.1, fun a ha => absurd ha (Nat.not_lt_zero _)⟩, hg.2⟩
  refine ⟨fun Bs hBs w => ⟨∏ i ∈ Finset.Icc 1 k, (w - (k : ℂ) / 2 + 1 / 2 + (u i : ℂ)), fun g hg => ?_⟩,
    fun Bs hBs w => ⟨∏ i ∈ Finset.Icc 1 k, (w - (k : ℂ) / 2 + 1 / 2 + (u' i : ℂ)), fun g hg => ?_⟩⟩
  · refine ContinuousLinearMap.ext fun v => ?_
    rw [hL Wp Wq k r k D.z D.z' D.π D.π' _ _ D.z_mem D.z'_mem hD hT.2.1 hT.2.2.1 J hF g (hg0 g hg) Bs hBs w v,
      hT.2.2.2.2.2 Bs hBs w (J g v)]
    rfl
  · refine ContinuousLinearMap.ext fun v => ?_
    rw [hR Wp Wq k r k D.z D.z' D.π D.π' _ _ D.z_mem D.z'_mem hD hT'.2.1 hT'.2.2.1 J hF g (hg0 g hg) Bs hBs w v,
      hT'.2.2.2.2.2 Bs hBs w v, map_smul]
    rfl

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end
