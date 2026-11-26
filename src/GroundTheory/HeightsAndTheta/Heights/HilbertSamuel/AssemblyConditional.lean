module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Assembly
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockComplexGramMetricChange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ATeleSt
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageDatum
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockRealGramComparison
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComplexGramMetricChange

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsReductionToProjectiveBlock
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def ReductionToProjectiveBlock.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (I : AllFam) (d : HSMBlockDatum D K ι Ω),
    I.IsFamily →
    (fun n => hsDefect D (blockChi d) (I K ι (mCoordIdeal d.y) (D + 1) fun _ => d.A) n -
        (genDeg (mCoordIdeal d.y) D d.A.a : ℝ) * hsDefect D (chiP D) (hhOf I D) n) =o[atTop] pw D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFrameChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def FrameChange.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ),
    ∃ (B : Matrix (Ix κ) (Ix κ) ℚ) (d' : HSMDatum D Ω κ) (e : Fin (D + 1) → Ix κ),
      IsInvMat B ∧ d'.x = matAct B d.x ∧ (∀ z, d'.m.ρ (matActC B z) = d.m.ρ z) ∧ IsProjFrame d'.x e ∧
      (fun n => resChi d' n - resChi d n - latLogIndex d.x d'.x n) =o[atTop] pw D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDefectMetricChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

theorem top_sub_top_mixPot (I : AllFam) (hI : I.IsFamily) {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type}
    [Fintype κ] {x : Ix κ → Ω} {m₀ m₁ : ConeMetric ℂ (Ix κ)}
    (hP : IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1)) (hs₀ : IsSmoothMetric m₀)
    (hs₁ : IsSmoothMetric m₁) :
    top I x m₁ D - top I x m₀ D = ∑ i ∈ Finset.range (D + 1),
      ptsIntegral (ι := GlobalTheory κ) (coordIdeal ℤ x) (mixPot m₀ m₁ D i) (logRatio m₀ m₁) := by
  classical
  have hB := tele_smooth_ratio hs₀ hs₁
  have hsymm := (hI Unit (GlobalTheory κ)).1
  have hadd := (hI Unit (GlobalTheory κ)).2.1
  have htel := Finset.sum_range_sub
    (fun i => I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1) (tele_fam m₀ m₁ (D + 1) i)) (D + 1)
  have hT0 : tele_fam m₀ m₁ (D + 1) 0 = fun _ => HermLine.ofCone m₀ := by
    funext j
    simp [tele_fam]
  have hT1 : tele_fam m₀ m₁ (D + 1) (D + 1) = fun _ => HermLine.ofCone m₁ := by
    funext j
    simp [tele_fam, j.isLt]
  simp only [hT0, hT1] at htel
  unfold top
  rw [← htel]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have e1 : I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1) (tele_fam m₀ m₁ (D + 1) (i + 1)) =
      I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1)
        (Fin.snoc (tele_fam m₀ m₁ D i) (HermLine.ofCone m₁)) := by
    rw [← tele_fam_succAbove m₀ m₁ D i hi (i + 1) (Or.inr rfl)]
    have : HermLine.ofCone m₁ = tele_fam m₀ m₁ (D + 1) (i + 1) ⟨i, hi⟩ := by
      simp [tele_fam]
    rw [this, ← tele_comp_perm]
    exact (hsymm _ _ _ _ hP (tele_fam_smooth hs₀ hs₁ _ _)).symm
  have e0 : I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1) (tele_fam m₀ m₁ (D + 1) i) =
      I Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1)
        (Fin.snoc (tele_fam m₀ m₁ D i) (HermLine.ofCone m₀)) := by
    rw [← tele_fam_succAbove m₀ m₁ D i hi i (Or.inl rfl)]
    have : HermLine.ofCone m₀ = tele_fam m₀ m₁ (D + 1) i ⟨i, hi⟩ := by
      simp [tele_fam]
    rw [this, ← tele_comp_perm]
    exact (hsymm _ _ _ _ hP (tele_fam_smooth hs₀ hs₁ _ _)).symm
  rw [e1, e0, tele_ofCone_tensor m₀ m₁,
    hadd _ _ _ _ _ hP (tele_fam_smooth hs₀ hs₁ _ _) (tele_smooth_ofCone hs₀) hB,
    add_sub_cancel_left, fam_degZero I hI hP _ (tele_fam_smooth hs₀ hs₁ _ _) _ hB rfl]
  have hpot : pot (tele_fam m₀ m₁ D i) = mixPot m₀ m₁ D i := by
    funext j z
    simp only [pot, mixPot, tele_fam]
    split_ifs <;> rfl
  rw [hpot]
  rfl

theorem DefectMetricChange.proof (hR : RealGramComparison.Statement)
    (hC : ComplexGramMetricChange.Statement) (hM : ResolutionMixedIntegral.Statement) :
    DefectMetricChange.Statement := by
  intro D Ω _ _ κ _ I d m₁ P0₁ hs hc hle hp e hI he
  have h₁ := hR D Ω κ (d.withMetric m₁ P0₁ hs hc hle hp) e he
  have h₀ := hR D Ω κ d e he
  have hc₁ := hC D Ω κ d m₁ P0₁ hs hc hle hp e he
  have htop : top I d.x m₁ D = top I d.x d.m D + ((D : ℝ) + 1) * resMetricInt d m₁ := by
    rw [← hM D Ω κ d m₁ hs, ← top_sub_top_mixPot I hI d.arith d.smooth hs]
    ring
  have hlog := isLittleO_pow_mul_log D
  refine (((h₁.trans_isLittleO hlog).sub (h₀.trans_isLittleO hlog)).add hc₁).congr_left fun n => ?_
  simp only [hsDefect, htop, Nat.factorial_succ]
  push_cast
  field_simp
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTopPullFS
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace TopPullFS

variable {κ : Type} [Fintype κ] {D : ℕ}

theorem linApply_projMat (e : Fin (D + 1) → Ix κ) (z : Ix κ → ℂ) (k : Fin (D + 1)) :
    linApply (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) z ⟨(), k⟩ = z (e k) := by
  classical
  simp only [linApply, projMat]
  rw [Finset.sum_eq_single (e k).2]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

theorem isSmoothHerm_ofCone {m : ConeMetric ℂ (Ix κ)} (hm : IsSmoothMetric m) :
    IsSmoothHerm (HermLine.ofCone m) := by
  refine hm.mono fun z hz => ?_
  obtain ⟨i, hi⟩ := hz ()
  exact fun h0 => hi (congrFun h0 _)

theorem fs_linApply (e : Fin (D + 1) → Ix κ) (z : Ix κ → ℂ) :
    (HermLine.ofCone (fsMetric (ι := Ix (Fin (D + 1))))).h
        (linApply (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) z) =
      Real.sqrt (∑ k, ‖z (e k)‖ ^ 2) := by
  simp only [HermLine.ofCone, fsMetric, EuclideanSpace.norm_eq]
  congr 1
  rw [Fintype.sum_sigma, Fintype.sum_unique]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [linApply_projMat]

end TopPullFS


open TopPullFS in
theorem TopPullFS.proof (hCM : ChangeOfModelStatement) (hBP : ProjFrameBasePtFree.Statement)
    (hIm : ProjFrameImage.Statement) (hDeg : ProjFrameGraphDeg.Statement) : TopPullFS.Statement := by
  intro D Ω _ _ κ _ I x m e hI hP hm hfr hFS
  obtain ⟨G, J, hJ, hJe⟩ := hDeg D Ω κ x e hP hfr
  have himg := hIm D Ω κ x e hfr
  have hSmoothFS : IsSmoothHerm (HermLine.ofCone (fsMetric (ι := Ix (Fin (D + 1))))) := by
    apply isSmoothHerm_ofCone
    intro z hz
    change ContDiffWithinAt ℝ _ (fun w : Ix (Fin (D + 1)) → ℂ => ‖WithLp.toLp 2 w‖) _ z
    have hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (WithLp.toLp 2 : (Ix (Fin (D + 1)) → ℂ) → _) :=
      PiLp.contDiff_toLp
    have hz' : WithLp.toLp 2 z ≠ 0 := by simpa using hz
    exact (hL.contDiffAt.norm ℂ hz').contDiffWithinAt
  have key := hCM I hI Unit (GlobalTheory κ) (GlobalTheory (Fin (D + 1))) (coordIdeal ℤ x) (D + 1) (projMat e) G J
    (fun _ => HermLine.ofCone (fsMetric (ι := Ix (Fin (D + 1))))) (fun _ => HermLine.ofCone m) hP
    (hBP D Ω κ x e hfr) (by rw [himg]; exact IndefiniteRowSideFullHecke.Inter.isArithVar_bot D) hJ
    (fun _ => hSmoothFS) (fun _ => isSmoothHerm_ofCone hm) (fun _ => rfl)
    (fun _ z hz => by
      rw [fs_linApply]
      exact hFS z ⟨fun h0 => by obtain ⟨i, hi⟩ := hz.1 (); exact hi (congrFun h0 _), hz.2⟩)
  rw [himg, hJe] at key
  simpa [top, hhOf] using key

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockDefectMetricChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics MeasureTheory

noncomputable section

set_option linter.unusedSectionVars false

section Telescoping

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def quotLine (C A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (ha : A.a = C.a) : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι where
  a := 0
  h z := A.h z / C.h z
  pos z hz := div_pos (A.pos z hz) (C.pos z hz)
  smul c z hc := by
    rw [A.smul c z hc, C.smul c z hc, ha]
    have hne : (∏ k, ‖c k‖ ^ C.a k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
    rw [mul_div_mul_left _ _ hne]
    simp

theorem tensor_quotLine (C A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (ha : A.a = C.a) (hv : ∀ z, C.h z = 0 → A.h z = 0) :
    C.tensor (quotLine C A ha) = A := by
  apply tele_herm_ext
  · funext k
    simp [ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, quotLine, ha]
  · funext z
    show C.h z * (A.h z / C.h z) = A.h z
    by_cases h0 : C.h z = 0
    · rw [h0, hv z h0, zero_mul]
    · exact mul_div_cancel₀ _ h0

theorem isSmoothHerm_quotLine {C A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (ha : A.a = C.a) (hC : IsSmoothHerm C) (hA : IsSmoothHerm A) :
    IsSmoothHerm (quotLine C A ha) :=
  hA.div hC fun z hz => (C.pos z hz).ne'

theorem fam_degZero_block (I : AllFam) (hI : I.IsFamily) {P : Ideal (MRing ι)} {n : ℕ}
    (hP : IsArithVar P (n + 1)) (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hL : ∀ j, IsSmoothHerm (L j))
    (B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hB : IsSmoothHerm B) (hB0 : B.a = 0) :
    I K ι P (n + 1) (Fin.snoc L B) = ptsIntegral P (pot L) fun z => Real.log (B.h z) := by
  classical
  have hR := (hI K ι).2.2 P n L B 1 0 hP hL hB (fun k => by simp [hB0])
    tele_one_homog (fun h1 => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr h1))
  rw [hR]
  unfold recR
  rw [tele_divSupp_one, finsum_mem_empty, zero_sub]
  unfold arInt
  have hl : logNorm B 1 = fun z => - Real.log (B.h z) := by
    funext z
    simp [logNorm, Real.log_inv]
  rw [hl, tele_ptsIntegral_neg, neg_neg]
  rfl

theorem ptsIntegral_log_sub (hInt : PtsIntegrableStatement) {P : Ideal (MRing ι)} {e : ℕ}
    (hP : IsArithVar P (e + 1)) (L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hL : ∀ j, IsSmoothHerm (L j))
    (B₀ B₁ : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (h₀ : IsSmoothHerm B₀) (h₁ : IsSmoothHerm B₁) (h₀a : B₀.a = 0) (h₁a : B₁.a = 0)
    (g : ((Σ k, ι k) → ℂ) → ℝ) (hg : ∀ z ∈ mcPts P, g z = Real.log (B₁.h z) - Real.log (B₀.h z)) :
    ptsIntegral P (pot L) (fun z => Real.log (B₁.h z)) - ptsIntegral P (pot L) (fun z => Real.log (B₀.h z)) =
      ptsIntegral P (pot L) g := by
  classical
  have hl : ∀ B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, (fun z => Real.log (B.h z)) = fun z => - logNorm B 1 z := by
    intro B
    funext z
    simp [logNorm, Real.log_inv]
  have hP1 : (1 : MRing ι) ∉ P := fun h1 => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr h1)
  have hsec : ∀ B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, B.a = 0 → IsSectionOn P B 1 := fun B hB =>
    ⟨0, fun k => by simp [hB], tele_one_homog, hP1⟩
  rw [hl B₁, hl B₀, tele_ptsIntegral_neg, tele_ptsIntegral_neg]
  unfold ptsIntegral
  split_ifs with hΨ
  · have hΨg : IsGoodProj P hΨ.choose := hΨ.choose_spec
    unfold ptsIntegralAt
    rw [neg_sub_neg, ← integral_sub (hInt K ι P e _ L B₀ 1 hP hΨg hL h₀ (hsec B₀ h₀a))
      (hInt K ι P e _ L B₁ 1 hP hΨg hL h₁ (hsec B₁ h₁a))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    rw [← finsum_mem_sub_distrib _ _ (fibreFinite K ι P e _ hP hΨg y)]
    refine finsum_mem_congr rfl fun w _ => ?_
    unfold sheetDensity
    split_ifs with hγ
    · have hz : hγ.choose y ∈ mcPts P := hγ.choose_spec.2.self_of_nhds.2.1
      rw [hg _ hz]
      simp only [logNorm, map_one, norm_one, one_div, Real.log_inv]
      ring
    · simp
  · simp

def blockTeleFam (A A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (N i : ℕ) : Fin N → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι :=
  fun j => if j.val < i then A' else A

theorem blockTeleFam_succAbove (A A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (D i : ℕ) (hi : i < D + 1) (k : ℕ) (hk : k = i ∨ k = i + 1) :
    blockTeleFam A A' (D + 1) k ∘ (⟨i, hi⟩ : Fin (D + 1)).succAbove = blockTeleFam A A' D i := by
  funext j
  simp only [Function.comp_apply, blockTeleFam]
  by_cases h : j.val < i
  · have h' : Fin.castSucc j < (⟨i, hi⟩ : Fin (D + 1)) := by
      rw [Fin.lt_def]
      exact h
    rw [Fin.succAbove_of_castSucc_lt _ _ h', if_pos (show (Fin.castSucc j).val < k by
      show j.val < k
      omega), if_pos h]
  · have h' : (⟨i, hi⟩ : Fin (D + 1)) ≤ Fin.castSucc j := by
      rw [Fin.le_def]
      show i ≤ j.val
      omega
    rw [Fin.succAbove_of_le_castSucc _ _ h', if_neg (show ¬ (Fin.succ j).val < k by
      show ¬ j.val + 1 < k
      omega), if_neg h]

theorem blockTeleFam_smooth {A A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A) (hA' : IsSmoothHerm A') (N i : ℕ)
    (j : Fin N) : IsSmoothHerm (blockTeleFam A A' N i j) := by
  unfold blockTeleFam
  split_ifs
  · exact hA'
  · exact hA

theorem top_sub_top_blockMixPot (hInt : PtsIntegrableStatement) (I : AllFam) (hI : I.IsFamily)
    {P : Ideal (MRing ι)} {D : ℕ} (hP : IsArithVar P (D + 1)) {A A' C : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A)
    (hA' : IsSmoothHerm A') (hC : IsSmoothHerm C) (ha : A.a = C.a) (ha' : A'.a = C.a)
    (hv : ∀ z, C.h z = 0 → A.h z = 0) (hv' : ∀ z, C.h z = 0 → A'.h z = 0) :
    I K ι P (D + 1) (fun _ => A') - I K ι P (D + 1) (fun _ => A) = ∑ i ∈ Finset.range (D + 1),
      ptsIntegral P (blockMixPot A A' D i) fun z => Real.log (A'.h z / A.h z) := by
  classical
  have hsymm := (hI K ι).1
  have hadd := (hI K ι).2.1
  have hB₀ := isSmoothHerm_quotLine ha hC hA
  have hB₁ := isSmoothHerm_quotLine ha' hC hA'
  have htel := Finset.sum_range_sub (fun i => I K ι P (D + 1) (blockTeleFam A A' (D + 1) i)) (D + 1)
  have hT0 : blockTeleFam A A' (D + 1) 0 = fun _ => A := by
    funext j
    simp [blockTeleFam]
  have hT1 : blockTeleFam A A' (D + 1) (D + 1) = fun _ => A' := by
    funext j
    simp [blockTeleFam, j.isLt]
  simp only [hT0, hT1] at htel
  rw [← htel]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hLs := blockTeleFam_smooth hA hA' D i
  have e1 : I K ι P (D + 1) (blockTeleFam A A' (D + 1) (i + 1)) =
      I K ι P (D + 1) (Fin.snoc (blockTeleFam A A' D i) A') := by
    have h := hsymm _ _ (blockTeleFam A A' (D + 1) (i + 1)) (tele_perm ⟨i, hi⟩) hP
      (blockTeleFam_smooth hA hA' _ _)
    have hv1 : blockTeleFam A A' (D + 1) (i + 1) ⟨i, hi⟩ = A' := by
      simp [blockTeleFam]
    rw [tele_comp_perm, blockTeleFam_succAbove A A' D i hi (i + 1) (Or.inr rfl), hv1] at h
    exact h.symm
  have e0 : I K ι P (D + 1) (blockTeleFam A A' (D + 1) i) =
      I K ι P (D + 1) (Fin.snoc (blockTeleFam A A' D i) A) := by
    have h := hsymm _ _ (blockTeleFam A A' (D + 1) i) (tele_perm ⟨i, hi⟩) hP
      (blockTeleFam_smooth hA hA' _ _)
    have hv0 : blockTeleFam A A' (D + 1) i ⟨i, hi⟩ = A := by
      simp [blockTeleFam]
    rw [tele_comp_perm, blockTeleFam_succAbove A A' D i hi i (Or.inl rfl), hv0] at h
    exact h.symm
  have hpot : pot (blockTeleFam A A' D i) = blockMixPot A A' D i := by
    funext j z
    simp only [pot, blockMixPot, blockTeleFam]
    split_ifs <;> rfl
  rw [e1, e0]
  have q1 : (Fin.snoc (α := fun _ => ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (blockTeleFam A A' D i) A') =
      Fin.snoc (α := fun _ => ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (blockTeleFam A A' D i) (C.tensor (quotLine C A' ha')) := by
    rw [tensor_quotLine C A' ha' hv']
  have q0 : (Fin.snoc (α := fun _ => ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (blockTeleFam A A' D i) A) =
      Fin.snoc (α := fun _ => ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (blockTeleFam A A' D i) (C.tensor (quotLine C A ha)) := by
    rw [tensor_quotLine C A ha hv]
  rw [q1, q0]
  rw [hadd _ _ _ _ _ hP hLs hC hB₁, hadd _ _ _ _ _ hP hLs hC hB₀, add_sub_add_left_eq_sub,
    fam_degZero_block I hI hP _ hLs _ hB₁ rfl, fam_degZero_block I hI hP _ hLs _ hB₀ rfl,
    ptsIntegral_log_sub hInt hP _ hLs _ _ hB₀ hB₁ rfl rfl (fun z => Real.log (A'.h z / A.h z)) ?_, hpot]
  intro z hz
  have hA0 := A.pos z hz.1
  have hA'0 := A'.pos z hz.1
  have hC0 := C.pos z hz.1
  show Real.log (A'.h z / A.h z) = Real.log (A'.h z / C.h z) - Real.log (A.h z / C.h z)
  rw [Real.log_div hA'0.ne' hA0.ne', Real.log_div hA'0.ne' hC0.ne', Real.log_div hA0.ne' hC0.ne']
  ring

end Telescoping

section Pivot

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem h_eq_zero_of_fs (k₀ : K) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hA : A.a = unitDeg k₀) (z : (Σ k, ι k) → ℂ)
    (hz : (HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) (unitDeg k₀)).h z = 0) : A.h z = 0 := by
  obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp hz
  have hk0 : k = k₀ := by
    by_contra hne
    simp [unitDeg, hne] at hk
  subst hk0
  have hρ : (fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩) = 0 := by
    simpa [unitDeg] using hk
  have hzk : (fun i => z ⟨k, i⟩) = 0 := by
    by_contra hne
    exact ((fsMetric (ι := ι k)).pos _ hne).ne' hρ
  set c : K → ℂ := fun k' => if k' = k then 2 else 1 with hc
  have hc0 : ∀ k', c k' ≠ 0 := fun k' => by
    simp only [hc]
    split_ifs <;> norm_num
  have hfix : (fun p : (Σ k, ι k) => c p.1 * z p) = z := by
    funext p
    by_cases hp : p.1 = k
    · obtain ⟨k', i⟩ := p
      simp only at hp
      subst hp
      have : z ⟨k', i⟩ = 0 := congrFun hzk i
      simp [this]
    · simp [hc, hp]
  have hs := A.smul c z hc0
  rw [hfix, hA] at hs
  have hprod : (∏ k', ‖c k'‖ ^ unitDeg k k') = 2 := by
    rw [Finset.prod_eq_single k (fun k' _ hk' => by simp [unitDeg, hk']) (fun h => absurd (Finset.mem_univ k) h)]
    simp [hc, unitDeg]
  rw [hprod] at hs
  linarith

end Pivot

theorem BlockDefectMetricChange.proof (hR : BlockRealGramComparison.Statement)
    (hC : BlockComplexGramMetricChange.Statement) (hM : BlockResolutionMixedIntegral.Statement)
    (hInt : PtsIntegrableStatement) : BlockDefectMetricChange.Statement := by
  intro D K _ _ ι _ Ω _ _ I d A' P0' hdeg hc hle hp hI
  have h₁ := hR D K ι Ω (d.withMetric A' P0' hdeg hc hle hp)
  have h₀ := hR D K ι Ω d
  have hc₁ := hC D K ι Ω d A' P0' hdeg hc hle hp
  have hFS := GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs (ι := ι) (unitDeg d.k₀)
  have htop : I K ι (mCoordIdeal d.y) (D + 1) (fun _ => A') =
      I K ι (mCoordIdeal d.y) (D + 1) (fun _ => d.A) + ((D : ℝ) + 1) * blockMetricInt d A' := by
    rw [← hM D K ι Ω d A' hdeg hp.1, ← top_sub_top_blockMixPot hInt I hI d.arith d.semipos.1 hp.1 hFS
      (d.deg.trans rfl) (hdeg.trans rfl) (h_eq_zero_of_fs d.k₀ d.A d.deg) (h_eq_zero_of_fs d.k₀ A' hdeg)]
    ring
  have hlog := isLittleO_pow_mul_log D
  refine (((h₁.trans_isLittleO hlog).sub (h₀.trans_isLittleO hlog)).add hc₁).congr_left fun n => ?_
  simp only [hsDefect, htop, Nat.factorial_succ]
  push_cast
  field_simp
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

theorem BlockResolutionDegree.proof (hRank : BlockSectionsRank.Statement)
    (hInt : BlockResolutionDegreeIntegral.Statement) : BlockResolutionDegree.Statement := by
  intro D K _ _ ι _ Ω _ _ d A₀ A₁ h₀ h₁ s₀ s₁ t ht
  obtain ⟨C, hC⟩ := hRank D K ι Ω d.y d.k₀ d.one_le d.arith d.birat
  refine ⟨C, fun n => ?_⟩
  rw [hInt D K ι Ω d A₀ A₁ h₀ h₁ s₀ s₁ t ht]
  exact hC n

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PReductionToProjectiveBlock
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

theorem ReductionToProjectiveBlock.proof (hRP : ReductionToProjective.Statement)
    (hMC : BlockMetricChange.Statement) (hIm : BlockImageDatum.Statement) (hTop : BlockImageTop.Statement)
    (hGD : BlockImageGenDeg.Statement) : ReductionToProjectiveBlock.Statement := by
  intro D K _ _ ι _ Ω _ _ I d hI
  obtain ⟨d₀, r, M, N, d', hy, hk, hB, hmet, hchi⟩ := hIm D K ι Ω d

  have h1 := hMC D K ι Ω I d d₀ hI hy hk

  have h2 := (hRP D Ω (Fin r) I d' hI).2

  have hdeg : d₀.A.a = unitDeg d.k₀ := hk ▸ d₀.deg
  have htop : I K ι (mCoordIdeal d₀.y) (D + 1) (fun _ => d₀.A) = top I d'.x d'.m D := by
    rw [hy]
    exact hTop D K ι Ω (Fin r) I d.y d.k₀ d₀.A M N d'.x d'.m hI d.arith d.birat d'.arith hB hdeg
      d₀.semipos.1 d'.smooth hmet

  have hg : genDeg (ι := GlobalTheory (Fin r)) (coordIdeal ℤ d'.x) D 1 = genDeg (mCoordIdeal d.y) D d.A.a := by
    rw [d.deg]
    exact hGD D K ι Ω (Fin r) d.y d.k₀ M N d'.x d.arith d.birat hB
  rw [hg] at h2
  refine (h2.sub h1).congr_left fun n => ?_
  simp only [hsDefect, hchi n, htop]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFrameChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

namespace FrameChange

section Matrices

variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]

theorem matAct_matAct (A A' : Matrix J J ℚ) (x : J → Ω) : matAct A (matAct A' x) = matAct (A * A') x := by
  funext i
  simp only [matAct, Matrix.mul_apply, Rat.cast_sum, Rat.cast_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem isInvMat_mul {A A' : Matrix J J ℚ} (hA : IsInvMat A) (hA' : IsInvMat A') : IsInvMat (A * A') := by
  obtain ⟨C, hC⟩ := hA
  obtain ⟨C', hC'⟩ := hA'
  refine ⟨C' * C, fun v => ⟨?_, ?_⟩⟩
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hC' (C.mulVec v)).1, (hC v).1]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hC (A'.mulVec v)).2, (hC' v).2]


open Classical in
def scaleMat {D : ℕ} (e : Fin (D + 1) → J) (m : ℕ) : Matrix J J ℚ :=
  Matrix.diagonal fun i => if i ∈ Set.range e then 1 else (m : ℚ)


open Classical in
theorem matAct_scaleMat {D : ℕ} (e : Fin (D + 1) → J) (m : ℕ) (y : J → Ω) :
    matAct (scaleMat e m) y = scaleOff e m y := by
  funext i
  simp only [matAct, scaleMat, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  rw [if_pos rfl]
  unfold scaleOff
  split_ifs <;> simp


open Classical in
theorem isInvMat_scaleMat {D : ℕ} (e : Fin (D + 1) → J) {m : ℕ} (hm : 0 < m) : IsInvMat (scaleMat e m) := by
  have hc : ∀ i, (if i ∈ Set.range e then 1 else (m : ℚ)) ≠ 0 := fun i => by
    split_ifs
    · exact one_ne_zero
    · exact_mod_cast hm.ne'
  refine ⟨Matrix.diagonal fun i => (if i ∈ Set.range e then 1 else (m : ℚ))⁻¹, fun v => ⟨?_, ?_⟩⟩
  · funext i
    simp only [scaleMat, Matrix.mulVec_diagonal]
    rw [← mul_assoc, mul_inv_cancel₀ (hc i), one_mul]
  · funext i
    simp only [scaleMat, Matrix.mulVec_diagonal]
    rw [← mul_assoc, inv_mul_cancel₀ (hc i), one_mul]

end Matrices

theorem proof (hN : RatNoetherFrame.Statement) (hT : HSMTransport.Statement) (hI : ResChiIndex.Statement) :
    FrameChange.Statement := by
  intro D Ω _ _ κ _ d
  obtain ⟨B₀, e, hB₀, hfr⟩ := hN D Ω κ d.x d.arith
  obtain ⟨m, hm, hfr'⟩ := exists_scaleOff_isProjFrame (matAct B₀ d.x) e hfr
  have hB : IsInvMat (scaleMat e m * B₀) := isInvMat_mul (isInvMat_scaleMat e hm) hB₀
  obtain ⟨d', hx', hm', hG⟩ := hT D Ω κ d _ hB
  have hx'' : d'.x = scaleOff e m (matAct B₀ d.x) := by
    rw [hx', ← matAct_matAct, matAct_scaleMat]
  refine ⟨_, d', e, hB, hx', hm', by rw [hx'']; exact hfr', ?_⟩
  have h0 := hI D Ω κ d d' _ hB hx' hG
  have hz : (fun n => resChi d' n - resChi d n - latLogIndex d.x d'.x n) = fun _ => (0 : ℝ) :=
    funext fun n => by rw [h0 n, sub_self]
  rw [hz]
  exact isLittleO_zero _ _

end FrameChange

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertSamuelProjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

theorem chiP_zero_dim (n : ℕ) : chiP 0 n = 0 := by
  simp [chiP, monoNormSq, Finset.Nat.antidiagonalTuple_one]

theorem HilbertSamuelProjective.proof (hR : ReductionToProjective.Statement) (hV : SecondVeronese.Statement)
    (h0 : PointHeightFS.Statement) : HilbertSamuelProjective.Statement := by
  intro D I hI
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · have hh := h0 I hI
    refine (isLittleO_zero (fun n : ℕ => (n : ℝ) ^ (0 + 1)) atTop).congr' ?_ EventuallyEq.rfl
    refine Eventually.of_forall fun n => ?_
    simp [hsDefect, hh, chiP_zero_dim]
  · obtain ⟨Ω, _, _, κ, _, d, hchi, htop, hdeg⟩ := hV D hD
    have h2 := (hR D Ω κ I d hI).2
    have hfun : resChi d = fun m => chiP D (2 * m) := funext hchi
    rw [hfun, htop I hI, hdeg] at h2
    push_cast at h2
    exact hilbertSamuelDefect_projectiveSpace_isLittleO D (hhOf I D) h2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PReductionToProjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

namespace ReductionToProjective

theorem powLog_shift_le (D : ℕ) {n j : ℕ} (hj : j ≤ n) :
    ((n + j : ℕ) : ℝ) ^ D * Real.log (((n + j : ℕ) : ℝ) + 1) ≤
      2 ^ (D + 1) * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by
  have h1 := powLog_mono D (show n + j ≤ 2 * n by omega)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h2 : 2 * Real.log ((n : ℝ) + 1) = Real.log (((n : ℝ) + 1) ^ 2) := by
    rw [Real.log_pow]; push_cast; ring
  have hlog : Real.log (((2 * n : ℕ) : ℝ) + 1) ≤ 2 * Real.log ((n : ℝ) + 1) := by
    rw [h2]
    exact Real.log_le_log (by positivity) (by push_cast; nlinarith)
  have hp : ((2 * n : ℕ) : ℝ) ^ D = 2 ^ D * (n : ℝ) ^ D := by push_cast; rw [mul_pow]
  calc ((n + j : ℕ) : ℝ) ^ D * Real.log (((n + j : ℕ) : ℝ) + 1)
      ≤ ((2 * n : ℕ) : ℝ) ^ D * Real.log (((2 * n : ℕ) : ℝ) + 1) := h1
    _ ≤ ((2 * n : ℕ) : ℝ) ^ D * (2 * Real.log ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = 2 ^ (D + 1) * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by rw [hp]; ring

theorem sub_chiP_isBigO (D k : ℕ) (δ C : ℝ) (hδ : 0 ≤ δ) (chi : ℕ → ℝ)
    (hlo : ∀ n : ℕ, k + 1 ≤ n → δ * chiP D (n - k) - C * (n : ℝ) ^ D * Real.log (n + 1) ≤ chi n)
    (hhi : ∀ n : ℕ, k + 1 ≤ n → chi n ≤ δ * chiP D (n + k) + C * (n : ℝ) ^ D * Real.log (n + 1)) :
    (fun n => chi n - δ * chiP D n) =O[atTop] fun n : ℕ => (n : ℝ) ^ D * Real.log ((n : ℝ) + 1) := by
  obtain ⟨C', hC'⟩ := exists_chiP_succ_sub_le D
  refine IsBigO.of_bound (δ * (k * (|C'| * 2 ^ (D + 1))) + |C|) ?_
  filter_upwards [eventually_ge_atTop (k + 1)] with n hn
  have hP0 : 0 ≤ (n : ℝ) ^ D * Real.log ((n : ℝ) + 1) := powLog_nonneg D n
  have hCP : C * (n : ℝ) ^ D * Real.log (n + 1) ≤ |C| * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self C) hP0
  have hCP' : -(|C| * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1))) ≤ C * (n : ℝ) ^ D * Real.log (n + 1) := by
    rw [mul_assoc, ← neg_mul]; exact mul_le_mul_of_nonneg_right (neg_abs_le C) hP0
  have h2 : (1 : ℝ) ≤ 2 ^ (D + 1) := one_le_pow₀ (by norm_num)

  have hup : chiP D (n + k) - chiP D n ≤ k * (|C'| * 2 ^ (D + 1)) * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by
    refine (chiP_add_sub_le D C' hC' k n (by omega)).trans ?_
    calc ∑ j ∈ Finset.range k, |C'| * (((n + j : ℕ) : ℝ) ^ D * Real.log (((n + j : ℕ) : ℝ) + 1))
        ≤ ∑ j ∈ Finset.range k, |C'| * (2 ^ (D + 1) * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1))) := by
          refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ?_ (abs_nonneg C')
          exact powLog_shift_le D (by have := Finset.mem_range.1 hj; omega)
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

  have hdn : chiP D n - chiP D (n - k) ≤ k * (|C'| * 2 ^ (D + 1)) * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by
    have h := chiP_add_sub_le D C' hC' k (n - k) (by omega)
    rw [Nat.sub_add_cancel (by omega : k ≤ n)] at h
    refine h.trans ?_
    calc ∑ j ∈ Finset.range k, |C'| * (((n - k + j : ℕ) : ℝ) ^ D * Real.log (((n - k + j : ℕ) : ℝ) + 1))
        ≤ ∑ j ∈ Finset.range k, |C'| * (2 ^ (D + 1) * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1))) := by
          refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ?_ (abs_nonneg C')
          have hj' := Finset.mem_range.1 hj
          refine (powLog_mono D (show n - k + j ≤ n by omega)).trans ?_
          exact le_mul_of_one_le_left hP0 h2
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hlo' := hlo n hn
  have hhi' := hhi n hn
  have hu := mul_le_mul_of_nonneg_left hup hδ
  have hd := mul_le_mul_of_nonneg_left hdn hδ
  rw [Real.norm_eq_abs, Real.norm_of_nonneg hP0, abs_le]
  constructor
  · nlinarith
  · nlinarith

theorem defect_pullFS (hPB : ProjectionBounds.Statement) (hTop : TopPullFS.Statement) {D : ℕ} {Ω : Type}
    [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] (I : AllFam) (hI : I.IsFamily) (d : HSMDatum D Ω κ)
    (e : Fin (D + 1) → Ix κ) (hfr : IsProjFrame d.x e) (hFS : IsPullFS d.x e d.m) :
    (fun n => hsDefect D (resChi d) (top I d.x d.m D) n -
        (projDeg d.x e : ℝ) * hsDefect D (chiP D) (hhOf I D) n)
      =O[atTop] fun n : ℕ => (n : ℝ) ^ D * Real.log ((n : ℝ) + 1) := by
  obtain ⟨k, E, C, -, -, -, -, -, -, -, hs⟩ := hPB D Ω κ d e hfr hFS
  have ht := hTop D Ω κ I d.x d.m e hI d.arith d.smooth hfr hFS
  refine (sub_chiP_isBigO D k (projDeg d.x e) C (Nat.cast_nonneg _) (resChi d) (fun n hn => (hs n hn).1)
    (fun n hn => (hs n hn).2)).congr_left fun n => ?_
  simp only [hsDefect, ht]
  ring

theorem isLittleO_pow_pw (D : ℕ) : (fun n : ℕ => (n : ℝ) ^ D) =o[atTop] pw D :=
  (isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) (Nat.lt_succ_self D)).comp_tendsto tendsto_natCast_atTop_atTop

theorem proof (hPB : ProjectionBounds.Statement) (hCL : ChangeOfLattice.Statement)
    (hTop : TopPullFS.Statement) (hDeg : ProjDegGenDeg.Statement) (hInv : GenDegMatAct.Statement)
    (hFC : FrameChange.Statement) (hMF : MetricToFS.Statement) : ReductionToProjective.Statement := by
  intro D Ω _ _ κ _ I d hI
  refine ⟨fun e hfr hFS => defect_pullFS hPB hTop I hI d e hfr hFS, ?_⟩
  obtain ⟨B, d', e, hB, hx', hm', hfr', hidx⟩ := hFC D Ω κ d
  obtain ⟨d₀, hx₀, hFS₀, hmet⟩ := hMF D Ω κ I d' e hI hfr'
  have hfr₀ : IsProjFrame d₀.x e := hx₀ ▸ hfr'
  have hFS₀' : IsPullFS d₀.x e d₀.m := hx₀ ▸ hFS₀
  have h1 := (defect_pullFS hPB hTop I hI d₀ e hfr₀ hFS₀').trans_isLittleO (isLittleO_pow_mul_log D)
  rw [hx₀] at h1
  have h2 := (hCL D Ω κ I d.x B d.m d'.m hI d.arith d.indep hB d.smooth hm').trans_isLittleO
    (isLittleO_pow_pw D)
  rw [← hx'] at h2
  have hg : (genDeg (ι := GlobalTheory κ) (coordIdeal ℤ d.x) D 1 : ℝ) = (projDeg d'.x e : ℝ) := by
    have hd := hDeg D Ω κ d'.x e d'.arith hfr'
    have hi := hInv D Ω κ d.x B hB
    rw [← hx', hd] at hi
    rw [← hi]
    push_cast
    rfl
  rw [hg]
  refine ((h1.sub hmet).sub (hidx.add h2)).congr_left fun n => ?_
  simp only [hsDefect]
  ring

end ReductionToProjective

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMetricToFS
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

theorem MetricToFS.proof (hE : PullFSExtension.Statement) (hC : DefectMetricChange.Statement) :
    MetricToFS.Statement := by
  intro D Ω _ _ κ _ I d e hI hF
  obtain ⟨m₀, hs, hc, hp, hpull⟩ := hE D Ω κ d.x e hF
  exact ⟨d.withMetric m₀ ⊥ hs hc bot_le hp, rfl, hpull,
    hC D Ω κ I d m₀ ⊥ hs hc bot_le hp e hI hF⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockMetricChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

theorem BlockMetricChange.proof (hMeas : BlockMeasureChange.Statement)
    (hMet : BlockDefectMetricChange.Statement) : BlockMetricChange.Statement := by
  intro D K _ _ ι _ Ω _ _ I d d' hI hy hk
  have hdeg : d'.A.a = unitDeg d.k₀ := hk ▸ d'.deg
  have hle : d'.P0 ≤ mCoordIdeal d.y := hy ▸ d'.normalForm_baseLattice_le_dualSpan_sup_line
  have hp : IsSemipositiveRel d'.P0 (mCoordIdeal d.y) d'.A := hy ▸ d'.semipos

  have h1 := hMeas D K ι Ω (d.withMetric d'.A d'.P0 hdeg d'.conjInv hle hp) d' hy hk rfl
  have h2 := hMet D K ι Ω I d d'.A d'.P0 hdeg d'.conjInv hle hp hI
  refine (h1.add h2).congr_left fun n => ?_
  simp only [hsDefect, hy]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTheoremHSMBlock
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

theorem TheoremHSMBlock.proof (hR : ReductionToProjectiveBlock.Statement)
    (hP : HilbertSamuelProjective.Statement) (hS : SupBoundBlock.Statement) :
    TheoremHSMBlock.Statement := by
  intro D K _ _ ι _ Ω _ _ I d hI
  refine ⟨?_, hS D K ι Ω d⟩
  have h1 := hR D K ι Ω I d hI
  have h2 := (hP D I hI).const_mul_left (genDeg (mCoordIdeal d.y) D d.A.a : ℝ)
  refine (h1.add h2).congr_left fun n => ?_
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem TheoremHSMBlock.of_open
    (h0 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceIndex.Statement)
    (h1 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockModuleFinite.Statement)
    (h2 : GroundTheory.Heights₂.Heights.HilbertSamuel.ModulePieceHilbert.Statement)
    (h3 : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockModuleCycle.Statement)
    (h4 : ReciprocityTheory.ChartRestriction.G.AI.I4.PFCoordStatement)
    (h5 : ReciprocityTheory.ChartRestriction.G.AI.I4.ChangeOfModelStatement)
    (h6 : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameGraphDeg.Statement)
    (h7 : GroundTheory.Heights₂.Heights.HilbertSamuel.HSMTransport.Statement)
    (h8 : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionDegree.Statement)
    (h9 : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedBridge.Statement)
    (h10 : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionImageSup.Statement)
    (h11 : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionDegreeIntegral.Statement)
    (h12 : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionMixedBridge.Statement)
    (h13 : GroundTheory.Heights₂.Heights.Inter.PtsAbsIntegrable.Statement)
    (h14 : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageInverse.Statement)
    (h15 : GroundTheory.Heights₂.Heights.HilbertSamuel.GraphChangeOfModel.Statement)
    (h16 : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockGraphDeg.Statement)
    (h17 : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGramMono.Statement)
    (h18 : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGraphDeg.Statement)
    : GroundTheory.Heights₂.Heights.HilbertSamuel.TheoremHSMBlock.Statement :=
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TheoremHSMBlock.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionToProjectiveBlock.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionToProjective.proof ProjectionBounds.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLattice.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLatticeNested.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockChainSum.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockStepLocal.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceCycle.proof h0 h1 h2 h3) TwoBlockCycleExpand.full
  TwoBlockCoeffCycle.full) TwoBlockStepBound.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockTop.proof h4
  Closed.ReciprocityTheory.ChartRestriction.G.AI.I4.ImageCoord CoordArithOfFnField.full TwoBlockFnField.full MetricTransportSmooth.full)))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TopPullFS.proof h5 ProjFrameBasePtFree.full ProjFrameImage.full h6)
  ProjDegGenDeg.full GenDegMatAct.full (GroundTheory.Heights₂.Heights.HilbertSamuel.FrameChange.proof RatNoetherFrame.full h7
  ResChiIndex.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.MetricToFS.proof PullFSExtension.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.DefectMetricChange.proof RealGramComparison.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ComplexGramMetricChange.proof MetricChange.full ProjectionBounds.full
  PullFSExtension.full ResolutionMetricPair.full ResolutionFormsIndependent.full h8)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedIntegral.proof h9 ResolutionInterpIntegral.full))))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockMetricChange.proof BlockMeasureChange.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockDefectMetricChange.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockRealGramComparison.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionSupBound.proof h10 NonvanishingDense.full) SupBoundBlock.full
  SupBoundCount.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockComplexGramMetricChange.proof MetricChange.full
  BlockResolutionMetricPair.full BlockResolutionFormsIndependent.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionDegree.proof BlockSectionsRank.full h11))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionMixedIntegral.proof h12 BlockResolutionInterpIntegral.full)
  (GroundTheory.Heights₂.Heights.PtsIntegrable.of_found h13 Closed.PtsSumMeasurable)))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageDatum.proof BlockImageArith.full h14 AnResNullForm.full
  BlockImageMetrics.full BlockImageChi.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageTop.proof h15
  BlockGraphImage.full h16) BlockImageGenDeg.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertSamuelProjective.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionToProjective.proof ProjectionBounds.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLattice.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ChangeOfLatticeNested.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockChainSum.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockStepLocal.proof
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockPieceCycle.proof h0 h1 h2 h3) TwoBlockCycleExpand.full
  TwoBlockCoeffCycle.full) TwoBlockStepBound.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockTop.proof h4
  Closed.ReciprocityTheory.ChartRestriction.G.AI.I4.ImageCoord CoordArithOfFnField.full TwoBlockFnField.full MetricTransportSmooth.full)))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.TopPullFS.proof h5 ProjFrameBasePtFree.full ProjFrameImage.full h6)
  ProjDegGenDeg.full GenDegMatAct.full (GroundTheory.Heights₂.Heights.HilbertSamuel.FrameChange.proof RatNoetherFrame.full h7
  ResChiIndex.full) (GroundTheory.Heights₂.Heights.HilbertSamuel.MetricToFS.proof PullFSExtension.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.DefectMetricChange.proof RealGramComparison.full
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ComplexGramMetricChange.proof MetricChange.full ProjectionBounds.full
  PullFSExtension.full ResolutionMetricPair.full ResolutionFormsIndependent.full h8)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMixedIntegral.proof h9 ResolutionInterpIntegral.full))))
  (GroundTheory.Heights₂.Heights.HilbertSamuel.SecondVeronese.proof VeroneseArith.full VeroneseSemipos.full
  VeroneseResolution.full (GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseChi.proof VeroneseMonoBasis.full h17)
  (GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseTop.proof h15 VeroneseArith.full VeroneseGraphImage.full h18)
  VeroneseGenDeg.full) PointHeightFS.full) SupBoundBlock.full)

end GroundTheory.Heights₂.Heights.HilbertSamuel
