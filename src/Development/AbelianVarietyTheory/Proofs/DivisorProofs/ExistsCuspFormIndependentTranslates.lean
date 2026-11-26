module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionIsLocallyBlockUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallUnipotentUnitaryElementIsOneProof
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitInterpolationDetWeightFreeBallIndefinite

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormNonzeroAtOneLift
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeBallNoContractionUnitaryUpperLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeBallNoContractionUnitaryUpperLevel
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.FreeBallAt

open GlobalTheory.Up GlobalTheory.Up.BallExPf
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem noContraction_of_rmul (X : DataX E r) {x1 b : Frame X.Ψ r} (hx1 : x1 ∈ X.dom)
    (hb : b ∈ Bor X.Ψ r) (h : GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction X (rmul x1 b)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction X x1 := by
  intro N hN hop
  refine h N hN fun τ => ?_
  obtain ⟨c, hc0, hc1, hc⟩ := hop τ
  refine ⟨c, hc0, hc1, fun u => ?_⟩
  rw [GlobalTheory.MajInv.maj_rmul X.toData hx1 hb, GlobalTheory.MajInv.maj_rmul X.toData hx1 hb]
  exact hc u

theorem opNormLe_of_ball (hr : 0 < r) (X : Data E r) {x0 z1 : Frame X.Ψ r} {γ : GL (Fin r) E}
    (h0 : IsOrth X x0) (h1 : IsOrth X z1) (h2 : IsOrth X (lact γ z1))
    (hlt : rhX X x0 z1 < 1 / (49 * (r : ℝ) ^ 2))
    (hlt2 : rhX X x0 (lact γ z1) < 1 / (49 * (r : ℝ) ^ 2)) (τ : X.Ψ) :
    GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.OpNormLe X x0 τ (γ : Matrix (Fin r) (Fin r) E) (Real.exp (1 / (3 * (r : ℝ)))) := by
  intro u
  rw [ModeHalfA.maj_orth X h0, ModeHalfA.maj_orth X h0]
  change ReciprocityTheory.MultiplicativeHeights.normSq _ ≤ _ * ReciprocityTheory.MultiplicativeHeights.normSq _
  have hk := ReciprocityTheory.MultiplicativeHeights.sb_ballRatio_nonneg hr
  have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (LUPf.orthogonalFrame_det_ne_zero X x0 h0 τ)
  have hu1 : IsUnit (mat z1 τ).det := isUnit_iff_ne_zero.mpr (LUPf.orthogonalFrame_det_ne_zero X z1 h1 τ)
  have b1 := (frame_bound hr X h0 h1 hlt τ ((mat x0 τ)⁻¹ *ᵥ u)).1
  have b2 := (frame_bound hr X h0 h2 hlt2 τ ((mat z1 τ)⁻¹ *ᵥ u)).2
  have e : mat (lact γ z1) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat z1 τ := rfl
  rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv_cancel_right _ _ hu] at b1
  rw [e, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hu1,
    ← Matrix.mulVec_mulVec] at b2
  have hn : 0 ≤ ReciprocityTheory.MultiplicativeHeights.normSq ((mat x0 τ)⁻¹ *ᵥ u) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hE : ReciprocityTheory.MultiplicativeHeights.ballRatio r ^ 2 ≤ Real.exp (1 / (3 * (r : ℝ))) ^ 2 :=
    pow_le_pow_left₀ hk (ReciprocityTheory.MultiplicativeHeights.sb_ballRatio_le hr) 2
  calc _ ≤ _ := b2
    _ ≤ _ := mul_le_mul_of_nonneg_left b1 hk
    _ = ReciprocityTheory.MultiplicativeHeights.ballRatio r ^ 2 * ReciprocityTheory.MultiplicativeHeights.normSq ((mat x0 τ)⁻¹ *ᵥ u) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hE hn

theorem freeBall_at : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (G : Subgroup (GL (Fin r) E)) (g : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g → 3 * r < g → X.Γ ≤ G → (∀ γ ∈ G, IsUStab X.Gm X.L' γ) → (∀ γ ∈ G, IsUStab X.Gm X.Λ γ) → (∀ γ ∈ G, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver X.L' g γ) → ∀ x ∈ X.dom, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction X x → ∃ x0 : Frame X.Ψ r, IsOrth X.toData x0 ∧ (∃ b ∈ Bor X.Ψ r, x = rmul x0 b) ∧ GlobalTheory.Up.FreeBall X.toData G x0 (1 / (49 * (r : ℝ) ^ 2)) := by
  intro E _ _ _ r X G g hsp hg hΓ hL' hΛ hU x hx hNC
  obtain ⟨x1, h1, b, hb, rfl⟩ := ortho_holds r X.toData x hx
  have hx1 : x1 ∈ X.dom := IW.orth_mem_dom X.toData x1 h1
  have hNC1 := noContraction_of_rmul X hx1 hb hNC
  refine ⟨x1, h1, ⟨b, hb, rfl⟩, hΓ, hΛ, fun γ hγ hne z hz hlt => ?_⟩
  by_contra hlt2
  rw [not_le] at hlt2
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have := rhX_nonneg h1 hz
    simp at hlt
    linarith
  obtain ⟨z1, hz1, b', hb', rfl⟩ := ortho_holds r X.toData z hz
  rw [FundSetPf.lact_rmul, rhX_rmul _ _ hb'] at hlt2
  rw [rhX_rmul _ _ hb'] at hlt
  have h2 := isOrth_lact_of_isUStab (hΛ γ hγ) hz1
  exact hne (GlobalTheory.T.smallUnipotentUnitaryElementIsOne_proof E r X g hsp hg G hL' hU x1 hx1 hNC1 γ hγ
    (opNormLe_of_ball hr X.toData h1 hz1 h2 hlt hlt2))

end GlobalTheory.FreeBallAt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeBallNoContractionUnitaryUpperLevelStatement
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freeBall_noContraction_unitaryUpperLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (G : Subgroup (GL (Fin r) E)) (g : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g → 3 * r < g → X.Γ ≤ G → (∀ γ ∈ G, IsUStab X.Gm X.L' γ) → (∀ γ ∈ G, IsUStab X.Gm X.Λ γ) → (∀ γ ∈ G, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver X.L' g γ) → ∀ x ∈ X.dom, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction X x → ∃ x0 : Frame X.Ψ r, IsOrth X.toData x0 ∧ (∃ b ∈ Bor X.Ψ r, x = rmul x0 b) ∧ GlobalTheory.Up.FreeBall X.toData G x0 (1 / (49 * (r : ℝ) ^ 2)) := by
  first | exact @GlobalTheory.FreeBallAt.freeBall_at | exact GlobalTheory.FreeBallAt.freeBall_at | (intros; apply GlobalTheory.FreeBallAt.freeBall_at <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperLevelTrivialDefiniteNoContraction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperLevelTrivialDefiniteNoContraction
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.DefiniteLevel

open Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_comb_colP {r : ℕ} (X : Data E r) (hp : X.p0 = r) (x : Frame X.Ψ r) (τ : X.Ψ)
    (hx : (mat x τ).det ≠ 0) (v : Fin r → ℂ) :
    ∃ K : Fin X.p0 → ℂ, v = ∑ a, K a • X.colP x τ a := by
  refine ⟨fun a => ((mat x τ)⁻¹ *ᵥ v) (Fin.castLE X.p0_le a), ?_⟩
  have h1 : v = mat x τ *ᵥ ((mat x τ)⁻¹ *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hx), Matrix.one_mulVec]
  have h2 : ∀ w : Fin r → ℂ, mat x τ *ᵥ w = ∑ j, w j • ReciprocityTheory.ChartRestriction.G.FD.col (mat x τ) j := by
    intro w; funext k; simp [Matrix.mulVec, dotProduct, ReciprocityTheory.ChartRestriction.G.FD.col, Finset.sum_apply, mul_comm]
  conv_lhs => rw [h1, h2]
  exact (Fintype.sum_equiv (finCongr hp) _ _ (fun a => rfl)).symm

theorem maj_mulVec_of_definite {r : ℕ} (X : Data E r) (hp : X.p0 = 0 ∨ X.p0 = r) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (γ : GL (Fin r) E)
    (hγ : ∀ u v, herm X.Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      herm X.Gm u v)
    (τ : X.Ψ) (u : Fin r → ℂ) :
    X.maj x τ (((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ u) = X.maj x τ u := by
  set g := (γ : Matrix (Fin r) (Fin r) E).map τ.1 with hg
  set g' := ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 with hg'
  have hgg' : ∀ w, g *ᵥ (g' *ᵥ w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, hg, hg', ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  have hg'g : ∀ w, g' *ᵥ (g *ᵥ w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, hg, hg', ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  have hiso := GlobalTheory.MajInv.hermC_stab X hγ τ.1
  have key := MajorantConjugateTransfer.maj_transfer X hx hx τ g g' hgg' hiso ?_ ?_ (g *ᵥ u)
  · rwa [hg'g] at key
  · intro c
    rcases hp with hp | hp
    · exact absurd c.isLt (by omega)
    · exact exists_comb_colP X hp x τ (hx τ).1 _
  · intro a
    rcases hp with hp | hp
    · exact absurd a.isLt (by omega)
    · obtain ⟨L, hL⟩ := exists_comb_colP X hp x τ (hx τ).1 (g' *ᵥ X.colP x τ a)
      refine ⟨L, ?_⟩
      calc X.colP x τ a = g *ᵥ (g' *ᵥ X.colP x τ a) := (hgg' _).symm
        _ = g *ᵥ ∑ c, L c • X.colP x τ c := by rw [hL]
        _ = ∑ c, L c • (g *ᵥ X.colP x τ c) := by
          rw [Matrix.mulVec_sum]; simp_rw [Matrix.mulVec_smul]

theorem eq_one_of_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r)
    (G : Subgroup (GL (Fin r) E)) (g : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g → 3 * r < g →
    (∀ γ ∈ G, IsUStab X.Gm X.L' γ) → (∀ γ ∈ G, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver X.L' g γ) →
    (X.p0 = 0 ∨ X.p0 = r) → ∀ x ∈ X.dom, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction X x → ∀ γ ∈ G, γ = 1 := by
  intro E _ _ _ r X G g hg hgr hU hUn hp x hx hnc γ hγ
  refine GlobalTheory.T.smallUnipotentUnitaryElementIsOne_proof E r X g hg hgr G hU hUn x hx hnc γ hγ fun τ u => ?_
  rw [maj_mulVec_of_definite X.toData hp hx γ (hU γ hγ).1 τ u]
  have h0 := MajorantConjugateTransfer.maj_nonneg X.toData hx τ u
  have h1 : 1 ≤ Real.exp (1 / (3 * (r : ℝ))) := Real.one_le_exp (by positivity)
  exact le_mul_of_one_le_left h0 (one_le_pow₀ h1)

end GlobalTheory.DefiniteLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperLevelTrivialDefiniteNoContractionStatement
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperLevel_trivial_definite_noContraction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (G : Subgroup (GL (Fin r) E)) (g : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g → 3 * r < g → (∀ γ ∈ G, IsUStab X.Gm X.L' γ) → (∀ γ ∈ G, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver X.L' g γ) → (X.p0 = 0 ∨ X.p0 = r) → ∀ x ∈ X.dom, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction X x → ∀ γ ∈ G, γ = 1 := by
  first | exact @GlobalTheory.DefiniteLevel.eq_one_of_definite | exact GlobalTheory.DefiniteLevel.eq_one_of_definite | (intros; apply GlobalTheory.DefiniteLevel.eq_one_of_definite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUpperLevelSubgroupComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUpperLevelSubgroupComponent
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory

theorem upperLevel_isSubgroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (c : C), ∃ G : Subgroup (GL (Fin r) E), (∀ β, β ∈ G ↔ β ∈ M.upper c) ∧ (M.comp c).Γ ≤ G := by
  intro E _ _ _ r U C _ _ M c
  have h1 : M.tr 1 c ∈ (M.comp c).Γ := by
    have h := M.tr_mul 1 1 c
    simp only [one_mul, one_smul] at h
    have h' : (M.tr 1 c)⁻¹ ∈ (M.comp c).Γ := by
      simpa [mul_inv_rev, mul_assoc] using h
    simpa using inv_mem h'
  refine ⟨{ carrier := M.upper c
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun β => Iff.rfl, ?_⟩
  · rintro a b ⟨u, hu, γ, hγ, rfl⟩ ⟨v, hv, γ', hγ', rfl⟩
    have hc := (M.tr_conj u c γ').1 hγ'
    rw [hu] at hc
    have hm := M.tr_mul u v c
    rw [mul_smul, hv, hu] at hm
    refine ⟨u * v, by rw [mul_smul, hv, hu], γ * (M.tr u c * γ' * (M.tr u c)⁻¹) *
      (M.tr (u * v) c * (M.tr u c * M.tr v c)⁻¹)⁻¹, ?_, ?_⟩
    · exact mul_mem (mul_mem hγ hc) (inv_mem hm)
    · group
  · exact ⟨1, one_smul _ _, (M.tr 1 c)⁻¹, inv_mem h1, by group⟩
  · rintro a ⟨u, hu, γ, hγ, rfl⟩
    have hu' : u⁻¹ • c = c := by rw [inv_smul_eq_iff, hu]
    have hm := M.tr_mul u⁻¹ u c
    rw [inv_mul_cancel, one_smul, hu] at hm
    have hw : M.tr u⁻¹ c * M.tr u c ∈ (M.comp c).Γ := by
      have := mul_mem (inv_mem h1) hm
      simpa [mul_assoc] using inv_mem this
    have hc := (M.tr_conj u⁻¹ c γ⁻¹).1 (inv_mem hγ)
    rw [hu'] at hc
    refine ⟨u⁻¹, hu', (M.tr u⁻¹ c * M.tr u c)⁻¹ * (M.tr u⁻¹ c * γ⁻¹ * (M.tr u⁻¹ c)⁻¹), ?_, ?_⟩
    · exact mul_mem (inv_mem hw) hc
    · group
  · intro γ hγ
    exact ⟨1, one_smul _ _, γ * (M.tr 1 c)⁻¹, mul_mem hγ (inv_mem h1), by group⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUpperLevelSubgroupComponentStatement
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_upperLevel_subgroup_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (c : C), ∃ G : Subgroup (GL (Fin r) E), (∀ β, β ∈ G ↔ β ∈ M.upper c) ∧ (M.comp c).Γ ≤ G := by
  first | exact @GlobalTheory.upperLevel_isSubgroup | exact GlobalTheory.upperLevel_isSubgroup | (intros; apply GlobalTheory.upperLevel_isSubgroup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperLevelIsUnitaryStabiliserBothLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperLevelIsUnitaryStabiliserBothLattices
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.UpperStab

theorem upper_isUStab (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C]
    (M : TwoLevels E r U C) (c : C) :
    ∀ β ∈ M.upper c, IsUStab (M.comp c).Gm (M.comp c).L' β ∧ IsUStab (M.comp c).Gm (M.comp c).Λ β := by
  rintro β ⟨u, hu, γ, hγ, rfl⟩
  have hs := (M.comp c).Γ_stab γ hγ
  have hh : ∀ x y, herm (M.comp c).Gm (Matrix.mulVec ((γ * M.tr u c : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) x)
      (Matrix.mulVec ((γ * M.tr u c : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) y) = herm (M.comp c).Gm x y := by
    intro x y
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hs.1, M.comp_Gm c, M.tr_herm]
  refine ⟨⟨hh, fun v => ?_⟩, ⟨hh, fun v => ?_⟩⟩
  · have h1 := M.tr_L' u c v
    rw [hu] at h1
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, h1]
    exact M.Γ_L' c γ hγ _
  · have h1 := M.tr_Λ u c v
    rw [hu] at h1
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, h1]
    exact hs.2 _

end GlobalTheory.UpperStab
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperLevelIsUnitaryStabiliserBothLatticesStatement
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperLevel_isUnitaryStabiliser_both_lattices : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (c : C), ∀ β ∈ M.upper c, IsUStab (M.comp c).Gm (M.comp c).L' β ∧ IsUStab (M.comp c).Gm (M.comp c).Λ β := by
  first | exact @GlobalTheory.UpperStab.upper_isUStab | exact GlobalTheory.UpperStab.upper_isUStab | (intros; apply GlobalTheory.UpperStab.upper_isUStab <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetPowerSectionNeZeroDefinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetPowerSectionNeZeroDefinite
set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
open scoped ComplexConjugate

namespace GlobalTheory.DefConst

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def detPow (Ψ : Finset (E →+* ℂ)) (a : ℤ) (x : Frame Ψ r) : ℂ := ∏ τ, (mat x τ).det ^ a

theorem telescope : ∀ (n : ℕ) (f : Fin (n + 1) → ℝ), (∀ i, f i ≠ 0) →
    ∏ i : Fin n, f i.succ / f i.castSucc = f (Fin.last n) / f 0
  | 0, f, h => by
    rw [Fin.prod_univ_zero]; exact (div_self (h 0)).symm
  | n + 1, f, h => by
    rw [Fin.prod_univ_castSucc]
    have ih : ∏ i : Fin n, f i.succ.castSucc / f i.castSucc.castSucc =
        f (Fin.last n).castSucc / f (0 : Fin (n + 1)).castSucc :=
      telescope n (fun i => f i.castSucc) (fun i => h _)
    simp only [Fin.succ_castSucc]
    rw [ih, Fin.succ_last, Fin.castSucc_zero]
    have h1 := h (Fin.last n).castSucc
    have h2 := h 0
    field_simp

theorem lminor_zero (M : Matrix (Fin r) (Fin r) ℂ) : lminor M 0 = 1 := by
  unfold lminor
  exact Matrix.det_eq_one_of_card_eq_zero (by simp; exact Fintype.card_eq_zero)

theorem lminor_last (M : Matrix (Fin r) (Fin r) ℂ) : lminor M (Fin.last r) = M.det := by
  unfold lminor
  exact Matrix.det_submatrix_equiv_self (finCongr (Fin.val_last r)) M

theorem gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = x.transpose * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  exact Finset.sum_comm

theorem det_gram (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    (gram τ G x).det = x.det * (G.map τ).det * starRingEnd ℂ x.det := by
  rw [gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  congr 1
  exact (RingHom.map_det (starRingEnd ℂ) x).symm

theorem dmin_ne (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm x τ i ≠ 0 := by
  intro h
  have := (hx τ).2 i
  rw [h] at this
  simp at this

theorem pnorm_factor (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (a : ℤ) (τ : X.Ψ) :
    ‖(mat x τ).det ^ a‖ * ∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(a : ℝ) / 2) =
      ‖(X.Gm.map τ.1).det‖ ^ (-(a : ℝ) / 2) := by
  have hD : (mat x τ).det ≠ 0 := (hx τ).1
  have hpos : 0 < ‖(mat x τ).det‖ := norm_pos_iff.mpr hD
  have ht := telescope r (fun i => ‖dmin X.Gm x τ i‖) (fun i => norm_ne_zero_iff.mpr (dmin_ne X hx τ i))
  beta_reduce at ht
  have hprod : ∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(a : ℝ) / 2) =
      (‖dmin X.Gm x τ (Fin.last r)‖ / ‖dmin X.Gm x τ 0‖) ^ (-(a : ℝ) / 2) := by
    simp_rw [norm_div]
    rw [Real.finsetProd_rpow _ _ (fun i _ => by positivity) _, ht]
  rw [hprod]
  have h0 : dmin X.Gm x τ 0 = 1 := lminor_zero _
  have hl : dmin X.Gm x τ (Fin.last r) = (mat x τ).det * (X.Gm.map τ.1).det * starRingEnd ℂ (mat x τ).det := by
    unfold dmin; rw [lminor_last, det_gram]
  rw [h0, hl, norm_one, div_one, norm_mul, norm_mul, Complex.norm_conj, norm_zpow]
  have hg : 0 ≤ ‖(X.Gm.map τ.1).det‖ := norm_nonneg _
  rw [show ‖(mat x τ).det‖ * ‖(X.Gm.map τ.1).det‖ * ‖(mat x τ).det‖ =
      ‖(mat x τ).det‖ * ‖(mat x τ).det‖ * ‖(X.Gm.map τ.1).det‖ by ring,
    Real.mul_rpow (by positivity) hg, Real.mul_rpow hpos.le hpos.le, ← Real.rpow_intCast,
    ← mul_assoc, ← mul_assoc, ← Real.rpow_add hpos, ← Real.rpow_add hpos]
  have : (a : ℝ) + -(a : ℝ) / 2 + -(a : ℝ) / 2 = 0 := by ring
  rw [this, Real.rpow_zero, one_mul]

theorem pnorm_detPow (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la : Wt X.Ψ r) (a : ℤ)
    (hla : ∀ τ i, la τ i = a) :
    X.pnorm la (detPow X.Ψ a) x = ∏ τ : X.Ψ, ‖(X.Gm.map τ.1).det‖ ^ (-(a : ℝ) / 2) := by
  unfold Data.pnorm detPow
  simp only [hla, norm_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun τ _ => pnorm_factor X hx a τ

theorem det_diff (Ψ : Finset (E →+* ℂ)) (τ : Ψ) : Differentiable ℂ (fun x : Frame Ψ r => (mat x τ).det) := by
  simp only [Matrix.det_apply', mat, Matrix.of_apply]
  fun_prop

theorem detPow_diff (X : Data E r) (a : ℤ) : DifferentiableOn ℂ (detPow X.Ψ a) X.dom := by
  intro x hx
  apply DifferentiableAt.differentiableWithinAt
  unfold detPow
  have h : ∀ τ : X.Ψ, DifferentiableAt ℂ (fun y : Frame X.Ψ r => (mat y τ).det ^ a) x :=
    fun τ => (det_diff X.Ψ τ x).zpow (Or.inl (hx τ).1)
  fun_prop

theorem lact_one {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) : lact 1 x = x := by
  funext τ
  simp [lact, mat, Matrix.map_one]
  rfl

theorem chi_one (X : Data E r) (la : Wt X.Ψ r) : X.χ la 1 = 1 := by
  have h1 : (1 : GL (Fin r) E) ∈ X.Γ := X.Γ.one_mem
  have hm := X.χ_mul la 1 h1 1 h1
  rw [mul_one] at hm
  obtain ⟨n, hn, hf⟩ := X.χ_fin la
  have hne : X.χ la 1 ≠ 0 := fun h0 => by
    have := hf 1 h1
    rw [h0, zero_pow hn.ne'] at this
    exact zero_ne_one this
  exact mul_left_cancel₀ hne (hm.symm.trans (mul_one _).symm)

theorem hermC_mulVec (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (P : Matrix (Fin r) (Fin r) ℂ)
    (v w : Fin r → ℂ) :
    hermC τ G (P.mulVec v) (P.mulVec w) = ∑ k, ∑ l, v k * gram τ G P k l * conj (w l) := by
  have sw : ∀ f : Fin r → Fin r → Fin r → Fin r → ℂ,
      ∑ a, ∑ b, ∑ k, ∑ l, f a b k l = ∑ k, ∑ l, ∑ a, ∑ b, f a b k l := by
    intro f
    calc ∑ a, ∑ b, ∑ k, ∑ l, f a b k l = ∑ a, ∑ k, ∑ b, ∑ l, f a b k l :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ k, ∑ a, ∑ b, ∑ l, f a b k l := Finset.sum_comm
      _ = ∑ k, ∑ a, ∑ l, ∑ b, f a b k l :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ k, ∑ l, ∑ a, ∑ b, f a b k l := Finset.sum_congr rfl fun k _ => Finset.sum_comm
  simp only [hermC, gram, col, Matrix.of_apply, Matrix.mulVec, dotProduct]
  calc _ = ∑ a, ∑ b, ∑ k, ∑ l, P a k * v k * τ (G a b) * conj (P b l * w l) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ a, ∑ b, P a k * v k * τ (G a b) * conj (P b l * w l) := sw _
    _ = _ := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [map_mul]; ring

theorem not_iso (X : Data E r) (hp : X.p0 = 0 ∨ X.p0 = r) (ξ : Fin r → E) : ¬ X.IsIso ξ := by
  rintro ⟨-, h0, hne⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : E →+* ℂ, τ ∈ X.Ψ := by
    let τ0 : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
    by_cases h : τ0 ∈ X.Ψ
    · exact ⟨τ0, h⟩
    · refine ⟨ComplexEmbedding.conjugate τ0, (X.cmType _).2 ?_⟩
      simpa using h
  obtain ⟨P, hP, hg⟩ := X.signature ⟨τ, hτ⟩
  set u : Fin r → ℂ := fun a => τ (ξ a) with hu_def
  have hu : hermC τ X.Gm u u = 0 := by
    have := congrArg τ h0
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [herm, cc, map_sum, map_mul, map_zero, IsCMField.complexEmbedding_complexConj] at this
    simpa [hermC, u] using this
  obtain ⟨e, he, hsg⟩ : ∃ e : ℂ, e ≠ 0 ∧ ∀ a : Fin r, ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) = e := by
    rcases hp with h | h
    · exact ⟨-1, by norm_num, fun a => by simp [sgn, h]⟩
    · exact ⟨1, one_ne_zero, fun a => by simp [sgn, h, a.isLt]⟩
  set v := P⁻¹.mulVec u with hv_def
  have hPv : P.mulVec v = u := by
    rw [hv_def, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hP), Matrix.one_mulVec]
  have hsum : hermC τ X.Gm u u = e * ∑ a, v a * conj (v a) := by
    rw [← hPv, hermC_mulVec, hg]
    simp only [Matrix.diagonal_apply, hsg, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hv : v = 0 := by
    have h1 : ∑ a, (Complex.normSq (v a) : ℂ) = 0 := by
      have := hsum.symm.trans hu
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h he
      · simpa [Complex.mul_conj] using h
    have h2 : ∑ a, Complex.normSq (v a) = 0 := by exact_mod_cast h1
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Complex.normSq_nonneg _)] at h2
    funext a
    simpa using h2 a (Finset.mem_univ _)
  have hu0 : u = 0 := by rw [← hPv, hv, Matrix.mulVec_zero]
  apply hne
  funext a
  have := congrFun hu0 a
  simpa [u] using this

theorem detPow_mem_SS (X : Data E r) (hΓ : ∀ γ ∈ X.Γ, γ = 1) (hdef : ∀ ξ, ¬ X.IsIso ξ) (la : Wt X.Ψ r)
    (a : ℤ) (hla : ∀ τ i, la τ i = a) : detPow X.Ψ a ∈ X.SS la := by
  refine ⟨⟨⟨detPow_diff X a, ?_, ?_⟩, ⟨_, fun x hx => (pnorm_detPow X hx la a hla).le⟩⟩,
    fun ξ hξ => absurd hξ (hdef ξ)⟩
  · intro x _ b hb
    unfold detPow bchar
    have hb' : ∀ τ : X.Ψ, (mat b τ).det = ∏ i, b τ i i := fun τ =>
      Matrix.det_of_upperTriangular (fun i j hij => (hb τ).2 i j hij)
    have e1 : ∀ τ : X.Ψ, (mat (rmul x b) τ).det ^ a = (mat x τ).det ^ a * ∏ i, b τ i i ^ la τ i := by
      intro τ
      rw [show mat (rmul x b) τ = mat x τ * mat b τ from rfl, Matrix.det_mul, mul_zpow, hb' τ]
      simp only [hla]
      rw [Finset.prod_zpow]
    simp only [e1, Finset.prod_mul_distrib]
    ring
  · intro γ hγ x _
    rw [hΓ γ hγ, lact_one, chi_one, one_mul]

theorem exists_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (∀ γ ∈ X.Γ, γ = 1) → (X.p0 = 0 ∨ X.p0 = r) → ∀ s : ℕ, ∀ x ∈ X.dom,
      ∃ P ∈ X.SS (deMul X.Ψ r X.p0 s), P x ≠ 0 := by
  intro E _ _ _ r X hΓ hp s x hx
  refine ⟨detPow X.Ψ (if X.p0 = 0 then ((s / 2 : ℕ) : ℤ) else -((s / 2 : ℕ) : ℤ)),
    detPow_mem_SS X hΓ (not_iso X hp) _ _ ?_, ?_⟩
  · intro τ i
    by_cases h0 : X.p0 = 0
    · simp [deMul, h0]
    · have h : X.p0 = r := hp.resolve_left h0
      have hr : r ≠ 0 := h ▸ h0
      simp [deMul, h0, h, hr, i.isLt]
  · exact Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (hx τ).1

end GlobalTheory.DefConst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetPowerSectionNeZeroDefiniteStatement
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_detPowerSection_ne_zero_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (∀ γ ∈ X.Γ, γ = 1) → (X.p0 = 0 ∨ X.p0 = r) → ∀ s : ℕ, ∀ x ∈ X.dom, ∃ P ∈ X.SS (deMul X.Ψ r X.p0 s), P x ≠ 0 := by
  first | exact @GlobalTheory.DefConst.exists_ne_zero | exact GlobalTheory.DefConst.exists_ne_zero | (intros; apply GlobalTheory.DefConst.exists_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTotallySplitPrimeUpperLevelUnipotent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTotallySplitPrimeUpperLevelUnipotent
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.LevelSplit

theorem primesOver_eq (E : Type) [Field E] [NumberField E] {g : ℕ} (hg : g.Prime) :
    (Ideal.span {(g : ℤ)}).primesOver (𝓞 E) = {P : Ideal (𝓞 E) | P.IsPrime ∧ (g : 𝓞 E) ∈ P} := by
  ext P
  simp only [Ideal.primesOver, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hP, hL⟩
    refine ⟨hP, ?_⟩
    have h1 : (g : ℤ) ∈ Ideal.span {(g : ℤ)} := Ideal.mem_span_singleton_self _
    rw [hL.over] at h1
    simpa using (Ideal.mem_comap.mp h1)
  · rintro ⟨hP, hgP⟩
    refine ⟨hP, ⟨?_⟩⟩
    have hmax : (Ideal.span {(g : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hg).irreducible
    refine hmax.eq_of_le (Ideal.comap_ne_top _ hP.ne_top) ?_
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
    simpa using hgP

end GlobalTheory.LevelSplit

theorem GlobalTheory.levelHyp_totallySplit_unipotent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C), LevelHyp M → ∃ g : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g ∧ 3 * r < g ∧ ∀ c, ∀ β ∈ M.upper c, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver (M.comp c).L' g β := by
  intro E _ _ _ r U C _ _ M hM
  obtain ⟨g, ⟨hg, hcard⟩, hgr, hU⟩ := hM
  have hset := GlobalTheory.LevelSplit.primesOver_eq E hg
  refine ⟨g, ⟨hg, ?_⟩, hgr, ?_⟩
  · rw [hset]; exact hcard
  · intro c β hβ P hP
    rw [hset] at hP
    exact ⟨r, fun v hv => hU c β hβ P hP.1 hP.2 v hv⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTotallySplitPrimeUpperLevelUnipotentStatement
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_totallySplitPrime_upperLevel_unipotent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C), LevelHyp M → ∃ g : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g ∧ 3 * r < g ∧ ∀ c, ∀ β ∈ M.upper c, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver (M.comp c).L' g β := by
  first | exact @GlobalTheory.levelHyp_totallySplit_unipotent | exact GlobalTheory.levelHyp_totallySplit_unipotent | (intros; apply GlobalTheory.levelHyp_totallySplit_unipotent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormNonzeroAtOneLift
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.LiftInterp

theorem zero_mem_SS {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) : (0 : Frame X.Ψ r → ℂ) ∈ X.SS la := by
  obtain ⟨⟨hz, -, -⟩, -⟩ := siegelSpaceAlgebra_holds r X la la 0
  exact hz

theorem bchar_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Ψ : Finset (E →+* ℂ)}
    (la : Wt Ψ r) {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) : bchar la b ≠ 0 := by
  classical
  unfold bchar
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ ?_
  intro h0
  apply (hb τ).1
  have hU : (mat b τ).IsUpperTriangular := fun a c hca => (hb τ).2 a c hca
  rw [Matrix.det_of_upperTriangular hU]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simpa [mat] using h0)

theorem comp_interp {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r)
    (hχ : ∀ la, ∀ γ ∈ X.Γ, X.χ la γ = 1) (G : Subgroup (GL (Fin r) E)) (g : ℕ)
    (hg : GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g) (hgr : 3 * r < g) (hΓG : X.Γ ≤ G)
    (hL' : ∀ γ ∈ G, IsUStab X.Gm X.L' γ) (hΛ : ∀ γ ∈ G, IsUStab X.Gm X.Λ γ)
    (hU : ∀ γ ∈ G, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver X.L' g γ) (s : ℕ) (hs : Even s)
    (hsb : 2 * r + 50 * r ^ 2 * (X.Ψ.card * (X.p0 * (r - X.p0))) + 1 ≤ s)
    (x : Frame X.Ψ r) (hx : x ∈ X.dom) (hNC : GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction X x) :
    ∃ P ∈ X.SS (deMul X.Ψ r X.p0 s), P x ≠ 0 ∧ ∀ γ ∈ G, γ ∉ X.Γ → P (lact γ x) = 0 := by
  by_cases hdef : X.p0 = 0 ∨ X.p0 = r
  · have h1 := GlobalTheory.T.upperLevel_trivial_definite_noContraction E r X G g hg hgr hL' hU hdef x hx hNC
    obtain ⟨P, hP, hP0⟩ := GlobalTheory.T.exists_detPowerSection_ne_zero_definite E r X.toData (fun γ hγ => h1 γ (hΓG hγ)) hdef s x hx
    refine ⟨P, hP, hP0, fun γ hγ hγ' => absurd ?_ hγ'⟩
    rw [h1 γ hγ]
    exact X.Γ.one_mem
  · push_neg at hdef
    have hp0 : 0 < X.p0 := Nat.pos_of_ne_zero hdef.1
    have hp1 : X.p0 < r := lt_of_le_of_ne X.p0_le hdef.2
    obtain ⟨x0, h0, ⟨b, hb, rfl⟩, hFB⟩ := GlobalTheory.T.freeBall_noContraction_unitaryUpperLevel E r X G g hg hgr hΓG hL' hΛ hU x hx hNC
    obtain ⟨P, hP, hP0, hPγ⟩ := GlobalTheory.T.orbitInterpolation_detWeight_freeBall_indefinite E r X.toData hχ G x0 h0 hFB hp0 hp1 s hs hsb
    have hx0 : x0 ∈ X.dom := IW.orth_mem_dom X.toData x0 h0
    refine ⟨P, hP, ?_, fun γ hγ hγ' => ?_⟩
    · rw [hP.1.1.2.1 x0 hx0 b hb]
      exact mul_ne_zero (bchar_ne_zero _ hb) hP0
    · have hy : lact γ x0 ∈ X.dom := GlobalTheory.MajInv.lact_mem_dom X.toData (hΛ γ hγ) hx0
      rw [FundSetPf.lact_rmul, hP.1.1.2.1 _ hy b hb, hPγ γ hγ hγ', mul_zero]

theorem castFrame_symm_cast {E : Type} [Field E] {r : ℕ} {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ')
    (y : Frame Ψ r) : castFrame h.symm (castFrame h y) = y := by
  subst h; rfl

theorem castFrame_lact {E : Type} [Field E] {r : ℕ} {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ')
    (γ : GL (Fin r) E) (y : Frame Ψ r) : castFrame h (lact γ y) = lact γ (castFrame h y) := by
  subst h; rfl

theorem castFrame_mem_GG {E : Type} [Field E] {r : ℕ} {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ')
    (G : Matrix (Fin r) (Fin r) E) (p : ℕ) (y : Frame Ψ' r) (hy : y ∈ GG Ψ' G p) :
    castFrame h.symm y ∈ GG Ψ G p := by
  subst h; exact hy

theorem castWt_deMul {E : Type} [Field E] {r : ℕ} {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (p s : ℕ) :
    castWt h (deMul Ψ' r p s) = deMul Ψ r p s := by
  subst h; rfl

theorem exists_form_one_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite U] [Finite C] [MulAction U C] (M : TwoLevels E r U C), LevelHyp M → ∀ s : ℕ, Even s → 2 * r + 50 * r ^ 2 * M.dimX + 1 ≤ s → ∀ (c : C) (x : Frame M.Ψ r), GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction (M.comp c) (castFrame (M.comp_Ψ c).symm x) → x ∈ M.dom → ∃ u ∈ M.SS (deMul M.Ψ r M.p0 s), u c x ≠ 0 ∧ (∀ h : U, h ≠ 1 → M.pull h u c x = 0) ∧ ∀ c', (∀ h : U, h • c ≠ c') → ∀ y, u c' y = 0 := by
  intro E _ _ _ r U C _ _ _ _ M hLH s hs hsb c x hNC hx
  classical
  obtain ⟨g, hg, hgr, hUn⟩ := GlobalTheory.T.exists_totallySplitPrime_upperLevel_unipotent E r U C M hLH
  obtain ⟨G, hG, hΓG⟩ := GlobalTheory.T.exists_upperLevel_subgroup_component E r U C M c
  have hΨ : (M.comp c).Ψ = M.Ψ := M.comp_Ψ c
  have hx' : castFrame hΨ.symm x ∈ (M.comp c).dom := by
    have := castFrame_mem_GG hΨ M.Gm M.p0 x hx
    show castFrame hΨ.symm x ∈ GG (M.comp c).Ψ (M.comp c).Gm (M.comp c).p0
    rw [M.comp_Gm c, M.comp_basePoint c]
    exact this
  have hsb' : 2 * r + 50 * r ^ 2 * ((M.comp c).Ψ.card * ((M.comp c).p0 * (r - (M.comp c).p0))) + 1 ≤ s := by
    rw [hΨ, M.comp_basePoint c]; exact hsb
  obtain ⟨P, hP, hP0, hPγ⟩ := comp_interp (M.comp c) (M.χ_one c) G g hg hgr hΓG
    (fun β hβ => (GlobalTheory.T.upperLevel_isUnitaryStabiliser_both_lattices E r U C M c β ((hG β).1 hβ)).1) (fun β hβ => (GlobalTheory.T.upperLevel_isUnitaryStabiliser_both_lattices E r U C M c β ((hG β).1 hβ)).2)
    (fun β hβ => hUn c β ((hG β).1 hβ)) s hs hsb' _ hx' hNC
  let u : C → Frame M.Ψ r → ℂ := fun c' y => if c' = c then P (castFrame hΨ.symm y) else 0
  refine ⟨u, ?_, ?_, ?_, ?_⟩
  · intro c'
    by_cases hc : c' = c
    · subst hc
      have e : (fun y => u c' (castFrame (M.comp_Ψ c') y)) = P := by
        funext y
        simp only [u, if_pos rfl]
        exact congrArg P (castFrame_symm_cast _ y)
      rw [e, castWt_deMul]
      rw [M.comp_basePoint c'] at hP
      exact hP
    · have e : (fun y => u c' (castFrame (M.comp_Ψ c') y)) = 0 := by
        funext y
        simp [u, hc]
      rw [e]
      exact zero_mem_SS _ _
  · simpa [u] using hP0
  · intro h hh
    unfold TwoLevels.pull
    by_cases hc : h • c = c
    · simp only [u, hc, if_pos rfl]
      rw [castFrame_lact]
      refine hPγ _ ((hG _).2 ⟨h, hc, 1, (M.comp c).Γ.one_mem, by simp⟩) fun hm => hh ?_
      exact M.tr_faithful h c hc hm
    · simp [u, hc]
  · intro c' hc' y
    have hne : c' ≠ c := fun e => hc' 1 (by simp [e])
    simp [u, hne]

end GlobalTheory.LiftInterp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormNonzeroAtOneLiftStatement
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspForm_nonzero_at_one_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite U] [Finite C] [MulAction U C] (M : TwoLevels E r U C), LevelHyp M → ∀ s : ℕ, Even s → 2 * r + 50 * r ^ 2 * M.dimX + 1 ≤ s → ∀ (c : C) (x : Frame M.Ψ r), GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction (M.comp c) (castFrame (M.comp_Ψ c).symm x) → x ∈ M.dom → ∃ u ∈ M.SS (deMul M.Ψ r M.p0 s), u c x ≠ 0 ∧ (∀ h : U, h ≠ 1 → M.pull h u c x = 0) ∧ ∀ c', (∀ h : U, h • c ≠ c') → ∀ y, u c' y = 0 := by
  first | exact @GlobalTheory.LiftInterp.exists_form_one_lift | exact GlobalTheory.LiftInterp.exists_form_one_lift | (intros; apply GlobalTheory.LiftInterp.exists_form_one_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormIndependentTranslates
set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open scoped Matrix

namespace GlobalTheory.TranslatesDet

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem hermMat {G γ : Matrix (Fin r) (Fin r) E}
    (h : ∀ v w, herm G (Matrix.mulVec γ v) (Matrix.mulVec γ w) = herm G v w) :
    γᵀ * G * γ.map cc = G := by
  ext c d
  have h1 := h (Pi.single c 1) (Pi.single d 1)
  simp only [herm, Matrix.mulVec_single_one] at h1
  have h2 : (∑ a, ∑ b, (Pi.single c (1 : E) : Fin r → E) a * G a b *
      cc ((Pi.single d (1 : E) : Fin r → E) b)) = G c d := by simp [Pi.single_apply, cc]
  rw [← h2, ← h1]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem gramLact {G : Matrix (Fin r) (Fin r) E} {γ : GL (Fin r) E}
    (h : ∀ v w, herm G (Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v)
      (Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) w) = herm G v w)
    (τ : E →+* ℂ) (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G ((γ : Matrix (Fin r) (Fin r) E).map τ * M) = gram τ G M := by
  have hc : ((γ : Matrix (Fin r) (Fin r) E).map τ).map (starRingEnd ℂ) =
      ((γ : Matrix (Fin r) (Fin r) E).map cc).map τ := by
    ext a b; simp [cc, NumberField.IsCMField.complexEmbedding_complexConj]
  have key : ((γ : Matrix (Fin r) (Fin r) E).map τ)ᵀ * G.map τ *
      ((γ : Matrix (Fin r) (Fin r) E).map τ).map (starRingEnd ℂ) = G.map τ := by
    rw [hc, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hermMat h]
  rw [FrameDegreeData.gram_eq, FrameDegreeData.gram_eq, Matrix.transpose_mul, Matrix.map_mul]
  calc Mᵀ * ((γ : Matrix (Fin r) (Fin r) E).map τ)ᵀ * G.map τ *
        (((γ : Matrix (Fin r) (Fin r) E).map τ).map (starRingEnd ℂ) * M.map (starRingEnd ℂ))
      = Mᵀ * (((γ : Matrix (Fin r) (Fin r) E).map τ)ᵀ * G.map τ *
        ((γ : Matrix (Fin r) (Fin r) E).map τ).map (starRingEnd ℂ)) * M.map (starRingEnd ℂ) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [key]

theorem lactGG {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {p0 : ℕ} {γ : GL (Fin r) E}
    (h : ∀ v w, herm G (Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v)
      (Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) w) = herm G v w)
    {x : Frame Ψ r} (hx : x ∈ GG Ψ G p0) : lact γ x ∈ GG Ψ G p0 := by
  intro τ
  have hm : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  refine ⟨?_, fun i => ?_⟩
  · rw [hm, Matrix.det_mul]
    refine mul_ne_zero ?_ (hx τ).1
    have hd : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det = τ.1 (γ : Matrix (Fin r) (Fin r) E).det := by
      rw [RingHom.map_det]; rfl
    rw [hd]
    exact (map_ne_zero τ.1).2 (Matrix.GeneralLinearGroup.det_ne_zero γ)
  · have e : dmin G (lact γ x) τ i = dmin G x τ i := by
      unfold dmin; rw [hm, gramLact h]
    rw [e]; exact (hx τ).2 i

theorem lactMul {Ψ : Finset (E →+* ℂ)} (a b : GL (Fin r) E) (x : Frame Ψ r) :
    lact a (lact b x) = lact (a * b) x := by
  funext τ
  show ((a : Matrix (Fin r) (Fin r) E).map τ.1 * ((b : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) :
    Matrix (Fin r) (Fin r) ℂ) = ((a * b : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

theorem castGG {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') {G : Matrix (Fin r) (Fin r) E} {p0 : ℕ}
    {x : Frame Ψ r} (hx : x ∈ GG Ψ G p0) : castFrame h x ∈ GG Ψ' G p0 := by
  subst h; exact hx

section Two

variable {U C : Type} [Group U] [MulAction U C] (M : TwoLevels E r U C)

theorem domOfComp (c : C) {x : Frame (M.comp c).Ψ r} (hx : x ∈ (M.comp c).dom) :
    castFrame (M.comp_Ψ c) x ∈ M.dom := by
  have h := castGG (M.comp_Ψ c) hx
  rw [M.comp_Gm c, M.comp_basePoint c] at h
  exact h

theorem domToComp (c : C) {x : Frame M.Ψ r} (hx : x ∈ M.dom) :
    castFrame (M.comp_Ψ c).symm x ∈ (M.comp c).dom := by
  have hx' : x ∈ GG M.Ψ (M.comp c).Gm (M.comp c).p0 := by
    rw [M.comp_Gm c, M.comp_basePoint c]; exact hx
  exact castGG (M.comp_Ψ c).symm hx'

theorem trDom (u : U) (c : C) {x : Frame M.Ψ r} (hx : x ∈ M.dom) : lact (M.tr u c) x ∈ M.dom :=
  lactGG (M.tr_herm u c) hx

theorem ssLact {la : Wt M.Ψ r} {F : C → Frame M.Ψ r → ℂ} (hF : F ∈ M.SS la) (c : C)
    {γ : GL (Fin r) E} (hγ : γ ∈ (M.comp c).Γ) {x : Frame M.Ψ r} (hx : x ∈ M.dom) :
    F c (lact γ x) = F c x := by
  have h1 := (hF c).1.1.2.2 γ hγ (castFrame (M.comp_Ψ c).symm x) (domToComp M c hx)
  rw [M.χ_one c _ γ hγ, one_mul] at h1
  exact h1

theorem ssZero (la : Wt M.Ψ r) : (0 : C → Frame M.Ψ r → ℂ) ∈ M.SS la := by
  intro c
  exact ⟨BoundedSectionAlgebra.bdd_zero _ _, fun ξ _ x _ => BoundedSectionAlgebra.fj_zero _ _ ξ x 0⟩

theorem ssAdd {la : Wt M.Ψ r} {F G : C → Frame M.Ψ r → ℂ} (hF : F ∈ M.SS la) (hG : G ∈ M.SS la) :
    F + G ∈ M.SS la := by
  intro c
  have h := hF c
  have h' := hG c
  have e : (fun y => (F + G) c (castFrame (M.comp_Ψ c) y)) =
      (fun y => F c (castFrame (M.comp_Ψ c) y)) + (fun y => G c (castFrame (M.comp_Ψ c) y)) := rfl
  rw [e]
  exact ⟨BoundedSectionAlgebra.bdd_add _ h.1 h'.1, fun ξ hξ x hx => by
    rw [BoundedSectionAlgebra.fj_add _ h.1 h'.1 hξ hx, h.2 ξ hξ x hx, h'.2 ξ hξ x hx, add_zero]⟩

theorem ssSum {la : Wt M.Ψ r} {ι : Type} (s : Finset ι) (f : ι → C → Frame M.Ψ r → ℂ)
    (h : ∀ i ∈ s, f i ∈ M.SS la) : ∑ i ∈ s, f i ∈ M.SS la :=
  Finset.sum_induction f (fun F => F ∈ M.SS la) (fun _ _ ha hb => ssAdd M ha hb) (ssZero M la) h

end Two

end GlobalTheory.TranslatesDet

namespace GlobalTheory.TranslatesDet

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable {U C : Type} [Group U] [MulAction U C] (M : TwoLevels E r U C)

theorem detNeAt [Fintype U] [DecidableEq U] {la : Wt M.Ψ r} {u u0 : C → Frame M.Ψ r → ℂ}
    (hu : u ∈ M.SS la) {c0 : C} {x0 : Frame M.Ψ r} (hx0 : x0 ∈ M.dom) (hne : u c0 x0 ≠ 0)
    (hz : ∀ h : U, h ≠ 1 → M.pull h u c0 x0 = 0)
    (hrep : ∀ (g : U) (y : Frame M.Ψ r), u0 (g • c0) y = u (g • c0) y) (k : U) :
    ∃ x ∈ M.dom, M.detTr u0 (k • c0) x ≠ 0 := by
  refine ⟨lact (M.tr k c0) x0, trDom M k c0 hx0, ?_⟩
  have ht1 : M.tr 1 c0 ∈ (M.comp c0).Γ := by
    have h := M.tr_mul 1 1 c0
    simp only [mul_one, one_smul] at h
    have e : M.tr 1 c0 * (M.tr 1 c0 * M.tr 1 c0)⁻¹ = (M.tr 1 c0)⁻¹ := by group
    rw [e] at h
    exact inv_mem_iff.mp h
  have ha : M.pull 1 u c0 x0 ≠ 0 := by
    simp only [TwoLevels.pull, one_smul]
    rw [ssLact M hu c0 ht1 hx0]
    exact hne
  have entry : ∀ g : U, M.pull g u0 (k • c0) (lact (M.tr k c0) x0) = M.pull (g * k) u c0 x0 := by
    intro g
    have hzd : lact (M.tr g (k • c0)) (lact (M.tr k c0) x0) ∈ M.dom :=
      trDom M g (k • c0) (trDom M k c0 hx0)
    have e1 : lact (M.tr (g * k) c0) x0 =
        lact (M.tr (g * k) c0 * (M.tr g (k • c0) * M.tr k c0)⁻¹)
          (lact (M.tr g (k • c0)) (lact (M.tr k c0) x0)) := by
      rw [lactMul (M.tr g (k • c0)) (M.tr k c0) x0, lactMul, inv_mul_cancel_right]
    simp only [TwoLevels.pull]
    rw [e1, ← mul_smul, hrep (g * k)]
    exact (ssLact M hu ((g * k) • c0) (M.tr_mul g k c0) hzd).symm
  let σ : Equiv.Perm U := (Equiv.inv U).trans (Equiv.mulRight k⁻¹)
  have key : ∀ h h' : U, h * h' * k = 1 ↔ σ h = h' := by
    intro h h'
    show h * h' * k = 1 ↔ h⁻¹ * k⁻¹ = h'
    constructor
    · intro e
      have e2 : h⁻¹ * (h * h' * k) * k⁻¹ = h' := by group
      rw [e] at e2
      simpa using e2
    · intro e
      rw [← e]
      group
  have hmat : (Matrix.of fun h h' : U => M.pull (h * h') u0 (k • c0) (lact (M.tr k c0) x0)) =
      (M.pull 1 u c0 x0 • (1 : Matrix U U ℂ)).submatrix σ id := by
    ext h h'
    rw [Matrix.of_apply, entry, Matrix.submatrix_apply, id, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    by_cases e : h * h' * k = 1
    · rw [if_pos ((key h h').1 e), e, mul_one]
    · rw [if_neg (fun e' => e ((key h h').2 e')), mul_zero]
      exact hz _ e
  unfold TwoLevels.detTr
  rw [hmat, Matrix.det_permute, Matrix.det_smul, Matrix.det_one, mul_one]
  refine mul_ne_zero ?_ (pow_ne_zero _ ha)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

theorem independentTranslates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    IndependentTranslates E := by
  intro E _ _ _ r U C _ _ _ _ _ M hL s hs hsle
  classical
  have hB : ∀ c : C, ∃ x ∈ (M.comp c).dom, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction (M.comp c) x := fun c => by
    obtain ⟨x, hx, h1, -⟩ := GlobalTheory.T.existsBalancedFrameCMUnitary_proof E r (M.comp c)
    exact ⟨x, hx, h1⟩
  choose xb hxb hnc using hB
  have hI : ∀ c : C, ∃ u ∈ M.SS (deMul M.Ψ r M.p0 s), u c (castFrame (M.comp_Ψ c) (xb c)) ≠ 0 ∧
      (∀ h : U, h ≠ 1 → M.pull h u c (castFrame (M.comp_Ψ c) (xb c)) = 0) ∧
      ∀ c', (∀ h : U, h • c ≠ c') → ∀ y, u c' y = 0 := fun c =>
    GlobalTheory.T.exists_cuspForm_nonzero_at_one_lift E r U C M hL s hs hsle c _ (hnc c) (domOfComp M c (hxb c))
  choose uc huS hu0 hu1 hu2 using hI
  haveI : Fintype (Quotient (MulAction.orbitRel U C)) := Fintype.ofFinite _
  have hsum : ∀ c' y, (∑ q : Quotient (MulAction.orbitRel U C), uc q.out) c' y =
      uc (Quotient.mk (MulAction.orbitRel U C) c').out c' y := by
    intro c' y
    rw [Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_eq_single (Quotient.mk (MulAction.orbitRel U C) c') (fun q _ hq => ?_)
      (fun h => absurd (Finset.mem_univ _) h)
    refine hu2 q.out c' (fun h hh => hq ?_) y
    have e : (Quotient.mk (MulAction.orbitRel U C) q.out) = Quotient.mk (MulAction.orbitRel U C) c' :=
      Quotient.sound (MulAction.orbitRel_apply.2 ⟨h⁻¹, by show h⁻¹ • c' = q.out; rw [← hh, inv_smul_smul]⟩)
    rwa [Quotient.out_eq] at e
  have hrep : ∀ (q : Quotient (MulAction.orbitRel U C)) (g : U) (y : Frame M.Ψ r),
      (∑ q' : Quotient (MulAction.orbitRel U C), uc q'.out) (g • q.out) y = uc q.out (g • q.out) y := by
    intro q g y
    rw [hsum]
    have e : Quotient.mk (MulAction.orbitRel U C) (g • q.out) = q :=
      (Quotient.sound (MulAction.orbitRel_apply.2 ⟨g, rfl⟩)).trans (Quotient.out_eq q)
    rw [e]
  refine ⟨∑ q : Quotient (MulAction.orbitRel U C), uc q.out,
    ssSum M _ _ (fun q _ => huS q.out), fun c => ?_⟩
  obtain ⟨m, hm⟩ : (Quotient.mk (MulAction.orbitRel U C) c).out ∈ MulAction.orbit U c :=
    MulAction.orbitRel_apply.1 (Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel U C) c)))
  have hk : m⁻¹ • (Quotient.mk (MulAction.orbitRel U C) c).out = c := by
    rw [← hm, inv_smul_smul]
  rw [← hk]
  exact detNeAt M (huS _) (domOfComp M _ (hxb _)) (hu0 _) (hu1 _) (hrep _) m⁻¹

end GlobalTheory.TranslatesDet
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormIndependentTranslatesStatement
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspForm_independent_translates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], IndependentTranslates E := by
  first | exact @GlobalTheory.TranslatesDet.independentTranslates | exact GlobalTheory.TranslatesDet.independentTranslates | (intros; apply GlobalTheory.TranslatesDet.independentTranslates <;> assumption)
end
