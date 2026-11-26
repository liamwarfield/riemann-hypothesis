module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.StepSplitHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.ThetaMbe0GOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.SelfDualLatticesOneOrbit
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.HatZSecondProjTranspose
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.StepLiftG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryGramLifts.ScaleB

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.ZzScale
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.ScaleCh
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.AlgGUNS
noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

def AlgGAllNS : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L), M.split = some g →
  ∀ (r : ℕ) (T T' : F), (∃ u v : 𝒪[F], (u : F) * T = 1 ∧ (v : F) * T' = 1) →
    (∃ c : 𝒪[F], T - T' = (g.q : F) ^ 2 * c) →
  ∀ (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R),
    Z₁.map M.R.subtype = HermSp.ZZplusOf M Zh₁ T T' → Z₂.map M.R.subtype = HermSp.ZZplusOf M Zh₂ T T' →
    IsUnit Zh₁.det → IsUnit Zh₂.det →
    Zh₁.det * (Zh₂.submatrix Fin.castSucc Fin.castSucc).det =
      Zh₂.det * (Zh₁.submatrix Fin.castSucc Fin.castSucc).det →
    IsUnit (Zh₁.det * M.L.cj Zh₁.det - algebraMap F E (T * T') *
      ((Zh₁.submatrix Fin.castSucc Fin.castSucc).det * M.L.cj (Zh₁.submatrix Fin.castSucc Fin.castSucc).det)) →
    IsUnit (Zh₂.det * M.L.cj Zh₂.det - algebraMap F E (T * T') *
      ((Zh₂.submatrix Fin.castSucc Fin.castSucc).det * M.L.cj (Zh₂.submatrix Fin.castSucc Fin.castSucc).det)) →
    T ∈ 𝒪[F] → IsUnit (Z₁.map M.R.subtype).det → IsUnit (Z₂.map M.R.subtype).det →
    IsUnit (HermSp.ZZplusOf M (Zh₁.map M.L.cj) T T').det → IsUnit (HermSp.ZZplusOf M (Zh₂.map M.L.cj) T T').det →
    Nat.card (ThetaGC M.L.O (M.L.cj : E →+* E) (algebraMap F E (g.q : F))
        (algebraMap F E ((g.q : F)⁻¹)) Zh₁ Zh₂ (algebraMap F E T) (algebraMap F E T')) =
      Nat.card (IsoMbe Z₁ Z₂)

theorem algGAllNS_of (h0 : StepSplit) (h1 : FirstIsometryForward) (h2 : FirstIsometryBackward) (h3 : FirstIsometryUniqueness)
    (h4 : StepDu) (h5 : StepDuU) : AlgGAllNS := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' hT hq Zh₁ Zh₂ Z₁ Z₂ e₁ e₂ u₁ u₂ hrel hG₁ hG₂ hT0 hd₁ hd₂ hσ₁ hσ₂
  obtain ⟨c, hc⟩ := hq
  have hT'0 : T' ∈ 𝒪[F] := by
    have : T' = T - (g.q : F) ^ 2 * c := by rw [← hc]; ring
    rw [this]
    exact sub_mem hT0 (mul_mem (pow_mem g.q.2 2) c.2)
  have hq : ∃ c : 𝒪[F], T - T' = (g.q : F) ^ 2 * c := ⟨c, hc⟩
  let TT : M.R := ⟨g.e.symm (T, T'), mem_R_of hs _ ⟨T, hT0⟩ ⟨T', hT'0⟩ (g.q * c) (by simp)
    (by push_cast; rw [hc]; ring)⟩
  have hTT : g.e (TT : E) = (T, T') := by simp [TT]
  let Zs₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R :=
    Matrix.of fun a b => ⟨_, zsig_mem hs T T' c hc Zh₁ Z₁ e₁ a b⟩
  have eZs₁ : Zs₁.map M.R.subtype = HermSp.ZZplusOf M (Zh₁.map M.L.cj) T T' := by ext a b; rfl
  let Zs₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R :=
    Matrix.of fun a b => ⟨_, zsig_mem hs T T' c hc Zh₂ Z₂ e₂ a b⟩
  have eZs₂ : Zs₂.map M.R.subtype = HermSp.ZZplusOf M (Zh₂.map M.L.cj) T T' := by ext a b; rfl
  let Zσ₁ : M.Mat (r + 1) := ⟨Zs₁, by rw [eZs₁]; exact hσ₁⟩
  let Zσ₂ : M.Mat (r + 1) := ⟨Zs₂, by rw [eZs₂]; exact hσ₂⟩
  have eσ₁ : Zσ₁.Z.map M.R.subtype = HermSp.ZZplusOf M (Zh₁.map M.L.cj) T T' := eZs₁
  have eσ₂ : Zσ₂.Z.map M.R.subtype = HermSp.ZZplusOf M (Zh₂.map M.L.cj) T T' := eZs₂
  let Y₁ : M.Mat (r + 1) := ⟨Z₁, hd₁⟩
  let Y₂ : M.Mat (r + 1) := ⟨Z₂, hd₂⟩
  have H₁ : GHyp M g T T' TT Zh₁ Y₁ Zσ₁ := ⟨hT, hq, hTT, e₁, eσ₁, u₁, hG₁⟩
  have H₂ : GHyp M g T T' TT Zh₂ Y₂ Zσ₂ := ⟨hT, hq, hTT, e₂, eσ₂, u₂, hG₂⟩
  have H₁' := gHyp_cj H₁
  have H₂' := gHyp_cj H₂
  have hrel' := kapEq_cj (M := M) hrel
  show _ = Nat.card (IsoMbe Y₁.Z Y₂.Z)
  rw [h0 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel]
  refine Nat.card_congr
    { toFun := fun p => Classical.choose (h1 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel p.1.1
          p.2.1 p.2.2.2.1)
      invFun := fun γ =>
        ⟨(Classical.choose (h2 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel γ),
          Classical.choose (h2 F E M g hs r T T' TT _ _ Zσ₁ Zσ₂ Y₁ Y₂ H₁' H₂' hrel'
            (Classical.choose (h4 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel γ)))), by
          have s1 := Classical.choose_spec (h2 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel γ)
          have s4 := Classical.choose_spec (h4 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel γ)
          have s2 := Classical.choose_spec (h2 F E M g hs r T T' TT _ _ Zσ₁ Zσ₂ Y₁ Y₂ H₁' H₂' hrel'
            (Classical.choose (h4 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel γ)))
          exact ⟨s1.1, s2.1, s1.2.1, s2.2.1, s4 _ _ s1.2.2 s2.2.2⟩⟩
      left_inv := fun p => by
        have sf := Classical.choose_spec (h1 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel p.1.1
          p.2.1 p.2.2.2.1)
        set γ := Classical.choose (h1 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel p.1.1
          p.2.1 p.2.2.2.1)
        have s1 := Classical.choose_spec (h2 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel γ)
        have s4 := Classical.choose_spec (h4 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel γ)
        have s2 := Classical.choose_spec (h2 F E M g hs r T T' TT _ _ Zσ₁ Zσ₂ Y₁ Y₂ H₁' H₂' hrel'
            (Classical.choose (h4 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel γ)))
        have e1 := ind_det hs γ _ _ s1.2.2 sf
        apply Subtype.ext
        refine Prod.ext e1 ?_
        refine h5 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel p.1.1 _ _ ?_ p.2.2.2.2.2
        rw [← e1]
        exact s4 _ _ s1.2.2 s2.2.2
      right_inv := fun γ => by
        have s1 := Classical.choose_spec (h2 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel γ)
        refine h3 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel _ _ _
          (Classical.choose_spec (h1 F E M g hs r T T' TT Zh₁ Zh₂ Y₁ Y₂ Zσ₁ Zσ₂ H₁ H₂ hrel _ s1.1 s1.2.1))
          s1.2.2 }

theorem algGAllNS_holds : AlgGAllNS :=
  algGAllNS_of stepSplit_holds firstIso_forward_holds firstIso_backward_holds firstIso_uniqueness_holds (stepDu_of_lift stepLiftG) stepDuU

end Formalism.L2.SG.LocalCountModules.AlgGSplit
end
end

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

def ScaleChoiceP : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (g : SplitG M.L) (hs : M.split = some g) (r : ℕ) (T T' : F),
    (∃ u v : 𝒪[F], (u : F) * T = 1 ∧ (v : F) * T' = 1) → (∃ c : 𝒪[F], T - T' = (g.q : F) ^ 2 * c) →
    T ∈ 𝒪[F] →
  ∀ (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R),
    Z₁.map M.R.subtype = HermSp.ZZplusOf M Zh₁ T T' → Z₂.map M.R.subtype = HermSp.ZZplusOf M Zh₂ T T' →
    IsUnit Zh₁.det → IsUnit Zh₂.det →
    Zh₁.det * (Zh₂.submatrix Fin.castSucc Fin.castSucc).det =
      Zh₂.det * (Zh₁.submatrix Fin.castSucc Fin.castSucc).det →
    ∃ α : E, α * M.L.cj α = 1 ∧ α ∈ M.L.O ∧ (α - 1) * algebraMap F E ((g.q : F)⁻¹) ∈ M.L.O ∧
      ∃ Z₁' Z₂' : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R,
        Z₁'.map M.R.subtype = HermSp.ZZplusOf M (Zh₁ * dlast r α) T T' ∧
        Z₂'.map M.R.subtype = HermSp.ZZplusOf M (Zh₂ * dlast r α) T T' ∧
        IsUnit (Z₁'.map M.R.subtype).det ∧ IsUnit (Z₂'.map M.R.subtype).det ∧
        IsUnit (HermSp.ZZplusOf M ((Zh₁ * dlast r α).map M.L.cj) T T').det ∧
        IsUnit (HermSp.ZZplusOf M ((Zh₂ * dlast r α).map M.L.cj) T T').det ∧
        Nat.card (IsoMbe Z₁' Z₂') = Nat.card (IsoMbe Z₁ Z₂)

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ} (hs : M.split = some g)

theorem zz_split (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    HermSp.ZZplusOf M Zh T T' = ZZm g Zh T T' +
      Matrix.of fun a b => cor r a b (g.e.symm (T / (g.q : F), -T' / (g.q : F))) := by
  unfold ZZm
  ext a b
  simp only [Matrix.add_apply, Matrix.of_apply, cor]
  split_ifs
  · have h0 : g.e.symm (-T / (g.q : F), T' / (g.q : F)) + g.e.symm (T / (g.q : F), -T' / (g.q : F)) = 0 := by
      rw [← map_add (f := _), Prod.mk_add_mk]
      have e : (-T / (g.q : F) + T / (g.q : F), T' / (g.q : F) + -T' / (g.q : F)) = (0 : F × F) :=
        Prod.ext (by simp [neg_div]) (by simp [neg_div])
      rw [e, map_zero]
    rw [add_assoc, h0, add_zero]
  · simp


include hs in
theorem zz_unit_iff (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    IsUnit (HermSp.ZZplusOf M Zh T T').det ↔
      ph1 g Zh.det + T * ph1 g (Zh.submatrix Fin.castSucc Fin.castSucc).det ≠ 0 ∧
        ph2 g Zh.det + T' * ph2 g (Zh.submatrix Fin.castSucc Fin.castSucc).det ≠ 0 := by
  have hq : ((g.q : F)) ≠ 0 := fun h => g.q_irr.ne_zero (by ext; simpa using h)
  have hcor1 : (Matrix.of fun a b => cor r a b (g.e.symm (T / (g.q : F), -T' / (g.q : F)))).map (ph1 g) = Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG.cornerM r (T / (g.q : F)) := by
    ext a b
    simp only [Matrix.map_apply, Matrix.of_apply, cor, Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG.cornerM]
    split_ifs <;> simp [firstProj_apply]
  have hcor2 : (Matrix.of fun a b => cor r a b (g.e.symm (T / (g.q : F), -T' / (g.q : F)))).map (ph2 g) = Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG.cornerM r (-T' / (g.q : F)) := by
    ext a b
    simp only [Matrix.map_apply, Matrix.of_apply, cor, Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG.cornerM]
    split_ifs <;> simp [secondProj_apply]
  have hd1 : (Zh.map (ph1 g)).det = ph1 g Zh.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  have hd2 : (Zh.map (ph2 g)).det = ph2 g Zh.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  have hs1 : ((Zh.map (ph1 g)).submatrix Fin.castSucc Fin.castSucc).det =
      ph1 g (Zh.submatrix Fin.castSucc Fin.castSucc).det := by
    rw [Matrix.submatrix_map, RingHom.map_det, RingHom.mapMatrix_apply]
  have hs2 : ((Zh.map (ph2 g)).submatrix Fin.castSucc Fin.castSucc).det =
      ph2 g (Zh.submatrix Fin.castSucc Fin.castSucc).det := by
    rw [Matrix.submatrix_map, RingHom.map_det, RingHom.mapMatrix_apply]
  have e1 : ph1 g (HermSp.ZZplusOf M Zh T T').det = ((g.q : F)⁻¹) ^ (r + 1) *
      (ph1 g Zh.det + T * ph1 g (Zh.submatrix Fin.castSucc Fin.castSucc).det) := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, zz_split, Matrix.map_add _ (map_add _), zzMinus_firstProj_smul hs, hcor1,
      Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG.det_add_cornerM]
    have es : ∀ (c : F) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) F),
        ((c • A).submatrix Fin.castSucc Fin.castSucc).det = c ^ r * (A.submatrix Fin.castSucc Fin.castSucc).det := by
      intro c A
      have : (c • A).submatrix Fin.castSucc Fin.castSucc = c • A.submatrix Fin.castSucc Fin.castSucc := by
        ext i j
        rfl
      rw [this, Matrix.det_smul, Fintype.card_fin]
    rw [Matrix.det_smul, Fintype.card_fin, es, hd1, hs1]
    ring
  have e2 : ph2 g (HermSp.ZZplusOf M Zh T T').det = (-((g.q : F)⁻¹)) ^ (r + 1) *
      (ph2 g Zh.det + T' * ph2 g (Zh.submatrix Fin.castSucc Fin.castSucc).det) := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, zz_split, Matrix.map_add _ (map_add _), zzMinus_secondProj_transpose hs, hcor2,
      Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG.det_add_cornerM]
    have es : ∀ (c : F) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) F),
        ((c • A).submatrix Fin.castSucc Fin.castSucc).det = c ^ r * (A.submatrix Fin.castSucc Fin.castSucc).det := by
      intro c A
      have : (c • A).submatrix Fin.castSucc Fin.castSucc = c • A.submatrix Fin.castSucc Fin.castSucc := by
        ext i j
        rfl
      rw [this, Matrix.det_smul, Fintype.card_fin]
    have et : ∀ A : Matrix (Fin (r + 1)) (Fin (r + 1)) F,
        (A.transpose.submatrix Fin.castSucc Fin.castSucc).det = (A.submatrix Fin.castSucc Fin.castSucc).det := by
      intro A
      rw [← Matrix.transpose_submatrix, Matrix.det_transpose]
    rw [Matrix.det_smul, Fintype.card_fin, es, Matrix.det_transpose, et, hd2, hs2]
    ring
  rw [isUnit_iff_ph (g := g), e1, e2, mul_ne_zero_iff, mul_ne_zero_iff]
  simp only [ne_eq, pow_eq_zero_iff', inv_eq_zero, neg_eq_zero, hq, false_and, not_false_eq_true, true_and]

theorem dlast_det {K : Type} [CommRing K] (δ : K) : (dlast r δ).det = δ := by
  unfold dlast
  rw [Matrix.det_diagonal, Finset.prod_ite_eq']
  simp

theorem head_mul_dlast {K : Type} [CommRing K] (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (δ : K) :
    (A * dlast r δ).submatrix Fin.castSucc Fin.castSucc = A.submatrix Fin.castSucc Fin.castSucc := by
  ext i j
  simp [dlast, Matrix.mul_diagonal, Fin.castSucc_ne_last]

end Formalism.L2.SG.LocalCountModules.AlgGSplit
end
end

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ} (hs : M.split = some g)

include hs in
theorem zz_scale (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R) (hZ : Z.map M.R.subtype = HermSp.ZZplusOf M Zh T T')
    (u : F) (hu0 : u ≠ 0) (δ₁ δ₂ cc : M.R) (α : E) (he1 : g.e (δ₁ : E) = (u, 1))
    (he2 : g.e (δ₂ : E) = (1, u⁻¹)) (hcc : g.e (cc : E) = ((1 - u) * T / (g.q : F), (1 - u) * T' / (g.q : F)))
    (hα : g.e α = (u, u⁻¹)) :
    (dlast r δ₂ * (Z * dlast r δ₁ + Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then cc else 0)).map
        M.R.subtype = HermSp.ZZplusOf M (Zh * dlast r α) T T' := by
  ext a b
  have hZab : ((Z a b : M.R) : E) = HermSp.ZZplusOf M Zh T T' a b := by
    rw [← hZ]; rfl
  have hq : ((g.q : F)) ≠ 0 := by
    intro h
    exact g.q_irr.ne_zero (Subtype.ext h)
  simp only [HermSp.ZZplusOf, hs, Matrix.of_apply] at hZab
  simp only [HermSp.ZZplusOf, hs, Matrix.map_apply, Matrix.of_apply, dlast, Matrix.diagonal_mul,
    Matrix.mul_diagonal, Matrix.add_apply, Subring.coe_subtype]
  apply g.e.injective
  by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r
  · subst ha; subst hb
    simp only [and_self, if_true] at hZab ⊢
    push_cast
    rw [map_sub, map_mul, map_add (f := _), map_mul, hZab]
    simp only [map_sub, AlgEquiv.apply_symm_apply, he1, he2, hcc, hα, map_mul]
    ext <;> simp <;> field_simp <;> ring
  · simp only [ha, hb, and_false, if_false, if_true, and_true] at hZab ⊢
    push_cast
    simp only [sub_zero, add_zero] at hZab ⊢
    rw [map_mul, map_mul, hZab]
    simp only [AlgEquiv.apply_symm_apply, he2, hα, map_mul]
    ext <;> simp <;> field_simp
  · simp only [ha, hb, false_and, if_false, if_true] at hZab ⊢
    push_cast
    simp only [sub_zero, add_zero, one_mul] at hZab ⊢
    rw [map_mul, hZab]
    simp only [AlgEquiv.apply_symm_apply, he1, hα, map_mul]
    ext <;> simp <;> field_simp
  · simp only [ha, hb, false_and, and_false, if_false] at hZab ⊢
    push_cast
    simp only [sub_zero, add_zero, one_mul, mul_one] at hZab ⊢
    rw [hZab]

end Formalism.L2.SG.LocalCountModules.AlgGSplit
end
end

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

theorem nz1 {F : Type} [Field F] {A a t u : F} (hA : A ≠ 0) (h : u ≠ -t * a / A) : A * u + t * a ≠ 0 := by
  intro h0
  apply h
  rw [eq_div_iff hA]
  linear_combination h0

theorem nz2 {F : Type} [Field F] {B b t u : F} (hB : B ≠ 0) (ht : t ≠ 0) (hu : u ≠ 0) (h : u ≠ -B / (t * b)) :
    B * u⁻¹ + t * b ≠ 0 := by
  intro h0
  by_cases hb : b = 0
  · rw [hb, mul_zero, add_zero] at h0
    exact mul_ne_zero hB (inv_ne_zero hu) h0
  · apply h
    rw [eq_div_iff (mul_ne_zero ht hb)]
    have h1 : B + t * b * u = 0 := by
      have h2 := congrArg (· * u) h0
      simp only [add_mul, inv_mul_cancel_right₀ hu, zero_mul] at h2
      exact h2
    linear_combination h1

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem firstProj_conj_algebra (x : E) : ph1 g (M.L.cj x) = ph2 g x := by
  show (g.e (M.L.cj x)).1 = (g.e x).2
  rw [g.e_cj]
  rfl
theorem secondProj_conj_algebra (x : E) : ph2 g (M.L.cj x) = ph1 g x := by
  show (g.e (M.L.cj x)).2 = (g.e x).1
  rw [g.e_cj]
  rfl

theorem scaleChoice_holds : ScaleChoiceP := by
  intro F _ _ _ E _ _ _ _ M g hs r T T' hT hq hT0 Zh₁ Zh₂ Z₁ Z₂ e₁ e₂ u₁ u₂ hrel
  classical
  have hq0 := q_ne g
  obtain ⟨c0, hc⟩ := hq
  obtain ⟨uT, vT, huT, hvT⟩ := hT
  have hTne : T ≠ 0 := by rintro rfl; simp at huT
  have hT'ne : T' ≠ 0 := by rintro rfl; simp at hvT
  have hT'0 : T' ∈ 𝒪[F] := by
    have : T' = T - (g.q : F) ^ 2 * c0 := by rw [← hc]; ring
    rw [this]; exact sub_mem hT0 (mul_mem (pow_mem g.q.2 2) c0.2)
  have hu₁ := (isUnit_iff_ph (g := g) _).1 u₁
  have hu₂ := (isUnit_iff_ph (g := g) _).1 u₂
  set d₁ := (Zh₁.submatrix Fin.castSucc Fin.castSucc).det
  set d₂ := (Zh₂.submatrix Fin.castSucc Fin.castSucc).det

  let L : List F := [-T * ph1 g d₁ / ph1 g Zh₁.det, -T' * ph1 g d₁ / ph1 g Zh₁.det,
    -ph2 g Zh₁.det / (T' * ph2 g d₁), -ph2 g Zh₁.det / (T * ph2 g d₁),
    -T * ph1 g d₂ / ph1 g Zh₂.det, -T' * ph1 g d₂ / ph1 g Zh₂.det,
    -ph2 g Zh₂.det / (T' * ph2 g d₂), -ph2 g Zh₂.det / (T * ph2 g d₂)]
  let f : ℕ → F := fun k => ((1 + g.q ^ (k + 1) : 𝒪[F]) : F)
  have finj : Function.Injective f := by
    intro j k h
    have h' : (1 + g.q ^ (j + 1) : 𝒪[F]) = 1 + g.q ^ (k + 1) := Subtype.ext h
    have := pow_injective_of_not_isUnit g.q_irr.not_isUnit g.q_irr.ne_zero (add_left_cancel h')
    simpa using this
  obtain ⟨k, -, hk⟩ : ∃ k ∈ Finset.range 9, f k ∉ L.toFinset := by
    by_contra hcon
    push_neg at hcon
    have hsub : (Finset.range 9).image f ⊆ L.toFinset := fun x hx => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx; exact hcon k hk
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ finj, Finset.card_range] at h1
    have h2 : L.toFinset.card ≤ 8 := (List.toFinset_card_le L).trans (by simp [L])
    omega
  simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false, not_or, L] at hk
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := hk

  have hU : IsUnit (1 + g.q ^ (k + 1) : 𝒪[F]) := by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (-(g.q ^ (k + 1)) : 𝒪[F]) with h | h
    · exact absurd ((isUnit_pow_iff (Nat.succ_ne_zero k)).1 ((IsUnit.neg_iff _).1 h)) g.q_irr.not_isUnit
    · rwa [sub_neg_eq_add] at h
  obtain ⟨uO, huOd⟩ : ∃ uO : 𝒪[F], uO = 1 + g.q ^ (k + 1) := ⟨_, rfl⟩
  obtain ⟨u', hu'd⟩ : ∃ u' : 𝒪[F], u' = ((hU.unit⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) := ⟨_, rfl⟩
  have huu : (uO : F) * (u' : F) = 1 := by
    have h := congrArg Subtype.val hU.mul_val_inv
    rw [huOd, hu'd]
    exact_mod_cast h
  obtain ⟨u, hud⟩ : ∃ u : F, u = (uO : F) := ⟨_, rfl⟩
  rw [← hud] at huu
  have hu0 : u ≠ 0 := left_ne_zero_of_mul_eq_one huu
  have hu' : (u' : F) = u⁻¹ := eq_inv_of_mul_eq_one_right huu
  have huv : u = 1 + (g.q : F) ^ (k + 1) := by rw [hud, huOd]; push_cast; ring
  have huvO : (uO : F) = 1 + (g.q : F) ^ (k + 1) := by rw [← hud, huv]
  have hfk : f k = u := by simp only [f]; push_cast; rw [huv]

  obtain ⟨α, hαd⟩ : ∃ α : E, α = g.e.symm (u, u⁻¹) := ⟨_, rfl⟩
  have hα : g.e α = (u, u⁻¹) := by simp [hαd]
  have mq : (g.q : F) ^ k ∈ 𝒪[F] := pow_mem g.q.2 k
  let δ₁ : M.R := ⟨g.e.symm (u, 1), mem_R_of hs _ uO 1 (g.q ^ k) (by simp [hud]) (by push_cast; rw [huvO]; ring)⟩
  let δ₁i : M.R := ⟨g.e.symm (u⁻¹, 1), mem_R_of hs _ u' 1 (-(u' * g.q ^ k)) (by simp [hu'])
    (by push_cast; rw [hu']; field_simp; rw [huv]; ring)⟩
  let δ₂ : M.R := ⟨g.e.symm (1, u⁻¹), mem_R_of hs _ 1 u' (u' * g.q ^ k) (by simp [hu'])
    (by push_cast; rw [hu']; field_simp; rw [huv]; ring)⟩
  let δ₂i : M.R := ⟨g.e.symm (1, u), mem_R_of hs _ 1 uO (-(g.q ^ k)) (by simp [hud])
    (by push_cast; rw [huvO]; ring)⟩
  let cc : M.R := ⟨g.e.symm ((1 - u) * T / (g.q : F), (1 - u) * T' / (g.q : F)),
    mem_R_of hs _ (-(g.q ^ k) * ⟨T, hT0⟩) (-(g.q ^ k) * ⟨T', hT'0⟩) (-(g.q ^ (k + 1)) * c0)
      (by rw [AlgEquiv.apply_symm_apply]; push_cast; rw [huv]; refine Prod.ext ?_ ?_ <;> (simp only; field_simp; ring))
      (by push_cast; linear_combination (-(g.q : F) ^ k) * hc)⟩
  have he1 : g.e (δ₁ : E) = (u, 1) := by simp [δ₁]
  have he2 : g.e (δ₂ : E) = (1, u⁻¹) := by simp [δ₂]
  have hcc : g.e (cc : E) = ((1 - u) * T / (g.q : F), (1 - u) * T' / (g.q : F)) := by simp [cc]
  have hδ₁ : IsUnit δ₁ := isUnit_iff_exists_inv.2 ⟨δ₁i, by
    apply Subtype.ext; apply g.e.injective
    simp [δ₁, δ₁i, hu0]⟩
  have hδ₂ : δ₂ * δ₂i = 1 := by
    apply Subtype.ext; apply g.e.injective
    simp [δ₂, δ₂i, hu0]
  let C : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R := Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then cc else 0
  refine ⟨α, ?_, ?_, ?_, dlast r δ₂ * (Z₁ * dlast r δ₁ + C), dlast r δ₂ * (Z₂ * dlast r δ₁ + C),
    zz_scale hs Zh₁ T T' Z₁ e₁ u hu0 δ₁ δ₂ cc α he1 he2 hcc hα,
    zz_scale hs Zh₂ T T' Z₂ e₂ u hu0 δ₁ δ₂ cc α he1 he2 hcc hα, ?_, ?_, ?_, ?_, ?_⟩
  · apply g.e.injective
    rw [map_mul, e_cjA, hα, map_one]
    refine Prod.ext ?_ ?_ <;> simp [hu0]
  · exact mem_O_of_comp g _ (by rw [hα, hud]; exact uO.2) (by rw [hα, ← hu']; exact u'.2)
  · refine mem_O_of_comp g _ ?_ ?_
    · rw [map_mul, map_sub, hα, map_one, Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG.e_alg]
      have : (u - 1) * (g.q : F)⁻¹ = (g.q : F) ^ k := by rw [huv]; field_simp; ring
      simp only [Prod.fst_mul, Prod.fst_sub, Prod.fst_one]
      rw [this]; exact mq
    · rw [map_mul, map_sub, hα, map_one, Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG.e_alg]
      have : (u⁻¹ - 1) * (g.q : F)⁻¹ = -((u' : F) * (g.q : F) ^ k) := by
        rw [hu']; field_simp; rw [huv]; ring
      simp only [Prod.snd_mul, Prod.snd_sub, Prod.snd_one]
      rw [this]; exact neg_mem (mul_mem u'.2 mq)
  · rw [zz_scale hs Zh₁ T T' Z₁ e₁ u hu0 δ₁ δ₂ cc α he1 he2 hcc hα, zz_unit_iff hs, Matrix.det_mul, dlast_det,
      head_mul_dlast, map_mul, map_mul, firstProj_apply (g := g) α, secondProj_apply (g := g) α, hα]
    rw [hfk] at b1 b3
    exact ⟨nz1 hu₁.1 b1, nz2 hu₁.2 hT'ne hu0 b3⟩
  · rw [zz_scale hs Zh₂ T T' Z₂ e₂ u hu0 δ₁ δ₂ cc α he1 he2 hcc hα, zz_unit_iff hs, Matrix.det_mul, dlast_det,
      head_mul_dlast, map_mul, map_mul, firstProj_apply (g := g) α, secondProj_apply (g := g) α, hα]
    rw [hfk] at b5 b7
    exact ⟨nz1 hu₂.1 b5, nz2 hu₂.2 hT'ne hu0 b7⟩
  · rw [zz_unit_iff hs, det_map_cj, head_map_cj, firstProj_conj_algebra, firstProj_conj_algebra, secondProj_conj_algebra, secondProj_conj_algebra, Matrix.det_mul, dlast_det,
      head_mul_dlast, map_mul, map_mul, firstProj_apply (g := g) α, secondProj_apply (g := g) α, hα]
    rw [hfk] at b2 b4
    exact ⟨nz2 hu₁.2 hTne hu0 b4, nz1 hu₁.1 b2⟩
  · rw [zz_unit_iff hs, det_map_cj, head_map_cj, firstProj_conj_algebra, firstProj_conj_algebra, secondProj_conj_algebra, secondProj_conj_algebra, Matrix.det_mul, dlast_det,
      head_mul_dlast, map_mul, map_mul, firstProj_apply (g := g) α, secondProj_apply (g := g) α, hα]
    rw [hfk] at b6 b8
    exact ⟨nz2 hu₂.2 hTne hu0 b8, nz1 hu₂.1 b6⟩
  · exact (card_isoMbe_lastRow _ _ δ₂ δ₂i hδ₂).symm.trans (card_isoMbe_lastCol Z₁ Z₂ δ₁ cc hδ₁).symm

end Formalism.L2.SG.LocalCountModules.AlgGSplit
