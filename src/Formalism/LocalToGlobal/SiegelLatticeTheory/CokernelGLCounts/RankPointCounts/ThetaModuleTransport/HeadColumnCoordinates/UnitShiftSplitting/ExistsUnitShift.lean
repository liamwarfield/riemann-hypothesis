module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.CornerDeterminantCounts.ThetaMbeU

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.LocCntUG
namespace Formalism.L2.SG.LocalCountModules.LocCntUG

def LocCntUG : Prop :=
  Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, Formalism.L2.SG.LsDatumA.ModSideU M r n true)

end Formalism.L2.SG.LocalCountModules.LocCntUG
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.ThetaMbeG
noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def ThetaMbeG (M : Model F E) (r n : ℕ) : Prop :=
  M.split.isSome = true →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    IsUnit (H.Dl t₁.f t₁.f' r) →
    ∀ (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R), Z₁.map M.R.subtype = H.ZZplus t₁ →
      Z₂.map M.R.subtype = HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T' →
      IsUnit (headDet M Z₂) →
      Nat.card (Theta H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ') = Nat.card (IsoMbe Z₁ Z₂)

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.DetUpdateRowLastSingle
noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG

variable {R : Type} [CommRing R] {r : ℕ}

def cornerM (r : ℕ) (c : R) : Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then c else 0

theorem cornerM_castSucc_left (c : R) (a : Fin r) (b : Fin (r + 1)) :
    cornerM r c a.castSucc b = 0 := by
  simp [cornerM, (Fin.castSucc_lt_last a).ne]

theorem cornerM_castSucc_right (c : R) (a : Fin (r + 1)) (b : Fin r) :
    cornerM r c a b.castSucc = 0 := by
  simp [cornerM, (Fin.castSucc_lt_last b).ne]

theorem cornerM_last (c : R) : cornerM r c (Fin.last r) (Fin.last r) = c := by
  simp [cornerM]

theorem head_add_cornerM (A : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (c : R) :
    (A + cornerM r c).submatrix Fin.castSucc Fin.castSucc = A.submatrix Fin.castSucc Fin.castSucc := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.add_apply, cornerM_castSucc_left, add_zero]

theorem det_updateRow_last_single (A : Matrix (Fin (r + 1)) (Fin (r + 1)) R) :
    (A.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)).det =
      (A.submatrix Fin.castSucc Fin.castSucc).det := by
  have hsub : (A.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)).submatrix Fin.castSucc
      Fin.castSucc = A.submatrix Fin.castSucc Fin.castSucc := by
    ext a b
    simp [Matrix.updateRow_ne (Fin.castSucc_lt_last a).ne]
  rw [Matrix.det_succ_row _ (Fin.last r), Finset.sum_eq_single (Fin.last r)]
  · rw [Fin.succAbove_last, hsub, Matrix.updateRow_self, Pi.single_eq_same, mul_one,
      Fin.val_last, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  · intro j _ hj
    rw [Matrix.updateRow_self, Pi.single_eq_of_ne hj, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem det_add_cornerM (A : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (c : R) :
    (A + cornerM r c).det = A.det + c * (A.submatrix Fin.castSucc Fin.castSucc).det := by
  have h : A + cornerM r c =
      A.updateRow (Fin.last r) (A (Fin.last r) + c • Pi.single (Fin.last r) 1) := by
    ext i j
    by_cases hi : i = Fin.last r
    · subst hi
      by_cases hj : j = Fin.last r
      · subst hj
        simp [cornerM]
      · simp [cornerM, hj, Pi.single_apply]
    · simp [cornerM, hi, Matrix.updateRow_ne hi]
  rw [h, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self,
    det_updateRow_last_single]

theorem headCols_add_cornerM (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (c : R) :
    headCols (Z + cornerM r c) = headCols Z := by
  unfold headCols
  simp only [Matrix.add_apply, cornerM_castSucc_right, add_zero]

def mbeShift (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (c : R) : MbMod (Z + cornerM r c) ≃ₗ[R] MbMod Z :=
  Submodule.quotEquivOfEq _ _ (headCols_add_cornerM Z c)

theorem mbeShift_mk (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (c : R) (v : Fin (r + 1) → R) :
    mbeShift Z c (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := rfl

theorem mbeShift_eCl (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (c : R) :
    mbeShift Z c (eCl (Z + cornerM r c)) = eCl Z := rfl

theorem mbeShift_bCls (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (c : R) :
    mbeShift Z c (bCls (Z + cornerM r c)) = bCls Z + c • eCl Z := by
  unfold bCls eCl
  rw [mbeShift_mk, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]
  congr 1
  funext i
  by_cases hi : i = Fin.last r
  · subst hi
    simp [cornerM]
  · simp [cornerM, hi, Pi.single_apply]

theorem card_isoMbe_shift (Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (c : R) :
    Nat.card (IsoMbe (Z₁ + cornerM r c) (Z₂ + cornerM r c)) = Nat.card (IsoMbe Z₁ Z₂) := by
  have he₁ := mbeShift_eCl Z₁ c
  have he₂ := mbeShift_eCl Z₂ c
  have hb₁ := mbeShift_bCls Z₁ c
  have hb₂ := mbeShift_bCls Z₂ c
  refine Nat.card_congr
    { toFun := fun γ => ⟨((mbeShift Z₁ c).symm.trans γ.1).trans (mbeShift Z₂ c), ?_, ?_⟩
      invFun := fun δ => ⟨((mbeShift Z₁ c).trans δ.1).trans (mbeShift Z₂ c).symm, ?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have k : (mbeShift Z₁ c).symm (bCls Z₁) =
        bCls (Z₁ + cornerM r c) - c • eCl (Z₁ + cornerM r c) := by
      rw [LinearEquiv.symm_apply_eq, map_sub, map_smul, hb₁, he₁, add_sub_cancel_right]
    simp only [LinearEquiv.trans_apply, k, map_sub, map_smul, γ.2.1, γ.2.2, hb₂, he₂,
      add_sub_cancel_right]
  · have k : (mbeShift Z₁ c).symm (eCl Z₁) = eCl (Z₁ + cornerM r c) := by
      rw [LinearEquiv.symm_apply_eq, he₁]
    simp only [LinearEquiv.trans_apply, k, γ.2.2, he₂]
  · simp only [LinearEquiv.trans_apply, hb₁, map_add (f := _), map_smul, δ.2.1, δ.2.2]
    rw [← map_smul, ← map_add (f := _), LinearEquiv.symm_apply_eq, hb₂]
  · simp only [LinearEquiv.trans_apply, he₁, δ.2.2]
    rw [LinearEquiv.symm_apply_eq, he₂]
  · intro γ
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    simp
  · intro δ
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    simp

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG
end
end

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem e_alg (g : SplitG M.L) (s : F) : g.e (algebraMap F E s) = (s, s) := by
  rw [AlgEquiv.commutes]
  rfl

theorem cj_alg (s : F) : M.L.cj (algebraMap F E s) = algebraMap F E s := M.L.cj.commutes s

theorem comp_mem_O (g : SplitG M.L) {x : E} (hx : x ∈ M.L.O) :
    (g.e x).1 ∈ 𝒪[F] ∧ (g.e x).2 ∈ 𝒪[F] := by
  have hxI : IsIntegral 𝒪[F] x := (M.L.O_def x).mp hx
  have key : ∀ f : E →ₐ[F] F, f x ∈ 𝒪[F] := fun f =>
    (Valuation.integer.integers (valuation F)).mem_of_integral (hxI.map (f.restrictScalars 𝒪[F]))
  exact ⟨key ((AlgHom.fst F F F).comp g.e.toAlgHom), key ((AlgHom.snd F F F).comp g.e.toAlgHom)⟩

theorem mem_R_of {g : SplitG M.L} (hs : M.split = some g) {x : E} (h1 : (g.e x).1 ∈ 𝒪[F])
    (h2 : (g.e x).2 ∈ 𝒪[F]) (h3 : ∃ c ∈ 𝒪[F], (g.e x).1 - (g.e x).2 = (g.q : F) * c) : x ∈ M.R := by
  obtain ⟨c, hc, hce⟩ := h3
  unfold Model.R
  rw [hs]
  dsimp only
  rw [Subring.mem_comap, Subring.mem_map]
  refine ⟨(⟨(g.e x).1, h1⟩, ⟨(g.e x).2, h2⟩), ?_, rfl⟩
  rw [RingHom.mem_eqLocus, RingHom.comp_apply, RingHom.comp_apply, Ideal.Quotient.eq,
    Ideal.mem_span_singleton']
  refine ⟨⟨c, hc⟩, Subtype.ext ?_⟩
  show c * (g.q : F) = (g.e x).1 - (g.e x).2
  rw [hce, mul_comm]

theorem alg_mem_R {g : SplitG M.L} (hs : M.split = some g) (a : 𝒪[F]) : algebraMap F E a ∈ M.R := by
  have he := e_alg g (a : F)
  refine mem_R_of hs ?_ ?_ ⟨0, zero_mem _, ?_⟩ <;> rw [he]
  · exact a.2
  · exact a.2
  · simp

theorem isUnit_of_comp (g : SplitG M.L) {y : E} (h1 : (g.e y).1 ≠ 0) (h2 : (g.e y).2 ≠ 0) : IsUnit y := by
  have hu : IsUnit (g.e y) := Prod.isUnit_iff.mpr ⟨h1.isUnit, h2.isUnit⟩
  exact (isUnit_map_iff g.e y).mp hu

theorem exists_unit_shift (g : SplitG M.L) (u : E) : ∃ a : 𝒪[F], IsUnit (u + algebraMap F E a) := by
  have hq0 : (g.q : F) ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext h)
  have hq1 : (g.q : F) ≠ 1 := fun h => g.q_irr.not_isUnit (by
    rw [show g.q = 1 from Subtype.ext h]
    exact isUnit_one)
  have hsh : ∀ a : 𝒪[F], IsUnit (u + algebraMap F E a) ∨
      ((g.e u).1 + (a : F) = 0 ∨ (g.e u).2 + (a : F) = 0) := by
    intro a
    by_cases h1 : (g.e u).1 + (a : F) = 0
    · exact Or.inr (Or.inl h1)
    by_cases h2 : (g.e u).2 + (a : F) = 0
    · exact Or.inr (Or.inr h2)
    left
    apply isUnit_of_comp g
    · rw [map_add (f := _), e_alg g]
      exact h1
    · rw [map_add (f := _), e_alg g]
      exact h2
  rcases hsh 0 with h0 | h0
  · exact ⟨0, h0⟩
  rcases hsh 1 with h1 | h1
  · exact ⟨1, h1⟩
  rcases hsh g.q with h2 | h2
  · exact ⟨g.q, h2⟩
  exfalso
  push_cast at h0 h1
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    first
    | exact one_ne_zero (by linear_combination h1 - h0)
    | exact hq0 (by linear_combination h2 - h0)
    | exact hq1 (by linear_combination h2 - h1)

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG
