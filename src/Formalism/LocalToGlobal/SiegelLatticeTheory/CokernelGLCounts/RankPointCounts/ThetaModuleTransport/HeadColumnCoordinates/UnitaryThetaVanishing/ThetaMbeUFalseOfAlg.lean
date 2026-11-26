module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.CoordLHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryThetaVanishing.StepsL

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryThetaVanishing.CoordUHolds
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryThetaVanishing.MemSpanOfSharpU
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryThetaVanishing.HOmPOmPU
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryThetaVanishing.ThetaMbeUFalseOf
noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem gdet_fix (H : HermSp M V) {r : ℕ} (f f' : Fin (r + 1) → V) (T T' : F) :
    M.L.cj (H.Gdet f f' T T') = H.Gdet f f' T T' := by
  have hn : ∀ x : E, M.L.cj (H.normE x) = H.normE x := by
    intro x
    rw [HermSp.normE, map_mul, M.L.cj_cj, mul_comm]
  simp only [HermSp.Gdet, map_sub, map_mul, AlgEquiv.commutes, hn]

theorem gdet_unit (H : HermSp M V) {r : ℕ} (f f' : Fin (r + 1) → V) (T T' : F)
    (hG : H.Gdet f f' T T' ≠ 0) : IsUnit (H.Gdet f f' T T') := by
  obtain ⟨a, ha⟩ := (M.L.cj_fix _).mp (gdet_fix H f f' T T')
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hG
    rw [← ha, map_zero]
  rw [← ha]
  exact (IsUnit.mk0 a ha0).map (algebraMap F E)

theorem gdet_rel (H : HermSp M V) {r : ℕ} (f₁ f₁' f₂ f₂' : Fin (r + 1) → V) (T T' : F)
    (hrel : H.Dl f₁ f₁' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl f₁ f₁' (r + 1)) :
    H.Gdet f₂ f₂' T T' * H.normE (H.Dl f₁ f₁' (r + 1)) =
      H.normE (H.Dl f₂ f₂' (r + 1)) * H.Gdet f₁ f₁' T T' := by
  have hmul : ∀ x y : E, H.normE x * H.normE y = H.normE (x * y) := by
    intro x y
    simp only [HermSp.normE, map_mul]
    ring
  have h := congrArg H.normE hrel
  rw [← hmul, ← hmul] at h
  simp only [HermSp.Gdet]
  linear_combination (algebraMap F E (T * T')) * h

theorem unit_gramC_of (H : HermSp M V) {r : ℕ} (f f' : Fin (r + 1) → V) (T T' : F)
    (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T')
    (hD1 : IsUnit (H.Dl f f' (r + 1))) (hG : IsUnit (H.Gdet f f' T T')) :
    IsUnit (gramC (M.L.cj : E →+* E) (H.Zhat f f') (algebraMap F E T) (algebraMap F E T')).det := by
  rw [gramC_eq H f f' T T' hF hF', Matrix.det_transpose]
  obtain ⟨s, hs, hdet⟩ := gram_det H f f' T T' hF hF' hD1
  have : (H.gram (Sum.elim f f')).det = H.Gdet f f' T T' * s := by
    rw [← hdet, mul_assoc, hs, mul_one]
  rw [this]
  exact hG.mul ⟨⟨s, s, hs, hs⟩, rfl⟩

theorem thetaMbeU_false_of (h1 : CoordU) (h2 : AlgAll) (M : Model F E) (r n : ℕ) :
    Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUL.ThetaMbeU M r n false := by
  obtain ⟨L, sp, mu⟩ := M
  cases sp with
  | some g => intro hmode; simp at hmode
  | none =>
  intro _ V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD Z₁ Z₂ e₁ e₂
  have hs : (⟨L, none, mu⟩ : Model F E).split = none := rfl
  have z₁ : Z₁.Z.map (Model.R ⟨L, none, mu⟩).subtype = H.Zhat t₁.f t₁.f' := by
    rw [e₁]; exact zzplusOf_none hs _ _ _
  have z₂ : Z₂.Z.map (Model.R ⟨L, none, mu⟩).subtype = H.Zhat f₂ f₂' := by
    rw [e₂]; exact zzplusOf_none hs _ _ _
  have hU1 : IsUnit (H.Dl t₁.f t₁.f' (r + 1)) := dl_succ_unit hyp
  have hU2 : IsUnit (H.Dl f₂ f₂' (r + 1)) := by rw [dl_full, ← z₂]; exact Z₂.unit
  have hrel : H.Dl t₁.f t₁.f' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl t₁.f t₁.f' (r + 1) :=
    hyp.2.2.2.1.2.2.2.2.2
  have hint : ∀ a b, H.Zhat f₂ f₂' a b ∈ L.O := by
    intro a b
    rw [← z₂]
    exact (Z₂.Z a b).2
  have hT : t₁.T ∈ 𝒪[F] := hyp.1.1.2.1.2.2.2.1
  have hT' : t₁.T' ∈ 𝒪[F] := hyp.1.1.2.2.1.2.2.2.1
  have hF₁ : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f t₁.T := ⟨hyp.1.1.2.1.2.1, hyp.1.1.2.1.2.2.1⟩
  have hF₁' : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f' t₁.T' := ⟨hyp.1.1.2.2.1.2.1, hyp.1.1.2.2.1.2.2.1⟩
  have hGu₁ : IsUnit (H.Gdet t₁.f t₁.f' t₁.T t₁.T') := gdet_unit H _ _ _ _ hyp.1.1.2.2.2.2.1
  have hGu₂ : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T') := by
    have hN₂ : IsUnit (H.normE (H.Dl f₂ f₂' (r + 1))) := hU2.mul (hU2.map L.cj)
    have := gdet_rel H t₁.f t₁.f' f₂ f₂' t₁.T t₁.T' hrel
    have hp : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T' * H.normE (H.Dl t₁.f t₁.f' (r + 1))) := by
      rw [this]; exact hN₂.mul hGu₁
    exact isUnit_of_mul_isUnit_left hp
  have hG1 := unit_gramC_of H _ _ _ _ hF₁ hF₁' hU1 hGu₁
  have hG2 := unit_gramC_of H _ _ _ _ hyp.2.1 hyp.2.2.1 hU2 hGu₂
  have hh : ((Z₁.Z.map (Model.R ⟨L, none, mu⟩).subtype).submatrix Fin.castSucc Fin.castSucc).det *
      (Z₂.Z.map (Model.R ⟨L, none, mu⟩).subtype).det =
      ((Z₂.Z.map (Model.R ⟨L, none, mu⟩).subtype).submatrix Fin.castSucc Fin.castSucc).det *
      (Z₁.Z.map (Model.R ⟨L, none, mu⟩).subtype).det := by
    rw [z₁, z₂, ← dl_eq_det, ← dl_eq_det, ← dl_full, ← dl_full]
    exact hrel
  rw [← z₁] at hG1
  rw [← z₂] at hG2
  rw [h1 F E ⟨L, none, mu⟩ hs r n V H hn t₁ f₂ f₂' φ φ' hyp hD hU2 hint, ← z₁, ← z₂]
  exact h2 E L.O (L.cj : E →+* E) (fun x => L.cj_cj x) (fun x hx => cj_mem_O L hx)
    r _ _ (Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O L ⟨t₁.T, hT⟩) (Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O L ⟨t₁.T', hT'⟩)
    (AlgEquiv.commutes _ _) (AlgEquiv.commutes _ _) Z₁.Z Z₂.Z Z₁.unit Z₂.unit hh hG1 hG2

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU
end
end

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {r : ℕ}

def kapU (f f' : Fin (r + 1) → V) : E := Ring.inverse (H.Dl f f' (r + 1)) * H.Dl f f' r

theorem h_om'_f'U (f f' : Fin (r + 1) → V) (T' : F) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') (b : Fin (r + 1)) :
    H.h (H.om' f f') (f' b) = if b = Fin.last r then H.Dl f f' r * -algebraMap F E T' else 0 := by
  unfold HermSp.om'
  rw [h_sum_smul_left]
  by_cases hb : b = Fin.last r
  · subst hb
    rw [if_pos rfl, Finset.sum_eq_single (Fin.last r)]
    · rw [hF'.2, adj_last]
    · intro c _ hc
      rw [hF'.1 c (Fin.last r) (Or.inl hc), mul_zero]
    · simp
  · rw [if_neg hb]
    apply Finset.sum_eq_zero
    intro c _
    rw [hF'.1 c b (Or.inr hb), mul_zero]

theorem h_om'_om'U (f f' : Fin (r + 1) → V) (T' : F) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') :
    H.h (H.om' f f') (H.om' f f') = M.L.cj (H.Dl f f' r) * (H.Dl f f' r * -algebraMap F E T') := by
  have e := h_sum_smul_left (H := H) (fun c => (H.Zhat f f').adjugate c (Fin.last r)) f' (H.om' f f')
  change H.h (∑ c, (H.Zhat f f').adjugate c (Fin.last r) • f' c) (H.om' f f') = _
  rw [e, Finset.sum_eq_single (Fin.last r)]
  · rw [H.h_herm, h_om'_f'U H f f' T' hF', if_pos rfl, adj_last, map_mul, map_neg, AlgEquiv.commutes]
    ring
  · intro c _ hc
    rw [H.h_herm, h_om'_f'U H f f' T' hF', if_neg hc, map_zero, mul_zero]
  · simp

private theorem hermSp_h_smul_right_eq_cj_mul' (x y : V) (a : E) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [H.h_herm, H.h_smul_left, map_mul, ← H.h_herm]

theorem h_omP_omPU (f f' : Fin (r + 1) → V) (T' : F) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') :
    H.h (omP H f f') (omP H f f') = -(algebraMap F E T') * (kapU H f f' * M.L.cj (kapU H f f')) := by
  unfold omP kapU
  rw [H.h_smul_left, hermSp_h_smul_right_eq_cj_mul', h_om'_om'U H f f' T' hF', map_mul]
  ring

theorem eta_mul (f f' : Fin (r + 1) → V) (T T' : F) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T')
    (hD : IsUnit (H.Dl f f' (r + 1))) :
    (1 + algebraMap F E T * H.h (omP H f f') (omP H f f')) * H.normE (H.Dl f f' (r + 1)) =
      H.Gdet f f' T T' := by
  rw [h_omP_omPU H f f' T' hF']
  unfold kapU HermSp.Gdet HermSp.normE
  have hinv : Ring.inverse (H.Dl f f' (r + 1)) * H.Dl f f' (r + 1) = 1 := Ring.inverse_mul_cancel _ hD
  have hinv' : M.L.cj (Ring.inverse (H.Dl f f' (r + 1))) * M.L.cj (H.Dl f f' (r + 1)) = 1 := by
    rw [← map_mul, hinv, map_one]
  rw [map_mul, map_mul (algebraMap F E)]
  linear_combination (-(algebraMap F E T) * algebraMap F E T' * H.Dl f f' r * M.L.cj (H.Dl f f' r) *
      M.L.cj (Ring.inverse (H.Dl f f' (r + 1))) * M.L.cj (H.Dl f f' (r + 1))) * hinv +
    (-(algebraMap F E T) * algebraMap F E T' * H.Dl f f' r * M.L.cj (H.Dl f f' r)) * hinv'

theorem eta_unit (f f' : Fin (r + 1) → V) (T T' : F) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T')
    (hD : IsUnit (H.Dl f f' (r + 1))) (hG : IsUnit (H.Gdet f f' T T')) :
    IsUnit (1 + algebraMap F E T * H.h (omP H f f') (omP H f f')) :=
  isUnit_of_mul_isUnit_left (by rw [eta_mul H f f' T T' hF' hD]; exact hG)

theorem mem_X_ofU (f f' : Fin (r + 1) → V) (T T' : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') (hD : IsUnit (H.Dl f f' (r + 1))) (hG : IsUnit (H.Gdet f f' T T'))
    (v : V) (hv : v ∈ Submodule.span E (Set.range (Sum.elim f f')))
    (h1 : ∀ a, H.h v (f a) = 0) (h2 : H.h (H.om' f f') v = 0) : v ∈ H.X f := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hv
  rw [Fintype.sum_sum_type] at h1 h2 ⊢
  simp only [Sum.elim_inl, Sum.elim_inr] at h1 h2 ⊢
  have hu : IsUnit (H.Zhat f f').det := by rw [← dl_full]; exact hD
  have hZ : (H.Zhat f f').mulVec (fun b => c (Sum.inr b)) =
      Pi.single (Fin.last r) (algebraMap F E T * c (Sum.inl (Fin.last r))) := by
    funext a
    have := h1 a
    rw [H.h_add_left, h_sum_left, h_sum_left] at this
    simp only [h_frame H f T hF] at this
    rw [Finset.sum_eq_single (Fin.last r) (fun b _ hb => by simp [hb]) (by simp)] at this
    have e : (H.Zhat f f').mulVec (fun b => c (Sum.inr b)) a = ∑ b, c (Sum.inr b) * H.h (f' b) (f a) := by
      rw [Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun b _ => mul_comm _ _
    rw [e]
    by_cases ha : a = Fin.last r
    · subst ha
      simp only [and_self, if_true] at this
      rw [Pi.single_eq_same]
      linear_combination this
    · simp only [ha, false_and, if_false, mul_zero, zero_add] at this
      rw [Pi.single_eq_of_ne ha]
      exact this
  have hc'eq : (fun b => c (Sum.inr b)) =
      (H.Zhat f f')⁻¹.mulVec (Pi.single (Fin.last r) (algebraMap F E T * c (Sum.inl (Fin.last r)))) := by
    rw [← hZ, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  have hcl' : c (Sum.inr (Fin.last r)) = kapU H f f' * (algebraMap F E T * c (Sum.inl (Fin.last r))) := by
    have := congrFun hc'eq (Fin.last r)
    have hs : Pi.single (Fin.last r) (algebraMap F E T * c (Sum.inl (Fin.last r))) =
        (algebraMap F E T * c (Sum.inl (Fin.last r))) • Pi.single (Fin.last r) (1 : E) := by
      ext i
      by_cases hi : i = Fin.last r <;> simp [hi]
    rw [hs, Matrix.mulVec_smul, Matrix.mulVec_single_one, Pi.smul_apply, Matrix.col_apply, smul_eq_mul,
      Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, adj_last, ← dl_full] at this
    rw [kapU]
    exact this.trans (by ring)
  have hl : c (Sum.inl (Fin.last r)) = 0 := by
    rw [h_add_right, h_sum_right, h_sum_right] at h2
    simp only [h_om'_f, h_om'_f'U H f f' T' hF'] at h2
    rw [Finset.sum_eq_single (Fin.last r) (fun b _ hb => by rw [if_neg hb, mul_zero]) (by simp),
      Finset.sum_eq_single (Fin.last r) (fun b _ hb => by rw [if_neg hb, mul_zero]) (by simp),
      if_pos rfl, if_pos rfl, ← dl_full, hcl', kapU, map_mul, map_mul, map_mul, AlgEquiv.commutes] at h2
    have h3 : M.L.cj (H.Dl f f' (r + 1)) * M.L.cj (Ring.inverse (H.Dl f f' (r + 1))) = 1 := by
      rw [← map_mul, Ring.mul_inverse_cancel _ hD, map_one]
    have hmul : M.L.cj (c (Sum.inl (Fin.last r))) * H.Gdet f f' T T' = 0 := by
      unfold HermSp.Gdet HermSp.normE
      rw [(algebraMap F E).map_mul]
      linear_combination (M.L.cj (H.Dl f f' (r + 1))) * h2 +
        (algebraMap F E T * algebraMap F E T' * H.Dl f f' r * M.L.cj (H.Dl f f' r) *
          M.L.cj (c (Sum.inl (Fin.last r)))) * h3
    have h4 := hG.mul_left_eq_zero.1 hmul
    have := congrArg M.L.cj h4
    rwa [M.L.cj_cj, map_zero] at this
  have hp'' : ∀ b, c (Sum.inr b) = 0 := by
    intro b
    have := congrFun hc'eq b
    rw [hl, mul_zero, Pi.single_zero, Matrix.mulVec_zero] at this
    exact this
  simp only [hp'', zero_smul, Finset.sum_const_zero, add_zero]
  rw [Fin.sum_univ_castSucc, hl, zero_smul, add_zero]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU
end
end

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {r : ℕ}

def nuU (f f' : Fin (r + 1) → V) : E := H.h (omP H f f') (omP H f f')

def alU (f f' : Fin (r + 1) → V) (T : F) (u : V) : E :=
  Ring.inverse (1 + algebraMap F E T * nuU H f f') * (H.h u (omP H f f') - nuU H f f' * H.h u (f (Fin.last r)))

theorem decompU (f f' : Fin (r + 1) → V) (T T' : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') (hD : IsUnit (H.Dl f f' (r + 1))) (hG : IsUnit (H.Gdet f f' T T'))
    (u : V) (hu : u ∈ Submodule.span E (Set.range (Sum.elim f f'))) (hX : u ∈ H.perp (H.X f)) :
    u - (alU H f f' T u • f (Fin.last r) + (H.h u (f (Fin.last r)) + algebraMap F E T * alU H f f' T u) •
      omP H f f') ∈ H.X f := by
  have hX' := (mem_perpX_iff H f u).1 hX
  apply mem_X_ofU H f f' T T' hF hF' hD hG
  · refine Submodule.sub_mem _ hu (Submodule.add_mem _ (Submodule.smul_mem _ _ ?_)
      (Submodule.smul_mem _ _ (omP_mem_span H f f')))
    exact Submodule.subset_span ⟨Sum.inl _, rfl⟩
  · intro a
    rw [h_sub_left H, H.h_add_left, H.h_smul_left, H.h_smul_left, h_frame H f T hF,
      h_omP_f H f f' hD]
    by_cases ha : a = Fin.last r
    · subst ha
      simp only [and_self, if_true]
      ring
    · obtain ⟨a', rfl⟩ := Fin.exists_castSucc_eq.2 ha
      simp [ha, hX' a']
  · have hη : (1 + algebraMap F E T * nuU H f f') * Ring.inverse (1 + algebraMap F E T * nuU H f f') = 1 :=
      Ring.mul_inverse_cancel _ (eta_unit H f f' T T' hF' hD hG)
    have e1 : H.h (u - (alU H f f' T u • f (Fin.last r) + (H.h u (f (Fin.last r)) +
        algebraMap F E T * alU H f f' T u) • omP H f f')) (omP H f f') = 0 := by
      rw [h_sub_left H, H.h_add_left, H.h_smul_left, H.h_smul_left, h_z_omP H f f' hD]
      rw [show H.h (omP H f f') (omP H f f') = nuU H f f' from rfl, alU]
      linear_combination (-(H.h u (omP H f f') - nuU H f f' * H.h u (f (Fin.last r)))) * hη
    have e2 : H.h (u - (alU H f f' T u • f (Fin.last r) + (H.h u (f (Fin.last r)) +
        algebraMap F E T * alU H f f' T u) • omP H f f')) (H.om' f f') = 0 := by
      rw [omP, h_smul_right] at e1
      have hu' : IsUnit (M.L.cj (Ring.inverse (H.Dl f f' (r + 1)))) :=
        (IsUnit.map M.L.cj (⟨⟨Ring.inverse (H.Dl f f' (r + 1)), H.Dl f f' (r + 1), Ring.inverse_mul_cancel _ hD,
          Ring.mul_inverse_cancel _ hD⟩, rfl⟩ :
          IsUnit (Ring.inverse (H.Dl f f' (r + 1)))))
      exact hu'.mul_right_eq_zero.1 e1
    rw [H.h_herm, e2, map_zero]

theorem mkW_decompU (f f' : Fin (r + 1) → V) (T T' : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') (hD : IsUnit (H.Dl f f' (r + 1))) (hG : IsUnit (H.Gdet f f' T T'))
    (u : ↥(H.perp (H.X f))) (hu : (u : V) ∈ Submodule.span E (Set.range (Sum.elim f f'))) :
    H.mkW f u = alU H f f' T u • H.mkW f ⟨f (Fin.last r), z_mem H f T hF⟩ +
      (H.h u (f (Fin.last r)) + algebraMap F E T * alU H f f' T u) •
        H.mkW f ⟨omP H f f', omP_mem H f f' hD⟩ := by
  have hd := decompU H f f' T T' hF hF' hD hG u hu u.2
  unfold HermSp.mkW
  rw [← map_smul, ← map_smul, ← map_add (f := _), Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub,
    Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul]
  exact hd

theorem mkW_decompU' (f f' : Fin (r + 1) → V) (T T' : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') (hD : IsUnit (H.Dl f f' (r + 1))) (hG : IsUnit (H.Gdet f f' T T'))
    (u : ↥(H.perp (H.X f'))) (hu : (u : V) ∈ Submodule.span E (Set.range (Sum.elim f f'))) :
    H.mkW f' u = alU H f' f T' u • H.mkW f' ⟨f' (Fin.last r), z_mem H f' T' hF'⟩ +
      (H.h u (f' (Fin.last r)) + algebraMap F E T' * alU H f' f T' u) •
        H.mkW f' ⟨omP H f' f, omP_mem H f' f (unit_swap H f f' hD)⟩ := by
  have hG' : IsUnit (H.Gdet f' f T' T) := by
    have he : H.Gdet f' f T' T = H.Gdet f f' T T' := by
      unfold HermSp.Gdet HermSp.normE
      rw [dl_swap_full H f f', dl_swap_r H f f', M.L.cj_cj, M.L.cj_cj, mul_comm T' T]
      ring
    rw [he]
    exact hG
  have hu' : (u : V) ∈ Submodule.span E (Set.range (Sum.elim f' f)) := by
    rw [Set.Sum.elim_range, Set.union_comm, ← Set.Sum.elim_range]
    exact hu
  exact mkW_decompU H f' f T' T hF' hF (unit_swap H f f' hD) hG' u hu'

def GoodU {r : ℕ} (t : Term V M r) : Prop :=
  M.split = none ∧ Formalism.MainNotions.ThinScalesBound.FrameK H t.f t.T ∧ Formalism.MainNotions.ThinScalesBound.FrameK H t.f' t.T' ∧
    IsUnit (H.Dl t.f t.f' (r + 1)) ∧ IsUnit (H.Gdet t.f t.f' t.T t.T')

private theorem MMfam_eq_sum_elim_of_goodU {t : Term V M r} (hg : GoodU H t) : H.MMfam t = Sum.elim t.f t.f' := by
  unfold HermSp.MMfam
  rw [hg.1]

theorem gramH_eqU {r : ℕ} {t : Term V M r} (hg : GoodU H t) :
    gramH H (H.MMfam t) = gramC (M.L.cj : E →+* E) (H.Zhat t.f t.f') (algebraMap F E t.T)
      (algebraMap F E t.T') := by
  rw [MMfam_eq_sum_elim_of_goodU H hg]
  obtain ⟨-, ⟨h0, hT⟩, ⟨h0', hT'⟩, -, -⟩ := hg
  ext i j
  rcases i with a | a <;> rcases j with b | b <;>
    simp only [gramC, gramH, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.transpose_apply, HermSp.Zhat]
  · split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      exact hT
    · exact h0 a b (not_and_or.mp h)
  · first
      | exact H.h_herm _ _
      | exact (H.h_herm _ _).symm
      | simp [H.h_herm]
  · split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      exact hT'
    · exact h0' a b (not_and_or.mp h)

theorem unit_gramHU {r : ℕ} {t : Term V M r} (hg : GoodU H t) :
    IsUnit (gramH H (H.MMfam t)).det := by
  rw [gramH_eqU H hg]
  exact unit_gramC_of H t.f t.f' t.T t.T' hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2

theorem relSub_eqU {r : ℕ} {t : Term V M r} (hg : GoodU H t) :
    relSub H t = relC M.L.O (M.L.cj : E →+* E) (H.Zhat t.f t.f') (algebraMap F E t.T)
      (algebraMap F E t.T') := by
  ext y
  simp only [relSub, relC, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq]
  rw [← gramH_eqU H hg]
  rfl

def PsiU {r : ℕ} {t : Term V M r} (hg : GoodU H t) :
    DDt H t ≃ₗ[M.L.O] DDc M.L.O (M.L.cj : E →+* E) (H.Zhat t.f t.f') (algebraMap F E t.T)
      (algebraMap F E t.T') :=
  (ddEquiv H t (unit_gramHU H hg)).trans (Submodule.quotEquivOfEq _ _ (relSub_eqU H hg))

theorem PsiU_mk {r : ℕ} {t : Term V M r} (hg : GoodU H t) (u : ↥(MMsharp H t)) :
    PsiU H hg (ddMk H t u) = Submodule.Quotient.mk (sharpEquiv H t (unit_gramHU H hg) u) := rfl

theorem h_eq_formCU {r : ℕ} {t : Term V M r} (hg : GoodU H t) (u w : ↥(MMsharp H t)) :
    H.h u w = formC M.L.O (M.L.cj : E →+* E) (H.Zhat t.f t.f') (algebraMap F E t.T)
      (algebraMap F E t.T') (sharpEquiv H t (unit_gramHU H hg) u)
      (sharpEquiv H t (unit_gramHU H hg) w) := by
  rw [h_eq_form H (H.MMfam t) (unit_gramHU H hg) (u : V) (w : V) ((mem_MMsharp_iff H t u).1 u.2).1,
    gramH_eqU H hg]
  simp only [formC, sharpEquiv_apply]
  rfl

def PcU {t : Term V M r} (hg : GoodU H t) : H.Wb t.f →ₗ[E] E × E :=
  coordW H t.f (t.f (Fin.last r)) (omP H t.f t.f') (z_mem H t.f t.T hg.2.1)
    (omP_mem H t.f t.f' hg.2.2.2.1)

def PcU' {t : Term V M r} (hg : GoodU H t) : H.Wb t.f' →ₗ[E] E × E :=
  coordW H t.f' (omP H t.f' t.f) (t.f' (Fin.last r))
    (omP_mem H t.f' t.f (unit_swap H t.f t.f' hg.2.2.2.1)) (z_mem H t.f' t.T' hg.2.2.1)

theorem sharp_inlU {t : Term V M r} (hg : GoodU H t) (u : ↥(MMsharp H t)) (a : Fin (r + 1)) :
    (sharpEquiv H t (unit_gramHU H hg) u (Sum.inl a) : E) = H.h u (t.f a) := by
  rw [sharpEquiv_apply, MMfam_eq_sum_elim_of_goodU H hg, Sum.elim_inl]

theorem sharp_inrU {t : Term V M r} (hg : GoodU H t) (u : ↥(MMsharp H t)) (b : Fin (r + 1)) :
    (sharpEquiv H t (unit_gramHU H hg) u (Sum.inr b) : E) = H.h u (t.f' b) := by
  rw [sharpEquiv_apply, MMfam_eq_sum_elim_of_goodU H hg, Sum.elim_inr]

theorem mem_span_of_sharpU {t : Term V M r} (hg : GoodU H t) (u : ↥(MMsharp H t)) :
    (u : V) ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) := by
  have hs := ((mem_MMsharp_iff H t u).1 u.2).1
  rwa [MMfam_eq_sum_elim_of_goodU H hg] at hs

theorem gam_imageU {t : Term V M r} (hg : GoodU H t) :
    (fun p => (PsiU H hg p.1, PcU H hg p.2)) '' Gam H t =
      GamC M.L.O (M.L.cj : E →+* E) (H.Zhat t.f t.f') (algebraMap F E t.T) (algebraMap F E t.T') := by
  ext ⟨d, c⟩
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, he⟩
    refine ⟨sharpEquiv H t (unit_gramHU H hg) u, fun a => ?_, ?_⟩
    · apply Subtype.ext
      rw [sharp_inlU H hg]
      exact (mem_perpX_iff H t.f u).1 hu a
    · rw [← he]
      beta_reduce
      rw [PsiU_mk]
      refine Prod.ext rfl (Prod.ext ?_ ?_)
      · show H.h u (t.f (Fin.last r)) = _
        rw [sharp_inlU H hg]
      · show H.h u (omP H t.f t.f') = _
        rw [h_omP, lamStarC]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [sharp_inrU H hg]
        rfl
  · rintro ⟨Y, hY, he⟩
    set u := (sharpEquiv H t (unit_gramHU H hg)).symm Y with hu
    have hYu : sharpEquiv H t (unit_gramHU H hg) u = Y := by rw [hu, LinearEquiv.apply_symm_apply]
    have hX : (u : V) ∈ H.perp (H.X t.f) := by
      rw [mem_perpX_iff]
      intro a
      rw [← sharp_inlU H hg, hYu, hY a]
      rfl
    refine ⟨(ddMk H t u, H.mkW t.f ⟨u, hX⟩), ⟨u, hX, rfl⟩, ?_⟩
    rw [he]
    beta_reduce
    rw [PsiU_mk, hYu]
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · show H.h u (t.f (Fin.last r)) = _
      rw [← sharp_inlU H hg, hYu]
    · show H.h u (omP H t.f t.f') = _
      rw [h_omP, lamStarC]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← sharp_inrU H hg u, hYu]
      rfl

theorem gam_imageU' {t : Term V M r} (hg : GoodU H t) :
    (fun p => (PsiU H hg p.1, PcU' H hg p.2)) '' Gam' H t =
      GamC' M.L.O (M.L.cj : E →+* E) (H.Zhat t.f t.f') (algebraMap F E t.T) (algebraMap F E t.T') := by
  ext ⟨d, c⟩
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, he⟩
    refine ⟨sharpEquiv H t (unit_gramHU H hg) u, fun a => ?_, ?_⟩
    · apply Subtype.ext
      rw [sharp_inrU H hg]
      exact (mem_perpX_iff H t.f' u).1 hu a
    · rw [← he]
      beta_reduce
      rw [PsiU_mk]
      refine Prod.ext rfl (Prod.ext ?_ ?_)
      · show H.h u (omP H t.f' t.f) = _
        rw [h_omP_swap H t.f t.f' hg.2.2.2.1, lamC, Matrix.mulVec, dotProduct]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [sharp_inlU H hg]
      · show H.h u (t.f' (Fin.last r)) = _
        rw [sharp_inrU H hg]
  · rintro ⟨Y, hY, he⟩
    set u := (sharpEquiv H t (unit_gramHU H hg)).symm Y with hu
    have hYu : sharpEquiv H t (unit_gramHU H hg) u = Y := by rw [hu, LinearEquiv.apply_symm_apply]
    have hX : (u : V) ∈ H.perp (H.X t.f') := by
      rw [mem_perpX_iff]
      intro a
      rw [← sharp_inrU H hg, hYu, hY a]
      rfl
    refine ⟨(ddMk H t u, H.mkW t.f' ⟨u, hX⟩), ⟨u, hX, rfl⟩, ?_⟩
    rw [he]
    beta_reduce
    rw [PsiU_mk, hYu]
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · show H.h u (omP H t.f' t.f) = _
      rw [h_omP_swap H t.f t.f' hg.2.2.2.1, lamC, Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← sharp_inlU H hg u, hYu]
    · show H.h u (t.f' (Fin.last r)) = _
      rw [← sharp_inrU H hg, hYu]

theorem gam_sepU {t₁ t₂ : Term V M r} (hg₁ : GoodU H t₁) (hg₂ : GoodU H t₂) (hT : t₂.T = t₁.T)
    (hν : nuU H t₂.f t₂.f' = nuU H t₁.f t₁.f')
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f)
    (hz : φ (H.mkW t₁.f ⟨_, z_mem H t₁.f t₁.T hg₁.2.1⟩) = H.mkW t₂.f ⟨_, z_mem H t₂.f t₂.T hg₂.2.1⟩)
    (ho : φ (H.mkW t₁.f ⟨_, omP_mem H t₁.f t₁.f' hg₁.2.2.2.1⟩) =
      H.mkW t₂.f ⟨_, omP_mem H t₂.f t₂.f' hg₂.2.2.2.1⟩) :
    ∀ p ∈ Gam H t₁, ∀ q ∈ Gam H t₂, PcU H hg₂ q.2 = PcU H hg₁ p.2 → q.2 = φ p.2 := by
  intro p hp q hq hc
  obtain ⟨u, hu, rfl⟩ := hp
  obtain ⟨w, hw, rfl⟩ := hq
  have e1 : H.h (w : V) (t₂.f (Fin.last r)) = H.h (u : V) (t₁.f (Fin.last r)) := congrArg Prod.fst hc
  have e2 : H.h (w : V) (omP H t₂.f t₂.f') = H.h (u : V) (omP H t₁.f t₁.f') := congrArg Prod.snd hc
  have hα : alU H t₂.f t₂.f' t₂.T (w : V) = alU H t₁.f t₁.f' t₁.T (u : V) := by
    unfold alU
    rw [hT, hν, e1, e2]
  have hβ : H.h (w : V) (t₂.f (Fin.last r)) + algebraMap F E t₂.T * alU H t₂.f t₂.f' t₂.T (w : V) =
      H.h (u : V) (t₁.f (Fin.last r)) + algebraMap F E t₁.T * alU H t₁.f t₁.f' t₁.T (u : V) := by
    rw [e1, hα, hT]
  show H.mkW t₂.f ⟨w, hw⟩ = φ (H.mkW t₁.f ⟨u, hu⟩)
  rw [mkW_decompU H t₂.f t₂.f' t₂.T t₂.T' hg₂.2.1 hg₂.2.2.1 hg₂.2.2.2.1 hg₂.2.2.2.2 ⟨w, hw⟩
      (mem_span_of_sharpU H hg₂ w),
    mkW_decompU H t₁.f t₁.f' t₁.T t₁.T' hg₁.2.1 hg₁.2.2.1 hg₁.2.2.2.1 hg₁.2.2.2.2 ⟨u, hu⟩
      (mem_span_of_sharpU H hg₁ u),
    map_add, map_smul, map_smul, hz, ho, hβ, hα]

theorem gam_sepU' {t₁ t₂ : Term V M r} (hg₁ : GoodU H t₁) (hg₂ : GoodU H t₂) (hT : t₂.T' = t₁.T')
    (hν : nuU H t₂.f' t₂.f = nuU H t₁.f' t₁.f)
    (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f')
    (hz : φ' (H.mkW t₁.f' ⟨_, z_mem H t₁.f' t₁.T' hg₁.2.2.1⟩) =
      H.mkW t₂.f' ⟨_, z_mem H t₂.f' t₂.T' hg₂.2.2.1⟩)
    (ho : φ' (H.mkW t₁.f' ⟨_, omP_mem H t₁.f' t₁.f (unit_swap H t₁.f t₁.f' hg₁.2.2.2.1)⟩) =
      H.mkW t₂.f' ⟨_, omP_mem H t₂.f' t₂.f (unit_swap H t₂.f t₂.f' hg₂.2.2.2.1)⟩) :
    ∀ p ∈ Gam' H t₁, ∀ q ∈ Gam' H t₂, PcU' H hg₂ q.2 = PcU' H hg₁ p.2 → q.2 = φ' p.2 := by
  intro p hp q hq hc
  obtain ⟨u, hu, rfl⟩ := hp
  obtain ⟨w, hw, rfl⟩ := hq
  have e1 : H.h (w : V) (omP H t₂.f' t₂.f) = H.h (u : V) (omP H t₁.f' t₁.f) := congrArg Prod.fst hc
  have e2 : H.h (w : V) (t₂.f' (Fin.last r)) = H.h (u : V) (t₁.f' (Fin.last r)) := congrArg Prod.snd hc
  have hα : alU H t₂.f' t₂.f t₂.T' (w : V) = alU H t₁.f' t₁.f t₁.T' (u : V) := by
    unfold alU
    rw [hT, hν, e1, e2]
  have hβ : H.h (w : V) (t₂.f' (Fin.last r)) + algebraMap F E t₂.T' * alU H t₂.f' t₂.f t₂.T' (w : V) =
      H.h (u : V) (t₁.f' (Fin.last r)) + algebraMap F E t₁.T' * alU H t₁.f' t₁.f t₁.T' (u : V) := by
    rw [e2, hα, hT]
  show H.mkW t₂.f' ⟨w, hw⟩ = φ' (H.mkW t₁.f' ⟨u, hu⟩)
  rw [mkW_decompU' H t₂.f t₂.f' t₂.T t₂.T' hg₂.2.1 hg₂.2.2.1 hg₂.2.2.2.1 hg₂.2.2.2.2 ⟨w, hw⟩
      (mem_span_of_sharpU H hg₂ w),
    mkW_decompU' H t₁.f t₁.f' t₁.T t₁.T' hg₁.2.1 hg₁.2.2.1 hg₁.2.2.2.1 hg₁.2.2.2.2 ⟨u, hu⟩
      (mem_span_of_sharpU H hg₁ u),
    map_add, map_smul, map_smul, hz, ho, hβ, hα]

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU
end
end

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU

section Parts

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {r : ℕ}

theorem mmInt_U {t : Term V M r} (hg : GoodU H t) (hT : t.T ∈ 𝒪[F]) (hT' : t.T' ∈ 𝒪[F])
    (hint : ∀ a b, H.Zhat t.f t.f' a b ∈ M.L.O) : MMInt H t := by
  have hTO : algebraMap F E t.T ∈ M.L.O := Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L ⟨t.T, hT⟩
  have hTO' : algebraMap F E t.T' ∈ M.L.O := Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L ⟨t.T', hT'⟩
  have hgen : ∀ i j, H.h (H.MMfam t i) (H.MMfam t j) ∈ M.L.O := by
    intro i j
    have e := congrFun (congrFun (gramH_eqU H hg) i) j
    simp only [gramH, Matrix.of_apply] at e
    rw [e]
    rcases i with a | a <;> rcases j with b | b
    · simp only [gramC, Matrix.fromBlocks_apply₁₁, Matrix.of_apply]
      split_ifs
      · exact neg_mem hTO
      · exact zero_mem _
    · simp only [gramC, Matrix.fromBlocks_apply₁₂, Matrix.of_apply]
      exact cj_mem_O M.L (hint a b)
    · simp only [gramC, Matrix.fromBlocks_apply₂₁, Matrix.transpose_apply]
      exact hint b a
    · simp only [gramC, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
      split_ifs
      · exact neg_mem hTO'
      · exact zero_mem _
  have hzero : ∀ y : V, H.h 0 y = 0 := by
    intro y
    have h0 := H.h_smul_left 0 0 y
    rwa [zero_smul, zero_mul] at h0
  have h1 : ∀ i, ∀ m ∈ MMo H t, H.h m (H.MMfam t i) ∈ M.L.O := by
    intro i m hm
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact hgen j i
    | zero => rw [hzero]; exact zero_mem _
    | add x y _ _ hx hy => rw [H.h_add_left]; exact add_mem hx hy
    | smul c x _ hx => rw [Subring.smul_def, H.h_smul_left]; exact mul_mem c.2 hx
  intro m hm m' hm'
  have h2 : ∀ i, H.h (H.MMfam t i) m' ∈ M.L.O := by
    intro i
    rw [H.h_herm]
    exact cj_mem_O M.L (h1 i m' hm')
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact h2 j
  | zero => rw [hzero]; exact zero_mem _
  | add x y _ _ hx hy => rw [H.h_add_left]; exact add_mem hx hy
  | smul c x _ hx => rw [Subring.smul_def, H.h_smul_left]; exact mul_mem c.2 hx

theorem PsiU_symm_mk {t : Term V M r} (hg : GoodU H t) (Y : Ix r → M.L.O) :
    (PsiU H hg).symm (Submodule.Quotient.mk Y) =
      ddMk H t ((sharpEquiv H t (unit_gramHU H hg)).symm Y) := by
  rw [LinearEquiv.symm_apply_eq, PsiU_mk, LinearEquiv.apply_symm_apply]

theorem isomD_iffU {t₁ t₂ : Term V M r} (hg₁ : GoodU H t₁) (hg₂ : GoodU H t₂)
    (θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂) :
    IsomD H t₁ t₂ θ ↔ ∀ Y W Y₂ W₂ : Ix r → M.L.O,
      PsiU H hg₂ (θ ((PsiU H hg₁).symm (Submodule.Quotient.mk Y))) = Submodule.Quotient.mk Y₂ →
      PsiU H hg₂ (θ ((PsiU H hg₁).symm (Submodule.Quotient.mk W))) = Submodule.Quotient.mk W₂ →
      formC M.L.O (M.L.cj : E →+* E) (H.Zhat t₂.f t₂.f') (algebraMap F E t₂.T) (algebraMap F E t₂.T')
          Y₂ W₂ -
        formC M.L.O (M.L.cj : E →+* E) (H.Zhat t₁.f t₁.f') (algebraMap F E t₁.T)
          (algebraMap F E t₁.T') Y W ∈ M.L.O := by
  unfold IsomD
  constructor
  · intro h Y W Y₂ W₂ hY hW
    rw [PsiU_symm_mk H hg₁, ← LinearEquiv.eq_symm_apply, PsiU_symm_mk H hg₂] at hY hW
    have key := h _ _ _ _ hY hW
    rw [h_eq_formCU H hg₂, h_eq_formCU H hg₁] at key
    simpa only [LinearEquiv.apply_symm_apply] using key
  · intro h x y x₂ y₂ hx hy
    have hx' : PsiU H hg₂ (θ ((PsiU H hg₁).symm
        (Submodule.Quotient.mk (sharpEquiv H t₁ (unit_gramHU H hg₁) x)))) =
        Submodule.Quotient.mk (sharpEquiv H t₂ (unit_gramHU H hg₂) x₂) := by
      rw [PsiU_symm_mk H hg₁, LinearEquiv.symm_apply_apply, hx, PsiU_mk]
    have hy' : PsiU H hg₂ (θ ((PsiU H hg₁).symm
        (Submodule.Quotient.mk (sharpEquiv H t₁ (unit_gramHU H hg₁) y)))) =
        Submodule.Quotient.mk (sharpEquiv H t₂ (unit_gramHU H hg₂) y₂) := by
      rw [PsiU_symm_mk H hg₁, LinearEquiv.symm_apply_apply, hy, PsiU_mk]
    rw [h_eq_formCU H hg₂, h_eq_formCU H hg₁]
    exact h _ _ _ _ hx' hy'

theorem kap_eq (f₁ f₁' f₂ f₂' : Fin (r + 1) → V) (hD₁ : IsUnit (H.Dl f₁ f₁' (r + 1)))
    (hD₂ : IsUnit (H.Dl f₂ f₂' (r + 1)))
    (hrel : H.Dl f₁ f₁' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl f₁ f₁' (r + 1)) :
    kapU H f₂ f₂' = kapU H f₁ f₁' := by
  obtain ⟨u₁, hu₁⟩ := hD₁
  obtain ⟨u₂, hu₂⟩ := hD₂
  simp only [kapU]
  rw [← hu₁, ← hu₂] at hrel ⊢
  rw [Ring.inverse_unit, Ring.inverse_unit, Units.inv_mul_eq_iff_eq_mul, mul_left_comm,
    Units.eq_inv_mul_iff_mul_eq]
  linear_combination -hrel

private theorem Dl_swap_eq_cj_Dl (f f' : Fin (r + 1) → V) (l : ℕ) :
    H.Dl f' f l = M.L.cj (H.Dl f f' l) := by
  unfold HermSp.Dl
  split_ifs with hl
  · rw [AlgEquiv.map_det, ← Matrix.det_transpose]
    congr 1
    ext a b
    simp only [HermSp.Zhat, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.of_apply,
      AlgEquiv.mapMatrix_apply, Matrix.map_apply]
    exact H.h_herm _ _
  · simp

theorem rel_swap (f₁ f₁' f₂ f₂' : Fin (r + 1) → V)
    (hrel : H.Dl f₁ f₁' r * H.Dl f₂ f₂' (r + 1) = H.Dl f₂ f₂' r * H.Dl f₁ f₁' (r + 1)) :
    H.Dl f₁' f₁ r * H.Dl f₂' f₂ (r + 1) = H.Dl f₂' f₂ r * H.Dl f₁' f₁ (r + 1) := by
  rw [Dl_swap_eq_cj_Dl H f₁, Dl_swap_eq_cj_Dl H f₂, Dl_swap_eq_cj_Dl H f₂, Dl_swap_eq_cj_Dl H f₁, ← map_mul, ← map_mul,
    hrel]

end Parts

private theorem image_prod_map_eq_iff_image_transport_eq {A₁ A₂ B₁ B₂ C₁ C₂ D : Type*} (G₁ : Set (A₁ × B₁)) (G₂ : Set (A₂ × B₂))
    (Ψ₁ : A₁ → C₁) (Ψ₁' : C₁ → A₁) (hΨ₁ : ∀ a, Ψ₁' (Ψ₁ a) = a) (Ψ₂ : A₂ → C₂)
    (hΨ₂ : Function.Injective Ψ₂) (P₁ : B₁ → D) (P₂ : B₂ → D) (θ : A₁ → A₂) (φ : B₁ → B₂)
    (hP : ∀ b, P₂ (φ b) = P₁ b)
    (sep : ∀ p ∈ G₁, ∀ q ∈ G₂, P₂ q.2 = P₁ p.2 → q.2 = φ p.2) :
    (fun p : A₁ × B₁ => (θ p.1, φ p.2)) '' G₁ = G₂ ↔
      (fun p : C₁ × D => (Ψ₂ (θ (Ψ₁' p.1)), p.2)) '' ((fun p : A₁ × B₁ => (Ψ₁ p.1, P₁ p.2)) '' G₁) =
        (fun p : A₂ × B₂ => (Ψ₂ p.1, P₂ p.2)) '' G₂ := by
  rw [Set.image_image]
  simp only [hΨ₁]
  constructor
  · intro h
    rw [← h, Set.image_image]
    simp only [hP]
  · intro h
    ext ⟨x, y⟩
    constructor
    · rintro ⟨p, hp, hpq⟩
      have hm : (Ψ₂ (θ p.1), P₁ p.2) ∈ (fun p : A₂ × B₂ => (Ψ₂ p.1, P₂ p.2)) '' G₂ := by
        rw [← h]
        exact ⟨p, hp, rfl⟩
      obtain ⟨q, hq, hqe⟩ := hm
      simp only [Prod.mk.injEq] at hqe hpq
      have h1 := hΨ₂ hqe.1
      have h2 := sep p hp q hq hqe.2
      rw [← hpq.1, ← hpq.2, ← h1, ← h2]
      exact hq
    · intro hq
      have hm : (Ψ₂ x, P₂ y) ∈ (fun p : A₁ × B₁ => (Ψ₂ (θ p.1), P₁ p.2)) '' G₁ := by
        rw [h]
        exact ⟨(x, y), hq, rfl⟩
      obtain ⟨p, hp, hpe⟩ := hm
      simp only [Prod.mk.injEq] at hpe
      have h1 := hΨ₂ hpe.1
      have h2 := sep p hp (x, y) hq hpe.2.symm
      refine ⟨p, hp, ?_⟩
      simp only [Prod.mk.injEq]
      exact ⟨h1, h2.symm⟩

theorem coordU_holds : CoordU := by
  intro F _ _ _ E _ _ _ _ M hsplit r n V _ _ H _ t₁ f₂ f₂' φ φ' hyp hDr hD₂ hZ
  obtain ⟨⟨⟨_, hF₁, hF₁', hD₁, hG₁, _⟩, _⟩, hK₂, hK₂', hId, hS, hS'⟩ := hyp
  obtain ⟨hiso, hiso', _, hom', hom, hrel⟩ := hId
  set t₂ : Term V M r := { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } with ht₂
  have hK₁ : MainNotions.ThinScalesBound.FrameK H t₁.f t₁.T := ⟨hF₁.2.1, hF₁.2.2.1⟩
  have hK₁' : MainNotions.ThinScalesBound.FrameK H t₁.f' t₁.T' := ⟨hF₁'.2.1, hF₁'.2.2.1⟩
  have hT : t₁.T ∈ 𝒪[F] := hF₁.2.2.2.1
  have hT' : t₁.T' ∈ 𝒪[F] := hF₁'.2.2.2.1
  have hG₁u := Formalism.L2.SG.LsDatumA.isUnit_Gdet H _ _ _ _ hG₁
  have hN₁ : IsUnit (H.normE (H.Dl t₁.f t₁.f' (r + 1))) := hD₁.mul (hD₁.map M.L.cj)
  have hN₂ : IsUnit (H.normE (H.Dl f₂ f₂' (r + 1))) := hD₂.mul (hD₂.map M.L.cj)
  have e := gdet_rel H t₁.f t₁.f' f₂ f₂' t₁.T t₁.T' hrel
  have hG₂ : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T') := by
    have hm : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T' * H.normE (H.Dl t₁.f t₁.f' (r + 1))) := by
      rw [e]
      exact hN₂.mul hG₁u
    exact isUnit_of_mul_isUnit_left hm
  have hg₁ : GoodU H t₁ := ⟨hsplit, hK₁, hK₁', hD₁, hG₁u⟩
  have hg₂ : GoodU H t₂ := ⟨hsplit, hK₂, hK₂', hD₂, hG₂⟩
  have hint₂ : MMInt H t₂ := mmInt_U H hg₂ hT hT' hZ
  have hD₁s : IsUnit (H.Dl t₁.f' t₁.f (r + 1)) := by
    rw [Dl_swap_eq_cj_Dl]
    exact hD₁.map _
  have hD₂s : IsUnit (H.Dl f₂' f₂ (r + 1)) := by
    rw [Dl_swap_eq_cj_Dl]
    exact hD₂.map _
  have hnu : nuU H t₂.f t₂.f' = nuU H t₁.f t₁.f' := by
    show nuU H f₂ f₂' = nuU H t₁.f t₁.f'
    unfold nuU
    rw [h_omP_omPU H f₂ f₂' t₁.T' hK₂', h_omP_omPU H t₁.f t₁.f' t₁.T' hK₁',
      kap_eq H t₁.f t₁.f' f₂ f₂' hD₁ hD₂ hrel]
  have hnu' : nuU H t₂.f' t₂.f = nuU H t₁.f' t₁.f := by
    show nuU H f₂' f₂ = nuU H t₁.f' t₁.f
    unfold nuU
    rw [h_omP_omPU H f₂' f₂ t₁.T hK₂, h_omP_omPU H t₁.f' t₁.f t₁.T hK₁,
      kap_eq H t₁.f' t₁.f f₂' f₂ hD₁s hD₂s (rel_swap H _ _ _ _ hrel)]
  have sends1 : ∀ {g₁ g₂ : Fin (r + 1) → V} (ψ : H.Wb g₁ →ₗ[E] H.Wb g₂) (v₁ v₂ : V)
      (h₁ : v₁ ∈ H.perp (H.X g₁)) (h₂ : v₂ ∈ H.perp (H.X g₂)), H.SendsTo ψ 1 1 v₁ v₂ →
      ψ (H.mkW g₁ ⟨v₁, h₁⟩) = H.mkW g₂ ⟨v₂, h₂⟩ := by
    intro g₁ g₂ ψ v₁ v₂ h₁ h₂ hs
    simpa only [one_smul] using hs ⟨v₁, h₁⟩ ⟨v₂, h₂⟩ rfl rfl
  have hc : ∀ w, PcU H hg₂ (φ w) = PcU H hg₁ w := by
    intro w
    unfold PcU
    refine coordW_comp H φ hiso _ _ _ _ _ _ _ _ ?_ ?_ w
    · exact sends1 _ _ _ _ _ hS
    · exact sends_omP H φ hD₁ hD₂ hom'
  have hc' : ∀ w, PcU' H hg₂ (φ' w) = PcU' H hg₁ w := by
    intro w
    unfold PcU'
    refine coordW_comp H φ' hiso' _ _ _ _ _ _ _ _ ?_ ?_ w
    · exact sends_omP' H φ' hD₁ hD₂ hom
    · exact sends1 _ _ _ _ _ hS'
  have sep := gam_sepU H hg₁ hg₂ rfl hnu φ (sends1 _ _ _ _ _ hS) (sends_omP H φ hD₁ hD₂ hom')
  have sep' := gam_sepU' H hg₁ hg₂ rfl hnu' φ' (sends1 _ _ _ _ _ hS') (sends_omP' H φ' hD₁ hD₂ hom)
  let eqv : (DDt H t₁ ≃ₗ[M.L.O] DDt H t₂) ≃
      (DDc M.L.O (M.L.cj : E →+* E) (H.Zhat t₁.f t₁.f') (algebraMap F E t₁.T) (algebraMap F E t₁.T') ≃ₗ[M.L.O]
        DDc M.L.O (M.L.cj : E →+* E) (H.Zhat f₂ f₂') (algebraMap F E t₁.T) (algebraMap F E t₁.T')) :=
    { toFun := fun θ => ((PsiU H hg₁).symm.trans θ).trans (PsiU H hg₂)
      invFun := fun ψ => ((PsiU H hg₁).trans ψ).trans (PsiU H hg₂).symm
      left_inv := fun θ => by
        ext x
        simp
      right_inv := fun ψ => by
        ext x
        simp }
  refine Nat.card_congr (Equiv.subtypeEquiv eqv ?_)
  intro θ
  simp only [Theta, ThetaC, Set.mem_setOf_eq]
  rw [isomD_iffU H hg₁ hg₂ θ]
  have key := image_prod_map_eq_iff_image_transport_eq (Gam H t₁) (Gam H t₂) (PsiU H hg₁) (PsiU H hg₁).symm
    (PsiU H hg₁).symm_apply_apply (PsiU H hg₂) (PsiU H hg₂).injective (PcU H hg₁) (PcU H hg₂) θ φ
    hc sep
  have key' := image_prod_map_eq_iff_image_transport_eq (Gam' H t₁) (Gam' H t₂) (PsiU H hg₁) (PsiU H hg₁).symm
    (PsiU H hg₁).symm_apply_apply (PsiU H hg₂) (PsiU H hg₂).injective (PcU' H hg₁) (PcU' H hg₂) θ φ'
    hc' sep'
  constructor
  · rintro ⟨_, _, hI, hGm, _⟩
    obtain ⟨hA, hB⟩ := hGm hsplit
    refine ⟨hI, ?_, ?_⟩
    · rw [← gam_imageU H hg₁]
      refine Eq.trans ?_ (gam_imageU H hg₂)
      exact key.1 hA
    · rw [← gam_imageU' H hg₁]
      refine Eq.trans ?_ (gam_imageU' H hg₂)
      exact key'.1 hB
  · rintro ⟨hI, hA, hB⟩
    refine ⟨hD₂, hint₂, hI, fun _ => ⟨?_, ?_⟩, fun g hg => ?_⟩
    · refine key.2 ?_
      rw [gam_imageU H hg₁]
      exact hA.trans (gam_imageU H hg₂).symm
    · refine key'.2 ?_
      rw [gam_imageU' H hg₁]
      exact hB.trans (gam_imageU' H hg₂).symm
    · rw [hsplit] at hg
      cases hg

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU
end
end

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU

theorem thetaMbeU_false_of_alg (h2 : AlgAll) {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Formalism.MainNotions.S.Loc.Model F E) (r n : ℕ) : Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUL.ThetaMbeU M r n false :=
  thetaMbeU_false_of coordU_holds h2 M r n

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU
