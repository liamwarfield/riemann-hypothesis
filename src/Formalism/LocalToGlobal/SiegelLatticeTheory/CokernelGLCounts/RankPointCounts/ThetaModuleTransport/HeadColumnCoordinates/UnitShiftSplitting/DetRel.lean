module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.ExistsUnitShift

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.HSmulSubRight
noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem h_smul_sub_left (H : HermSp M V) (c : E) (x y z : V) :
    H.h (c • (x - y)) z = c * (H.h x z - H.h y z) := by
  have : c • (x - y) = c • x + (-c) • y := by rw [smul_sub, sub_eq_add_neg, neg_smul]
  rw [this, H.h_add_left, H.h_smul_left, H.h_smul_left]
  ring

theorem h_smul_sub_right (H : HermSp M V) (c : E) (x y z : V) :
    H.h z (c • (x - y)) = M.L.cj c * (H.h z x - H.h z y) := by
  rw [H.h_herm, h_smul_sub_left, map_mul, map_sub, ← H.h_herm, ← H.h_herm]

theorem e_cj (g : SplitG M.L) (x : E) : g.e (M.L.cj x) = ((g.e x).2, (g.e x).1) := g.e_cj x

theorem zz_mem_R {g : SplitG M.L} (hs : M.split = some g) (H : HermSp M V) {r : ℕ} (t : Term V M r)
    (hF : Formalism.MainNotions.ThinScalesBound.FrameK H t.f t.T) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H t.f' t.T')
    (hT : ∃ c : 𝒪[F], t.T - t.T' = (g.q : F) ^ 2 * c) (hint : MMInt H t) (a b : Fin (r + 1)) :
    HermSp.ZZplusOf M (H.Zhat t.f t.f') t.T t.T' a b ∈ M.R := by
  have hq0 : (g.q : F) ≠ 0 := fun h => g.q_irr.ne_zero (Subtype.ext h)
  set q : F := (g.q : F) with hqdef
  set qi : E := algebraMap F E q⁻¹ with hqi
  have hMM : H.MMfam t = Sum.elim t.f (fun a => qi • (t.f' a - t.f a)) := by
    unfold HermSp.MMfam; rw [hs]
  have memf : ∀ a, t.f a ∈ MMo H t := fun a => Submodule.subset_span ⟨Sum.inl a, by rw [hMM]; rfl⟩
  have memg : ∀ a, qi • (t.f' a - t.f a) ∈ MMo H t :=
    fun a => Submodule.subset_span ⟨Sum.inr a, by rw [hMM]; rfl⟩
  have i1 := comp_mem_O g (hint _ (memg b) _ (memf a))
  have i2 := comp_mem_O g (hint _ (memg a) _ (memf b))
  have i3 := comp_mem_O g (hint _ (memg b) _ (memg a))
  rw [h_smul_sub_left] at i1 i2
  rw [h_smul_sub_left, h_smul_sub_right, h_smul_sub_right, H.h_herm (t.f' a) (t.f b)] at i3
  obtain ⟨c, hc⟩ := hT
  have eqi : g.e qi = (q⁻¹, q⁻¹) := e_alg g _
  have cqi : M.L.cj qi = qi := cj_alg _
  have eZ : ∀ a b, H.Zhat t.f t.f' a b = H.h (t.f' b) (t.f a) := fun _ _ => rfl
  unfold HermSp.ZZplusOf
  rw [hs]
  simp only [Matrix.of_apply, eZ]
  set z := g.e (H.h (t.f' b) (t.f a)) with hz
  set w := g.e (H.h (t.f' a) (t.f b)) with hw
  by_cases hab : a = Fin.last r ∧ b = Fin.last r
  · obtain ⟨rfl, rfl⟩ := hab
    rw [if_pos ⟨rfl, rfl⟩]
    rw [hF.2] at i1
    rw [hF.2, hF'.2] at i3
    simp only [map_mul, map_sub, map_add (f := _), map_neg, e_alg, e_cj, cj_alg, eqi, cqi, Prod.fst_mul, Prod.snd_mul,
      Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg] at i1 i3
    rw [← hz] at i1 i3
    apply mem_R_of hs
    · simp only [map_sub, AlgEquiv.apply_symm_apply, Prod.fst_sub, ← hz, ← hqdef]
      convert i1.1 using 1; field_simp; try ring
    · simp only [map_sub, AlgEquiv.apply_symm_apply, Prod.snd_sub, ← hz, ← hqdef]
      have : -(z.2 / q) - t.T' / q = -(q⁻¹ * (z.2 - -t.T)) + q * c := by
        field_simp; linear_combination hc
      rw [this]
      exact (𝒪[F]).add_mem ((𝒪[F]).neg_mem i1.2) ((𝒪[F]).mul_mem g.q.2 c.2)
    · refine ⟨-_, (𝒪[F]).neg_mem i3.1, ?_⟩
      simp only [map_sub, AlgEquiv.apply_symm_apply, Prod.fst_sub, Prod.snd_sub, ← hz, ← hqdef]
      field_simp
      try ring
  · rw [if_neg hab, sub_zero]
    have hab' : a ≠ Fin.last r ∨ b ≠ Fin.last r := not_and_or.1 hab
    have hba' : b ≠ Fin.last r ∨ a ≠ Fin.last r := hab'.symm
    rw [hF.1 b a hba'] at i1
    rw [hF.1 a b hab'] at i2
    rw [hF.1 b a hba', hF'.1 b a hba'] at i3
    simp only [map_mul, map_sub, map_add (f := _), map_neg, map_zero, e_alg, e_cj, cj_alg, eqi, cqi, Prod.fst_mul, Prod.snd_mul,
      Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, Prod.fst_zero,
      Prod.snd_zero] at i1 i2 i3
    rw [← hz] at i1 i3
    rw [← hw] at i2 i3
    apply mem_R_of hs
    · simp only [AlgEquiv.apply_symm_apply, ← hqdef]
      convert i1.1 using 1; field_simp; try ring
    · simp only [AlgEquiv.apply_symm_apply, ← hqdef]
      convert (𝒪[F]).neg_mem i2.2 using 1; field_simp; ring
    · refine ⟨-_, (𝒪[F]).neg_mem i3.1, ?_⟩
      simp only [AlgEquiv.apply_symm_apply, ← hqdef]
      field_simp
      ring

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG
end
end

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E}

theorem rel_smul_corner {R : Type} [CommRing R] {r : ℕ} (B₁ B₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) R)
    (s c : R) (hrel : (B₁.submatrix Fin.castSucc Fin.castSucc).det * B₂.det =
      (B₂.submatrix Fin.castSucc Fin.castSucc).det * B₁.det) :
    ((s • B₁ + cornerM r c).submatrix Fin.castSucc Fin.castSucc).det * (s • B₂ + cornerM r c).det =
      ((s • B₂ + cornerM r c).submatrix Fin.castSucc Fin.castSucc).det * (s • B₁ + cornerM r c).det := by
  have hsub : ∀ B : Matrix (Fin (r + 1)) (Fin (r + 1)) R,
      (s • B).submatrix Fin.castSucc Fin.castSucc = s • B.submatrix Fin.castSucc Fin.castSucc := fun B => by
    ext a b; simp
  rw [det_add_cornerM, det_add_cornerM, head_add_cornerM, head_add_cornerM, hsub, hsub, Matrix.det_smul, Matrix.det_smul, Matrix.det_smul, Matrix.det_smul]
  simp only [Fintype.card_fin]
  linear_combination (s ^ r * s ^ (r + 1)) * hrel

theorem rel_transpose {R : Type} [CommRing R] {r : ℕ} (B₁ B₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) R)
    (hrel : (B₁.submatrix Fin.castSucc Fin.castSucc).det * B₂.det =
      (B₂.submatrix Fin.castSucc Fin.castSucc).det * B₁.det) :
    (B₁.transpose.submatrix Fin.castSucc Fin.castSucc).det * B₂.transpose.det =
      (B₂.transpose.submatrix Fin.castSucc Fin.castSucc).det * B₁.transpose.det := by
  rw [← Matrix.transpose_submatrix, ← Matrix.transpose_submatrix]
  simp only [Matrix.det_transpose]
  exact hrel

theorem det_rel_split {g : SplitG M.L} (hs : M.split = some g) {r : ℕ}
    (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (hrel : (Zh₁.submatrix Fin.castSucc Fin.castSucc).det * Zh₂.det =
      (Zh₂.submatrix Fin.castSucc Fin.castSucc).det * Zh₁.det) :
    ((HermSp.ZZplusOf M Zh₁ T T').submatrix Fin.castSucc Fin.castSucc).det * (HermSp.ZZplusOf M Zh₂ T T').det =
      ((HermSp.ZZplusOf M Zh₂ T T').submatrix Fin.castSucc Fin.castSucc).det *
        (HermSp.ZZplusOf M Zh₁ T T').det := by
  let φ₁ : E →+* F := (RingHom.fst F F).comp g.e.toRingEquiv.toRingHom
  let φ₂ : E →+* F := (RingHom.snd F F).comp g.e.toRingEquiv.toRingHom
  have hφ₁ : ∀ x, φ₁ x = (g.e x).1 := fun _ => rfl
  have hφ₂ : ∀ x, φ₂ x = (g.e x).2 := fun _ => rfl
  have hdet : ∀ (φ : E →+* F) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E), φ A.det = (A.map φ).det := by
    intro φ A; rw [RingHom.map_det]; rfl
  have hhd : ∀ (φ : E →+* F) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E),
      φ (A.submatrix Fin.castSucc Fin.castSucc).det = ((A.map φ).submatrix Fin.castSucc Fin.castSucc).det := by
    intro φ A; rw [RingHom.map_det]; rfl
  have hrelφ : ∀ φ : E →+* F, ((Zh₁.map φ).submatrix Fin.castSucc Fin.castSucc).det * (Zh₂.map φ).det =
      ((Zh₂.map φ).submatrix Fin.castSucc Fin.castSucc).det * (Zh₁.map φ).det := by
    intro φ
    rw [← hdet, ← hdet, ← hhd, ← hhd, ← map_mul, ← map_mul, hrel]
  have m1 : ∀ Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E,
      (HermSp.ZZplusOf M Zh T T').map φ₁ = ((g.q : F)⁻¹) • Zh.map φ₁ + cornerM r (T / (g.q : F)) := by
    intro Zh
    ext a b
    unfold HermSp.ZZplusOf
    rw [hs]
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, cornerM, smul_eq_mul,
      hφ₁, map_sub, AlgEquiv.apply_symm_apply, Prod.fst_sub]
    split_ifs with h
    · simp only [map_sub, AlgEquiv.apply_symm_apply, Prod.fst_sub]; ring
    · simp only [map_zero, Prod.fst_zero]; ring
  have m2 : ∀ Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E,
      (HermSp.ZZplusOf M Zh T T').map φ₂ = (-(g.q : F)⁻¹) • (Zh.map φ₂).transpose +
        cornerM r (-(T' / (g.q : F))) := by
    intro Zh
    ext a b
    unfold HermSp.ZZplusOf
    rw [hs]
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, cornerM, smul_eq_mul,
      hφ₂, Matrix.transpose_apply, map_sub, AlgEquiv.apply_symm_apply, Prod.snd_sub]
    split_ifs with h
    · simp only [map_sub, AlgEquiv.apply_symm_apply, Prod.snd_sub]; ring
    · simp only [map_zero, Prod.snd_zero]; ring
  apply g.e.injective
  refine Prod.ext ?_ ?_
  · show φ₁ _ = φ₁ _
    rw [map_mul, map_mul, hdet, hdet, hhd, hhd, m1, m1]
    exact rel_smul_corner _ _ _ _ (hrelφ φ₁)
  · show φ₂ _ = φ₂ _
    rw [map_mul, map_mul, hdet, hdet, hhd, hhd, m2, m2]
    exact rel_smul_corner _ _ _ _ (rel_transpose _ _ (hrelφ φ₂))

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG
