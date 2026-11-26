module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMomentMatrixTransform

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMapSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtendByZeroZero
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Matrix

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.LeviIdx

open GlobalTheory.EmbChart

section Lift

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F))
  {ι : Type} [Fintype ι] [DecidableEq ι]

def ext0 (M : Matrix ι ι (Fv F v ⊗[F] E)) : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := M.map (tensAt E v)

theorem matrixExtendByZero_add (M N : Matrix ι ι (Fv F v ⊗[F] E)) : ext0 v (M + N) = ext0 v M + ext0 v N := by
  ext i j; simp [ext0]

theorem matrixExtendByZero_zero : ext0 v (0 : Matrix ι ι (Fv F v ⊗[F] E)) = 0 := by
  ext i j; simp [ext0]

theorem ext_zero_mul_right (M : Matrix ι ι (Fv F v ⊗[F] E)) (C : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    ext0 v M * C = ext0 v (M * C.map (compFin F E v)) := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ext0, Matrix.mul_apply, Matrix.map_apply, map_sum, tensAt_mul_right]

theorem ext_zero_mul_left (M : Matrix ι ι (Fv F v ⊗[F] E)) (C : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    C * ext0 v M = ext0 v (C.map (compFin F E v) * M) := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ext0, Matrix.mul_apply, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, tensAt_mul_right, mul_comm]

theorem matrixExtendByZero_mul (M N : Matrix ι ι (Fv F v ⊗[F] E)) : ext0 v M * ext0 v N = ext0 v (M * N) := by
  rw [ext_zero_mul_right]
  congr 2
  ext i j
  exact compFin_tensAt v _

theorem ext_zero_transpose (M : Matrix ι ι (Fv F v ⊗[F] E)) : (ext0 v M)ᵀ = ext0 v Mᵀ := rfl

theorem ext_zero_map_conj (σ : E →ₐ[F] E) (M : Matrix ι ι (Fv F v ⊗[F] E)) :
    (ext0 v M).map (cA σ) = ext0 v (M.map (sigR (Fv F v) σ)) := by
  ext i j
  exact sigR_tensAt v σ _

theorem ext_zero_comp_finite (M : Matrix ι ι (Fv F v ⊗[F] E)) : (ext0 v M).map (compFin F E v) = M := by
  ext i j
  exact compFin_tensAt v _

def lift (Y : Matrix ι ι (Fv F v ⊗[F] E)) : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := 1 + ext0 v (Y - 1)

theorem lift_mul (Y Z : Matrix ι ι (Fv F v ⊗[F] E)) : lift v Y * lift v Z = lift v (Y * Z) := by
  have e : Y * Z - 1 = (Y - 1) + (Z - 1) + (Y - 1) * (Z - 1) := by noncomm_ring
  rw [lift, lift, lift, e, matrixExtendByZero_add, matrixExtendByZero_add, ← matrixExtendByZero_mul]
  noncomm_ring

theorem lift_one : lift v (1 : Matrix ι ι (Fv F v ⊗[F] E)) = 1 := by
  rw [lift, sub_self, matrixExtendByZero_zero, add_zero]

theorem compFin_lift (Y : Matrix ι ι (Fv F v ⊗[F] E)) : (lift v Y).map (compFin F E v) = Y := by
  have h2 : (1 : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).map (compFin F E v) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h1 : (lift v Y).map (compFin F E v) = (1 : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).map (compFin F E v) +
      (ext0 v (Y - 1)).map (compFin F E v) := by
    ext i j; simp only [lift, Matrix.map_apply, Matrix.add_apply, map_add (f := _)]
  rw [h1, ext_zero_comp_finite, h2]
  abel

theorem lift_sub_one_at (Y : Matrix ι ι (Fv F v ⊗[F] E)) : At (evFin F v) (lift v Y - 1) := by
  intro u hu
  rw [lift, add_sub_cancel_left]
  ext i j
  simp only [ext0, Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply]
  rw [Algebra.smul_def, mul_comm, tensAt_mul_right]
  have : compFin F E v (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) u) = 0 := by
    change (evFin F v u) ⊗ₜ[F] (1 : E) = 0
    rw [hu, TensorProduct.zero_tmul]
  rw [this, mul_zero, map_zero]

theorem lift_unitary (σ : E →ₐ[F] E) (J : Matrix ι ι E) (Y : Matrix ι ι (Fv F v ⊗[F] E))
    (hY : Yᵀ * J.map (inclR (Fv F v)) * Y.map (sigR (Fv F v) σ) = J.map (inclR (Fv F v))) :
    (lift v Y)ᵀ * incM F J * (lift v Y).map (cA σ) = incM F J := by
  set C := incM F J
  have hC : C.map (compFin F E v) = J.map (inclR (Fv F v)) := by
    ext i j
    change compFin F E v ((1 : AF F) ⊗ₜ[F] J i j) = (1 : Fv F v) ⊗ₜ[F] J i j
    change evFin F v 1 ⊗ₜ[F] J i j = _
    rw [map_one]
  have hT : (lift v Y)ᵀ = 1 + ext0 v (Y - 1)ᵀ := by
    rw [lift, Matrix.transpose_add, Matrix.transpose_one, ext_zero_transpose]
  have hS : (lift v Y).map (cA σ) = 1 + ext0 v ((Y - 1).map (sigR (Fv F v) σ)) := by
    rw [← ext_zero_map_conj]
    ext i j
    simp [lift, Matrix.one_apply]
  rw [hT, hS]
  have e1 : (1 + ext0 v (Y - 1)ᵀ) * C * (1 + ext0 v ((Y - 1).map (sigR (Fv F v) σ))) =
      C + (ext0 v (Y - 1)ᵀ * C + C * ext0 v ((Y - 1).map (sigR (Fv F v) σ)) +
        ext0 v (Y - 1)ᵀ * C * ext0 v ((Y - 1).map (sigR (Fv F v) σ))) := by noncomm_ring
  rw [e1, ext_zero_mul_right, matrixExtendByZero_mul, ext_zero_mul_left, ← matrixExtendByZero_add, ← matrixExtendByZero_add, hC]
  have hYs : (Y - 1).map (sigR (Fv F v) σ) = Y.map (sigR (Fv F v) σ) - 1 := by
    rw [Matrix.map_sub _ (fun a b => map_sub _ a b), Matrix.map_one _ (map_zero _) (map_one _)]
  rw [hYs, Matrix.transpose_sub, Matrix.transpose_one]
  set Jl : Matrix ι ι (Fv F v ⊗[F] E) := J.map (inclR (Fv F v))
  have e2 : (Yᵀ - 1) * Jl + Jl * (Y.map (sigR (Fv F v) σ) - 1) + (Yᵀ - 1) * Jl * (Y.map (sigR (Fv F v) σ) - 1) =
      Yᵀ * Jl * Y.map (sigR (Fv F v) σ) - Jl := by noncomm_ring
  rw [e2, hY, sub_self, matrixExtendByZero_zero, add_zero]

end Lift

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem map_mul_alg (f : Fv F v ⊗[F] E →ₐ[Fv F v] Fv F v) (M N : Matrix ι ι (Fv F v ⊗[F] E)) :
    (M * N).map f = M.map f * N.map f :=
  Matrix.map_mul (f := f.toRingHom)

theorem mat_split_ext (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) {Y Z : Matrix ι ι (Fv F v ⊗[F] E)}
    (h1 : Y.map (splitProj t) = Z.map (splitProj t))
    (h2 : Y.map (splitProj (t.comp σ)) = Z.map (splitProj (t.comp σ))) : Y = Z := by
  ext i j
  exact split_ext h t (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)

def pairMat (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (A B : Matrix ι ι (Fv F v)) :
    Matrix ι ι (Fv F v ⊗[F] E) := fun i j => (splitAlgEquiv h t).symm (A i j, B i j)

theorem pairMat_fst (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (A B : Matrix ι ι (Fv F v)) :
    (pairMat h t A B).map (splitProj t) = A := by
  ext i j; simp [pairMat]

theorem pairMat_snd (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (A B : Matrix ι ι (Fv F v)) :
    (pairMat h t A B).map (splitProj (t.comp σ)) = B := by
  ext i j; simp [pairMat]

theorem pairMat_mul (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (A B A' B' : Matrix ι ι (Fv F v)) :
    pairMat h t A B * pairMat h t A' B' = pairMat h t (A * A') (B * B') :=
  mat_split_ext h t (by rw [map_mul_alg, pairMat_fst, pairMat_fst, pairMat_fst])
    (by rw [map_mul_alg, pairMat_snd, pairMat_snd, pairMat_snd])

theorem pairMat_one (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) :
    pairMat h t (1 : Matrix ι ι (Fv F v)) 1 = 1 :=
  mat_split_ext h t (by rw [pairMat_fst, Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [pairMat_snd, Matrix.map_one _ (map_zero _) (map_one _)])

def conjC (t : E →ₐ[F] Fv F v) (K : Matrix ι ι E) (g : GL ι (Fv F v)) : Matrix ι ι (Fv F v) :=
  (K.map t)⁻¹ * ((g⁻¹ : GL ι (Fv F v)) : Matrix ι ι (Fv F v))ᵀ * K.map t

theorem conjC_mul (t : E →ₐ[F] Fv F v) (K : Matrix ι ι E) (hK : IsUnit (K.map t).det)
    (g₁ g₂ : GL ι (Fv F v)) : conjC t K (g₁ * g₂) = conjC t K g₁ * conjC t K g₂ := by
  simp only [conjC, mul_inv_rev, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv_cancel_left _ _ hK]

theorem conjC_one (t : E →ₐ[F] Fv F v) (K : Matrix ι ι E) (hK : IsUnit (K.map t).det) :
    conjC t K 1 = 1 := by
  simp only [conjC, inv_one, Units.val_one, Matrix.transpose_one, Matrix.mul_one]
  exact Matrix.nonsing_inv_mul _ hK

def locM (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (K : Matrix ι ι E) (g : GL ι (Fv F v)) :
    Matrix ι ι (Fv F v ⊗[F] E) := pairMat h t g (conjC t K g)

theorem locM_mul (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (K : Matrix ι ι E)
    (hK : IsUnit (K.map t).det) (g₁ g₂ : GL ι (Fv F v)) :
    locM h t K (g₁ * g₂) = locM h t K g₁ * locM h t K g₂ := by
  rw [locM, locM, locM, pairMat_mul, conjC_mul t K hK, Units.val_mul]

theorem locM_one (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (K : Matrix ι ι E)
    (hK : IsUnit (K.map t).det) : locM h t K 1 = 1 := by
  rw [locM, conjC_one t K hK, Units.val_one, pairMat_one]

theorem locM_unitary (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (K : Matrix ι ι E)
    (hK : IsUnit (K.map t).det) (skew : ∀ i j, σ (K j i) = -K i j) (g : GL ι (Fv F v)) :
    (locM h t K g)ᵀ * K.map (inclR (Fv F v)) * (locM h t K g).map (sigR (Fv F v) σ) =
      K.map (inclR (Fv F v)) := by
  have hJl : ∀ τ : E →ₐ[F] Fv F v, (K.map (inclR (Fv F v))).map (splitProj τ) = K.map τ := fun τ =>
    Matrix.ext fun i j => by
      simp only [Matrix.map_apply]; exact splitProj_inclR τ (K i j)
  have hs1 : ((locM h t K g).map (sigR (Fv F v) σ)).map (splitProj t) = conjC t K g := by
    rw [Matrix.map_map]
    have : (splitProj t ∘ sigR (Fv F v) σ) = splitProj (t.comp σ) := funext fun y => (splitProj_comp t σ y).symm
    rw [this, locM, pairMat_snd]
  have hs2 : ((locM h t K g).map (sigR (Fv F v) σ)).map (splitProj (t.comp σ)) = g := by
    rw [Matrix.map_map]
    have : (splitProj (t.comp σ) ∘ sigR (Fv F v) σ) = splitProj t := funext fun y => splitProj_comp_sigR h t y
    rw [this, locM, pairMat_fst]
  have hKs : K.map (t.comp σ) = -(K.map t)ᵀ := by
    ext i j
    simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.neg_apply, AlgHom.comp_apply]
    rw [skew j i, map_neg]
  set A : Matrix ι ι (Fv F v) := ((g⁻¹ : GL ι (Fv F v)) : Matrix ι ι (Fv F v))
  have eA : A * (g : Matrix ι ι (Fv F v)) = 1 := Units.inv_mul g
  refine mat_split_ext h t ?_ ?_
  · rw [map_mul_alg, map_mul_alg, Matrix.transpose_map, hJl, hs1, locM, pairMat_fst, conjC]
    set Jt := K.map t
    calc (g : Matrix ι ι (Fv F v))ᵀ * Jt * (Jt⁻¹ * Aᵀ * Jt)
        = (g : Matrix ι ι (Fv F v))ᵀ * (Jt * Jt⁻¹) * Aᵀ * Jt := by simp only [Matrix.mul_assoc]
      _ = (A * (g : Matrix ι ι (Fv F v)))ᵀ * Jt := by
          rw [Matrix.mul_nonsing_inv _ hK, Matrix.mul_one, Matrix.transpose_mul]
      _ = Jt := by rw [eA, Matrix.transpose_one, Matrix.one_mul]
  · rw [map_mul_alg, map_mul_alg, Matrix.transpose_map, hJl, hs2, locM, pairMat_snd, conjC, hKs]
    set Jt := K.map t
    have e : (Jt⁻¹)ᵀ * Jtᵀ = 1 := by
      rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hK, Matrix.transpose_one]
    calc (Jt⁻¹ * Aᵀ * Jt)ᵀ * -Jtᵀ * (g : Matrix ι ι (Fv F v))
        = -(Jtᵀ * A * ((Jt⁻¹)ᵀ * Jtᵀ) * (g : Matrix ι ι (Fv F v))) := by
          simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_neg, Matrix.neg_mul,
            Matrix.mul_assoc]
      _ = -Jtᵀ := by rw [e, Matrix.mul_one, Matrix.mul_assoc, eA, Matrix.mul_one]

end Local

section Hom

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {v : HeightOneSpectrum (𝓞 F)} {ι : Type} [Fintype ι] [DecidableEq ι]

def adelicGL (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (K : Matrix ι ι E)
    (hK : IsUnit (K.map t).det) (g : GL ι (Fv F v)) : GL ι (AE F E) :=
  ⟨lift v (locM h t K g), lift v (locM h t K g⁻¹),
    by rw [lift_mul, ← locM_mul h t K hK, mul_inv_cancel, locM_one h t K hK, lift_one],
    by rw [lift_mul, ← locM_mul h t K hK, inv_mul_cancel, locM_one h t K hK, lift_one]⟩

theorem adelicGL_at (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (K : Matrix ι ι E)
    (hK : IsUnit (K.map t).det) (g : GL ι (Fv F v)) :
    At (evFin F v) (((adelicGL h t K hK g : GL ι (AE F E)) : Matrix ι ι (AE F E)) - 1) :=
  lift_sub_one_at v _

theorem adelicGL_unitary (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (K : Matrix ι ι E)
    (hK : IsUnit (K.map t).det) (skew : ∀ i j, σ (K j i) = -K i j) (g : GL ι (Fv F v)) :
    ((adelicGL h t K hK g : GL ι (AE F E)) : Matrix ι ι (AE F E))ᵀ * incM F K *
      ((adelicGL h t K hK g : GL ι (AE F E)) : Matrix ι ι (AE F E)).map (cA σ) = incM F K :=
  lift_unitary v σ K _ (locM_unitary h t K hK skew g)

theorem adelicGL_map_piW (h : IsCMExt F E σ) (t : E →ₐ[F] Fv F v) (K : Matrix ι ι E)
    (hK : IsUnit (K.map t).det) (g : GL ι (Fv F v)) :
    Matrix.GeneralLinearGroup.map (piW t) (adelicGL h t K hK g) = g := by
  apply Units.ext
  show (lift v (locM h t K g)).map (piW t) = (g : Matrix ι ι (Fv F v))
  conv_rhs => rw [← pairMat_fst h t (g : Matrix ι ι (Fv F v)) (conjC t K g),
    ← compFin_lift v (pairMat h t (g : Matrix ι ι (Fv F v)) (conjC t K g)), Matrix.map_map]
  rfl

end Hom

end GlobalTheory.LeviIdx

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMapSurjective
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.DblScal
open scoped Matrix

noncomputable section

namespace GlobalTheory.DblScal

namespace SplitSurj

theorem dbl_incM {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ}
    (J : Matrix (Fin d) (Fin d) E) : dbl (incM F J) = incM F (dbl J) := by
  ext (i | i) (j | j) <;> simp [dbl, incM]

theorem dbl_skew {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ}
    (J : Matrix (Fin d) (Fin d) E) (hJ : ∀ i j, σ (J j i) = -J i j) :
    ∀ i j, σ (dbl J j i) = -dbl J i j := by
  rintro (i | i) (j | j) <;> simp [dbl, hJ]

theorem isUnit_det_dbl_map {F E K : Type} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
    (t : E →ₐ[F] K) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (hJ : J.det ≠ 0) : IsUnit ((dbl J).map t).det := by
  have h1 : (J.map t).det ≠ 0 := by
    rw [show J.map t = (t : E →+* K).mapMatrix J from rfl, ← RingHom.map_det]
    exact (map_ne_zero _).2 hJ
  rw [dbl, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero t), Matrix.det_fromBlocks_zero₂₁]
  refine isUnit_iff_ne_zero.2 (mul_ne_zero h1 ?_)
  rw [show ((-J).map t) = -(J.map t) by ext i j; simp, Matrix.det_neg]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) h1

end SplitSurj

open SplitSurj in
theorem locMatD_surjOn : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (d : ℕ) (J : Matrix (Fin d) (Fin d) E), J.det ≠ 0 → (∀ i j, σ (J j i) = -J i j) →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (c : GL (Fin d) (Fv F v)),
    Set.SurjOn (locMatD (σ := σ) (J := J) t c) (UDAt σ J (evFin F v)) Set.univ := by
  intro F E _ _ _ _ _ σ h d J hdet hJ v t c A _
  have hK := isUnit_det_dbl_map t J hdet
  have skew := dbl_skew σ J hJ
  let A' : GL (Fin d ⊕ Fin d) (Fv F v) := dsum c * A * (dsum c)⁻¹
  let G : GL (Fin d ⊕ Fin d) (AE F E) := GlobalTheory.LeviIdx.adelicGL h t (dbl J) hK A'
  have hu : G ∈ UG (cA σ) (dbl (incM F J)) := by
    show (G : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E))ᵀ * dbl (incM F J) *
      (G : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (cA σ) = dbl (incM F J)
    rw [dbl_incM]
    exact GlobalTheory.LeviIdx.adelicGL_unitary h t (dbl J) hK skew A'
  refine ⟨⟨G, hu⟩, GlobalTheory.LeviIdx.adelicGL_at h t (dbl J) hK A', ?_⟩
  change (dsum c)⁻¹ * Matrix.GeneralLinearGroup.map (piW t) G * dsum c = A
  rw [GlobalTheory.LeviIdx.adelicGL_map_piW]
  show (dsum c)⁻¹ * (dsum c * A * (dsum c)⁻¹) * dsum c = A
  group

end GlobalTheory.DblScal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMapSurjectiveStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.DblScal
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_matrix_map_surjective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (d : ℕ) (J : Matrix (Fin d) (Fin d) E), J.det ≠ 0 → (∀ i j, σ (J j i) = -J i j) →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (c : GL (Fin d) (Fv F v)),
    Set.SurjOn (locMatD (σ := σ) (J := J) t c) (UDAt σ J (evFin F v)) Set.univ := by
  first | exact @GlobalTheory.DblScal.locMatD_surjOn | exact GlobalTheory.DblScal.locMatD_surjOn | (intros; apply GlobalTheory.DblScal.locMatD_surjOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMapInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMapInjective
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.DblScal
open scoped Matrix

noncomputable section

namespace GlobalTheory.DblScal

open Matrix

theorem isUnit_det_dbl_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl (F := F)}
    (t : E →ₐ[F] Fv F v) {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (hJ : J.det ≠ 0) :
    IsUnit ((dbl J).map t).det := by
  have e : ((dbl J).map t).det = (t : E →+* Fv F v) (dbl J).det := by
    rw [RingHom.map_det]; rfl
  rw [e, isUnit_iff_ne_zero]
  have hd : (dbl J).det ≠ 0 := by
    rw [dbl, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
    exact mul_ne_zero hJ (mul_ne_zero (pow_ne_zero _ (by simp)) hJ)
  exact (map_ne_zero_iff _ (t : E →+* Fv F v).injective).2 hd

theorem unitary_at {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (X : UD σ J) :
    ((X.1.val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (piW t))ᵀ * (dbl J).map t *
      (X.1.val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (piW (t.comp σ)) = (dbl J).map t := by
  have hX : (X.1.val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E))ᵀ * dbl (incM F J) *
      (X.1.val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (cA σ) = dbl (incM F J) := X.2
  have h := congrArg (fun M => M.map (piW t)) hX
  simp only [Matrix.map_mul, Matrix.transpose_map] at h
  have eD : (dbl (incM F J)).map (piW t) = (dbl J).map t := by
    ext (i | i) (j | j) <;> simp [dbl, incM, GlobalTheory.Div.CoordOpp.piW_inclR]
  have eC : ((X.1.val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (cA σ)).map (piW t) =
      (X.1.val : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)).map (piW (t.comp σ)) := by
    ext i j; simp [GlobalTheory.Div.CoordOpp.piW_cA]
  rw [eD, eC] at h
  simpa [Matrix.transpose_map] using h

end GlobalTheory.DblScal

open GlobalTheory.DblScal in
theorem GlobalTheory.DblScal.locMatD_injOn : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (d : ℕ) (J : Matrix (Fin d) (Fin d) E), J.det ≠ 0 →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (c : GL (Fin d) (Fv F v)),
    Set.InjOn (locMatD (σ := σ) (J := J) t c) (UDAt σ J (evFin F v)) := by
  intro F E _ _ _ _ _ σ hcm d J hJ v t c p hp q hq hpq
  set P : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) := p.1.val with hPdef
  set Q : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E) := q.1.val with hQdef

  have e0 : (dsum c)⁻¹ * Matrix.GeneralLinearGroup.map (piW t) p.1 * dsum c =
      (dsum c)⁻¹ * Matrix.GeneralLinearGroup.map (piW t) q.1 * dsum c := hpq
  have eG := mul_left_cancel (mul_right_cancel e0)
  have h1 : P.map (piW t) = Q.map (piW t) := congrArg Units.val eG

  have h2 : P.map (piW (t.comp σ)) = Q.map (piW (t.comp σ)) := by
    have hUp := unitary_at t p
    have hUq := unitary_at t q
    rw [← hPdef] at hUp
    rw [← hQdef, ← h1] at hUq
    set g := Matrix.GeneralLinearGroup.map (piW t) p.1
    have hg : (g : Matrix _ _ (Fv F v)) = P.map (piW t) := rfl
    have hinv : ((g⁻¹ : GL _ (Fv F v)) : Matrix _ _ (Fv F v))ᵀ * (P.map (piW t))ᵀ = 1 := by
      rw [← hg, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
    have e1 : (dbl J).map t * P.map (piW (t.comp σ)) = (dbl J).map t * Q.map (piW (t.comp σ)) := by
      have := hUp.trans hUq.symm
      have := congrArg (fun M => ((g⁻¹ : GL _ (Fv F v)) : Matrix _ _ (Fv F v))ᵀ * M) this
      simpa only [← Matrix.mul_assoc, hinv, Matrix.one_mul] using this
    have hD := isUnit_det_dbl_map t hJ
    have := congrArg (fun M => ((dbl J).map t)⁻¹ * M) e1
    simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hD, Matrix.one_mul] using this

  set e := GlobalTheory.EmbChart.atPlace v (1 : Fv F v)
  have hev : evFin F v (1 - e) = 0 := by rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self]
  have hp' : At (evFin F v) (P - 1) := hp
  have hq' : At (evFin F v) (Q - 1) := hq
  have hM : P - Q = e • (P - Q) := by
    have h0 : (1 - e) • (P - Q) = 0 := by
      have : P - Q = (P - 1) - (Q - 1) := by abel
      rw [this, smul_sub, hp' (1 - e) hev, hq' (1 - e) hev, sub_zero]
    rw [sub_smul, one_smul, sub_eq_zero] at h0
    exact h0
  refine Subtype.ext (Units.ext ?_)
  change P = Q
  rw [← sub_eq_zero, hM]
  ext i j
  rw [Matrix.smul_apply, Matrix.zero_apply]
  apply GlobalTheory.InertVacIso.smul_eq_zero_of_compFin
  apply GlobalTheory.AdelicU.split_ext hcm t
  · change piW t ((P - Q) i j) = splitProj t 0
    rw [map_zero, Matrix.sub_apply, map_sub, sub_eq_zero]
    exact congrFun (congrFun h1 i) j
  · change piW (t.comp σ) ((P - Q) i j) = splitProj (t.comp σ) 0
    rw [map_zero, Matrix.sub_apply, map_sub, sub_eq_zero]
    exact congrFun (congrFun h2 i) j

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMapInjectiveStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.DblScal
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_matrix_map_injective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (d : ℕ) (J : Matrix (Fin d) (Fin d) E), J.det ≠ 0 →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (c : GL (Fin d) (Fv F v)),
    Set.InjOn (locMatD (σ := σ) (J := J) t c) (UDAt σ J (evFin F v)) := by
  first | exact @GlobalTheory.DblScal.locMatD_injOn | exact GlobalTheory.DblScal.locMatD_injOn | (intros; apply GlobalTheory.DblScal.locMatD_injOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleScalingLocalEquivariance
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DblScalDet

open GlobalTheory.DblScal
open scoped Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem udat_mul {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E} {R : Type} [Zero R] {ev : AF F → R}
    {p q : UD σ J} (hp : p ∈ UDAt σ J ev) (hq : q ∈ UDAt σ J ev) : p * q ∈ UDAt σ J ev := by
  intro u hu
  have e : ((((p * q : UD σ J) : GL (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) - 1 =
      ((((p : UD σ J) : GL (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) *
        (((q : UD σ J) : GL (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) +
      ((((q : UD σ J) : GL (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) := by
    simp [sub_mul]
  rw [e, smul_add, ← Matrix.smul_mul, hp u hu, hq u hu, Matrix.zero_mul, add_zero]

theorem udat_one {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E} {R : Type} [Zero R] {ev : AF F → R} :
    (1 : UD σ J) ∈ UDAt σ J ev := by
  intro u _
  simp

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hn, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hn)
  have key : (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star =
      (Aᵀ * M * A.map star).submatrix e.symm e.symm := by
    ext i j; rfl
  have hd := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, hA, Matrix.det_mul, Matrix.det_mul] at hd
  intro h0
  rw [h0] at hd
  simp [Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg] at hd
  exact pow_ne_zero _ (by norm_num) hd.symm

theorem det_ne_zero_of_skew {σ : E →ₐ[F] E} {B : Base F E} {d r s : ℕ} {W : Spc F E d} (h : W.IsSkew σ B r s) :
    W.J.det ≠ 0 := by
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  have h0 := det_ne_zero_of_hasSig (h.sig (InfinitePlace.mk φ))
  intro e
  apply h0
  rw [Matrix.det_smul, show W.J.map _ = RingHom.mapMatrix _ W.J from rfl, ← RingHom.map_det, e, map_zero, mul_zero]

theorem mulLaw : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (ψ : AddChar (AF F) ℂ) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v)
    (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) (dd : DblCo σ X W) (omd : DblRep σ (n := n) W),
    IsUSplitting (adeleClass F) ψ dd (actB (cA σ)) omd → LocOps omd v →
    ∀ ιd, IsLinD ψ dd t b c ιd → ∀ cd, IsShapeD omd t c ιd cd →
    cd 1 = 1 ∧ ∀ p ∈ UDAt σ W.J (evFin F v), ∀ q ∈ UDAt σ W.J (evFin F v), cd (p * q) = cd p * cd q := by
  intro F E _ _ _ _ _ σ ψ n d X W v t b c dd omd hS hL ιd hI cd hD
  obtain ⟨φ0, hφ0, hne⟩ : ∃ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), ιd φ ≠ 0 := by
    have hmem : (intM (Fv F v) (Fin n) (Fin d ⊕ Fin d)).indicator (1 : Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v) → ℂ) ∈
        SB (Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)) := indicator_intM_mem_SB
    obtain ⟨φ, hφ, he⟩ := hI.bij.surjOn hmem
    refine ⟨φ, hφ, fun h => ?_⟩
    have h0 := congrFun he 0
    rw [h, Set.indicator_of_mem (fun i j => by simp)] at h0
    simp at h0
  obtain ⟨Z, hZ⟩ : ∃ Z, ιd φ0 Z ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have comp : ∀ p q : UD σ W.J, ∀ φ φ₁ φ₂ : (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) → ℂ,
      Acts (evFin F v) (omd q) φ φ₁ → Acts (evFin F v) (omd p) φ₁ φ₂ → Acts (evFin F v) (omd (p * q)) φ φ₂ := by
    intro p q φ φ₁ φ₂ hq hp r hr
    have h1 := hq r hr
    have hr1 : Rest (evFin F v) φ₁ r := ⟨hr.1, h1 ▸ hS.pres q _ hr.2⟩
    rw [map_mul, Module.End.mul_apply, h1, hp r hr1]
  refine ⟨?_, ?_⟩
  · have hA : Acts (evFin F v) (omd 1) φ0 φ0 := fun r _ => by rw [map_one, Module.End.one_apply]
    have e := congrFun (hD 1 udat_one φ0 hφ0 φ0 hφ0 hA) Z
    simp only [map_one, Units.val_one, Matrix.mul_one, Pi.smul_apply, smul_eq_mul] at e
    exact (mul_eq_right₀ hZ).mp e.symm
  · intro p hp q hq
    obtain ⟨φ₁, hφ₁, h1⟩ := hL q hq φ0 hφ0
    obtain ⟨φ₂, hφ₂, h2⟩ := hL p hp φ₁ hφ₁
    have e1 := hD q hq φ0 hφ0 φ₁ hφ₁ h1
    have e2 := hD p hp φ₁ hφ₁ φ₂ hφ₂ h2
    have e3 := hD (p * q) (udat_mul hp hq) φ0 hφ0 φ₂ hφ₂ (comp p q φ0 φ₁ φ₂ h1 h2)
    have hG : GlobalTheory.SplitFlip.invT (locMatD t c (p * q)) =
        GlobalTheory.SplitFlip.invT (locMatD t c p) * GlobalTheory.SplitFlip.invT (locMatD t c q) := by
      rw [map_mul, map_mul]
    set G := GlobalTheory.SplitFlip.invT (locMatD t c (p * q))
    have hY := congrFun (e3.symm.trans e2) (Z * (G⁻¹).val)
    rw [e1] at hY
    simp only [Pi.smul_apply, smul_eq_mul] at hY
    have k1 : Z * (G⁻¹).val * G.val = Z := by rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    have k2 : Z * (G⁻¹).val * (GlobalTheory.SplitFlip.invT (locMatD t c p)).val * (GlobalTheory.SplitFlip.invT (locMatD t c q)).val = Z := by
      rw [Matrix.mul_assoc, ← Units.val_mul, ← hG, k1]
    rw [k1, k2, ← mul_assoc] at hY
    exact mul_right_cancel₀ hZ hY

end GlobalTheory.DblScalDet


open GlobalTheory.DblScalDet in
theorem GlobalTheory.DblScal.scalar_factors_through_det : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
      (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd → GlobalTheory.DblScal.LocOps omd v →
      ∀ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd → ∀ cd, GlobalTheory.DblScal.IsShapeD omd t c ιd cd →
      ∃ χd : (Fv F v)ˣ → ℂ, ∀ p ∈ GlobalTheory.DblScal.UDAt σ W.J (evFin F v),
        cd p = χd (GlobalTheory.SplitFlip.gdet (GlobalTheory.DblScal.locMatD t c p)) := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v t b c dd omd hS hL ιd hI cd hD
  obtain ⟨h1, hmul⟩ := mulLaw F E σ B.ψ n d X W v t b c dd omd hS hL ιd hI cd hD
  have hJ : W.J.det ≠ 0 := det_ne_zero_of_skew hP.skew
  have hinj := GlobalTheory.T.local_matrix_map_injective F E σ hP.base.cm d W.J hJ v t c
  have hsurj := GlobalTheory.T.local_matrix_map_surjective F E σ hP.base.cm d W.J hJ hP.skew.skew v t c
  have hex : ∀ A : GL (Fin d ⊕ Fin d) (Fv F v), ∃ p ∈ GlobalTheory.DblScal.UDAt σ W.J (evFin F v), GlobalTheory.DblScal.locMatD t c p = A :=
    fun A => hsurj (Set.mem_univ A)
  choose sec hsU hs using hex
  have hsm : ∀ A A', sec (A * A') = sec A * sec A' := fun A A' =>
    hinj (hsU _) (udat_mul (hsU A) (hsU A')) (by rw [hs, map_mul, hs, hs])
  have hs1 : sec 1 = 1 := hinj (hsU 1) udat_one (by rw [hs, map_one])
  let f : GL (Fin d ⊕ Fin d) (Fv F v) →* ℂˣ :=
    { toFun := fun A => ⟨cd (sec A), cd (sec A⁻¹),
        by rw [← hmul _ (hsU _) _ (hsU _), ← hsm, mul_inv_cancel, hs1, h1],
        by rw [← hmul _ (hsU _) _ (hsU _), ← hsm, inv_mul_cancel, hs1, h1]⟩
      map_one' := Units.ext (by simp only [hs1, h1, Units.val_one])
      map_mul' := fun A A' => Units.ext (by simp only [Units.val_mul]; rw [hsm, hmul _ (hsU _) _ (hsU _)]) }
  let e : Fin d ⊕ Fin d ≃ Fin (d + d) := finSumFinEquiv
  let rr : GL (Fin (d + d)) (Fv F v) →* GL (Fin d ⊕ Fin d) (Fv F v) :=
    Units.map (Matrix.reindexAlgEquiv (Fv F v) (Fv F v) e.symm).toMonoidHom
  have h2 : (2 : Fv F v) ≠ 0 := fun h => two_ne_zero (α := F) ((algebraMap F (Fv F v)).injective (by rw [map_ofNat, h, map_zero]))
  obtain ⟨χ, hχ⟩ := GlobalTheory.ghom_factors_through_det (k := Fv F v) h2 (f.comp rr)
  refine ⟨fun x => (χ x : ℂ), fun p hp => ?_⟩
  have hp' : sec (GlobalTheory.DblScal.locMatD t c p) = p := hinj (hsU _) hp (hs _)
  set A := GlobalTheory.DblScal.locMatD t c p
  let A' : GL (Fin (d + d)) (Fv F v) := Units.map (Matrix.reindexAlgEquiv (Fv F v) (Fv F v) e).toMonoidHom A
  have hA : rr A' = A := Units.ext (by ext i j; simp [rr, A'])
  have hdet : Matrix.GeneralLinearGroup.det A' = GlobalTheory.SplitFlip.gdet A :=
    Units.ext (by simp [A', GlobalTheory.SplitFlip.gdet, Matrix.det_reindex_self])
  have hf := hχ A'
  rw [MonoidHom.comp_apply, hA, hdet] at hf
  calc cd p = cd (sec A) := by rw [hp']
    _ = ((f A : ℂˣ) : ℂ) := rfl
    _ = _ := by rw [hf]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleScalingLocalEquivarianceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_scaling_local_equivariance : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
      (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd → GlobalTheory.DblScal.LocOps omd v →
      ∀ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd → ∀ cd, GlobalTheory.DblScal.IsShapeD omd t c ιd cd →
      ∃ χd : (Fv F v)ˣ → ℂ, ∀ p ∈ GlobalTheory.DblScal.UDAt σ W.J (evFin F v),
        cd p = χd (GlobalTheory.SplitFlip.gdet (GlobalTheory.DblScal.locMatD t c p)) := by
  first | exact @GlobalTheory.DblScal.scalar_factors_through_det | exact GlobalTheory.DblScal.scalar_factors_through_det | (intros; apply GlobalTheory.DblScal.scalar_factors_through_det <;> assumption)
end
