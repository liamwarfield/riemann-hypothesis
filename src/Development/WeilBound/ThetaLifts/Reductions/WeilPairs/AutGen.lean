module

public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutDef

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InfiniteNormOne
theorem UpperTheory.Reformulated.B.InfiniteNormOne.infinite_norm_one :
    ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E]
      [inst_4 : Algebra F E] {σ : E →ₐ[F] E} {B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E}
      {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
      {θ : NumberField.InfinitePlace F → TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) E →+* ℂ}
      {ι : (NumberField.InfinitePlace F → ℂ) →+ Formalism.IndefR.DatumF.AEF F E},
      PositivityTheory.ThKW.Ctx σ B JS JT ξ₀ θ ι → {t : E | t * (σ : E → E) t = (1 : E)}.Infinite := by
  intro F E _ _ _ _ _ σ B nS nT JS JT ξ θ ι h
  obtain ⟨-, -, -, h0, hσ, -, -⟩ := h
  have hz : ∀ n : ℤ, (n : E) - ξ ≠ 0 := fun n hn => h0 <| by
    have e : ξ = (n : E) := (sub_eq_zero.mp hn).symm
    have e2 : σ ξ = ξ := by rw [e, map_intCast]
    linear_combination (1 / 2 : E) * hσ - (1 / 2 : E) * e2
  have hp : ∀ n : ℤ, (n : E) + ξ ≠ 0 := fun n hn => hz (-n) <| by
    push_cast; linear_combination -hn
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℤ => ((n : E) + ξ) / ((n : E) - ξ))
    (fun n m hnm => ?_) (fun n => ?_)
  · have e := (div_eq_div_iff (hz n) (hz m)).mp hnm
    have e2 : ((n : E) - m) * ξ = 0 := by linear_combination (-1 / 2 : E) * e
    exact Int.cast_injective (sub_eq_zero.mp ((mul_eq_zero.mp e2).resolve_right h0))
  · simp only [Set.mem_setOf_eq, map_div₀, map_add (f := _), map_sub, map_intCast, hσ, sub_neg_eq_add,
      ← sub_eq_add_neg]
    rw [div_mul_div_comm, mul_comm, div_self (mul_ne_zero (hz n) (hp n))]
end

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutGenA
set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct Matrix Kronecker Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix Formalism.IndefR.DatumF

namespace PositivityTheory.ThKW.GenA

section Abstract

theorem det_unit_sig {K ι G : Type} [Field K] [Fintype ι] [DecidableEq ι] [FunLike G K K] [RingHomClass G K K] (σ : G)
    {M P : Matrix ι ι K} (hP : P.det ≠ 0) (h : (M.map σ)ᵀ * P * M = P) :
    M.det * σ M.det = 1 ∧ M.det * σ (M - 1).det = (-1) ^ Fintype.card ι * (M - 1).det := by
  have hd : ∀ N : Matrix ι ι K, (N.map σ)ᵀ.det = σ N.det := fun N => by
    rw [det_transpose]; exact (RingHom.map_det (σ : K →+* K) N).symm
  constructor
  · have := congrArg Matrix.det h
    rw [det_mul, det_mul, hd] at this
    refine mul_right_cancel₀ hP ?_
    linear_combination this
  · have hm : (M - 1).map σ = M.map σ - 1 := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    have e : ((M - 1).map σ)ᵀ * P * M = P * -(M - 1) := by
      rw [hm, transpose_sub, transpose_one, Matrix.sub_mul, Matrix.sub_mul, h, Matrix.one_mul, neg_sub, Matrix.mul_sub,
        Matrix.mul_one]
    have := congrArg Matrix.det e
    rw [det_mul, det_mul, det_mul, hd, det_neg] at this
    refine mul_right_cancel₀ hP ?_
    linear_combination this

theorem kron_unit_sig {K G : Type} [Field K] [FunLike G K K] [RingHomClass G K K] (σ : G) {m n : ℕ}
    {a Gm : Matrix (Fin n) (Fin n) K} {b H : Matrix (Fin m) (Fin m) K} (hG : IsUnit Gm.det)
    (ha : (a.map σ)ᵀ * Gm * a = Gm) (hb : (b.map σ)ᵀ * H * b = H) :
    ((b ⊗ₖ aᵀ).map σ)ᵀ * (H ⊗ₖ Gm⁻¹ᵀ) * (b ⊗ₖ aᵀ) = H ⊗ₖ Gm⁻¹ᵀ := by
  have h1 : (Gm⁻¹ * (a.map σ)ᵀ * Gm) * a = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (a.map σ)ᵀ, ha, Matrix.nonsing_inv_mul _ hG]
  have h2 : a * Gm⁻¹ * (a.map σ)ᵀ = Gm⁻¹ := by
    have h3 := mul_eq_one_comm.1 h1
    calc a * Gm⁻¹ * (a.map σ)ᵀ = a * (Gm⁻¹ * (a.map σ)ᵀ * Gm) * Gm⁻¹ := by
          simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.mul_one]
      _ = Gm⁻¹ := by rw [h3, Matrix.one_mul]
  have e : ((b ⊗ₖ aᵀ).map σ)ᵀ = (b.map σ)ᵀ ⊗ₖ a.map σ := by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp [Matrix.kroneckerMap_apply, map_mul]
  rw [e, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hb]
  congr 1
  conv_rhs => rw [← h2]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

theorem cart_exists {k : ℕ} (G : Matrix (Fin k) (Fin k) ℂ) (hG : Gᴴ = G) (hd : G.det ≠ 0) (r : ℝ) (hr : r ≠ 0) :
    ∃ s, Formalism.IndefR.Datum.IsCartanInv ((r : ℂ) • G) s := by
  refine GlobalTheory.Mem.ThetaNonzero.exists_isCartanInv ?_ (isUnit_iff_ne_zero.2 ?_)
  · show ((r : ℂ) • G)ᴴ = (r : ℂ) • G
    rw [conjTranspose_smul, hG, Complex.star_def, Complex.conj_ofReal]
  · rw [det_smul]
    exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.2 hr)) hd

theorem cart_refl {k : ℕ} (G : Matrix (Fin k) (Fin k) ℂ) (hG : Gᴴ = G) (hd : G.det ≠ 0) (r : ℝ) (hr : r ≠ 0)
    (y : Fin k → ℂ) (hy : star y ⬝ᵥ G *ᵥ y ≠ 0) (d : ℂ) :
    ∃ s, Formalism.IndefR.Datum.IsCartanInv ((r : ℂ) • G) s ∧
      s * (1 + d • vecMulVec y (star y ᵥ* G)) = (1 + d • vecMulVec y (star y ᵥ* G)) * s := by
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr
  obtain ⟨s, h1, h2⟩ := GlobalTheory.T.exists_cartanInvolution_comm_quasiReflection _ ((r : ℂ) • G)
    (by rw [conjTranspose_smul, hG, Complex.star_def, Complex.conj_ofReal])
    (by rw [det_smul]; exact mul_ne_zero (pow_ne_zero _ hr') hd) y
    (by
      have e : star y ⬝ᵥ ((r : ℂ) • G) *ᵥ y = (r : ℂ) * (star y ⬝ᵥ G *ᵥ y) := by
        simp only [dotProduct, mulVec, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      rw [e]
      exact mul_ne_zero hr' hy)
  refine ⟨s, h1, ?_⟩
  have e : d • vecMulVec y (star y ᵥ* G) = (d / r) • vecMulVec y (star y ᵥ* ((r : ℂ) • G)) := by
    ext i j
    simp only [Matrix.smul_apply, vecMulVec_apply, vecMul, dotProduct, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    field_simp
  rw [e]
  exact h2 _

theorem blk_comm {O : Type} [Fintype O] [DecidableEq O] {m n : ℕ} {sT b : O → Matrix (Fin m) (Fin m) ℂ}
    {sS a : O → Matrix (Fin n) (Fin n) ℂ} (h1 : ∀ w, sT w * b w = b w * sT w) (h2 : ∀ w, a w * sS w = sS w * a w) :
    GlobalTheory.RealWeil.blk sT sS * GlobalTheory.RealWeil.blk b a = GlobalTheory.RealWeil.blk b a * GlobalTheory.RealWeil.blk sT sS := by
  rw [GlobalTheory.RealWeil.blk_mul, GlobalTheory.RealWeil.blk_mul]
  congr 1 <;> funext w
  exacts [h1 w, h2 w]

end Abstract

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incAF_injective : Function.Injective (incAF F E) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)

theorem mt_unitary (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : GAF σ J) :
    ((mtF σ J g).map (cAF σ))ᵀ * J.map (incAF F E) * mtF σ J g = J.map (incAF F E) := g.2

theorem mt_ext {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g h : GAF σ J} (e : mtF σ J g = mtF σ J h) :
    g = h := Subtype.ext (Units.ext e)

theorem mt_one (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : mtF σ J 1 = 1 := rfl

theorem mt_mul (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g h : GAF σ J) :
    mtF σ J (g * h) = mtF σ J g * mtF σ J h := rfl

theorem map_unitary (σ : E →ₐ[F] E) {n : ℕ} (J a : Matrix (Fin n) (Fin n) E) :
    ((a.map (incAF F E)).map (cAF σ))ᵀ * J.map (incAF F E) * a.map (incAF F E) =
      ((a.map σ)ᵀ * J * a).map (incAF F E) := by
  rw [Matrix.map_mul, Matrix.map_mul]
  rfl

theorem det_ne_of_unitary {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J)
    {a : Matrix (Fin n) (Fin n) E} (h : (a.map σ)ᵀ * J * a = J) : a.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det h
  rw [det_mul, det_mul, h0, mul_zero] at this
  exact hJ.2 this.symm

theorem infPart_incAF (x : E) : infPartF F E (incAF F E x) = (1 : Ainf F) ⊗ₜ[F] x := by
  show Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) ((1 : AF F) ⊗ₜ[F] x) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem herm_map {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J)
    (τ : E →+* ℂ) : (J.map τ)ᴴ = J.map τ := by
  ext i j
  rw [conjTranspose_apply, Matrix.map_apply, Matrix.map_apply, ← hcm.2.2.2, hJ.1]

theorem det_map_ne {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) (τ : E →+* ℂ) :
    (J.map τ).det ≠ 0 := by
  rw [show (J.map τ).det = τ J.det from (RingHom.map_det τ J).symm]
  exact (map_ne_zero τ).2 hJ.2

theorem im_ne {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {ξ₀ : E} (h0 : ξ₀ ≠ 0) (hξ : σ ξ₀ = -ξ₀) (τ : E →+* ℂ) :
    (τ ξ₀).im ≠ 0 := by
  intro him
  have h1 : star (τ ξ₀) = -τ ξ₀ := by rw [← hcm.2.2.2, hξ, map_neg]
  have hre : (τ ξ₀).re = 0 := by
    have := congrArg Complex.re h1
    rw [Complex.star_def, Complex.conj_re, Complex.neg_re] at this
    linarith
  apply h0
  apply τ.injective
  rw [map_zero]
  exact Complex.ext (by rw [hre, Complex.zero_re]) (by rw [him, Complex.zero_im])

theorem hermE_alt (c : E ≃ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    GlobalTheory.UnRep.hermE c Jᵀ x y = (fun b => c (y b)) ⬝ᵥ J *ᵥ x := by
  simp only [GlobalTheory.UnRep.hermE, dotProduct, mulVec, transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem isUnE_iff (c : E ≃ₐ[F] E) {n : ℕ} (J M : Matrix (Fin n) (Fin n) E) :
    GlobalTheory.UnRep.IsUnE c Jᵀ M ↔ (M.map (c : E →ₐ[F] E))ᵀ * J * M = J := by
  have e1 : ∀ y : Fin n → E, (fun b => c ((M *ᵥ y) b)) = (fun b => c (y b)) ᵥ* (M.map (c : E →ₐ[F] E))ᵀ :=
    fun y => by
      rw [vecMul_transpose]
      funext i
      exact RingHom.map_mulVec ((c : E →ₐ[F] E) : E →+* E) M y i
  have e : ∀ x y, GlobalTheory.UnRep.hermE c Jᵀ (M *ᵥ x) (M *ᵥ y) =
      (fun b => c (y b)) ⬝ᵥ ((M.map (c : E →ₐ[F] E))ᵀ * J * M) *ᵥ x := fun x y => by
    rw [hermE_alt, e1, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  have hs : ∀ i : Fin n, (fun b => c ((Pi.single i (1 : E) : Fin n → E) b)) = (Pi.single i (1 : E) : Fin n → E) :=
    fun i => funext fun b => by by_cases h : b = i <;> simp [h]
  refine ⟨fun h => ?_, fun h x y => by rw [e, h, hermE_alt]⟩
  ext i j
  have := h (Pi.single j 1) (Pi.single i 1)
  rw [e, hermE_alt, hs] at this
  simpa using this

theorem quad_map {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (c : E ≃ₐ[F] E) (hc : (c : E →ₐ[F] E) = σ) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (τ : E →+* ℂ) :
    star (τ ∘ x) ⬝ᵥ J.map τ *ᵥ (τ ∘ x) = τ (GlobalTheory.UnRep.hermE c Jᵀ x x) := by
  have h' : ∀ z, τ (c z) = star (τ z) := fun z => by rw [← hcm.2.2.2, ← hc]; rfl
  rw [hermE_alt, RingHom.map_dotProduct]
  congr 1
  · funext i
    simp [h']
  · funext i
    exact (RingHom.map_mulVec τ J x i).symm

theorem refl_map {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (c : E ≃ₐ[F] E) (hc : (c : E →ₐ[F] E) = σ) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (u : E) (τ : E →+* ℂ) :
    (GlobalTheory.UnRep.refl c Jᵀ x u).map τ =
      1 + τ ((u - 1) / GlobalTheory.UnRep.hermE c Jᵀ x x) • vecMulVec (τ ∘ x) (star (τ ∘ x) ᵥ* J.map τ) := by
  have h' : ∀ z, τ (c z) = star (τ z) := fun z => by rw [← hcm.2.2.2, ← hc]; rfl
  have e : τ ∘ (Jᵀ *ᵥ fun b => c (x b)) = star (τ ∘ x) ᵥ* J.map τ := by
    funext j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Function.comp_apply, mulVec, vecMul, dotProduct, transpose_apply, map_sum, map_mul, Matrix.map_apply,
      Pi.star_apply, h']
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [GlobalTheory.UnRep.refl, ← RingHom.mapMatrix_apply, map_add (f := _), map_one, ← e]
  congr 1
  ext i j
  simp [vecMulVec_apply, map_mul]

end PositivityTheory.ThKW.GenA

end
end

noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}

theorem exists_isRatF {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : GAF σ J} (hg : g ∈ GQF σ J) : ∃ a, IsRatF σ J g a := by
  obtain ⟨a, -, ha⟩ := hg
  exact ⟨a.1, (congrArg Units.val ha).symm⟩

theorem IsRatF.mem {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : GAF σ J} {a} (h : IsRatF σ J g a) : g ∈ GQF σ J := by
  have hu : (a.map σ)ᵀ * J * a = J := by
    have e := GenA.mt_unitary σ J g
    rw [show mtF σ J g = _ from h, GenA.map_unitary] at e
    exact Matrix.map_injective GenA.incAF_injective e
  have hd : a.det ≠ 0 := by
    intro h0
    have : Nontrivial (AEF F E) := GenA.incAF_injective.nontrivial
    have hu' := Matrix.isUnits_det_units (g : HR (AF F) σ J).1
    rw [show ((g : HR (AF F) σ J).1 : Matrix (Fin n) (Fin n) (AEF F E)) = a.map (incAF F E) from h,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero] at hu'
    exact not_isUnit_zero hu'
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero a hd, hu, Units.ext h.symm⟩

theorem IsRatF.unitary {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : GAF σ J} {a} (h : IsRatF σ J g a) :
    (a.map σ)ᵀ * J * a = J := by
  have e := GenA.mt_unitary σ J g
  rw [show mtF σ J g = _ from h, GenA.map_unitary] at e
  exact Matrix.map_injective GenA.incAF_injective e

theorem IsRatF.mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g g' : GAF σ J} {a a'} (h : IsRatF σ J g a)
    (h' : IsRatF σ J g' a') : IsRatF σ J (g * g') (a * a') := by
  show mtF σ J (g * g') = (a * a').map (incAF F E)
  rw [GenA.mt_mul, show mtF σ J g = _ from h, show mtF σ J g' = _ from h', Matrix.map_mul]

theorem isRatF_one {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : IsRatF σ J 1 1 := by
  show mtF σ J 1 = (1 : Matrix (Fin n) (Fin n) E).map (incAF F E)
  rw [GenA.mt_one, Matrix.map_one _ (incAF F E).map_zero (incAF F E).map_one]

theorem exists_of_unitary {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) {a : Matrix (Fin n) (Fin n) E}
    (h : (a.map σ)ᵀ * J * a = J) : ∃ g, IsRatF σ J g a := by
  have hd := GenA.det_ne_of_unitary hJ h
  refine ⟨(⟨Formalism.UG.bc (incAF F E) (Matrix.GeneralLinearGroup.mkOfDetNeZero a hd), ?_⟩ : HR (AF F) σ J), rfl⟩
  show ((a.map (incAF F E)).map (cAF σ))ᵀ * J.map (incAF F E) * a.map (incAF F E) = J.map (incAF F E)
  rw [GenA.map_unitary, h]

theorem infinite_norm_one (C : Ctx σ B JS JT ξ₀ θ ι) : {t : E | t * σ t = 1}.Infinite :=
  _root_.UpperTheory.Reformulated.B.InfiniteNormOne.infinite_norm_one C

theorem det_kron (C : Ctx σ B JS JT ξ₀ θ ι) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) :
    (b ⊗ₖ aᵀ).det * σ (b ⊗ₖ aᵀ).det = 1 ∧
      (b ⊗ₖ aᵀ).det * σ (b ⊗ₖ aᵀ - 1).det = (-1) ^ Fintype.card (Fin nT × Fin nS) * (b ⊗ₖ aᵀ - 1).det := by
  have hu : IsUnit JS.det := isUnit_iff_ne_zero.2 C.hS.2
  have hP : (JT ⊗ₖ JS⁻¹ᵀ).det ≠ 0 := by
    rw [det_kronecker, det_transpose]
    exact mul_ne_zero (pow_ne_zero _ C.hT.2) (pow_ne_zero _ (Matrix.isUnit_nonsing_inv_det JS hu).ne_zero)
  exact GenA.det_unit_sig σ hP (GenA.kron_unit_sig σ hu ha.unitary hb.unitary)

namespace GenR

theorem isRat_ext {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g g' : GAF σ J} {a} (h : IsRatF σ J g a)
    (h' : IsRatF σ J g' a) : g = g' :=
  GenA.mt_ext (h.trans h'.symm)

theorem rat_ind (c : E ≃ₐ[F] E) (hcm : IsCMExt F E (c : E →ₐ[F] E)) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : IsHermND (c : E →ₐ[F] E) J) (R : GAF (c : E →ₐ[F] E) J → Prop) (h1 : R 1)
    (hm : ∀ g ∈ GQF (c : E →ₐ[F] E) J, ∀ g' ∈ GQF (c : E →ₐ[F] E) J, R g → R g' → R (g * g'))
    (hr : ∀ g x u, GlobalTheory.UnRep.hermE c Jᵀ x x ≠ 0 → IsRatF (c : E →ₐ[F] E) J g (GlobalTheory.UnRep.refl c Jᵀ x u) → R g) :
    ∀ g ∈ GQF (c : E →ₐ[F] E) J, R g := by
  have hH : GlobalTheory.UnRep.IsHermForm c Jᵀ := ⟨GlobalTheory.SplitDetCharF.sig_invol hcm, fun h => by
      obtain ⟨x, hx⟩ := GlobalTheory.SplitDetCharF.sig_ne hcm
      exact hx (by subst h; rfl), fun a b => hJ.1 a b, by rw [Matrix.det_transpose]; exact hJ.2⟩
  have key : ∀ l : List ((Fin n → E) × E), (∀ p ∈ l, GlobalTheory.UnRep.hermE c Jᵀ p.1 p.1 ≠ 0 ∧ p.2 * c p.2 = 1) →
      ∀ g, IsRatF (c : E →ₐ[F] E) J g (l.map fun p => GlobalTheory.UnRep.refl c Jᵀ p.1 p.2).prod → R g := by
    intro l
    induction l with
    | nil =>
      intro _ g hg
      rw [List.map_nil, List.prod_nil] at hg
      rw [isRat_ext hg (isRatF_one J)]
      exact h1
    | cons p l ih =>
      intro hl g hg
      obtain ⟨p1, p2⟩ := hl p List.mem_cons_self
      have hl' : ∀ q ∈ l, GlobalTheory.UnRep.hermE c Jᵀ q.1 q.1 ≠ 0 ∧ q.2 * c q.2 = 1 :=
        fun q hq => hl q (List.mem_cons_of_mem _ hq)
      obtain ⟨g₁, r1⟩ := exists_of_unitary hJ ((GenA.isUnE_iff c J _).1
        ((GlobalTheory.UnRep.ReflLaws.refl_laws _ _ c n Jᵀ hH p.1 p1).2.2.2 p.2 p2))
      obtain ⟨g₂, r2⟩ := exists_of_unitary hJ ((GenA.isUnE_iff c J _).1 (GlobalTheory.UnRep.ReflGen.isUnE_prod hH l hl'))
      rw [List.map_cons, List.prod_cons] at hg
      rw [isRat_ext hg (r1.mul r2)]
      exact hm _ r1.mem _ r2.mem (hr g₁ p.1 p.2 p1 r1) (ih hl' g₂ r2)
  intro g hg
  obtain ⟨a, ha⟩ := exists_isRatF hg
  obtain ⟨l, hl, e⟩ := GlobalTheory.UnRep.isUnE_eq_prod_refl _ _ c n Jᵀ hH a ((GenA.isUnE_iff c J a).2 ha.unitary)
  subst e
  exact key l hl g ha

theorem compAt_rat (C : Ctx σ B JS JT ξ₀ θ ι) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : GAF σ J} {a}
    (h : IsRatF σ J g a) (w : InfinitePlace F) : compAtF θ w (mtF σ J g) = a.map (tauB B w) := by
  rw [show mtF σ J g = _ from h]
  ext i j
  show θ w (infPartF F E (incAF F E (a i j))) = tauB B w (a i j)
  rw [GenA.infPart_incAF]
  exact (C.inf w).1 (a i j)

theorem compAt_one {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (w : InfinitePlace F) : compAtF θ w (mtF σ J 1) = 1 := by
  rw [GenA.mt_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem cart_blk (C : Ctx σ B JS JT ξ₀ θ ι) {sS : InfinitePlace F → Matrix (Fin nS) (Fin nS) ℂ}
    {sT : InfinitePlace F → Matrix (Fin nT) (Fin nT) ℂ}
    (hS : ∀ w, Formalism.IndefR.Datum.IsCartanInv (JS.map (tauB B w)) (sS w))
    (hT : ∀ w, Formalism.IndefR.Datum.IsCartanInv (((2 * (tauB B w ξ₀).im : ℝ) : ℂ) • JT.map (tauB B w)) (sT w)) :
    CartF σ JS JT ξ₀ B θ (GlobalTheory.RealWeil.blk sT sS) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [GlobalTheory.RealWeil.blk_mul]
    simp only [fun w => (hS w).1, fun w => (hT w).1]
    exact GlobalTheory.RealWeil.blk_one
  · unfold HMF
    rw [GlobalTheory.RealWeil.blk_mul]
    refine GlobalTheory.RealWeil.blk_posDef (fun w => (hT w).2.2) fun w => ?_
    rw [← GlobalTheory.RealSymplForm.cartan_inv_mul (hS w)]
    exact (hS w).2.2.inv
  · intro k t hk
    rw [mMF_apply]
    refine GenA.blk_comm (fun w => ?_) (fun w => ?_)
    · rw [compAt_rat C hk]
      have e : (t • (1 : Matrix (Fin nT) (Fin nT) E)).map (tauB B w) = tauB B w t • 1 := by
        ext i j
        by_cases hij : i = j <;> simp [hij]
      rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
    · rw [inv_one, compAt_one, Matrix.one_mul, Matrix.mul_one]

end GenR

theorem rat_gen (C : Ctx σ B JS JT ξ₀ θ ι) (Q : GAF σ JS × GAF σ JT → Prop)
    (hm : ∀ p q, p.1 ∈ GQF σ JS → p.2 ∈ GQF σ JT → q.1 ∈ GQF σ JS → q.2 ∈ GQF σ JT → Q p → Q q → Q (p * q))
    (hs : ∀ p s, p.1 ∈ GQF σ JS → p.2 ∈ GQF σ JT → CartF σ JS JT ξ₀ B θ s →
      s * mMF σ JS JT θ p = mMF σ JS JT θ p * s → Q p) :
    ∀ p, p.1 ∈ GQF σ JS → p.2 ∈ GQF σ JT → Q p := by
  have hcm := C.good.cm
  have hσ := GlobalTheory.SplitDetCharF.sig_invol hcm
  obtain ⟨c, hc⟩ : ∃ c : E ≃ₐ[F] E, (c : E →ₐ[F] E) = σ :=
    ⟨AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ), rfl⟩
  subst hc
  have hr : ∀ w, (2 * (tauB B w ξ₀).im : ℝ) ≠ 0 := fun w => mul_ne_zero two_ne_zero (GenA.im_ne hcm C.h0 C.hξ _)
  have hcS : ∀ w, ∃ s, Formalism.IndefR.Datum.IsCartanInv (JS.map (tauB B w)) s := fun w => by
    simpa using GenA.cart_exists _ (GenA.herm_map hcm C.hS (tauB B w)) (GenA.det_map_ne C.hS (tauB B w)) 1 one_ne_zero
  have hcT : ∀ w, ∃ s, Formalism.IndefR.Datum.IsCartanInv (((2 * (tauB B w ξ₀).im : ℝ) : ℂ) • JT.map (tauB B w)) s :=
    fun w => GenA.cart_exists _ (GenA.herm_map hcm C.hT (tauB B w)) (GenA.det_map_ne C.hT (tauB B w)) _ (hr w)
  choose sS0 hS0 using hcS
  choose sT0 hT0 using hcT
  have Q11 : Q (1, 1) := hs (1, 1) (GlobalTheory.RealWeil.blk sT0 sS0) (one_mem _) (one_mem _) (GenR.cart_blk C hS0 hT0)
    (by
      show _ * mMF _ JS JT θ 1 = mMF _ JS JT θ 1 * _
      rw [map_one, Matrix.mul_one, Matrix.one_mul])
  have hT : ∀ h ∈ GQF (c : E →ₐ[F] E) JT, Q (1, h) := by
    refine GenR.rat_ind c hcm C.hT (fun h => Q (1, h)) Q11 (fun g hg g' hg' a b => ?_) (fun g x u hx hg => ?_)
    · have := hm (1, g) (1, g') (one_mem _) hg (one_mem _) hg' a b
      rwa [Prod.mk_mul_mk, mul_one] at this
    · have := fun w => GenA.cart_refl (JT.map (tauB B w)) (GenA.herm_map hcm C.hT (tauB B w))
        (GenA.det_map_ne C.hT (tauB B w)) _ (hr w) (tauB B w ∘ x)
        (by rw [GenA.quad_map hcm c rfl]; exact (map_ne_zero _).2 hx) (tauB B w ((u - 1) / GlobalTheory.UnRep.hermE c JTᵀ x x))
      choose sT hT1 hT2 using this
      refine hs (1, g) (GlobalTheory.RealWeil.blk sT sS0) (one_mem _) hg.mem (GenR.cart_blk C hS0 hT1) ?_
      rw [mMF_apply]
      refine GenA.blk_comm (fun w => ?_) (fun w => ?_)
      · rw [GenR.compAt_rat C hg, GenA.refl_map hcm c rfl]
        exact hT2 w
      · rw [inv_one, GenR.compAt_one, Matrix.one_mul, Matrix.mul_one]
  have hS : ∀ g ∈ GQF (c : E →ₐ[F] E) JS, Q (g⁻¹, 1) := by
    refine GenR.rat_ind c hcm C.hS (fun g => Q (g⁻¹, 1)) (by rw [inv_one]; exact Q11) (fun g hg g' hg' a b => ?_)
      (fun g x u hx hg => ?_)
    · have := hm (g'⁻¹, 1) (g⁻¹, 1) (inv_mem hg') (one_mem _) (inv_mem hg) (one_mem _) b a
      rwa [Prod.mk_mul_mk, mul_one, ← _root_.mul_inv_rev] at this
    · have := fun w => GenA.cart_refl (JS.map (tauB B w)) (GenA.herm_map hcm C.hS (tauB B w))
        (GenA.det_map_ne C.hS (tauB B w)) 1 one_ne_zero (tauB B w ∘ x)
        (by rw [GenA.quad_map hcm c rfl]; exact (map_ne_zero _).2 hx) (tauB B w ((u - 1) / GlobalTheory.UnRep.hermE c JSᵀ x x))
      choose sS hS1 hS2 using this
      have hS1' : ∀ w, Formalism.IndefR.Datum.IsCartanInv (JS.map (tauB B w)) (sS w) := fun w => by simpa using hS1 w
      refine hs (g⁻¹, 1) (GlobalTheory.RealWeil.blk sT0 sS) (inv_mem hg.mem) (one_mem _) (GenR.cart_blk C hS1' hT0) ?_
      rw [mMF_apply, inv_inv]
      refine GenA.blk_comm (fun w => ?_) (fun w => ?_)
      · rw [GenR.compAt_one, Matrix.one_mul, Matrix.mul_one]
      · rw [GenR.compAt_rat C hg, GenA.refl_map hcm c rfl]
        exact (hS2 w).symm
  intro p h1 h2
  have e : p = (p.1, 1) * (1, p.2) := by
    rw [Prod.mk_mul_mk, mul_one, one_mul]
  have a1 : Q (p.1, 1) := by
    have := hS _ (inv_mem h1)
    rwa [inv_inv] at this
  rw [e]
  exact hm _ _ h1 (one_mem _) (one_mem _) h2 a1 (hT _ h2)

end PositivityTheory.ThKW

end
