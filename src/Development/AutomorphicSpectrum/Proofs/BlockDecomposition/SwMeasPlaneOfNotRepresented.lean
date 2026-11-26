module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.NDDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityUnitLattice
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonrepresentedSignatureObstruction
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureAddBlockAnisotropic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureAddRankOneBlock

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SwMeasPlaneOfNotRepresented
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Plane

open Matrix GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Hasse

theorem det_eq_of_sig {A D : Matrix (Fin 2) (Fin 2) ℂ} {p q : ℕ} (hA : Formalism.UG.HasSignature A p q)
    (hD : Formalism.UG.HasSignature D p q) : ∃ r : ℝ, 0 < r ∧ D.det = r * A.det := by
  obtain ⟨Q, hQ, e⟩ := GlobalTheory.HermAdelicNorm.congr_of_hasSignature hA hD
  refine ⟨Complex.normSq Q.det, Complex.normSq_pos.2 hQ, ?_⟩
  have h1 : (Q.map (starRingEnd ℂ)).det = starRingEnd ℂ Q.det := (RingHom.map_det (starRingEnd ℂ) Q).symm
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h1, Complex.normSq_eq_conj_mul_self]
  ring

theorem sign_det {A : Matrix (Fin 2) (Fin 2) ℂ} {p q : ℕ} (h : Formalism.UG.HasSignature A p q) {δ : ℝ}
    (hdet : A.det = δ) (s : Fin 2 → ℝ)
    (hs : Formalism.UG.HasSignature (Matrix.diagonal fun i => (s i : ℂ)) p q) (hpos : 0 < s 0 * s 1) : 0 < δ := by
  obtain ⟨r, hr, e⟩ := det_eq_of_sig h hs
  rw [Matrix.det_diagonal, Fin.prod_univ_two, hdet] at e
  have e' : s 0 * s 1 = r * δ := by exact_mod_cast e
  rw [e'] at hpos
  exact (pos_iff_pos_of_mul_pos hpos).1 hr

theorem neg_det {A : Matrix (Fin 2) (Fin 2) ℂ} {p q : ℕ} (h : Formalism.UG.HasSignature A p q) {δ : ℝ}
    (hdet : A.det = δ) (s : Fin 2 → ℝ)
    (hs : Formalism.UG.HasSignature (Matrix.diagonal fun i => (s i : ℂ)) p q) (hneg : s 0 * s 1 < 0) : δ < 0 := by
  obtain ⟨r, hr, e⟩ := det_eq_of_sig h hs
  rw [Matrix.det_diagonal, Fin.prod_univ_two, hdet] at e
  have e' : s 0 * s 1 = r * δ := by exact_mod_cast e
  rw [e'] at hneg
  by_contra hc
  exact absurd hneg (not_lt.2 (mul_nonneg hr.le (not_lt.1 hc)))

theorem plane_sig {A : Matrix (Fin 2) (Fin 2) ℂ} {p q : ℕ} (h : Formalism.UG.HasSignature A p q) {c δ : ℝ}
    (hdet : A.det = δ) (hc : c ≠ 0) (h1 : p = 2 → 0 < c) (h2 : q = 2 → c < 0) :
    Formalism.UG.HasSignature (Matrix.diagonal fun i => ((![c, c * δ] i : ℝ) : ℂ)) p q := by
  have hpq : p + q = 2 := by simpa using (Formalism.UG.P.sig_data _ _ _ h).1.symm
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (p = 2 ∧ q = 0) ∨ (p = 1 ∧ q = 1) ∨ (p = 0 ∧ q = 2) := by omega
  · have hd : 0 < δ := sign_det h hdet ![1, 1]
      (hasSignature_diagonal _ rfl (fun i => by fin_cases i <;> simp)) (by simp)
    have hc' := h1 rfl
    exact hasSignature_diagonal _ rfl (fun i => by
      fin_cases i
      · simpa using hc'
      · simpa using mul_pos hc' hd)
  · have hd : δ < 0 := neg_det h hdet ![1, -1]
      (hasSignature_diagonal _ rfl (fun i => by fin_cases i <;> simp)) (by simp)
    rcases lt_or_gt_of_ne hc with hneg | hpos
    · have := hasSignature_diagonal (P := 1) (N := 1) ![-c, -(c * δ)] rfl (fun i => by
        fin_cases i
        · simpa using hneg
        · simpa using mul_pos_of_neg_of_neg hneg hd)
      have := hasSig_neg this
      convert this using 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · exact hasSignature_diagonal _ rfl (fun i => by
        fin_cases i
        · simpa using hpos
        · simpa using mul_neg_of_pos_of_neg hpos hd)
  · have hd : 0 < δ := sign_det h hdet ![-1, -1]
      (hasSignature_diagonal _ rfl (fun i => by fin_cases i <;> simp)) (by simp)
    have hc' := h2 rfl
    exact hasSignature_diagonal _ rfl (fun i => by
      fin_cases i
      · simpa using hc'
      · simpa using mul_neg_of_neg_of_pos hc' hd)

theorem quad_nonneg {A : Matrix (Fin 2) (Fin 2) ℂ} (h : Formalism.UG.HasSignature A 2 0) (w : Fin 2 → ℂ) :
    0 ≤ (star w ⬝ᵥ (A *ᵥ w)).re := by
  have hD : Formalism.UG.HasSignature (Matrix.diagonal fun _ : Fin 2 => ((1 : ℝ) : ℂ)) 2 0 :=
    hasSignature_diagonal _ rfl (fun i => by fin_cases i <;> simp)
  obtain ⟨Q, -, e⟩ := GlobalTheory.HermAdelicNorm.congr_of_hasSignature hD h
  have hone : (Matrix.diagonal fun _ : Fin 2 => ((1 : ℝ) : ℂ)) = 1 := by
    simp
  rw [hone, Matrix.mul_one] at e
  have key : star w ⬝ᵥ (A *ᵥ w) = star ((Q.map (starRingEnd ℂ)) *ᵥ w) ⬝ᵥ ((Q.map (starRingEnd ℂ)) *ᵥ w) := by
    rw [e, ← Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec]
    congr 2
    ext i j
    simp [Matrix.conjTranspose_apply]
  rw [key, dotProduct, Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  have hc : ∀ z : ℂ, star z * z = ((Complex.normSq z : ℝ) : ℂ) := fun z => by
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  simp only [Pi.star_apply]
  rw [hc, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

end GlobalTheory.CompanionTheory.SW.Plane

namespace GlobalTheory.CompanionTheory.SW.Plane

open Matrix GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Hasse

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem real_of_fixed {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) (τ : E →+* ℂ) {x : E} (hx : σ x = x) :
    τ x = (((τ x).re : ℝ) : ℂ) := by
  have h := hCM.2.2.2 τ x
  rw [hx] at h
  exact (Complex.conj_eq_iff_real.1 h.symm).choose_spec ▸ by simp

theorem det_fixed {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) :
    σ J.det = J.det := by
  have h1 : (J.map (σ : E →+* E)) = Jᵀ := by
    ext i j
    exact hJ.1 j i
  have h2 : (σ : E →+* E) J.det = (J.map (σ : E →+* E)).det := RingHom.map_det _ _
  rw [h1, Matrix.det_transpose] at h2
  exact h2

theorem exists_place {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) (J : Matrix (Fin 2) (Fin 2) E)
    (hJ : IsHermND σ J) (t : F) (ht : t ≠ 0) (hne : ∀ x : Fin 2 → E, hE σ J x x ≠ algebraMap F E t) :
    ∃ (τ : E →+* ℂ) (c : ℝ), c ≠ 0 ∧ τ (algebraMap F E t) = c ∧
      ∀ w : Fin 2 → ℂ, c * (star w ⬝ᵥ (J.map τ *ᵥ w)).re ≤ 0 := by
  by_contra hcon
  push_neg at hcon
  haveI : IsTotallyReal F := hCM.1
  haveI : IsTotallyComplex E := hCM.2.1
  haveI : Algebra.IsQuadraticExtension F E := ⟨hCM.2.2.1⟩
  haveI : IsCMField E := IsCMField.ofCMExtension F E
  have hcc : ∀ x : E, ReciprocityTheory.ChartRestriction.G.FD.cc x = σ x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective ((GlobalTheory.Published.embedding_cc τ x).trans (hCM.2.2.2 τ x).symm)
  set a : E := algebraMap F E t with ha
  set D : E := J.det with hD
  have hσa : σ a = a := σ.commutes t
  have hσD : σ D = D := det_fixed hJ
  have ha0 : a ≠ 0 := (map_ne_zero _).2 ht
  have hD0 : D ≠ 0 := hJ.2
  let G' : Matrix (Fin 2) (Fin 2) E := Matrix.diagonal ![a, a * D]
  have hG'd : G'.det = a * (a * D) := by
    simp [G', Matrix.det_diagonal, Fin.prod_univ_two]
  have hG'c : ∀ i j, ReciprocityTheory.ChartRestriction.G.FD.cc (G' i j) = G' j i := fun i j => by
    rw [hcc]
    fin_cases i <;> fin_cases j <;> simp [G', hσa, hσD]
  have hsig : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin 2) (Fin 2) ℂ, Q.det ≠ 0 ∧
      G'.map τ = Qᵀ * J.map τ * Q.map (starRingEnd ℂ) := fun τ => by
    have hc := real_of_fixed hCM τ hσa
    have hδ := real_of_fixed hCM τ hσD
    set c : ℝ := (τ a).re with hcdef
    set δ : ℝ := (τ D).re with hδdef
    have hc0 : c ≠ 0 := fun h => by
      rw [h] at hc
      exact ha0 (τ.injective (by simpa using hc))
    have hH : Formalism.UG.IsHerm (starRingEnd ℂ) (J.map τ) := by
      unfold Formalism.UG.IsHerm
      rw [Formalism.UG.P.cT_conj_eq]
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
      rw [← hJ.1 i j, hCM.2.2.2 τ]
    obtain ⟨p, q, hs⟩ := Formalism.UG.P.signature_exists _ (J.map τ) hH (map_isUnit_det J hJ.2 τ)
    have hdet : (J.map τ).det = δ := by
      rw [← hδ]
      exact (RingHom.map_det τ J).symm
    have hpq : p + q = 2 := by simpa using (Formalism.UG.P.sig_data _ _ _ hs).1.symm
    have h1 : p = 2 → 0 < c := fun hp => by
      have hq : q = 0 := by omega
      subst hp hq
      by_contra hneg
      have hneg' : c < 0 := lt_of_le_of_ne (not_lt.1 hneg) hc0
      obtain ⟨w, hw⟩ := hcon τ c hc0 hc
      exact absurd hw (not_lt.2 (mul_nonpos_of_nonpos_of_nonneg hneg'.le (quad_nonneg hs w)))
    have h2 : q = 2 → c < 0 := fun hq => by
      have hp : p = 0 := by omega
      subst hp hq
      by_contra hpos
      have hpos' : 0 < c := lt_of_le_of_ne (not_lt.1 hpos) hc0.symm
      obtain ⟨w, hw⟩ := hcon τ c hc0 hc
      have h3 := quad_nonneg (hasSig_neg hs) w
      have h4 : ((star w ⬝ᵥ ((-(J.map τ)) *ᵥ w))).re = -(star w ⬝ᵥ (J.map τ *ᵥ w)).re := by
        simp only [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re]
      rw [h4] at h3
      nlinarith
    obtain ⟨Q, hQ, e⟩ := GlobalTheory.HermAdelicNorm.congr_of_hasSignature hs (plane_sig hs hdet hc0 h1 h2)
    refine ⟨Q, hQ, ?_⟩
    rw [← e]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [G', Matrix.diagonal_apply, ← hc, ← hδ]
  obtain ⟨P, -, hP⟩ := GlobalTheory.QNorm.landherr_and_landherrSt.1 E 2 J G'
    (fun i j => by rw [hcc]; exact hJ.1 j i) hG'c hJ.2
    (by rw [hG'd]; exact mul_ne_zero ha0 (mul_ne_zero ha0 hD0)) hsig
    ⟨a⁻¹, by
      rw [hcc, hG'd, map_inv₀, hσa]
      field_simp
      rfl⟩
  refine hne (fun i => σ (P i 0)) ?_
  have e := congrFun (congrFun hP 0) 0
  have hσσ : ∀ x : E, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hCM.2.2.2, hCM.2.2.2]; simp)
  simp only [G', Matrix.diagonal_apply_eq, Matrix.cons_val_zero] at e
  rw [e]
  simp only [hE, hform, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hcc, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [hσσ]

theorem exists_hom {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) (τ : E →+* ℂ) :
    ∃ Φ : Ainf F ⊗[F] E →+* ℂ, (∀ e, Φ (inclR (Ainf F) e) = τ e) ∧
      ∀ y, Φ (sigR (Ainf F) σ y) = star (Φ y) := by
  haveI : IsTotallyReal F := hCM.1
  let φ : F →+* ℂ := τ.comp (algebraMap F E)
  let v : InfinitePlace F := InfinitePlace.mk φ
  have hv : v.IsReal := IsTotallyReal.isReal v
  have hφ : ComplexEmbedding.IsReal φ := InfinitePlace.isReal_mk_iff.1 hv
  let ψ : Ainf F →+* ℝ := (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv).comp
    (Pi.evalRingHom (fun w : InfinitePlace F => w.Completion) v)
  have hψ : ∀ x : F, ((ψ (algebraMap F (Ainf F) x) : ℝ) : ℂ) = φ x := fun x => by
    have h1 : ψ (algebraMap F (Ainf F) x) = InfinitePlace.embedding_of_isReal hv x := by
      change InfinitePlace.Completion.extensionEmbeddingOfIsReal hv (algebraMap F v.Completion x) = _
      rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
        Algebra.algebraMap_self_apply]
      simpa using InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hv (WithAbs.toAbs v.1 x)
    rw [h1, InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_mk_eq_of_isReal hφ]
  letI : Algebra F ℂ := φ.toAlgebra
  let f : Ainf F →ₐ[F] ℂ := { Complex.ofRealHom.comp ψ with commutes' := hψ }
  let g : E →ₐ[F] ℂ := { τ with commutes' := fun _ => rfl }
  refine ⟨(Algebra.TensorProduct.productMap f g).toRingHom, fun e => ?_, fun y => ?_⟩
  · simp [inclR, f, g]
  · induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      simp [sigR, f, g, hCM.2.2.2 τ]
    | add x y hx hy => simp only [map_add (f := _), star_add, hx, hy]

end GlobalTheory.CompanionTheory.SW.Plane

namespace GlobalTheory.CompanionTheory.SW

end GlobalTheory.CompanionTheory.SW
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryMovingUnitVector
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryMovingUnitVector
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypUnit

section Form

variable {K : Type} [CommRing K] {M : ℕ}

theorem fin_three {P : Fin (M + 2) → Prop} (h0 : P 0) (h1 : P 1) (h2 : ∀ i : Fin M, P i.succ.succ)
    (i : Fin (M + 2)) : P i :=
  Fin.cases h0 (fun i => Fin.cases h1 (fun i => h2 i) i) i

theorem sum_three (f : Fin (M + 2) → K) : ∑ i, f i = f 0 + f 1 + ∑ i : Fin M, f i.succ.succ := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  exact (add_assoc _ _ _).symm

variable (s : K →+* K) (A : Matrix (Fin M) (Fin M) K)

theorem hform_hypOne (x y : Fin (M + 2) → K) :
    hform s (hypOne A) x y = s (x 0) * y 1 + s (x 1) * y 0 + hform s A (tailH x) (tailH y) := by
  simp only [hform, sum_three, hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one,
    hypOne_zero_rest, hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one, hypOne_rest_rest, tailH]
  simp

theorem hform_add_right (x y y' : Fin M → K) :
    hform s A x (y + y') = hform s A x y + hform s A x y' := by
  simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_add_left (x x' y : Fin M → K) :
    hform s A (x + x') y = hform s A x y + hform s A x' y := by
  simp only [hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hform_smul_right (c : K) (x y : Fin M → K) :
    hform s A x (c • y) = c * hform s A x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_smul_left (c : K) (x y : Fin M → K) :
    hform s A (c • x) y = s c * hform s A x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_conj (hs : ∀ e, s (s e) = e) (hA : ∀ i j, s (A j i) = A i j) (x y : Fin M → K) :
    s (hform s A x y) = hform s A y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hform, map_sum, map_mul, hs]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hA]; ring

def cvK (c : K) (x v : Fin (M + 2) → K) : Fin (M + 2) → K :=
  vH (x 0 * v 0)
    (v 0 * x 1 + Ring.inverse (s (x 0)) * (v 1 - c * v 0 - hform s A (tailH x) (tailH v)))
    (fun i => v 0 * x i.succ.succ + v i.succ.succ)

def cvL (c : K) (x : Fin (M + 2) → K) : (Fin (M + 2) → K) →ₗ[K] (Fin (M + 2) → K) where
  toFun := cvK s A c x
  map_add' u v := by
    have ht : tailH (u + v) = tailH u + tailH v := rfl
    funext i
    refine fin_three (P := fun i => cvK s A c x (u + v) i = (cvK s A c x u + cvK s A c x v) i) ?_ ?_ ?_ i
    · show x 0 * (u 0 + v 0) = x 0 * u 0 + x 0 * v 0
      ring
    · show (u 0 + v 0) * x 1 + Ring.inverse (s (x 0)) *
          (u 1 + v 1 - c * (u 0 + v 0) - hform s A (tailH x) (tailH (u + v))) =
        (u 0 * x 1 + Ring.inverse (s (x 0)) * (u 1 - c * u 0 - hform s A (tailH x) (tailH u))) +
        (v 0 * x 1 + Ring.inverse (s (x 0)) * (v 1 - c * v 0 - hform s A (tailH x) (tailH v)))
      rw [ht, hform_add_right]
      ring
    · intro i
      show (u 0 + v 0) * x i.succ.succ + (u i.succ.succ + v i.succ.succ) =
        (u 0 * x i.succ.succ + u i.succ.succ) + (v 0 * x i.succ.succ + v i.succ.succ)
      ring
  map_smul' e v := by
    have ht : tailH (e • v) = e • tailH v := rfl
    funext i
    refine fin_three (P := fun i => cvK s A c x (e • v) i = (e • cvK s A c x v) i) ?_ ?_ ?_ i
    · show x 0 * (e * v 0) = e * (x 0 * v 0)
      ring
    · show (e * v 0) * x 1 + Ring.inverse (s (x 0)) *
          (e * v 1 - c * (e * v 0) - hform s A (tailH x) (tailH (e • v))) =
        e * (v 0 * x 1 + Ring.inverse (s (x 0)) * (v 1 - c * v 0 - hform s A (tailH x) (tailH v)))
      rw [ht, hform_smul_right]
      ring
    · intro i
      show (e * v 0) * x i.succ.succ + e * v i.succ.succ = e * (v 0 * x i.succ.succ + v i.succ.succ)
      ring

theorem hform_cvK (hs : ∀ e, s (s e) = e) (hA : ∀ i j, s (A j i) = A i j) (c : K)
    (x : Fin (M + 2) → K) (hx : IsUnit (x 0)) (hc : c + s c = hform s (hypOne A) x x)
    (u v : Fin (M + 2) → K) :
    hform s (hypOne A) (cvK s A c x u) (cvK s A c x v) = hform s (hypOne A) u v := by
  have hsa : IsUnit (s (x 0)) := hx.map s
  have hab : s (x 0) * Ring.inverse (s (x 0)) = 1 := Ring.mul_inverse_cancel _ hsa
  have hba : s (Ring.inverse (s (x 0))) * x 0 = 1 := by
    have := congrArg s hab
    rwa [map_mul, hs, map_one, mul_comm] at this
  have htail : ∀ w : Fin (M + 2) → K, tailH (cvK s A c x w) = w 0 • tailH x + tailH w := fun _ => rfl
  rw [hform_hypOne, hform_hypOne s A u v, htail, htail, hform_add_left, hform_add_right,
    hform_add_right, hform_smul_left, hform_smul_left, hform_smul_right, hform_smul_right]
  rw [hform_hypOne] at hc
  have hconj := hform_conj s A hs hA (tailH x) (tailH u)
  have e0 : ∀ w : Fin (M + 2) → K, cvK s A c x w 0 = x 0 * w 0 := fun _ => rfl
  have e1 : ∀ w : Fin (M + 2) → K, cvK s A c x w 1 = w 0 * x 1 + Ring.inverse (s (x 0)) *
      (w 1 - c * w 0 - hform s A (tailH x) (tailH w)) := fun _ => rfl
  rw [e0, e0, e1, e1]
  simp only [map_add (f := _), map_sub, map_mul, hconj]
  linear_combination (s (u 0) * (v 1 - c * v 0 - hform s A (tailH x) (tailH v))) * hab +
    (v 0 * (s (u 1) - s c * s (u 0) - hform s A (tailH u) (tailH x))) * hba -
    (s (u 0) * v 0) * hc

theorem cvK_surjective (c : K) (x : Fin (M + 2) → K) (hx : IsUnit (x 0)) (hs : IsUnit (s (x 0))) :
    Function.Surjective (cvK s A c x) := by
  intro w
  have ha : x 0 * Ring.inverse (x 0) = 1 := Ring.mul_inverse_cancel _ hx
  have hb : Ring.inverse (s (x 0)) * s (x 0) = 1 := Ring.inverse_mul_cancel _ hs
  set α := Ring.inverse (x 0) * w 0 with hα
  set U : Fin M → K := fun i => w i.succ.succ - α * x i.succ.succ with hU
  refine ⟨vH α (s (x 0) * (w 1 - α * x 1) + c * α + hform s A (tailH x) U) U, ?_⟩
  funext i
  refine fin_three (P := fun i => cvK s A c x
    (vH α (s (x 0) * (w 1 - α * x 1) + c * α + hform s A (tailH x) U) U) i = w i) ?_ ?_ ?_ i
  · show x 0 * α = w 0
    rw [hα, ← mul_assoc, ha, one_mul]
  · show α * x 1 + Ring.inverse (s (x 0)) *
      (s (x 0) * (w 1 - α * x 1) + c * α + hform s A (tailH x) U - c * α - hform s A (tailH x) U) = w 1
    linear_combination (w 1 - α * x 1) * hb
  · intro i
    show α * x i.succ.succ + U i = w i.succ.succ
    rw [hU]
    ring

theorem cT_mul_apply (H C : Matrix (Fin M) (Fin M) K) (i j : Fin M) :
    (Formalism.UG.cT s C * H * C) i j = hform s H (fun k => C k i) (fun k => C k j) := by
  simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hform,
    Finset.sum_mul]
  exact Finset.sum_comm

theorem hform_single (H : Matrix (Fin M) (Fin M) K) (i j : Fin M) :
    hform s H (Pi.single i 1) (Pi.single j 1) = H i j := by
  simp [hform, Pi.single_apply, apply_ite s]

theorem exists_unitary (hs : ∀ e, s (s e) = e) (hA : ∀ i j, s (A j i) = A i j) (c : K)
    (x : Fin (M + 2) → K) (hx : IsUnit (x 0)) (hc : c + s c = hform s (hypOne A) x x) :
    ∃ g : GL (Fin (M + 2)) K, g ∈ Formalism.UG.UJ s (hypOne A) ∧
      ∀ v, (g : Matrix (Fin (M + 2)) (Fin (M + 2)) K).mulVec v = cvK s A c x v := by
  set C := LinearMap.toMatrix' (cvL s A c x) with hC
  have hmul : ∀ v, C.mulVec v = cvK s A c x v := fun v => by
    rw [hC, LinearMap.toMatrix'_mulVec]
    rfl
  have hunit : IsUnit C := by
    rw [← Matrix.mulVec_surjective_iff_isUnit]
    intro w
    obtain ⟨v, hv⟩ := cvK_surjective s A c x hx (hx.map s) w
    exact ⟨v, (hmul v).trans hv⟩
  obtain ⟨g, hg⟩ := hunit
  refine ⟨g, ?_, fun v => by rw [hg, hmul]⟩
  show Formalism.UG.cT s (g : Matrix (Fin (M + 2)) (Fin (M + 2)) K) * hypOne A * g = hypOne A
  rw [hg]
  ext i j
  rw [cT_mul_apply]
  have hcol : ∀ k, (fun l => C l k) = cvK s A c x (Pi.single k 1) := fun k => by
    rw [← hmul, Matrix.mulVec_single_one]
    rfl
  rw [hcol, hcol, hform_cvK s A hs hA c x hx hc, hform_single]

end Form

section Tensor

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem sigR_inclR_apply (σ : E →ₐ[F] E) (e : E) :
    sigR R σ (inclR (F := F) R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem JR_hypOne {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    JR R (hypOne J) = hypOne (JR (F := F) R J) := by
  ext i j
  refine fin_three (P := fun i => JR (F := F) R (hypOne J) i j = hypOne (JR (F := F) R J) i j) ?_ ?_ ?_ i
  · refine fin_three (P := fun j => JR (F := F) R (hypOne J) 0 j = hypOne (JR (F := F) R J) 0 j) ?_ ?_ ?_ j
    · simp [JR, hypOne_zero_zero]
    · simp [JR, hypOne_zero_one]
    · intro j; simp [JR, hypOne_zero_rest]
  · refine fin_three (P := fun j => JR (F := F) R (hypOne J) 1 j = hypOne (JR (F := F) R J) 1 j) ?_ ?_ ?_ j
    · simp [JR, hypOne_one_zero]
    · simp [JR, hypOne_one_one]
    · intro j; simp [JR, hypOne_one_rest]
  · intro i
    refine fin_three (P := fun j => JR (F := F) R (hypOne J) i.succ.succ j =
      hypOne (JR (F := F) R J) i.succ.succ j) ?_ ?_ ?_ j
    · simp [JR, hypOne_rest_zero]
    · simp [JR, hypOne_rest_one]
    · intro j; simp [JR, hypOne_rest_rest]

end Tensor

theorem cvec_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] (x : Fin (M + 2) → R ⊗[F] E), IsUnit (x 0) → ∃ g : HA R σ (hypOne J), ∀ v : Fin (M + 2) → R ⊗[F] E, ((HA.mat R σ (hypOne J) g : GL (Fin (M + 2)) (R ⊗[F] E)) : Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E)).mulVec v = cvec R σ J x v := by
  intro F E _ _ _ _ _ σ hcm M J hJ R _ _ x hx
  have hinv := sig_invol σ hcm
  have hs : ∀ e, sigR R σ (sigR R σ e) = e := sigR_sigR R σ hinv
  have hA : ∀ i j, sigR R σ (JR (F := F) R J j i) = JR (F := F) R J i j := fun i j => by
    show sigR R σ (inclR R (J j i)) = inclR R (J i j)
    rw [sigR_inclR_apply, hJ.1]
  have ht : hR R σ (hypOne J) x x = hform (sigR R σ) (hypOne (JR (F := F) R J)) x x := by
    rw [hR, JR_hypOne]
  have htc : sigR R σ (hR R σ (hypOne J) x x) = hR R σ (hypOne J) x x := by
    rw [ht, hform_hypOne]
    simp only [map_add (f := _), map_mul, hs, hform_conj (sigR R σ) (JR (F := F) R J) hs hA]
    ring
  have hhalf : sigR R σ (halfR (F := F) (E := E) R) = halfR (F := F) (E := E) R := by
    rw [halfR, sigR_inclR_apply, AlgHom.commutes]
  have h2 : halfR (F := F) (E := E) R + halfR (F := F) (E := E) R = 1 := by
    rw [halfR, ← map_add (f := _), ← map_add (f := _)]
    norm_num
  have hc : tHalf R σ J x + sigR R σ (tHalf R σ J x) =
      hform (sigR R σ) (hypOne (JR (F := F) R J)) x x := by
    rw [tHalf, map_mul, hhalf, htc, ← ht]
    linear_combination (hR R σ (hypOne J) x x) * h2
  obtain ⟨g, hg, hv⟩ := exists_unitary (sigR R σ) (JR (F := F) R J) hs hA (tHalf R σ J x) x hx hc
  refine ⟨⟨g, ?_⟩, hv⟩
  show g ∈ Formalism.UG.UJ (sigR R σ) (JR R (hypOne J))
  rw [JR_hypOne]
  exact hg

end GlobalTheory.CompanionTheory.WeilSiegel.HypUnit
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryMovingUnitVectorStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_moving_unit_vector : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] (x : Fin (M + 2) → R ⊗[F] E), IsUnit (x 0) → ∃ g : HA R σ (hypOne J), ∀ v : Fin (M + 2) → R ⊗[F] E, ((HA.mat R σ (hypOne J) g : GL (Fin (M + 2)) (R ⊗[F] E)) : Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E)).mulVec v = cvec R σ J x v := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypUnit.cvec_unitary | exact GlobalTheory.CompanionTheory.WeilSiegel.HypUnit.cvec_unitary | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypUnit.cvec_unitary <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicFramesUnitaryStable
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicFramesUnitaryStable
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.Basic

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage

theorem linearIndependent_mulVec_GL {E : Type} [Field E] {M n : ℕ} (A : GL (Fin M) E)
    {X : Fin n → Fin M → E} (hX : LinearIndependent E X) :
    LinearIndependent E (fun a => (A : Matrix (Fin M) (Fin M) E) *ᵥ X a) := by
  have hinj : Function.Injective (Matrix.mulVecLin (A : Matrix (Fin M) (Fin M) E)) := by
    intro x y hxy
    have h : ∀ v : Fin M → E, ((A⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ
        ((A : Matrix (Fin M) (Fin M) E) *ᵥ v) = v := by
      intro v
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    have hxy' : (A : Matrix (Fin M) (Fin M) E) *ᵥ x = (A : Matrix (Fin M) (Fin M) E) *ᵥ y := hxy
    rw [← h x, ← h y, hxy']
  exact hX.map' (Matrix.mulVecLin (A : Matrix (Fin M) (Fin M) E)) (LinearMap.ker_eq_bot.2 hinj)

theorem gact_mem_framesE {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M n : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (g : UJ (σ : E →+* E) J) {T : Matrix (Fin n) (Fin n) E}
    {q : Fin n → Fin M → E} (hq : q ∈ framesE σ J T) : gact σ g q ∈ framesE σ J T := by
  have h1 : LinearIndependent E (gact σ g q) := linearIndependent_mulVec_GL (g : GL (Fin M) E) hq.1
  have h2 : gramE σ J (gact σ g q) = T := by
    rw [gramE_gact]
    exact hq.2
  exact ⟨h1, h2⟩

theorem hypOne_basic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsHermND σ (hypOne J) ∧ e0 E M ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) ∧ ∀ (g : UJ (σ : E →+* E) (hypOne J)) (q : Fin 1 → Fin (M + 2) → E), q ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) → gact σ g q ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) := by
  intro F E _ _ _ _ _ σ _ M J hJ
  exact ⟨isHermND_hypOne σ hJ, e0_mem_framesE σ J, fun g q hq => gact_mem_framesE σ g hq⟩

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.Basic
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicFramesUnitaryStableStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_frames_unitary_stable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsHermND σ (hypOne J) ∧ e0 E M ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) ∧ ∀ (g : UJ (σ : E →+* E) (hypOne J)) (q : Fin 1 → Fin (M + 2) → E), q ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) → gact σ g q ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.Basic.hypOne_basic | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.Basic.hypOne_basic | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.Basic.hypOne_basic <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockOneStepConst
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StepC

theorem theta_hypothesis_c : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (c : ℝ≥0), IsEulerProd b I c minf m → ∃ S₂ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₂ ⊆ S → ∀ (φinf : (Fin (n + 1) → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞) (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) (Ψinf : (Fin 1 → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞) (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable φinf → (∀ v, Measurable (φ v)) → (∀ g : HA (Ainf F) σ (blockOne (algebraMap F E t) J), Ψinf (actW (Ainf F) σ _ g (fun _ => Fin.cons 1 (fun _ => 0))) = ∫⁻ X, φinf (actW (Ainf F) σ _ g (consTup X)) ∂minf) → (∀ v, ∀ g : HA (Fv F v) σ (blockOne (algebraMap F E t) J), Ψ v (actW (Fv F v) σ _ g (fun _ => Fin.cons 1 (fun _ => 0))) = ∫⁻ X, φ v (actW (Fv F v) σ _ g (consTup X)) ∂(m v)) → (∀ v, v ∉ S → ∀ g : HA (Fv F v) σ (blockOne (algebraMap F E t) J), m v {X | actW (Fv F v) σ _ g (consTup X) ∈ latV b v} = (latV b v).indicator (fun _ => m v (latV b v)) (actW (Fv F v) σ _ g (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)))) → ∀ h : HA (AF F) σ (blockOne (algebraMap F E t) J), (c : ℝ≥0∞) * ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal) * pureL b S Ψinf Ψ (actW (AF F) σ _ h (fun _ => Fin.cons 1 (fun _ => 0))) = ∫⁻ X, pureL b S φinf φ (actW (AF F) σ _ h (consTup X)) ∂I := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n d b I minf m c hE
  classical
  have hLi : IsLocR (Ainf F) := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1
  have hLv : ∀ v, IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F
  haveI hBi : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI hBv : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  obtain ⟨hfin, hsum, S₀, hS₀⟩ := hE
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.adelic_unitary_finite_set_decomposition F E σ hCM M J hJ t ht d b
  refine ⟨S₀ ∪ S₁, fun S hS φinf φ Ψinf Ψ hφinf hφ hΨinf hΨ hG h => ?_⟩
  have hS0 : S₀ ⊆ S := fun x hx => hS (by simp [hx])
  have hS1 : S₁ ⊆ S := fun x hx => hS (by simp [hx])
  obtain ⟨ginf, g, Sh, hh⟩ := hS₁ h
  obtain ⟨hi, hii⟩ := hh S hS1
  have hmi : Measurable fun Y : Fin n → Fin M → Ainf F ⊗[F] E =>
      actW (Ainf F) σ _ ginf (consTup Y) := GlobalTheory.T.unitary_action_cons_tuple_measurable F E σ hCM (Ainf F) hLi n M _ ginf
  have hmv : ∀ v, Measurable fun Y : Fin n → Fin M → Fv F v ⊗[F] E =>
      actW (Fv F v) σ _ (g v) (consTup Y) := fun v => GlobalTheory.T.unitary_action_cons_tuple_measurable F E σ hCM (Fv F v) (hLv v) n M _ (g v)
  have hlatm : ∀ v, MeasurableSet (latV b v : Set (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E)) := fun v => GlobalTheory.CompanionTheory.SW.Step.lattice_measurable σ hCM b (n + 1) (M + 1) v
  simp_rw [hi]
  have hmψ : ∀ v, Measurable (fun Y : Fin n → Fin M → Fv F v ⊗[F] E => if v ∈ S then φ v (actW (Fv F v) σ _ (g v) (consTup Y)) else (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (consTup Y))) := fun v => by
    by_cases hv : v ∈ S
    · simp only [hv, if_true]; exact (hφ v).comp (hmv v)
    · simp only [hv, if_false]; exact (measurable_one.indicator (hlatm v)).comp (hmv v)
  have hsplit : ∏ v ∈ S ∪ Sh, ∫⁻ X, (if v ∈ S then φ v (actW (Fv F v) σ _ (g v) (consTup X)) else (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (consTup X))) ∂(m v) =
      (∏ v ∈ S, Ψ v (actW (Fv F v) σ _ (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)))) *
        ((∏ v ∈ Sh \ S, (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)))) * ∏ v ∈ Sh \ S, m v (latV b v)) := by
    rw [Finset.union_comm, ← Finset.sdiff_union_self_eq_union, Finset.prod_union Finset.sdiff_disjoint, mul_comm, ← Finset.prod_mul_distrib]
    congr 1
    · refine Finset.prod_congr rfl fun v hv => ?_
      simp only [hv, if_true]; exact (hΨ v (g v)).symm
    · refine Finset.prod_congr rfl fun v hv => ?_
      have hvS : v ∉ S := (Finset.mem_sdiff.1 hv).2
      simp only [hvS, if_false]
      have e1 : ∫⁻ X, (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (consTup X)) ∂(m v) =
          m v {X | actW (Fv F v) σ _ (g v) (consTup X) ∈ latV b v} := by
        have : (fun X : Fin n → Fin M → Fv F v ⊗[F] E => (latV b v).indicator (1 : (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) (actW (Fv F v) σ _ (g v) (consTup X))) =
            {X | actW (Fv F v) σ _ (g v) (consTup X) ∈ latV b v}.indicator 1 := by
          funext X; simp [Set.indicator]
        rw [this]; exact lintegral_indicator_one ((hmv v) (hlatm v))
      rw [e1, hG v hvS (g v)]
      simp [Set.indicator]
  have hmφ : Measurable (fun Y : Fin n → Fin M → Ainf F ⊗[F] E => φinf (actW (Ainf F) σ _ ginf (consTup Y))) := hφinf.comp hmi
  have htail := GlobalTheory.T.tprod_complement_split_finset (HeightOneSpectrum (𝓞 F)) (fun v => (m v (latV b v)).toReal) S (S ∪ Sh) hsum Finset.subset_union_left
  rw [Finset.union_sdiff_left] at htail
  have hτ : ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal) = (∏ v ∈ Sh \ S, m v (latV b v)) *
      ENNReal.ofReal (∏' v : {v // v ∉ S ∪ Sh}, (m v.1 (latV b v.1)).toReal) := by
    rw [htail, ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg),
      ENNReal.ofReal_prod_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
    congr 1
    exact Finset.prod_congr rfl fun v _ => ENNReal.ofReal_toReal (hfin v).ne
  rw [hS₀ (S ∪ Sh) (hS0.trans Finset.subset_union_left) _ _ hmφ hmψ, hii, hsplit, hτ, hΨinf ginf]
  ring

end GlobalTheory.CompanionTheory.SW.StepC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtensionByZeroOrbitFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtensionByZeroOrbitFormula
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem map_cols0 {R S : Type*} [Zero R] [Zero S] {a r t n : ℕ} (f : R → S) (hf : f 0 = 0)
    (e : Fin n ≃ Fin r ⊕ Fin t) (x : Matrix (Fin a) (Fin r) R) :
    ((Matrix.fromCols x (0 : Matrix (Fin a) (Fin t) R)).submatrix id e).map f =
      (Matrix.fromCols (x.map f) (0 : Matrix (Fin a) (Fin t) S)).submatrix id e := by
  ext i j
  simp only [Matrix.map_apply, Matrix.submatrix_apply, id]
  rcases e j with k | k
  · simp
  · simp [hf]

theorem mul_cols0 {R : Type*} [NonUnitalNonAssocSemiring R] {a b r t n : ℕ}
    (e : Fin n ≃ Fin r ⊕ Fin t) (A : Matrix (Fin a) (Fin b) R) (x : Matrix (Fin b) (Fin r) R) :
    A * (Matrix.fromCols x (0 : Matrix (Fin b) (Fin t) R)).submatrix id e =
      (Matrix.fromCols (A * x) (0 : Matrix (Fin a) (Fin t) R)).submatrix id e := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
  rcases e j with k | k
  · simp [Matrix.mul_apply]
  · simp

theorem extension_by_zero_orbit_action : Ext0 := by
  intro D n t W hn x₀ h
  have h1 : (rat (L.ext0 hn x₀) : Matrix (Fin W.rank) (Fin n) (AE D)) =
      (Matrix.fromCols (rat x₀ : Matrix (Fin W.rank) (Fin W.rank) (AE D))
        (0 : Matrix (Fin W.rank) (Fin t) (AE D))).submatrix id (finSumFinEquiv.trans (finCongr hn)).symm :=
    map_cols0 (incA D) (map_zero _) _ x₀
  have h2 := mul_cols0 (t := t) (finSumFinEquiv.trans (finCongr hn)).symm (mt W h⁻¹)
    (rat x₀ : Matrix (Fin W.rank) (Fin W.rank) (AE D))
  exact (congrArg (fun M => mt W h⁻¹ * M) h1).trans h2

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtensionByZeroOrbitFormulaStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extension_by_zero_orbit_formula : Ext0 := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.extension_by_zero_orbit_action | exact GlobalTheory.CompanionTheory.ColumnSplitting.extension_by_zero_orbit_action | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.extension_by_zero_orbit_action <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureTranslationInvariant
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureTranslationInvariant
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem nuT_shear_invariant : ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n)
    (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ x₀ (y : Mx D W.rank t),
    (nuT hn I μ x₀).map (fun z => (z.1, z.2 + mm z.1 y)) = nuT hn I μ x₀ := by
  intro D n t B W d hn I μ hμ x₀ y
  have hring := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨i1, i2, i3, i4, i5⟩ := top_mx (D := D) W.rank t
  obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) t n
  obtain ⟨k1, -, -, -, -⟩ := top_mx (D := D) B.rank t
  obtain ⟨-, g2, g3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have : BorelSpace (GA D W) := ⟨rfl⟩
  obtain ⟨hc, 𝓕, hf⟩ := I.cov₁
  have := hf.1
  have := I.haar
  have := I.probK
  have hQ := sigmaFinite_parameter_product_measure I μ hμ
  obtain ⟨p1, p2⟩ := top_pair (D := D) B.rank W.rank t
  have o1 : OpensMeasurableSpace (Mx D B.rank W.rank × Mx D B.rank t) := p1.opensMeasurable
  have hS : Measurable fun z : Mx D B.rank W.rank × Mx D B.rank t => (z.1, z.2 + mm z.1 y) :=
    (continuous_fst.prodMk (continuous_snd.add (continuous_fst.matrix_mul continuous_const))).measurable
  have hτ : MeasurePreserving (fun p : I.l.K × Par D n t W => (p.1, p.2.1, p.2.2.1, p.2.2.2 + y))
      (I.νK.prod (Q0 I μ)) (I.νK.prod (Q0 I μ)) := by
    unfold Q0
    exact (MeasurePreserving.id _).prod ((MeasurePreserving.id _).prod
      ((MeasurePreserving.id _).prod (measurePreserving_add_right μ y)))
  have hπ := measurable_pi (d := d) hn I x₀
  have hcomp : (fun z : Mx D B.rank W.rank × Mx D B.rank t => (z.1, z.2 + mm z.1 y)) ∘
        (fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)) =
      (fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)) ∘
        (fun p : I.l.K × Par D n t W => (p.1, p.2.1, p.2.2.1, p.2.2.2 + y)) := by
    funext p
    refine Prod.ext rfl ?_
    have key : ∀ {a b c : ℕ} (g : Mx D a a) (ξ : Mx D a b) (u : Mx D a c) (y' y : Mx D b c),
        mm g (mm ξ y' + u) + mm (mm g ξ) y = mm g (mm ξ (y' + y) + u) := by
      intro a b c g ξ u y' y
      simp only [mm, Matrix.mul_add, Matrix.mul_assoc]
      abel
    exact key _ _ _ _ _
  unfold nuT
  rw [Measure.map_map hS hπ, hcomp, ← Measure.map_map hπ hτ.measurable, hτ.map_eq]

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureTranslationInvariantStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_measure_translation_invariant : ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ x₀ (y : Mx D W.rank t), (nuT hn I μ x₀).map (fun z => (z.1, z.2 + mm z.1 y)) = nuT hn I μ x₀ := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.nuT_shear_invariant | exact GlobalTheory.CompanionTheory.ColumnSplitting.nuT_shear_invariant | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.nuT_shear_invariant <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureConcentratedOnQuadric
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureConcentratedOnQuadric
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ColumnSplitting

variable {D : D7}

theorem continuous_adjM {a b : ℕ} : Continuous (adj : Mx D a b → Mx D b a) := by
  have hc : Continuous (cA D) := GlobalTheory.FockCompare.ThetaCont.continuous_conj
  exact (continuous_id.matrix_map hc).matrix_transpose

theorem continuous_ipM {X : Type} [TopologicalSpace X] (V : HSp D) {a b : ℕ} {f : X → Mx D V.rank a}
    {g : X → Mx D V.rank b} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => ip V (f x) (g x) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  exact (continuous_adjM.comp hf).matrix_mul (continuous_const.matrix_mul hg)

theorem continuous_qvM (V : HSp D) {r t : ℕ} (b₀ : HermE D r) :
    Continuous (qv (t := t) V b₀) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hT := (top_mx (D := D) t t).1
  have hy : Continuous (yv (t := t) V b₀) :=
    continuous_const.matrix_mul (continuous_ipM V continuous_fst continuous_snd)
  have h2 : Continuous fun z : Mx D V.rank r × Mx D V.rank t => ip V z.2 z.2 :=
    continuous_ipM V continuous_snd continuous_snd
  have h3 : Continuous fun z : Mx D V.rank r × Mx D V.rank t =>
      pr b₀ (yv V b₀ z) (yv V b₀ z) :=
    (continuous_adjM.comp hy).matrix_mul (continuous_const.matrix_mul hy)
  have hs : ContinuousSub (Mx D t t) := @IsTopologicalAddGroup.to_continuousSub _ _ _ hT
  exact h2.sub h3

theorem nuT_supp : ZpEq → AcEq → ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ (b₀ : HermE D W.rank), b₀.1.det ≠ 0 → ∀ x₀, gramQ W x₀ = b₀.1 → nuT hn I μ x₀ {z | ¬ ((1 : AE D) • z.1 = z.1 ∧ (1 : AE D) • z.2 = z.2 ∧ ip B z.1 z.1 = (1 : AE D) • rat b₀.1 ∧ qv B b₀ z = 0)} = 0 := by
  intro hZ hA D n t B W d hn I μ _ b₀ hb x₀ hx
  obtain ⟨g1, -⟩ := top_pair (D := D) B.rank W.rank t
  have o1 : OpensMeasurableSpace (Mx D B.rank W.rank × Mx D B.rank t) := g1.opensMeasurable
  have t1 := (top_mx (D := D) W.rank W.rank).2.2.2.1
  have t2 := (top_mx (D := D) t t).2.2.2.1
  have hcl : IsClosed {z : Mx D B.rank W.rank × Mx D B.rank t |
      ip B z.1 z.1 = rat b₀.1 ∧ qv B b₀ z = 0} :=
    (isClosed_eq (continuous_ipM B continuous_fst continuous_fst)
      continuous_const).inter (isClosed_eq (continuous_qvM B b₀) continuous_const)
  have hS : {z : Mx D B.rank W.rank × Mx D B.rank t | ¬ ((1 : AE D) • z.1 = z.1 ∧ (1 : AE D) • z.2 = z.2 ∧
      ip B z.1 z.1 = (1 : AE D) • rat b₀.1 ∧ qv B b₀ z = 0)} =
      {z | ip B z.1 z.1 = rat b₀.1 ∧ qv B b₀ z = 0}ᶜ := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, one_smul, true_and]
  rw [hS]
  unfold nuT
  rw [Measure.map_apply (measurable_pi hn I x₀) hcl.measurableSet.compl]
  have hE : (fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)) ⁻¹'
      {z | ip B z.1 z.1 = rat b₀.1 ∧ qv B b₀ z = 0}ᶜ = ∅ := by
    ext p
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    obtain ⟨a1, -, a3⟩ := hA D W.rank t B b₀ ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)
    obtain ⟨z1, -, z3⟩ := hZ D n t B W d hn b₀ hb x₀ hx p.2
    exact ⟨a1.trans z1, a3.trans z3⟩
  rw [hE, measure_empty]

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureConcentratedOnQuadricStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_measure_concentrated_on_quadric : ZpEq → AcEq → ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ (b₀ : HermE D W.rank), b₀.1.det ≠ 0 → ∀ x₀, gramQ W x₀ = b₀.1 → nuT hn I μ x₀ {z | ¬ ((1 : AE D) • z.1 = z.1 ∧ (1 : AE D) • z.2 = z.2 ∧ ip B z.1 z.1 = (1 : AE D) • rat b₀.1 ∧ qv B b₀ z = 0)} = 0 := by
  first | exact @GlobalTheory.CompanionTheory.ColumnSplitting.nuT_supp | exact GlobalTheory.CompanionTheory.ColumnSplitting.nuT_supp | (intros; apply GlobalTheory.CompanionTheory.ColumnSplitting.nuT_supp <;> assumption)
end
end
