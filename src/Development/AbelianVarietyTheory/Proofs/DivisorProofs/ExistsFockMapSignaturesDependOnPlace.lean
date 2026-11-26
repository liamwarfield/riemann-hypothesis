module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualSkewIdealLatticeIsSelfDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockVacuumGaussianFrames
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockMapOfCanonicalCommutationRelations

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianVacuumFramesPlaceSignatures
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianVacuumFramesPlaceSignatures
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD GlobalTheory.FockVacuum

noncomputable section

namespace GlobalTheory.HoweD

section Sign

variable {ι : Type} {P Q R S : ι → ℕ}

def cplxD (ι : Type) (P Q R S : ι → ℕ) : (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ] (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) where
  toFun c w := Matrix.of fun a b => lineSign a b * Complex.I * c w a b
  map_add' c c' := by ext w a b; simp [mul_add]
  map_smul' r c := by ext w a b; simp; ring

theorem cplxD_apply (c : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) :
    cplxD ι P Q R S c w a b = lineSign a b * Complex.I * c w a b := rfl

theorem cplxD_cplxD (c : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) : cplxD ι P Q R S (cplxD ι P Q R S c) = -c := by
  ext w a b
  rcases lineSign_cases a b with h | h <;> simp [cplxD_apply, h, ← mul_assoc]

theorem herm_cplxD [Fintype ι] (c c' : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :
    ∑ w, ∑ a, ∑ b, lineSign a b * cplxD ι P Q R S c w a b * star (cplxD ι P Q R S c' w a b) =
      ∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b) := by
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rcases lineSign_cases a b with h | h <;> simp [cplxD_apply, h]
  · linear_combination (-(c w a b * (starRingEnd ℂ) (c' w a b))) * Complex.I_mul_I
  · linear_combination (c w a b * (starRingEnd ℂ) (c' w a b)) * Complex.I_mul_I

theorem herm_cplxD_pos [Fintype ι] (c : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) (hc : c ≠ 0) :
    0 < -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (cplxD ι P Q R S c w a b)).im := by
  have h : ∀ w a b, (lineSign a b * c w a b * star (cplxD ι P Q R S c w a b)).im = -Complex.normSq (c w a b) := by
    intro w a b
    rcases lineSign_cases a b with h | h <;> simp [cplxD_apply, h, Complex.normSq_apply] <;> ring
  simp only [Complex.im_sum, h, Finset.sum_neg_distrib]
  obtain ⟨w, a, b, hw⟩ : ∃ w a b, c w a b ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hc (by ext w a b; exact h0 w a b)
  have : 0 < ∑ w, ∑ a, ∑ b, Complex.normSq (c w a b) :=
    Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
      ⟨w, Finset.mem_univ _, Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
        ⟨a, Finset.mem_univ _, Finset.sum_pos' (fun _ _ => Complex.normSq_nonneg _)
          ⟨b, Finset.mem_univ _, Complex.normSq_pos.2 hw⟩⟩⟩
  linarith

theorem cplxD_single [DecidableEq ι] (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) :
    cplxD ι P Q R S (Pi.single w (Matrix.single a b 1)) =
      (lineSign a b).re • (Pi.single w (Matrix.single a b Complex.I) : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) := by
  ext w' a' b'
  rw [cplxD_apply]
  by_cases hw : w' = w
  · subst hw
    by_cases hab : a = a' ∧ b = b'
    · obtain ⟨rfl, rfl⟩ := hab
      rcases lineSign_cases a b with h | h <;> simp [h]
    · simp [Matrix.single_apply, hab]
  · simp [hw]

end Sign

theorem exists_vacuumD : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β κ : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] {P Q R S : InfinitePlace F → ℕ}
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (D : Matrix α β (AE F E) → (SInf F κ →L[ℂ] SInf F κ)),
    IsCMExt F E σ → FramedD τ JA JB a b A C →
    (∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x =
        fderiv ℝ f x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
          (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((d.e u).2 i)) : ℝ) * f x) →
    ∃ f₀ : SInf F κ, f₀ ≠ 0 ∧ ∀ (w : InfinitePlace F) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (u u' : Matrix α β (AE F E)),
      At (evI F) u → At (evI F) u' →
      (∀ w', u.map (piInf (τ w')) = A w' * (Pi.single w (Matrix.single a b 1) : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w' * (C w')ᵀ) →
      (∀ w', u'.map (piInf (τ w')) = A w' * (Pi.single w (Matrix.single a b Complex.I) : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w' * (C w')ᵀ) →
      D u f₀ + (lineSign a b * Complex.I) • D u' f₀ = 0 := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S τ JA JB d a₀ b₀ A C D hCM hFr hD
  have hU := fun c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ =>
    GlobalTheory.T.existsUnique_archimedeanMatrix_adeleExtension_of_components σ τ hCM (fun w => A w * c w * (C w)ᵀ)
  choose U hU hU' using hU
  have hadd : ∀ c c', U (c + c') = U c + U c' := fun c c' => by
    refine (hU' (c + c') _ ⟨fun u hu => ?_, fun w => ?_⟩).symm
    · rw [smul_add, (hU c).1 u hu, (hU c').1 u hu, add_zero]
    · rw [Matrix.map_add _ (map_add _), (hU c).2, (hU c').2, Pi.add_apply, Matrix.mul_add, Matrix.add_mul]
  have hsmul : ∀ (r : ℝ) c, U (r • c) = realAd F r • U c := fun r c => by
    refine (hU' (r • c) _ ⟨fun u hu => ?_, fun w => ?_⟩).symm
    · rw [smul_comm, (hU c).1 u hu, smul_zero]
    · rw [GlobalTheory.T.realScalarArchimedeanAdele_smul_matrix_realPlace σ τ hCM, (hU c).2, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul]
      ext i j
      simp
  let p : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    { toFun := fun c i => evI F ((d.e (U c)).1 i)
      map_add' := fun c c' => by
        funext i
        rw [hadd, map_add (f := _)]
        exact map_add (evR F) _ _
      map_smul' := fun r c => by
        funext i
        rw [hsmul, map_smul]
        exact evI_realAd_mul r _ }
  let q : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    { toFun := fun c i => evI F ((d.e (U c)).2 i)
      map_add' := fun c c' => by
        funext i
        rw [hadd, map_add (f := _)]
        exact map_add (evR F) _ _
      map_smul' := fun r c => by
        funext i
        rw [hsmul, map_smul]
        exact evI_realAd_mul r _ }
  have hω : ∀ c c', trPair F κ (p c) (q c') - trPair F κ (p c') (q c) =
      -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im := fun c c' => by
    rw [← GlobalTheory.T.archimedean_trace_symplectic_orthonormal_frames σ τ JA JB a₀ b₀ A C hCM hFr (U c) (U c') c c' (hU c).1 (hU c').1 (hU c).2 (hU c').2, d.form,
      trPair_apply, trPair_apply, ← map_sub, ← evR_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_sub, map_sum, map_mul]
    rfl
  have hs : Function.Surjective (p.prod q) := by
    rintro ⟨v, v'⟩
    let u := d.e.symm (fun i => infAd (v i), fun i => infAd (v' i))
    have hu : At (evI F) u := fun t ht => by
      rw [← map_smul, LinearEquiv.map_eq_zero_iff]
      ext i
      · exact mul_infAd t ht _
      · exact mul_infAd t ht _
    choose A' hA' using fun w => (hFr.2.1 w).2
    choose C' hC' using fun w => (hFr.2.2 w).2
    have huc : u = U fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ := hU' _ _ ⟨hu, fun w => by
      have : (C' w)ᵀ * (C w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hC', Matrix.transpose_one]
      simp only [Matrix.mul_assoc]
      rw [this, Matrix.mul_one, ← Matrix.mul_assoc, hA', Matrix.one_mul]⟩
    refine ⟨fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ, Prod.ext (funext fun i => ?_) (funext fun i => ?_)⟩
    · change evI F ((d.e (U _)).1 i) = v i
      rw [← huc, LinearEquiv.apply_symm_apply, evI_infAd]
    · change evI F ((d.e (U _)).2 i) = v' i
      rw [← huc, LinearEquiv.apply_symm_apply, evI_infAd]
  obtain ⟨X, Y, hX, hY, hYp, hXY⟩ := exists_siegel (trPair F κ) p q (cplxD _ P Q R S) cplxD_cplxD
    (fun c c' => by rw [hω, hω, herm_cplxD]) (fun c hc => by rw [hω]; exact herm_cplxD_pos c hc) hs
  obtain ⟨f, hf0, hf⟩ := exists_gaussian X Y hX hY hYp
  refine ⟨f, hf0, fun w a b u u' hu hu' hc hc' => ?_⟩
  have e1 := hU' _ u ⟨hu, hc⟩
  have e2 := hU' _ u' ⟨hu', hc'⟩
  set c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ := Pi.single w (Matrix.single a b 1) with hcdef
  set c' : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ := Pi.single w (Matrix.single a b Complex.I) with hcdef'
  have hJ : cplxD _ P Q R S c = (lineSign a b).re • c' := cplxD_single w a b
  ext x
  have h1 := hXY c x
  have h2 := hXY (cplxD _ P Q R S c) x
  rw [cplxD_cplxD] at h2
  rw [hJ] at h1 h2
  simp only [map_smul, map_neg, smul_eq_mul] at h1 h2
  have k1 : D u f x = 2 * Real.pi * Complex.I * ((X x (p c) : ℝ) + Complex.I * (Y x (p c) : ℝ)) * f x -
      2 * Real.pi * Complex.I * (trPair F κ x (q c) : ℝ) * f x := by
    rw [hD u hu, hf, e1]; rfl
  have k2 : D u' f x = 2 * Real.pi * Complex.I * ((X x (p c') : ℝ) + Complex.I * (Y x (p c') : ℝ)) * f x -
      2 * Real.pi * Complex.I * (trPair F κ x (q c') : ℝ) * f x := by
    rw [hD u' hu', hf, e2]; rfl
  change D u f x + (lineSign a b * Complex.I) * D u' f x = 0
  rw [k1, k2]
  have h1' := congrArg (fun t : ℝ => (t : ℂ)) h1
  have h2' := congrArg (fun t : ℝ => (t : ℂ)) h2
  have hl : (((lineSign a b).re : ℝ) : ℂ) = lineSign a b := by
    rcases lineSign_cases a b with h | h <;> simp [h]
  push_cast at h1' h2'
  rw [hl] at h1' h2'
  linear_combination (2 * Real.pi * Complex.I * f x) * h1' + (2 * Real.pi * Complex.I * Complex.I * f x) * h2' +
    (2 * Real.pi * Complex.I * f x * lineSign a b * (Y x (p c') : ℝ)) * Complex.I_mul_I

end GlobalTheory.HoweD
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianVacuumFramesPlaceSignaturesStatement
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gaussianVacuum_frames_placeSignatures : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β κ : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] {P Q R S : InfinitePlace F → ℕ}
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (D : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → (SInf F κ →L[ℂ] SInf F κ)),
    IsCMExt F E σ → FramedD τ JA JB a b A C →
    (∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x =
        fderiv ℝ f x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
          (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((d.e u).2 i)) : ℝ) * f x) →
    ∃ f₀ : SInf F κ, f₀ ≠ 0 ∧ ∀ (w : InfinitePlace F) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (u u' : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
      At (evI F) u → At (evI F) u' →
      (∀ w', u.map (piInf (τ w')) = A w' * (Pi.single w (Matrix.single a b 1) : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w' * (C w')ᵀ) →
      (∀ w', u'.map (piInf (τ w')) = A w' * (Pi.single w (Matrix.single a b Complex.I) : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w' * (C w')ᵀ) →
      D u f₀ + (lineSign a b * Complex.I) • D u' f₀ = 0 := by
  first | exact @GlobalTheory.HoweD.exists_vacuumD | exact GlobalTheory.HoweD.exists_vacuumD | (intros; apply GlobalTheory.HoweD.exists_vacuumD <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMapOfCanonicalCommutationPlacewiseSignature
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PderivProdRenameSigmaOfNotMem
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.CCRFock

open MvPolynomial

def polMapD (W : Type) [Fintype W] [DecidableEq W] (Λ : W → Type) :
    (⨂[ℂ] w : W, MvPolynomial (Λ w) ℂ) →ₗ[ℂ] MvPolynomial (Σ w, Λ w) ℂ :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ W (MvPolynomial (Σ w, Λ w) ℂ)).compLinearMap
    fun w => (MvPolynomial.rename (Sigma.mk w)).toLinearMap)

theorem polMapD_tprod (W : Type) [Fintype W] [DecidableEq W] (Λ : W → Type) (q : ∀ w, MvPolynomial (Λ w) ℂ) :
    polMapD W Λ (PiTensorProduct.tprod ℂ q) = ∏ v, MvPolynomial.rename (Sigma.mk v) (q v) := by
  simp [polMapD]

theorem polMapD_index_injective (W : Type) [Fintype W] (Λ : W → Type) :
    Function.Injective (fun f : ∀ w, (Λ w →₀ ℕ) => ∑ w, Finsupp.mapDomain (Sigma.mk w) (f w)) := by
  have key : ∀ (f : ∀ w, (Λ w →₀ ℕ)) (w : W) (l : Λ w),
      (∑ w, Finsupp.mapDomain (Sigma.mk w) (f w)) ⟨w, l⟩ = f w l := by
    intro f w l
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single w]
    · exact Finsupp.mapDomain_apply_of_injective sigma_mk_injective _ _
    · intro v _ hv
      apply Finsupp.mapDomain_notin_range
      rintro ⟨x, hx⟩
      exact hv (congrArg Sigma.fst hx)
    · intro h
      exact absurd (Finset.mem_univ w) h
  intro f g h
  funext w
  ext l
  rw [← key f w l, ← key g w l]
  exact congrArg (fun F : (Σ w, Λ w) →₀ ℕ => F ⟨w, l⟩) h

theorem polMapD_tprod_monomial (W : Type) [Fintype W] [DecidableEq W] (Λ : W → Type) (f : ∀ w, (Λ w →₀ ℕ)) :
    polMapD W Λ (PiTensorProduct.tprod ℂ (fun w => (monomial (f w) (1 : ℂ) : MvPolynomial (Λ w) ℂ))) =
      monomial (∑ w, Finsupp.mapDomain (Sigma.mk w) (f w)) 1 := by
  rw [monomial_sum_one]
  simp only [polMapD, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, AlgHom.toLinearMap_apply, rename_monomial]

theorem polMapD_injective (W : Type) [Fintype W] [DecidableEq W] (Λ : W → Type) :
    Function.Injective (polMapD W Λ) := by
  let B := Basis.piTensorProduct (fun w : W => basisMonomials (Λ w) ℂ)
  have hli : LinearIndependent ℂ (polMapD W Λ ∘ B) := by
    have h := (basisMonomials (Σ w, Λ w) ℂ).linearIndependent.comp _ (polMapD_index_injective W Λ)
    have e : polMapD W Λ ∘ B = (basisMonomials (Σ w, Λ w) ℂ) ∘
        (fun f : ∀ w, (Λ w →₀ ℕ) => ∑ w, Finsupp.mapDomain (Sigma.mk w) (f w)) := by
      funext f
      simp only [Function.comp, B, Basis.piTensorProduct_apply, coe_basisMonomials]
      exact polMapD_tprod_monomial W Λ f
    rw [e]
    exact h
  have h1 : polMapD W Λ ∘ₗ Finsupp.linearCombination ℂ B =
      Finsupp.linearCombination ℂ (polMapD W Λ ∘ B) := by
    ext f
    simp
  intro x y hxy
  apply B.repr.injective
  apply hli
  rw [← h1]
  simp only [LinearMap.comp_apply, Module.Basis.linearCombination_repr, hxy]

theorem atPl_tprod_dep {W : Type} [Fintype W] [DecidableEq W] {Λ : W → Type} (w : W)
    (L : Module.End ℂ (MvPolynomial (Λ w) ℂ)) (p : ∀ v, MvPolynomial (Λ v) ℂ) :
    atPl (V := fun w => MvPolynomial (Λ w) ℂ) w L (PiTensorProduct.tprod ℂ p) =
      PiTensorProduct.tprod ℂ (Function.update p w (L (p w))) := by
  unfold atPl
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext v
  by_cases hv : v = w
  · subst hv; simp
  · simp [Function.update_of_ne hv]

theorem polMapD_atPl_mulLeft_X (W : Type) [Fintype W] [DecidableEq W] (Λ : W → Type) (w : W) (l : Λ w) :
    polMapD W Λ ∘ₗ atPl (V := fun w => MvPolynomial (Λ w) ℂ) w (LinearMap.mulLeft ℂ (MvPolynomial.X l)) =
      LinearMap.mulLeft ℂ (MvPolynomial.X ⟨w, l⟩) ∘ₗ polMapD W Λ := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro p
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, atPl_tprod_dep, polMapD_tprod,
    LinearMap.mulLeft_apply]
  rw [Fintype.prod_eq_mul_prod_compl w, Fintype.prod_eq_mul_prod_compl w
    (fun v => MvPolynomial.rename (Sigma.mk v) (p v)), ← mul_assoc]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun v hv => ?_
    have hv' : v ≠ w := by simpa using hv
    rw [Function.update_of_ne hv']

theorem pderiv_rename_sigmaMk_of_ne {W : Type} {Λ : W → Type} {v w : W} (h : v ≠ w) (l : Λ w)
    (r : MvPolynomial (Λ v) ℂ) :
    MvPolynomial.pderiv (⟨w, l⟩ : Σ w, Λ w) (MvPolynomial.rename (Sigma.mk v) r) = 0 := by
  induction r using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, MvPolynomial.rename_X, Derivation.leibniz, hp, MvPolynomial.pderiv_X_of_ne]
    · simp
    · intro e; exact h (congrArg Sigma.fst e)

theorem pderiv_prod_rename_sigma_of_notMem {W : Type} {Λ : W → Type} {w : W} (l : Λ w)
    (q : ∀ v, MvPolynomial (Λ v) ℂ) (s : Finset W) (hs : w ∉ s) :
    MvPolynomial.pderiv (⟨w, l⟩ : Σ w, Λ w) (∏ v ∈ s, MvPolynomial.rename (Sigma.mk v) (q v)) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.mem_insert, not_or] at hs
    rw [Finset.prod_insert ha, Derivation.leibniz, ih hs.2,
      pderiv_rename_sigmaMk_of_ne (fun e => hs.1 e.symm)]
    simp

theorem polMapD_atPl_pderiv (W : Type) [Fintype W] [DecidableEq W] (Λ : W → Type) (w : W) (l : Λ w) :
    polMapD W Λ ∘ₗ atPl (V := fun w => MvPolynomial (Λ w) ℂ) w (MvPolynomial.pderiv l).toLinearMap =
      (MvPolynomial.pderiv (⟨w, l⟩ : Σ w, Λ w)).toLinearMap ∘ₗ polMapD W Λ := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro q
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, atPl_tprod_dep, polMapD_tprod]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w)]
  have h1 : ∏ i ∈ Finset.univ.erase w, MvPolynomial.rename (Sigma.mk i)
      (Function.update q w ((MvPolynomial.pderiv l).toLinearMap (q w)) i) =
      ∏ i ∈ Finset.univ.erase w, MvPolynomial.rename (Sigma.mk i) (q i) :=
    Finset.prod_congr rfl fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [h1, Function.update_self, Derivation.coeFn_coe, Derivation.coeFn_coe, Derivation.leibniz,
    pderiv_prod_rename_sigma_of_notMem l q _ (Finset.notMem_erase w _),
    MvPolynomial.pderiv_rename sigma_mk_injective l (q w)]
  simp [mul_comm]

theorem exists_polMapD : ∀ (W : Type) [Fintype W] [DecidableEq W] (Λ : W → Type),
    ∃ θ : (⨂[ℂ] w : W, MvPolynomial (Λ w) ℂ) →ₗ[ℂ] MvPolynomial (Σ w, Λ w) ℂ, Function.Injective θ ∧
      ∀ (w : W) (l : Λ w) (T : ⨂[ℂ] w : W, MvPolynomial (Λ w) ℂ),
        θ (atPl (V := fun w => MvPolynomial (Λ w) ℂ) w (LinearMap.mulLeft ℂ (MvPolynomial.X l)) T) =
            MvPolynomial.X ⟨w, l⟩ * θ T ∧
          θ (atPl (V := fun w => MvPolynomial (Λ w) ℂ) w (MvPolynomial.pderiv l).toLinearMap T) =
            MvPolynomial.pderiv ⟨w, l⟩ (θ T) := by
  intro W _ _ Λ
  refine ⟨polMapD W Λ, polMapD_injective W Λ, fun w l T => ⟨?_, ?_⟩⟩
  · exact LinearMap.congr_fun (polMapD_atPl_mulLeft_X W Λ w l) T
  · exact LinearMap.congr_fun (polMapD_atPl_pderiv W Λ w l) T

end GlobalTheory.CCRFock

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineSignMulSelf
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.HoweD.CCRSig

variable {W : Type} [DecidableEq W] {P Q R S : W → ℕ}

def unitAtS (j : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) (z : ℂ) : ∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ :=
  Pi.single j.1 (Matrix.single j.2.1 j.2.2 z)

theorem sum_unitAtS [Fintype W] (j k : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) (z z' : ℂ) :
    (∑ w, ∑ a, ∑ b, lineSign a b * unitAtS j z w a b * star (unitAtS k z' w a b)) =
      if j = k then lineSign j.2.1 j.2.2 * z * star z' else 0 := by
  obtain ⟨w0, a0, b0⟩ := j
  obtain ⟨w1, a1, b1⟩ := k
  rw [Finset.sum_eq_single w0]
  · by_cases hw : w1 = w0
    · subst hw
      simp only [unitAtS, Pi.single_eq_same]
      rw [Finset.sum_eq_single a0, Finset.sum_eq_single b0]
      · by_cases ha : a0 = a1
        · subst ha
          by_cases hb : b0 = b1
          · subst hb; simp
          · have : (⟨w1, a0, b0⟩ : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) ≠ ⟨w1, a0, b1⟩ := by
              intro h; simp at h; exact hb h
            simp [this, hb, Ne.symm hb]
        · have : (⟨w1, a0, b0⟩ : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) ≠ ⟨w1, a1, b1⟩ := by
            intro h; simp at h; exact ha h.1
          simp [this, ha, Ne.symm ha]
      · intro b _ hb; simp [Ne.symm hb]
      · simp
      · intro a _ ha; simp [Ne.symm ha]
      · simp
    · have : (⟨w0, a0, b0⟩ : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) ≠ ⟨w1, a1, b1⟩ := by
        intro h; exact hw (congrArg Sigma.fst h).symm
      simp [unitAtS, hw, this]
  · intro w _ hw; simp [unitAtS, hw]
  · simp

theorem sum_unitAtS_eq [Fintype W] (c : ∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :
    c = ∑ j : (Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)), unitAtS j (c j.1 j.2.1 j.2.2) := by
  funext w a b
  simp only [Finset.sum_apply, Matrix.sum_apply, Fintype.sum_sigma, unitAtS]
  rw [Finset.sum_eq_single w]
  · simp only [Pi.single_eq_same]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single a, Finset.sum_eq_single b]
    · simp
    · intro b' _ hb; simp [Matrix.single_apply, hb]
    · simp
    · intro a' _ ha; simp [Matrix.single_apply, ha]
    · simp
  · intro w' _ hw; simp [Pi.single_eq_of_ne' hw]
  · simp

end GlobalTheory.HoweD.CCRSig

namespace GlobalTheory.HoweD.CCRSig

variable {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [DecidableEq W] {P Q R S : W → ℕ}

theorem lineSign_cases {P Q R S : ℕ} (a : Ix P Q) (b : Ix R S) : (lineSign a b : ℂ) = 1 ∨ (lineSign a b : ℂ) = -1 := by
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign]

theorem lineSign_mul_self {P Q R S : ℕ} (a : Ix P Q) (b : Ix R S) : lineSign a b * lineSign a b = 1 := by
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign]

theorem comm_expand (A A' B B' : Module.End ℂ V) (c u v : ℂ) :
    -(c • (A + u • A')) * (c • (B - v • B')) - (c • (B - v • B')) * -(c • (A + u • A')) =
      -((c * c) • ((A * B - B * A) - v • (A * B' - B' * A) + u • (A' * B - B * A') - (u * v) • (A' * B' - B' * A'))) := by
  simp only [neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, mul_add, add_mul, mul_sub, sub_mul]
  module

theorem inv_sq : (2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ * (2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ =
    (8 * (Real.pi : ℂ))⁻¹ := by
  have h : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) = 2 * (Real.pi : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast; ring
  rw [← mul_inv]
  congr 1
  linear_combination 4 * h

def ccrM (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V)
    (j : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) : Module.End ℂ V :=
  (2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ •
    (H (unitAtS j 1) - (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAtS j Complex.I))

def ccrD (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V)
    (j : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) : Module.End ℂ V :=
  -((2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ •
    (H (unitAtS j 1) + (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAtS j Complex.I)))

theorem ccrM_comm [Fintype W] (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V)
    (hc : ∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1)
    (j k : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) : ccrM H j * ccrM H k = ccrM H k * ccrM H j := by
  have h11 := hc (unitAtS j 1) (unitAtS k 1)
  have h1i := hc (unitAtS j 1) (unitAtS k Complex.I)
  have hi1 := hc (unitAtS j Complex.I) (unitAtS k 1)
  have hii := hc (unitAtS j Complex.I) (unitAtS k Complex.I)
  rw [sum_unitAtS] at h11 h1i hi1 hii
  by_cases hjk : j = k
  · rw [hjk]
  · simp only [if_neg hjk, Complex.zero_im, Complex.ofReal_zero, mul_zero, zero_smul, sub_eq_zero] at h11 h1i hi1 hii
    unfold ccrM
    have c : Commute (H (unitAtS j 1) - (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAtS j Complex.I))
        (H (unitAtS k 1) - (lineSign k.2.1 k.2.2 * Complex.I) • H (unitAtS k Complex.I)) :=
      Commute.sub_left (Commute.sub_right h11 (Commute.smul_right h1i _))
        (Commute.smul_left (Commute.sub_right hi1 (Commute.smul_right hii _)) _)
    exact ((c.smul_left _).smul_right _).eq

theorem ccrD_ccrM_comm [Fintype W] (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V)
    (hc : ∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1)
    (j k : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) :
    ccrD H j * ccrM H k - ccrM H k * ccrD H j = if j = k then 1 else 0 := by
  unfold ccrD ccrM
  rw [comm_expand, hc, hc, hc, hc, sum_unitAtS, sum_unitAtS, sum_unitAtS, sum_unitAtS,
    inv_sq]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  by_cases h : j = k
  · subst h
    simp only [if_true, smul_smul, ← sub_smul, ← add_smul, ← neg_smul]
    conv_rhs => rw [← one_smul ℂ (1 : Module.End ℂ V)]
    congr 1
    rcases lineSign_cases j.2.1 j.2.2 with h | h
    · rw [h]; simp; field_simp; linear_combination (-8 : ℂ) * Complex.I_sq
    · rw [h]; simp; field_simp; linear_combination (-8 : ℂ) * Complex.I_sq
  · simp [h]

theorem unitAtS_re_im (j : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) (z : ℂ) :
    unitAtS j z = ((z.re : ℝ) : ℂ) • unitAtS j 1 + ((z.im : ℝ) : ℂ) • unitAtS j Complex.I := by
  funext w
  by_cases hw : w = j.1
  · subst hw
    simp only [unitAtS, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Matrix.smul_single, ← Matrix.single_add, smul_eq_mul,
      mul_one, Complex.re_add_im]
  · simp [unitAtS, Pi.single_eq_of_ne hw]

theorem heis_expanccrD [Fintype W] (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V)
    (hadd : ∀ c c', H (c + c') = H c + H c') (hsmul : ∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c)
    (c : ∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :
    H c = ∑ j : (Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)),
      ((((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefM (c j.1 j.2.1 j.2.2) (lineSign j.2.1 j.2.2)) • ccrM H j +
        (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefD (c j.1 j.2.1 j.2.2) (lineSign j.2.1 j.2.2)) • ccrD H j) := by
  have h0 : H 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  let H' : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →+ Module.End ℂ V := ⟨⟨H, h0⟩, hadd⟩
  have hsum : H c = ∑ j : (Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)), H (unitAtS j (c j.1 j.2.1 j.2.2)) := by
    conv_lhs => rw [sum_unitAtS_eq c]
    exact map_sum H' _ _
  rw [hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [unitAtS_re_im, hadd, hsmul, hsmul]
  have hs : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    exact_mod_cast this.ne'
  have he := lineSign_mul_self j.2.1 j.2.2
  unfold ccrM ccrD GlobalTheory.CCRFock.coefM GlobalTheory.CCRFock.coefD
  generalize ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) = s at hs ⊢
  generalize lineSign j.2.1 j.2.2 = e at he ⊢
  generalize H (unitAtS j 1) = A
  generalize H (unitAtS j Complex.I) = B
  generalize ((c j.1 j.2.1 j.2.2).re : ℂ) = x
  generalize ((c j.1 j.2.1 j.2.2).im : ℂ) = y
  have hI := Complex.I_mul_I
  match_scalars
  · field_simp
    ring
  · field_simp
    linear_combination (2 * y * e * e) * hI - 2 * y * he

end GlobalTheory.HoweD.CCRSig

namespace GlobalTheory.HoweD


open GlobalTheory.HoweD.CCRSig in
theorem ccr_fock_ops_sig : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : W → ℕ} (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V), (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) → (∀ c c', H c * H c' - H c' * H c = ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1) → ∃ m D : (Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) → Module.End ℂ V, (∀ i j, m i * m j = m j * m i) ∧ (∀ i j, D i * m j - m j * D i = if i = j then 1 else 0) ∧ (∀ (j : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) (f₀ : V), H (Pi.single j.1 (Matrix.single j.2.1 j.2.2 1)) f₀ + (lineSign j.2.1 j.2.2 * Complex.I) • H (Pi.single j.1 (Matrix.single j.2.1 j.2.2 Complex.I)) f₀ = 0 → D j f₀ = 0) ∧ ∀ c, H c = ∑ j : (Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)), ((((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefM (c j.1 j.2.1 j.2.2) (lineSign j.2.1 j.2.2)) • m j + (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefD (c j.1 j.2.1 j.2.2) (lineSign j.2.1 j.2.2)) • D j) := by
  intro V _ _ W _ _ P Q R S H hadd hsmul hc
  refine ⟨ccrM H, ccrD H, ccrM_comm H hc, ccrD_ccrM_comm H hc, fun j f₀ h => ?_, heis_expanccrD H hadd hsmul⟩
  have h' : H (unitAtS j 1) f₀ + (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAtS j Complex.I) f₀ = 0 := h
  simp only [GlobalTheory.HoweD.CCRSig.ccrD, LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.add_apply, h', smul_zero, neg_zero]

end GlobalTheory.HoweD
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMapOfCanonicalCommutationPlacewiseSignature
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.CCRFock
open MvPolynomial

theorem atPl_linear_dep {W : Type} [Fintype W] [DecidableEq W] {Λ : W → Type} (w : W) :
    ∃ L : Module.End ℂ (MvPolynomial (Λ w) ℂ) →ₗ[ℂ] Module.End ℂ (⨂[ℂ] v : W, MvPolynomial (Λ v) ℂ),
      ∀ A, L A = GlobalTheory.RealLift.atPl (V := fun v : W => MvPolynomial (Λ v) ℂ) w A :=
  ⟨{ toFun := fun A => GlobalTheory.RealLift.atPl (V := fun v : W => MvPolynomial (Λ v) ℂ) w A
     map_add' := fun A B => by
       unfold GlobalTheory.RealLift.atPl
       exact PiTensorProduct.map_update_add
         (fun v : W => (LinearMap.id : MvPolynomial (Λ v) ℂ →ₗ[ℂ] MvPolynomial (Λ v) ℂ)) w A B
     map_smul' := fun c A => by
       unfold GlobalTheory.RealLift.atPl
       exact PiTensorProduct.map_update_smul
         (fun v : W => (LinearMap.id : MvPolynomial (Λ v) ℂ →ₗ[ℂ] MvPolynomial (Λ v) ℂ)) w c A }, fun _ => rfl⟩

theorem fock_map_of_ccr_dep : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : W → ℕ}
    (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V),
    (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) →
    (∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1) →
    ∀ f₀ : V, f₀ ≠ 0 →
    (∀ w a b, H (Pi.single w (Matrix.single a b 1)) f₀ +
      (lineSign a b * Complex.I) • H (Pi.single w (Matrix.single a b Complex.I)) f₀ = 0) →
    ∃ Φ : (⨂[ℂ] w : W, Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) →ₗ[ℂ] V, Function.Injective Φ ∧
      ∀ c T, Φ (sumPl (fun w => heisOp (c w)) T) = H c (Φ T) := by
  intro V _ _ W _ _ P Q R S H hadd hsmul hcomm f₀ hf₀ hvac
  obtain ⟨m, D, hm, hdm, hD0, hH⟩ := GlobalTheory.HoweD.ccr_fock_ops_sig H hadd hsmul hcomm
  obtain ⟨θ, hθ, hθ'⟩ := GlobalTheory.CCRFock.exists_polMapD W (fun w => Ix (P w) (Q w) × Ix (R w) (S w))
  have hd0 : ∀ j, D j f₀ = 0 := fun j => hD0 j f₀ (hvac j.1 j.2.1 j.2.2)
  have hD := GlobalTheory.CCRFock.polEval_pderiv m D hm f₀ (fun i j => by convert hdm i j) hd0
  refine ⟨polEval m hm f₀ ∘ₗ θ, ?_, ?_⟩
  · exact (GlobalTheory.FockAlg.injective_of_pderiv (polEval m hm f₀) D hD (by rw [polEval_one]; exact hf₀)).comp hθ
  · intro c T
    rw [hH c, Fintype.sum_sigma]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.comp_apply, sumPl, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    obtain ⟨L, hL⟩ := atPl_linear_dep (W := W) (Λ := fun w => Ix (P w) (Q w) × Ix (R w) (S w)) w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [heisOp_eq_sum_mul_pderiv, ← hL, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sum_apply, map_sum, map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply]
    simp only [hL]
    refine Finset.sum_congr rfl fun l _ => ?_
    obtain ⟨hX, hY⟩ := hθ' w l T
    rw [hX, hY, polEval_X, hD]

end GlobalTheory.CCRFock
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMapOfCanonicalCommutationPlacewiseSignatureStatement
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockMap_of_canonicalCommutation_placewise_signature : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : W → ℕ}
    (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V),
    (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) →
    (∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1) →
    ∀ f₀ : V, f₀ ≠ 0 →
    (∀ w a b, H (Pi.single w (Matrix.single a b 1)) f₀ +
      (lineSign a b * Complex.I) • H (Pi.single w (Matrix.single a b Complex.I)) f₀ = 0) →
    ∃ Φ : (⨂[ℂ] w : W, Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)) →ₗ[ℂ] V, Function.Injective Φ ∧
      ∀ c T, Φ (sumPl (fun w => heisOp (c w)) T) = H c (Φ T) := by
  first | exact @GlobalTheory.CCRFock.fock_map_of_ccr_dep | exact GlobalTheory.CCRFock.fock_map_of_ccr_dep | (intros; apply GlobalTheory.CCRFock.fock_map_of_ccr_dep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockMapSignaturesDependOnPlace
noncomputable section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD

theorem exists_isFockMapD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → IsStd ψ → FramedD τ JA JB a b A C →
    ∃ Φ, IsFockMapD ψ τ d A C Φ := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C hCM hψ hFr
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ α β κ ψ JA JB d hψ
  have hDf : ∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x =
      fderiv ℝ f x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
        (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((d.e u).2 i)) : ℝ) * f x :=
    fun u hu f x => (hD u hu f).2 x
  obtain ⟨hadd, hsm, hcom⟩ := GlobalTheory.T.archHeisenbergDerivative_additive_commutator σ JA JB d D hDf
  have hex := fun c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ =>
    GlobalTheory.T.existsUnique_archimedeanMatrix_adeleExtension_of_components σ τ hCM (fun w => A w * c w * (C w)ᵀ)
  choose uOf huOf using fun c => (hex c).exists
  have huniq : ∀ c u, At (evI F) u → (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) → u = uOf c :=
    fun c u hu hw => (hex c).unique ⟨hu, hw⟩ (huOf c)
  have hAt_add : ∀ u u' : Matrix α β (AE F E), At (evI F) u → At (evI F) u' → At (evI F) (u + u') :=
    fun u u' hu hu' z hz => by rw [smul_add, hu z hz, hu' z hz, add_zero]
  have hAt_smul : ∀ (r : ℝ) (u : Matrix α β (AE F E)), At (evI F) u → At (evI F) (realAd F r • u) :=
    fun r u hu z hz => by rw [smul_comm, hu z hz, smul_zero]
  let H : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ (SInf F κ) :=
    fun c => (D (uOf c)).toLinearMap
  have hHadd : ∀ c c', H (c + c') = H c + H c' := by
    intro c c'
    have e : uOf (c + c') = uOf c + uOf c' := by
      symm
      refine huniq _ _ (hAt_add _ _ (huOf c).1 (huOf c').1) fun w => ?_
      rw [Matrix.map_add _ (map_add _), (huOf c).2 w, (huOf c').2 w]
      simp [Matrix.mul_add, Matrix.add_mul]
    ext1 f
    simp only [H, e, hadd _ _ (huOf c).1 (huOf c').1]
    rfl
  have hHsmul : ∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c := by
    intro r c
    have e : uOf ((r : ℂ) • c) = realAd F r • uOf c := by
      symm
      refine huniq _ _ (hAt_smul r _ (huOf c).1) fun w => ?_
      rw [GlobalTheory.T.realScalarArchimedeanAdele_smul_matrix_realPlace σ τ hCM, (huOf c).2 w]
      simp [Matrix.mul_smul, Matrix.smul_mul]
    ext1 f
    simp only [H, e, hsm _ r (huOf c).1]
    rfl
  have hHcomm : ∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1 := by
    intro c c'
    ext1 f
    have h1 := hcom _ _ (huOf c).1 (huOf c').1 f
    rw [GlobalTheory.T.archimedean_trace_symplectic_orthonormal_frames σ τ JA JB a b A C hCM hFr _ _ c c' (huOf c).1 (huOf c').1 (huOf c).2 (huOf c').2] at h1
    simp only [H, LinearMap.sub_apply, Module.End.mul_apply, ContinuousLinearMap.coe_coe, LinearMap.smul_apply,
      Module.End.one_apply]
    rw [h1]
    congr 1
    push_cast
    ring
  obtain ⟨f₀, hf₀, hv⟩ := GlobalTheory.T.exists_gaussianVacuum_frames_placeSignatures σ τ JA JB d a b A C D hCM hFr hDf
  have hHvac : ∀ w a b, H (Pi.single w (Matrix.single a b 1)) f₀ +
      (lineSign a b * Complex.I) • H (Pi.single w (Matrix.single a b Complex.I)) f₀ = 0 := fun w a b =>
    hv w a b _ _ (huOf _).1 (huOf _).1 (huOf _).2 (huOf _).2
  obtain ⟨Φ, hinj, hint⟩ := GlobalTheory.T.fockMap_of_canonicalCommutation_placewise_signature H hHadd hHsmul hHcomm f₀ hf₀ hHvac
  refine ⟨Φ, hinj, fun u hu c hc T => ?_⟩
  rw [hint, huniq c u hu hc]
  exact (hD _ (huOf c).1 (Φ T)).1

end GlobalTheory.HoweD

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockMapSignaturesDependOnPlaceStatement
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fockMap_signatures_depend_on_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → IsStd ψ → FramedD τ JA JB a b A C →
    ∃ Φ, IsFockMapD ψ τ d A C Φ := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C hCM hψ hFr
  exact GlobalTheory.HoweD.exists_isFockMapD F E σ α β κ P Q R S ψ τ JA JB d a b A C hCM hψ hFr
end
