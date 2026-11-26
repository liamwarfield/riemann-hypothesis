module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.WeilSiegelFormula.HeadOfSiegel
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralEqCoefficientNonrepresented
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.SiegelWeilFreeOfBlockNonemptyFrames
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanSiegelWeilMeasure

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.SiegelDeg
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilProductOverPlaces
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilProductOverPlaces
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelND.DxN

theorem selfDual_isEulerProd_n : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) → GlobalTheory.CompanionTheory.SW.IsEulerProd b dx 1 (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M) (fun v => GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M) ∧ ∀ v, GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M (latV b v) = 1 := by
  intro F E _ _ _ _ _ σ hCM M J hJ n _ hM ψ hψ dx hdx d b laminf lam hinf hlam
  exact selfDual_isEulerProd_tuple F E σ hCM M J hJ n hM ψ hψ dx hdx d b laminf lam hinf hlam

end GlobalTheory.CompanionTheory.SiegelND.DxN

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilProductOverPlacesStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_weil_product_over_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) → GlobalTheory.CompanionTheory.SW.IsEulerProd b dx 1 (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M) (fun v => GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M) ∧ ∀ v, GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M (latV b v) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.DxN.selfDual_isEulerProd_n | exact GlobalTheory.CompanionTheory.SiegelND.DxN.selfDual_isEulerProd_n | (intros; apply GlobalTheory.CompanionTheory.SiegelND.DxN.selfDual_isEulerProd_n <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatIntegrableAnyHaar
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatIntegrableAnyHaar
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.SBInt

theorem integrable_isSchwartzBruhat_tuple : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M n : ℕ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)), dx.IsAddHaarMeasure → ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ → Integrable Φ dx := by
  intro F E _ _ _ _ _ σ hCM M n dx hdx Φ hΦ
  exact (GlobalTheory.CompanionTheory.SiegelND.Integ.Phase.continuous_integrable σ hCM dx hdx hΦ).2

end GlobalTheory.CompanionTheory.SiegelND.Coef.SBInt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatIntegrableAnyHaarStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bruhat_integrable_any_haar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M n : ℕ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)), dx.IsAddHaarMeasure → ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ → Integrable Φ dx := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.SBInt.integrable_isSchwartzBruhat_tuple | exact GlobalTheory.CompanionTheory.SiegelND.Coef.SBInt.integrable_isSchwartzBruhat_tuple | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.SBInt.integrable_isSchwartzBruhat_tuple <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SingularHermitianCongruentBlockNormalForm
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SingularHermitianCongruentBlockNormalForm
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Deg.NF

theorem exists_radical_basis {K : Type*} [Field K] {r : ℕ} (B : Matrix (Fin r) (Fin r) K)
    (hd : B.det = 0) :
    ∃ (t k : ℕ) (e : Module.Basis (Fin t ⊕ Fin k) K (Fin r → K)), 0 < k ∧
      (∀ j, B *ᵥ e (Sum.inr j) = 0) ∧
      (∀ w : Fin t → K, B *ᵥ (∑ j, w j • e (Sum.inl j)) = 0 → w = 0) := by
  obtain ⟨N, hN⟩ : ∃ N : Submodule K (Fin r → K), N = LinearMap.ker B.mulVecLin := ⟨_, rfl⟩
  have hmemN : ∀ v, v ∈ N ↔ B *ᵥ v = 0 := fun v => by
    rw [hN, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl N
  obtain ⟨bN⟩ : Nonempty (Module.Basis (Fin (Module.finrank K N)) K N) := ⟨Module.finBasis K N⟩
  obtain ⟨bC⟩ : Nonempty (Module.Basis (Fin (Module.finrank K C)) K C) := ⟨Module.finBasis K C⟩
  obtain ⟨e, he⟩ : ∃ e : Module.Basis (Fin (Module.finrank K C) ⊕ Fin (Module.finrank K N)) K (Fin r → K),
      e = (bC.prod bN).map (Submodule.prodEquivOfIsCompl C N hC.symm) := ⟨_, rfl⟩
  have he_inl : ∀ j, e (Sum.inl j) = (bC j : Fin r → K) := fun j => by
    rw [he, Module.Basis.map_apply, Module.Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']
    simp
  have he_inr : ∀ j, e (Sum.inr j) = (bN j : Fin r → K) := fun j => by
    rw [he, Module.Basis.map_apply, Module.Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']
    simp
  refine ⟨Module.finrank K C, Module.finrank K N, e, ?_, ?_, ?_⟩
  · obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
    rw [Module.finrank_pos_iff_exists_ne_zero]
    refine ⟨⟨v, (hmemN v).mpr hv⟩, fun h => hv0 ?_⟩
    simpa using congrArg Subtype.val h
  · intro j
    rw [he_inr]
    exact (hmemN _).mp (bN j).2
  · intro w hw
    simp only [he_inl] at hw
    have hc : ((∑ j, w j • bC j : C) : Fin r → K) = ∑ j, w j • (bC j : Fin r → K) := by
      simp
    have hNmem : ((∑ j, w j • bC j : C) : Fin r → K) ∈ N := by
      rw [hmemN, hc]
      exact hw
    have h0 : ((∑ j, w j • bC j : C) : Fin r → K) = 0 :=
      Submodule.disjoint_def.mp hC.disjoint _ hNmem (Submodule.coe_mem _)
    funext j
    exact Fintype.linearIndependent_iff.mp bC.linearIndependent w (Submodule.coe_eq_zero.mp h0) j

theorem exists_blockNF {K : Type*} [Field K] (s : K →+* K) (hs : ∀ x, s (s x) = x) {r : ℕ}
    (B : Matrix (Fin r) (Fin r) K) (hB : (B.map s)ᵀ = B) (hd : B.det = 0) :
    ∃ (P : Matrix (Fin r) (Fin r) K) (t : ℕ) (h : t < r), P.det ≠ 0 ∧
      (∀ i j : Fin r, (t ≤ i.1 ∨ t ≤ j.1) → ((P.map s)ᵀ * B * P) i j = 0) ∧
      (((P.map s)ᵀ * B * P).submatrix (Fin.castLE h.le) (Fin.castLE h.le)).det ≠ 0 := by
  obtain ⟨t, k, e, hk, hker, hinj⟩ := exists_radical_basis B hd
  have hcard : t + k = r := by
    have h1 := Module.finrank_eq_card_basis e
    rw [Module.finrank_fin_fun, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h1
    exact h1.symm
  subst hcard
  have ht : t < t + k := Nat.lt_add_of_pos_right hk
  have hsplit : ∀ c : Fin t ⊕ Fin k, (∃ i', c = Sum.inl i') ∨ ∃ i', c = Sum.inr i' := by
    rintro (i' | i')
    · exact Or.inl ⟨i', rfl⟩
    · exact Or.inr ⟨i', rfl⟩
  have hinr : ∀ i : Fin (t + k), t ≤ i.1 → ∃ i', finSumFinEquiv.symm i = Sum.inr i' := by
    intro i hi
    rcases hsplit (finSumFinEquiv.symm i) with ⟨i', hc⟩ | ⟨i', hc⟩
    · exfalso
      have h1 : finSumFinEquiv (finSumFinEquiv.symm i) = i := finSumFinEquiv.apply_symm_apply i
      rw [hc, finSumFinEquiv_apply_left] at h1
      have h2 : i.1 = i'.1 := (congrArg Fin.val h1).symm
      have h3 := i'.isLt
      omega
    · exact ⟨i', hc⟩
  have hcast : ∀ j : Fin t, finSumFinEquiv.symm (Fin.castLE ht.le j) = Sum.inl j := by
    intro j
    have h1 : Fin.castLE ht.le j = Fin.castAdd k j := Fin.ext rfl
    rw [h1, finSumFinEquiv_symm_apply_castAdd]
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin (t + k)) (Fin (t + k)) K,
      ∀ a b, P a b = e (finSumFinEquiv.symm b) a :=
    ⟨Matrix.of fun a b => e (finSumFinEquiv.symm b) a, fun _ _ => rfl⟩
  have hBab : ∀ a b, s (B b a) = B a b := fun a b => by
    simpa using congrFun (congrFun hB a) b
  have hentry : ∀ i j, ((P.map s)ᵀ * B * P) i j =
      (fun a => s (e (finSumFinEquiv.symm i) a)) ⬝ᵥ (B *ᵥ e (finSumFinEquiv.symm j)) := by
    intro i j
    rw [Matrix.mul_assoc]
    simp only [Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.transpose_apply,
      Matrix.map_apply, hP]
  have hrow : ∀ i' : Fin k, Matrix.vecMul (fun a => s (e (Sum.inr i') a)) B = 0 := by
    intro i'
    ext b
    have h0 : (B *ᵥ e (Sum.inr i')) b = 0 := by rw [hker i', Pi.zero_apply]
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
    calc ∑ a, s (e (Sum.inr i') a) * B a b = ∑ a, s (B b a * e (Sum.inr i') a) :=
          Finset.sum_congr rfl fun a _ => by rw [map_mul, hBab, mul_comm]
      _ = s (∑ a, B b a * e (Sum.inr i') a) := (map_sum s _ _).symm
      _ = s ((B *ᵥ e (Sum.inr i')) b) := rfl
      _ = 0 := by rw [h0, map_zero]
  have hzero : ∀ i j : Fin (t + k), (t ≤ i.1 ∨ t ≤ j.1) → ((P.map s)ᵀ * B * P) i j = 0 := by
    intro i j hij
    rw [hentry]
    rcases hij with hi | hj
    · obtain ⟨i', hi'⟩ := hinr i hi
      rw [hi', Matrix.dotProduct_mulVec, hrow i', zero_dotProduct]
    · obtain ⟨j', hj'⟩ := hinr j hj
      rw [hj', hker j', dotProduct_zero]
  have hli : LinearIndependent K (fun b => e (finSumFinEquiv.symm b)) :=
    e.linearIndependent.comp _ finSumFinEquiv.symm.injective
  have hmv : ∀ v : Fin (t + k) → K, P *ᵥ v = ∑ b, v b • e (finSumFinEquiv.symm b) := by
    intro v
    ext a
    simp [Matrix.mulVec, dotProduct, hP, Finset.sum_apply, mul_comm]
  have hPdet : P.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hv0
    funext b
    exact Fintype.linearIndependent_iff.mp hli v (by rw [← hmv v]; exact hv) b
  have hPs : ((P.map s)ᵀ).det ≠ 0 := by
    rw [Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero s).mpr hPdet
  have hTy : ∀ i (y : Fin (t + k) → K),
      ((P.map s)ᵀ *ᵥ y) i = (fun a => s (e (finSumFinEquiv.symm i) a)) ⬝ᵥ y := by
    intro i y
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply, hP]
  refine ⟨P, t, ht, hPdet, hzero, ?_⟩
  intro hB0
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hB0
  apply hw0
  apply hinj w
  obtain ⟨u, hu⟩ : ∃ u : Fin (t + k) → K, u = ∑ j, w j • e (Sum.inl j) := ⟨_, rfl⟩
  rw [← hu]
  have hexp : ∀ i, (fun a => s (e (finSumFinEquiv.symm i) a)) ⬝ᵥ (B *ᵥ u) =
      ∑ j, ((P.map s)ᵀ * B * P) i (Fin.castLE ht.le j) * w j := by
    intro i
    rw [hu, Matrix.mulVec_sum, dotProduct_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, hentry, hcast, mul_comm]
  by_contra hBu
  apply hPs
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨B *ᵥ u, hBu, ?_⟩
  funext i
  rw [hTy, Pi.zero_apply]
  rcases hsplit (finSumFinEquiv.symm i) with ⟨i', hc⟩ | ⟨i', hc⟩
  · have h1 : finSumFinEquiv (finSumFinEquiv.symm i) = i := finSumFinEquiv.apply_symm_apply i
    rw [hc, finSumFinEquiv_apply_left] at h1
    have hi : i = Fin.castLE ht.le i' := h1.symm.trans (Fin.ext rfl)
    rw [hexp, hi]
    have h2 := congrFun hw i'
    first
    | exact h2
    | (simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Pi.zero_apply] at h2; exact h2)
  · rw [hc, Matrix.dotProduct_mulVec, hrow i', zero_dotProduct]

end GlobalTheory.CompanionTheory.WeilSiegel.Deg.NF

namespace GlobalTheory.CompanionTheory.WeilSiegel.Deg

theorem exists_congrH_isBlockNF (D : D7) (r : ℕ) (β : HermE D r) (hd : β.1.det = 0) :
    ∃ (a : Matrix (Fin r) (Fin r) D.host.E) (t : ℕ) (γ : HermE D r),
      a.det ≠ 0 ∧ IsBlockNF t γ ∧ β = congrH a γ := by
  obtain ⟨P, t, ht, hP, hzero, hblock⟩ := NF.exists_blockNF (D.sp.cm.sig : D.host.E →+* D.host.E)
    (fun x => star_star x) β.1 β.2 hd
  have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  refine ⟨P⁻¹, t, congrH P β, ?_, ⟨ht, hzero, hblock⟩, ?_⟩
  · intro h0
    have h1 := congrArg Matrix.det (Matrix.nonsing_inv_mul P hu)
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  · apply Subtype.ext
    change β.1 = ((P⁻¹).map (D.sp.cm.sig : D.host.E →+* D.host.E))ᵀ *
      ((P.map (D.sp.cm.sig : D.host.E →+* D.host.E))ᵀ * β.1 * P) * P⁻¹
    have h1 : ((P⁻¹).map (D.sp.cm.sig : D.host.E →+* D.host.E))ᵀ *
        (P.map (D.sp.cm.sig : D.host.E →+* D.host.E))ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, Matrix.mul_nonsing_inv P hu,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv P hu, Matrix.mul_one]

end GlobalTheory.CompanionTheory.WeilSiegel.Deg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SingularHermitianCongruentBlockNormalFormStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.singular_hermitian_congruent_block_normal_form : ∀ (D : D7) (r : ℕ) (β : HermE D r), β.1.det = 0 → ∃ (a : Matrix (Fin r) (Fin r) D.host.E) (t : ℕ) (γ : HermE D r), a.det ≠ 0 ∧ GlobalTheory.CompanionTheory.WeilSiegel.Deg.IsBlockNF t γ ∧ β = GlobalTheory.CompanionTheory.WeilSiegel.Deg.congrH a γ := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Deg.exists_congrH_isBlockNF | exact GlobalTheory.CompanionTheory.WeilSiegel.Deg.exists_congrH_isBlockNF | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Deg.exists_congrH_isBlockNF <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralCongruenceInvariant
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralCongruenceInvariant
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Deg

theorem gramQ_mul_right (D : D7) (V : HSp D) {r : ℕ} (x : Matrix (Fin V.rank) (Fin r) D.host.E)
    (a : Matrix (Fin r) (Fin r) D.host.E) :
    gramQ V (x * a) = (a.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ * gramQ V x * a := by
  have hm : (x * a).map (D.sp.cm.sig : D.host.E → D.host.E) =
      x.map (D.sp.cm.sig : D.host.E → D.host.E) * a.map (D.sp.cm.sig : D.host.E → D.host.E) :=
    Matrix.map_mul (f := (D.sp.cm.sig : D.host.E →+* D.host.E))
  unfold gramQ
  rw [hm, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

def congrEquiv (D : D7) (V : HSp D) {r : ℕ} (β : HermE D r) (a : Matrix (Fin r) (Fin r) D.host.E)
    (ha : a.det ≠ 0) :
    {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1} ≃
      {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = (congrH a β).1} :=
  have hu : IsUnit a.det := isUnit_iff_ne_zero.mpr ha
  have hi : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a hu
  have hi' : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul a hu
  have hu' : IsUnit (a⁻¹).det := by
    have := congrArg Matrix.det hi
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact IsUnit.of_mul_eq_one _ (by rwa [mul_comm] at this)
  have hc : ((a⁻¹).map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ *
      (a.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ = 1 := by
    rw [← Matrix.transpose_mul]
    have hm : (a * a⁻¹).map (D.sp.cm.sig : D.host.E → D.host.E) =
        a.map (D.sp.cm.sig : D.host.E → D.host.E) * (a⁻¹).map (D.sp.cm.sig : D.host.E → D.host.E) :=
      Matrix.map_mul (f := (D.sp.cm.sig : D.host.E →+* D.host.E))
    rw [← hm, hi, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  { toFun := fun x => ⟨x.1 * a, by
      rw [Matrix.rank_mul_eq_left_of_isUnit_det a x.1 hu]
      exact x.2.1, by
      rw [gramQ_mul_right, x.2.2]; rfl⟩
    invFun := fun x => ⟨x.1 * a⁻¹, by
      rw [Matrix.rank_mul_eq_left_of_isUnit_det a⁻¹ x.1 hu']
      exact x.2.1, by
      rw [gramQ_mul_right, x.2.2]
      change ((a⁻¹).map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ *
        ((a.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ * β.1 * a) * a⁻¹ = β.1
      calc _ = (((a⁻¹).map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ *
              (a.map (D.sp.cm.sig : D.host.E → D.host.E))ᵀ) * β.1 * (a * a⁻¹) := by
            simp only [Matrix.mul_assoc]
        _ = β.1 := by rw [hc, hi, Matrix.one_mul, Matrix.mul_one]⟩
    left_inv := fun x => Subtype.ext (by
      change x.1 * a * a⁻¹ = x.1
      rw [Matrix.mul_assoc, hi, Matrix.mul_one])
    right_inv := fun x => Subtype.ext (by
      change x.1 * a⁻¹ * a = x.1
      rw [Matrix.mul_assoc, hi', Matrix.mul_one]) }

theorem ifrB_congrH : ∀ (D : D7) (V : HSp D) (ν : Measure (GA D V)) (r : ℕ) (φ : Mx D V.rank r → ℂ) (β : HermE D r)
    (a : Matrix (Fin r) (Fin r) D.host.E), a.det ≠ 0 →
    IfrB V ν φ (GlobalTheory.CompanionTheory.WeilSiegel.Deg.congrH a β) = IfrB V ν (pull a φ) β := by
  intro D V ν r φ β a ha
  have key : (fun h : GA D V => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E //
        x.rank = r ∧ gramQ V x = (congrH a β).1},
        φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D)))) =
      (fun h : GA D V => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E //
        x.rank = r ∧ gramQ V x = β.1},
        pull a φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D)))) := by
    funext h
    rw [← (congrEquiv D V β a ha).tsum_eq]
    refine tsum_congr fun x => ?_
    have hm : (x.1 * a).map (incA D) = HMul.hMul (x.1.map (incA D)) (a.map (incA D)) :=
      Matrix.map_mul (f := incA D)
    change φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) ((x.1 * a).map (incA D))) =
      φ (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D))) (a.map (incA D)))
    rw [hm, Matrix.mul_assoc]
  unfold IfrB
  rw [key]

end GlobalTheory.CompanionTheory.WeilSiegel.Deg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralCongruenceInvariantStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_integral_congruence_invariant : ∀ (D : D7) (V : HSp D) (ν : Measure (GA D V)) (r : ℕ) (φ : Mx D V.rank r → ℂ) (β : HermE D r) (a : Matrix (Fin r) (Fin r) D.host.E), a.det ≠ 0 → IfrB V ν φ (GlobalTheory.CompanionTheory.WeilSiegel.Deg.congrH a β) = IfrB V ν (pull a φ) β := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Deg.ifrB_congrH | exact GlobalTheory.CompanionTheory.WeilSiegel.Deg.ifrB_congrH | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Deg.ifrB_congrH <;> assumption)
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.SiegelWeilRankCoefficient
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.BlockCoefficientLocalGlobalFactor
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.AdelicSiegelWeilCoefficientEq
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.HermitianLatticeMemIffEntries
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hermitian_lattice_mem_iff_entries : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite, ∀ Y : HermR (Fv F v) σ n, Y ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.latH σ b v n ↔ (fun a i => (Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a i) ∈ (latV (M := n) (n := n) b v : Set (Fin n → Fin n → Fv F v ⊗[F] E)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.LatCmp.latH_iff_latV | exact GlobalTheory.CompanionTheory.SiegelND.Coef.LatCmp.latH_iff_latV
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.AdelicSiegelWeilCoefficientEq
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.Coefs

theorem mem_gramNear_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (R : Type) [CommRing R] [Algebra F R] {n : ℕ} (c : HermR R σ n) (U : Set (HermR R σ n)) (X : Fin n → Fin M → R ⊗[F] E) :
    X ∈ gramNear R σ J c U ↔ c - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ R X ∈ U := by
  constructor
  · rintro ⟨u, hu, e⟩
    have : c - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ R X = u := Subtype.ext e
    rwa [this]
  · intro h
    exact ⟨_, h, rfl⟩

theorem gramTest_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (R : Type) [CommRing R] [Algebra F R] {n : ℕ} (c : HermR R σ n) (ρ : HermR R σ n → ℝ) (X : Fin n → Fin M → R ⊗[F] E) :
    gramTest R σ J c ρ X = ρ (c - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ R X) := by
  have h : (c : Matrix (Fin n) (Fin n) (R ⊗[F] E)) - gramR R σ J X ∈ HermR R σ n :=
    (c - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ R X).2
  unfold gramTest
  exact dif_pos h

theorem hermMap_sub_gramH {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R') {n : ℕ} (c : HermR R σ n) (X : Fin n → Fin M → R ⊗[F] E) :
    GlobalTheory.CompanionTheory.SiegelND.Coef.hermMap f σ (c - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ R X) =
      GlobalTheory.CompanionTheory.SiegelND.Coef.hermMap f σ c - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ R' (fun a i => Algebra.TensorProduct.map f (AlgHom.id F E) (X a i)) := by
  rw [GlobalTheory.CompanionTheory.SiegelND.Coef.hermMap_sub, GlobalTheory.CompanionTheory.SiegelND.Coef.hermMap_gramH]

theorem hermMap_hermOf' {F E : Type} [Field F] [Field E] [Algebra F E] {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R') (σ : E →ₐ[F] E) {n : ℕ} (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c) :
    GlobalTheory.CompanionTheory.SiegelND.Coef.hermMap f σ (hermOf R σ T hT) = hermOf R' σ T hT :=
  GlobalTheory.CompanionTheory.SiegelND.Coef.hermMap_hermOf f σ T hT

theorem hermV_sub_gram {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) {n : ℕ} (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c) (x : Fin n → Fin M → AF F ⊗[F] E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    GlobalTheory.CompanionTheory.SiegelND.Coef.hermV σ v (GlobalTheory.CompanionTheory.SiegelND.Coef.hermFin σ (hermOf (AF F) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (AF F) x)) =
      hermOf (Fv F v) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Fv F v) (HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin x)) := by
  unfold GlobalTheory.CompanionTheory.SiegelND.Coef.hermV GlobalTheory.CompanionTheory.SiegelND.Coef.hermFin
  rw [hermMap_sub_gramH hCM hJ, hermMap_sub_gramH hCM hJ, hermMap_hermOf', hermMap_hermOf']
  rfl

theorem hermInf_sub_gram {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) {n : ℕ} (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c) (x : Fin n → Fin M → AF F ⊗[F] E) :
    GlobalTheory.CompanionTheory.SiegelND.Coef.hermInf σ (hermOf (AF F) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (AF F) x) =
      hermOf (Ainf F) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Ainf F) (HeckeCharacterZeroLocus.SiegelWeilU.projInf x) := by
  unfold GlobalTheory.CompanionTheory.SiegelND.Coef.hermInf
  rw [hermMap_sub_gramH hCM hJ, hermMap_hermOf']
  rfl

theorem hermV_entries {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} (B : HermR (AF F) σ n) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    (fun a i => (GlobalTheory.CompanionTheory.SiegelND.Coef.hermV σ v (GlobalTheory.CompanionTheory.SiegelND.Coef.hermFin σ B) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a i) =
      HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin (fun a i => (B : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) a i)) := rfl

theorem mem_intH_iff {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {d n : ℕ} (b : Module.Basis (Fin d) F E) (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) (B : HermR (AF F) σ n)
    (h3 : ∀ v, v ∉ S → ∀ Y : HermR (Fv F v) σ n, Y ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.latH σ b v n ↔
      (fun a i => (Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a i) ∈ (latV (M := n) (n := n) b v : Set (Fin n → Fin n → Fv F v ⊗[F] E))) :
    B ∈ intH σ b S ↔ GlobalTheory.CompanionTheory.SiegelND.Coef.hermFin σ B ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.intH σ b n S := by
  constructor
  · intro h v hv
    have hh : HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin (fun a i => (B : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) a i)) ∈ (latV (M := n) (n := n) b v : Set (Fin n → Fin n → Fv F v ⊗[F] E)) := h v hv
    rw [← hermV_entries] at hh
    exact (h3 v hv _).2 hh
  · intro h v hv
    have hh := (h3 v hv _).1 (h v hv)
    rw [hermV_entries] at hh
    exact hh

theorem indicator_intH {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {d n : ℕ} (b : Module.Basis (Fin d) F E) (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) (B : HermR (AF F) σ n)
    (h3 : ∀ v, v ∉ S → ∀ Y : HermR (Fv F v) σ n, Y ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.latH σ b v n ↔
      (fun a i => (Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a i) ∈ (latV (M := n) (n := n) b v : Set (Fin n → Fin n → Fv F v ⊗[F] E))) :
    (intH σ b S).indicator (fun _ => (1 : ℂ)) B =
      (GlobalTheory.CompanionTheory.SiegelND.Coef.intH σ b n S).indicator (fun _ => (1 : ℂ)) (GlobalTheory.CompanionTheory.SiegelND.Coef.hermFin σ B) := by
  classical
  have hiff := mem_intH_iff b S B h3
  by_cases h : B ∈ intH σ b S
  · exact (Set.indicator_of_mem h (fun _ => (1 : ℂ))).trans (Set.indicator_of_mem (hiff.1 h) (fun _ => (1 : ℂ))).symm
  · exact (Set.indicator_of_notMem h (fun _ => (1 : ℂ))).trans (Set.indicator_of_notMem (fun h' => h (hiff.2 h')) (fun _ => (1 : ℂ))).symm

theorem measurable_gramTest {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) {n : ℕ} (c : HermR (Ainf F) σ n) (ρ : HermR (Ainf F) σ n → ℝ) (hρ : Continuous ρ) :
    Measurable (gramTest (Ainf F) σ J c ρ) := by
  obtain ⟨a1, a2, a3, a4, -⟩ := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1
  haveI := a1; haveI := a2; haveI := a3; haveI := a4
  obtain ⟨t1, -, -, -, -, -, -, hB, -, hG⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Ainf F)
  haveI := t1
  haveI := hB n M
  have e : gramTest (Ainf F) σ J c ρ = fun X => ρ (c - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Ainf F) X) :=
    funext (gramTest_eq hCM hJ (Ainf F) c ρ)
  rw [e]
  have hc : Continuous fun X : Fin n → Fin M → Ainf F ⊗[F] E => c - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Ainf F) X :=
    Continuous.subtype_mk (continuous_const.sub (hG n M J)) _
  exact (hρ.comp hc).measurable

theorem sfinite_herm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {n : ℕ} (db : Measure (HermR (AF F) σ n)) (h : db.IsAddHaarMeasure) : SFinite db := by
  obtain ⟨⟨a1, a2, a3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨t1, t2, t3, t4, -, -, -, -, hC, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI : IsTopologicalRing (AF F ⊗[F] E) := t1
  haveI : LocallyCompactSpace (AF F ⊗[F] E) := t2
  haveI : SecondCountableTopology (AF F ⊗[F] E) := t3
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AF F ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AF F ⊗[F] E))
  haveI : LocallyCompactSpace (HermR (AF F) σ n) := (hC n).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (HermR (AF F) σ n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaCompactSpace (HermR (AF F) σ n) := inferInstance
  haveI := h
  haveI := Measure.IsAddHaarMeasure.sigmaFinite db
  infer_instance


set_option maxHeartbeats 600000 in
theorem coefS_pure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx → ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) → ∀ (minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E)), IsGramFibFree (Ainf F) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) minf → ∀ (m : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFibFree (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n) (m v)) → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c), ∃ S₁ : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), ∀ S, S₁ ⊆ S → ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzArch φ → ∀ A : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (Fin n → Fin M → Fv F v ⊗[F] E), (∀ v, IsCompact (A v) ∧ IsOpen (A v)) → (∀ v, v ∉ S → A v = latV b v) → coefS σ J ψ dx db (pureN φ A) T b S = (∫ X, φ X ∂(minf (hermOf (Ainf F) σ T hT))) * ∏ v ∈ S, ((m v (hermOf (Fv F v) σ T hT) (A v)).toReal : ℂ) := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn h2n ψ hψ dx hdx db hdb d b laminf lam hinf hlam minf hminf m hm T hT
  classical
  obtain ⟨hEu, hlat⟩ := GlobalTheory.T.siegel_weil_product_over_places F E σ hCM M J hJ n hn h2n ψ hψ dx hdx d b laminf lam hinf hlam
  obtain ⟨S₀, hS₀⟩ := GlobalTheory.T.euler_product_almost_all_standard F E M n d b dx 1 _ _ hEu
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.hermitian_euler_product_standard F E σ hCM n hn ψ hψ db hdb d b laminf lam hinf hlam
  have hq := GlobalTheory.T.lattice_gram_integral_almost_all F E σ hCM M J hJ n d b T hT
  have hlc := GlobalTheory.T.hermitian_lattice_mem_iff_entries F E σ hCM n d b
  have hqf := Filter.eventually_cofinite.1 hq
  have hlf := Filter.eventually_cofinite.1 hlc
  refine ⟨S₀ ∪ S₁ ∪ hqf.toFinset ∪ hlf.toFinset, fun S hS φ hφ A hA hAl => ?_⟩
  have hS0 : S₀ ⊆ S := fun x hx => hS (by simp [hx])
  have hS1 : S₁ ⊆ S := fun x hx => hS (by simp [hx])
  have hS2 : ∀ v, v ∉ S → ∀ X ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)),
      hermOf (Fv F v) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Fv F v) X ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.latH σ b v n := by
    intro v hv
    by_contra hc
    exact hv (hS (by simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq]; exact Or.inl (Or.inr hc)))
  have hS3 : ∀ v, v ∉ S → ∀ Y : HermR (Fv F v) σ n, Y ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.latH σ b v n ↔
      (fun a i => (Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a i) ∈ (latV (M := n) (n := n) b v : Set (Fin n → Fin n → Fv F v ⊗[F] E)) := by
    intro v hv
    by_contra hc
    exact hv (hS (by simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq]; exact Or.inr hc))
  obtain ⟨ρ, U, hρ, hρs, hU, hUs, hUpos, hI, hc, hbd, hlim⟩ := hS₁ S hS1
  have hΦSB : GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (pureN φ A) :=
    GlobalTheory.T.factorizable_siegel_weil_finite_set F E σ hCM M J hJ n hn h2n d b S φ A hφ hA hAl
  have hΦdx : Integrable (pureN φ A) dx := GlobalTheory.T.schwartz_bruhat_integrable_any_haar F E σ hCM M n dx hdx.1 _ hΦSB
  have hstar : Integrable (starN σ J ψ dx (pureN φ A)) db :=
    GlobalTheory.T.siegel_weil_convergent_range F E σ hCM M J hJ n h2n ψ hψ dx hdx db hdb _ hΦSB
  have hsd := hdx.1
  have hdb1 := hdb.1
  haveI : SFinite dx := by infer_instance
  haveI : SFinite db := sfinite_herm hCM db hdb1
  set cI : HermR (Ainf F) σ n := hermOf (Ainf F) σ T hT with hcI
  have hInf := GlobalTheory.T.archimedean_siegel_weil_measure F E σ hCM M J hJ n hn h2n d b laminf hinf minf hminf cI φ hφ
  obtain ⟨hφm, -, hInf⟩ := hInf
  have hInf := hInf ρ hρ hρs
  have hV0 := fun v => GlobalTheory.T.local_siegel_weil_unramified_measure F E σ hCM M J hJ n hn h2n d b v (lam v) (hlam v) (m v) (hm v)
    (hermOf (Fv F v) σ T hT) (A v) (hA v).1 (hA v).2
  have hV := fun v => (hV0 v).2.2 (fun k => U k v) (fun k => hU k v) (hUs v)
  have hρpos : ∀ k, 0 < ∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) := fun k => (hρ k).2.2.2
  have hck : ∀ k, (∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db) ≠ 0 := by
    intro k
    rw [hc k]
    refine mul_ne_zero (by exact_mod_cast (hρpos k).ne') (Finset.prod_ne_zero_iff.2 fun v _ => ?_)
    exact_mod_cast (hUpos k v).ne'
  have hfub := fun k => GlobalTheory.T.fubini_fourier_hermitian_integral F E σ M J hJ n hCM ψ hψ dx db inferInstance inferInstance _ hΦdx
      (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) (hI k).1 (hI k).2 T hT
  have hchi : Continuous (GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T) := (hfub 0).1
  have hφ'm : ∀ k, Measurable (fun X => φ X * (gramTest (Ainf F) σ J cI (ρ k) X : ℂ)) := by
    intro k
    exact hφm.mul (Complex.measurable_ofReal.comp (measurable_gramTest hCM hJ cI (ρ k) (hρ k).1))
  have key : ∀ k, ∫ B, (GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) B / ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db) *
        (starN σ J ψ dx (pureN φ A) B * GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T B) ∂db =
      ((∫ X, φ X * (gramTest (Ainf F) σ J cI (ρ k) X : ℂ) ∂(GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M)) /
          ((∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) : ℝ) : ℂ)) *
        ∏ v ∈ S, (((GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M
          (A v ∩ gramNear (Fv F v) σ J (hermOf (Fv F v) σ T hT) (U k v))).toReal /
            (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (U k v)).toReal : ℝ) : ℂ) := by
    intro k
    have hf := (hfub k).2
    let A' : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (Fin n → Fin M → Fv F v ⊗[F] E) := fun v =>
      if v ∈ S then A v ∩ gramNear (Fv F v) σ J (hermOf (Fv F v) σ T hT) (U k v) else A v
    have hA'S : ∀ v ∈ S, A' v = A v ∩ gramNear (Fv F v) σ J (hermOf (Fv F v) σ T hT) (U k v) :=
      fun v hv => if_pos hv
    have hA'n : ∀ v, v ∉ S → A' v = latV b v := fun v hv => (if_neg hv).trans (hAl v hv)
    have h3 : ∀ (x : Fin n → Fin M → AF F ⊗[F] E) v,
        GlobalTheory.CompanionTheory.SiegelND.Coef.hermV σ v (GlobalTheory.CompanionTheory.SiegelND.Coef.hermFin σ (hermOf (AF F) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (AF F) x)) =
          hermOf (Fv F v) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Fv F v) (HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin x)) := by
      intro x v
      exact hermV_sub_gram hCM hJ T hT x v
    have h0 : ∀ x : Fin n → Fin M → AF F ⊗[F] E,
        GlobalTheory.CompanionTheory.SiegelND.Coef.hermInf σ (hermOf (AF F) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (AF F) x) =
          cI - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Ainf F) (HeckeCharacterZeroLocus.SiegelWeilU.projInf x) := by
      intro x
      exact hermInf_sub_gram hCM hJ T hT x
    have hmem : ∀ x : Fin n → Fin M → AF F ⊗[F] E,
        (HeckeCharacterZeroLocus.SiegelWeilU.projFin x ∈ boxF A ∧ GlobalTheory.CompanionTheory.SiegelND.Coef.hermFin σ (hermOf (AF F) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (AF F) x) ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.boxH σ b n S (U k)) ↔
          HeckeCharacterZeroLocus.SiegelWeilU.projFin x ∈ boxF A' := by
      intro x
      constructor
      · rintro ⟨h, h'⟩ v
        by_cases hv : v ∈ S
        · rw [hA'S v hv]
          refine ⟨h v, ?_⟩
          rw [mem_gramNear_iff hCM hJ, ← h3 x v]
          exact h'.1 v hv
        · rw [show A' v = A v from if_neg hv]
          exact h v
      · intro h
        refine ⟨fun v => ?_, fun v hv => ?_, fun v hv => ?_⟩
        · by_cases hv : v ∈ S
          · have := h v
            rw [hA'S v hv] at this
            exact this.1
          · have := h v
            rwa [show A' v = A v from if_neg hv] at this
        · have := h v
          rw [hA'S v hv] at this
          rw [h3 x v, ← mem_gramNear_iff hCM hJ]
          exact this.2
        · have := h v
          rw [hA'n v hv] at this
          rw [h3 x v]
          exact hS2 v hv _ this
    have hpt : ∀ x, pureN φ A x * GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) (hermOf (AF F) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (AF F) x) =
        pureN (fun X => φ X * (gramTest (Ainf F) σ J cI (ρ k) X : ℂ)) A' x := by
      intro x
      have eR : pureN (fun X => φ X * (gramTest (Ainf F) σ J cI (ρ k) X : ℂ)) A' x =
          (φ (HeckeCharacterZeroLocus.SiegelWeilU.projInf x) * (ρ k (cI - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Ainf F) (HeckeCharacterZeroLocus.SiegelWeilU.projInf x)) : ℂ)) *
            (boxF A').indicator (fun _ => (1 : ℂ)) (HeckeCharacterZeroLocus.SiegelWeilU.projFin x) := by
        show (φ _ * (gramTest (Ainf F) σ J cI (ρ k) _ : ℂ)) * _ = _
        rw [gramTest_eq hCM hJ]
      rw [eR]
      unfold pureN GlobalTheory.CompanionTheory.SiegelND.Coef.testH
      rw [h0 x]
      by_cases h : HeckeCharacterZeroLocus.SiegelWeilU.projFin x ∈ boxF A'
      · obtain ⟨ha, hb⟩ := (hmem x).2 h
        rw [Set.indicator_of_mem ha, Set.indicator_of_mem hb, Set.indicator_of_mem h]
        ring
      · rw [Set.indicator_of_notMem h, mul_zero]
        by_cases ha : HeckeCharacterZeroLocus.SiegelWeilU.projFin x ∈ boxF A
        · have hb : GlobalTheory.CompanionTheory.SiegelND.Coef.hermFin σ (hermOf (AF F) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (AF F) x) ∉ GlobalTheory.CompanionTheory.SiegelND.Coef.boxH σ b n S (U k) :=
            fun hb => h ((hmem x).1 ⟨ha, hb⟩)
          rw [Set.indicator_of_notMem hb]
          simp
        · rw [Set.indicator_of_notMem ha]
          simp
    have hmeasA' : ∀ v, MeasurableSet (A' v) := by
      intro v
      by_cases hv : v ∈ S
      · rw [hA'S v hv]; exact ((hV v).1 k).1
      · rw [show A' v = A v from if_neg hv]; exact (hV0 v).1
    have hfinA' : ∀ v, GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M (A' v) ≠ ⊤ := by
      intro v
      by_cases hv : v ∈ S
      · rw [hA'S v hv]; exact ((hV v).1 k).2
      · rw [hA'n v hv, hlat v]; exact ENNReal.one_ne_top
    have he := (hS₀ S hS0 _ (hφ'm k) (hInf.1 k) A' hmeasA' hfinA' hA'n).2
    have htail : (∏' v : {v // v ∉ S}, (GlobalTheory.CompanionTheory.SW.coordW (Fv F v.1) b (lam v.1) n M (latV b v.1)).toReal) = 1 := by
      simp [hlat]
    rw [htail] at he
    have hprod : (∏ v ∈ S, ((GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M (A' v)).toReal : ℂ)) =
        ∏ v ∈ S, ((GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M
          (A v ∩ gramNear (Fv F v) σ J (hermOf (Fv F v) σ T hT) (U k v))).toReal : ℂ) :=
      Finset.prod_congr rfl fun v hv => by rw [hA'S v hv]
    have e1 : ∫ B, (GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) B / ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db) *
        (starN σ J ψ dx (pureN φ A) B * GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T B) ∂db =
        (∫ B, GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) B *
          (starN σ J ψ dx (pureN φ A) B * GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T B) ∂db) /
          ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db := by
      rw [← integral_div]
      exact integral_congr_ae (Filter.Eventually.of_forall fun bb => by simp only []; ring)
    rw [e1, hf, integral_congr_ae (Filter.Eventually.of_forall hpt), he, hprod, hc k]
    push_cast
    rw [Finset.prod_div_distrib]
    simp only [NNReal.coe_one, Complex.ofReal_one, one_mul, mul_one]
    rw [div_mul_div_comm]
  have hint : ∀ B : HermR (AF F) σ n, (intH σ b S).indicator (fun _ => (1 : ℂ)) B =
      (GlobalTheory.CompanionTheory.SiegelND.Coef.intH σ b n S).indicator (fun _ => (1 : ℂ)) (GlobalTheory.CompanionTheory.SiegelND.Coef.hermFin σ B) := by
    intro B
    exact indicator_intH b S B hS3
  have lim1 : Filter.Tendsto (fun k => ∫ B, (GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) B /
        ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db) *
        (starN σ J ψ dx (pureN φ A) B * GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T B) ∂db) Filter.atTop
      (nhds (coefS σ J ψ dx db (pureN φ A) T b S)) := by
    have hcs : coefS σ J ψ dx db (pureN φ A) T b S = ∫ B, (GlobalTheory.CompanionTheory.SiegelND.Coef.intH σ b n S).indicator (fun _ => (1 : ℂ)) (GlobalTheory.CompanionTheory.SiegelND.Coef.hermFin σ B) *
        (starN σ J ψ dx (pureN φ A) B * GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T B) ∂db := by
      unfold coefS
      exact integral_congr_ae (Filter.Eventually.of_forall fun B => by
        simp only [hint B]
        rfl)
    rw [hcs]
    have hnorm : ∀ B, ‖GlobalTheory.CompanionTheory.SiegelND.Coef.chiT σ ψ T B‖ = 1 := fun B => hψ.2.1 _
    refine tendsto_integral_of_dominated_convergence (fun B => ‖starN σ J ψ dx (pureN φ A) B‖) ?_ hstar.norm ?_ ?_
    · intro k
      exact ((hI k).1.div_const _).aestronglyMeasurable.mul (hstar.aestronglyMeasurable.mul hchi.aestronglyMeasurable)
    · intro k
      refine Filter.Eventually.of_forall fun B => ?_
      rw [norm_mul, norm_mul, hnorm, mul_one, norm_div]
      exact mul_le_of_le_one_left (norm_nonneg _)
        ((div_le_one (norm_pos_iff.2 (hck k))).2 (hbd k B))
    · refine Filter.Eventually.of_forall fun B => ?_
      exact (hlim B).mul_const _
  have lim2 := hInf.2.mul (tendsto_finsetProd S fun v _ =>
    (Complex.continuous_ofReal.tendsto _).comp (hV v).2)
  exact tendsto_nhds_unique lim1 (lim2.congr fun k => by simpa using (key k).symm)

end GlobalTheory.CompanionTheory.WhitFree.Coefs
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.AdelicSiegelWeilCoefficientEqStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adelic_siegelWeil_coefficient_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx → ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) → ∀ (minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E)), IsGramFibFree (Ainf F) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) minf → ∀ (m : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFibFree (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n) (m v)) → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c), ∃ S₁ : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), ∀ S, S₁ ⊆ S → ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzArch φ → ∀ A : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (Fin n → Fin M → Fv F v ⊗[F] E), (∀ v, IsCompact (A v) ∧ IsOpen (A v)) → (∀ v, v ∉ S → A v = latV b v) → coefS σ J ψ dx db (pureN φ A) T b S = (∫ X, φ X ∂(minf (hermOf (Ainf F) σ T hT))) * ∏ v ∈ S, ((m v (hermOf (Fv F v) σ T hT) (A v)).toReal : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.Coefs.coefS_pure | exact GlobalTheory.CompanionTheory.WhitFree.Coefs.coefS_pure
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.BlockCoefficientLocalGlobalFactor
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WhitFree

theorem pure_identity {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    {n : ℕ} (hn : 0 < n) (hM : 2 * n < M) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ)
    (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (hdx : SdW F E σ M J (AF F) ψ n dx)
    (db : Measure (HermR (AF F) σ n)) (hdb : SdHerm F E σ (AF F) ψ n db)
    (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F))
    (lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Measure (Fv F v))
    (hinf : GlobalTheory.CompanionTheory.SW.IsStdInf laminf) (hlam : ∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v))
    (minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (hminf : IsGramFibFree (Ainf F) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M)
      (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) minf)
    (m : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), HermR (Fv F v) σ n →
      Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (hm : ∀ v, IsGramFibFree (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M)
      (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n) (m v))
    (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c)
    (I : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (hI : GlobalTheory.CompanionTheory.SW.IsEulerProd b I 1 (minf (hermOf (Ainf F) σ T hT)) (fun v => m v (hermOf (Fv F v) σ T hT)))
    (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (hφ : GlobalTheory.Published.SiegelOneVector.IsSchwartzArch φ)
    (A : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hA : ∀ v, IsCompact (A v) ∧ IsOpen (A v)) (hAl : ∀ v, v ∉ S₀ → A v = latV b v) :
    Integrable (pureN φ A) I ∧ coefN σ J ψ dx db (pureN φ A) T = ∫ X, pureN φ A X ∂I := by
  classical
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.euler_product_almost_all_standard F E M n d b I 1 _ _ hI
  obtain ⟨S₂, hS₂⟩ := GlobalTheory.T.adelic_siegelWeil_coefficient_eq F E σ hCM M J hJ n hn hM ψ hψ dx hdx db hdb d b laminf lam hinf hlam minf hminf m hm T hT
  obtain ⟨hφm, hφi, -⟩ := GlobalTheory.T.archimedean_siegel_weil_measure F E σ hCM M J hJ n hn hM d b laminf hinf minf hminf (hermOf (Ainf F) σ T hT) φ hφ
  have hfin := fun v => GlobalTheory.T.local_siegel_weil_unramified_measure F E σ hCM M J hJ n hn hM d b v (lam v) (hlam v) (m v) (hm v)
    (hermOf (Fv F v) σ T hT) (A v) (hA v).1 (hA v).2
  have hΦSB : GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (pureN φ A) :=
    GlobalTheory.T.factorizable_siegel_weil_finite_set F E σ hCM M J hJ n hn hM d b S₀ φ A hφ hA hAl
  have hstar : Integrable (starN σ J ψ dx (pureN φ A)) db :=
    GlobalTheory.T.siegel_weil_convergent_range F E σ hCM M J hJ n hM ψ hψ dx hdx db hdb _ hΦSB
  have hlimC := GlobalTheory.T.siegel_weil_stabilizer_integrable F E σ hCM M J hJ n hn hM ψ hψ dx db d b _ hstar T
  have htail := GlobalTheory.T.tendsto_tail_infinite_product_one _ hI.2.1
  have hev : ∀ᶠ S in Filter.atTop, S₀ ∪ S₁ ∪ S₂ ⊆ S := Filter.eventually_ge_atTop _
  obtain ⟨Sb, hSb⟩ : ∃ S, S₀ ∪ S₁ ∪ S₂ ⊆ S := ⟨_, subset_rfl⟩
  have hEu : ∀ S, S₀ ∪ S₁ ∪ S₂ ⊆ S → Integrable (pureN φ A) I ∧ ∫ X, pureN φ A X ∂I = ((1 : NNReal) : ℂ) * (∫ X, φ X ∂(minf (hermOf (Ainf F) σ T hT))) *
      (∏ v ∈ S, ((m v (hermOf (Fv F v) σ T hT) (A v)).toReal : ℂ)) *
      ((∏' v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal : ℝ) : ℂ) := by
    intro S hS
    have hs0 : S₀ ⊆ S := fun x hx => hS (by simp [hx])
    have hs1 : S₁ ⊆ S := fun x hx => hS (by simp [hx])
    exact hS₁ S hs1 φ hφm hφi A (fun v => (hfin v).1) (fun v => (hfin v).2.1)
      (fun v hv => hAl v fun h => hv (hs0 h))
  refine ⟨(hEu Sb hSb).1, ?_⟩
  have hlim2 : Filter.Tendsto (fun S => coefS σ J ψ dx db (pureN φ A) T b S *
      ((∏' v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal : ℝ) : ℂ))
      Filter.atTop (nhds (coefN σ J ψ dx db (pureN φ A) T * ((1 : ℝ) : ℂ))) :=
    hlimC.mul ((Complex.continuous_ofReal.tendsto _).comp htail)
  have hconst : ∀ᶠ S in Filter.atTop, coefS σ J ψ dx db (pureN φ A) T b S *
      ((∏' v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal : ℝ) : ℂ) =
      ∫ X, pureN φ A X ∂I := by
    filter_upwards [hev] with S hS
    have hs0 : S₀ ⊆ S := fun x hx => hS (by simp [hx])
    have hs2 : S₂ ⊆ S := fun x hx => hS (by simp [hx])
    rw [hS₂ S hs2 φ hφ A hA (fun v hv => hAl v fun h => hv (hs0 h)), (hEu S hS).2]
    simp
  have := tendsto_nhds_unique (hlim2.congr' hconst) tendsto_const_nhds
  simpa using this

theorem coefN_eq_integral {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    {n : ℕ} (hn : 0 < n) (hM : 2 * n < M) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ)
    (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (hdx : SdW F E σ M J (AF F) ψ n dx)
    (db : Measure (HermR (AF F) σ n)) (hdb : SdHerm F E σ (AF F) ψ n db)
    (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F))
    (lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Measure (Fv F v))
    (hinf : GlobalTheory.CompanionTheory.SW.IsStdInf laminf) (hlam : ∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v))
    (minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (hminf : IsGramFibFree (Ainf F) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M)
      (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) minf)
    (m : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), HermR (Fv F v) σ n →
      Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (hm : ∀ v, IsGramFibFree (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M)
      (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n) (m v))
    (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c)
    (I : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (hI : GlobalTheory.CompanionTheory.SW.IsEulerProd b I 1 (minf (hermOf (Ainf F) σ T hT)) (fun v => m v (hermOf (Fv F v) σ T hT)))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (hΦ : GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ) :
    coefN σ J ψ dx db Φ T = ∫ X, Φ X ∂I := by
  obtain ⟨k, φ, A, S, hφ, hA, hAl, hsum⟩ := GlobalTheory.T.schwartz_bruhat_factorizable_decomposition F E σ hCM M J hJ n hn hM d b Φ hΦ
  have hSB : ∀ i, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (pureN (φ i) (A i)) := fun i =>
    GlobalTheory.T.factorizable_siegel_weil_finite_set F E σ hCM M J hJ n hn hM d b S (φ i) (A i) (hφ i) (hA i) (hAl i)
  have hP := fun i => pure_identity σ hCM J hJ hn hM ψ hψ dx hdx db hdb d b laminf lam hinf hlam minf hminf m hm T hT I hI S
    (φ i) (hφ i) (A i) (hA i) (hAl i)
  have hΦe : Φ = fun X => ∑ i, pureN (φ i) (A i) X := funext hsum
  rw [hΦe, GlobalTheory.T.siegel_weil_orbital_integral_formula F E σ hCM M J hJ n hn hM ψ hψ dx hdx db hdb T k _ hSB, integral_finsetSum _ fun i _ => (hP i).1]
  exact Finset.sum_congr rfl fun i _ => (hP i).2

end GlobalTheory.CompanionTheory.WhitFree

namespace GlobalTheory.CompanionTheory.WhitFree

theorem whit_eq_integral : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (ν : Measure (GA D V)) (φ : Mx D V.rank r → ℂ), Hyp D r V ψ θ μ lam ν φ → ∀ (t : ℕ) (β : HermE D r), GlobalTheory.CompanionTheory.WeilSiegel.Deg.IsBlockNF t β → ∀ (d : ℕ) (b : Module.Basis (Fin d) D.host.F D.host.E) (laminf : Measure (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F)) (lamv : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F), Measure (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v)) (minf : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) D.sp.cm.sig r → Measure (Fin r → Fin V.rank → HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F ⊗[D.host.F] D.host.E)) (m : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F), HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) D.sp.cm.sig r → Measure (Fin r → Fin V.rank → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lamv v)) → IsGramFibFree (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) D.sp.cm.sig V.gram r (GlobalTheory.CompanionTheory.SW.coordW (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) b laminf r V.rank) (GlobalTheory.CompanionTheory.SW.coordHerm (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) D.sp.cm.sig b laminf r) minf → (∀ v, IsGramFibFree (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) D.sp.cm.sig V.gram r (GlobalTheory.CompanionTheory.SW.coordW (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) b (lamv v) r V.rank) (GlobalTheory.CompanionTheory.SW.coordHerm (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) D.sp.cm.sig b (lamv v) r) (m v)) → ∀ I : Measure (Fin r → Fin V.rank → AE D), GlobalTheory.CompanionTheory.SW.IsEulerProd b I 1 (minf (HeckeCharacterZeroLocus.SiegelWeilU.hermOf (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) D.sp.cm.sig β.1 (hermE_symm β))) (fun v => m v (HeckeCharacterZeroLocus.SiegelWeilU.hermOf (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) D.sp.cm.sig β.1 (hermE_symm β))) → Integrable (fun X => φ (trM X)) I → W ψ V μ lam φ β = ∫ X, φ (trM X) ∂I := by
  intro D r V ψ θ μ lam ν φ hyp t β hβ d b laminf lamv minf m hinf hlamv hminf hm I hI _
  obtain ⟨hr, hψ, hθ, hμ, hlam, -, hφ, -⟩ := hyp
  have hCM := GlobalTheory.DefiniteQuotient.cmExt D
  have hJ := GlobalTheory.DefiniteQuotient.gram_hermND V
  obtain ⟨dx, db, hdx, hdb, hW⟩ := GlobalTheory.T.exists_self_dual_siegel_weil_measures D r V ψ hψ μ hμ lam hlam
  obtain ⟨ht, -⟩ := hβ
  rw [hW φ β]
  exact coefN_eq_integral D.sp.cm.sig hCM V.gram hJ (by omega) hr ψ hψ dx hdx db hdb d b laminf lamv hinf hlamv minf hminf
    m hm β.1 (hermE_symm β) I hI _ (GlobalTheory.T.schwartz_function_schwartz_bruhat D θ hθ V.rank r φ hφ)

end GlobalTheory.CompanionTheory.WhitFree
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.BlockCoefficientLocalGlobalFactorStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.block_coefficient_local_global_factor : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (ν : Measure (GA D V)) (φ : Mx D V.rank r → ℂ), Hyp D r V ψ θ μ lam ν φ → ∀ (t : ℕ) (β : HermE D r), GlobalTheory.CompanionTheory.WeilSiegel.Deg.IsBlockNF t β → ∀ (d : ℕ) (b : Module.Basis (Fin d) D.host.F D.host.E) (laminf : Measure (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F)) (lamv : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F), Measure (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v)) (minf : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) D.sp.cm.sig r → Measure (Fin r → Fin V.rank → HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F ⊗[D.host.F] D.host.E)) (m : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F), HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) D.sp.cm.sig r → Measure (Fin r → Fin V.rank → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lamv v)) → IsGramFibFree (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) D.sp.cm.sig V.gram r (GlobalTheory.CompanionTheory.SW.coordW (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) b laminf r V.rank) (GlobalTheory.CompanionTheory.SW.coordHerm (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) D.sp.cm.sig b laminf r) minf → (∀ v, IsGramFibFree (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) D.sp.cm.sig V.gram r (GlobalTheory.CompanionTheory.SW.coordW (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) b (lamv v) r V.rank) (GlobalTheory.CompanionTheory.SW.coordHerm (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) D.sp.cm.sig b (lamv v) r) (m v)) → ∀ I : Measure (Fin r → Fin V.rank → AE D), GlobalTheory.CompanionTheory.SW.IsEulerProd b I 1 (minf (HeckeCharacterZeroLocus.SiegelWeilU.hermOf (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) D.sp.cm.sig β.1 (hermE_symm β))) (fun v => m v (HeckeCharacterZeroLocus.SiegelWeilU.hermOf (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) D.sp.cm.sig β.1 (hermE_symm β))) → Integrable (fun X => φ (trM X)) I → W ψ V μ lam φ β = ∫ X, φ (trM X) ∂I := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.whit_eq_integral | exact GlobalTheory.CompanionTheory.WhitFree.whit_eq_integral
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.SiegelWeilRankCoefficient
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WeilSiegel.Frame

theorem siegel_frame : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (ν : Measure (GA D V)) (φ : Mx D V.rank r → ℂ), Hyp D r V ψ θ μ lam ν φ → ∀ (t : ℕ) (β : HermE D r), GlobalTheory.CompanionTheory.WeilSiegel.Deg.IsBlockNF t β → (∃ x : Matrix (Fin V.rank) (Fin r) D.host.E, x.rank = r ∧ gramQ V x = β.1) → IfrB V ν φ β = W ψ V μ lam φ β := by
  intro D r V ψ θ μ lam ν φ hH t β hNF hx
  obtain ⟨hr, hψ, hθ, hμ, hlam, hν, hφ, habs⟩ := id hH
  obtain ⟨x, hxr, hxg⟩ := hx
  have hCM : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt D.host.F D.host.E D.sp.cm.sig := Formalism.MainNotions.UnusedSlot34.isCMExt_D D
  have hJ : HeckeCharacterZeroLocus.SiegelWeilU.IsHermND D.sp.cm.sig V.gram := isHermND_gram V
  obtain ⟨⟨𝓕, h𝓕⟩, -⟩ := GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram ν hν
  have hfr : (framesE D.sp.cm.sig V.gram β.1).Nonempty := by
    refine ⟨fun a i => x i a, ?_⟩
    rw [trM_mem_framesE_iff]
    exact ⟨hxr, hxg⟩
  obtain ⟨d, b, laminf, lamv, minf, m, h1, h2, h3, h4⟩ :=
    GlobalTheory.T.exists_tamagawa_measure_normalization D.host.F D.host.E D.sp.cm.sig hCM V.rank V.gram hJ r
  have hS := GlobalTheory.T.siegelWeil_free_of_block_nonempty_frames D.host.F D.host.E D.sp.cm.sig hCM V.rank V.gram hJ r t β.1 (hermE_symm β) hNF hr hfr
    d b laminf lamv h1 h2 ν 𝓕 hν h𝓕 minf m h3 h4
  obtain ⟨hi, he⟩ := GlobalTheory.T.frame_integral_theta_measure_formula D r V θ hθ ν hν 𝓕 h𝓕 φ hφ habs β
  rw [he]
  exact (GlobalTheory.T.block_coefficient_local_global_factor D r V ψ θ μ lam ν φ hH t β hNF d b laminf lamv minf m h1 h2 h3 h4 _ hS hi).symm

end GlobalTheory.CompanionTheory.WeilSiegel.Frame
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.SiegelWeilRankCoefficientStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.siegel_weil_rank_coefficient : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (ν : Measure (GA D V)) (φ : Mx D V.rank r → ℂ), Hyp D r V ψ θ μ lam ν φ → ∀ (t : ℕ) (β : HermE D r), GlobalTheory.CompanionTheory.WeilSiegel.Deg.IsBlockNF t β → (∃ x : Matrix (Fin V.rank) (Fin r) D.host.E, x.rank = r ∧ gramQ V x = β.1) → IfrB V ν φ β = W ψ V μ lam φ β := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Frame.siegel_frame | exact GlobalTheory.CompanionTheory.WeilSiegel.Frame.siegel_frame
end
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WeilSiegel.Deg

theorem siegelDeg : PositivityTheory.GramSchwartzFunctions.BC.SiegelDeg := by
  intro D r V ψ θ μ lam ν φ hH β hβ
  obtain ⟨a, t, γ, ha, hγ, rfl⟩ := GlobalTheory.T.singular_hermitian_congruent_block_normal_form D r β hβ
  rw [GlobalTheory.T.frame_integral_congruence_invariant D V ν r φ γ a ha, ← GlobalTheory.T.whittaker_coefficient_congruence_pullback D r V ψ μ lam φ γ a ha hH.2.2.2.1 hH.2.2.2.2.1]
  have hH' := GlobalTheory.T.hypotheses_preserved_by_linear_pullback D r V ψ θ μ lam ν φ a ha hH
  by_cases hx : ∃ x : Matrix (Fin V.rank) (Fin r) D.host.E, x.rank = r ∧ gramQ V x = γ.1
  · exact GlobalTheory.T.siegel_weil_rank_coefficient D r V ψ θ μ lam ν (pull a φ) hH' t γ hγ hx
  · exact GlobalTheory.T.frame_integral_eq_coefficient_nonrepresented D r V ψ θ μ lam ν (pull a φ) hH' t γ hγ hx

end GlobalTheory.CompanionTheory.WeilSiegel.Deg
end

theorem PositivityTheory.Rg.Wsf.weilSiegelFormula : GlobalTheory.Published.WeilSiegelFormula :=
  PositivityTheory.PfWsf.Top.head_of_deg GlobalTheory.CompanionTheory.WeilSiegel.Deg.siegelDeg
