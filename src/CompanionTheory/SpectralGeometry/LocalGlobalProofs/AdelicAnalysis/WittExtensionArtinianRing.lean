module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarMapLinearScalingByDeterminant
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolume

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitChoiceOfIsArtinianRingIsReduced
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem unitChoice_of_isArtinianRing_isReduced :
    ∀ (R : Type) [CommRing R] [IsArtinianRing R] [IsReduced R], PIW.AdelicOrbitU.UnitChoice R := by
  intro R _ _ _ k f hf
  classical
  let φ := IsArtinianRing.equivPi R
  have hex : ∀ I : MaximalSpectrum R, ∃ i, φ (f i) I ≠ 0 := by
    intro I
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    haveI : I.asIdeal.IsMaximal := I.isMaximal
    let ψ : R →+* R ⧸ I.asIdeal :=
      (Pi.evalRingHom (fun J : MaximalSpectrum R => R ⧸ J.asIdeal) I).comp φ.toRingHom
    have hle : Ideal.span (Set.range f) ≤ RingHom.ker ψ := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact (RingHom.mem_ker).2 (h i)
    rw [hf] at hle
    have h1 : ψ 1 = 0 := (RingHom.mem_ker).1 (hle Submodule.mem_top)
    rw [map_one] at h1
    exact one_ne_zero h1
  choose c hc using hex
  let E : Fin k → ∀ I : MaximalSpectrum R, R ⧸ I.asIdeal := fun i I => if c I = i then 1 else 0
  refine ⟨fun i => φ.symm (E i), ?_, ?_, ?_, ?_⟩
  · intro i
    rw [← map_mul]
    apply congrArg φ.symm
    funext I
    by_cases h : c I = i <;> simp [Pi.mul_apply, E, h]
  · intro i j hij
    rw [← map_mul, ← map_zero φ.symm]
    apply congrArg φ.symm
    funext I
    by_cases hi : c I = i
    · simp [Pi.mul_apply, E, hi, hij]
    · simp [Pi.mul_apply, E, hi]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [← map_sum, ← map_one φ.symm]
      apply congrArg φ.symm
      funext I
      simp [Finset.sum_apply, E]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [← isUnit_map_iff φ, map_sum, Pi.isUnit_iff]
      intro I
      have hcomp : (∑ i, φ (φ.symm (E i) * f i)) I = φ (f (c I)) I := by
        simp only [map_mul, AlgEquiv.apply_symm_apply, Finset.sum_apply, Pi.mul_apply, E, ite_mul,
          one_mul, zero_mul, Fintype.sum_ite_eq]
      rw [hcomp]
      haveI : I.asIdeal.IsMaximal := I.isMaximal
      letI := Ideal.Quotient.field I.asIdeal
      exact isUnit_iff_ne_zero.2 (hc I)

end GlobalTheory.CompanionTheory.SW
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionArtinianRing
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.WittTuples

theorem exists_actW_eq_of_gramR_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [IsArtinianRing R] [IsReduced R] (n : ℕ) (X Y : Fin n → Fin M → R ⊗[F] E), gramR R σ J X = gramR R σ J Y → IsUnit (gramR R σ J X).det → ∃ h : HA R σ J, actW R σ J h X = Y := by
  intro F E _ _ _ _ _ σ hCM M J hJ R _ _ _ _ n X Y hXY hdet
  have hσ := HermTop.sigma_sigma hCM
  have hS : cT (sigR R σ) (gramR R σ J X) = gramR R σ J X := by
    ext a b
    exact HermTop.gramR_mem (R := R) hσ hJ.1 X a b
  obtain ⟨g, D, hg⟩ := GlobalTheory.CompanionTheory.SW.exists_diagonal_congr F E σ hCM R n _ hS hdet
  have hgram : ∀ Z : Fin n → Fin M → R ⊗[F] E, gramR R σ J (rmul R Z (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
      cT (sigR R σ) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * gramR R σ J Z * (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    fun Z => (GlobalTheory.CompanionTheory.SW.RMulGram.rmul_gram_facts F E σ hCM R M n J Z g 1).1
  have hX' := (hgram X).trans hg
  have hY' : gramR R σ J (rmul R Y (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
      gramR R σ J (rmul R X (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by
    rw [hgram, hgram, hXY]
  obtain ⟨h, hh⟩ := GlobalTheory.CompanionTheory.SW.WittDiag.trans_diag F E σ hCM R (GlobalTheory.CompanionTheory.SW.unitChoice_of_isArtinianRing_isReduced R) M J hJ n D _ _ hX' hY'
  refine ⟨h, ?_⟩
  have hk : actTup R (HA.mat R σ J h) (rmul R X (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
      rmul R (actTup R (HA.mat R σ J h) X) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    (GlobalTheory.CompanionTheory.SW.RMulGram.rmul_gram_facts F E σ hCM R M n J X g 1).2.2.2 _
  have he : rmul R (actW R σ J h X) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
      rmul R Y (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := hk.symm.trans hh
  have hcancel : ∀ Z : Fin n → Fin M → R ⊗[F] E,
      rmul R (rmul R Z (g : Matrix (Fin n) (Fin n) (R ⊗[F] E))) ((g⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = Z := by
    intro Z
    have h1 := GlobalTheory.CompanionTheory.SW.RMulGram.rmul_gram_facts F E σ hCM R M n J Z g ((g⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))
    rw [h1.2.1, Units.mul_inv, h1.2.2.1]
  rw [← hcancel (actW R σ J h X), he, hcancel]

end GlobalTheory.CompanionTheory.SW.WittTuples
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WittExtensionArtinianRingStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_extension_artinian_ring : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [IsArtinianRing R] [IsReduced R] (n : ℕ) (X Y : Fin n → Fin M → R ⊗[F] E), gramR R σ J X = gramR R σ J Y → IsUnit (gramR R σ J X).det → ∃ h : HA R σ J, actW R σ J h X = Y := by
  first | exact @GlobalTheory.CompanionTheory.SW.WittTuples.exists_actW_eq_of_gramR_eq | exact GlobalTheory.CompanionTheory.SW.WittTuples.exists_actW_eq_of_gramR_eq | (intros; apply GlobalTheory.CompanionTheory.SW.WittTuples.exists_actW_eq_of_gramR_eq <;> assumption)
end
