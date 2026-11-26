module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.MassOneCounts.DensExact
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.MassOneCounts.ZOfSurj
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionFive
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardUnimodularHermitianRepsLevelOne
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.PlugInf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TateIntegralFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterSideEquidistribution
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDensityRatioFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarFibrationFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDensityOfMassOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFormulaOfTotalMassOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinSplitOfNarrow
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LFunctionSideEquidistribution
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIdentityOfLocalDensities
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountingFormulaOfComponents

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianExistencePrinciple
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianExistencePrinciple
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.RgBase

open PositivityTheory.Rg.Base1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem norm_tmul_one {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : AF F ⊗[F] E) :
    (Algebra.norm (AF F) x) ⊗ₜ[F] (1 : E) = sigR (AF F) σ x * x := by
  have e := GlobalTheory.Doubling.algebraMap_norm_eq h (R := AF F) x
  rw [Algebra.TensorProduct.algebraMap_apply] at e
  rw [mul_comm]
  exact e

theorem isNm_iff {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : (AF F ⊗[F] E)ˣ) (a : (AF F)ˣ) :
    IsNm σ x a ↔ Algebra.norm (AF F) (x : AF F ⊗[F] E) = a := by
  have hinj : Function.Injective (fun r : AF F => r ⊗ₜ[F] (1 : E)) :=
    Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective
  unfold IsNm
  rw [← norm_tmul_one h]
  exact ⟨fun e => (hinj e).symm, fun e => by rw [e]⟩

theorem hEx : HEx := by
  intro F E _ _ _ _ _ σ h
  haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩
  refine ⟨(GlobalTheory.IdeleNormChar.normSign (K := F) E).ker, ?_, ?_, ?_⟩
  · intro a
    rw [MonoidHom.mem_ker]
    constructor
    · intro ha
      obtain ⟨t, x, hx⟩ := (GlobalTheory.IdeleNormChar.normSign_eq_one_iff E a).1 ha
      refine ⟨t, x, a / GlobalTheory.QuadSymbol.toUnits F (AdeleRing (𝓞 F) F) t, ?_, ?_⟩
      · exact (isNm_iff h x _).2 (congrArg Units.val hx)
      · exact (mul_div_cancel (GlobalTheory.QuadSymbol.toUnits F (AdeleRing (𝓞 F) F) t) a).symm
    · rintro ⟨t, x, n, hn, rfl⟩
      have h1 : GlobalTheory.IdeleNormChar.normSign E (pr t) = 1 := GlobalTheory.IdeleNormChar.normSign_toUnits E t
      have h2 : GlobalTheory.IdeleNormChar.normSign E n = 1 :=
        GlobalTheory.IdeleNormChar.normSign_of_mem E ⟨x, Units.ext ((isNm_iff h x n).1 hn)⟩
      rw [map_mul, h1, h2, one_mul]
  · refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    filter_upwards [GlobalTheory.IdeleNormChar.eventually_normSign (K := F) E] with a ha
    exact ha
  · obtain ⟨b, hb⟩ := GlobalTheory.IdeleNormChar.exists_normSign_ne_one (K := F) E
    have hr : (GlobalTheory.IdeleNormChar.normSign (K := F) E).range = ⊤ := by
      rw [eq_top_iff]
      intro u _
      rcases Int.units_eq_one_or u with rfl | rfl
      · exact one_mem _
      · exact ⟨b, (Int.units_eq_one_or _).resolve_left hb⟩
    rw [Subgroup.index_ker, hr, Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_units_int]

end GlobalTheory.CompanionTheory.RgBase

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianExistencePrincipleStatement
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_existence_principle : HEx := by
  first | exact @GlobalTheory.CompanionTheory.RgBase.hEx | exact GlobalTheory.CompanionTheory.RgBase.hEx | (intros; apply GlobalTheory.CompanionTheory.RgBase.hEx <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDensityFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDensityFormula
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open PositivityTheory.Rg.Base1 PositivityTheory.SiegelWeilFormula.Densx
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.RankOne

theorem dens : Dens := by
  intro F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hσ hJ hli hlam hμ hF hmi hm S φ A hT
  obtain ⟨hφ, hφc, hφ0, hφU, hA, -⟩ := hT
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨c1, c2, -, c4⟩ := GlobalTheory.CompanionTheory.SW.ArchFibre.fibre_integral (Ainf F)
    (GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hσ.1) hσ hJ b li hli.1 mi hmi φ hφ hφc hφ0 hφU
  have hv : ∀ v ∈ S, Continuous (fun s : Fv F v => (m v (hermScal (Fv F v) σ s) (A v)).toReal) ∧
      HasCompactSupport (fun s : Fv F v => (m v (hermScal (Fv F v) σ s) (A v)).toReal) ∧
      ENNReal.ofReal (∫ s, (m v (hermScal (Fv F v) σ s) (A v)).toReal ∂(lam v)) =
        coordW (Fv F v) b (lam v) 1 1 (A v) := fun v hvS => by
    have : BorelSpace (Fv F v) := ⟨rfl⟩
    exact GlobalTheory.CompanionTheory.SW.FibreCpt.masses_field (Fv F v) (GlobalTheory.T.completion_is_local_ring F v) hσ hJ b (lam v) (hlam v).1
      (m v) (hm v) (A v) (hA v hvS).1 (hA v hvS).2.1 (hA v hvS).2.2
  refine ⟨c1, c2, fun v hvS => ⟨continuous_const.mul (hv v hvS).1, (hv v hvS).2.1.mul_left⟩, ?_⟩
  have hI0 : 0 ≤ ∫ y, Gi mi φ y ∂li :=
    integral_nonneg fun s => integral_nonneg fun X => hφ0 X
  have hJ0 : ∀ v ∈ S, 0 ≤ ∫ s, gv m A v s ∂(lam v) := fun v _ =>
    integral_nonneg fun s => mul_nonneg (NNReal.coe_nonneg _) ENNReal.toReal_nonneg
  have hloc : ∀ v ∈ S, ENNReal.ofReal (∫ s, gv m A v s ∂(lam v)) =
      (cfac E v : ℝ≥0∞) * coordW (Fv F v) b (lam v) 1 1 (A v) := fun v hvS => by
    have e : ∫ s, gv m A v s ∂(lam v) =
        (cfac E v : ℝ) * ∫ s, (m v (hermScal (Fv F v) σ s) (A v)).toReal ∂(lam v) :=
      integral_const_mul _ _
    rw [e, ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal, (hv v hvS).2.2]
  rw [ENNReal.ofReal_mul hI0, ENNReal.ofReal_prod_of_nonneg hJ0, Finset.prod_congr rfl hloc,
    Finset.prod_mul_distrib]
  have e0 : ENNReal.ofReal (∫ y, Gi mi φ y ∂li) = ∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW (Ainf F) b li 1 1) := c4
  rw [e0, vol]
  ring

end GlobalTheory.CompanionTheory.SW.RankOne

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDensityFormulaStatement
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_density_formula : Dens := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOne.dens | exact GlobalTheory.CompanionTheory.SW.RankOne.dens | (intros; apply GlobalTheory.CompanionTheory.SW.RankOne.dens <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeOfScalarFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeOfScalarFormula
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BaseSimil

open PositivityTheory.Rg.Base1 PositivityTheory.SiegelWeilFormula.Densx

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def g1 (x : E) (hx : x ≠ 0) : GL (Fin 1) E :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of fun _ _ => x) (by rw [Matrix.det_fin_one]; exact hx)

theorem scalar_matrix_apply (x : E) (hx : x ≠ 0) (i j : Fin 1) :
    ((g1 x hx : GL (Fin 1) E) : Matrix (Fin 1) (Fin 1) E) i j = x := rfl

theorem tuple_action_scalar_eq_mul (R : Type) [CommRing R] [Algebra F R] (x : E) (hx : x ≠ 0) :
    actTup R (bc (inclR R) (g1 x hx)) =
      fun (X : Fin 1 → Fin 1 → R ⊗[F] E) a i => inclR R x * X a i := by
  funext X a i
  have hi : ∀ j : Fin 1, j = i := fun j => Subsingleton.elim _ _
  have h1 : ((bc (inclR R) (g1 x hx) : GL (Fin 1) (R ⊗[F] E)) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) i 0 = inclR R x := rfl
  change ∑ j, ((bc (inclR R) (g1 x hx) : GL (Fin 1) (R ⊗[F] E)) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) i j * X a j = _
  rw [Fin.sum_univ_one, h1, Subsingleton.elim i 0]

end Alg

theorem map_fib (hS : Scal) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (J : Matrix (Fin 1) (Fin 1) E) (hJ : IsHermND σ J)
    (R : Type) [CommRing R] [Nontrivial R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    (hL : IsLocR R) (μ : Measure (Fin 1 → Fin 1 → R ⊗[F] E)) (ν : Measure (HermR R σ 1))
    (m : HermR R σ 1 → Measure (Fin 1 → Fin 1 → R ⊗[F] E)) (hμ : μ.IsAddHaarMeasure) (hν : ν.IsAddHaarMeasure)
    (hm : IsGramFib R σ J 1 μ ν m) (x : E) (hx : x ≠ 0) (l β : F) (hl : σ x * x = algebraMap F E l) (hβ : β ≠ 0) :
    (m (hermScal R σ (algebraMap F R β))).map (actTup R (bc (inclR R) (g1 x hx))) =
      m (hermScal R σ (algebraMap F R (l * β))) := by
  have hn : algebraMap F R l ⊗ₜ[F] (1 : E) =
      sigR R σ ((Units.map (inclR (F := F) (E := E) R : E →* R ⊗[F] E) (Units.mk0 x hx) : (R ⊗[F] E)ˣ) : R ⊗[F] E) *
        ((Units.map (inclR (F := F) (E := E) R : E →* R ⊗[F] E) (Units.mk0 x hx) : (R ⊗[F] E)ˣ) : R ⊗[F] E) := by
    change _ = sigR R σ (inclR R x) * inclR R x
    have h1 : sigR R σ (inclR R x) = inclR R (σ x) := by simp [sigR, inclR]
    rw [h1, ← map_mul, hl]
    have := (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes l
    change _ = (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E) (algebraMap F E l)
    rw [this]
    simp [Algebra.TensorProduct.algebraMap_apply]
  have hu : IsUnit (algebraMap F R β) := (IsUnit.mk0 _ hβ).map _
  have := hS F E σ hcm J hJ R hL μ ν m hμ hν hm _ _ _ hn hu
  rw [tuple_action_scalar_eq_mul, map_mul]
  exact this

theorem hermitian_similitude_scalar {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (J : Matrix (Fin 1) (Fin 1) E)
    (x : E) (hx : x ≠ 0) (l : F) (hl : σ x * x = algebraMap F E l) :
    cT (σ : E →+* E) ((g1 x hx : GL (Fin 1) E) : Matrix (Fin 1) (Fin 1) E) * J *
        ((g1 x hx : GL (Fin 1) E) : Matrix (Fin 1) (Fin 1) E) = (algebraMap F E l) • J := by
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.smul_apply, smul_eq_mul, cT, Matrix.transpose_apply,
    Matrix.map_apply, scalar_matrix_apply]
  rw [← hl]
  change σ x * J 0 0 * x = σ x * x * J 0 0
  ring

theorem exists_norm {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (J : Matrix (Fin 1) (Fin 1) E) (hJ : IsHermND σ J) (β β' : F) (hβ : β ≠ 0)
    (hs : (sph σ J β).Nonempty) (hs' : (sph σ J β').Nonempty) (hβ' : β' ≠ 0) :
    ∃ x : E, x ≠ 0 ∧ σ x * x = algebraMap F E (β' / β) := by
  obtain ⟨X, hX⟩ := hs
  obtain ⟨Y, hY⟩ := hs'
  have hJ0 : J 0 0 ≠ 0 := by
    have := hJ.2
    rwa [Matrix.det_fin_one] at this
  have e : ∀ (Z : Fin 1 → Fin 1 → E) (t : F), Z ∈ sph σ J t → σ (Z 0 0) * J 0 0 * Z 0 0 = algebraMap F E t := by
    intro Z t hZ
    have h0 := congrFun (congrFun hZ 0) 0
    simpa [gramE, hE, hform] using h0
  have eX := e X β hX
  have eY := e Y β' hY
  have hb : algebraMap F E β ≠ 0 := by simpa using hβ
  have hx : X 0 0 ≠ 0 := by
    intro h
    rw [h] at eX
    exact hb (by simpa using eX.symm)
  have hsx : σ (X 0 0) ≠ 0 := by simpa using hx
  refine ⟨Y 0 0 / X 0 0, ?_, ?_⟩
  · refine div_ne_zero ?_ hx
    intro h
    rw [h] at eY
    exact (by simpa using hβ' : algebraMap F E β' ≠ 0) (by simpa using eY.symm)
  · rw [map_div₀, map_div₀, ← eX, ← eY]
    field_simp

theorem simil : Scal → Simil := by
  intro hScal F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hcm hJ hli hlam hμ h𝓕 hmi hm β β' hβ hβ' hs hs' c hc
  have hl0 : β' / β ≠ 0 := div_ne_zero hβ' hβ
  obtain ⟨x, hx, hxl⟩ := exists_norm σ J hJ β β' hβ hs hs' hβ'
  have hγ := hermitian_similitude_scalar σ J x hx (β' / β) hxl
  obtain ⟨μ', 𝓕', hμ', h𝓕', hth⟩ := GlobalTheory.CompanionTheory.SW.SimTheta.theta_simil F E σ hcm 1 J hJ μ 𝓕 hμ h𝓕 (g1 x hx) (β' / β) hl0 hγ
  have hT : (fun _ _ => algebraMap F E β' : Matrix (Fin 1) (Fin 1) E) =
      (algebraMap F E (β' / β)) • (fun _ _ => algebraMap F E β : Matrix (Fin 1) (Fin 1) E) := by
    funext a b'
    change algebraMap F E β' = algebraMap F E (β' / β) * algebraMap F E β
    rw [← map_mul, div_mul_cancel₀ _ hβ]
  have hth1 := hth 1 _ _ hT
  have hind := GlobalTheory.CompanionTheory.SW.ThetaIndep.thetaMeas_gram_indep F E σ hcm 1 J hJ μ μ' 𝓕 𝓕' hμ h𝓕 hμ' h𝓕' 1 (fun _ _ => algebraMap F E β)
  change (thetaMeas σ J μ' 𝓕' (sph σ J β)).map _ = thetaMeas σ J μ 𝓕 (sph σ J β') at hth1
  change thetaMeas σ J μ 𝓕 (sph σ J β) = thetaMeas σ J μ' 𝓕' (sph σ J β) at hind
  obtain ⟨⟨i1, i2, i3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have hLi : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hcm.1
  have hLv : ∀ v, IsLocR (Fv F v) := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  have : ∀ v, BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  have hWi := SWIsom.haar_of_loc σ hcm (Ainf F) hLi b li hli.1 1 1
  have hWv := fun v => SWIsom.haar_of_loc σ hcm (Fv F v) (hLv v) b (lam v) (hlam v).1 1 1
  have hβ'' : β' / β * β = β' := div_mul_cancel₀ _ hβ
  have sInf := map_fib hScal σ hcm J hJ (Ainf F) hLi _ _ mi hWi.1 hWi.2 hmi x hx (β' / β) β hxl hβ
  have sV := fun v => map_fib hScal σ hcm J hJ (Fv F v) (hLv v) _ _ (m v) (hWv v).1 (hWv v).2 (hm v) x hx (β' / β) β hxl hβ
  rw [hβ''] at sInf
  simp only [hβ''] at sV
  have hproj : ∀ X : Fin 1 → Fin 1 → AF F ⊗[F] E,
      projInf (actTup (AF F) (bc (inclR (AF F)) (g1 x hx)) X) =
          actTup (Ainf F) (bc (inclR (Ainf F)) (g1 x hx)) (projInf X) ∧
        ∀ v, projV v (projFin (actTup (AF F) (bc (inclR (AF F)) (g1 x hx)) X)) =
          actTup (Fv F v) (bc (inclR (Fv F v)) (g1 x hx)) (projV v (projFin X)) := by
    intro X
    refine ⟨?_, fun v => ?_⟩
    · funext a i
      exact SWIsom.map_actTup (fstA F) (g1 x hx) X a i
    · have h1 : projFin (actTup (AF F) (bc (inclR (AF F)) (g1 x hx)) X) =
          actTup (Af F) (bc (inclR (Af F)) (g1 x hx)) (projFin X) := by
        funext a i
        exact SWIsom.map_actTup (sndA F) (g1 x hx) X a i
      rw [h1]
      funext a i
      exact SWIsom.map_actTup (evalV F v) (g1 x hx) (projFin X) a i
  have hfin : ∀ v, (cfac E v • m v (hermScal (Fv F v) σ (algebraMap F _ β'))) (latV b v) < ⊤ := by
    intro v
    have := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hcm 1 J hJ (Fv F v) (hLv v) 1 _ _ (m v) (hWv v).1 (hWv v).2 (hm v)
      (hermScal (Fv F v) σ (algebraMap F _ β'))).1
    have h2 := ((GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 1).2.2.2.1 v).1.measure_lt_top
      (μ := m v (hermScal (Fv F v) σ (algebraMap F _ β')))
    rw [Measure.smul_apply]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top h2
  have hu : IsUnitProd (1 : ℝ≥0) (fun _ : HeightOneSpectrum (𝓞 F) => (1 : ℝ≥0)) :=
    ⟨Filter.Eventually.of_forall fun _ => rfl, by simp⟩
  have key := GlobalTheory.CompanionTheory.SW.MassSimil.euler_move_c F E σ hcm d b 1 1 (thetaMeas σ J μ' 𝓕' (sph σ J β))
    (mi (hermScal (Ainf F) σ (algebraMap F _ β)))
    (mi (hermScal (Ainf F) σ (algebraMap F _ β')))
    (fun v => cfac E v • m v (hermScal (Fv F v) σ (algebraMap F _ β)))
    (fun v => cfac E v • m v (hermScal (Fv F v) σ (algebraMap F _ β')))
    (actTup (AF F) (bc (inclR (AF F)) (g1 x hx)))
    (actTup (Ainf F) (bc (inclR (Ainf F)) (g1 x hx))) (fun v => actTup (Fv F v) (bc (inclR (Fv F v)) (g1 x hx)))
    (SWIsom.measurable_actTup σ hcm (AF F) _) (SWIsom.measurable_of_loc σ hcm (Ainf F) hLi _)
    (fun v => SWIsom.measurable_of_loc σ hcm (Fv F v) (hLv v) _) hproj
    ((GlobalTheory.CompanionTheory.SW.LatRat.latV_rational F E σ hcm d b 1 1).2.1 (g1 x hx)) 1 (fun _ => 1) hu
    (by rw [sInf, one_smul]) (fun v => by
      rw [Measure.map_smul, sV v, one_smul]
      exact (SWIsom.measurable_of_loc σ hcm (Fv F v) (hLv v) _).aemeasurable) hfin c
  unfold EP at hc ⊢
  rw [hind] at hc
  rw [← hth1]
  exact key hc

end GlobalTheory.CompanionTheory.SW.BaseSimil
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeOfScalarFormulaStatement
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitude_of_scalar_formula : Scal → Simil := by
  first | exact @GlobalTheory.CompanionTheory.SW.BaseSimil.simil | exact GlobalTheory.CompanionTheory.SW.BaseSimil.simil | (intros; apply GlobalTheory.CompanionTheory.SW.BaseSimil.simil <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.MassOneBase.MassOne
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.MassOneCounts.CountGood
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.FormRes
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Densx

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.SiegelWeilFormula.Gunr PositivityTheory.SiegelWeilFormula.MOne
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem zOf_repr {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (w : Fin 1 × Fin d → v.adicCompletionIntegers F) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (zOf b v w) k = (w (0, k) : Fv F v) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [zOf, map_sum, Finsupp.single_apply]

theorem zOf_mem' {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (w : Fin 1 × Fin d → v.adicCompletionIntegers F) : zOf b v w ∈ Rv b v := by
  intro k
  rw [zOf_repr]
  exact (w (0, k)).2

theorem form_res (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (J : Matrix (Fin 1) (Fin 1) E) (hJ : IsHermND σ J) (d : ℕ)
    (b : Module.Basis (Fin d) F E) (B : Matrix (Fin 1 × Fin d) (Fin 1 × Fin d) F)
    (hBt : ∀ (R : Type) [CommRing R] [Algebra F R] (x y : Fin 1 → R ⊗[F] E),
      Algebra.trace R (R ⊗[F] E) (hR R σ J x y) =
        (fun p : Fin 1 × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2) ⬝ᵥ
          (B.map (algebraMap F R) *ᵥ fun p : Fin 1 × Fin d => (Algebra.TensorProduct.basis R b).repr (y p.1) p.2))
    (v : HeightOneSpectrum (𝓞 F))
    (hfix : ∀ x : Fv F v ⊗[F] E, sigR (Fv F v) σ x = x → ∃ c : Fv F v, x = algebraMap (Fv F v) (Fv F v ⊗[F] E) c)
    (htr : ∀ a : Fv F v ⊗[F] E,
      (∀ y ∈ Rv b v, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (a * y) ∈ v.adicCompletionIntegers F) ↔ a ∈ Rv b v)
    (hR1 : (1 : Fv F v ⊗[F] E) ∈ Rv b v)
    (hRmul : ∀ x ∈ Rv b v, ∀ y ∈ Rv b v, x * y ∈ Rv b v)
    (hRsig : ∀ x ∈ Rv b v, sigR (Fv F v) σ x ∈ Rv b v)
    (h2 : Valued.v (2 : Fv F v) = 1) (hj : inclR (Fv F v) (J 0 0) ∈ Rv b v)
    (ϖ : v.adicCompletionIntegers F) (hϖ0 : (ϖ : Fv F v) ≠ 0) (hϖ1 : ‖(ϖ : Fv F v)‖ < 1)
    (hϖd : ∀ x : v.adicCompletionIntegers F, ‖(x : Fv F v)‖ < 1 → ϖ ∣ x)
    (w : Fin 1 × Fin d → v.adicCompletionIntegers F) (s : v.adicCompletionIntegers F) :
    Valued.v ((2 : Fv F v)⁻¹ * ((fun p => (w p : Fv F v)) ⬝ᵥ
        (B.map (algebraMap F (Fv F v)) *ᵥ fun p => (w p : Fv F v))) - s) < 1 ↔
      ∃ y ∈ Rv b v, sigR (Fv F v) σ (zOf b v w) * inclR (Fv F v) (J 0 0) * zOf b v w -
        algebraMap (Fv F v) (Fv F v ⊗[F] E) s = algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ * y := by
  classical
  have hσσ : ∀ x, σ (σ x) = x := GlobalTheory.CompanionTheory.SW.SWIsom.sigma_sigma σ hCM
  have hj0 : σ (J 0 0) = J 0 0 := hJ.1 0 0
  have h20 : (2 : Fv F v) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h2
    exact zero_ne_one h2
  have hd : d = 2 := by
    rw [← hCM.2.2.1, Module.finrank_eq_card_basis b, Fintype.card_fin]

  have htrc : ∀ c : Fv F v, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (algebraMap (Fv F v) _ c) = 2 * c := by
    intro c
    rw [Algebra.trace_algebraMap_of_basis (Algebra.TensorProduct.basis (Fv F v) b), Fintype.card_fin, hd,
      nsmul_eq_mul]
    norm_num

  have hint : ∀ c : Fv F v, algebraMap (Fv F v) (Fv F v ⊗[F] E) c ∈ Rv b v → c ∈ v.adicCompletionIntegers F := by
    intro c hc
    have h1 := (htr _).2 hc 1 hR1
    rw [mul_one, htrc] at h1
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1 ⊢
    rwa [map_mul, h2, one_mul] at h1

  have hsc : ∀ u : Fv F v, u ∈ v.adicCompletionIntegers F → algebraMap (Fv F v) (Fv F v ⊗[F] E) u ∈ Rv b v := by
    intro u hu k
    rw [Algebra.algebraMap_eq_smul_one, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact Subring.mul_mem _ hu (hR1 k)
  set z := zOf b v w with hz
  have hzR : z ∈ Rv b v := zOf_mem' b v w
  have hsig2 : ∀ x, sigR (Fv F v) σ (sigR (Fv F v) σ x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [sigR, hσσ]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hsj : sigR (Fv F v) σ (inclR (Fv F v) (J 0 0)) = inclR (Fv F v) (J 0 0) := by
    simp [sigR, inclR, hj0]
  set Q := sigR (Fv F v) σ z * inclR (Fv F v) (J 0 0) * z with hQ
  have hQfix : sigR (Fv F v) σ Q = Q := by
    rw [hQ, map_mul, map_mul, hsig2, hsj]
    ring
  obtain ⟨c, hc⟩ := hfix Q hQfix
  have hQR : Q ∈ Rv b v := hRmul _ (hRmul _ (hRsig _ hzR) _ hj) _ hzR
  have hcO : c ∈ v.adicCompletionIntegers F := hint c (hc ▸ hQR)

  have hform : (fun p => (w p : Fv F v)) ⬝ᵥ (B.map (algebraMap F (Fv F v)) *ᵥ fun p => (w p : Fv F v)) = 2 * c := by
    have e1 := hBt (Fv F v) (fun _ => z) (fun _ => z)
    have e2 : hR (Fv F v) σ J (fun _ => z) (fun _ => z) = Q := by
      simp [hR, hform, JR, Matrix.map_apply, hQ]
    have e3 : (fun p : Fin 1 × Fin d => (Algebra.TensorProduct.basis (Fv F v) b).repr ((fun _ => z) p.1) p.2) =
        fun p => (w p : Fv F v) := by
      funext p
      obtain ⟨i, k⟩ := p
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      exact zOf_repr b v w k
    rw [e2, e3, hc, htrc] at e1
    exact e1.symm
  rw [hform, ← mul_assoc, inv_mul_cancel₀ h20, one_mul, hc]
  constructor
  · intro hlt
    have hcs : c - s ∈ v.adicCompletionIntegers F :=
      Subring.sub_mem _ hcO s.2
    obtain ⟨u, hu⟩ := hϖd ⟨c - s, hcs⟩ (by rwa [Valued.toNormedField.norm_lt_one_iff])
    refine ⟨algebraMap (Fv F v) _ (u : Fv F v), hsc _ u.2, ?_⟩
    have hu' : c - (s : Fv F v) = (ϖ : Fv F v) * u := congrArg Subtype.val hu
    rw [← map_sub, hu', map_mul]
  · rintro ⟨y, hy, he⟩
    set u := (ϖ : Fv F v)⁻¹ * (c - s) with hu
    have hyu : y = algebraMap (Fv F v) _ u := by
      have := congrArg (fun q => algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ : Fv F v)⁻¹ * q) he
      rw [← map_sub, ← map_mul, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hϖ0, map_one, one_mul] at this
      rw [hu, this]
    have huO : u ∈ v.adicCompletionIntegers F := hint u (hyu ▸ hy)
    have hcs : c - (s : Fv F v) = (ϖ : Fv F v) * u := by
      rw [hu, ← mul_assoc, mul_inv_cancel₀ hϖ0, one_mul]
    rw [hcs, map_mul]
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at huO
    have hϖv : Valued.v (ϖ : Fv F v) < 1 := by rwa [← Valued.toNormedField.norm_lt_one_iff]
    calc Valued.v (ϖ : Fv F v) * Valued.v u ≤ Valued.v (ϖ : Fv F v) := by
          first
          | exact mul_le_of_le_one_right' huO
          | exact mul_le_of_le_one_right zero_le' huO
      _ < 1 := hϖv

end PositivityTheory.SiegelWeilFormula.Densx

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.MassOneCounts.FormRes
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.MOne

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem form_res (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (J : Matrix (Fin 1) (Fin 1) E) (hJ : IsHermND σ J) (d : ℕ)
    (b : Module.Basis (Fin d) F E) (B : Matrix (Fin 1 × Fin d) (Fin 1 × Fin d) F)
    (hBt : ∀ (R : Type) [CommRing R] [Algebra F R] (x y : Fin 1 → R ⊗[F] E),
      Algebra.trace R (R ⊗[F] E) (hR R σ J x y) =
        (fun p : Fin 1 × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2) ⬝ᵥ
          (B.map (algebraMap F R) *ᵥ fun p : Fin 1 × Fin d => (Algebra.TensorProduct.basis R b).repr (y p.1) p.2))
    (v : HeightOneSpectrum (𝓞 F))
    (hfix : ∀ x : Fv F v ⊗[F] E, sigR (Fv F v) σ x = x → ∃ c : Fv F v, x = algebraMap (Fv F v) (Fv F v ⊗[F] E) c)
    (htr : ∀ a : Fv F v ⊗[F] E,
      (∀ y ∈ Rv b v, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (a * y) ∈ v.adicCompletionIntegers F) ↔ a ∈ Rv b v)
    (hR1 : (1 : Fv F v ⊗[F] E) ∈ Rv b v)
    (hRmul : ∀ x ∈ Rv b v, ∀ y ∈ Rv b v, x * y ∈ Rv b v)
    (hRsig : ∀ x ∈ Rv b v, sigR (Fv F v) σ x ∈ Rv b v)
    (h2 : Valued.v (2 : Fv F v) = 1) (hj : inclR (Fv F v) (J 0 0) ∈ Rv b v)
    (ϖ : v.adicCompletionIntegers F) (hϖ0 : (ϖ : Fv F v) ≠ 0) (hϖ1 : ‖(ϖ : Fv F v)‖ < 1)
    (hϖd : ∀ x : v.adicCompletionIntegers F, ‖(x : Fv F v)‖ < 1 → ϖ ∣ x)
    (w : Fin 1 × Fin d → v.adicCompletionIntegers F) (s : v.adicCompletionIntegers F) :
    Valued.v ((2 : Fv F v)⁻¹ * ((fun p => (w p : Fv F v)) ⬝ᵥ
        (B.map (algebraMap F (Fv F v)) *ᵥ fun p => (w p : Fv F v))) - s) < 1 ↔
      ∃ y ∈ Rv b v, sigR (Fv F v) σ (zOf b v w) * inclR (Fv F v) (J 0 0) * zOf b v w -
        algebraMap (Fv F v) (Fv F v ⊗[F] E) s = algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ * y :=
  PositivityTheory.SiegelWeilFormula.Densx.form_res σ hCM J hJ d b B hBt v hfix htr hR1 hRmul hRsig h2 hj ϖ hϖ0 hϖ1 hϖd w s

end PositivityTheory.SiegelWeilFormula.MOne

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.MassOneCounts.SolCountOneOne
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.MOne

open PositivityTheory.PfSWUS.Loc

theorem card_bridge {W A R : Type} [CommRing R] (ϖ : R) (a : W → A) (ha : Function.Surjective a) (φ : W → R)
    (hφ : Function.Surjective φ) (hker : ∀ w w', a w = a w' ↔ φ w - φ w' ∈ lev ϖ 1) (PA : A → Prop) (PR : R → Prop)
    (hP : ∀ w, PA (a w) ↔ PR (φ w)) :
    Nat.card {y // PA y} = Nat.card (Ideal.Quotient.mk (lev ϖ 1) '' {x | PR x}) := by
  classical
  choose s hs using ha
  let e : A → R ⧸ lev ϖ 1 := fun y => Ideal.Quotient.mk (lev ϖ 1) (φ (s y))
  have hinj : Function.Injective e := by
    intro y y' h
    have h' := Ideal.Quotient.eq.mp h
    rw [← hs y, ← hs y']
    exact (hker _ _).mpr h'
  have himg : e '' {y | PA y} = Ideal.Quotient.mk (lev ϖ 1) '' {x | PR x} := by
    ext c
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨φ (s y), ?_, rfl⟩
      have hy' : PA (a (s y)) := by
        rw [hs y]
        exact hy
      exact (hP _).mp hy'
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨w, rfl⟩ := hφ x
      refine ⟨a w, (hP w).mpr hx, ?_⟩
      exact Ideal.Quotient.eq.mpr ((hker _ _).mp (hs (a w)))
  rw [← himg, Nat.card_image_of_injective hinj]
  rfl

theorem solCount_one_one {R : Type} [CommRing R] (σ : R →+* R) (ϖ : R) (j t : R) :
    solCount σ ϖ (Matrix.of fun _ _ => j : Matrix (Fin 1) (Fin 1) R) (Matrix.of fun _ _ => t : Matrix (Fin 1) (Fin 1) R) 1 =
      Nat.card (Ideal.Quotient.mk (lev ϖ 1) '' {x : R | Ideal.Quotient.mk (lev ϖ 1) (σ x * j * x) =
        Ideal.Quotient.mk (lev ϖ 1) t}) := by
  classical
  unfold solCount
  have hinj : Function.Injective (fun y : Matrix (Fin 1) (Fin 1) (R ⧸ lev ϖ 1) => y 0 0) := by
    intro y y' h
    ext a b
    obtain rfl : a = 0 := Subsingleton.elim _ _
    obtain rfl : b = 0 := Subsingleton.elim _ _
    exact h
  rw [← Nat.card_image_of_injective hinj, Set.image_image]
  refine congrArg (fun s : Set (R ⧸ lev ϖ 1) => Nat.card s) ?_
  ext c
  constructor
  · rintro ⟨X, hX, rfl⟩
    refine ⟨X 0 0, ?_, rfl⟩
    have h00 := congrFun (congrFun hX 0) 0
    simpa [red, cT, Matrix.mul_apply] using h00
  · rintro ⟨x, hx, rfl⟩
    refine ⟨Matrix.of fun _ _ => x, ?_, rfl⟩
    simp only [Set.mem_ofPred_eq]
    ext a b
    obtain rfl : a = 0 := Subsingleton.elim _ _
    obtain rfl : b = 0 := Subsingleton.elim _ _
    simpa [red, cT, Matrix.mul_apply] using hx

end PositivityTheory.SiegelWeilFormula.MOne

end
end

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.MOne

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology GlobalTheory.CompanionTheory.SW.LGPrim
  PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct ENNReal NNReal Matrix

section Helpers

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem alg_mem {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (h1 : (1 : Fv F v ⊗[F] E) ∈ Rv b v) (c : Fv F v) (hc : c ∈ v.adicCompletionIntegers F) :
    algebraMap (Fv F v) (Fv F v ⊗[F] E) c ∈ Rv b v := by
  simp only [Rv, Set.mem_ofPred_eq] at h1 ⊢
  intro k
  rw [Algebra.algebraMap_eq_smul_one, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact mul_mem hc (h1 k)

theorem sigR_alg (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (c : Fv F v) :
    sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) c) = algebraMap (Fv F v) (Fv F v ⊗[F] E) c := by
  simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one, Algebra.algebraMap_self, RingHom.id_apply]

theorem sigR_inclR (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : E) :
    sigR (Fv F v) σ (inclR (Fv F v) x) = inclR (Fv F v) (σ x) := by
  simp only [sigR, inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

end Helpers

theorem count_good (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (J : Matrix (Fin 1) (Fin 1) E) (hJ : IsHermND σ J) (d : ℕ)
    (b : Module.Basis (Fin d) F E) (B : Matrix (Fin 1 × Fin d) (Fin 1 × Fin d) F)
    (hBt : ∀ (R : Type) [CommRing R] [Algebra F R] (x y : Fin 1 → R ⊗[F] E),
      Algebra.trace R (R ⊗[F] E) (hR R σ J x y) =
        (fun p : Fin 1 × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2) ⬝ᵥ
          (B.map (algebraMap F R) *ᵥ fun p : Fin 1 × Fin d => (Algebra.TensorProduct.basis R b).repr (y p.1) p.2)) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ BO : Matrix (Fin 1 × Fin d) (Fin 1 × Fin d) (v.adicCompletionIntegers F),
        BO.map phi = B.map (algebraMap F (Fv F v)) →
      ∀ s : v.adicCompletionIntegers F, Valued.v (s : Fv F v) = 1 →
        (Nat.card {y : Fin 1 × Fin d → IsLocalRing.ResidueField (v.adicCompletionIntegers F) //
            (2 : IsLocalRing.ResidueField (v.adicCompletionIntegers F))⁻¹ *
              (y ⬝ᵥ ((BO.map (IsLocalRing.residue (v.adicCompletionIntegers F))) *ᵥ y)) =
              IsLocalRing.residue (v.adicCompletionIntegers F) s} : ℝ) =
          (Ideal.absNorm v.asIdeal : ℝ) - Densx.eR E v := by
  classical
  have hFI := GlobalTheory.T.unramified_finite_integral F (basisSet σ b)
  obtain ⟨hintE, hun⟩ := GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units F E σ hCM d b
  have hj0 : J 0 0 ≠ 0 := by
    have h := hJ.2
    rwa [Matrix.det_unique] at h
  filter_upwards [hFI, hintE (J 0 0), hintE (J 0 0)⁻¹, hun 2 two_ne_zero] with v hInt hjI hjiI hv2 BO hBO s hsu
  have hv2' : Valued.v (2 : Fv F v) = 1 := by rwa [map_ofNat] at hv2
  obtain ⟨ϖ, hϖ0, hϖ1, hϖd, hϖc⟩ := GlobalTheory.T.uniformizer_existence F v
  obtain ⟨S, σS, hS, hsig⟩ := GlobalTheory.T.residue_ring_structure F E σ d b v hInt
  have hfix := GlobalTheory.T.fixed_field_structure F E σ hCM v
  have htr := GlobalTheory.T.trace_dual_at_place F E σ hCM d b v hInt
  have hR1 : (1 : Fv F v ⊗[F] E) ∈ Rv b v := by
    rw [← hS]
    exact S.one_mem
  have hRS : ∀ x, x ∈ Rv b v ↔ x ∈ S := fun x => by rw [← hS]; rfl
  have hRmul : ∀ x ∈ Rv b v, ∀ y ∈ Rv b v, x * y ∈ Rv b v := by
    intro x hx y hy
    rw [hRS] at hx hy ⊢
    exact S.mul_mem hx hy
  have hRsig : ∀ x ∈ Rv b v, sigR (Fv F v) σ x ∈ Rv b v := by
    intro x hx
    rw [hRS] at hx ⊢
    have h := (σS ⟨x, hx⟩).2
    rwa [hsig] at h
  have hϖS : algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ : Fv F v) ∈ S :=
    (hRS _).1 (alg_mem b v hR1 (ϖ : Fv F v) ϖ.2)
  let ε : ℤ := if IsField (Fv F v ⊗[F] E) then -1 else 1
  have hε : (ε : ℂ) = PositivityTheory.SiegelWeilFormula.Gen.eSp E v := by
    simp only [ε, PositivityTheory.SiegelWeilFormula.Gen.eSp]
    split_ifs <;> simp
  have hQ := PositivityTheory.SiegelWeilFormula.Gunr.quadAt_of GlobalTheory.T.unramified_quadratic_condition_one GlobalTheory.T.unramified_quadratic_condition_two GlobalTheory.T.unramified_quadratic_condition_three GlobalTheory.T.unramified_quadratic_condition_four GlobalTheory.T.unramified_quadratic_condition_five
    F E σ hCM d b v hInt S σS hS hsig ϖ hϖ0 hϖ1 hϖd hϖc hϖS ε hε
  let ϖS : S := ⟨_, hϖS⟩
  have hjS : inclR (Fv F v) (J 0 0) ∈ S := (hRS _).1 hjI
  have hjiS : inclR (Fv F v) (J 0 0)⁻¹ ∈ S := (hRS _).1 hjiI
  let jS : S := ⟨_, hjS⟩
  let jiS : S := ⟨_, hjiS⟩
  have hsinv : (s : Fv F v)⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hsu, inv_one]
  have htS : algebraMap (Fv F v) (Fv F v ⊗[F] E) (s : Fv F v) ∈ S := (hRS _).1 (alg_mem b v hR1 _ s.2)
  have htiS : algebraMap (Fv F v) (Fv F v ⊗[F] E) (s : Fv F v)⁻¹ ∈ S := (hRS _).1 (alg_mem b v hR1 _ hsinv)
  let tS : S := ⟨_, htS⟩
  let tiS : S := ⟨_, htiS⟩
  have hs0 : (s : Fv F v) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hsu
    exact zero_ne_one hsu
  have hUj : PositivityTheory.PfSWUS.Loc.IsUnimod σS (Matrix.of fun _ _ => jS : Matrix (Fin 1) (Fin 1) S) := by
    refine ⟨?_, ?_⟩
    · ext i k
      simp only [PositivityTheory.PfSWUS.Loc.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]
      rw [hsig]
      simp only [jS]
      rw [sigR_inclR, hJ.1 0 0]
    · rw [Matrix.det_unique]
      refine ⟨⟨jS, jiS, ?_, ?_⟩, rfl⟩
      · apply Subtype.ext
        simp only [jS, jiS, MulMemClass.coe_mul, OneMemClass.coe_one]
        rw [← map_mul, mul_inv_cancel₀ hj0, map_one]
      · apply Subtype.ext
        simp only [jS, jiS, MulMemClass.coe_mul, OneMemClass.coe_one]
        rw [← map_mul, inv_mul_cancel₀ hj0, map_one]
  have hUt : PositivityTheory.PfSWUS.Loc.IsUnimod σS (Matrix.of fun _ _ => tS : Matrix (Fin 1) (Fin 1) S) := by
    refine ⟨?_, ?_⟩
    · ext i k
      simp only [PositivityTheory.PfSWUS.Loc.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]
      rw [hsig]
      simp only [tS]
      rw [sigR_alg]
    · rw [Matrix.det_unique]
      refine ⟨⟨tS, tiS, ?_, ?_⟩, rfl⟩
      · apply Subtype.ext
        simp only [tS, tiS, MulMemClass.coe_mul, OneMemClass.coe_one]
        rw [← map_mul, mul_inv_cancel₀ hs0, map_one]
      · apply Subtype.ext
        simp only [tS, tiS, MulMemClass.coe_mul, OneMemClass.coe_one]
        rw [← map_mul, inv_mul_cancel₀ hs0, map_one]
  have hcount := GlobalTheory.T.card_unimodular_hermitian_reps_level_one S σS ϖS (Ideal.absNorm v.asIdeal) ε hQ 1 1 le_rfl _ _ hUj hUt
  rw [solCount_one_one] at hcount

  have hlev : ∀ x : S, x ∈ PositivityTheory.PfSWUS.Loc.lev ϖS 1 ↔
      ∃ y ∈ Rv b v, (x : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ * y := by
    intro x
    rw [PositivityTheory.PfSWUS.Loc.lev, pow_one, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨a, (hRS _).2 a.2, ?_⟩
      rw [← ha, MulMemClass.coe_mul, mul_comm]
    · rintro ⟨y, hy, he⟩
      refine ⟨⟨y, (hRS _).1 hy⟩, ?_⟩
      apply Subtype.ext
      rw [MulMemClass.coe_mul, he, mul_comm]
  let φ : (Fin 1 × Fin d → v.adicCompletionIntegers F) → S := fun w => ⟨zOf b v w, (hRS _).1 (zOf_mem b v w)⟩
  have hφ : Function.Surjective φ := by
    intro x
    obtain ⟨w, hw⟩ := zOf_surj b v x ((hRS _).2 x.2)
    exact ⟨w, Subtype.ext hw⟩
  have ha : Function.Surjective (fun (w : Fin 1 × Fin d → v.adicCompletionIntegers F) p =>
      IsLocalRing.residue (v.adicCompletionIntegers F) (w p)) := by
    intro y
    exact ⟨fun p => lift (y p), funext fun p => res_lift (y p)⟩
  have hker : ∀ w w' : Fin 1 × Fin d → v.adicCompletionIntegers F,
      (fun p => IsLocalRing.residue (v.adicCompletionIntegers F) (w p)) =
        (fun p => IsLocalRing.residue (v.adicCompletionIntegers F) (w' p)) ↔
      φ w - φ w' ∈ PositivityTheory.PfSWUS.Loc.lev ϖS 1 := by
    intro w w'
    rw [hlev, funext_iff]
    simp only [res_eq_iff]
    rw [zOf_ker b v ϖ hϖ0 hϖ1 hϖd w w']
    rfl
  have hhalf : ((2 : Fv F v)⁻¹) ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv2', inv_one]
  let half : v.adicCompletionIntegers F := ⟨(2 : Fv F v)⁻¹, hhalf⟩
  have hhalfr : IsLocalRing.residue (v.adicCompletionIntegers F) half = (2 : IsLocalRing.ResidueField _)⁻¹ := by
    have h2h : half * 2 = 1 := by
      apply Subtype.ext
      show (2 : Fv F v)⁻¹ * 2 = 1
      have h20 : (2 : Fv F v) ≠ 0 := by
        intro h0
        rw [h0, map_zero] at hv2'
        exact zero_ne_one hv2'
      exact inv_mul_cancel₀ h20
    have := congrArg (IsLocalRing.residue (v.adicCompletionIntegers F)) h2h
    rw [map_mul, map_one, map_ofNat] at this
    exact eq_inv_of_mul_eq_one_left this
  have hP : ∀ w : Fin 1 × Fin d → v.adicCompletionIntegers F,
      ((2 : IsLocalRing.ResidueField (v.adicCompletionIntegers F))⁻¹ *
        ((fun p => IsLocalRing.residue (v.adicCompletionIntegers F) (w p)) ⬝ᵥ
          ((BO.map (IsLocalRing.residue (v.adicCompletionIntegers F))) *ᵥ
            (fun p => IsLocalRing.residue (v.adicCompletionIntegers F) (w p)))) =
          IsLocalRing.residue (v.adicCompletionIntegers F) s) ↔
      Ideal.Quotient.mk (PositivityTheory.PfSWUS.Loc.lev ϖS 1) (σS (φ w) * jS * φ w) =
        Ideal.Quotient.mk (PositivityTheory.PfSWUS.Loc.lev ϖS 1) tS := by
    intro w
    have e1 : (fun p => IsLocalRing.residue (v.adicCompletionIntegers F) (w p)) ⬝ᵥ
        ((BO.map (IsLocalRing.residue (v.adicCompletionIntegers F))) *ᵥ
          (fun p => IsLocalRing.residue (v.adicCompletionIntegers F) (w p))) =
        IsLocalRing.residue (v.adicCompletionIntegers F) (w ⬝ᵥ (BO *ᵥ w)) :=
      (map_quad (IsLocalRing.residue (v.adicCompletionIntegers F)) BO w).symm
    have e2 : (((half * (w ⬝ᵥ (BO *ᵥ w)) : v.adicCompletionIntegers F)) : Fv F v) =
        (2 : Fv F v)⁻¹ * ((fun p => (w p : Fv F v)) ⬝ᵥ
          (B.map (algebraMap F (Fv F v)) *ᵥ fun p => (w p : Fv F v))) := by
      rw [← hBO]
      have h := map_quad (phi (v := v)) BO w
      exact congrArg (fun t => (2 : Fv F v)⁻¹ * t) h
    rw [e1, ← hhalfr, ← map_mul, res_eq_iff, e2, form_res σ hCM J hJ d b B hBt v hfix htr hR1 hRmul hRsig hv2' hjI
      ϖ hϖ0 hϖ1 hϖd w s, Ideal.Quotient.eq, hlev]
    simp only [φ, jS, tS, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, hsig]
  have hbr := card_bridge ϖS _ ha φ hφ hker
    (fun y => (2 : IsLocalRing.ResidueField (v.adicCompletionIntegers F))⁻¹ *
      (y ⬝ᵥ ((BO.map (IsLocalRing.residue (v.adicCompletionIntegers F))) *ᵥ y)) =
        IsLocalRing.residue (v.adicCompletionIntegers F) s)
    (fun x => Ideal.Quotient.mk (PositivityTheory.PfSWUS.Loc.lev ϖS 1) (σS x * jS * x) =
      Ideal.Quotient.mk (PositivityTheory.PfSWUS.Loc.lev ϖS 1) tS) hP
  rw [hbr, hcount]
  have hq0 : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by
    have : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
    have : Ideal.absNorm v.asIdeal ≠ 0 := by omega
    exact_mod_cast this
  have heR : Densx.eR E v = (ε : ℝ) := by
    simp only [Densx.eR, ← hε, Complex.intCast_re]
  rw [heR, Fin.prod_univ_one]
  norm_num
  field_simp

end PositivityTheory.SiegelWeilFormula.MOne

end
end

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.BaseOne

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.SW PositivityTheory.SiegelWeilFormula.Densx
  GlobalTheory.CompanionTheory.SW.LGPrim
open scoped TensorProduct ENNReal NNReal Matrix

theorem eR_eq (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    eR E v = 1 ∨ eR E v = -1 := by
  unfold eR PositivityTheory.SiegelWeilFormula.Gen.eSp
  split_ifs <;> simp

theorem massOne : MassOne := by
  intro F E _ _ _ _ _ σ hCM J hJ d b
  classical
  obtain ⟨B, hBs, hBd, hBt⟩ := GlobalTheory.CompanionTheory.SW.trace_form_coords F E σ hCM 1 J hJ d b
  obtain ⟨-, hun⟩ := GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units F E σ hCM d b
  have hd : d = 2 := by
    have h1 := Module.finrank_eq_card_basis b
    rw [hCM.2.2.1, Fintype.card_fin] at h1
    exact h1.symm
  have hent : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i j, algebraMap F (Fv F v) (B i j) ∈ v.adicCompletionIntegers F := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    by_cases h0 : B i j = 0
    · refine Filter.Eventually.of_forall fun v => ?_
      rw [h0, map_zero]
      exact zero_mem _
    · refine (hun _ h0).mono fun v hv => ?_
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      exact hv.le
  filter_upwards [hun 2 two_ne_zero, hun _ hBd, hent, PositivityTheory.SiegelWeilFormula.MOne.count_good F E σ hCM J hJ d b B hBt]
    with v hv2 hvd hve hcnt lam hlam m hm s hsu
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hsu
    exact zero_ne_one hsu
  have hv2' : Valued.v (2 : Fv F v) = 1 := by rwa [map_ofNat] at hv2
  have hdet : Valued.v (B.map (algebraMap F (Fv F v))).det = 1 := by
    have h1 := (algebraMap F (Fv F v)).map_det B
    rw [h1] at hvd
    exact hvd
  let BO : Matrix (Fin 1 × Fin d) (Fin 1 × Fin d) (v.adicCompletionIntegers F) :=
    Matrix.of fun i j => ⟨algebraMap F (Fv F v) (B i j), hve i j⟩
  have hBO : BO.map phi = B.map (algebraMap F (Fv F v)) := by
    ext i j
    rfl
  have hs : s ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hsu.le
  let s' : v.adicCompletionIntegers F := ⟨s, hs⟩
  have hN := hcnt BO hBO s' hsu
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = Nat.card {y : Fin 1 × Fin d → IsLocalRing.ResidueField (v.adicCompletionIntegers F) //
      (2 : IsLocalRing.ResidueField (v.adicCompletionIntegers F))⁻¹ *
        (y ⬝ᵥ ((BO.map (IsLocalRing.residue (v.adicCompletionIntegers F))) *ᵥ y)) =
        IsLocalRing.residue (v.adicCompletionIntegers F) s'} := ⟨_, rfl⟩
  rw [← hNdef] at hN
  have hq1 : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq0 : (Ideal.absNorm v.asIdeal : ℝ≥0) ≠ 0 := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := by omega
    exact_mod_cast this
  have hcardι : Fintype.card (Fin 1 × Fin d) - 1 = 1 := by simp [hd]
  let D : ℝ≥0 := (N : ℝ≥0) * (Ideal.absNorm v.asIdeal : ℝ≥0)⁻¹
  have hD : ∀ A : Set (Fv F v), MeasurableSet A → A ⊆ {z | Valued.v (z - s) < Valued.v s} →
      (Measure.pi fun _ : Fin 1 × Fin d => lam)
        {x | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧
          (2 : Fv F v)⁻¹ * (x ⬝ᵥ ((B.map (algebraMap F (Fv F v))) *ᵥ x)) ∈ A} = (D : ℝ≥0∞) * lam A := by
    intro A hA hAs
    have h := PositivityTheory.SiegelWeilFormula.MOne.dens_exact lam hlam hv2' (Fin 1 × Fin d) BO (by rw [hBO]; exact hBs.map _)
      (by rw [hBO]; exact hdet) s' hsu A hA hAs
    rw [hBO, hcardι, ← hNdef] at h
    rw [h]
    congr 1
    simp only [D, ENNReal.coe_mul, ENNReal.coe_natCast, ENNReal.coe_inv hq0, pow_one]
  have hloc := GlobalTheory.CompanionTheory.SW.LocGood.local_mass σ hCM 1 J hJ d b v (B.map (algebraMap F (Fv F v)))
    (fun x y => hBt (Fv F v) x y) lam hlam m hm s hs0 D hD
  have hq2 : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast hq1
  have hx : 0 < 1 - eR E v / (Ideal.absNorm v.asIdeal : ℝ) := by
    have hqp : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by linarith
    rcases eR_eq F E v with he | he <;> rw [he]
    · rw [sub_pos, div_lt_one hqp]
      linarith
    · have : 0 < 1 / (Ideal.absNorm v.asIdeal : ℝ) := by positivity
      rw [neg_div, sub_neg_eq_add]
      linarith [this, one_div (Ideal.absNorm v.asIdeal : ℝ)]
  have hDr : (D : ℝ) = 1 - eR E v / (Ideal.absNorm v.asIdeal : ℝ) := by
    have hqp : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by positivity
    simp only [D, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_inv]
    rw [hN]
    field_simp
  have hne : m (hermScal (Fv F v) σ s) (latV b v) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at hloc
    have : (D : ℝ) = 0 := hloc.symm
    rw [hDr] at this
    linarith
  have hmD : m (hermScal (Fv F v) σ s) (latV b v) = (D : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_toReal hne, hloc, ENNReal.ofReal_coe_nnreal]
  rw [hmD, ← ENNReal.coe_mul, ENNReal.coe_eq_one]
  apply NNReal.eq
  rw [NNReal.coe_mul, NNReal.coe_one, cfac, Real.coe_toNNReal _ (inv_nonneg.2 hx.le), hDr,
    inv_mul_cancel₀ hx.ne']

end PositivityTheory.SiegelWeilFormula.BaseOne

end
end

namespace PositivityTheory.Rg.Base1

theorem baseOne_of (hM : PositivityTheory.SiegelWeilFormula.Densx.MassOne) : PositivityTheory.SiegelWeilFormula.Densx.BaseOne :=
  GlobalTheory.T.siegel_weil_rank_one_base_case (GlobalTheory.T.length_formula_of_total_mass_one hM) (GlobalTheory.T.similitude_of_scalar_formula GlobalTheory.T.scalar_fibration_formula) GlobalTheory.T.hasse_principle_hermitian
    (GlobalTheory.T.counting_formula_of_components GlobalTheory.T.tate_integral_formula (GlobalTheory.T.character_side_equidistribution GlobalTheory.T.equidistribution) GlobalTheory.T.local_density_ratio_formula GlobalTheory.T.hermitian_existence_principle GlobalTheory.T.existence_test_functions GlobalTheory.T.local_density_formula
      (GlobalTheory.T.l_function_side_equidistribution GlobalTheory.T.equidistribution) (GlobalTheory.T.theta_identity_of_local_densities GlobalTheory.T.scalar_fibration_formula (GlobalTheory.T.local_density_of_mass_one GlobalTheory.T.scalar_fibration_formula hM)))

theorem baseOne : PositivityTheory.SiegelWeilFormula.Densx.BaseOne := baseOne_of PositivityTheory.SiegelWeilFormula.BaseOne.massOne

theorem densEq : PositivityTheory.SiegelWeilFormula.Gen.DensEq := PositivityTheory.SiegelWeilFormula.Densx.densEq_of_one baseOne PositivityTheory.SiegelWeilFormula.BaseOne.massOne

end PositivityTheory.Rg.Base1
