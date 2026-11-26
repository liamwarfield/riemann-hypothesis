module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinSeriesConvergent
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MemStabiliserIffFrameLowerBlock

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaIntegralUnfolding
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContinuousOfLevelRealK
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff
noncomputable section
namespace GlobalTheory.WeilContF
open Formalism.IndefR.DatumF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end GlobalTheory.WeilContF
end
noncomputable section
namespace GlobalTheory.WeilContF
open Formalism.IndefR.DatumF
open scoped Topology
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
attribute [local instance] finiteFE modTop topRing
theorem continuous_of_level_real_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ g : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ,
      (∃ U : AddSubgroup (Formalism.IndefR.DatumF.WOF F E nS nT), IsOpen (U : Set (Formalism.IndefR.DatumF.WOF F E nS nT)) ∧
        ∀ u ∈ U, u.map (Formalism.IndefR.DatumF.infPartF F E) = 0 → Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (u) g = g) →
      (∀ (k : ℕ) (L : (Fin k → ℝ) →+ Formalism.IndefR.DatumF.WOF F E nS nT), Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
        ∀ w : Formalism.IndefR.DatumF.WOF F E nS nT, ContDiff ℝ ∞ fun x => g (w + L x)) →
      Continuous g := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ hstd g hU hsm
  haveI := finiteFE (F := F) (E := E)
  haveI := modTop (F := F) (E := E)
  haveI := topRing (F := F) (E := E)
  haveI : IsTopologicalAddGroup (AEF F E) := IsTopologicalRing.to_topologicalAddGroup
  obtain ⟨U, hUo, hUf⟩ := hU
  let φ := (Module.finBasis ℝ (Fin nT × Fin nS × Fin (Module.finrank F E) → mixedEmbedding.mixedSpace F)).equivFunL
  let L : (Fin _ → ℝ) →+ WOF F E nS nT := (realCh F E nS nT).comp φ.symm.toLinearEquiv.toAddMonoidHom
  have hLc : Continuous L := (continuous_realCh nS nT).comp φ.symm.continuous
  have hL0 : ∀ t, (L t).map (finPartF F E) = 0 := fun t => by
    funext i j
    exact realCh_fin nS nT _ i j
  have hLφ : ∀ v, L (φ v) = realCh F E nS nT v := fun v => by
    show realCh F E nS nT (φ.symm (φ v)) = _
    rw [φ.symm_apply_apply]
  refine continuous_iff_continuousAt.2 fun w => ?_
  let a : WOF F E nS nT → WOF F E nS nT := fun w' => w + eInf F • (w' - w)
  let u : WOF F E nS nT → WOF F E nS nT := fun w' => w' - a w'
  have hsmc : Continuous fun y : WOF F E nS nT => eInf F • y := continuous_const_smul _
  have ha : Continuous a := continuous_const.add (hsmc.comp (continuous_sub_right w))
  have hu : Continuous u := continuous_id.sub ha
  have huw : u w = 0 := by
    show w - (w + eInf F • (w - w)) = 0
    rw [sub_self, smul_zero, add_zero, sub_self]
  have hinf : ∀ w', (u w').map (infPartF F E) = 0 := by
    intro w'
    have e : u w' = (w' - w) - eInf F • (w' - w) := sub_add_eq_sub_sub _ _ _
    funext i j
    show infPartF F E (u w' i j) = 0
    rw [e]
    exact infPartF_sub_eInf_smul _
  have hga : Continuous fun w' => g (a w') := by
    have h1 := (hsm _ L hLc hL0 w).continuous.comp
      (φ.continuous.comp ((continuous_realCo nS nT).comp (hsmc.comp (continuous_sub_right w))))
    refine h1.congr fun w' => ?_
    show g (w + L (φ (realCo F E nS nT (eInf F • (w' - w))))) = g (w + eInf F • (w' - w))
    rw [hLφ, realCh_realCo]
  have hg : Continuous fun w' => B.ψ (-symplOHF σ JS JT ξ₀ (a w') (u w')) * g (a w') :=
    (hstd.1.1.comp (continuous_symplOHF σ JS JT ξ₀ ha hu).neg).mul hga
  have hev : ∀ᶠ w' in 𝓝 w, u w' ∈ U :=
    hu.continuousAt.preimage_mem_nhds (hUo.mem_nhds (by rw [huw]; exact U.zero_mem))
  refine hg.continuousAt.congr (hev.mono fun w' hw' => ?_)
  have e := congrFun (hUf _ hw' (hinf w')) (a w')
  have e2 : a w' + u w' = w' := add_sub_cancel _ _
  show B.ψ (-symplOHF σ JS JT ξ₀ (a w') (u w')) * g (a w') = g w'
  rw [← e]
  show _ * (B.ψ (symplOHF σ JS JT ξ₀ (a w') (u w')) * g (a w' + u w')) = _
  rw [e2, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
end GlobalTheory.WeilContF
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_integral_unfolding : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ g : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ,
      (∃ U : AddSubgroup (Formalism.IndefR.DatumF.WOF F E nS nT), IsOpen (U : Set (Formalism.IndefR.DatumF.WOF F E nS nT)) ∧
        ∀ u ∈ U, u.map (Formalism.IndefR.DatumF.infPartF F E) = 0 → Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (u) g = g) →
      (∀ (k : ℕ) (L : (Fin k → ℝ) →+ Formalism.IndefR.DatumF.WOF F E nS nT), Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
        ∀ w : Formalism.IndefR.DatumF.WOF F E nS nT, ContDiff ℝ ∞ fun x => g (w + L x)) →
      Continuous g := by
  first | exact @_root_.GlobalTheory.WeilContF.continuous_of_level_real_k | exact _root_.GlobalTheory.WeilContF.continuous_of_level_real_k | (intros; apply _root_.GlobalTheory.WeilContF.continuous_of_level_real_k <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsAdmissibleEqLagrangianIntegral
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.LagrThetaAdm
open GlobalTheory.ThetaTrCont
open scoped Classical
variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]
end GlobalTheory.LagrThetaAdm
namespace GlobalTheory.LagrThetaAdm
open GlobalTheory.ThetaTrCont
open scoped Classical
variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [Invertible (2 : AdeleRing (𝓞 F) F)]
end GlobalTheory.LagrThetaAdm
namespace GlobalTheory.LagrThetaAdm
open GlobalTheory.ThetaTrCont GlobalTheory.WeilSchrodinger
open scoped Classical
theorem exists_admissible_eq_lagrangian_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
      (κ : Type) [Fintype κ]
      (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
      (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∃ l₂ ∈ (adeleClass F).adm κ, ∀ Φ ∈ schA F κ, l₂ Φ = GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JT JB ξ κ _ co hrat ν 𝓕 hν h𝓕
  have hψ : IsCharAF F B.ψ := GlobalTheory.StdCharFromIsStd.isCharAF hB.std
  set Cm : Matrix (Fin (nT + nT)) (Fin nT) (AF F ⊗[F] E) :=
    (diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id with hCm
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hfin : ν 𝓕 < ⊤ :=
    GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hKc ν h𝓕
  haveI : IsFiniteMeasure (ν.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  haveI : IsModuleTopology (AF F) (Matrix (Fin (nT + nT)) (Fin nS) (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin (nT + nT) → Fin nS → AE F E))
  have hce : Continuous co.e := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hCu : Continuous fun u : WOF F E nS nT => Cm * u := continuous_const.matrix_mul continuous_id
  have hcont : ∀ Φ ∈ schA F κ, Continuous fun u : WOF F E nS nT => thetaTr F co B.ψ Φ (Cm * u) :=
    fun Φ hΦ => ((schA_cont F B.ψ hψ.1 hψ.2.1 hΦ).2.comp hce).comp hCu
  have hint : ∀ Φ ∈ schA F κ, Integrable (fun u => thetaTr F co B.ψ Φ (Cm * u)) (ν.restrict 𝓕) := fun Φ hΦ => by
    obtain ⟨C, hC⟩ := thetaSum_schA_bdd F B.ψ hψ.1 hψ.2.1 hΦ
    exact Integrable.of_bound (hcont Φ hΦ).aestronglyMeasurable C (Filter.Eventually.of_forall fun u => hC _)
  have hadd : ∀ Φ ∈ schA F κ, ∀ Ψ ∈ schA F κ, ∀ w,
      thetaTr F co B.ψ (Φ + Ψ) w = thetaTr F co B.ψ Φ w + thetaTr F co B.ψ Ψ w := by
    intro Φ hΦ Ψ hΨ w
    have e : schr B.ψ (co.e w) (Φ + Ψ) = schr B.ψ (co.e w) Φ + schr B.ψ (co.e w) Ψ :=
      funext fun x => by simp [schr, mul_add]
    show thetaSum F (schr B.ψ (co.e w) (Φ + Ψ)) = thetaSum F (schr B.ψ (co.e w) Φ) + thetaSum F (schr B.ψ (co.e w) Ψ)
    rw [e]
    exact ((schA_cont F B.ψ hψ.1 hψ.2.1 hΦ).1 _).tsum_add ((schA_cont F B.ψ hψ.1 hψ.2.1 hΨ).1 _)
  have hsmul : ∀ (a : ℂ) (Φ : (κ → AF F) → ℂ) w, thetaTr F co B.ψ (a • Φ) w = a * thetaTr F co B.ψ Φ w := by
    intro a Φ w
    have e : schr B.ψ (co.e w) (a • Φ) = a • schr B.ψ (co.e w) Φ := funext fun x => by
      simp only [schr, Pi.smul_apply, smul_eq_mul]
      ring
    show thetaSum F (schr B.ψ (co.e w) (a • Φ)) = a * thetaSum F (schr B.ψ (co.e w) Φ)
    rw [e, thetaSum_smul]
  let L : schA F κ →ₗ[ℂ] ℂ :=
    { toFun := fun Φ => GlobalTheory.LagrTheta.lagrInt ν 𝓕 Cm (thetaTr F co B.ψ Φ)
      map_add' := fun Φ Ψ => by
        show ∫ u in 𝓕, thetaTr F co B.ψ (Φ.1 + Ψ.1) (Cm * u) ∂ν =
          ∫ u in 𝓕, thetaTr F co B.ψ Φ.1 (Cm * u) ∂ν + ∫ u in 𝓕, thetaTr F co B.ψ Ψ.1 (Cm * u) ∂ν
        simp_rw [hadd Φ.1 Φ.2 Ψ.1 Ψ.2]
        exact integral_add (hint _ Φ.2) (hint _ Ψ.2)
      map_smul' := fun a Φ => by
        show ∫ u in 𝓕, thetaTr F co B.ψ (a • Φ.1) (Cm * u) ∂ν = a • ∫ u in 𝓕, thetaTr F co B.ψ Φ.1 (Cm * u) ∂ν
        simp_rw [hsmul]
        rw [integral_const_mul, smul_eq_mul] }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend L
  have hlL : ∀ Φ (hΦ : Φ ∈ schA F κ), l Φ = L ⟨Φ, hΦ⟩ := fun Φ hΦ => LinearMap.congr_fun hl ⟨Φ, hΦ⟩
  refine ⟨l, ?_, fun Φ hΦ => hlL Φ hΦ⟩
  intro g hg
  obtain ⟨k, c, hc, hb⟩ := thetaSum_pure_le F B.ψ hψ.2.1 hg
  have hmem : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, pureA F f g ∈ schA F κ := fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩
  have hsn : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f =
        ((Finset.Iic (k, 0)).sup (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)) f := by
    intro f
    rw [Seminorm.finset_sup_apply, Seminorm.finset_sup_apply]
    congr 2
    funext i
    simp [schwartzSeminormFamily, SchwartzMap.seminorm_apply]
  refine ⟨SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (fun f => L ⟨pureA F f g, hmem f⟩)
    (fun f f' => ?_) (fun a f => ?_) ⟨Finset.Iic (k, 0), c * ν.real 𝓕, mul_nonneg hc measureReal_nonneg, fun f => ?_⟩,
    fun f => ?_⟩
  · rw [← map_add (f := _)]
    congr 1
    exact Subtype.ext (funext fun x => by simp [pureA, add_mul])
  · rw [RingHom.id_apply, ← map_smul]
    congr 1
    exact Subtype.ext (funext fun x => by simp [pureA, mul_assoc])
  · show ‖∫ u in 𝓕, thetaTr F co B.ψ (pureA F f g) (Cm * u) ∂ν‖ ≤ _
    refine (norm_setIntegral_le_of_norm_le_const hfin fun u _ => hb f (co.e (Cm * u))).trans (le_of_eq ?_)
    rw [hsn]
    ring
  · exact hlL _ (hmem f)
end GlobalTheory.LagrThetaAdm
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.GodementSumK
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH
noncomputable section
namespace GlobalTheory.CompanionTheory.GodementH
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
  {J : Type} [Fintype J]
end GlobalTheory.CompanionTheory.GodementH
end
noncomputable section
namespace GlobalTheory.CompanionTheory.GodementH
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {J : Type} [Fintype J]
end GlobalTheory.CompanionTheory.GodementH
end
noncomputable section
namespace GlobalTheory.CompanionTheory.GodementH
variable {n : ℕ}
end GlobalTheory.CompanionTheory.GodementH
end
noncomputable section
namespace GlobalTheory.CompanionTheory.GodementH
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
end GlobalTheory.CompanionTheory.GodementH
end
noncomputable section
namespace GlobalTheory.CompanionTheory.GodementH
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
end GlobalTheory.CompanionTheory.GodementH
end
noncomputable section
namespace GlobalTheory.CompanionTheory.GodementH
theorem godement_sum_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∃ σ₀ : ℝ, ∀ σ' : ℝ, σ₀ < σ' → ∃ (C : ℝ) (N : ℕ), ∀ x : G2 σ Y, Summable (fun q : Cos σ Y => a ((Quotient.out q).1 * x) ^ σ') ∧ ∑' q : Cos σ Y, a ((Quotient.out q).1 * x) ^ σ' ≤ C * (ht2 x : ℝ) ^ N := by
  intro F E _ _ _ _ _ σ B n Y r s hB hn hY b K a hb hK ha
  have hcm : IsCMExt F E σ := hB.cm
  obtain ⟨C, hC⟩ := key_bound hcm hb.2 hK ha
  have hrat : ∀ q : Cos σ Y, ∃ g : GL (Ix n) E,
      Matrix.GeneralLinearGroup.map (n := Ix n) (inclR (F := F) (E := E) (AF F)) g = (Quotient.out q).1.1 := fun q => by
    obtain ⟨g, hg⟩ := Subgroup.mem_subgroupOf.1 (Quotient.out q).2
    exact ⟨g, hg⟩
  choose g hg using hrat
  have hnz : ∀ q, ∃ f, mnr (pl b (g q)) f ≠ 0 := fun q => by
    have hP : ∃ P : Matrix (Fin n) (Ix n) E, P * (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) = 1 :=
      ⟨Matrix.fromCols 1 0, by rw [diagCols, Matrix.fromCols_mul_fromRows]; simp⟩
    obtain ⟨P, hP⟩ := hP
    have hg1 : ((g q).1 : Matrix (Ix n) (Ix n) E) * ((g q)⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hb1 : (b.1 : Matrix (Ix n) (Ix n) E) * (b⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    refine GlobalTheory.T.left_invertible_exists_nonzero_minor E (Ix n) n (pl b (g q)) ((P * ((g q).1 : Matrix (Ix n) (Ix n) E)) * (b.1 : Matrix (Ix n) (Ix n) E)) ?_
    calc (P * ((g q).1 : Matrix (Ix n) (Ix n) E)) * (b.1 : Matrix (Ix n) (Ix n) E) * pl b (g q)
        = P * ((g q).1 : Matrix (Ix n) (Ix n) E) * ((b.1 : Matrix (Ix n) (Ix n) E) * (b⁻¹).1) * ((g q)⁻¹).1 *
          (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) := by simp only [pl, Matrix.mul_assoc]
      _ = P * (((g q).1 : Matrix (Ix n) (Ix n) E) * ((g q)⁻¹).1) *
          (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) := by rw [hb1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hg1, Matrix.mul_one, hP]
  choose f₀ hf₀ using hnz
  let u : Cos σ Y → (Fin n → Ix n) → E := fun q f => mnr (pl b (g q)) f / mnr (pl b (g q)) (f₀ q)
  have hu1 : ∀ q, u q (f₀ q) = 1 := fun q => div_self (hf₀ q)
  have hinj : Function.Injective u := by
    intro q q' e
    obtain ⟨c, hc⟩ := GlobalTheory.T.plucker_minors_determine_column_space E (Ix n) n _ _ _ _ (hf₀ q) (hf₀ q') (fun f => congrFun e f)
    have hp := isPar_of_pl (hg q) (hg q') hc
    have : (Quotient.mk _ (Quotient.out q') : Cos σ Y) = Quotient.mk _ (Quotient.out q) :=
      cos_eq.2 (Subgroup.subset_closure ⟨_, hp⟩)
    rw [Quotient.out_eq, Quotient.out_eq] at this
    exact this.symm
  obtain ⟨C₁, c, hC₁, hcount⟩ := count hcm (Fin n → Ix n) (σ := σ)
  let h : Cos σ Y → ℝ := fun q => vecHt σ (u q)
  have h1 : ∀ q, 1 ≤ h q := fun q => by
    have := one_le_vecHt (σ := σ) (hu1 q)
    exact_mod_cast this
  have hcnt : ∀ T : ℝ, 1 ≤ T → {q | h q ≤ T}.Finite ∧ (Set.ncard {q | h q ≤ T} : ℝ) ≤ C₁ * T ^ c := by
    intro T hT
    obtain ⟨hfin, hle⟩ := hcount T hT
    have hmaps : Set.MapsTo u {q | h q ≤ T} {u : (Fin n → Ix n) → E | (∃ f₀, u f₀ = 1) ∧ (vecHt σ u : ℝ) ≤ T} :=
      fun q hq => ⟨⟨f₀ q, hu1 q⟩, hq⟩
    refine ⟨Set.Finite.of_injOn hmaps hinj.injOn hfin, le_trans ?_ hle⟩
    exact_mod_cast Set.ncard_le_ncard_of_injOn u hmaps hinj.injOn hfin
  have a_nonneg : ∀ y, 0 ≤ a y := fun y => by
    obtain ⟨p, t, hp, k, hk, rfl⟩ := ha.iwa y
    rw [ha.val p t hp k hk]; exact NNReal.coe_nonneg _
  refine ⟨c, fun s' hs' => ?_⟩
  have hs0 : 0 < s' := lt_of_le_of_lt (Nat.cast_nonneg c) hs'
  have hsum : Summable fun q => h q ^ (-s') := GlobalTheory.T.summable_height_pow_of_polynomial_count _ h h1 C₁ c hcnt s' hs'
  have hterm : ∀ (x : G2 σ Y) (q : Cos σ Y), a ((Quotient.out q).1 * x) ^ s' ≤
      ((C : ℝ) * (ht2 x : ℝ) ^ (2 * n)) ^ s' * h q ^ (-s') := by
    intro x q
    have hb1 := hC (Quotient.out q).1 (g q) (hg q) (f₀ q) (hf₀ q) x
    have hpos : 0 < h q := lt_of_lt_of_le one_pos (h1 q)
    have hb2 : a ((Quotient.out q).1 * x) ≤ ((C : ℝ) * (ht2 x : ℝ) ^ (2 * n)) * (h q)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hpos]; exact hb1
    calc _ ≤ (((C : ℝ) * (ht2 x : ℝ) ^ (2 * n)) * (h q)⁻¹) ^ s' := Real.rpow_le_rpow (a_nonneg _) hb2 hs0.le
      _ = _ := by
        rw [Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hpos.le, Real.rpow_neg hpos.le]
  refine ⟨(C : ℝ) ^ s' * ∑' q, h q ^ (-s'), ⌈2 * n * s'⌉₊, fun x => ?_⟩
  have hS : Summable fun q : Cos σ Y => a ((Quotient.out q).1 * x) ^ s' :=
    Summable.of_nonneg_of_le (fun q => Real.rpow_nonneg (a_nonneg _) _) (hterm x) (hsum.mul_left _)
  refine ⟨hS, ?_⟩
  have hx1 : (1 : ℝ) ≤ ht2 x := by exact_mod_cast one_le_heightGL F x.1
  have hx0 : (0 : ℝ) ≤ ht2 x := by positivity
  have hpow : ((ht2 x : ℝ) ^ (2 * n)) ^ s' ≤ (ht2 x : ℝ) ^ ⌈2 * n * s'⌉₊ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0, ← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le hx1 ?_
    push_cast
    exact Nat.le_ceil _
  have hT : 0 ≤ ∑' q, h q ^ (-s') := tsum_nonneg fun q => Real.rpow_nonneg (lt_of_lt_of_le one_pos (h1 q)).le _
  calc ∑' q : Cos σ Y, a ((Quotient.out q).1 * x) ^ s' ≤ ∑' q, ((C : ℝ) * (ht2 x : ℝ) ^ (2 * n)) ^ s' * h q ^ (-s') :=
        hS.tsum_le_tsum (hterm x) (hsum.mul_left _)
    _ = (C : ℝ) ^ s' * ((ht2 x : ℝ) ^ (2 * n)) ^ s' * ∑' q, h q ^ (-s') := by
        rw [tsum_mul_left, Real.mul_rpow (by positivity) (by positivity)]
    _ ≤ (C : ℝ) ^ s' * (ht2 x : ℝ) ^ ⌈2 * n * s'⌉₊ * ∑' q, h q ^ (-s') := by gcongr
    _ = _ := by ring
end GlobalTheory.CompanionTheory.GodementH
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaFunctionIntegrable
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContDiffDerivHeisOFLineK
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff
noncomputable section
namespace GlobalTheory.ThetaLineSmoothF
open Formalism.IndefR.DatumF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
section Form
variable (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ : E)
end Form
theorem contDiff_deriv_heisOF_line_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ (k : ℕ) (L' : (Fin k → ℝ) →+ Formalism.IndefR.DatumF.WOF F E nS nT), Continuous L' → (∀ t, (L' t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ w : Formalism.IndefR.DatumF.WOF F E nS nT, ContDiff ℝ ∞ fun x => deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L' x)) 0 := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ hψ f hf L hL hL0 k L' hL' hL0' w
  obtain ⟨lam, hl, hlam⟩ := exists_log hψ
  have hi : Continuous (fun v : Fin (k + 1) → ℝ => Fin.init v) := continuous_pi fun i => continuous_apply _
  let M : (Fin (k + 1) → ℝ) →+ WOF F E nS nT :=
    { toFun := fun v => L' (Fin.init v) + L (v (Fin.last k))
      map_zero' := by
        show L' (Fin.init (0 : Fin (k + 1) → ℝ)) + L ((0 : Fin (k + 1) → ℝ) (Fin.last k)) = 0
        rw [show Fin.init (0 : Fin (k + 1) → ℝ) = (0 : Fin k → ℝ) from rfl, Pi.zero_apply, map_zero, map_zero, add_zero]
      map_add' := fun u v => by
        show L' (Fin.init (u + v)) + L (u (Fin.last k) + v (Fin.last k)) = _
        rw [show Fin.init (u + v) = Fin.init u + Fin.init v from rfl, map_add (f := _), map_add (f := _)]
        abel }
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : ContinuousAdd (WOF F E nS nT) := inferInstanceAs (ContinuousAdd (Fin nT → Fin nS → AF F ⊗[F] E))
  have hM : Continuous M := (hL'.comp hi).add (hL.comp (continuous_apply _))
  have hM0 : ∀ v, (M v).map (finPartF F E) = 0 := fun v => by
    show (L' (Fin.init v) + L (v (Fin.last k))).map (finPartF F E) = 0
    rw [Matrix.map_add _ (map_add _), hL0', hL0, add_zero]
  have hg : ContDiff ℝ ∞ fun v => f (w + M v) := hf.smooth (k + 1) M hM hM0 w
  have hsnoc : ContDiff ℝ ∞ (fun p : (Fin k → ℝ) × ℝ => (Fin.snoc (α := fun _ => ℝ) p.1 p.2 : Fin (k + 1) → ℝ)) := by
    refine contDiff_pi.2 fun i => ?_
    induction i using Fin.lastCases with
    | last => simp only [Fin.snoc_last]; exact contDiff_snd
    | cast j => simp only [Fin.snoc_castSucc]; exact (contDiff_apply ℝ (fun _ => ℝ) j).comp contDiff_fst
  let h : (Fin k → ℝ) × ℝ → ℂ := fun p => f (w + M (Fin.snoc (α := fun _ => ℝ) p.1 p.2))
  have hh : ContDiff ℝ ∞ h := hg.comp hsnoc
  have hfe : ∀ x t, f (w + L' x + L t) = h (x, t) := by
    intro x t
    show _ = f (w + (L' (Fin.init (Fin.snoc (α := fun _ => ℝ) x t)) + L (Fin.snoc (α := fun _ => ℝ) x t (Fin.last k))))
    rw [Fin.init_snoc, Fin.snoc_last, add_assoc]
  have hpsi : ∀ y (t : ℝ), B.ψ (symplOHF σ JS JT ξ₀ y (L t)) =
      Complex.exp (t * lam (symplOHF σ JS JT ξ₀ y (L 1))) := by
    intro y t
    rw [hlam _ (snd_symplOHF σ JS JT ξ₀ y _ (hL0 t))]
    congr 1
    let φ : ℝ →+ ℂ :=
      { toFun := fun t => lam (symplOHF σ JS JT ξ₀ y (L t))
        map_zero' := by rw [map_zero L, symplOHF_zero_right, map_zero]
        map_add' := fun a b => by rw [map_add L, symplOHF_add_right, map_add (f := _)] }
    have hφ : Continuous φ := hl.comp (continuous_symplOHF σ JS JT ξ₀ continuous_const hL)
    have := (φ.toRealLinearMap hφ).map_smul t 1
    rw [smul_eq_mul, mul_one, Complex.real_smul] at this
    exact this
  have hd : ∀ x, HasDerivAt (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L' x))
      (lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1)) * h (x, 0) + fderiv ℝ h (x, 0) (0, 1)) 0 := by
    intro x
    have e : (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L' x)) = fun t : ℝ =>
        Complex.exp (t * lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1))) * h (x, t) := by
      funext t
      show B.ψ (symplOHF σ JS JT ξ₀ (w + L' x) (L t)) * f (w + L' x + L t) = _
      rw [hpsi, hfe]
    rw [e]
    have h0 : HasDerivAt (fun t : ℝ => (t : ℂ) * lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1)))
        (lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1))) 0 := by
      simpa using (HasDerivAt.ofReal_comp (hasDerivAt_id (0 : ℝ))).mul_const
        (lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1)))
    have hp : HasDerivAt (fun t : ℝ => (x, t)) ((0 : Fin k → ℝ), (1 : ℝ)) 0 :=
      (hasDerivAt_const (0 : ℝ) x).prodMk (hasDerivAt_id 0)
    have h2 : HasDerivAt (fun t : ℝ => h (x, t)) (fderiv ℝ h (x, 0) (0, 1)) 0 :=
      ((hh.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt (0 : ℝ) hp
    have h3 : HasDerivAt (fun t : ℝ => Complex.exp (t * lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1))) * h (x, t))
        (Complex.exp (((0 : ℝ) : ℂ) * lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1))) *
          lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1)) * h (x, 0) +
          Complex.exp (((0 : ℝ) : ℂ) * lam (symplOHF σ JS JT ξ₀ (w + L' x) (L 1))) * fderiv ℝ h (x, 0) (0, 1)) 0 :=
      h0.cexp.mul h2
    refine h3.congr_deriv ?_
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
  let φ' : (Fin k → ℝ) →+ ℂ :=
    { toFun := fun x => lam (symplOHF σ JS JT ξ₀ (L' x) (L 1))
      map_zero' := by rw [map_zero L', symplOHF_zero_left, map_zero]
      map_add' := fun a b => by rw [map_add L', symplOHF_add_left, map_add (f := _)] }
  have hφ' : ContDiff ℝ ∞ φ' :=
    (φ'.toRealLinearMap (hl.comp (continuous_symplOHF σ JS JT ξ₀ hL' continuous_const))).contDiff
  have e : (fun x => deriv (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L' x)) 0) = fun x =>
      (lam (symplOHF σ JS JT ξ₀ w (L 1)) + φ' x) * h (x, 0) + fderiv ℝ h (x, 0) (0, 1) := by
    funext x
    rw [(hd x).deriv, symplOHF_add_left, map_add (f := _)]
    rfl
  rw [e]
  have hin : ContDiff ℝ ∞ (fun x : Fin k → ℝ => (x, (0 : ℝ))) := contDiff_id.prodMk contDiff_const
  exact ((contDiff_const.add hφ').mul (hh.comp hin)).add
    (((hh.fderiv_right (m := ∞) (by simp)).comp hin).clm_apply contDiff_const)
end GlobalTheory.ThetaLineSmoothF
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_function_integrable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ (k : ℕ) (L' : (Fin k → ℝ) →+ Formalism.IndefR.DatumF.WOF F E nS nT), Continuous L' → (∀ t, (L' t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ w : Formalism.IndefR.DatumF.WOF F E nS nT, ContDiff ℝ ∞ fun x => deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w + L' x)) 0 := by
  first | exact @_root_.GlobalTheory.ThetaLineSmoothF.contDiff_deriv_heisOF_line_k | exact _root_.GlobalTheory.ThetaLineSmoothF.contDiff_deriv_heisOF_line_k | (intros; apply _root_.GlobalTheory.ThetaLineSmoothF.contDiff_deriv_heisOF_line_k <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsFinsetAnnLeK
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.SplitLagrF
open GlobalTheory.SplitInvFormF
theorem exists_finset_ann_le_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, IsSplitIdemF σ e → ∀ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) →
        ∃ G : Finset (WOF F E nS nT), (∀ g ∈ G, ∀ i j, e * g i j = g i j) ∧
          ∀ y : WOF F E nS nT, (∀ i j, cAF σ e * y i j = y i j) →
            (∀ g ∈ G, B.ψ (symplOHF σ JS JT ξ₀ g y - symplOHF σ JS JT ξ₀ y g) = 1) → y ∈ U := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he U hU
  classical
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨eh⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AEF F E) := eh.isEmbedding.t2Space
  have hψ : Continuous B.ψ := hB.std.1
  obtain ⟨he1, he2, v, ε, hpl, hsum⟩ := id he
  obtain ⟨N, Φ, hΦc, hΦi, hΦr⟩ := GlobalTheory.PlaceCoordsF.coords_at_place F E v ε hpl nS nT
  have hV : (Φ ⁻¹' (U : Set (WOF F E nS nT))) ∈ nhds (0 : Fin N → v.adicCompletion F) :=
    (hU.preimage hΦc).mem_nhds (by rw [Set.mem_preimage, map_zero]; exact U.zero_mem)
  obtain ⟨K, hK, hK0, hKn⟩ := GlobalTheory.NonarchShell.exists_compact_shell_nsmul F v N _ hV
  let Y : Set (WOF F E nS nT) := {y | ∀ i j, cAF σ e * y i j = y i j}
  have hYc : IsClosed Y := by
    simp only [Y, Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (continuous_const.mul ((continuous_apply j).comp (continuous_apply i)))
        ((continuous_apply j).comp (continuous_apply i))
  have hcc : cAF σ e * cAF σ e = cAF σ e := by rw [← map_mul, he1]
  have hYε : ∀ y ∈ Y, ∀ i j, algebraMap (AF F) (AEF F E) ε * y i j = y i j := by
    intro y hy i j
    rw [← hsum, ← hy i j]
    linear_combination (y i j) * he2 + (y i j) * hcc
  have hYn : ∀ y ∈ Y, ∀ n : ℕ, n • y ∈ Y := by
    intro y hy n i j
    show cAF σ e * (n • y i j) = n • y i j
    rw [mul_smul_comm, hy i j]
  let χ : WOF F E nS nT → WOF F E nS nT → ℂ := fun g y =>
    B.ψ (symplOHF σ JS JT ξ₀ g y - symplOHF σ JS JT ξ₀ y g)
  have hχc : ∀ g, Continuous (χ g) := fun g =>
    hψ.comp ((GlobalTheory.HeisThetaF.continuous_symplOHF_right g).sub (GlobalTheory.HeisThetaF.continuous_symplOHF_left g))
  have hχn : ∀ g y (n : ℕ), χ g (n • y) = χ g y ^ n := by
    intro g y n
    induction n with
    | zero =>
      simp only [χ, zero_smul, GlobalTheory.HeisThetaF.symplOHF_zero_left, GlobalTheory.HeisThetaF.symplOHF_zero_right, sub_zero,
        AddChar.map_zero_eq_one, pow_zero]
    | succ n ih =>
      rw [succ_nsmul, pow_succ, ← ih]
      simp only [χ]
      rw [GlobalTheory.HeisThetaF.symplOHF_add_left, GlobalTheory.HeisThetaF.symplOHF_add_right, ← AddChar.map_add_eq_mul]
      congr 1
      ring
  let S : Set (WOF F E nS nT) := Φ '' K ∩ Y
  have hSc : IsCompact S := (hK.image hΦc).inter_right hYc
  have hSdet : ∀ s ∈ S, ∃ g : WOF F E nS nT, (∀ i j, e * g i j = g i j) ∧ χ g s ≠ 1 := by
    rintro s ⟨⟨k, hk, rfl⟩, hsY⟩
    refine exists_detect (GlobalTheory.SplitDetCharF.sig_invol hB.cm) hB.std hS hT hξ hσξ he _ hsY ?_
    intro h0
    apply hK0
    rw [← map_zero Φ] at h0
    rwa [hΦi h0] at hk
  choose! gs hgsX hgsχ using hSdet
  obtain ⟨t, ht⟩ := hSc.elim_finite_subcover (fun s : S => {y | χ (gs s.1) y ≠ 1})
    (fun s => isOpen_ne_fun (hχc _) continuous_const) (fun s hs => Set.mem_iUnion.2 ⟨⟨s, hs⟩, hgsχ s hs⟩)
  refine ⟨t.image (fun s : S => gs s.1), ?_, ?_⟩
  · intro g hg
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.1 hg
    exact hgsX s.1 s.2
  · intro y hy hG
    by_contra hyU
    obtain ⟨t0, rfl⟩ := hΦr _ (hYε _ hy)
    obtain ⟨n, hn⟩ := hKn t0 hyU
    have hmem : Φ (n • t0) ∈ S := ⟨⟨_, hn, rfl⟩, by rw [map_nsmul]; exact hYn _ hy n⟩
    obtain ⟨s, hs, hsy⟩ := Set.mem_iUnion₂.1 (ht hmem)
    apply hsy
    show χ (gs s.1) (Φ (n • t0)) = 1
    rw [map_nsmul, hχn]
    have := hG (gs s.1) (Finset.mem_image_of_mem (fun s : S => gs s.1) hs)
    simp only [χ] at this ⊢
    rw [this, one_pow]
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
variable {B : Base F E}
theorem exists_open_sep_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : ξ₀ ≠ 0) (hσξ : σ ξ₀ = -ξ₀)
    {e : AEF F E} (he : IsSplitIdemF σ e) (U : AddSubgroup (conjHalf σ e nS nT))
    (hU : IsOpen (U : Set (conjHalf σ e nS nT))) :
    ∃ G : Finset (WOF F E nS nT), (∀ g ∈ G, g ∈ conjHalf σ (cAF σ e) nS nT) ∧
      ∀ y : conjHalf σ e nS nT, (∀ g ∈ G, commF σ JS JT ξ₀ B.ψ g y = 1) → y ∈ U := by
  obtain ⟨G, hG1, hG2⟩ := _root_.GlobalTheory.SplitLagrF.exists_finset_ann_le_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he
    (U.comap (projH σ nS nT he.1)) (hU.preimage (continuous_projH he.1))
  refine ⟨G, fun g hg => GlobalTheory.SplitVacF.mem_conjHalf_conj he (hG1 g hg), fun y hy => ?_⟩
  have := hG2 y.1 y.2 hy
  rwa [AddSubgroup.mem_comap, projH_coe] at this
theorem exists_compact_ann_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : ξ₀ ≠ 0) (hσξ : σ ξ₀ = -ξ₀)
    {e : AEF F E} (he : IsSplitIdemF σ e) (P : WOF F E nS nT → Prop)
    (hP : ∀ g ∈ conjHalf σ (cAF σ e) nS nT, ∃ k : ℕ, 0 < k ∧ P (k • g)) :
    ∃ K : Set (conjHalf σ e nS nT), IsCompact K ∧
      ∀ y : conjHalf σ e nS nT, (∀ g, P g → commF σ JS JT ξ₀ B.ψ g y = 1) → y ∈ K := by
  obtain ⟨i1, -⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  obtain ⟨K₀, hKo, hKc⟩ := exists_compact_open (nS := nS) (nT := nT) he
  obtain ⟨G, hG1, hG2⟩ := _root_.GlobalTheory.SplitLagrF.exists_open_sep_k hB hS hT hξ hσξ he K₀ hKo
  choose! k hk0 hk using hP
  refine (exists_compact_of_finite hKc
    (fun (y : conjHalf σ e nS nT) (g : G) => commF σ JS JT ξ₀ B.ψ g y)
    {y | ∀ g, P g → commF σ JS JT ξ₀ B.ψ g y = 1} ?_ ?_).imp fun K h => ⟨h.1, fun y hy => h.2 hy⟩
  · refine (Set.Finite.pi' (t := fun g : G => ((Polynomial.nthRoots (k g) (1 : ℂ)).toFinset : Set ℂ))
      fun g => Finset.finite_toSet _).subset ?_
    rintro _ ⟨y, hy, rfl⟩ g
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots (hk0 _ (hG1 _ g.2)),
      ← GlobalTheory.SplitVacF.commF_nsmul_left]
    exact hy _ (hk _ (hG1 _ g.2))
  · intro y y' h
    refine hG2 _ fun g hg => ?_
    have h1 : commF σ JS JT ξ₀ B.ψ g y = commF σ JS JT ξ₀ B.ψ g y' := congrFun h ⟨g, hg⟩
    rw [sub_eq_neg_add, AddSubgroup.coe_add, AddSubgroup.coe_neg, GlobalTheory.SplitVacF.commF_add_right, h1,
      GlobalTheory.SplitVacF.commF_neg_right]
end GlobalTheory.SplitLagrF
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKunfCells
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
set_option linter.unusedSectionVars false
namespace PositivityTheory.SiegelWeilFormula.kunf
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E} {nb : nA σ Y b → G2 σ Y}
theorem sigma_invol_k (B : Base F E) (hB : _root_.UpperTheory.TP.W.GoodK σ B) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]
theorem cells'_k (B : Base F E) (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hb : IsFrame2 σ Y b) {ε : ℤˣ} {w : G2 σ Y}
    (hw : inFrame b w = Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0) (hnb : IsNMap b nb) (T : nF σ Y b)
    (hT : IsND T) (γ : G2 σ Y) (hγ : γ ∈ rat2 σ Y) :
    (∃ p ∈ par2 σ Y, p ∈ rat2 σ Y ∧ ∃ ν ∈ nF σ Y b, γ = p * (w * nb ν)) ∨
    (∃ β₀ : nA σ Y b, B.ψ (-(Algebra.trace (AF F) (AE F E) (T.1.1 * β₀.1).trace)) ≠ 1 ∧
      ∃ t, IsPar (γ * nb β₀ * γ⁻¹) t ∧ Matrix.GeneralLinearGroup.det t = 1) := by
  have hb0 := hb
  obtain ⟨⟨ε₀, hε₀⟩, t₀, ht₀⟩ := hb
  have hs := _root_.PositivityTheory.SiegelWeilFormula.kunf.sigma_invol_k B hB
  set e : E := ((ε₀ : ℤ) : E) with he_def
  have he : e * e = 1 := by
    rw [he_def, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hse : σ.toRingHom e = e := map_intCast _ _
  obtain ⟨M, hM, hMf⟩ := rat_frame hε₀ hγ
  obtain ⟨hMM', hM'M⟩ := frame_inv σ.toRingHom hs e he hse M hMf
  have hMi := inFrame_inv_of_rat hM hMM'
  by_cases hc : M.toBlocks₂₁.det ≠ 0
  · left
    have hblk : M.toBlocks₂₁ * (M.toBlocks₂₂.map σ.toRingHom)ᵀ +
        M.toBlocks₂₂ * (e • (M.toBlocks₂₁.map σ.toRingHom)ᵀ) = 0 := by
      have h1 := congrArg Matrix.toBlocks₂₁ hMM'
      conv_lhs at h1 => rw [← Matrix.fromBlocks_toBlocks M]
      rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₁] at h1
      simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
        Matrix.toBlocks_fromBlocks₂₂] at h1
      rw [h1]; ext i j; simp [Matrix.toBlocks₂₁, Matrix.one_apply]
    have hν := herm_quot σ.toRingHom he _ _ hc hblk
    set νE := M.toBlocks₂₁⁻¹ * M.toBlocks₂₂ with hνE
    have hνA : (incM F νE)ᵀ = -((((ε₀ : ℤ) : AE F E)) • (incM F νE).map (cA σ)) := by
      rw [← incM_transpose', hν, incM_map_cA]
      ext i j; simp [incM, he_def]
    let ν : nA σ Y b := ⟨incM F νE, (mem_nA_iff hε₀ _).2 hνA⟩
    have hνF : ν ∈ nF σ Y b := mem_nF_iff.2 ⟨νE, rfl⟩
    have hwrat : w ∈ rat2 σ Y := rat_of_inFrame (M := jw n ((ε : ℤ) : E)) (by rw [hw, incM_jw, map_intCast]; rfl)
    refine ⟨γ * (w * nb ν)⁻¹, ?_, mul_mem hγ (inv_mem (mul_mem hwrat (nb_rat hnb hνF))), ν, hνF, by group⟩
    rw [mem_stabiliser_iff_frame_lower_block hb0, mul_inv_rev, ← nb_neg hnb, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul,
      GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hM, hnb, inFrame_w_inv hw, incM_toBlocks, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₁]
    have hcd : incM F M.toBlocks₂₁ * incM F νE = incM F M.toBlocks₂₂ := by
      rw [← incM_mul', hνE, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hc), Matrix.one_mul]
    show _ = 0
    simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul]
    change incM F M.toBlocks₂₁ * -(incM F νE) + incM F M.toBlocks₂₂ = 0
    rw [Matrix.mul_neg, hcd, neg_add_cancel]
  · right
    push Not at hc
    obtain ⟨T', hT'⟩ := mem_nF_iff.1 T.2
    have hTh : T'ᵀ = -(e • T'.map σ.toRingHom) := by
      have h1 := (mem_nA_iff hε₀ T.1.1).1 T.1.2
      rw [hT'] at h1
      apply incM_inj (F := F)
      rw [incM_transpose', h1, incM_map_cA]
      ext i j; simp [incM, he_def]
    have hTd : T'.det ≠ 0 := by
      intro h0; apply hT
      show T.1.1.det = 0
      rw [hT', incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
    have hda : e • (M.toBlocks₂₁.map σ.toRingHom)ᵀ * M.toBlocks₁₁ + (M.toBlocks₁₁.map σ.toRingHom)ᵀ * M.toBlocks₂₁ = 0 := by
      have h1 := congrArg Matrix.toBlocks₂₁ hM'M
      rw [toBlocks₂₁_mul', Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂] at h1
      rw [h1]; ext i j; simp [Matrix.toBlocks₂₁, Matrix.one_apply]
    obtain ⟨β₁, hβh, hcβ, ⟨v, w', hvw, hvw0⟩, htr⟩ :=
      exists_beta σ.toRingHom hs e he hse M.toBlocks₁₁ M.toBlocks₂₁ _ hc hda T' hTh hTd
    have hx0 : Algebra.trace F E (2 : E) ≠ 0 := by
      rw [show (2 : E) = algebraMap F E 2 from (map_ofNat (algebraMap F E) 2).symm, Algebra.trace_algebraMap, nsmul_eq_mul]
      exact mul_ne_zero (Nat.cast_ne_zero.2 Module.finrank_pos.ne') two_ne_zero
    obtain ⟨l, hl⟩ := psi_moves hB.std _ hx0
    set Λ : AE F E := algebraMap (AF F) (AE F E) l with hΛ
    have hcΛ : cA σ Λ = Λ := (cA σ).commutes l
    have hβA : (Λ • incM F β₁)ᵀ = -((((ε₀ : ℤ) : AE F E)) • (Λ • incM F β₁).map (cA σ)) := by
      have hc : ∀ x : E, cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := fun _ => rfl
      rw [Matrix.transpose_smul, ← incM_transpose', hβh]
      ext i j
      simp [incM, he_def, hcΛ, hc]
      ring
    let β₀ : nA σ Y b := ⟨Λ • incM F β₁, (mem_nA_iff hε₀ _).2 hβA⟩
    refine ⟨β₀, ?_, ?_⟩
    · have htt : Algebra.trace (AF F) (AE F E) (T.1.1 * β₀.1).trace = l * algebraMap F (AF F) (Algebra.trace F E 2) := by
        show Algebra.trace (AF F) (AE F E) (T.1.1 * (Λ • incM F β₁)).trace = _
        rw [hT', Matrix.mul_smul, Matrix.trace_smul, ← incM_mul', smul_eq_mul, hΛ, ← Algebra.smul_def,
          LinearMap.map_smul, tt_rat, htr, smul_eq_mul]
      rw [htt]; exact hl
    · set Z : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E := Matrix.fromBlocks 0 β₁ 0 0 with hZ
      have hN : Matrix.fromBlocks 1 (β₀ : Matrix (Fin n) (Fin n) (AE F E)) 0 1 = 1 + Λ • incM F Z := by
        show Matrix.fromBlocks 1 (Λ • incM F β₁) 0 1 = _
        ext (i | i) (j | j) <;> simp [hZ, incM, Matrix.one_apply]
      have h1 : incM F M * incM F (Matrix.fromBlocks (M.toBlocks₂₂.map σ.toRingHom)ᵀ (e • (M.toBlocks₁₂.map σ.toRingHom)ᵀ)
          (e • (M.toBlocks₂₁.map σ.toRingHom)ᵀ) (M.toBlocks₁₁.map σ.toRingHom)ᵀ) = 1 := by
        rw [← incM_mul', hMM']; ext i j; simp [incM, Matrix.one_apply]
      have hX : M * Z * Matrix.fromBlocks (M.toBlocks₂₂.map σ.toRingHom)ᵀ (e • (M.toBlocks₁₂.map σ.toRingHom)ᵀ)
          (e • (M.toBlocks₂₁.map σ.toRingHom)ᵀ) (M.toBlocks₁₁.map σ.toRingHom)ᵀ =
          Matrix.fromBlocks (M.toBlocks₁₁ * β₁ * (e • (M.toBlocks₂₁.map σ.toRingHom)ᵀ))
            (M.toBlocks₁₁ * β₁ * (M.toBlocks₁₁.map σ.toRingHom)ᵀ)
            (M.toBlocks₂₁ * β₁ * (e • (M.toBlocks₂₁.map σ.toRingHom)ᵀ))
            (M.toBlocks₂₁ * β₁ * (M.toBlocks₁₁.map σ.toRingHom)ᵀ) := by
        conv_lhs => enter [1, 1]; rw [← Matrix.fromBlocks_toBlocks M]
        rw [hZ, conj_blocks]
      have hP : inFrame b (γ * nb β₀ * γ⁻¹) = 1 + Λ • incM F (M * Z *
          Matrix.fromBlocks (M.toBlocks₂₂.map σ.toRingHom)ᵀ (e • (M.toBlocks₁₂.map σ.toRingHom)ᵀ)
            (e • (M.toBlocks₂₁.map σ.toRingHom)ᵀ) (M.toBlocks₁₁.map σ.toRingHom)ᵀ) := by
        rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hM, hnb, hMi, hN, Matrix.mul_add,
          Matrix.mul_one, Matrix.add_mul, h1, Matrix.mul_smul, Matrix.smul_mul, incM_mul', incM_mul']
      have h21 : (inFrame b (γ * nb β₀ * γ⁻¹)).toBlocks₂₁ = 0 := by
        rw [hP, hX, hcβ]
        ext i j; simp [Matrix.toBlocks₂₁, Matrix.one_apply, incM]
      have h11 : (inFrame b (γ * nb β₀ * γ⁻¹)).toBlocks₁₁ = 1 + Λ • incM F (Matrix.vecMulVec v w') := by
        rw [hP, hX, hvw]
        ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply, incM]
      obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 ((mem_stabiliser_iff_frame_lower_block hb0 _).2 h21)
      have ht1 := ((isPar_frame ht₀ _ t).1 ht).2
      refine ⟨t, ht, Units.ext ?_⟩
      show t.1.det = 1
      have hdet : (1 + Λ • incM F (Matrix.vecMulVec v w')).det = 1 := by
        rw [show Λ • incM F (Matrix.vecMulVec v w') =
          Matrix.vecMulVec (fun i => Λ * inclR (F := F) (AF F) (v i)) (fun j => inclR (F := F) (AF F) (w' j)) by
            ext i j; simp [incM, Matrix.vecMulVec_apply, mul_assoc]]
        apply det_one_add_rank_one
        have : (fun j => inclR (F := F) (AF F) (w' j)) ⬝ᵥ (fun i => Λ * inclR (F := F) (AF F) (v i)) =
            Λ * inclR (F := F) (AF F) (w' ⬝ᵥ v) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp [dotProduct, Finset.mul_sum, map_sum, mul_left_comm]
        rw [this, hvw0, map_zero, mul_zero]
      rw [ht1, Matrix.det_mul, Matrix.det_mul, h11, hdet, mul_one, ← Matrix.det_mul, incM_GL_mul_inv, Matrix.det_one]
theorem cells_k (B : Base F E) (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hb : IsFrame2 σ Y b) {ε : ℤˣ} {w : G2 σ Y}
    (hw : inFrame b w = Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0) (hnb : IsNMap b nb) (T : nF σ Y b)
    (hT : IsND T) (γ : G2 σ Y) (hγ : γ ∈ rat2 σ Y) :
    (∃ p ∈ par2 σ Y, p ∈ rat2 σ Y ∧ ∃ ν ∈ nF σ Y b, γ = p * (w * nb ν)) ∨
    (∃ β₀ : nA σ Y b, B.ψ (-(Algebra.trace (AF F) (AE F E) (T.1.1 * β₀.1).trace)) ≠ 1 ∧
      ∃ t, IsPar (γ * nb β₀ * γ⁻¹) t ∧ Matrix.GeneralLinearGroup.det t = 1) :=
  _root_.PositivityTheory.SiegelWeilFormula.kunf.cells'_k B hB hb hw hnb T hT γ hγ
end PositivityTheory.SiegelWeilFormula.kunf
end
end
end
