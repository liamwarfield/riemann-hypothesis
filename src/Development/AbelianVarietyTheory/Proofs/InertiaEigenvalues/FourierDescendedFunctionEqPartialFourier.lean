module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WHyp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapIsIsomSelfDualMeasureKerLEqPiHaar
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapIsIsomSelfDualMeasureKerLEqPiHaar
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.MeasTransport

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem star_smul_vec [hU : Unram F E] {r : ℕ} (a : F) (c : Fin r → E) : star (a • c) = a • star c := by
  funext i
  show star (a • c i) = a • star (c i)
  rw [Algebra.smul_def, Algebra.smul_def, star_mul', hU.star_fix, mul_comm]

def trForm [Unram F E] (r : ℕ) : LinearMap.BilinForm F (Fin r → E) :=
  LinearMap.mk₂ F (fun c b => Algebra.trace F E (star c ⬝ᵥ b))
    (fun c c' b => by simp only [star_add, add_dotProduct, map_add (f := _)])
    (fun a c b => by simp only [star_smul_vec, smul_dotProduct, map_smul])
    (fun c b b' => by simp only [dotProduct_add, map_add (f := _)])
    (fun a c b => by simp only [dotProduct_smul, map_smul])

theorem trForm_apply [Unram F E] {r : ℕ} (c b : Fin r → E) :
    trForm (F := F) r c b = Algebra.trace F E (star c ⬝ᵥ b) := rfl

theorem trace_star [hU : Unram F E] (z : E) : Algebra.trace F E (star z) = Algebra.trace F E z := by
  let σ : E ≃ₐ[F] E := AlgEquiv.ofRingEquiv (f := starRingAut) (fun a => hU.star_fix a)
  exact Algebra.trace_eq_of_algEquiv σ z

theorem trForm_symm [Unram F E] (r : ℕ) : (trForm (F := F) (E := E) r).IsSymm := by
  refine ⟨fun c b => ?_⟩
  rw [trForm_apply, trForm_apply, ← trace_star (F := F) (star b ⬝ᵥ c), ← star_dotProduct_star, star_star]

theorem trForm_sepLeft [hU : Unram F E] (r : ℕ) (c : Fin r → E) (h : ∀ b, trForm (F := F) r c b = 0) : c = 0 := by
  haveI : CharZero F := hU.charZero
  by_contra hc
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra h'
    push_neg at h'
    exact hc (funext h')
  have h1 := h (Pi.single i (star (c i))⁻¹)
  rw [trForm_apply, dotProduct_single, Pi.star_apply, mul_inv_cancel₀ (star_ne_zero.mpr hi),
    ← map_one (algebraMap F E), Algebra.trace_algebraMap, hU.finrank_eq] at h1
  norm_num at h1

theorem trForm_nondeg [Unram F E] (r : ℕ) : (trForm (F := F) (E := E) r).Nondegenerate := by
  refine ⟨fun c h => trForm_sepLeft (F := F) r c h, fun b h => trForm_sepLeft (F := F) r b fun c => ?_⟩
  rw [(trForm_symm r).eq]; exact h c

theorem kerL_eq [hU : Unram F E] (A : Et F E) (ψ : AddChar F ℂ) {r : ℕ} {x : A.K} {j : A.L ≃ₗ[E] (Fin r → E)}
    (hx : A.IsIsom x j) (y' y : A.L) :
    A.kerL ψ x y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y)) := by
  obtain ⟨b⟩ := (GlobalTheory.JR.Et.quadratic_structure F E A).1
  haveI : Module.Free A.K A.L := Module.Free.of_basis b
  haveI : Module.Finite A.K A.L := Module.Finite.of_basis b
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  haveI : Module.Finite F A.L := Module.Finite.trans A.K A.L
  haveI : Module.Finite E A.L := Module.Finite.of_restrictScalars_finite F E A.L
  unfold Et.kerL Et.psiK
  rw [hx, Algebra.trace_trace (R := F) (S := E) (T := A.L), ← Algebra.trace_trace (R := F) (S := A.K) (T := A.L)]
  congr 2
  rw [show algebraMap A.K A.L x * star y' * y = x • (star y' * y) by rw [Algebra.smul_def, mul_assoc], map_smul,
    smul_eq_mul]

end GlobalTheory.JR.MeasTransport

namespace GlobalTheory.JR.MeasTransport

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem addChar_sum (ψ : AddChar F ℂ) {ι : Type} (s : Finset ι) (f : ι → F) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddChar.map_zero_eq_one]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

theorem pi_selfDual [hU : Unram F E] (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (r : ℕ) (M : Meas r F E) :
    letI := M.mE
    SelfDual (Measure.pi fun _ : Fin r => M.μE) (fun a b => ψ (trForm (F := F) r a b)) := by
  letI := M.mE
  haveI := M.bE
  haveI := M.haarE
  haveI : IsUltrametricDist E := hU.ultraE
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  haveI : IsModuleTopology F E := isModuleTopologyOfFiniteDimensional
  haveI : IsModuleTopology F (Fin r → E) := IsModuleTopology.instPi

  let O : AddSubgroup (Fin r → E) :=
    { carrier := {v | ∀ i, ‖v i‖ ≤ 1}
      zero_mem' := by intro i; simp
      add_mem' := fun {a b} ha hb i => (IsUltrametricDist.norm_add_le_max (a i) (b i)).trans (max_le (ha i) (hb i))
      neg_mem' := fun {a} ha i => by simpa using ha i }
  have hmem : ∀ v, v ∈ O ↔ ∀ i, ‖v i‖ ≤ 1 := fun v => Iff.rfl
  have hOset : (O : Set (Fin r → E)) = Set.univ.pi fun _ => Metric.closedBall (0 : E) 1 := by
    ext v; simp [O, Set.mem_pi]
  have hOo : IsOpen (O : Set (Fin r → E)) := by
    rw [hOset]; exact isOpen_set_pi Set.finite_univ fun _ _ => IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hOk : IsCompact (O : Set (Fin r → E)) := by
    rw [hOset]; exact isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have hc := ((GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ).2.2.2
  have hdual : {y | ∀ x ∈ O, ψ (trForm (F := F) r x y) = 1} = (O : Set (Fin r → E)) := by
    ext y
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, hmem]
    constructor
    · intro h i
      refine (hc (y i)).1 fun e he => ?_
      have h1 := h (Pi.single i (star e)) (by
        intro k
        by_cases hk : k = i
        · subst hk; simp [hU.norm_star, he]
        · simp [hk])
      rw [trForm_apply] at h1
      simpa [dotProduct, Pi.single_apply, apply_ite star] using h1
    · intro h x hx
      set_option synthInstance.maxHeartbeats 100000 in
        rw [trForm_apply, dotProduct, map_sum, addChar_sum]
      refine Finset.prod_eq_one fun i _ => ?_
      rw [Pi.star_apply]
      exact (hc (y i)).2 (h i) (star (x i)) (by rw [hU.norm_star]; exact hx i)
  have hvol : (Measure.pi fun _ : Fin r => M.μE) O = 1 := by
    rw [hOset, Measure.pi_pi]; simp [M.volE]
  haveI : (Measure.pi fun _ : Fin r => M.μE).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have key := (GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ (Fin r → E) (trForm r) (trForm_symm r) (trForm_nondeg r) (Measure.pi fun _ : Fin r => M.μE) inferInstance).1 O
    hOo hOk |>.1
  rw [key, hdual, hvol, one_mul]

theorem map_selfDual [hU : Unram F E] [MeasurableSpace E] [BorelSpace E] (A : Et F E) (ψ : AddChar F ℂ) {r : ℕ}
    {x : A.K} {j : A.L ≃ₗ[E] (Fin r → E)} (hx : A.IsIsom x j) (μ : Measure A.L) (hμ : SelfDual μ (A.kerL ψ x)) :
    SelfDual (Measure.map j μ) (fun a b => ψ (trForm (F := F) r a b)) := by
  haveI : IsUltrametricDist E := hU.ultraE
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  haveI : IsModuleTopology F E := isModuleTopologyOfFiniteDimensional
  haveI : IsModuleTopology F (Fin r → E) := IsModuleTopology.instPi

  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  haveI : ContinuousAdd A.L := IsModuleTopology.toContinuousAdd F A.L
  haveI : ContinuousSMul F A.L := IsModuleTopology.toContinuousSMul F A.L
  let jF : A.L ≃ₗ[F] (Fin r → E) := j.restrictScalars F
  have hc : Continuous jF := IsModuleTopology.continuous_of_linearMap jF.toLinearMap
  have hcs : Continuous jF.symm := IsModuleTopology.continuous_of_linearMap jF.symm.toLinearMap
  let jC : A.L ≃L[F] (Fin r → E) := { jF with continuous_toFun := hc, continuous_invFun := hcs }
  have hcoe : (⇑jC : A.L → Fin r → E) = ⇑j := rfl
  have hme : MeasurableEmbedding (⇑j) := by rw [← hcoe]; exact jC.toHomeomorph.measurableEmbedding
  haveI := hμ.1
  have hfour : ∀ (g : (Fin r → E) → ℂ) (y : A.L),
      fourB (Measure.map j μ) (fun a b => ψ (trForm (F := F) r a b)) g (j y) = fourB μ (A.kerL ψ x) (g ∘ j) y := by
    intro g y
    unfold fourB
    rw [hme.integral_map]
    simp only [Function.comp, kerL_eq A ψ hx, trForm_apply]
  refine ⟨by rw [← hcoe]; exact jC.isAddHaarMeasure_map μ, fun f hf v => ?_⟩
  obtain ⟨y, rfl⟩ := j.surjective v
  have hfj : IsTest (f ∘ j) := by
    refine ⟨hf.1.comp_continuous (by rw [← hcoe]; exact jC.continuous), ?_⟩
    rw [← hcoe]; exact hf.2.comp_homeomorph jC.toHomeomorph
  rw [hfour]
  have h2 : (fourB (Measure.map j μ) (fun a b => ψ (trForm (F := F) r a b)) f) ∘ j = fourB μ (A.kerL ψ x) (f ∘ j) :=
    funext fun y => hfour f y
  rw [h2, hμ.2 _ hfj y]
  simp [map_neg]

theorem map_isIsom_eq_pi : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (r : ℕ) (M : Meas r F E) (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → (∀ y' y, A.kerL ψ x y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y))) ∧ ∀ μ : Measure A.L, SelfDual μ (A.kerL ψ x) → (letI := M.mE; Measure.map j μ = Measure.pi fun _ : Fin r => M.μE) := by
  intro F E _ _ _ _ hU A ψ hψ r M x j hx
  refine ⟨fun y' y => kerL_eq A ψ hx y' y, fun μ hμ => ?_⟩
  letI := M.mE
  haveI := M.bE
  haveI : IsUltrametricDist E := hU.ultraE
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hU.finrank_eq]; norm_num)
  haveI : IsModuleTopology F E := isModuleTopologyOfFiniteDimensional
  haveI : IsModuleTopology F (Fin r → E) := IsModuleTopology.instPi

  obtain ⟨⟨μ0, _, huniq⟩, _⟩ := GlobalTheory.JR.SelfDualUniq.selfDual_exists_unique_isTest F E ψ hψ (Fin r → E) (trForm r)
    (trForm_symm r) (trForm_nondeg r)
  exact (huniq _ (map_selfDual A ψ hx μ hμ)).trans (huniq _ (pi_selfDual ψ hψ r M)).symm

end GlobalTheory.JR.MeasTransport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapIsIsomSelfDualMeasureKerLEqPiHaarStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_isIsom_selfDualMeasure_kerL_eq_pi_haar : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (r : ℕ) (M : Meas r F E) (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → (∀ y' y, A.kerL ψ x y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y))) ∧ ∀ μ : Measure A.L, SelfDual μ (A.kerL ψ x) → (letI := M.mE; Measure.map j μ = Measure.pi fun _ : Fin r => M.μE) := by
  first | exact @GlobalTheory.JR.MeasTransport.map_isIsom_eq_pi | exact GlobalTheory.JR.MeasTransport.map_isIsom_eq_pi | (intros; apply GlobalTheory.JR.MeasTransport.map_isIsom_eq_pi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierDescendedFunctionEqPartialFourier
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.FourDesc

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem continuous_of_isStdChar {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) : Continuous (fun x => ψ x) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have h : ∀ᶠ z in 𝓝 x, ψ x = ψ z := by
    filter_upwards [Metric.closedBall_mem_nhds x one_pos] with z hz
    have hz' : ‖z - x‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have e : z = x + (z - x) := by abel
    rw [e, AddChar.map_add_eq_mul, hψ.1 (z - x) hz', mul_one]
  exact continuousAt_const.congr h

theorem continuous_star_E [Unram F E] : Continuous (star : E → E) :=
  (Isometry.of_dist_eq fun a b => by
    rw [dist_eq_norm, dist_eq_norm, ← star_sub, Unram.norm_star (F := F)]).continuous

end GlobalTheory.JR.FourDesc

open GlobalTheory.JR.FourDesc in
theorem GlobalTheory.JR.fourB_descFn : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (r : ℕ) (M : Meas r F E) (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ μ : Measure A.L, SelfDual μ (A.kerL ψ x) → ∀ (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)) (lam : F) (α : Matrix.unitaryGroup (Fin r) E → ℝ), IsLocallyConstant α → HasCompactSupport α → ∀ f : Hn r F E → ℂ, IsTest f → fourB μ (A.kerL ψ x) (A.descFn M Ax j lam α f) = A.descFn M Ax j lam α (fourU M ψ f) := by
  intro F E _ _ _ _ _ A ψ hψ r M x j hx μ hμ Ax lam α hα hαc f hf
  haveI : LocallyCompactSpace E := Unram.lcE (F := F) (E := E)
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : LocallyCompactSpace F := Unram.lcF (F := F) (E := E)
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  letI := M.mE
  haveI := M.bE
  letI := M.mU
  haveI := M.bU
  haveI := M.haarE
  haveI := M.haarU
  haveI : SigmaFinite M.μE := sigmaFinite_of_locallyFinite
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ (Unram.finrank_eq (F := F) (E := E))
  haveI : ContinuousStar E := ⟨continuous_star_E (F := F)⟩
  obtain ⟨P, hP⟩ : ∃ P : Measure (Fin r → E), P = Measure.pi fun _ => M.μE := ⟨_, rfl⟩
  haveI : SigmaFinite P := by rw [hP]; infer_instance
  haveI : IsFiniteMeasureOnCompacts P := by rw [hP]; infer_instance
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (Matrix.unitaryGroup (Fin r) E), ν = M.μU.restrict (tsupport α) := ⟨_, rfl⟩
  haveI : IsFiniteMeasure ν := by
    rw [hν]; exact isFiniteMeasure_restrict.2 hαc.isCompact.measure_lt_top.ne
  haveI : IsFiniteMeasureOnCompacts (P.prod ν) := inferInstance
  have hψc := continuous_of_isStdChar hψ
  have htr : Continuous (fun e : E => Algebra.trace F E e) :=
    LinearMap.continuous_of_finiteDimensional (Algebra.trace F E)
  have hfc : Continuous f := hf.1.continuous
  have hαcont : Continuous α := hα.continuous
  have hstar : ∀ (g : Matrix.unitaryGroup (Fin r) E) (v w : Fin r → E),
      star (g.1 *ᵥ v) ⬝ᵥ (g.1 *ᵥ w) = star v ⬝ᵥ w := by
    intro g v w
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose,
      Unitary.star_mul_self_of_mem g.2, Matrix.one_mulVec]
  let jg : Matrix.unitaryGroup (Fin r) E → (A.L ≃ₗ[E] (Fin r → E)) :=
    fun g => j.trans (Matrix.UnitaryGroup.toLinearEquiv g)
  have hjg : ∀ g y, jg g y = g.1 *ᵥ j y := fun g y => rfl
  have hjgI : ∀ g, A.IsIsom x (jg g) := fun g y y' => by rw [hjg, hjg, hstar, hx]
  have I := GlobalTheory.T.map_isIsom_selfDualMeasure_kerL_eq_pi_haar F E A ψ hψ r M x
  have hker : ∀ y' y, A.kerL ψ x y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y)) := (I j hx).1
  have hmapj : Measure.map j μ = P := by rw [hP]; exact (I j hx).2 μ hμ
  have hmapg : ∀ g, Measure.map (jg g) μ = P := fun g => by rw [hP]; exact (I (jg g) (hjgI g)).2 μ hμ
  have hjc : Continuous j :=
    IsModuleTopology.continuous_of_linearMap (R := F) ((j : A.L →ₗ[E] (Fin r → E)).restrictScalars F)
  have hjm : Measurable j := hjc.measurable
  have hgc : ∀ g : Matrix.unitaryGroup (Fin r) E, Continuous (fun v : Fin r → E => g.1 *ᵥ v) :=
    fun g => continuous_const.matrix_mulVec continuous_id
  have hPg : ∀ g : Matrix.unitaryGroup (Fin r) E, Measure.map (fun v => g.1 *ᵥ v) P = P := by
    intro g
    have e : (fun v => g.1 *ᵥ v) ∘ j = ⇑(jg g) := funext fun y => (hjg g y).symm
    conv_lhs => rw [← hmapj]
    rw [Measure.map_map (hgc g).measurable hjm, e, hmapg g]
  have hres : ∀ h : Matrix.unitaryGroup (Fin r) E → ℂ, (∀ g, g ∉ tsupport α → h g = 0) →
      ∫ g, h g ∂ν = ∫ g, h g ∂M.μU := by
    intro h hh
    rw [hν]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero hh
  funext y
  let G : (Fin r → E) → Matrix.unitaryGroup (Fin r) E → ℂ := fun v g =>
    f (actU g (Ax, v, lam)) * (α g : ℂ) * ψ (Algebra.trace F E (star v ⬝ᵥ j y))
  have hact : Continuous (fun p : (Fin r → E) × Matrix.unitaryGroup (Fin r) E => actU p.2 (Ax, p.1, lam)) := by
    unfold actU
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) (Continuous.prodMk ?_ continuous_const)
    · fun_prop
    · fun_prop
  have hGc : Continuous (Function.uncurry G) := by
    have h1 : Continuous (fun p : (Fin r → E) × Matrix.unitaryGroup (Fin r) E => star p.1 ⬝ᵥ j y) := by fun_prop
    exact ((hfc.comp hact).mul (Complex.continuous_ofReal.comp (hαcont.comp continuous_snd))).mul
      (hψc.comp (htr.comp h1))
  have hGs : HasCompactSupport (Function.uncurry G) := by
    refine HasCompactSupport.intro (((hf.2.isCompact.prod hαc.isCompact).image
      (f := fun q : Hn r F E × Matrix.unitaryGroup (Fin r) E => (star q.2.1 *ᵥ q.1.2.1, q.2)) (by fun_prop))) ?_
    rintro ⟨v, g⟩ hvg
    by_contra hne
    apply hvg
    have h1 : f (actU g (Ax, v, lam)) ≠ 0 := fun h => hne (by simp [G, h])
    have h2 : α g ≠ 0 := fun h => hne (by simp [G, h])
    refine ⟨(actU g (Ax, v, lam), g), ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩, ?_⟩
    simp only [actU, Prod.mk.injEq, and_true]
    rw [Matrix.mulVec_mulVec, Unitary.star_mul_self_of_mem g.2, Matrix.one_mulVec]
  have hGi : Integrable (Function.uncurry G) (P.prod ν) := hGc.integrable_of_hasCompactSupport hGs
  have hL : fourB μ (A.kerL ψ x) (A.descFn M Ax j lam α f) y = ∫ v, ∫ g, G v g ∂ν ∂P := by
    have e : ∀ y', A.descFn M Ax j lam α f y' * A.kerL ψ x y' y = (fun v => ∫ g, G v g ∂ν) (j y') := by
      intro y'
      simp only [Et.descFn, hker, G]
      rw [← hres _ (fun g hg => by simp [image_eq_zero_of_notMem_tsupport hg]), ← integral_mul_const]
    simp only [fourB, e]
    rw [← hmapj, integral_map hjm.aemeasurable (by
      rw [hmapj]; exact (hGc.stronglyMeasurable.integral_prod_right (ν := ν)).aestronglyMeasurable)]
  rw [hL, integral_integral_swap hGi]
  simp only [Et.descFn]
  rw [← hres _ (fun g hg => by simp [image_eq_zero_of_notMem_tsupport hg])]
  congr 1
  funext g
  have e1 : ∀ v, G v g = (f ((actU g (Ax, j y, lam)).1, g.1 *ᵥ v, lam) *
      ψ (Algebra.trace F E (star (g.1 *ᵥ v) ⬝ᵥ (actU g (Ax, j y, lam)).2.1))) * (α g : ℂ) := by
    intro v
    simp only [G, actU, hstar]
    ring
  simp_rw [e1]
  rw [integral_mul_const]
  congr 1
  have hHc : Continuous (fun c : Fin r → E => f ((actU g (Ax, j y, lam)).1, c, lam) *
      ψ (Algebra.trace F E (star c ⬝ᵥ (actU g (Ax, j y, lam)).2.1))) := by
    have h1 : Continuous (fun c : Fin r → E => star c ⬝ᵥ (actU g (Ax, j y, lam)).2.1) := by fun_prop
    have h2 : Continuous (fun c : Fin r → E => ((actU g (Ax, j y, lam)).1, c, lam)) := by fun_prop
    exact (hfc.comp h2).mul (hψc.comp (htr.comp h1))
  have key : ∫ c, (fun c : Fin r → E => f ((actU g (Ax, j y, lam)).1, c, lam) *
      ψ (Algebra.trace F E (star c ⬝ᵥ (actU g (Ax, j y, lam)).2.1))) c ∂(Measure.map (fun v => g.1 *ᵥ v) P) =
      ∫ v, (fun c : Fin r → E => f ((actU g (Ax, j y, lam)).1, c, lam) *
      ψ (Algebra.trace F E (star c ⬝ᵥ (actU g (Ax, j y, lam)).2.1))) (g.1 *ᵥ v) ∂P :=
    integral_map (hgc g).measurable.aemeasurable (by rw [hPg g]; exact hHc.aestronglyMeasurable)
  rw [hPg g] at key
  rw [key.symm]
  simp only [fourU]
  rw [hP]
  rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierDescendedFunctionEqPartialFourierStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_descendedFunction_eq_partialFourier : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (r : ℕ) (M : Meas r F E) (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ μ : Measure A.L, SelfDual μ (A.kerL ψ x) → ∀ (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)) (lam : F) (α : Matrix.unitaryGroup (Fin r) E → ℝ), IsLocallyConstant α → HasCompactSupport α → ∀ f : Hn r F E → ℂ, IsTest f → fourB μ (A.kerL ψ x) (A.descFn M Ax j lam α f) = A.descFn M Ax j lam α (fourU M ψ f) := by
  first | exact @GlobalTheory.JR.fourB_descFn | exact GlobalTheory.JR.fourB_descFn | (intros; apply GlobalTheory.JR.fourB_descFn <;> assumption)
end
