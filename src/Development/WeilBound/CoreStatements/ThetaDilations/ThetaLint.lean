module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolume
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarMapLinearScalingByDeterminant
public import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
public import CompanionTheory.AutomorphicTheory.ThetaDilations.ThetaLint

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

theorem theta_lint : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (n : ℕ) (S : Set (Fin n → Fin M → E)) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞), Measurable Φ → ∫⁻ X, Φ X ∂(thetaMeas σ J μ 𝓕 S) = (μ 𝓕)⁻¹ * ∫⁻ h in 𝓕, ∑' X : S, Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) ∂μ := by
  intro F E _ _ _ _ _ σ hcm M J hJ μ 𝓕 hμ h𝓕 n S Φ hΦ
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have := hB n M
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm M J hJ (AF F)
  have hm : ∀ X, Measurable fun h : HA (AF F) σ J => actW (AF F) σ J h⁻¹ X := fun X =>
    ((hact n).1.comp (continuous_inv.prodMk continuous_const)).measurable
  have : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.symm.toEquiv
  rw [thetaMeas, lintegral_smul_measure, lintegral_sum_measure, smul_eq_mul,
    lintegral_tsum (f := fun (X : S) h => Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) X.1)))
      fun X => (hΦ.comp (hm _)).aemeasurable]
  simp only [lintegral_map hΦ (hm _)]

theorem theta_int : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (n : ℕ) (S : Set (Fin n → Fin M → E)) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), Measurable Φ → Integrable Φ (thetaMeas σ J μ 𝓕 S) → meanC μ 𝓕 (thetaS F E σ M J Φ S) = ∫ X, Φ X ∂(thetaMeas σ J μ 𝓕 S) := _root_.CompanionTheory.PlacePermOperatorBicommutantSpan.theta_int

theorem act_rat {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {M n : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (γ : HFinIn (AF F) σ J) (X : Fin n → Fin M → E) :
    ∃ X' : Fin n → Fin M → E, actW (AF F) σ J γ.1 (ratTup (AF F) X) = ratTup (AF F) X' := by
  obtain ⟨γ, g, -, e⟩ := γ
  refine ⟨fun a => g.val *ᵥ X a, funext fun a => funext fun i => ?_⟩
  have e' : (HA.mat (AF F) σ J γ).val = g.val.map (inclR (AF F)) := (congrArg Units.val e).symm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [actW, actTup, e', ratTup, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]

theorem theta_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), (∀ h : HA (AF F) σ J, (thetaMeas σ J μ 𝓕 {X | gramE σ J X = T}).map (actW (AF F) σ J h) = thetaMeas σ J μ 𝓕 {X | gramE σ J X = T}) ∧ thetaMeas σ J μ 𝓕 {X | gramE σ J X = T} {X | gramR (AF F) σ J X = T.map (inclR (AF F))}ᶜ = 0 := _root_.CompanionTheory.PlacePermOperatorBicommutantSpan.theta_inv

end PositivityTheory.PlacePermOperatorBicommutantSpan
end
end

section -- merged from Development.WeilBound.CoreStatements.ThetaDilations.EulerMove
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

theorem euler_move : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (minf minf' : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m m' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (e : (Fin n → Fin M → AF F ⊗[F] E) → (Fin n → Fin M → AF F ⊗[F] E)) (einf : (Fin n → Fin M → Ainf F ⊗[F] E) → (Fin n → Fin M → Ainf F ⊗[F] E)) (ev : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → (Fin n → Fin M → Fv F v ⊗[F] E)), Measurable e → Measurable einf → (∀ v, Measurable (ev v)) → (∀ X, projInf (e X) = einf (projInf X) ∧ ∀ v, projV v (projFin (e X)) = ev v (projV v (projFin X))) → (∀ᶠ v in Filter.cofinite, ∀ X, ev v X ∈ latV b v ↔ X ∈ latV b v) → ∀ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c → minf.map einf = cinf • minf' → (∀ v, (m v).map (ev v) = c v • m' v) → (∀ v, m' v (latV b v) < ⊤) → IsEulerProd b I 1 minf m → IsEulerProd b (I.map e) 1 minf' m' := by
  intro F E _ _ _ _ _ σ hcm d b n M I mi mi' m m' e ei ev me mei mev hpr hG ci c hc h1 h2 hf ⟨_, hs, S₀, H⟩
  classical
  obtain ⟨S₁, hS₁⟩ := up_fin.1 hc
  have hG' := Filter.eventually_cofinite.1 hG
  obtain ⟨r1, r2, r3, r4, r5, -⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hcm d b n M
  have hBv : ∀ v, BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := fun v => by
    obtain ⟨_, _, _, _, -⟩ := GlobalTheory.T.completion_is_local_ring F v
    exact (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Fv F v)).2.2.2.2.2.2.2.1 n M
  have gd : ∀ v, v ∉ S₁ ∪ hG'.toFinset → ∀ X, ev v X ∈ latV b v ↔ X ∈ latV b v := fun v hv =>
    not_not.1 (mt hG'.mem_toFinset.2 fun h => hv (Finset.mem_union_right _ h))
  have hoff : ∀ v, v ∉ S₁ ∪ hG'.toFinset → m' v (latV b v) = m v (latV b v) := fun v hv => by
    have e1 := congrArg (fun μ => μ (latV b v)) (h2 v)
    simp only [(hS₁ _ Finset.subset_union_left).1 v hv, one_smul, Measure.map_apply (mev v) (r4 v).2.measurableSet] at e1
    rw [← e1]
    exact congrArg _ (Set.ext (gd v hv))
  refine ⟨hf, hs.congr_cofinite ((S₁ ∪ hG'.toFinset).eventually_cofinite_notMem.mono fun v hv => by simp only [hoff v hv]),
    S₀ ∪ (S₁ ∪ hG'.toFinset), fun S hS φi φ hφi hφ => ?_⟩
  have hS' : ∀ v, v ∉ S → v ∉ S₁ ∪ hG'.toFinset := fun v h h' => h (hS (Finset.mem_union_right _ h'))
  obtain ⟨-, u2⟩ := hS₁ S ((Finset.subset_union_left.trans Finset.subset_union_right).trans hS)
  obtain ⟨⟨_, _, _⟩, _, _, _⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  have := (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)).2.2.2.2.2.2.2.1 n M
  have hm : Measurable (pureL b S φi φ) := by
    have h3 : Measurable (projInf : (Fin n → Fin M → AF F ⊗[F] E) → _) := by
      have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
      have : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
      exact Measurable.of_eval fun a => Measurable.of_eval fun i =>
        ((continuous_apply_apply a i).comp r1).measurable
    exact ((hφi.comp h3).mul (Finset.measurable_fun_prod _ fun v _ =>
      (hφ v).comp ((r3 v).comp r2).measurable)).indicator (r5 S).measurableSet
  have e1 : ∀ X, pureL b S φi φ (e X) = pureL b S (fun X => φi (ei X)) (fun v X => φ v (ev v X)) X := fun X => by
    have e2 : e X ∈ intOff b S ↔ X ∈ intOff b S := forall₂_congr fun v hv => by rw [(hpr X).2, gd v (hS' v hv)]
    rw [pureL, pureL]
    by_cases hX : X ∈ intOff b S
    · rw [Set.indicator_of_mem hX, Set.indicator_of_mem (e2.2 hX)]
      simp only [(hpr X).1, (hpr X).2]
    · rw [Set.indicator_of_notMem hX, Set.indicator_of_notMem (mt e2.1 hX)]
  rw [lintegral_map hm me]
  simp only [e1]
  rw [H S (Finset.subset_union_left.trans hS) (fun X => φi (ei X)) (fun v X => φ v (ev v X)) (hφi.comp mei)
    fun v => (hφ v).comp (mev v), ← lintegral_map hφi mei, h1,
    Finset.prod_congr rfl fun v _ => (lintegral_map (hφ v) (mev v)).symm,
    tprod_congr fun v : {v // v ∉ S} => congrArg ENNReal.toReal (hoff v.1 (hS' _ v.2)).symm]
  simp only [h2, ENNReal.smul_def, lintegral_smul_measure, smul_eq_mul, Finset.prod_mul_distrib]
  rw [mul_mul_mul_comm, ← ENNReal.coe_finsetProd, ← ENNReal.coe_mul, u2, ENNReal.coe_one]
  simp

end PositivityTheory.PlacePermOperatorBicommutantSpan
end
end
