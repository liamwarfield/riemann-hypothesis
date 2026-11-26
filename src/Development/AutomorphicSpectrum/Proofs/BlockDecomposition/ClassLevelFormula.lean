module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationInvariantDoubledFormConjProduct
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonInert
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SwMeasPlaneOfNotRepresented

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClassLevelFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClassLevelFormula
noncomputable section

namespace GlobalTheory.CompanionTheory.GunrClassLev

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M n d : ℕ} {J : Matrix (Fin M) (Fin M) E} {T : Matrix (Fin n) (Fin n) E}
  {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ψv : Fv F v → ℂ} {S : Subring (Fv F v ⊗[F] E)}
  {σS : S →+* S} {ϖ : Fv F v} {ε : ℤ}

theorem coe_mul_pS_pow (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (k : ℕ) (t : S) :
    ((t * hG.pS ^ k : S) : Fv F v ⊗[F] E) = (ϖ ^ k) • (t : Fv F v ⊗[F] E) := by
  rw [Subring.coe_mul, Subring.coe_pow, Algebra.smul_def, map_pow, mul_comm]
  rfl

theorem smul_sub_mem_iff (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (k : ℕ) (s s' : S) :
    (ϖ ^ k)⁻¹ • (s : Fv F v ⊗[F] E) - (ϖ ^ k)⁻¹ • (s' : Fv F v ⊗[F] E) ∈ S ↔ s - s' ∈ lev hG.pS k := by
  have hne : ϖ ^ k ≠ 0 := pow_ne_zero _ hG.unif_ne
  constructor
  · intro h
    refine Ideal.mem_span_singleton'.2 ⟨⟨_, h⟩, Subtype.ext ?_⟩
    rw [coe_mul_pS_pow hG]
    show (ϖ ^ k) • ((ϖ ^ k)⁻¹ • (s : Fv F v ⊗[F] E) - (ϖ ^ k)⁻¹ • (s' : Fv F v ⊗[F] E)) = (s : Fv F v ⊗[F] E) - s'
    rw [← smul_sub, smul_smul, mul_inv_cancel₀ hne, one_smul]
  · intro h
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
    have e : (s : Fv F v ⊗[F] E) - (s' : Fv F v ⊗[F] E) = (ϖ ^ k) • (c : Fv F v ⊗[F] E) := by
      rw [← coe_mul_pS_pow hG, hc, AddSubgroupClass.coe_sub]
    rw [← smul_sub, e, smul_smul, inv_mul_cancel₀ hne, one_smul]
    exact c.2

theorem classLev : ClassLev := by
  intro F E _ _ _ _ _ σ M n d J T bs v ψv S σS ϖ ε hG k X X' hX hX'
  constructor
  · intro h
    refine Matrix.ext fun a b => ?_
    exact Ideal.Quotient.eq.2 ((smul_sub_mem_iff hG k (X a b) (X' a b)).1 (h a b))
  · intro h a b
    exact (smul_sub_mem_iff hG k (X a b) (X' a b)).2 (Ideal.Quotient.eq.1 (congrFun (congrFun h a) b))

end GlobalTheory.CompanionTheory.GunrClassLev

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClassLevelFormulaStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.class_level_formula : PositivityTheory.SiegelWeilFormula.Gunr.ClassLev := by
  first | exact @GlobalTheory.CompanionTheory.GunrClassLev.classLev | exact GlobalTheory.CompanionTheory.GunrClassLev.classLev | (intros; apply GlobalTheory.CompanionTheory.GunrClassLev.classLev <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwCentRatFComm
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwCentRatFComm
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.RatCentComm

theorem commute_norm {G : Type} [Group G] (θ : G →* G) (hθ : ∀ g, θ (θ g) = g) (D g : G)
    (hg : g ∈ twCent θ D) : g * (D * θ D) = (D * θ D) * g := by
  have h1 : g * D = D * θ g := hg
  have h2 : θ g = D⁻¹ * g * D := by rw [mul_assoc, h1]; group
  have h3 := congrArg θ h2
  rw [hθ, map_mul, map_mul, map_inv, h2] at h3
  calc g * (D * θ D)
      = (D * θ D) * ((θ D)⁻¹ * (D⁻¹ * g * D) * θ D) := by group
    _ = _ := by rw [← h3]

theorem twCent_ratF_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (δ : GL (Fin n) E),
    (δ * thE E n δ).val.charpoly.Separable →
    ∀ a ∈ twCent (thF E n) (ratF E n δ), ∀ b ∈ twCent (thF E n) (ratF E n δ), a * b = b * a := by
  intro E _ _ _ n δ hs a ha b hb
  have hθ : ∀ g, thF E n (thF E n g) = g :=
    GlobalTheory.LocTwist.thetaGL_thetaGL n _ (fun y => GlobalTheory.ThetaPull.cFin_cFin y)
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field _ hs
  have hv' : IsUnit (GlobalTheory.ClassParam.krylov (ratF E n δ * thF E n (ratF E n δ)).val
      (algebraMap E (Af E) ∘ v)).det := by
    have h1 := (IsUnit.mk0 _ hv).map (algebraMap E (Af E))
    rw [RingHom.map_det, RingHom.mapMatrix_apply, GlobalTheory.ClassParam.krylov_map] at h1
    rw [GlobalTheory.MassNorm.thF_ratF, ← map_mul]
    exact h1
  have hc : ∀ g ∈ twCent (thF E n) (ratF E n δ),
      Commute g.val (ratF E n δ * thF E n (ratF E n δ)).val := fun g hg => by
    change g.val * _ = _ * g.val
    rw [← Units.val_mul, ← Units.val_mul, commute_norm _ hθ _ _ hg]
  obtain ⟨p, hp⟩ := GlobalTheory.MassNorm.aeval_of_commute_cyclic _ hv' (hc a ha)
  obtain ⟨q, hq⟩ := GlobalTheory.MassNorm.aeval_of_commute_cyclic _ hv' (hc b hb)
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, hp, hq, ← map_mul, ← map_mul, mul_comm]

end GlobalTheory.CompanionTheory.RatCentComm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwCentRatFCommStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twCent_comm_of_charpoly_separable : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (δ : GL (Fin n) E),
  (δ * thE E n δ).val.charpoly.Separable →
  ∀ a ∈ twCent (thF E n) (ratF E n δ), ∀ b ∈ twCent (thF E n) (ratF E n δ), a * b = b * a := by
  first | exact @GlobalTheory.CompanionTheory.RatCentComm.twCent_ratF_comm | exact GlobalTheory.CompanionTheory.RatCentComm.twCent_ratF_comm | (intros; apply GlobalTheory.CompanionTheory.RatCentComm.twCent_ratF_comm <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelExhaustion
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelExhaustion
noncomputable section

namespace GlobalTheory.CompanionTheory.GunrExhaust

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen Filter Topology
open PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem eventually_pow_mul_mem {v : HeightOneSpectrum (𝓞 F)} {ϖ : Fv F v} (h : ‖ϖ‖ < 1) (c : Fv F v) :
    ∀ᶠ k : ℕ in atTop, ϖ ^ k * c ∈ v.adicCompletionIntegers F := by
  have h0 : Tendsto (fun k : ℕ => ‖ϖ‖ ^ k * ‖c‖) atTop (𝓝 (0 * ‖c‖)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h).mul_const _
  rw [zero_mul] at h0
  filter_upwards [h0.eventually (gt_mem_nhds one_pos)] with k hk
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff, norm_mul, norm_pow]
  exact hk.le

theorem eventually_smul_mem {σ : E →ₐ[F] E} {M n d : ℕ} {J : Matrix (Fin M) (Fin M) E} {T : Matrix (Fin n) (Fin n) E}
    {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ψv : Fv F v → ℂ} {S : Subring (Fv F v ⊗[F] E)}
    {σS : S →+* S} {ϖ : Fv F v} {ε : ℤ} (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (x : Fv F v ⊗[F] E) :
    ∀ᶠ k : ℕ in atTop, ϖ ^ k • x ∈ S := by
  have h : ∀ᶠ k : ℕ in atTop, ∀ i, ϖ ^ k * (Algebra.TensorProduct.basis (Fv F v) bs).repr x i ∈
      v.adicCompletionIntegers F :=
    eventually_all.2 fun i => eventually_pow_mul_mem hG.unif_lt _
  filter_upwards [h] with k hk
  have hmem : ϖ ^ k • x ∈ (S : Set (Fv F v ⊗[F] E)) := by
    rw [hG.carrier]
    intro i
    simpa [map_smul] using hk i
  exact hmem

theorem exhaust : Exhaust := by
  intro F E _ _ _ _ _ σ M n d J T bs v ψv S σS ϖ ε hG b
  have h : ∀ᶠ k : ℕ in atTop, ∀ a c, ϖ ^ k • (b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a c ∈ S :=
    eventually_all.2 fun a => eventually_all.2 fun c => eventually_smul_mem hG _
  obtain ⟨k, hk⟩ := h.exists
  have hX : PositivityTheory.PfSWUS.Loc.cT σS (Matrix.of fun a c => (⟨_, hk a c⟩ : S)) = Matrix.of fun a c => (⟨_, hk a c⟩ : S) := by
    ext a c
    have hb := b.2 a c
    simp only [PositivityTheory.PfSWUS.Loc.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]
    rw [hG.sig]
    simp only [sigR_smul]
    exact congrArg _ hb
  refine ⟨k, _, hX, ?_⟩
  apply Subtype.ext
  funext a c
  show (b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a c = (ϖ ^ k)⁻¹ • ϖ ^ k • (b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a c
  rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hG.unif_ne), one_smul]

end GlobalTheory.CompanionTheory.GunrExhaust

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelExhaustionStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_exhaustion : PositivityTheory.SiegelWeilFormula.Gunr.Exhaust := by
  first | exact @GlobalTheory.CompanionTheory.GunrExhaust.exhaust | exact GlobalTheory.CompanionTheory.GunrExhaust.exhaust | (intros; apply GlobalTheory.CompanionTheory.GunrExhaust.exhaust <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonsplitPlacePairEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonsplitPlacePairEquiv
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.LocHypInert

open GlobalTheory.CompanionTheory.LocInert

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cjv_apply (hC : CjEx) {w : Pl E} (hw : ¬ IsSplitAt w)
    (x : Av (w.under (𝓞 (maximalRealSubfield E)))) : evR hw (cjv _ x) = cj w (evR hw x) := by
  have h := hC E (w.under (𝓞 (maximalRealSubfield E)))
  set X : Af E := sLoc E w (evR hw x) with hX
  have hp : pLoc E w X = evR hw x := by
    change (Pi.single w (evR hw x) : ∀ u : Pl E, u.adicCompletion E) w = _
    simp
  have hx : projv _ X = x := by
    funext u
    obtain rfl := eq_aw hw u
    exact hp
  have hs : cjv (w.under (𝓞 (maximalRealSubfield E))) = h.choose := by
    rw [cjv, dite_eq_left h]
  rw [← hx, hs, ← h.choose_spec.2 X, evR_apply, evR_apply]
  change pLoc E w (conjFin (IsCMField.complexConj E).toRingEquiv X) = cj w (pLoc E w X)
  rw [pLoc_conjFin]
  exact GlobalTheory.BCT.GlobLev.conjLoc_eq_cj hw X

theorem evY_thv (hC : CjEx) {w : Pl E} (hw : ¬ IsSplitAt w) (a b : ℕ)
    (y : Yv a b (w.under (𝓞 (maximalRealSubfield E)))) :
    evY hw a b (thv a b _ y) = ((thL a w).prodMap (thL b w)) (evY hw a b y) := by
  have h : ∀ n (g : GL (Fin n) (Av (w.under (𝓞 (maximalRealSubfield E))))),
      GeneralLinearGroup.map (evR hw).toRingHom (thetaGL n (cjv _) g) =
        thL n w (GeneralLinearGroup.map (evR hw).toRingHom g) := fun n g => by
    rw [thL, if_neg hw]
    exact GlobalTheory.ThetaPull.map_thetaGL _ _ _ (cjv_apply hC hw) g
  exact Prod.ext (h a y.1) (h b y.2)

theorem inert_iso : CjEx → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (v : PlF E) (w : Above v), ¬ IsSplitAt w.1 →
  ∃ e : Yv a b v ≃ₜ* (GLw a w.1 × GLw b w.1), (∀ y, e y = evw w y) ∧
    (∀ y, e (thv a b v y) = ((thL a w.1).prodMap (thL b w.1)) (e y)) ∧ ∀ y, y ∈ Kv a b v ↔ e y ∈ K2 a b w.1 := by
  intro hC E _ _ _ a b v w hw
  obtain ⟨w, rfl⟩ := w
  exact ⟨evY hw a b, evY_apply hw a b, evY_thv hC hw a b, mem_Kv_iff hw a b⟩

end GlobalTheory.CompanionTheory.LocHypInert

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonsplitPlacePairEquivStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonsplit_place_pair_equiv : CjEx → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (v : PlF E) (w : Above v), ¬ IsSplitAt w.1 →
  ∃ e : Yv a b v ≃ₜ* (GLw a w.1 × GLw b w.1), (∀ y, e y = evw w y) ∧
    (∀ y, e (thv a b v y) = ((thL a w.1).prodMap (thL b w.1)) (e y)) ∧ ∀ y, y ∈ Kv a b v ↔ e y ∈ K2 a b w.1 := by
  first | exact @GlobalTheory.CompanionTheory.LocHypInert.inert_iso | exact GlobalTheory.CompanionTheory.LocHypInert.inert_iso | (intros; apply GlobalTheory.CompanionTheory.LocHypInert.inert_iso <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetMeasureFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetMeasureFormula
noncomputable section

namespace GlobalTheory.CompanionTheory.GunrCoset

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isOpen_Rv {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (Rv bs v) := by
  have hO : IsOpen ((v.adicCompletionIntegers F : ValuationSubring (Fv F v)) : Set (Fv F v)) :=
    Valued.isOpen_valuationSubring _
  have hc : ∀ k : Fin d, Continuous fun y : Fv F v ⊗[F] E =>
      (Algebra.TensorProduct.basis (Fv F v) bs).repr y k := fun k =>
    (continuous_apply k).comp (GlobalTheory.CompanionTheory.SW.TopK.isHomeomorph_coord (Fv F v) bs).continuous
  have : Rv bs v = ⋂ k : Fin d, (fun y : Fv F v ⊗[F] E =>
      (Algebra.TensorProduct.basis (Fv F v) bs).repr y k) ⁻¹'
        ((v.adicCompletionIntegers F : ValuationSubring (Fv F v)) : Set (Fv F v)) := by
    ext y
    simp [Rv]
  rw [this]
  exact isOpen_iInter_of_finite fun k => hO.preimage (hc k)

theorem continuousAdd_tens (v : HeightOneSpectrum (𝓞 F)) : ContinuousAdd (Fv F v ⊗[F] E) :=
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := GlobalTheory.CompanionTheory.SW.TopK.isModTop (Fv F v)
  IsModuleTopology.toContinuousAdd (Fv F v) _

theorem isOpen_integral_hermitian (σ : E →ₐ[F] E) (n : ℕ) {v : HeightOneSpectrum (𝓞 F)} (S : Subring (Fv F v ⊗[F] E))
    (hS : IsOpen (S : Set (Fv F v ⊗[F] E))) :
    IsOpen (H0 S σ n : Set (HermR (Fv F v) σ n)) := by
  have : (H0 S σ n : Set (HermR (Fv F v) σ n)) =
      ⋂ i : Fin n, ⋂ j : Fin n, (fun b : HermR (Fv F v) σ n =>
        (b : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) i j) ⁻¹' (S : Set (Fv F v ⊗[F] E)) := by
    ext b
    simp only [Set.mem_iInter, Set.mem_preimage]
    rfl
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    hS.preimage (continuous_subtype_val.matrix_elem i j)

theorem cosetMeas : CosetMeas := by
  intro F E _ _ _ _ _ σ M n d J T bs v ψv S σS ϖ ε hG
  haveI : ContinuousAdd (Fv F v ⊗[F] E) := continuousAdd_tens v
  haveI : BorelSpace (HermR (Fv F v) σ n) := ⟨rfl⟩
  have hS : IsOpen (S : Set (Fv F v ⊗[F] E)) := by
    rw [hG.carrier]
    exact isOpen_Rv bs v
  haveI : ContinuousAdd (HermR (Fv F v) σ n) := ⟨continuous_induced_rng.2
    ((continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd))⟩
  refine ⟨⟨fun c => (continuous_const.add continuous_id).measurable,
    fun c => (continuous_id.add continuous_const).measurable⟩, fun g => ?_⟩
  have hc : Continuous fun x : HermR (Fv F v) σ n => x + -g := continuous_id.add continuous_const
  have : {x : HermR (Fv F v) σ n | x - g ∈ H0 S σ n} =
      (fun x : HermR (Fv F v) σ n => x + -g) ⁻¹' (H0 S σ n : Set (HermR (Fv F v) σ n)) := by
    ext x
    simp [sub_eq_add_neg]
  rw [this]
  exact ((isOpen_integral_hermitian σ n S hS).preimage hc).measurableSet

end GlobalTheory.CompanionTheory.GunrCoset

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetMeasureFormulaStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_measure_formula : PositivityTheory.SiegelWeilFormula.Gunr.CosetMeas := by
  first | exact @GlobalTheory.CompanionTheory.GunrCoset.cosetMeas | exact GlobalTheory.CompanionTheory.GunrCoset.cosetMeas | (intros; apply GlobalTheory.CompanionTheory.GunrCoset.cosetMeas <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalMatrixIntegral
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalMatrixIntegral
noncomputable section

namespace GlobalTheory.CompanionTheory.Gunr

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

theorem inclR_mem_Rv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ}
    (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (e : E)
    (h : ∀ k, algebraMap F (Fv F v) (bs.repr e k) ∈ v.adicCompletionIntegers F) :
    inclR (F := F) (Fv F v) e ∈ Rv bs v := by
  simp only [Rv, Set.mem_ofPred_eq]
  intro k
  rw [show inclR (F := F) (Fv F v) e = (1 : Fv F v) ⊗ₜ[F] e from rfl,
    Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]
  exact h k

theorem sigR_inclR {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    sigR (Fv F v) σ (inclR (F := F) (Fv F v) e) = inclR (F := F) (Fv F v) (σ e) := by
  show Algebra.TensorProduct.map (AlgHom.id F (Fv F v)) σ ((1 : Fv F v) ⊗ₜ[F] e)
    = (1 : Fv F v) ⊗ₜ[F] σ e
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

theorem coe_det_matS {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} (S : Subring (Fv F v ⊗[F] E)) {m : ℕ} (X : Matrix (Fin m) (Fin m) E)
    (hX : ∀ i j, inclR (F := F) (Fv F v) (X i j) ∈ S) :
    (((matS S X hX).det : S) : Fv F v ⊗[F] E) = inclR (F := F) (Fv F v) X.det := by
  have h1 : S.subtype.mapMatrix (matS S X hX) = (inclR (F := F) (Fv F v)).mapMatrix X := by
    ext i j
    rfl
  rw [show (((matS S X hX).det : S) : Fv F v ⊗[F] E) = S.subtype (matS S X hX).det from rfl,
    RingHom.map_det, h1, ← RingHom.map_det]

theorem locMat : LocMat := by
  unfold LocMat
  intro F E _ _ _ _ _ σ d bs v S σS hS hσS m X hherm hdet hint
  have memS : ∀ e : E, (∀ k, algebraMap F (Fv F v) (bs.repr e k) ∈ v.adicCompletionIntegers F) →
      inclR (F := F) (Fv F v) e ∈ S := by
    intro e he
    have h := inclR_mem_Rv bs v e he
    rw [← hS] at h
    exact h
  have hX : ∀ i j, inclR (F := F) (Fv F v) (X i j) ∈ S := by
    intro i j
    apply memS
    intro k
    apply hint
    simp only [matSet, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inl ⟨(i, j, k), rfl⟩
  have hinv : inclR (F := F) (Fv F v) X.det⁻¹ ∈ S := by
    apply memS
    intro k
    apply hint
    simp only [matSet, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr ⟨k, rfl⟩
  refine ⟨hX, ?_, ?_⟩
  · ext i j
    show ((σS (matS S X hX j i) : S) : Fv F v ⊗[F] E) = inclR (F := F) (Fv F v) (X i j)
    rw [hσS]
    show sigR (Fv F v) σ (inclR (F := F) (Fv F v) (X j i)) = inclR (F := F) (Fv F v) (X i j)
    rw [sigR_inclR, hherm]
  · refine isUnit_iff_exists_inv.mpr ⟨⟨inclR (F := F) (Fv F v) X.det⁻¹, hinv⟩, ?_⟩
    apply Subtype.ext
    show (((matS S X hX).det : S) : Fv F v ⊗[F] E) * inclR (F := F) (Fv F v) X.det⁻¹ = 1
    rw [coe_det_matS, ← map_mul, mul_inv_cancel₀ hdet, map_one]

end GlobalTheory.CompanionTheory.Gunr

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalMatrixIntegralStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_matrix_integral : PositivityTheory.SiegelWeilFormula.Gunr.LocMat := by
  first | exact @GlobalTheory.CompanionTheory.Gunr.locMat | exact GlobalTheory.CompanionTheory.Gunr.locMat | (intros; apply GlobalTheory.CompanionTheory.Gunr.locMat <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetIntegralUnramifiedStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetIntegralUnramified
open MeasureTheory Set
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.CosetSum

variable {G : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]

def fib (H : AddSubgroup G) (c : G ⧸ H) : Set G := (QuotientAddGroup.mk : G → G ⧸ H) ⁻¹' {c}

theorem fib_mk (H : AddSubgroup G) (g : G) :
    fib H (g : G ⧸ H) = {x | x - g ∈ H} := by
  ext x
  simp only [fib, mem_preimage, mem_singleton_iff]
  exact QuotientAddGroup.eq_iff_sub_mem

theorem fib_meas (H : AddSubgroup G) (hm : ∀ g : G, MeasurableSet {x | x - g ∈ H})
    (c : G ⧸ H) : MeasurableSet (fib H c) := by
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective c
  rw [fib_mk]
  exact hm g

theorem fib_measure (ν : Measure G) [ν.IsAddLeftInvariant] (H : AddSubgroup G)
    (h1 : ν (H : Set G) = 1) (c : G ⧸ H) : ν (fib H c) = 1 := by
  obtain ⟨g, rfl⟩ := QuotientAddGroup.mk_surjective c
  have hpre : fib H (g : G ⧸ H) = (fun x => -g + x) ⁻¹' (H : Set G) := by
    rw [fib_mk]
    ext x
    simp [neg_add_eq_sub]
  rw [hpre, measure_preimage_add, h1]

theorem fib_disj (H : AddSubgroup G) : Pairwise (Function.onFun Disjoint (fib H)) :=
  fun _ _ hcd => (Set.disjoint_singleton.mpr hcd).preimage _

theorem fib_union (H : AddSubgroup G) : ⋃ c, fib H c = univ :=
  eq_univ_of_forall fun x => mem_iUnion.mpr ⟨(x : G ⧸ H), rfl⟩

theorem integrable_iff_and_integral_eq (G : Type) [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd G] (ν : Measure G) [ν.IsAddLeftInvariant] (H : AddSubgroup G)
    (hm : ∀ g : G, MeasurableSet {x | x - g ∈ H}) (h1 : ν (H : Set G) = 1)
    (hc : Countable (G ⧸ H)) (f : G → ℂ) (fbar : G ⧸ H → ℂ)
    (hf : ∀ g : G, f g = fbar (g : G ⧸ H)) :
    (Integrable f ν ↔ Summable fun c => ‖fbar c‖) ∧
      ((Summable fun c => ‖fbar c‖) → ∫ g, f g ∂ν = ∑' c, fbar c) := by
  have hmeas : Measurable f := by
    intro s _
    have hs : f ⁻¹' s = ⋃ c ∈ fbar ⁻¹' s, fib H c := by
      ext x
      simp [fib, hf]
    rw [hs]
    exact MeasurableSet.biUnion (to_countable _) fun c _ => fib_meas H hm c
  have hlin : ∫⁻ g, ‖f g‖ₑ ∂ν = ∑' c, ‖fbar c‖ₑ := by
    rw [← setLIntegral_univ, ← fib_union H, lintegral_iUnion (fib_meas H hm) (fib_disj H)]
    refine tsum_congr fun c => ?_
    rw [setLIntegral_congr_fun (fib_meas H hm c) (g := fun _ => ‖fbar c‖ₑ), setLIntegral_const,
      fib_measure ν H h1 c, mul_one]
    intro x hx
    simp only [fib, mem_preimage, mem_singleton_iff] at hx
    simp [hf, hx]
  have hiff : (Integrable f ν ↔ Summable fun c => ‖fbar c‖) := by
    rw [Integrable, hasFiniteIntegral_iff_enorm, hlin]
    simp only [hmeas.aestronglyMeasurable, true_and]
    rw [lt_top_iff_ne_top]
    simp only [← ofReal_norm]
    constructor
    · intro h
      have h' : (∑' c, ((‖fbar c‖₊ : ℝ≥0) : ℝ≥0∞)) ≠ ⊤ := by
        simpa [ofReal_norm, enorm_eq_nnnorm] using h
      have := ENNReal.tsum_coe_ne_top_iff_summable.mp h'
      exact NNReal.summable_coe.mpr this |>.congr fun c => by simp
    · intro h
      have h' : Summable fun c => ‖fbar c‖₊ := NNReal.summable_coe.mp (by simpa using h)
      simpa [ofReal_norm, enorm_eq_nnnorm] using ENNReal.tsum_coe_ne_top_iff_summable.mpr h'
  refine ⟨hiff, fun hs => ?_⟩
  have hint : Integrable f ν := hiff.mpr hs
  rw [← setIntegral_univ, ← fib_union H, integral_iUnion (fib_meas H hm) (fib_disj H) hint.integrableOn]
  refine tsum_congr fun c => ?_
  rw [setIntegral_congr_fun (fib_meas H hm c) (g := fun _ => fbar c), setIntegral_const]
  · simp [Measure.real, fib_measure ν H h1 c]
  · intro x hx
    simp only [fib, mem_preimage, mem_singleton_iff] at hx
    simp [hf, hx]

end GlobalTheory.CompanionTheory.CosetSum
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_integral_unramified : PositivityTheory.SiegelWeilFormula.Gunr.CosetInt := by
  first | exact @GlobalTheory.CompanionTheory.CosetSum.integrable_iff_and_integral_eq | exact GlobalTheory.CompanionTheory.CosetSum.integrable_iff_and_integral_eq | (intros; apply GlobalTheory.CompanionTheory.CosetSum.integrable_iff_and_integral_eq <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIntegralFormulaHyperbolic
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIntegralFormulaHyperbolic
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStage

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

theorem lintegral_tuple_vH {T : Type} [MeasurableSpace T] (m : Measure T) [SigmaFinite m] (n M : ℕ)
    (ψ : (Fin n → Fin (M + 2) → T) → ℝ≥0∞) (hψ : Measurable ψ) :
    ∫⁻ Y, ψ Y ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin (M + 2) => m) =
      ∫⁻ a : Fin 1 → Fin n → T, ∫⁻ s : Fin 1 → Fin n → T, ∫⁻ Y : Fin n → Fin M → T,
        ψ (fun j => vH (a 0 j) (s 0 j) (Y j))
        ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin M => m)
        ∂(Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin n => m)
        ∂(Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin n => m) := by
  have hu : ∀ f : (Fin n → T) → ℝ≥0∞,
      ∫⁻ a : Fin 1 → Fin n → T, f (a 0) ∂(Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin n => m) =
        ∫⁻ c, f c ∂(Measure.pi fun _ : Fin n => m) := fun f =>
    (measurePreserving_funUnique (Measure.pi fun _ : Fin n => m) (Fin 1)).lintegral_comp_emb
      (MeasurableEquiv.measurableEmbedding _) f
  have hc : ∀ c : Fin n → T, Measurable fun X : Fin n → Fin (M + 1) → T =>
      ψ (fun a => Fin.cons (c a) (X a)) := by
    intro c
    refine hψ.comp (measurable_pi_iff.2 fun a => ?_)
    exact (TupFubini.measurable_cons_tail (c a)).comp (measurable_pi_apply a)
  rw [TupFubini.lintegral_tuple_first_coord m n (M + 1) ψ hψ]
  refine Eq.trans ?_ (hu fun c => ∫⁻ s : Fin 1 → Fin n → T, ∫⁻ Y : Fin n → Fin M → T,
    ψ (fun j => vH (c j) (s 0 j) (Y j)) ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin M => m)
    ∂(Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin n => m)).symm
  refine lintegral_congr fun c => ?_
  rw [TupFubini.lintegral_tuple_first_coord m n M _ (hc c)]
  exact (hu fun c' => ∫⁻ Y : Fin n → Fin M → T, ψ (fun j => vH (c j) (c' j) (Y j))
    ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin M => m)).symm

theorem lintegral_chartS_of_unitary (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (hR : IsLocR R)
    (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (hlam : lam.IsAddHaarMeasure)
    (g : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ≥0∞) (hg : Measurable g)
    (hg0 : ∀ X, ¬ IsUnit (X 0 0) → g X = 0)
    (hc : ∀ x : Fin (M + 2) → R ⊗[F] E, IsUnit (x 0) → ∃ c : HA R σ (hypOne J), ∀ v,
      ((HA.mat R σ (hypOne J) c : GL (Fin (M + 2)) (R ⊗[F] E)) :
        Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E)).mulVec v = cvec R σ J x v) :
    ∫⁻ X, g X ∂(coordW R b lam (n + 1) (M + 2)) =
      ∫⁻ x, ∫⁻ a, ∫⁻ s, ∫⁻ Y, g (chartS R σ J x a s Y) ∂(coordW R b lam n M) ∂(coordW R b lam 1 n)
        ∂(coordW R b lam 1 n) ∂(coordW R b lam 1 (M + 2)) := by
  obtain ⟨i₁, i₂, i₃, i₄, -⟩ := id hR
  obtain ⟨k₁, k₂, k₃, k₄, -, -, -, hBorel, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  obtain ⟨hK, hW, -⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM R d b lam hlam
  have hJ' := (GlobalTheory.T.hyperbolic_sum_nondegenerate_frame F E σ hCM M J hJ).1
  have : SigmaFinite (coordK R b lam) := inferInstance
  have hBK : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hBt := hBorel 1 n
  have hHaar := hW 1 n
  have step : ∫⁻ X, g X ∂(coordW R b lam (n + 1) (M + 2)) =
      ∫⁻ x : Fin 1 → Fin (M + 2) → R ⊗[F] E, ∫⁻ Y : Fin n → Fin (M + 2) → R ⊗[F] E, g (Fin.cons (x 0) Y)
        ∂(coordW R b lam n (M + 2)) ∂(coordW R b lam 1 (M + 2)) :=
    TupFubini.lintegral_tuple_succ (coordK R b lam) n (M + 2) g hg
  rw [step]
  refine lintegral_congr fun x => ?_
  by_cases hu : IsUnit (x 0 0)
  · obtain ⟨c, hcv⟩ := hc (x 0) hu
    have hact : Measurable (actW R σ (hypOne J) c :
        (Fin n → Fin (M + 2) → R ⊗[F] E) → Fin n → Fin (M + 2) → R ⊗[F] E) := by
      have := hBorel n (M + 2)
      have hcont := ((GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM (M + 2) (hypOne J) hJ' R).2.2.2.2.2 n).1
      exact (hcont.comp (Continuous.prodMk_right c)).measurable
    have hinv := GlobalTheory.T.unitary_action_preserves_haar_local F E σ hCM (M + 2) (hypOne J) hJ' R hR n (coordW R b lam n (M + 2)) (hW n (M + 2)) c
    have hf : Measurable fun Y : Fin n → Fin (M + 2) → R ⊗[F] E => g (Fin.cons (x 0) Y) :=
      hg.comp (TupFubini.measurable_cons_tail (x 0))
    have hψ := hf.comp hact
    calc ∫⁻ Y : Fin n → Fin (M + 2) → R ⊗[F] E, g (Fin.cons (x 0) Y) ∂(coordW R b lam n (M + 2))
        = ∫⁻ Y, g (Fin.cons (x 0) Y) ∂((coordW R b lam n (M + 2)).map (actW R σ (hypOne J) c)) := by
          rw [hinv]
      _ = ∫⁻ Y, g (Fin.cons (x 0) (actW R σ (hypOne J) c Y)) ∂(coordW R b lam n (M + 2)) :=
          lintegral_map hf hact
      _ = ∫⁻ a, ∫⁻ s, ∫⁻ Y, g (Fin.cons (x 0) (actW R σ (hypOne J) c
            (fun j => vH (a 0 j) (s 0 j) (Y j)))) ∂(coordW R b lam n M) ∂(coordW R b lam 1 n)
            ∂(coordW R b lam 1 n) :=
          lintegral_tuple_vH (coordK R b lam) n M _ hψ
      _ = _ := by
          refine lintegral_congr fun a => ?_
          have ht := lintegral_add_right_eq_self (μ := coordW R b lam 1 n)
            (fun s : Fin 1 → Fin n → R ⊗[F] E => ∫⁻ Y, g (Fin.cons (x 0) (actW R σ (hypOne J) c
              (fun j => vH (a 0 j) (s 0 j) (Y j)))) ∂(coordW R b lam n M))
            (fun _ j => - (tHalf R σ J (x 0) * a 0 j))
          rw [← ht]
          refine lintegral_congr fun s => lintegral_congr fun Y => ?_
          congr 1
          unfold chartS
          congr 1
          funext j
          simpa [actW, actTup, sub_eq_add_neg] using hcv (vH (a 0 j) (s 0 j - tHalf R σ J (x 0) * a 0 j) (Y j))
  · have h0 : ∀ Y : Fin n → Fin (M + 2) → R ⊗[F] E, g (Fin.cons (x 0) Y) = 0 := fun Y => hg0 _ (by simpa using hu)
    have h1 : ∀ a s Y, g (chartS R σ J x a s Y) = 0 := fun a s Y => hg0 _ (by simpa [chartS] using hu)
    simp [h0, h1]

theorem chartS_lintegral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ g : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ≥0∞, Measurable g → (∀ X, ¬ IsUnit (X 0 0) → g X = 0) → ∫⁻ X, g X ∂(coordW R b lam (n + 1) (M + 2)) = ∫⁻ x, ∫⁻ a, ∫⁻ s, ∫⁻ Y, g (chartS R σ J x a s Y) ∂(coordW R b lam n M) ∂(coordW R b lam 1 n) ∂(coordW R b lam 1 n) ∂(coordW R b lam 1 (M + 2)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ R _ _ _ _ _ hR n d b lam hlam g hg hg0
  exact lintegral_chartS_of_unitary F E σ hCM M J hJ R hR n d b lam hlam g hg hg0
    fun x hx => GlobalTheory.CompanionTheory.WeilSiegel.HypUnit.cvec_unitary F E σ hCM M J hJ R x hx

end GlobalTheory.CompanionTheory.WeilSiegel.HypStage
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIntegralFormulaHyperbolicStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_integral_formula_hyperbolic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ g : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ≥0∞, Measurable g → (∀ X, ¬ IsUnit (X 0 0) → g X = 0) → ∫⁻ X, g X ∂(coordW R b lam (n + 1) (M + 2)) = ∫⁻ x, ∫⁻ a, ∫⁻ s, ∫⁻ Y, g (chartS R σ J x a s Y) ∂(coordW R b lam n M) ∂(coordW R b lam 1 n) ∂(coordW R b lam 1 n) ∂(coordW R b lam 1 (M + 2)) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStage.chartS_lintegral | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStage.chartS_lintegral | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStage.chartS_lintegral <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralHermitianInvariance
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralHermitianInvariance
noncomputable section

namespace GlobalTheory.CompanionTheory.GunrInv

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen
  PositivityTheory.SiegelWeilFormula.Gunr Filter
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem trPair_add_left (R : Type) [CommRing R] [Algebra F R] {n : ℕ}
    (A B C : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    trPair (F := F) (E := E) R (A + B) C = trPair (F := F) (E := E) R A C + trPair (F := F) (E := E) R B C := by
  simp only [trPair, Matrix.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _), mul_add]

theorem trPair_add_right (R : Type) [CommRing R] [Algebra F R] {n : ℕ}
    (A B C : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    trPair (F := F) (E := E) R A (B + C) = trPair (F := F) (E := E) R A B + trPair (F := F) (E := E) R A C := by
  simp only [trPair, Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]

theorem multiplicity_add_lattice_preserving {R : Type} [CommRing R] [MeasurableSpace R] {n : ℕ} (lam : Measure (Fin n → R))
    (L : AddSubgroup (Fin n → R)) (b h : Matrix (Fin n) (Fin n) R) (hh : ∀ y ∈ L, h.mulVec y ∈ L) :
    nu2 lam L L (b + h) = nu2 lam L L b := by
  have e : {x | ∃ y ∈ L, ∃ y' ∈ L, x = y + (b + h).mulVec y'} = {x | ∃ y ∈ L, ∃ y' ∈ L, x = y + b.mulVec y'} := by
    ext x
    constructor
    · rintro ⟨y, hy, y', hy', rfl⟩
      refine ⟨y + h.mulVec y', L.add_mem hy (hh y' hy'), y', hy', ?_⟩
      rw [Matrix.add_mulVec]
      abel
    · rintro ⟨y, hy, y', hy', rfl⟩
      refine ⟨y - h.mulVec y', L.sub_mem hy (hh y' hy'), y', hy', ?_⟩
      rw [Matrix.add_mulVec]
      abel
  simp only [nu2, e]

section Good

variable {σ : E →ₐ[F] E} {M n d : ℕ} {J : Matrix (Fin M) (Fin M) E} {T : Matrix (Fin n) (Fin n) E}
  {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ψv : Fv F v → ℂ} {S : Subring (Fv F v ⊗[F] E)}
  {σS : S →+* S} {ϖ : Fv F v} {ε : ℤ}

theorem trPair_mem (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) {A B : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)}
    (hA : ∀ i j, A i j ∈ S) (hB : ∀ i j, B i j ∈ S) :
    trPair (F := F) (E := E) (Fv F v) A B ∈ v.adicCompletionIntegers F := by
  have e : algebraMap F (Fv F v) (1 / 2) = (2 : Fv F v)⁻¹ := by
    rw [one_div, map_inv₀, map_ofNat]
  rw [trPair, e]
  exact mul_mem hG.half_mem (hG.trace_mem
    (sum_mem fun a _ => sum_mem fun c _ => mul_mem (hA a c) (hB c a)))

theorem gramR_mem (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) {Y : Fin n → Fin M → Fv F v ⊗[F] E}
    (hY : Y ∈ latV (M := M) (n := n) bs v) (a c : Fin n) : gramR (Fv F v) σ J Y a c ∈ S := by
  have hmem : ∀ a i, Y a i ∈ S := fun a i => by
    have : Y a i ∈ (S : Set (Fv F v ⊗[F] E)) := by
      rw [hG.carrier]
      exact fun k => hY a i k
    exact this
  have hsig : ∀ x ∈ S, sigR (Fv F v) σ x ∈ S := fun x hx => by
    have := (σS ⟨x, hx⟩).2
    rwa [hG.sig ⟨x, hx⟩] at this
  show ∑ i, ∑ j, sigR (Fv F v) σ (Y a i) * JR (Fv F v) J i j * Y c j ∈ S
  exact sum_mem fun i _ => sum_mem fun j _ =>
    mul_mem (mul_mem (hsig _ (hmem a i)) (hG.J_int i j)) (hmem c j)

theorem jtR_add (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (b h : HermR (Fv F v) σ n) (hh : h ∈ H0 S σ n) :
    jtR (Fv F v) σ J ψv μv ((latV bs v).indicator 1) (b + h) = jtR (Fv F v) σ J ψv μv ((latV bs v).indicator 1) b := by
  unfold jtR
  congr 1
  funext Y
  by_cases hY : Y ∈ latV (M := M) (n := n) bs v
  · have h1 : ψv (trPair (F := F) (E := E) (Fv F v) (h : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (gramR (Fv F v) σ J Y)) = 1 :=
      hG.psi_of_mem (trPair_mem hG hh (gramR_mem hG hY))
    rw [AddSubgroup.coe_add, trPair_add_left, hG.psi_add, h1, mul_one]
  · simp [Set.indicator_of_notMem hY]

theorem character_add_integral_hermitian (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (hT : ∀ a b, σ (T b a) = T a b)
    (b h : HermR (Fv F v) σ n) (hh : h ∈ H0 S σ n) :
    ψv (-trPair (Fv F v) (hermOf (Fv F v) σ T hT).1 (b + h).1) = ψv (-trPair (Fv F v) (hermOf (Fv F v) σ T hT).1 b.1) := by
  have h1 : trPair (F := F) (E := E) (Fv F v) (hermOf (Fv F v) σ T hT).1 h.1 ∈ v.adicCompletionIntegers F :=
    trPair_mem hG (fun i j => hG.T_int i j) hh
  have h2 : ψv (-trPair (F := F) (E := E) (Fv F v) (hermOf (Fv F v) σ T hT).1 h.1) = 1 :=
    hG.psi_of_mem (neg_mem h1)
  rw [AddSubgroup.coe_add, trPair_add_right, neg_add, hG.psi_add, h2, mul_one]

theorem mulVec_mem_L (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (L : AddSubgroup (Fin n → Fv F v ⊗[F] E))
    (hL : (L : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v) (h : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    (hh : ∀ i j, h i j ∈ S) (y : Fin n → Fv F v ⊗[F] E) (hy : y ∈ L) : h.mulVec y ∈ L := by
  have key : ∀ w : Fin n → Fv F v ⊗[F] E, w ∈ L ↔ ∀ a, w a ∈ S := fun w => by
    have e1 : w ∈ L ↔ w ∈ (latO bs v : Set (Fin n → Fv F v ⊗[F] E)) := by
      rw [← hL]; rfl
    have e2 : ∀ x, x ∈ S ↔ x ∈ Rv bs v := fun x => by
      rw [← hG.carrier]; rfl
    rw [e1]
    simp only [e2]
    rfl
  rw [key] at hy ⊢
  intro a
  show ∑ j, h a j * y j ∈ S
  exact sum_mem fun j _ => mul_mem (hh a j) (hy j)

end Good

theorem integrand_invariant_integral_hermitian : HermitianLatticeInvariance := by
  intro F E _ _ _ _ _ σ M n d J T bs v ψv S σS ϖ ε hG hT μv lam L hL z b h hh
  unfold whI
  rw [jtR_add hG μv b h hh, character_add_integral_hermitian hG hT b h hh]
  have e : nu2 lam L L (b + h).1 = nu2 lam L L b.1 := by
    rw [AddSubgroup.coe_add]
    exact multiplicity_add_lattice_preserving lam L _ _ (mulVec_mem_L hG L hL _ hh)
  rw [e]

end GlobalTheory.CompanionTheory.GunrInv

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralHermitianInvarianceStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_hermitian_invariance : PositivityTheory.SiegelWeilFormula.Gunr.HermitianLatticeInvariance := by
  first | exact @GlobalTheory.CompanionTheory.GunrInv.integrand_invariant_integral_hermitian | exact GlobalTheory.CompanionTheory.GunrInv.integrand_invariant_integral_hermitian | (intros; apply GlobalTheory.CompanionTheory.GunrInv.integrand_invariant_integral_hermitian <;> assumption)
end
end
