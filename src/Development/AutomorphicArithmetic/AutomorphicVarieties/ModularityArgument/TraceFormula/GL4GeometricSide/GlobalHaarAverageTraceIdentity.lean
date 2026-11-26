module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.AbsGlob
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.AvgFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.OfLinearEquiv
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveFinal
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.MultGOfMultFor
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.MultiplicityFormulaHolds
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.LieStab
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.LocAct
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.PartSum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.LowType
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.MultiFac
public import Development.DiscreteGroups.PiInvariants.CasimirInfinity.CasInfOfIm
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.LogAbsEqLogIdeleNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.ContOfRightInv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.EqZeroOfGrid
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.RlHecke
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.SumRefine
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.RlSimple

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignOne
noncomputable section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

namespace GlobalTheory.CompanionTheory.SignLine

theorem signOne : PositivityTheory.RgBcC.RealD.SignOne := by
  intro V _ _ S A hA hS h1
  haveI : FiniteDimensional ℂ S := Module.finite_of_finrank_pos (by rw [h1]; exact one_pos)
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp h1
  set B : S →ₗ[ℂ] S := A.restrict hS with hBdef
  obtain ⟨c, hc⟩ := hv (B v)
  have hBw : ∀ w : S, B w = c • w := by
    intro w
    obtain ⟨d, rfl⟩ := hv w
    rw [map_smul, ← hc, smul_comm]
  have hcc : c * c = 1 := by
    have h2 : B (B v) = v := by
      apply Subtype.ext
      show A (A (v : V)) = v
      have := congrArg (fun f : V →ₗ[ℂ] V => f v) hA
      simpa using this
    rw [hBw (B v), hBw v, smul_smul] at h2
    have h3 : (c * c - 1) • v = 0 := by rw [sub_smul, h2, one_smul, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv0
  refine ⟨c, mul_self_eq_one_iff.mp hcc, ?_⟩
  have hB : B = c • LinearMap.id := LinearMap.ext fun w => by rw [hBw]; rfl
  rw [trOn, dite_eq_left hS]
  change LinearMap.trace ℂ S B = c
  rw [hB, map_smul, LinearMap.trace_id]
  simp [h1]

end GlobalTheory.CompanionTheory.SignLine
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.CoreG
open PositivityTheory.RgBcC.RealD

theorem UpperTheory.V.Z.GSp4Splitting.coreG : CoreG := coreG_of countG_holds (multG_of_multFor multiplicity_formula_holds) GlobalTheory.CompanionTheory.SignLine.signOne
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.ExistsClass
open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.GKCoh MeasureTheory GlobalTheory.CompanionTheory.TwY.ThInv
open PositivityTheory.Rg.BcB (thetaA)

private theorem exists_class (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : CuspSub E n)
    (hπ : GlobalTheory.DiscSpec.IsNormalised π) :
    ∃ B : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ, (∀ φ ψ, starRingEnd ℂ (B φ ψ) = B ψ φ) ∧ (∀ φ, 0 ≤ (B φ φ).re) ∧
      (∀ φ, φ ≠ 0 → 0 < (B φ φ).re) ∧ (∀ (X : Lie E n) φ ψ, B (lieOp π X φ) ψ + B φ (lieOp π X ψ) = 0) ∧
      ∀ (g : GA E n) (φ ψ φ' ψ' : π.V), (∀ x, φ'.1.1 x = φ.1.1 (x * g)) → (∀ x, ψ'.1.1 x = ψ.1.1 (x * g)) →
        B φ' ψ' = B φ ψ := by
  obtain ⟨μ, hμ, hμ'⟩ := GlobalTheory.CompanionTheory.AdelicHaar.exists_haar_rightInvariant E n
  have hl := GlobalTheory.CompanionTheory.CuspForms.memL2_and_bounded_of_normalised GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL E n μ π hπ
  have hm : ∀ φ ∈ π.V, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E n) μ φ.1 := fun φ hφ => (hl φ hφ).1
  have inj : Function.Injective (toL2ₗ μ π.V hm) :=
    toL2ₗ_injective hm fun ψ hψ => ContAut.continuous_of_isOpen_stab E n ψ (π.cusp ψ hψ).1.level
  have sq : ∀ φ : π.V, (inner ℂ (toL2ₗ μ π.V hm φ) (toL2ₗ μ π.V hm φ)).re = ‖toL2ₗ μ π.V hm φ‖ ^ 2 := fun φ =>
    inner_self_eq_norm_sq (𝕜 := ℂ) _
  refine ⟨((innerₛₗ ℂ).comp (toL2ₗ μ π.V hm)).compl₂ (toL2ₗ μ π.V hm), fun φ ψ =>
    inner_conj_symm (𝕜 := ℂ) (toL2ₗ μ π.V hm ψ) (toL2ₗ μ π.V hm φ), fun φ => ?_,
    fun φ hφ => ?_, fun X φ ψ => ?_, fun g φ ψ φ' ψ' h h' => ?_⟩
  · exact (sq φ).symm ▸ sq_nonneg _
  · exact (sq φ).symm ▸ pow_pos (norm_pos_iff.2 fun e => hφ (inj (e.trans (map_zero _).symm))) 2
  · have e := GlobalTheory.CompanionTheory.PeterssonSkew.lie_skew_adjoint E n μ π hm (fun φ hφ => (hl φ hφ).2) X ψ φ
    exact (add_comm _ _).trans (add_eq_zero_iff_eq_neg.2 e)
  · change inner ℂ (hm _ φ'.2).toL2 (hm _ ψ'.2).toL2 = inner ℂ (hm _ φ.2).toL2 (hm _ ψ.2).toL2
    rw [GlobalTheory.AutomorphicL2Unitary.MemL2Quotient.inner_toL2_eq_theta_pairing, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient.inner_toL2_eq_theta_pairing, funext h, funext h']
    exact GlobalTheory.CompanionTheory.PeterssonSkew.pet_mul_right μ (hm _ ψ.2) (hm _ φ.2) g

theorem UpperTheory.V.Z.GSp4Splitting.petEx :
    PetEx := by
  intro E _ _ _ n _ π hθ
  obtain ⟨B, hc, h0, hp, hL, hg⟩ := exists_class E n π hθ.1
  have hv := thV_apply π hθ
  set T := thV π hθ
  have hTL : ∀ (X : Lie E n) (φ : π.V), T (lieOp π X φ) = -lieOp π (adjH X) (T φ) := fun X φ => by
    refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    have e : φ.1.1 = fun y => (T φ).1.1 (thetaA E n y) := funext fun y => by
      rw [hv, GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol]
    have e2 := lieD_theta X (T φ).1.2 (thetaA E n x)
    rw [← e, GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol] at e2
    exact (hv _ x).trans e2
  have ev : ∀ φ ψ, (B + (B.comp T).compl₂ T) φ ψ = B φ ψ + B (T φ) (T ψ) := fun _ _ => rfl
  simp only [IsPet]
  refine ⟨B + (B.comp T).compl₂ T, fun φ ψ => ?_, fun φ hφ => ?_, fun X φ ψ => ?_, fun g φ ψ φ' ψ' h h' => ?_,
    fun φ ψ φ' ψ' h h' => ?_⟩
  · rw [ev, ev, map_add (f := _), hc, hc]
  · rw [ev, Complex.add_re]
    exact add_pos_of_pos_of_nonneg (hp φ hφ) (h0 _)
  · have e1 := hL X φ ψ
    have e2 := hL (adjH X) (T φ) (T ψ)
    rw [ev, ev, hTL, hTL, map_neg, map_neg, LinearMap.neg_apply]
    linear_combination e1 - e2
  · rw [ev, ev, hg g φ ψ φ' ψ' h h', hg (thetaA E n g) (T φ) (T ψ) (T φ') (T ψ')] <;> intro x
    · rw [hv, hv, h, map_mul, GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol]
    · rw [hv, hv, h', map_mul, GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol]
  · have k : ∀ a a' : π.V, (∀ x, a'.1.1 x = a.1.1 (thetaA E n x)) → T a = a' ∧ T a' = a := fun a a' e =>
      ⟨Subtype.ext (Subtype.ext (funext fun x => (hv a x).trans (e x).symm)),
        Subtype.ext (Subtype.ext (funext fun x => by rw [hv, e, GlobalTheory.CompanionTheory.OnlyStab.thetaA_invol]))⟩
    rw [ev, ev, (k _ _ h).1, (k _ _ h).2, (k _ _ h').1, (k _ _ h').2, add_comm]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.IntegrableCoef
noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace UpperTheory.V.Z.GSp4Splitting

variable {n : ℕ}

private theorem cont_tr (E : PositivityTheory.RgBcC.KMod n) (T : E.V →L[ℂ] E.V) :
    Continuous fun κ : Un n =>
      LinearMap.trace ℂ E.V ((E.ρ κ * T : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) := by
  let L : (E.V →L[ℂ] E.V) →ₗ[ℂ] ℂ :=
    (LinearMap.trace ℂ E.V).comp (ContinuousLinearMap.coeLM ℂ)
  have hL : Continuous L := L.continuous_of_finiteDimensional
  exact hL.comp (E.cont.mul continuous_const)

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

private theorem integrable_coef [CompactSpace (Un n)] [MeasurableSpace (Un n)] [BorelSpace (Un n)]
    (ν : Measure (Un n)) [IsFiniteMeasure ν] (σ : Un n →* (V →ₗ[ℂ] V)) (hσ : IsK σ)
    {f : Un n → ℂ} (hf : Continuous f) (v w : V) :
    Integrable (fun κ => f κ * ⟪w, σ κ v⟫_ℂ) ν :=
  (hf.mul (hσ.cont v w)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem exists_avg [CompactSpace (Un n)] [MeasurableSpace (Un n)] [BorelSpace (Un n)]
    (ν : Measure (Un n)) [IsFiniteMeasure ν] (σ : Un n →* (V →ₗ[ℂ] V)) (hσ : IsK σ)
    {f : Un n → ℂ} (hf : Continuous f) (v : V) :
    ∃ p : V, ∀ w : V, ⟪w, p⟫_ℂ = ∫ κ, f κ * ⟪w, σ κ v⟫_ℂ ∂ν := by
  obtain ⟨S, hfd, hv, hS⟩ := hσ.fin v
  have hmem : ∀ κ, σ κ v ∈ S := fun κ => hS κ v hv
  let b := stdOrthonormalBasis ℂ S
  have hexp : ∀ κ, σ κ v = ∑ i, ⟪((b i : S) : V), σ κ v⟫_ℂ • ((b i : S) : V) := by
    intro κ
    have h := b.sum_repr' (⟨σ κ v, hmem κ⟩ : S)
    have h' := congrArg (Subtype.val) h
    simpa [Submodule.coe_sum, Submodule.coe_inner] using h'.symm
  refine ⟨∑ i, (∫ κ, f κ * ⟪((b i : S) : V), σ κ v⟫_ℂ ∂ν) • ((b i : S) : V), fun w => ?_⟩
  have hint : ∀ κ, f κ * ⟪w, σ κ v⟫_ℂ =
      ∑ i, (f κ * ⟪((b i : S) : V), σ κ v⟫_ℂ) * ⟪w, ((b i : S) : V)⟫_ℂ := by
    intro κ
    conv_lhs => rw [hexp κ]
    rw [inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_right]
    ring
  simp_rw [hint]
  rw [integral_finsetSum _ fun i _ => (integrable_coef ν σ hσ hf v _).mul_const _, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, integral_mul_const]

theorem avgEx : AvgEx := by
  intro n _ _ ν _ V _ _ σ hσ E T
  haveI : CompactSpace (Un n) := GlobalTheory.compactSpace_unitaryGroup (Fin n) ℂ
  have hf := cont_tr E T
  choose p hp using fun v : V => exists_avg ν σ hσ hf v
  have hI := fun v w : V => integrable_coef ν σ hσ hf v w
  refine ⟨{ toFun := p, map_add' := ?_, map_smul' := ?_ }, fun v w => hp v w⟩
  · intro x y
    refine ext_inner_left ℂ fun w => ?_
    rw [inner_add_right, hp, hp, hp, ← integral_add (hI x w) (hI y w)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
    simp only [map_add (f := _), inner_add_right, mul_add]
  · intro c x
    refine ext_inner_left ℂ fun w => ?_
    rw [RingHom.id_apply, inner_smul_right, hp, hp, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
    simp only [map_smul, inner_smul_right]
    ring

end UpperTheory.V.Z.GSp4Splitting
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.OpForm
noncomputable section

open NumberField MeasureTheory Measure
open GlobalTheory.CuspRep
open PositivityTheory.RgTw (G)

namespace UpperTheory.V.Z.GSp4Splitting

section Iter

variable {X Γ U ι : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [Monoid Γ] [TopologicalSpace Γ] [ContinuousMul Γ] [AddCommGroup U] [Module ℂ U]

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
private theorem prod_cs {κ : Type} [Fintype κ] (e : κ → X → ℂ) (he : ∀ v, Continuous (e v) ∧ HasCompactSupport (e v)) :
    Continuous (fun y : κ → X => ∏ v, e v (y v)) ∧ HasCompactSupport (fun y : κ → X => ∏ v, e v (y v)) := by
  refine ⟨continuous_finsetProd _ fun v _ => (he v).1.comp (continuous_apply v), ?_⟩
  refine HasCompactSupport.intro (isCompact_univ_pi fun v => (he v).2.isCompact) fun y hy => ?_
  obtain ⟨v, hv⟩ := not_forall.1 (mt Set.mem_univ_pi.2 hy)
  exact Finset.prod_eq_zero (Finset.mem_univ v) (image_eq_zero_of_notMem_tsupport hv)

private theorem iter_fin (μ : Measure X) [SigmaFinite μ] [IsFiniteMeasureOnCompacts μ]
    (e : ι → X → ℂ) (he : ∀ v, Continuous (e v) ∧ HasCompactSupport (e v)) (j : ι → X → Γ) (hj : ∀ v, Continuous (j v))
    (Φ : U → Γ → ℂ) (hΦ : ∀ u, Continuous (Φ u)) (val : ι → ℂ) (P : ι → Module.End ℂ U)
    (hloc : ∀ v u g, ∫ t, e v t * Φ u (g * j v t) ∂μ = val v * Φ (P v u) g) (m : ℕ) :
    ∀ (s : Fin m → ι) (u : U) (g : Γ),
      ∫ y : Fin m → X, (∏ i, e (s i) (y i)) * Φ u (g * (List.ofFn fun i => j (s i) (y i)).prod) ∂(Measure.pi fun _ => μ) =
        (∏ i, val (s i)) * Φ ((List.ofFn fun i => P (s i)).prod u) g := by
  induction m with
  | zero =>
    intro s u g
    simp [Measure.pi_of_empty (fun _ : Fin 0 => μ)]
  | succ m ih =>
    intro s u g
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) 0
    have hl : Continuous fun y : Fin (m + 1) → X => (List.ofFn fun i => j (s i) (y i)).prod := by
      simp only [List.ofFn_eq_map]
      exact continuous_list_prod _ fun i _ => (hj _).comp (continuous_apply i)
    have hF : Integrable (fun y : Fin (m + 1) → X => (∏ i, e (s i) (y i)) *
        Φ u (g * (List.ofFn fun i => j (s i) (y i)).prod)) (Measure.pi fun _ => μ) :=
      ((prod_cs (fun i => e (s i)) fun i => he _).1.mul ((hΦ u).comp (continuous_const.mul hl))).integrable_of_hasCompactSupport
        (prod_cs (fun i => e (s i)) fun i => he _).2.mul_right
    rw [← (hmp.symm _).integral_comp']
    refine (integral_prod _ (((hmp.symm _).integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hF)).trans ?_
    have hin : ∀ t : X, ∫ z : Fin m → X, (fun y : Fin (m + 1) → X => (∏ i, e (s i) (y i)) *
        Φ u (g * (List.ofFn fun i => j (s i) (y i)).prod)) ((MeasurableEquiv.piFinSuccAbove (fun _ => X) 0).symm (t, z))
          ∂(Measure.pi fun _ => μ) = (∏ i : Fin m, val (s i.succ)) *
            (e (s 0) t * Φ ((List.ofFn fun i : Fin m => P (s i.succ)).prod u) (g * j (s 0) t)) := by
      intro t
      have e1 : ∀ z : Fin m → X, (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => X) 0).symm (t, z) = Fin.cons t z :=
        fun z => Fin.insertNth_zero' t z
      simp only [e1, Fin.prod_univ_succ, List.ofFn_succ, List.prod_cons, Fin.cons_zero, Fin.cons_succ]
      simp only [← mul_assoc g, mul_assoc (e (s 0) t)]
      rw [integral_const_mul, ih (fun i => s i.succ) u (g * j (s 0) t)]
      ring
    refine (integral_congr_ae (Filter.Eventually.of_forall hin)).trans ?_
    rw [integral_const_mul, hloc, Fin.prod_univ_succ, List.ofFn_succ, List.prod_cons, Module.End.mul_apply]
    ring

private theorem iter_list [Fintype ι] (μ : Measure X) [SigmaFinite μ] [IsFiniteMeasureOnCompacts μ]
    (e : ι → X → ℂ) (he : ∀ v, Continuous (e v) ∧ HasCompactSupport (e v)) (j : ι → X → Γ) (hj : ∀ v, Continuous (j v))
    (Φ : U → Γ → ℂ) (hΦ : ∀ u, Continuous (Φ u)) (val : ι → ℂ) (P : ι → Module.End ℂ U)
    (hloc : ∀ v u g, ∫ t, e v t * Φ u (g * j v t) ∂μ = val v * Φ (P v u) g) (l : List ι) (hl : l.Nodup) (hm : ∀ v, v ∈ l)
    (u : U) (g : Γ) :
    ∫ y : ι → X, (∏ v, e v (y v)) * Φ u (g * (l.map fun v => j v (y v)).prod) ∂(Measure.pi fun _ => μ) =
      (∏ v, val v) * Φ ((l.map P).prod u) g := by
  classical
  let σ : Fin l.length ≃ ι := List.Nodup.getEquivOfForallMemList l hl hm
  have hσ : ∀ {β : Type} (f : ι → β), (List.ofFn fun i => f (σ i)) = l.map f := fun f => by
    conv_rhs => rw [← List.ofFn_get l, List.map_ofFn]
    rfl
  have hmp := measurePreserving_piCongrLeft (fun _ : ι => μ) σ
  have key := iter_fin μ e he j hj Φ hΦ val P hloc _ σ u g
  rw [hσ P, Equiv.prod_comp σ val] at key
  rw [← key, ← hmp.integral_comp']
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have e1 : ∀ i, MeasurableEquiv.piCongrLeft (fun _ : ι => X) σ y (σ i) = y i := fun i =>
    MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ι => X) σ y i
  beta_reduce
  rw [← hσ, ← Equiv.prod_comp σ]
  simp only [e1]

end Iter

private theorem prod_single {ι M : Type} [DecidableEq ι] [Monoid M] (y : ι → M) :
    ∀ l : List ι, l.Nodup → ∀ w, (l.map fun v => (Pi.mulSingle v (y v) : ι → M)).prod w = if w ∈ l then y w else 1 := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    intro hl w
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, Pi.mul_apply, ih hl.2]
    by_cases h : w = a
    · subst h
      simp [hl.1]
    · simp [h]

private theorem split_two {X Y K : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y]
    [LocallyCompactSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K] (e : X × Y ≃ₜ* K) (μ : Measure K) [IsHaarMeasure μ]
    (mX : Measure X) [IsHaarMeasure mX] (mY : Measure Y) [IsHaarMeasure mY] :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ f : K → ℂ, Continuous f → HasCompactSupport f →
      ∫ g, f g ∂μ = c * ∫ x, ∫ y, f (e (x, y)) ∂mY ∂mX := by
  let em : X × Y ≃ᵐ K := e.toHomeomorph.toMeasurableEquiv
  haveI : IsHaarMeasure ((mX.prod mY).map e) := ContinuousMulEquiv.isHaarMeasure_map _ e
  haveI : LocallyCompactSpace K := e.symm.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology K := e.symm.toHomeomorph.isEmbedding.secondCountableTopology
  have h := isMulLeftInvariant_eq_smul μ ((mX.prod mY).map e)
  have hpos := haarScalarFactor_pos_of_isHaarMeasure μ ((mX.prod mY).map e)
  generalize haarScalarFactor μ ((mX.prod mY).map e) = c at h hpos
  refine ⟨((c : ℝ) : ℂ), by exact_mod_cast hpos.ne', fun f hf hs => ?_⟩
  rw [h, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  congr 1
  refine (integral_map_equiv em f).trans ?_
  exact integral_prod (fun z => f (e z))
    ((hf.comp e.continuous).integrable_of_hasCompactSupport (hs.comp_homeomorph e.toHomeomorph))

private theorem hecke_cont {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (K : Subgroup Γ)
    (hK : IsOpen (K : Set Γ)) (h : Γ → ℂ) (hh : ∀ k ∈ K, ∀ g, h (g * k) = h g) : Continuous h := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hn : (fun x => g⁻¹ * x) ⁻¹' (K : Set Γ) ∈ nhds g :=
    (hK.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
  refine continuousAt_const.congr (f := fun _ => h g) (Filter.mem_of_superset hn fun x hx => ?_)
  have := hh _ hx g
  simpa using this.symm


open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.CG in
private def split0 (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    (InfinitePlace E → G n) × GL (Fin n) (Af E) ≃ₜ* PositivityTheory.Rg.BcB.E.H E n 0 where
  toFun p := (splitGA n p, 1)
  invFun g := (splitGA n).symm g.1
  left_inv p := by simp
  right_inv g := Prod.ext (by simp) (Units.ext (Matrix.ext fun i => Fin.elim0 i))
  map_mul' p q := by simp
  continuous_toFun := (splitGA n).continuous.prodMk continuous_const
  continuous_invFun := (splitGA n).symm.continuous.comp continuous_fst

end UpperTheory.V.Z.GSp4Splitting

open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH PositivityTheory.Rg.BcB.CG.lc_G PositivityTheory.Rg.BcB.CG.sc_G PositivityTheory.Rg.BcB.CG.lc_GLf
  PositivityTheory.Rg.BcB.CG.sc_GLf PositivityTheory.Rg.BcB.CG.t2_GL_finite_adeles PositivityTheory.Rg.BcB.CG.borelSpaceH in
open PositivityTheory.Rg.BcB.CG in
theorem UpperTheory.V.Z.GSp4Splitting.opForm :
    HeckeMem → RlComm → LocAct → OpForm := by
  intro _ _ hL E _ _ _ n hn π hθ K hKo hKc hKθ _ _ μf _ D lam hch _ _ ν _ hν _ _ μC _ μ _ P hP
  classical
  haveI : IsHaarMeasure (Measure.pi fun _ : InfinitePlace E => μC) := pi.isHaarMeasure _
  obtain ⟨c, hc0, hc⟩ := split_two (split0 E n) μ (Measure.pi fun _ : InfinitePlace E => μC) μf
  refine ⟨c, hc0, fun k val T hk h hh ψ u hu x => ?_⟩
  set e : InfinitePlace E → G n → ℂ := fun w => phiOf (lefE n (lam w)) (lefT n (lam w)) (k w) with he
  have hecs : ∀ w, Continuous (e w) ∧ HasCompactSupport (e w) := fun w =>
    PositivityTheory.Rg.BcB.F.F0.phiOf_cs μC _ _ _ _ _ (hk w)
  have hhc : Continuous h := hecke_cont K hKo h fun k hk g => by simpa using hh.2 1 K.one_mem k hk g
  have hcont : ∀ φ : π.V, Continuous φ.1.1 := fun φ => DiscreteGroups.T1.G.continuous_of_mem π φ.2
  have hphi : ∀ p : (InfinitePlace E → G n) × GL (Fin n) (Af E), phiProd lam k h (split0 E n p) = (∏ w, e w (p.1 w)) * h p.2 := by
    intro p
    have e1 : ∀ w, infAt E n w (split0 E n p).1 = p.1 w := fun w => gInf_splitGA n p w
    have e2 : finOf E n (split0 E n p).1 = p.2 := gFin_splitGA n p
    simp only [phiProd, e1, e2, he]
  have hphi' : phiProd lam k h = (fun p : (InfinitePlace E → G n) × GL (Fin n) (Af E) => (∏ w, e w (p.1 w)) * h p.2) ∘
      (split0 E n).symm.toHomeomorph := by
    funext y
    obtain ⟨p, rfl⟩ := (split0 E n).surjective y
    rw [hphi]
    exact (congrArg (fun p : (InfinitePlace E → G n) × GL (Fin n) (Af E) => (∏ w, e w (p.1 w)) * h p.2)
      ((split0 E n).symm_apply_apply p)).symm
  have hpc : Continuous (phiProd lam k h) := by
    rw [hphi']
    exact (((prod_cs e hecs).1.comp continuous_fst).mul (hhc.comp continuous_snd)).comp (Homeomorph.continuous _)
  have hps : HasCompactSupport (phiProd lam k h) := by
    rw [hphi']
    refine HasCompactSupport.comp_homeomorph ?_ _
    refine HasCompactSupport.intro ((prod_cs e hecs).2.isCompact.prod hh.1.isCompact) fun p hp => ?_
    rcases not_and_or.1 hp with h1 | h1
    · rw [show (∏ w, e w (p.1 w)) = 0 from
        image_eq_zero_of_notMem_tsupport (f := fun y : InfinitePlace E → G n => ∏ v, e v (y v)) h1, zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport h1, mul_zero]
  rw [hc (fun y => phiProd lam k h y * ψ.1.1 (x * y.1))
    (hpc.mul ((hcont ψ).comp (continuous_const.mul continuous_fst))) hps.mul_right, mul_assoc]
  congr 1
  let j : InfinitePlace E → G n → GA E n := fun w t => infP n (Pi.mulSingle w t)
  let l := (Finset.univ : Finset (InfinitePlace E)).toList
  let ih : (InfinitePlace E → G n) →* GA E n := MonoidHom.mk' (infP n) (infinitePart_mul n)
  have hjl : ∀ y : InfinitePlace E → G n, (l.map fun v => j v (y v)).prod = infP n y := by
    intro y
    have e1 : (l.map fun v => (Pi.mulSingle v (y v) : InfinitePlace E → G n)).prod = y := by
      funext w
      rw [prod_single y l (Finset.nodup_toList _), if_pos (Finset.mem_toList.2 (Finset.mem_univ w))]
    conv_rhs => rw [← e1]
    refine Eq.trans ?_ (map_list_prod ih _).symm
    rw [List.map_map]
    rfl
  have hj : ∀ w, Continuous (j w) := fun w => (continuous_infP n).comp (continuous_mulSingle (A := fun _ => G n) w)
  have key := iter_list μC e hecs j hj (fun u => (D.i u).1.1) (fun u => hcont _) (fun w => val w (infOf (lam w))) P
    (fun w u g => by
      have := hL E n hn π hθ K hKo hKc hKθ μf D w (lam w) (hch w) ν hν μC _ _ (P w) (hP w) (k w) (val w) (T w) (hk w) u g
      simp only [along_val] at this
      exact this) l (Finset.nodup_toList _) (fun v => Finset.mem_toList.2 (Finset.mem_univ v)) u x
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  beta_reduce
  rw [hjl, hu, heckeOp, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  beta_reduce
  rw [hphi, mul_assoc, mul_assoc x]
  rfl
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.OnePlace
open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc
open scoped InnerProductSpace

noncomputable section

namespace UpperTheory.V.Z.GSp4Splitting.OnePlaceCyclotomic

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E1 E2 : Fin n → Fin n → Module.End ℂ V}

private theorem mem1 (a b : Fin n) : E1 a b ∈ alg E1 E2 := Algebra.subset_adjoin ⟨a, b, Or.inl rfl⟩

private theorem mem2 (a b : Fin n) : E2 a b ∈ alg E1 E2 := Algebra.subset_adjoin ⟨a, b, Or.inr rfl⟩

private theorem adj (h : IsPair E1 E2) {a : Module.End ℂ V} (ha : a ∈ alg E1 E2) :
    ∃ a' ∈ alg E1 E2, ∀ x y : V, ⟪a x, y⟫_ℂ = ⟪x, a' y⟫_ℂ := by
  have key : ∀ a b (x y : V), ⟪E1 a b x, y⟫_ℂ = ⟪x, E2 b a y⟫_ℂ ∧ ⟪E2 a b x, y⟫_ℂ = ⟪x, E1 b a y⟫_ℂ := by
    intro a b x y
    have h1 := h.unitK a b x y
    have h2 := h.unitP a b x y
    simp only [kF, pF, LinearMap.add_apply, LinearMap.sub_apply, inner_add_left, inner_add_right, inner_sub_left,
      inner_sub_right] at h1 h2
    exact ⟨by linear_combination (h1 + h2) / 2, by linear_combination (h1 - h2) / 2⟩
  induction ha using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨a, b, rfl | rfl⟩ := hz
    · exact ⟨_, mem2 b a, fun x y => (key a b x y).1⟩
    · exact ⟨_, mem1 b a, fun x y => (key a b x y).2⟩
  | algebraMap c =>
    refine ⟨algebraMap ℂ _ (starRingEnd ℂ c), Subalgebra.algebraMap_mem _ _, fun x y => ?_⟩
    simp [Module.algebraMap_end_apply, inner_smul_left, inner_smul_right, mul_comm]
  | add u v _ _ hu hv =>
    obtain ⟨u', hu', hu⟩ := hu
    obtain ⟨v', hv', hv⟩ := hv
    exact ⟨u' + v', add_mem hu' hv', fun x y => by simp [inner_add_left, inner_add_right, hu, hv]⟩
  | mul u v _ _ hu hv =>
    obtain ⟨u', hu', hu⟩ := hu
    obtain ⟨v', hv', hv⟩ := hv
    exact ⟨v' * u', mul_mem hv' hu', fun x y => by simp [hu, hv]⟩

private theorem twist {A : Module.End ℂ V} (hA : A * A = 1) (hE : ∀ a b, A * E1 a b = E2 a b * A)
    {a : Module.End ℂ V} (ha : a ∈ alg E1 E2) : A * a * A ∈ alg E1 E2 := by
  induction ha using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨a, b, rfl | rfl⟩ := hz
    · rw [hE, mul_assoc, hA, mul_one]; exact mem2 a b
    · rw [mul_assoc, ← hE, ← mul_assoc, hA, one_mul]; exact mem1 a b
  | algebraMap c =>
    rw [← Algebra.commutes, mul_assoc, hA, mul_one]; exact Subalgebra.algebraMap_mem _ _
  | add u v _ _ hu hv => rw [mul_add, add_mul]; exact add_mem hu hv
  | mul u v _ _ hu hv =>
    have : A * (u * v) * A = (A * u * A) * (A * v * A) := by
      calc A * (u * v) * A = A * u * (A * A) * v * A := by rw [hA]; simp only [mul_assoc, mul_one, one_mul]
        _ = _ := by simp only [mul_assoc]
    rw [this]; exact mul_mem hu hv


variable (E1 E2) in
private def cyc (x : V) : Submodule ℂ V where
  carrier := {y | ∃ a ∈ alg E1 E2, a x = y}
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, add_mem ha hb, rfl⟩
  zero_mem' := ⟨0, zero_mem _, rfl⟩
  smul_mem' := by
    rintro c _ ⟨a, ha, rfl⟩
    exact ⟨c • a, Subalgebra.smul_mem _ ha c, rfl⟩

private theorem cyc_self (x : V) : x ∈ cyc E1 E2 x := ⟨1, one_mem _, rfl⟩

private theorem cyc_stab {x y : V} {a : Module.End ℂ V} (ha : a ∈ alg E1 E2) (hy : y ∈ cyc E1 E2 x) :
    a y ∈ cyc E1 E2 x := by
  obtain ⟨b, hb, rfl⟩ := hy
  exact ⟨a * b, mul_mem ha hb, rfl⟩

private theorem cyc_K {x : V} (a b : Fin n) : ∀ y ∈ cyc E1 E2 x, kF E1 E2 a b y ∈ cyc E1 E2 x :=
  fun _ hy => cyc_stab (add_mem (mem1 a b) (mem2 a b)) hy

section Res

variable {X : Submodule ℂ V}

private theorem epow_coe {F : Fin n → Fin n → Module.End ℂ V} {F' : Fin n → Fin n → Module.End ℂ X}
    (h : ∀ a b x, (F' a b x : V) = F a b x) (m : ℕ) : ∀ a b x, (epow F' m a b x : V) = epow F m a b x := by
  induction m with
  | zero => intro a b x; simp only [epow]; split_ifs <;> simp
  | succ m ih => intro a b x; simp [epow, LinearMap.sum_apply, h, ih]

private theorem gelA_coe {F : Fin n → Fin n → Module.End ℂ V} {F' : Fin n → Fin n → Module.End ℂ X}
    (h : ∀ a b x, (F' a b x : V) = F a b x) (m : ℕ) (x : X) : (gelA F' m x : V) = gelA F m x := by
  simp [gelA, LinearMap.sum_apply, epow_coe h]

private theorem gl_res {F : Fin n → Fin n → Module.End ℂ V} {F' : Fin n → Fin n → Module.End ℂ X}
    (h : ∀ a b x, (F' a b x : V) = F a b x) (hF : Formalism.REAL.GlRel F) : Formalism.REAL.GlRel F' := by
  intro a b c d
  have := hF a b c d
  ext x
  have h2 := LinearMap.congr_fun this x
  split_ifs at h2 ⊢ <;> simpa [h] using h2

private theorem alg_res {E1' E2' : Fin n → Fin n → Module.End ℂ X}
    (h1 : ∀ a b x, (E1' a b x : V) = E1 a b x) (h2 : ∀ a b x, (E2' a b x : V) = E2 a b x)
    {a : Module.End ℂ V} (ha : a ∈ alg E1 E2) : ∃ a' ∈ alg E1' E2', ∀ x : X, (a' x : V) = a x := by
  induction ha using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨a, b, rfl | rfl⟩ := hz
    · exact ⟨_, mem1 a b, h1 a b⟩
    · exact ⟨_, mem2 a b, h2 a b⟩
  | algebraMap c =>
    exact ⟨algebraMap ℂ _ c, Subalgebra.algebraMap_mem _ _, fun x => by simp [Module.algebraMap_end_apply]⟩
  | add u v _ _ hu hv =>
    obtain ⟨u', hu', hu⟩ := hu
    obtain ⟨v', hv', hv⟩ := hv
    exact ⟨u' + v', add_mem hu' hv', fun x => by simp [hu, hv]⟩
  | mul u v _ _ hu hv =>
    obtain ⟨u', hu', hu⟩ := hu
    obtain ⟨v', hv', hv⟩ := hv
    exact ⟨u' * v', mul_mem hu' hv', fun x => by simp [hu, hv]⟩

private theorem pair_res {E1' E2' : Fin n → Fin n → Module.End ℂ X}
    (h1 : ∀ a b x, (E1' a b x : V) = E1 a b x) (h2 : ∀ a b x, (E2' a b x : V) = E2 a b x) (h : IsPair E1 E2) :
    IsPair E1' E2' :=
  { gl1 := gl_res h1 h.gl1,
    gl2 := gl_res h2 h.gl2,
    comm := fun a b c d => by
      ext x
      simpa [h1, h2] using LinearMap.congr_fun (h.comm a b c d) x,
    unitK := fun a b x y => by simpa [kF, h1, h2, Submodule.coe_inner] using h.unitK a b x y,
    unitP := fun a b x y => by simpa [pF, h1, h2, Submodule.coe_inner] using h.unitP a b x y }

private theorem fin_comap {S : Submodule ℂ V} (hS : FiniteDimensional ℂ S) :
    FiniteDimensional ℂ (S.comap X.subtype) :=
  FiniteDimensional.of_injective (X.subtype.restrict (p := S.comap X.subtype) (q := S) fun _ hx => hx)
    fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun z : S => (z : V)) h))

private theorem der_res {σ : Un n →* (V →ₗ[ℂ] V)} {σ' : Un n →* (X →ₗ[ℂ] X)} {F : Fin n → Fin n → Module.End ℂ V}
    {F' : Fin n → Fin n → Module.End ℂ X} (h : ∀ a b x, (F' a b x : V) = F a b x)
    (hσ : ∀ k x, (σ' k x : V) = σ k x) (hd : IsDerivK σ F) : IsDerivK σ' F' := by
  refine ⟨fun k x y => by simpa [Submodule.coe_inner, hσ] using hd.1 k x y, fun v => ?_⟩
  obtain ⟨S, hfd, hv, hs, hk, hder⟩ := hd.2 v
  refine ⟨S.comap X.subtype, fin_comap hfd, hv, fun k w hw => ?_, fun a b w hw => ?_, fun Y γ hγ w hw => ?_⟩
  · show (σ' k w : V) ∈ S
    rw [hσ]; exact hs k _ hw
  · show (F' a b w : V) ∈ S
    rw [h]; exact hk a b _ hw
  · have h0 : HasDerivAt (fun t : ℝ => (σ' (γ t) w : V)) ((∑ a, ∑ b, Y a b • F' a b w : X) : V) 0 := by
      simpa [hσ, h] using hder Y γ hγ w hw
    rw [hasDerivAt_iff_isLittleO_nhds_zero] at h0 ⊢
    exact Asymptotics.isLittleO_norm_left.1 h0.norm_left

private theorem isK_res {σ : Un n →* (V →ₗ[ℂ] V)} {σ' : Un n →* (X →ₗ[ℂ] X)}
    (hσ : ∀ k x, (σ' k x : V) = σ k x) (hK : IsK σ) : IsK σ' :=
  { iso := fun k x y => by simpa [Submodule.coe_inner, hσ] using hK.iso k x y,
    fin := fun v => by
      obtain ⟨S, hfd, hv, hs⟩ := hK.fin v
      refine ⟨S.comap X.subtype, fin_comap hfd, hv, fun k w hw => ?_⟩
      show (σ' k w : V) ∈ S
      rw [hσ]; exact hs k _ hw,
    cont := fun v w => by simpa [Submodule.coe_inner, hσ] using hK.cont v w }

private theorem rep_res {σ : Un n →* (V →ₗ[ℂ] V)} (h : ∀ k, ∀ x ∈ X, σ k x ∈ X) :
    ∃ σ' : Un n →* (X →ₗ[ℂ] X), ∀ k x, (σ' k x : V) = σ k x :=
  ⟨{ toFun := fun k => (σ k).restrict (h k)
     map_one' := by ext x; simp
     map_mul' := fun a b => by ext x; simp }, fun _ _ => rfl⟩

private theorem trOn_res {S : Submodule ℂ V} (hSX : S ≤ X) {f : Module.End ℂ V} {f' : Module.End ℂ X}
    (h : ∀ x, (f' x : V) = f x) : trOn (S.comap X.subtype) f' = trOn S f := by
  have hiff : (∀ x ∈ S.comap X.subtype, f' x ∈ S.comap X.subtype) ↔ ∀ x ∈ S, f x ∈ S := by
    constructor
    · intro H x hx
      have := H ⟨x, hSX hx⟩ hx
      rwa [Submodule.mem_comap, Submodule.subtype_apply, h] at this
    · intro H x hx
      rw [Submodule.mem_comap, Submodule.subtype_apply, h]
      exact H _ hx
  unfold trOn
  by_cases H : ∀ x ∈ S, f x ∈ S
  · rw [dite_eq_left H, dite_eq_left (hiff.2 H), ← LinearMap.trace_conj' _ (Submodule.comapSubtypeEquivOfLe hSX)]
    congr 1
    ext x
    simp [LinearEquiv.conj_apply, h, Submodule.comapSubtypeEquivOfLe]
  · rw [dite_eq_right H, dite_eq_right fun H' => H (hiff.1 H')]

private theorem iso_res {σ : Un n →* (V →ₗ[ℂ] V)} {σ' : Un n →* (X →ₗ[ℂ] X)}
    (hσ : ∀ k x, (σ' k x : V) = σ k x) (hK : IsK σ) (E : KMod n) {S : Submodule ℂ V} (hfd : FiniteDimensional ℂ S)
    (hSX : S ≤ X) (hSi : S ≤ isoSp σ E) (hS : ∀ x ∈ X, x ∈ isoSp σ E → x ∈ S) (hst : ∀ k, ∀ x ∈ S, σ k x ∈ S) :
    isoSp σ' E = S.comap X.subtype := by
  apply le_antisymm
  · refine iSup_le fun t => ?_
    rintro _ ⟨ξ, rfl⟩
    refine hS _ (t.1 ξ).2 ?_
    have ht : X.subtype ∘ₗ t.1 ∈ invA σ E := fun k ξ => by
      show ((t.1 _ : X) : V) = σ k (t.1 ξ : X)
      rw [t.2 k ξ, hσ]
    exact le_iSup (fun t : invA σ E => LinearMap.range t.1) ⟨_, ht⟩ ⟨ξ, rfl⟩
  · haveI : CompleteSpace S := FiniteDimensional.complete ℂ S
    have heq : ∀ k v, S.starProjection (σ k v) = σ k (S.starProjection v) := by
      intro k v
      refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hst k _ (S.starProjection_apply_mem v)) fun w hw => ?_
      have hw' : w = σ k (σ k⁻¹ w) := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      rw [← map_sub, hw', hK.iso]
      exact S.starProjection_inner_eq_zero v _ (hst _ _ hw)
    let p : V →ₗ[ℂ] X := S.starProjection.toLinearMap.codRestrict X fun v => hSX (S.starProjection_apply_mem v)
    have hp : isoSp σ E ≤ (isoSp σ' E).comap p := by
      refine iSup_le fun t => ?_
      rintro _ ⟨ξ, rfl⟩
      have ht : p ∘ₗ t.1 ∈ invA σ' E := fun k ξ => by
        apply Subtype.ext
        rw [hσ]
        show S.starProjection (t.1 _) = σ k (S.starProjection (t.1 ξ))
        rw [t.2 k ξ, heq]
      exact le_iSup (fun t : invA σ' E => LinearMap.range t.1) ⟨_, ht⟩ ⟨ξ, rfl⟩
    intro x hx
    have h1 : p x = x := Subtype.ext (Submodule.starProjection_eq_self_iff.2 hx)
    have h2 : p x ∈ isoSp σ' E := hp (hSi hx)
    rwa [h1] at h2

end Res

end UpperTheory.V.Z.GSp4Splitting.OnePlaceCyclotomic

open UpperTheory.V.Z.GSp4Splitting.OnePlaceCyclotomic in
theorem UpperTheory.V.Z.GSp4Splitting.onePlace :
    CoreG → LieStab → ProjEx → AvgFacts → AvgTr → OnePlace := by
  intro hC hL hPr hAF hAT n lam hlam E T hT _ _ ν _ hν V _ _ E1 E2 σ A P hloc hP S hfd hne hSi hAS hSa hSs
  obtain ⟨x0, hx0, hx00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨e, he1, he2, he3, he4, -, he6⟩ := hPr n V σ hloc.isK E
  have hσc : ∀ x k, ∀ y ∈ cyc E1 E2 x, σ k y ∈ cyc E1 E2 x := fun x => hL n V σ _ hloc.der _ cyc_K
  set X := cyc E1 E2 x0 with hX
  have hSX : S ≤ X := fun y hy => hSs x0 hx0 y hy hx00
  have hXS : ∀ x ∈ X, x ∈ isoSp σ E → x ∈ S := by
    rintro _ ⟨a, ha, rfl⟩ hi
    exact hSa a ha x0 hx0 hi
  have hAX : ∀ x ∈ X, A x ∈ X := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 := cyc_stab (twist hloc.Asq hloc.AE ha) (hSX (hAS x0 hx0))
    have h2 : (A * a * A) (A x0) = A (a x0) := by
      rw [← Module.End.mul_apply, mul_assoc, hloc.Asq, mul_one, Module.End.mul_apply]
    rwa [h2] at h1
  have hσS : ∀ k, ∀ x ∈ S, σ k x ∈ S := by
    intro k x hx
    refine hXS _ (hσc x0 k x (hSX hx)) ?_
    have h1 := LinearMap.congr_fun (he4 k) x
    simp only [Module.End.mul_apply] at h1
    rw [he3 x (hSi hx)] at h1
    rw [← h1]
    exact he2 _
  have hirr : ∀ v ∈ X, ∀ w ∈ X, v ≠ 0 → w ∈ cyc E1 E2 v := by
    intro v hv w hw hv0
    have hle : cyc E1 E2 v ≤ X := by
      rintro _ ⟨a, ha, rfl⟩
      exact cyc_stab ha hv
    by_cases h0 : ∀ y ∈ cyc E1 E2 v, e y = 0
    · exfalso
      apply hv0
      obtain ⟨a, ha, hav⟩ := hv
      obtain ⟨a', ha', hadj⟩ := adj hloc.pair ha
      have h1 : ⟪a x0, v⟫_ℂ = 0 := by
        rw [hadj, ← he3 x0 (hSi hx0), he1, h0 _ (cyc_stab ha' (cyc_self v)), inner_zero_right]
      rw [hav] at h1
      exact inner_self_eq_zero.1 h1
    · push Not at h0
      obtain ⟨y, hy, hy0⟩ := h0
      have h1 : e y ∈ cyc E1 E2 v := he6 _ (hσc v) y hy
      obtain ⟨b, hb, hbx⟩ := hSs _ (hXS _ (hle h1) (he2 y)) x0 hx0 hy0
      obtain ⟨a, ha, rfl⟩ := hw
      exact cyc_stab ha (hbx ▸ cyc_stab hb h1)
  obtain ⟨σ', hσ⟩ := rep_res (X := X) (hσc x0)
  let E1' : Fin n → Fin n → Module.End ℂ X := fun a b => (E1 a b).restrict fun _ hy => cyc_stab (mem1 a b) hy
  let E2' : Fin n → Fin n → Module.End ℂ X := fun a b => (E2 a b).restrict fun _ hy => cyc_stab (mem2 a b) hy
  have h1 : ∀ a b x, (E1' a b x : V) = E1 a b x := fun _ _ _ => rfl
  have h2 : ∀ a b x, (E2' a b x : V) = E2 a b x := fun _ _ _ => rfl
  let A' : Module.End ℂ X := A.restrict hAX
  have hA : ∀ x, (A' x : V) = A x := fun _ => rfl
  have hPX : ∀ x ∈ X, P x ∈ X := (hAF n ν V σ hloc.isK E T P hT.1 hP).2.2.2.1 X (hσc x0)
  let P' : Module.End ℂ X := P.restrict hPX
  have hP' : ∀ x, (P' x : V) = P x := fun _ => rfl
  clear_value E1' E2' A' P'
  have hAσ : ∀ k, A' * σ' k = σ' k * A' := fun k => by
    ext x
    simpa [hA, hσ] using LinearMap.congr_fun (hloc.Aσ k) x
  have hcore : IsCoreMod (infOf lam) E1' E2' σ' A' :=
    { pair := pair_res h1 h2 hloc.pair
      ch1 := fun m x => Subtype.ext (by rw [gelA_coe h1, hloc.ch1]; rfl)
      ch2 := fun m x => Subtype.ext (by
        rw [gelA_coe (F := barF E2) (fun a b y => by simp [barF, h2]), hloc.ch2]; rfl)
      nontriv := ⟨⟨⟨x0, cyc_self x0⟩, 0, fun h => hx00 (congrArg Subtype.val h)⟩⟩
      irr := fun v w hv => by
        obtain ⟨a, ha, hav⟩ := hirr v v.2 w w.2 fun h => hv (Subtype.ext h)
        obtain ⟨a', ha', haa⟩ := alg_res h1 h2 ha
        exact ⟨a', ha', Subtype.ext (by rw [haa, hav])⟩
      der := der_res (F := kF E1 E2) (fun a b x => by simp [kF, h1, h2]) hσ hloc.der
      Asq := by
        ext x
        simpa [hA] using LinearMap.congr_fun hloc.Asq x
      Aiso := fun x y => by simpa [Submodule.coe_inner, hA] using hloc.Aiso x y
      Aσ := hAσ
      AE := fun a b => by
        ext x
        simpa [hA, h1, h2] using LinearMap.congr_fun (hloc.AE a b) x }
  have hiso := iso_res hσ hloc.isK E hfd hSX hSi hXS hσS
  have havg : IsAvg ν σ' E T P' := fun v w => by
    simpa only [Submodule.coe_inner, hσ, hP'] using hP v w
  obtain ⟨hf, hn, htr⟩ := hAT n ν hν X σ' (isK_res hσ hloc.isK) E T P' A' hT.1 havg hAσ (hiso ▸ fin_comap hfd)
  have hne' : isoSp σ' E ≠ ⊥ := by
    rw [hiso]
    intro h
    have hm : (⟨x0, cyc_self x0⟩ : X) ∈ S.comap X.subtype := hx0
    rw [h] at hm
    exact hx00 (congrArg Subtype.val ((Submodule.mem_bot ℂ).1 hm))
  obtain ⟨s, hs, hst⟩ := hC n lam hlam E T hT X E1' E2' σ' A' hcore hf (hn hne')
  rw [hiso, trOn_res hSX (f := P * A) (fun x => by simp [hP', hA]), hst] at htr
  rcases hs with rfl | rfl
  · left; rw [htr, one_mul]
  · right; rw [htr, neg_one_mul]
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.RlPair
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL GlobalTheory.UnitaryBC
open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.RgBcC.Bridge PositivityTheory.Rg.BcB.Desc
open scoped InnerProductSpace ComplexConjugate

namespace UpperTheory.V.Z.GSp4Splitting

private theorem adj_of_skew {M : Type} [AddCommGroup M] [Module ℂ M] (H : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ)
    (A B : Module.End ℂ M)
    (h : ∀ (z : ℂ) (φ ψ : M), H ((z • A + star z • B) φ) ψ + H φ ((z • A + star z • B) ψ) = 0)
    (φ ψ : M) : H (A φ) ψ = - H φ (B ψ) := by
  have h1 := h 1 φ ψ
  have hI := h Complex.I φ ψ
  simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add (f := _), map_smulₛₗ, one_smul, star_one,
    Complex.star_def, Complex.conj_I, map_neg, neg_smul, map_one, RingHom.id_apply, smul_eq_mul,
    Complex.conj_conj, LinearMap.neg_apply] at h1 hI
  linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * hI +
    ((H (A φ) ψ + H φ (B ψ) - H (B φ) ψ - H φ (A ψ)) / 2) * Complex.I_sq

private theorem lie_single {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (π : CuspSub E n)
    (τ : E →+* ℂ) (a b : Fin n) (z : ℂ) :
    lieOp π (fun i j => atEmb τ (Matrix.single a b z i j)) =
      z • cx τ (lieOp π) a b + star z • cx (PositivityTheory.Rg.Cz.barE E τ) (lieOp π) a b := by
  rw [PositivityTheory.Rg.Cz.GK.lieOp_atEmb, Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro j _ hj
    simp [Matrix.single_apply, hj.symm]
  · simp
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    simp [Matrix.single_apply, hi.symm]
  · simp

private theorem cx_val {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (π : CuspSub E n)
    (τ : E →+* ℂ) (a b : Fin n) (ψ : π.V) : (cx τ (lieOp π) a b ψ).1 = Eop τ a b ψ.1 := by
  rw [← GlobalTheory.WigCap.res_Eop]
  rfl

private theorem emb_ne {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (w : InfinitePlace E) :
    w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
  intro h
  have hc : w.IsComplex := IsTotallyComplex.isComplex w
  exact (InfinitePlace.isComplex_iff.1 hc) (ComplexEmbedding.isReal_iff.2 h.symm)

private theorem gl_pull {U M : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (J : U →ₗ[ℂ] M) (hJ : Function.Injective J) (e : Fin n → Fin n → Module.End ℂ U)
    (F : Fin n → Fin n → Module.End ℂ M) (hF : GlRel F) (h : ∀ a b u, J (e a b u) = F a b (J u)) : GlRel e := by
  intro a b c d
  refine LinearMap.ext fun u => hJ ?_
  have key := LinearMap.congr_fun (hF a b c d) (J u)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at key ⊢
  rw [map_sub, map_sub, h, h, h, h, key]
  split_ifs <;> simp [h]

private theorem gl_neg_swap {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (F : Fin n → Fin n → Module.End ℂ M) (hF : GlRel F) : GlRel (fun a b => -F b a) := by
  intro a b c d
  have key := hF b a d c
  simp only [neg_mul_neg]
  rw [key]
  by_cases h1 : b = c <;> by_cases h2 : d = a
  · subst h1; subst h2; simp; abel
  · have h2' : ¬ a = d := fun h => h2 h.symm
    subst h1
    simp [h2, h2']
  · subst h2
    have h1' : ¬ c = b := fun h => h1 h.symm
    simp [h1, h1']
  · have h2' : ¬ a = d := fun h => h2 h.symm
    have h1' : ¬ c = b := fun h => h1 h.symm
    simp [h1, h1', h2, h2']

end UpperTheory.V.Z.GSp4Splitting

theorem UpperTheory.V.Z.GSp4Splitting.rlPair :
    RlPair := by
  intro E _ _ _ n hn π hθ K hKo hKc hKθ _ _ μf _ D w
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := emb_ne w
  let A : Fin n → Fin n → Module.End ℂ π.V := cx w.embedding (lieOp π)
  let B : Fin n → Fin n → Module.End ℂ π.V := cx (PositivityTheory.Rg.Cz.barE E w.embedding) (lieOp π)
  have v1 : ∀ a b u, (D.i (D.E1 w a b u)).1 = Eop w.embedding a b (D.i u).1 := fun a b u => D.hE1 w a b u
  have v2 : ∀ a b u, (D.i (D.E2 w a b u)).1 = -Eop (ComplexEmbedding.conjugate w.embedding) b a (D.i u).1 :=
    fun a b u => D.hE2 w a b u
  have iE1 : ∀ a b u, D.i (D.E1 w a b u) = A a b (D.i u) := fun a b u =>
    Subtype.ext ((v1 a b u).trans (cx_val π _ a b _).symm)
  have iE2 : ∀ a b u, D.i (D.E2 w a b u) = -B b a (D.i u) := fun a b u =>
    Subtype.ext ((v2 a b u).trans (congrArg Neg.neg (cx_val π _ b a _).symm))
  have adjA : ∀ a b φ ψ, D.H (A a b φ) ψ = -D.H φ (B a b ψ) := fun a b =>
    adj_of_skew D.H _ _ fun z φ ψ => by
      rw [← lie_single]
      exact D.pet.2.2.1 _ φ ψ
  have adjB : ∀ a b φ ψ, D.H (B a b φ) ψ = -D.H φ (A a b ψ) := fun a b φ ψ => by
    have h := congrArg (starRingEnd ℂ) (adjA a b ψ φ)
    rw [map_neg, D.pet.1, D.pet.1] at h
    rw [h, neg_neg]
  have hJ : Function.Injective (π.V.subtype ∘ₗ D.i) := π.V.injective_subtype.comp D.inj
  refine { gl1 := ?_, gl2 := ?_, comm := ?_, unitK := ?_, unitP := ?_ }
  · exact gl_pull _ hJ _ _ (glRel_Eop w.embedding) v1
  · exact gl_pull _ hJ _ _ (gl_neg_swap _ (glRel_Eop (ComplexEmbedding.conjugate w.embedding))) v2
  · intro a b c d
    refine LinearMap.ext fun u => D.inj (Subtype.ext ?_)
    change (D.i (D.E1 w a b (D.E2 w c d u))).1 = (D.i (D.E2 w c d (D.E1 w a b u))).1
    rw [v1, v2, v2, v1, map_neg]
    exact congrArg Neg.neg (LinearMap.congr_fun (Eop_comm hne a b d c) (D.i u).1)
  · intro a b x y
    simp only [kF, LinearMap.add_apply]
    rw [D.inner_eq, D.inner_eq]
    simp only [map_add (f := _), iE1, iE2, map_neg, LinearMap.add_apply, LinearMap.neg_apply, adjA, adjB]
    ring
  · intro a b x y
    simp only [pF, LinearMap.sub_apply]
    rw [D.inner_eq, D.inner_eq]
    simp only [map_sub, iE1, iE2, map_neg, LinearMap.sub_apply, LinearMap.neg_apply, adjA, adjB]
    ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.RlChar
open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc

namespace UpperTheory.V.Z.GSp4Splitting

open NumberField Finset

private theorem map_epow {n : ℕ} {U W : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
    [AddCommGroup W] [Module ℂ W] (j : U →ₗ[ℂ] W) (M : Fin n → Fin n → Module.End ℂ U)
    (N : Fin n → Fin n → Module.End ℂ W) (h : ∀ a b u, j (M a b u) = N a b (j u)) (m : ℕ) :
    ∀ a b u, j (PositivityTheory.RgBcC.RealD.epow M m a b u) = Formalism.REAL.epow N m a b (j u) := by
  induction m with
  | zero =>
    intro a b u
    by_cases hab : a = b <;> simp [PositivityTheory.RgBcC.RealD.epow, Formalism.REAL.epow, hab]
  | succ m ih =>
    intro a b u
    rw [PositivityTheory.RgBcC.Bridge.epow_succ']
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [PositivityTheory.RgBcC.RealD.epow, LinearMap.sum_apply, map_sum, Module.End.mul_apply, h, ih]

private theorem map_gelA {n : ℕ} {U W : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
    [AddCommGroup W] [Module ℂ W] (j : U →ₗ[ℂ] W) (M : Fin n → Fin n → Module.End ℂ U)
    (N : Fin n → Fin n → Module.End ℂ W) (h : ∀ a b u, j (M a b u) = N a b (j u)) (m : ℕ) (u : U) :
    j (gelA M m u) = Formalism.REAL.etr N m (j u) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gelA, Formalism.REAL.etr, LinearMap.sum_apply, map_sum, map_epow j M N h m]

end UpperTheory.V.Z.GSp4Splitting

theorem UpperTheory.V.Z.GSp4Splitting.rlChar :
    RlChar := by
  intro E _ _ _ n _ π _ K _ _ _ _ _ μf _ D w lam hch
  have hin : Function.Injective ((π.V.subtype).comp D.i) :=
    Subtype.val_injective.comp D.inj
  have h1 := (PositivityTheory.RgBcC.Bridge.hasInfCharGL_iff π.V _ _).1 hch.1
  have h2 := (PositivityTheory.RgBcC.Bridge.hasInfCharGL_iff π.V _ _).1 hch.2
  constructor
  · intro m x
    apply hin
    have e := map_gelA ((π.V.subtype).comp D.i) (D.E1 w) (PositivityTheory.RgBcC.Bridge.eopW w true)
      (fun a b u => D.hE1 w a b u) m x
    rw [e, map_smul]
    simpa [PositivityTheory.RgBcC.Bridge.eopW] using h1 _ (D.i x).2 m
  · intro m x
    apply hin
    have e := map_gelA ((π.V.subtype).comp D.i) (barF (D.E2 w)) (PositivityTheory.RgBcC.Bridge.eopW w false)
      (fun a b u => by
        have := D.hE2 w b a u
        simp only [barF, LinearMap.neg_apply, map_neg, LinearMap.comp_apply, Submodule.subtype_apply,
          Submodule.coe_neg, this, neg_neg]) m x
    rw [e, map_smul]
    simpa [PositivityTheory.RgBcC.Bridge.eopW] using h2 _ (D.i x).2 m
end

namespace UpperTheory.V.Z.GSp4Splitting

theorem global_haarAverage_trace_identity : PositivityTheory.Rg.BcB.Desc.ThetaFixedGlobalCharacter :=
  exists_global_hecke_theta_lift avgEx (absGlob multiFac lieStab projEx avgFacts (onePlace coreG lieStab projEx avgFacts (avgTr avgFacts))) lowIso2 heckeMem
    (rlEx petEx heckeMem) rlPair rlChar rlK rlTheta rlComm (rlHecke heckeMem) (rlSimple heckeMem lieStab rlK) rlFin
    (rlLow heckeMem lowType) (opForm heckeMem rlComm locAct)

end UpperTheory.V.Z.GSp4Splitting
