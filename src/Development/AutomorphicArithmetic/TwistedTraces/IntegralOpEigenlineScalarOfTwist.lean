module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TvDefs
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TwistPerm
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ThickFrames
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TwistYA
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.InnerOps

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.IntegralOpEigenlineScalarOfTwist
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4HoweTheory.TraceLine
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

theorem UpperTheory.V.Z.Tf.L4.traceLine :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (W : Submodule ℂ V), Module.finrank ℂ W = 1 → ∀ (B : V →ₗ[ℂ] V) (m : ℂ), m ≠ 0 →
      (∀ v, B v ∈ W) → (∀ v ∈ W, B v = m • v) → ∀ A : V ≃ₗ[ℂ] V, (∀ v ∈ W, A v ∈ W) →
        ∃ c : ℂ, c ≠ 0 ∧ HasFinTrace (B ∘ₗ (A : V →ₗ[ℂ] V)) c := by
  intro V _ _ W hW B m hm hB hBW A hA
  have hR : LinearMap.range (B ∘ₗ (A : V →ₗ[ℂ] V)) = W := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      exact hB _
    · intro w hw
      refine ⟨A.symm (m⁻¹ • w), ?_⟩
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      rw [hBW _ (W.smul_mem _ hw), smul_smul, mul_inv_cancel₀ hm, one_smul]
  have h1 : Module.finrank ℂ (LinearMap.range (B ∘ₗ (A : V →ₗ[ℂ] V))) = 1 := by rw [hR, hW]
  have hfin : FiniteDimensional ℂ (LinearMap.range (B ∘ₗ (A : V →ₗ[ℂ] V))) :=
    Module.finite_of_finrank_eq_succ h1
  refine ⟨_, ?_, hfin, rfl⟩
  set f := (B ∘ₗ (A : V →ₗ[ℂ] V)).restrict (p := LinearMap.range (B ∘ₗ (A : V →ₗ[ℂ] V)))
    (q := LinearMap.range (B ∘ₗ (A : V →ₗ[ℂ] V)))
    (fun v _ => LinearMap.mem_range_self (B ∘ₗ (A : V →ₗ[ℂ] V)) v) with hf
  obtain ⟨v, hv, hgen⟩ := finrank_eq_one_iff'.1 h1
  obtain ⟨c, hc⟩ := hgen (f v)
  have hfc : f = c • LinearMap.id := by
    ext1 w
    obtain ⟨a, rfl⟩ := hgen w
    rw [map_smul, ← hc, LinearMap.smul_apply, LinearMap.id_apply, smul_comm]
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h2 : ((f v : LinearMap.range (B ∘ₗ (A : V →ₗ[ℂ] V))) : V) = 0 := by
      rw [← hc]; simp
    have h3 : B (A (v : V)) = 0 := h2
    have hvW : (v : V) ∈ W := hR ▸ v.2
    rw [hBW _ (hA _ hvW), smul_eq_zero] at h3
    rcases h3 with h3 | h3
    · exact hm h3
    · exact hv (Subtype.ext (by simpa using h3))
  rw [hfc, map_smul, LinearMap.trace_id, h1]
  simpa using hc0
end

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate Classical InnerProductSpace

theorem UpperTheory.integralOp_eigenline_scalar_of_twist :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (m : Measure G)
        [m.IsHaarMeasure] (τ : SmIrr G) (I : τ.V ≃ₗ[ℂ] τ.V) (s : G →* G) (J : Subgroup G) (χ : G → ℂ) (A : τ.V →ₗ[ℂ] τ.V) (e : τ.V),
        CO J → IsChr J χ → m J = 1 → IsIntegralOp m τ.ρ ((J : Set G).indicator fun x => conj (χ x)) A →
        e ≠ 0 → (∀ g ∈ J, τ.ρ g e = χ g • e) → (∀ x : τ.V, (∀ g ∈ J, τ.ρ g x = χ g • x) → ∃ c : ℂ, x = c • e) →
        (∀ x ∈ J, s x ∈ J ∧ χ (s x) = χ x) → (∀ g x, I (τ.ρ g x) = τ.ρ (s g) (I x)) →
        ∃ t : ℂ, t ≠ 0 ∧ HasTwTrace m τ I ((J : Set G).indicator fun x => conj (χ x)) t := by
  intro G _ _ _ _ _ m _ τ I s J χ A e hCO hχ hm hA he hty hone hs hI
  have hJo : IsOpen (J : Set G) := hCO.2
  have hcc : ∀ g ∈ J, conj (χ g) * χ g = 1 := by
    intro g hg
    rw [Complex.conj_mul', hχ.2.1 g hg]
    simp

  have hAe : A e = e := by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, sub_eq_zero, (hA e l).2]
    have h1 : (fun g => ((J : Set G).indicator (fun x => conj (χ x)) g) * l (τ.ρ g e)) =
        (J : Set G).indicator fun _ => l e := by
      funext g
      by_cases hg : g ∈ (J : Set G)
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, hty g hg, map_smul, smul_eq_mul,
          ← mul_assoc, hcc g hg, one_mul]
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, zero_mul]
    rw [h1, integral_indicator_const _ hJo.measurableSet]
    simp [Measure.real, hm]

  have hAty : ∀ x, ∀ u ∈ J, τ.ρ u (A x) = χ u • A x := by
    intro x u hu
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    have h1 := (hA x (l ∘ₗ τ.ρ u)).2
    have h2 := (hA x l).2
    rw [map_sub, map_smul, sub_eq_zero, h2, smul_eq_mul, ← integral_const_mul,
      ← integral_mul_left_eq_self (fun g => χ u * (((J : Set G).indicator (fun x => conj (χ x)) g) * l (τ.ρ g x))) u]
    refine h1.trans (integral_congr_ae (Filter.Eventually.of_forall fun g => ?_))
    have h3 : χ u * (J : Set G).indicator (fun x => conj (χ x)) (u * g) =
        (J : Set G).indicator (fun x => conj (χ x)) g := by
      by_cases hg : g ∈ J
      · have hug : u * g ∈ (J : Set G) := J.mul_mem hu hg
        have hg' : g ∈ (J : Set G) := hg
        rw [Set.indicator_of_mem hug, Set.indicator_of_mem hg', hχ.2.2 u hu g hg, map_mul, ← mul_assoc,
          mul_comm (χ u), hcc u hu, one_mul]
      · have hug : u * g ∉ (J : Set G) := fun h => hg ((J.mul_mem_cancel_left hu).1 h)
        have hg' : g ∉ (J : Set G) := hg
        rw [Set.indicator_of_notMem hug, Set.indicator_of_notMem hg', mul_zero]
    simp only [← mul_assoc, h3, map_mul, LinearMap.comp_apply, Module.End.mul_apply]

  obtain ⟨a, ha⟩ := hone (I.symm e) (by
    intro g hg
    apply I.injective
    rw [hI, map_smul, LinearEquiv.apply_symm_apply, hty _ (hs g hg).1, (hs g hg).2])
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    exact he (by simpa using ha)
  have hIe : I e = a⁻¹ • e := by
    have h1 : e = a • I e := by
      have := congrArg I ha
      rwa [LinearEquiv.apply_symm_apply, map_smul] at this
    rw [eq_inv_smul_iff₀ ha0]
    exact h1.symm
  obtain ⟨t, ht, htr⟩ := UpperTheory.V.Z.Tf.L4.traceLine τ.V (Submodule.span ℂ {e}) (finrank_span_singleton he) A 1 one_ne_zero
    (fun v => by
      obtain ⟨c, hc⟩ := hone (A v) (hAty v)
      rw [hc]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e))
    (fun v hv => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
      rw [map_smul, hAe, one_smul])
    I
    (fun v hv => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
      rw [map_smul, hIe]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)))
  exact ⟨t, ht, A, hA, htr⟩
end

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.GaloisTwistCommuteArchOperatorAndOffProjection
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate Classical InnerProductSpace

set_option maxHeartbeats 1600000 in
theorem UpperTheory.galoisTwist_commute_archOperator_and_offProjection :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → ∀ k n : ℕ,
        ∀ (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure] (θ : Twist μ), IsGalTwist σ θ →
        ∀ (D : InfD σ k) (s : Fin (k + 1) → archGroup F n →* archGroup E n) (hs : ∀ i, Continuous (s i)), IsBlockElement D n s →
        ∀ (νE : Measure (archGroup E n)) [νE.IsHaarMeasure] (νF : Measure (archGroup F n)) [νF.IsHaarMeasure] (b a : TI F n)
          (aE : TI E n) (aF : TI F n), ArchSlot D νE νF b a aE aF →
        ∀ (q : Pl F) (w₀ : PlacesOver E q) (T : Ty σ n q w₀),
          Commute θ.U (Oinf μ νE aE) ∧ Commute θ.U (prj (offN μ T)) := by
  intro F E _ _ _ _ _ _ σ hσ k n μ _ θ hθ D s hs hposition νE _ νF _ b a aE aF hA q w₀ T
  obtain ⟨tp1, -, tp3⟩ := twistPerm F E σ hσ k n μ θ hθ
  refine ⟨?_, tp3 q w₀ T (nsS T : Set (Pl F))⟩
  obtain ⟨-, -, ag3, -⟩ := archBasic F E σ k D n
  let O : Fin (k + 1) → LL μ →L[ℂ] LL μ := fun i => OComponent μ (s i) (hs i) νF a
  have hOi : Oinf μ νE aE = (List.ofFn O).prod :=
    tensOp F E σ k D n νE νF hA.meas s hs hposition (LL μ) _ (fun _ => a) aE hA.tens
  have hss : ∀ i j, i ≠ j → ∀ g h, Commute (s i g) (s j h) := fun i j hij g h => by
    rw [hposition, hposition]
    show _ * _ = _ * _
    rw [← ag3, ← ag3]
    exact congrArg _ (Pi.mulSingle_commute (f := fun _ : Fin (k + 1) => archGroup F n) hij g h).eq
  have hOc : ∀ (B : LL μ →L[ℂ] LL μ) i, (∀ g, Commute B (rightRegularRep (rationalGLOne (K := E) (n := n)) μ (archP E n (s i g)))) →
      Commute B (O i) := fun B i h => ContinuousLinearMap.ext fun v =>
    UpperTheory.ConvolutionTheory.L1.TY.operatorAt_int μ (hs i) (hs i) νF a B (fun x u => DFunLike.congr_fun (h x).eq u) v
  have hrep : ∀ x y : normOneGL (K := E) (n := n), Commute x y →
      Commute (rightRegularRep (rationalGLOne (K := E) (n := n)) μ x) (rightRegularRep (rationalGLOne (K := E) (n := n)) μ y) := fun x y h =>
    ContinuousLinearMap.ext fun v => by
      simp only [ContinuousLinearMap.mul_apply]
      rw [← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, h.eq]
  have hOa : ∀ i j, i ≠ j → ∀ g, Commute (O i) (rightRegularRep (rationalGLOne (K := E) (n := n)) μ (archP E n (s j g))) :=
    fun i j hij g => (hOc _ i fun x => hrep _ _ ((hss j i hij.symm g x).map _)).symm
  have hOO : ∀ i j, Commute (O i) (O j) := fun i j => by
    by_cases e : i = j
    · rw [e]
    · exact hOc _ j (hOa i j e)
  have hUO : ∀ i, θ.U * O (i + 1) = O i * θ.U := fun i => ContinuousLinearMap.ext fun v =>
    UpperTheory.ConvolutionTheory.L1.TY.operatorAt_int μ (hs _) (hs _) νF a θ.U (tp1 D s hposition i) v
  have key : ∀ l : List (Fin (k + 1)), θ.U * (l.map fun i => O (i + 1)).prod = (l.map O).prod * θ.U := by
    intro l
    induction l with
    | nil => simp
    | cons x l ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [← mul_assoc, hUO, mul_assoc, ih, mul_assoc]
  have hperm : (List.ofFn fun i => O (i + 1)).prod = (List.ofFn O).prod := by
    refine List.Perm.prod_eq' (Equiv.Perm.ofFn_comp_perm (Equiv.addRight (1 : Fin (k + 1))) O) ?_
    rw [List.ofFn_eq_map, List.pairwise_map]
    exact List.pairwise_of_forall fun x y => hOO _ _
  have h := key (List.finRange (k + 1))
  rw [← List.ofFn_eq_map, ← List.ofFn_eq_map, hperm] at h
  rw [hOi]
  exact h
end

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.ProdLocalOperatorsMemFixedAndOffNCMDatum
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate Classical InnerProductSpace

section Ops
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]

private theorem rhoL_mul (w : Pl K) (g h : Gw n w) : rhoL μ w (g * h) = rhoL μ w g ∘L rhoL μ w h := by
  have := (UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥).2.2.2.2.2.1
  simp only [rhoL, map_mul, this]

private theorem rhoL_comm {w w' : Pl K} (h : w ≠ w') (g : Gw n w) (g' : Gw n w') :
    Commute (rhoL μ w g) (rhoL μ w' g') := by
  have h1 := (UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥).2.2.2.2.2.1
  have h2 := (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.2.2.1 w' h.symm g g'
  show rhoL μ w g ∘L rhoL μ w' g' = rhoL μ w' g' ∘L rhoL μ w g
  simp only [rhoL, ← h1, h2]

private theorem oloc_comm {w : Pl K} [MeasurableSpace (Gw n w)] {m : Measure (Gw n w)} {ψ : Gw n w → ℂ}
    {Bo : LL μ →L[ℂ] LL μ} (h : IsOloc μ w m ψ Bo) (R : LL μ →L[ℂ] LL μ) (hR : ∀ g, Commute R (rhoL μ w g)) :
    Commute R Bo := by
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_
  show ⟪u, R (Bo v)⟫_ℂ = ⟪u, Bo (R v)⟫_ℂ
  rw [← ContinuousLinearMap.adjoint_inner_left R, h, h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show ψ g * _ = ψ g * _
  congr 1
  rw [ContinuousLinearMap.adjoint_inner_left]
  have := congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (hR g).eq
  simp only [ContinuousLinearMap.mul_apply] at this
  rw [this]

private theorem oloc_fix {w : Pl K} [MeasurableSpace (Gw n w)] [BorelSpace (Gw n w)] {m : Measure (Gw n w)}
    [m.IsHaarMeasure] {ψ : Gw n w → ℂ} {Bo : LL μ →L[ℂ] LL μ} (h : IsOloc μ w m ψ Bo) (J : Subgroup (Gw n w))
    (hJ : ∀ u ∈ J, ∀ g, ψ (u * g) = ψ g) (v : LL μ) : Bo v ∈ fixL μ w J := by
  refine ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ _).2.1 _).2 ?_
  rintro _ ⟨u, hu, rfl⟩
  refine ext_inner_left ℂ fun a => ?_
  show ⟪a, rhoL μ w u (Bo v)⟫_ℂ = ⟪a, Bo v⟫_ℂ
  rw [← ContinuousLinearMap.adjoint_inner_left (rhoL μ w u), h, h,
    ← integral_mul_left_eq_self (μ := m) (fun g => ψ g * ⟪a, rhoL μ w g v⟫_ℂ) u]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show ψ g * _ = ψ (u * g) * _
  rw [hJ u hu, rhoL_mul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]

private theorem mem_eigL {w : Pl K} {J : Subgroup (Gw n w)} {χ : Gw n w → ℂ} {v : LL μ} :
    v ∈ eigL μ w J χ ↔ ∀ x ∈ J, rhoL μ w x v = χ x • v := by
  simp [eigL, Submodule.mem_iInf, LinearMap.mem_eqLocus]

private theorem mem_fixL {w : Pl K} {J : Subgroup (Gw n w)} {v : LL μ} :
    v ∈ fixL μ w J ↔ ∀ x ∈ J, rhoL μ w x v = v := by
  refine ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ _).2.1 v).trans ⟨fun h x hx => h _ ⟨x, hx, rfl⟩, ?_⟩
  rintro h _ ⟨x, hx, rfl⟩
  exact h x hx

end Ops

private theorem prod_range {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (X : Set H) (l : List (H →L[ℂ] H))
    (hl : ∀ O ∈ l, ∀ v ∈ X, O v ∈ X) (hO : ∃ O ∈ l, ∀ v, O v ∈ X) (f : H) : l.prod f ∈ X := by
  induction l with
  | nil => obtain ⟨O, hO, -⟩ := hO; simp at hO
  | cons a t ih =>
    rw [List.prod_cons, ContinuousLinearMap.mul_apply]
    obtain ⟨O, hO, hr⟩ := hO
    rcases List.mem_cons.1 hO with rfl | ht
    · exact hr _
    · exact hl a List.mem_cons_self _ (ih (fun O' h' => hl O' (List.mem_cons_of_mem _ h')) ⟨O, ht, hr⟩)

private theorem under_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F}
    (w : PlacesOver E v) : w.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext w.2.over.symm

theorem UpperTheory.prod_localOperators_mem_fixed_and_offN_CMDatum :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ) (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure] (q : Pl F) (w₀ : PlacesOver E q)
        (T : Ty σ n q w₀) (r : ℕ) (p : Fin r → Pl F), Function.Injective p → (∀ i, p i ∈ nsS T) →
        ∀ [∀ u : Pl E, MeasurableSpace (Gw n u)] [∀ u : Pl E, BorelSpace (Gw n u)] (mm : ∀ u : Pl E, Measure (Gw n u)),
          (∀ u, (mm u).IsHaarMeasure) →
        ∀ (ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ) (U : ∀ i, Subgroup (Gw n (T.mk' (p i)).1)),
          (∀ i, ∀ u ∈ U i, ∀ g, ψ (p i) (u * g) = ψ (p i) g) →
        ∀ B : Fin r → LL μ →L[ℂ] LL μ, (∀ i, IsOloc μ (T.mk' (p i)).1 (mm _) (ψ (p i)) (B i)) →
          (∀ f, (List.ofFn B).prod f ∈ ⨅ i, fixL μ (T.mk' (p i)).1 (U i)) ∧ (∀ f ∈ offN μ T, (List.ofFn B).prod f ∈ offN μ T) := by
  intro F E _ _ _ _ _ σ n μ _ q w₀ T r p hp hns _ _ mm hmm ψ U hU B hB
  have hfix : ∀ i v, B i v ∈ fixL μ (T.mk' (p i)).1 (U i) := fun i v => by
    haveI := hmm (T.mk' (p i)).1
    exact oloc_fix μ (hB i) (U i) (hU i) v
  have hne : ∀ i j, i ≠ j → (T.mk' (p i)).1 ≠ (T.mk' (p j)).1 := fun i j hij h =>
    hij (hp ((under_eq (T.mk' (p i))).symm.trans
      ((congrArg (fun w : Pl E => w.under (𝓞 F)) h).trans (under_eq (T.mk' (p j))))))
  have hcomm : ∀ i (w : Pl E), w ≠ (T.mk' (p i)).1 → ∀ (g : Gw n w) (v : LL μ),
      B i (rhoL μ w g v) = rhoL μ w g (B i v) := fun i w hw g v => by
    have := congrArg (fun S : LL μ →L[ℂ] LL μ => S v)
      (oloc_comm μ (hB i) (rhoL μ w g) fun g' => rhoL_comm μ hw g g').eq
    simp only [ContinuousLinearMap.mul_apply] at this
    exact this.symm
  refine ⟨fun f => ?_, ?_⟩
  · rw [Submodule.mem_iInf]
    intro i
    refine prod_range (fixL μ (T.mk' (p i)).1 (U i) : Set (LL μ)) (List.ofFn B) (fun O hO v hv => ?_)
      ⟨B i, (List.mem_ofFn' _ _).2 ⟨i, rfl⟩, hfix i⟩ f
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hO
    by_cases h : j = i
    · subst h
      exact hfix j v
    · refine (mem_fixL μ).2 fun x hx => ?_
      rw [← hcomm j _ (hne i j (Ne.symm h)) x v, (mem_fixL μ).1 hv x hx]
  · have hoff : ∀ {v : LL μ}, v ∈ offN μ T ↔
        ∀ w : Pl E, w.under (𝓞 F) ∉ (nsS T : Set (Pl F)) → ∀ x ∈ T.J w, rhoL μ w x v = T.χ w x • v := by
      intro v
      simp only [offN, Submodule.mem_iInf, mem_eigL]
    have key : ∀ O ∈ List.ofFn B, ∀ f ∈ offN μ T, O f ∈ offN μ T := by
      intro O hO f hf
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hO
      refine hoff.2 fun w hw x hx => ?_
      have hwi : w ≠ (T.mk' (p i)).1 := fun h => hw (by
        rw [h, under_eq]
        exact hns i)
      rw [← hcomm i w hwi x f, hoff.1 hf w hw x hx, map_smul]
    exact List.prod_induction (fun O : LL μ →L[ℂ] LL μ => ∀ f ∈ offN μ T, O f ∈ offN μ T)
      (fun a b ha hb f hf => ha _ (hb f hf)) (fun f hf => hf) key
end

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.HeckeOperatorSummandWeightCMDatum
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate Classical InnerProductSpace

namespace UpperTheory.EigenLatticeOffDiagonal

section Ops
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]

private theorem rhoL_mul (w : Pl K) (g h : Gw n w) : rhoL μ w (g * h) = rhoL μ w g ∘L rhoL μ w h := by
  have := (UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥).2.2.2.2.2.1
  simp only [rhoL, map_mul, this]

private theorem rhoL_comm {w w' : Pl K} (h : w ≠ w') (g : Gw n w) (g' : Gw n w') : Commute (rhoL μ w g) (rhoL μ w' g') := by
  have h1 := (UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥).2.2.2.2.2.1
  have h2 := (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.2.2.1 w' h.symm g g'
  show rhoL μ w g ∘L rhoL μ w' g' = rhoL μ w' g' ∘L rhoL μ w g
  simp only [rhoL, ← h1, h2]

private theorem arch_comm (a : archGroup K n) (w : Pl K) (g : Gw n w) :
    Commute (rightRegularRep (rationalGLOne (K := K) (n := n)) μ (archP K n a)) (rhoL μ w g) := by
  show rightRegularRep (rationalGLOne (K := K) (n := n)) μ (archP K n a) * rightRegularRep (rationalGLOne (K := K) (n := n)) μ (MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g)) =
    rightRegularRep (rationalGLOne (K := K) (n := n)) μ (MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g)) * rightRegularRep (rationalGLOne (K := K) (n := n)) μ (archP K n a)
  rw [← UnitaryRep.map_mul, ← UnitaryRep.map_mul, archimedeanProjection_apply, MultiplicityOne.finProj_mul_archProj_comm]

private theorem oloc_comm {w : Pl K} [MeasurableSpace (Gw n w)] {m : Measure (Gw n w)} {ψ : Gw n w → ℂ}
    {Bo : LL μ →L[ℂ] LL μ} (h : IsOloc μ w m ψ Bo) (R : LL μ →L[ℂ] LL μ) (hR : ∀ g, Commute R (rhoL μ w g)) :
    Commute R Bo := by
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_
  show ⟪u, R (Bo v)⟫_ℂ = ⟪u, Bo (R v)⟫_ℂ
  rw [← ContinuousLinearMap.adjoint_inner_left R, h, h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show ψ g * _ = ψ g * _
  congr 1
  rw [ContinuousLinearMap.adjoint_inner_left]
  have := congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (hR g).eq
  simp only [ContinuousLinearMap.mul_apply] at this
  rw [this]

private theorem oloc_fix {w : Pl K} [MeasurableSpace (Gw n w)] [BorelSpace (Gw n w)] {m : Measure (Gw n w)} [m.IsHaarMeasure]
    {ψ : Gw n w → ℂ} {Bo : LL μ →L[ℂ] LL μ} (h : IsOloc μ w m ψ Bo) (J : Subgroup (Gw n w))
    (hJ : ∀ u ∈ J, ∀ g, ψ (u * g) = ψ g) (v : LL μ) : Bo v ∈ fixL μ w J := by
  refine ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ _).2.1 _).2 ?_
  rintro _ ⟨u, hu, rfl⟩
  refine ext_inner_left ℂ fun a => ?_
  show ⟪a, rhoL μ w u (Bo v)⟫_ℂ = ⟪a, Bo v⟫_ℂ
  rw [← ContinuousLinearMap.adjoint_inner_left (rhoL μ w u), h, h,
    ← integral_mul_left_eq_self (μ := m) (fun g => ψ g * ⟪a, rhoL μ w g v⟫_ℂ) u]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show ψ g * _ = ψ (u * g) * _
  rw [hJ u hu, rhoL_mul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]

private theorem mem_eigL {w : Pl K} {J : Subgroup (Gw n w)} {χ : Gw n w → ℂ} {v : LL μ} :
    v ∈ eigL μ w J χ ↔ ∀ x ∈ J, rhoL μ w x v = χ x • v := by
  simp [eigL, Submodule.mem_iInf, LinearMap.mem_eqLocus]

private theorem comm_prj {V : Submodule ℂ (LL μ)} (hV : IsClosed (V : Set (LL μ))) (R : LL μ →L[ℂ] LL μ)
    (hR : Commute (prj V) R) (v : LL μ) (hv : v ∈ V) : R v ∈ V := by
  have hself : ∀ x ∈ V, prj V x = x := fun x hx =>
    Submodule.starProjection_eq_self_iff.2 (Submodule.le_topologicalClosure V hx)
  have h := congrArg (fun S : LL μ →L[ℂ] LL μ => S v) hR.eq
  simp only [ContinuousLinearMap.mul_apply, hself v hv] at h
  rw [← h]
  exact hV.submodule_topologicalClosure_eq.le (Submodule.starProjection_apply_mem V.topologicalClosure (R v))

end Ops

section Ty
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E ≃ₐ[F] E} {n : ℕ} {q : Pl F} {w₀ : PlacesOver E q} (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure]

private theorem mem_offN (T : Ty σ n q w₀) {v : LL μ} :
    v ∈ offN μ T ↔ ∀ w, w.under (𝓞 F) ∉ (nsS T : Set (Pl F)) → ∀ x ∈ T.J w, rhoL μ w x v = T.χ w x • v := by
  simp only [offN, Submodule.mem_iInf, mem_eigL]

private theorem off_step (T : Ty σ n q w₀) (Bo : LL μ →L[ℂ] LL μ) (w₁ : Pl E)
    (hfix : ∀ v, Bo v ∈ fixL μ w₁ (T.J w₁)) (hχ : T.χ w₁ = 1)
    (hc : ∀ w, w ≠ w₁ → ∀ g, Commute Bo (rhoL μ w g)) (v : LL μ) (hv : v ∈ offN μ T) : Bo v ∈ offN μ T := by
  rw [mem_offN] at hv ⊢
  intro w hw x hx
  by_cases h : w = w₁
  · subst h
    have hch : IsChr (T.J w) 1 := hχ ▸ T.chr w
    have h1 := (UpperTheory.ConvolutionTheory.L1.eigBasic E n μ w (T.J w) 1 (T.co w) hch).2.1
    have h2 : Bo v ∈ eigL μ w (T.J w) 1 := by rw [h1]; exact hfix v
    rw [hχ]
    exact (mem_eigL μ).1 h2 x hx
  · have := congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (hc w h x).eq
    simp only [ContinuousLinearMap.mul_apply] at this
    rw [← this, hv w hw x hx, map_smul]

end Ty

end UpperTheory.EigenLatticeOffDiagonal

open UpperTheory.EigenLatticeOffDiagonal hiding rhoL_mul rhoL_comm oloc_comm oloc_fix in
theorem UpperTheory.heckeOperator_summand_weight_CMDatum :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ) (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure] (q : Pl F) (w₀ : PlacesOver E q),
        GM.Split E q → ∀ (T : Ty σ n q w₀) (V : Submodule ℂ (LL μ)), IsSummand μ V → ∀ (e : Fin n → ℤ) (j r : ℕ) (p : Fin r → Pl F),
        (∀ i, p i ∈ T.sp) → ∀ [∀ u : Pl E, MeasurableSpace (Gw n u)] [∀ u : Pl E, BorelSpace (Gw n u)]
          (mm : ∀ u : Pl E, Measure (Gw n u)), (∀ u, (mm u).IsHaarMeasure ∧ mm u (T.J u) = 1) →
        ∀ (ψ : ∀ v : Pl F, Gw n (T.mk' v).1 → ℂ), (∀ i, Test (ψ (p i)) ∧ ∀ u ∈ T.J (T.mk' (p i)).1, ∀ g, ψ (p i) (u * g) = ψ (p i) g) →
        ∀ B : Fin r → LL μ →L[ℂ] LL μ, (∀ i, IsOloc μ (T.mk' (p i)).1 (mm _) (ψ (p i)) (B i)) →
          (∀ g, Commute ((Uiw μ w₀.1 e ^ j) ∘L (List.ofFn B).prod) (rightRegularRep (rationalGLOne (K := E) (n := n)) μ (archP E n g))) ∧
          (∀ w ∉ T.marked, ∀ g, Commute ((Uiw μ w₀.1 e ^ j) ∘L (List.ofFn B).prod) (rhoL μ w g)) ∧
          (∀ f ∈ offN μ T, ((Uiw μ w₀.1 e ^ j) ∘L (List.ofFn B).prod) f ∈ offN μ T) ∧
          (∀ f ∈ V, ((Uiw μ w₀.1 e ^ j) ∘L (List.ofFn B).prod) f ∈ V) := by
  intro F E _ _ _ _ _ σ n μ _ q w₀ hq T V hV e j r p hp _ _ mm hmm ψ hψ B hBo
  have hVc : IsClosed (V : Set (LL μ)) := IsSummandOf.closed hV
  have hVrho : ∀ (w : Pl E) (g : Gw n w), Commute (prj V) (rhoL μ w g) := fun w g =>
    ((UpperTheory.ConvolutionTheory.Tf.innerOps E n μ).2.2.2.1 _ V hVc (IsSummandOf.inv hV)).symm
  let Good : (LL μ →L[ℂ] LL μ) → Prop := fun O => (∀ v ∈ offN μ T, O v ∈ offN μ T) ∧
    (∀ g, Commute O (rightRegularRep (rationalGLOne (K := E) (n := n)) μ (archP E n g))) ∧
    (∀ w ∉ T.marked, ∀ g, Commute O (rhoL μ w g)) ∧ (∀ v ∈ V, O v ∈ V)
  have hGone : Good 1 := ⟨fun v hv => hv, fun g => Commute.one_left _, fun w _ g => Commute.one_left _, fun v hv => hv⟩
  have hGmul : ∀ O₁ O₂, Good O₁ → Good O₂ → Good (O₁ * O₂) := fun O₁ O₂ h₁ h₂ =>
    ⟨fun v hv => h₁.1 _ (h₂.1 v hv), fun g => (h₁.2.1 g).mul_left (h₂.2.1 g),
      fun w hw g => (h₁.2.2.1 w hw g).mul_left (h₂.2.2.1 w hw g), fun v hv => h₁.2.2.2 _ (h₂.2.2.2 v hv)⟩
  have hBG : Good (List.ofFn B).prod := by
    refine List.prod_induction _ hGmul hGone fun O hO => ?_
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hO
    haveI := (hmm (T.mk' (p i)).1).1
    have hsp : p i ∈ T.sp := hp i
    have hspl : GM.Split E (p i) := (Finset.mem_filter.1 hsp).2
    have ht := (hψ i).2
    have hne : ∀ w ∉ T.marked, w ≠ (T.mk' (p i)).1 := fun w hw h => hw (Or.inr ⟨p i, hsp, h⟩)
    refine ⟨off_step μ T (B i) _ (oloc_fix μ (hBo i) _ ht) (T.triv _ hspl _) (fun w hw g => ?_),
      fun g => ?_, fun w hw g => ?_, comm_prj μ hVc _ (oloc_comm μ (hBo i) _ fun g' => hVrho _ g')⟩
    · exact (oloc_comm μ (hBo i) _ fun g' => rhoL_comm μ hw g g').symm
    · exact (oloc_comm μ (hBo i) _ fun g' => arch_comm μ g _ g').symm
    · exact (oloc_comm μ (hBo i) _ fun g' => rhoL_comm μ (hne w hw) g g').symm
  have hUG : Good (Uiw μ w₀.1 e) := by
    have hI : T.J w₀.1 = GLnLocal.iwahori (w₀.1.adicCompletion E) n := T.at_q w₀
    have hco := T.co w₀.1
    rw [hI] at hco
    have hh := UpperTheory.ConvolutionTheory.Tf.hopBasic E n μ w₀.1 (GLnLocal.iwahori _ n) (Cartan.diagPow _ n e) hco.2 hco.1
    have hne : ∀ w ∉ T.marked, w ≠ w₀.1 := fun w hw h => hw (Or.inl h)
    refine ⟨off_step μ T _ w₀.1 (fun v => ?_) (T.triv q hq w₀) (fun w hw g => ?_), fun g => ?_, fun w hw g => ?_,
      comm_prj μ hVc _ (hh.2.2.2.2.1 _ fun g' => hVrho _ g')⟩
    · rw [hI]; exact hh.2.1 v
    · exact (hh.2.2.2.2.1 _ fun g' => rhoL_comm μ hw g g').symm
    · exact (hh.2.2.2.2.1 _ fun g' => arch_comm μ g _ g').symm
    · exact (hh.2.2.2.2.1 _ fun g' => rhoL_comm μ (hne w hw) g g').symm
  have hUjG : Good (Uiw μ w₀.1 e ^ j) := by
    induction j with
    | zero => simpa using hGone
    | succ k ih => rw [pow_succ]; exact hGmul _ _ ih hUG
  have hCG : Good ((Uiw μ w₀.1 e ^ j) ∘L (List.ofFn B).prod) := hGmul _ _ hUjG hBG
  exact ⟨hCG.2.1, hCG.2.2.1, hCG.1, hCG.2.2.2⟩
end

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.TraceEigenspaceOfSelfAdjointInvariantSubspaces
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate Classical InnerProductSpace

namespace UpperTheory.RedH

section Hil
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem prj_mem_cl {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) (v : H) : v ∈ V.topologicalClosure ↔ v ∈ V := by
  rw [hV.submodule_topologicalClosure_eq]

private theorem prj_mem {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) (v : H) : prj V v ∈ V :=
  (prj_mem_cl hV _).1 (Submodule.starProjection_apply_mem _ v)

private theorem prj_self {V : Submodule ℂ H} {v : H} (hv : v ∈ V) : prj V v = v :=
  Submodule.starProjection_eq_self_iff.2 (Submodule.le_topologicalClosure V hv)

private theorem prj_adj (V : Submodule ℂ H) : ContinuousLinearMap.adjoint (prj V) = prj V :=
  (isSelfAdjoint_starProjection _).adjoint_eq

private theorem prj_comm {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) (T : H →L[ℂ] H)
    (hT : ContinuousLinearMap.adjoint T = T) (h : ∀ v ∈ V, T v ∈ V) : T * prj V = prj V * T := by
  refine ContinuousLinearMap.ext fun v => ?_
  show T (prj V v) = prj V (T v)
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ((prj_mem_cl hV _).2 (h _ (prj_mem hV v))) fun w hw => ?_
  rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right, hT]
  exact Submodule.starProjection_inner_eq_zero v _ ((prj_mem_cl hV _).2 (h w ((prj_mem_cl hV _).1 hw)))

private theorem eigIn_closed {W : Submodule ℂ H} (hW : IsClosed (W : Set H)) (A : H →L[ℂ] H) (x : ℝ) :
    IsClosed (eigIn W A x : Set H) := by
  have : (eigIn W A x : Set H) = (W : Set H) ∩ {v | A v = (x : ℂ) • v} := by
    ext v
    simp [eigIn, Module.End.mem_eigenspace_iff]
  rw [this]
  exact hW.inter (isClosed_eq A.continuous (continuous_const_smul _))

private theorem mem_eigIn {W : Submodule ℂ H} {A : H →L[ℂ] H} {x : ℝ} {v : H} :
    v ∈ eigIn W A x ↔ v ∈ W ∧ A v = (x : ℂ) • v := by
  simp [eigIn, Module.End.mem_eigenspace_iff]

private theorem prj_inf {P X : Submodule ℂ H} (hP : IsClosed (P : Set H)) (hX : IsClosed (X : Set H))
    (h : ∀ v ∈ X, prj P v ∈ X) : prj X * prj P = prj (X ⊓ P) ∧ prj P * prj X = prj (X ⊓ P) := by
  have hc := prj_comm hX (prj P) (prj_adj P) h
  have hXP : IsClosed ((X ⊓ P : Submodule ℂ H) : Set H) := by
    rw [Submodule.coe_inf]; exact hX.inter hP
  have key : prj X * prj P = prj (X ⊓ P) := by
    refine ContinuousLinearMap.ext fun v => ?_
    show prj X (prj P v) = (X ⊓ P).topologicalClosure.starProjection v
    symm
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun w hw => ?_
    · refine (prj_mem_cl hXP _).2 ⟨prj_mem hX _, ?_⟩
      have := congrArg (fun S : H →L[ℂ] H => S v) hc
      simp only [ContinuousLinearMap.mul_apply] at this
      rw [← this]
      exact prj_mem hP _
    · have hw' := (prj_mem_cl hXP _).1 hw
      have hs : ∀ (Q : Submodule ℂ H) (a b : H), ⟪prj Q a, b⟫_ℂ = ⟪a, prj Q b⟫_ℂ := fun Q a b => by
        rw [← ContinuousLinearMap.adjoint_inner_right, prj_adj]
      rw [inner_sub_left, hs, hs, prj_self hw'.1, prj_self hw'.2, sub_self]
  exact ⟨key, hc.trans key⟩

private theorem core (Ty Fx V : Submodule ℂ H) (hTy : IsClosed (Ty : Set H)) (hFx : IsClosed (Fx : Set H))
    (hV : IsClosed (V : Set H)) (hle : Ty ≤ Fx) (Oa : H →L[ℂ] H) (hOa : ContinuousLinearMap.adjoint Oa = Oa)
    (hOT : ∀ v ∈ Ty, Oa v ∈ Ty) (hOF : ∀ v ∈ Fx, Oa v ∈ Fx) (hVT : ∀ v ∈ Ty, prj V v ∈ Ty) (x : ℝ) :
    prj (eigIn V (Oa ∘L prj Fx) x) * prj Ty = prj (eigIn (V ⊓ Ty) Oa x) ∧
    prj Ty * prj (eigIn V (Oa ∘L prj Fx) x) = prj (eigIn (V ⊓ Ty) Oa x) ∧
    prj (eigIn V (Oa ∘L prj Fx) x) * (Oa ∘L prj Fx) = (x : ℂ) • prj (eigIn V (Oa ∘L prj Fx) x) := by
  set A := Oa ∘L prj Fx with hA
  set X := eigIn V A x with hXd
  have hXc : IsClosed (X : Set H) := eigIn_closed hV A x
  have hOP : Oa * prj Ty = prj Ty * Oa := prj_comm hTy Oa hOa hOT
  have hOFx : Oa * prj Fx = prj Fx * Oa := prj_comm hFx Oa hOa hOF
  have hVP : prj V * prj Ty = prj Ty * prj V := prj_comm hTy (prj V) (prj_adj V) hVT
  have hFP : prj Fx * prj Ty = prj Ty := by
    refine ContinuousLinearMap.ext fun v => ?_
    exact prj_self (hle (prj_mem hTy v))
  have hPF : prj Ty * prj Fx = prj Ty :=
    (prj_comm hFx (prj Ty) (prj_adj Ty) fun v _ => hle (prj_mem hTy v)).trans hFP
  have hAP : A * prj Ty = prj Ty * A := by
    show Oa * prj Fx * prj Ty = prj Ty * (Oa * prj Fx)
    rw [mul_assoc, hFP, hOP, ← mul_assoc, ← hOP, mul_assoc, hPF, hOP]
  have hAadj : star A = A := by
    show star (Oa * prj Fx) = Oa * prj Fx
    rw [star_mul, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint, hOa, prj_adj, hOFx]
  have heq : X ⊓ Ty = eigIn (V ⊓ Ty) Oa x := by
    ext v
    simp only [Submodule.mem_inf, mem_eigIn, hXd]
    have hA1 : v ∈ Ty → A v = Oa v := fun hv => by
      show Oa (prj Fx v) = Oa v
      rw [prj_self (hle hv)]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h3⟩, by rwa [← hA1 h3]⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩
      exact ⟨⟨h1, by rwa [hA1 h3]⟩, h3⟩
  have hPX : ∀ v ∈ X, prj Ty v ∈ X := by
    intro v hv
    obtain ⟨h1, h2⟩ := mem_eigIn.1 hv
    refine mem_eigIn.2 ⟨?_, ?_⟩
    · have := congrArg (fun S : H →L[ℂ] H => S v) hVP
      simp only [ContinuousLinearMap.mul_apply, prj_self h1] at this
      rw [← this]
      exact prj_mem hV _
    · have := congrArg (fun S : H →L[ℂ] H => S v) hAP
      simp only [ContinuousLinearMap.mul_apply] at this
      rw [this, h2, map_smul]
  obtain ⟨k1, k2⟩ := prj_inf hTy hXc hPX
  rw [heq] at k1 k2
  refine ⟨k1, k2, ?_⟩
  have hAX : A * prj X = (x : ℂ) • prj X := by
    refine ContinuousLinearMap.ext fun v => ?_
    exact (mem_eigIn.1 (prj_mem hXc v)).2
  have hsX : star (prj X) = prj X := by
    rw [ContinuousLinearMap.star_eq_adjoint, prj_adj]
  have := congrArg star hAX
  rwa [star_mul, star_smul, hAadj, hsX, RCLike.star_def, Complex.conj_ofReal] at this

private theorem isHS_prj (E : Submodule ℂ H) [FiniteDimensional ℂ E] : IsHilbertSchmidt (prj E) := by
  have hcl : E.topologicalClosure = E :=
    (Submodule.closed_of_finiteDimensional E).submodule_topologicalClosure_eq
  haveI : FiniteDimensional ℂ E.topologicalClosure := by rw [hcl]; infer_instance
  have h1 : IsHilbertSchmidt (E.topologicalClosure.subtypeL) := by
    rw [isHilbertSchmidt_iff (stdOrthonormalBasis ℂ E.topologicalClosure).toHilbertBasis, tsum_fintype]
    exact ENNReal.sum_lt_top.2 fun i _ => ENNReal.pow_lt_top enorm_lt_top
  exact h1.comp_right E.topologicalClosure.orthogonalProjection

private theorem prj_idem {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) : prj V * prj V = prj V :=
  ContinuousLinearMap.ext fun v => prj_self (prj_mem hV v)

private theorem trace_sm (c : ℂ) (S : H →L[ℂ] H) : trace (c • S) = c * trace S := by
  simp only [trace, ContinuousLinearMap.smul_apply, inner_smul_right, tsum_mul_left]

private theorem alg {R : Type} [Ring R] [Algebra ℂ R] (PX P PY A Oa U S Θ : R) (k x : ℂ)
    (h1 : PX * P = PY) (h3 : PX * A = x • PX) (h4 : U * A = A * U)
    (h5 : Oa * S = A * S) (h6 : P * (U * S) = U * S) :
    PX * ((U * ((k • (Oa * S)) * Θ)) * PX) = (k * x) • (PY * (((U * S) * Θ) * PX)) := by
  have e1 : U * ((k • (Oa * S)) * Θ) = k • (A * ((U * S) * Θ)) := by
    rw [h5, smul_mul_assoc, mul_smul_comm]
    congr 1
    simp only [← mul_assoc]
    rw [h4]
  have e2 : PX * ((U * S) * Θ) = PY * ((U * S) * Θ) := by
    rw [← h1, mul_assoc PX P, ← mul_assoc P, h6]
  rw [e1, smul_mul_assoc, mul_smul_comm, ← mul_assoc PX (A * _), ← mul_assoc PX A, h3, smul_mul_assoc,
    smul_mul_assoc, smul_smul, e2, mul_assoc PY]

end Hil

end UpperTheory.RedH

theorem UpperTheory.trace_eigenspace_of_selfAdjoint_invariant_subspaces :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Ty Fx V : Submodule ℂ H),
        IsClosed (Ty : Set H) → IsClosed (Fx : Set H) → IsClosed (V : Set H) → Ty ≤ Fx → ∀ Oa : H →L[ℂ] H,
        ContinuousLinearMap.adjoint Oa = Oa → (∀ v ∈ Ty, Oa v ∈ Ty) → (∀ v ∈ Fx, Oa v ∈ Fx) → (∀ v ∈ Ty, prj V v ∈ Ty) →
        ∀ (x : ℝ) (κ : ℂ) (U S Θ : H →L[ℂ] H), FiniteDimensional ℂ ↥(eigIn (V ⊓ Ty) Oa x) →
          Commute U (Oa ∘L prj Fx) → (∀ v, S v ∈ Ty) → (∀ v, U (S v) ∈ Ty) →
          trOn (eigIn V (Oa ∘L prj Fx) x) (U ∘L (κ • (Oa ∘L S)) ∘L Θ) = (κ * x) * trOn (eigIn (V ⊓ Ty) Oa x) (U ∘L S ∘L Θ) := by
  intro H _ _ _ Ty Fx V hTy hFx hV hle Oa hOa hOT hOF hVT x κ U S Θ hfin hUA hS hUS
  obtain ⟨k1, k2, k3⟩ := UpperTheory.RedH.core Ty Fx V hTy hFx hV hle Oa hOa hOT hOF hVT x
  set PX := prj (eigIn V (Oa ∘L prj Fx) x) with hPX
  set PY := prj (eigIn (V ⊓ Ty) Oa x) with hPY
  have hXc : IsClosed ((eigIn V (Oa ∘L prj Fx) x : Submodule ℂ H) : Set H) := UpperTheory.RedH.eigIn_closed hV _ x
  have hXX : PX * PX = PX := UpperTheory.RedH.prj_idem hXc
  have hXY : PX * PY = PY := by rw [← k1, ← mul_assoc, hXX]
  have hYc : IsClosed ((eigIn (V ⊓ Ty) Oa x : Submodule ℂ H) : Set H) :=
    Submodule.closed_of_finiteDimensional _
  have hYY : PY * PY = PY := UpperTheory.RedH.prj_idem hYc
  have hHS : IsHilbertSchmidt PY := UpperTheory.RedH.isHS_prj _
  have hTC : IsTraceClass PY := by
    have h := isTraceClass_comp hHS hHS
    have e : PY ∘L PY = PY := hYY
    rwa [e] at h
  have hal := UpperTheory.RedH.alg PX (prj Ty) PY (Oa ∘L prj Fx) Oa U S Θ κ (x : ℂ) k1 k3 hUA.eq
    (by
      refine ContinuousLinearMap.ext fun v => ?_
      show Oa (S v) = Oa (prj Fx (S v))
      rw [UpperTheory.RedH.prj_self (hle (hS v))])
    (by
      refine ContinuousLinearMap.ext fun v => ?_
      exact UpperTheory.RedH.prj_self (hUS v))
  set D : H →L[ℂ] H := (U * S) * Θ with hD
  have t1 : trace (PY * (D * PX)) = trace (D * PY) := by
    have h := trace_comp_comm hTC (D * PX)
    have e1 : (D * PX) ∘L PY = D * PY := by
      show (D * PX) * PY = D * PY
      rw [mul_assoc, hXY]
    rw [e1] at h
    exact h.symm
  have t2 : trace (PY * (D * PY)) = trace (D * PY) := by
    have h := trace_comp_comm hTC (D * PY)
    have e1 : (D * PY) ∘L PY = D * PY := by
      show (D * PY) * PY = D * PY
      rw [mul_assoc, hYY]
    rw [e1] at h
    exact h.symm
  unfold trOn
  rw [← hPX, ← hPY]
  have g1 : PX ∘L (U ∘L (κ • (Oa ∘L S)) ∘L Θ) ∘L PX = (κ * x) • (PY * (D * PX)) := hal
  have g2 : PY ∘L (U ∘L S ∘L Θ) ∘L PY = PY * (D * PY) := by
    show PY * ((U * (S * Θ)) * PY) = PY * (D * PY)
    simp only [hD, mul_assoc]
  rw [g1, g2, UpperTheory.RedH.trace_sm, t1, t2]
end
