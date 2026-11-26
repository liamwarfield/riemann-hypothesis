module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocHeckeInert
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.UiwPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwDomMul

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.LocUApply
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SfDefs
noncomputable section

open GroundTheory.Automorphic
open scoped InnerProductSpace

namespace UpperTheory.ConvolutionTheory.C.Sf

variable {G : Type} [Group G] [TopologicalSpace G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {S : Type} [AddCommGroup S] [Module ℂ S]

def fixU (π : UnitaryRep G H) (U : Subgroup G) : Submodule ℂ H where
  carrier := {v | ∀ u ∈ U, π u v = v}
  add_mem' {a b} ha hb u hu := by rw [map_add (f := _), ha u hu, hb u hu]
  zero_mem' u _ := map_zero _
  smul_mem' c v hv u hu := by rw [map_smul, hv u hu]

theorem mem_fixU {π : UnitaryRep G H} {U : Subgroup G} {v : H} : v ∈ fixU π U ↔ ∀ u ∈ U, π u v = v := Iff.rfl

theorem isClosed_fixU (π : UnitaryRep G H) (U : Subgroup G) : IsClosed (fixU π U : Set H) := by
  have : (fixU π U : Set H) = ⋂ u ∈ U, {v | π u v = v} := by
    ext v
    simp [mem_fixU]
  rw [this]
  exact isClosed_biInter fun u _ => isClosed_eq (π u).continuous continuous_id

structure Eqv (τ : Representation ℂ G S) (π : UnitaryRep G H) (D : Submodule ℂ H) (f : S →ₗ[ℂ] H) : Prop where
  mem : ∀ x, f x ∈ D
  map : ∀ g x, f (τ g x) = π g (f x)

def spanAll (τ : Representation ℂ G S) (π : UnitaryRep G H) (D : Submodule ℂ H) : Submodule ℂ H :=
  Submodule.span ℂ {y | ∃ f, Eqv τ π D f ∧ ∃ x, y = f x}

def spanFix (τ : Representation ℂ G S) (π : UnitaryRep G H) (D : Submodule ℂ H) (U : Subgroup G) : Submodule ℂ H :=
  Submodule.span ℂ {y | ∃ f, Eqv τ π D f ∧ ∃ x ∈ fixedVectors τ U, y = f x}

def IsOp [MeasurableSpace G] (π : UnitaryRep G H) (m : MeasureTheory.Measure G) (φ : G → ℂ) (T : H →L[ℂ] H) : Prop :=
  ∀ u v : H, ⟪u, T v⟫_ℂ = ∫ g, φ g * ⟪u, π g v⟫_ℂ ∂m

end UpperTheory.ConvolutionTheory.C.Sf
end
end

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

namespace UpperTheory.ConvolutionTheory.C.Sf

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def locU (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (w : Pl K) : UnitaryRep (Gw n w) (LL μ) :=
  (rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom ((MultiplicityOne.finProj K n).comp (AdelicGLn.localEmbedding w))
    (MultiplicityOne.continuous_finProj.comp (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).1)

theorem locU_apply (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (w : Pl K) (g : Gw n w) : locU μ w g = rhoL μ w g := rfl

theorem fixU_locU (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (w : Pl K) (J : Subgroup (Gw n w)) :
    fixU (locU μ w) J = fixL μ w J := by
  ext v
  simp only [mem_fixU, fixL, fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe, LinearMap.id_apply]
  constructor
  · rintro h _ ⟨u, hu, rfl⟩
    exact h u hu
  · intro h u hu
    exact h _ (Subgroup.mem_map_of_mem _ hu)

end UpperTheory.ConvolutionTheory.C.Sf
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OfinProd
noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory.GM
open scoped Classical

namespace UpperTheory.ConvolutionTheory.C

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def sphOff (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (P : Finset (Pl K)) : Submodule ℂ (LL μ) :=
  ⨅ v ∉ P, fixL μ v (GLnLocal.integralGL (v.adicCompletion K) n)

def levOn (P : Finset (Pl K)) (U : ∀ v : Pl K, Subgroup (Gw n v)) : Subgroup (AdelicGLn.FiniteAdelicGL K n) :=
  levF fun v => if v ∈ P then U v else GLnLocal.integralGL (v.adicCompletion K) n

def FixLev : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (P : Finset (Pl K))
    (U : ∀ v : Pl K, Subgroup (Gw n v)), fixF μ (levOn P U) = sphOff μ P ⊓ ⨅ v ∈ P, fixL μ v (U v)

def OfinProd : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (mf : Measure (AdelicGLn.FiniteAdelicGL K n)) [mf.IsHaarMeasure], mf (AdelicGLn.integralFiniteGL K n) = 1 →
    ∀ (r : ℕ) (w : Fin r → Pl K) [∀ i, MeasurableSpace (Gw n (w i))] [∀ i, BorelSpace (Gw n (w i))]
      (m : ∀ i, Measure (Gw n (w i))) (φ : ∀ i, Gw n (w i) → ℂ) (T : Fin r → LL μ →L[ℂ] LL μ) (e : TF K n),
      Function.Injective w → (∀ i, (m i).IsHaarMeasure ∧ m i (GLnLocal.integralGL ((w i).adicCompletion K) n) = 1) →
      (∀ i, Test (φ i)) → (∀ i, IsOloc μ (w i) (m i) (φ i) (T i)) →
      (∀ x, e x = if ∀ v ∉ Finset.univ.image w, finAt v (finEmb K n x) ∈ GLnLocal.integralGL (v.adicCompletion K) n then
        ∏ i, φ i (finAt (w i) (finEmb K n x)) else 0) →
      Ofin μ mf e = (List.ofFn T).prod ∘L prj (sphOff μ (Finset.univ.image w))

def EigAdm : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (a : TI K n) (x : ℝ), x ≠ 0 → ∀ (P : Finset (Pl K))
    (U : ∀ v : Pl K, Subgroup (Gw n v)), (∀ v ∈ P, CO (U v)) →
    FiniteDimensional ℂ ↥(eigIn (cuspidalL2 μ) (Oinf μ ν a) x ⊓ sphOff μ P ⊓ ⨅ v ∈ P, fixL μ v (U v))

def TermF : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex F] (σ : E ≃ₐ[F] E)
    (n l : ℕ), 0 < n → ∀ (μ : Measure (normOneGL (K := F) (n := n))) [μ.IsHaarMeasure] (ν : Measure (archGroup F n)) [ν.IsHaarMeasure]
    [∀ v : Pl F, MeasurableSpace (Gw n v)] [∀ v : Pl F, BorelSpace (Gw n v)] (m : ∀ v : Pl F, Measure (Gw n v)),
    (∀ v, (m v).IsHaarMeasure ∧ m v (GLnLocal.integralGL (v.adicCompletion F) n) = 1) →
    ∃ κ : ℝ, 0 < κ ∧ ∀ (a : TI F n) (q : Pl F) (w₀ : PlacesOver E q) (S : Finset (Pl F)) (V : Submodule ℂ (LL μ))
      (τ : ∀ v : Pl F, SmIrr (Gw n v)) (x : ℝ), IsSummand μ V → 0 < x → (∀ v ∈ insert q S, Occurs μ V v (τ v)) →
      ∃ N : ℕ, (0 < N ↔ eigIn V (Oinf μ ν a) x ⊓ sphOff μ (insert q S) ≠ ⊥) ∧
        ∀ (L : Loc σ n q w₀) (e : Fin n → ℤ) (𝔣 : Side (Twist.id μ) l), L.S = S → Antitone e → IsSideF L ν a e 𝔣 →
        ∀ (j : ℕ) (sq : ℂ) (s : Pl F → ℂ), HasTrace (m q) (τ q).ρ ((iwCoset q (j • e)).indicator 1) sq →
          (∀ v ∈ S, HasTrace (m v) (τ v).ρ (L.f v) (s v)) →
          trOn (eigIn V 𝔣.toAmp.A x) ((𝔣.Uq 0 ^ j) ∘L Rop μ 𝔣.g ∘L (Twist.id μ).U) = κ * x * N * sq * ∏ v ∈ S, s v

end UpperTheory.ConvolutionTheory.C
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OlocEx
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped InnerProductSpace

theorem UpperTheory.ConvolutionTheory.C.olocEx :
    UpperTheory.ConvolutionTheory.C.OlocEx := by
  intro K _ _ n μ _ w _ _ m _ φ hφ
  have hL : MemLp φ 1 m := hφ.1.continuous.memLp_of_hasCompactSupport hφ.2
  let π : UnitaryRep (Gw n w) (LL μ) := (rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom
    ((MultiplicityOne.finProj K n).comp (AdelicGLn.localEmbedding w))
    (MultiplicityOne.continuous_finProj.comp (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).1)
  refine ⟨π.integrated m hL.toLp, fun u v => ?_, fun T hT => ?_⟩
  · have hπ : ∀ g, π g v = rhoL μ w g v := fun _ => rfl
    rw [UnitaryRep.inner_integrated]
    refine integral_congr_ae ((MemLp.coeFn_toLp hL).mono fun g hg => ?_)
    simp only [hπ]
    rw [hg]
  · refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_
    rw [hT u v, UnitaryRep.inner_integrated]
    have hπ : ∀ g, π g v = rhoL μ w g v := fun _ => rfl
    refine integral_congr_ae ((MemLp.coeFn_toLp hL).mono fun g hg => ?_)
    simp only [hπ]
    rw [hg]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.HopOloc
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

open scoped InnerProductSpace

namespace UpperTheory.ConvolutionTheory.C.HopfExpansion

section
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem setInt_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (m : Measure G) [m.IsMulLeftInvariant]
    (f : G → E) (y : G) {S T : Set G} (hS : MeasurableSet S) (hT : MeasurableSet T) (h : ∀ x, x ∈ S ↔ y * x ∈ T) :
    ∫ x in S, f (y * x) ∂m = ∫ x in T, f x ∂m := by
  rw [← integral_indicator hS, ← integral_indicator hT, ← integral_mul_left_eq_self (T.indicator f) y]
  congr 1
  ext x
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((h x).1 hx)]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx ((h x).2 h'))]

private theorem avg (π : UnitaryRep G H) (m : Measure G) [m.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts m]
    (J : Subgroup G) (hJ : IsCompact (J : Set G)) (hJo : IsOpen (J : Set G)) (hm : m J = 1)
    (W : Submodule ℂ H) (hW : ∀ v, v ∈ W ↔ ∀ j ∈ J, π j v = v) (u v : H) :
    ∫ j in (J : Set G), ⟪u, π j v⟫_ℂ ∂m = ⟪u, prj W v⟫_ℂ := by
  have hmeas : MeasurableSet (J : Set G) := hJo.measurableSet
  have hint : IntegrableOn (fun j => π j v) (J : Set G) m :=
    (π.continuous_orbit v).continuousOn.integrableOn_compact' hJ hmeas
  have hcl : IsClosed (W : Set H) := by
    have : (W : Set H) = ⋂ j ∈ J, {v | π j v = v} := by
      ext v
      simp [hW]
    rw [this]
    exact isClosed_biInter fun j _ => isClosed_eq (π j).continuous continuous_id
  have hA : (∫ j in (J : Set G), π j v ∂m) ∈ W := by
    rw [hW]
    intro j₀ hj₀
    rw [← ContinuousLinearMap.integral_comp_comm _ hint]
    have := setInt_shift m (fun j => π j v) j₀ hmeas hmeas (fun x => by
      simp [Subgroup.mul_mem_cancel_left J hj₀])
    simpa [UnitaryRep.map_mul_apply] using this
  have hin : ∀ w ∈ W, ⟪w, ∫ j in (J : Set G), π j v ∂m⟫_ℂ = ⟪w, v⟫_ℂ := by
    intro w hw
    rw [← integral_inner hint w]
    have : ∀ j ∈ (J : Set G), ⟪w, π j v⟫_ℂ = ⟪w, v⟫_ℂ := by
      intro j hj
      rw [UnitaryRep.inner_map_right, (hW w).1 hw _ (J.inv_mem hj)]
    rw [setIntegral_congr_fun hmeas this]
    simp [Measure.real, hm]
  have hP : prj W v = ∫ j in (J : Set G), π j v ∂m := by
    change W.topologicalClosure.starProjection v = _
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.le_topologicalClosure _ hA) ?_
    intro w hw
    rw [hcl.submodule_topologicalClosure_eq] at hw
    rw [inner_sub_left, ← inner_conj_symm, ← inner_conj_symm _ w, hin w hw]
    simp
  rw [hP, integral_inner hint u]

private theorem main (π : UnitaryRep G H) (m : Measure G) [m.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts m]
    (J : Subgroup G) (hJ : IsCompact (J : Set G)) (hJo : IsOpen (J : Set G)) (hm : m J = 1)
    (W : Submodule ℂ H) (hW : ∀ v, v ∈ W ↔ ∀ j ∈ J, π j v = v) (x : G) (u v : H) :
    ⟪u, (∑ᶠ c ∈ {c : G ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * x)}, π c.out) (prj W v)⟫_ℂ =
      ∫ g, Set.indicator {g | ∃ a ∈ J, ∃ b ∈ J, g = a * x * b} 1 g * ⟪u, π g v⟫_ℂ ∂m := by
  haveI : DiscreteTopology (G ⧸ J) := QuotientGroup.discreteTopology hJo
  set S : Set (G ⧸ J) := {c | ∃ k ∈ J, c = QuotientGroup.mk (k * x)} with hSdef
  have hSfin : S.Finite := by
    have e : S = (fun k : G => (QuotientGroup.mk (k * x) : G ⧸ J)) '' (J : Set G) := by
      ext c
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact ⟨k, hk, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨k, hk, rfl⟩
    rw [e]
    exact (hJ.image (QuotientGroup.continuous_mk.comp (continuous_id.mul continuous_const))).finite_of_discrete
  set D : Set G := {g | ∃ a ∈ J, ∃ b ∈ J, g = a * x * b} with hDdef
  let P : G ⧸ J → Set G := fun c => QuotientGroup.mk ⁻¹' {c}
  have hPo : ∀ c, IsOpen (P c) := fun c => (isOpen_discrete {c}).preimage QuotientGroup.continuous_mk
  have hPmem : ∀ (c : G ⧸ J) (h : G), h ∈ (J : Set G) ↔ c.out * h ∈ P c := by
    intro c h
    have : (QuotientGroup.mk (c.out * h) : G ⧸ J) = c ↔ h ∈ J := by
      conv_lhs => rhs; rw [← QuotientGroup.out_eq' c]
      rw [QuotientGroup.eq]
      simp
    exact this.symm
  have hD : D = ⋃ c ∈ hSfin.toFinset, P c := by
    ext g
    simp only [Set.mem_iUnion, Set.Finite.mem_toFinset, exists_prop]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      refine ⟨QuotientGroup.mk (a * x), ⟨a, ha, rfl⟩, ?_⟩
      change (QuotientGroup.mk (a * x * b) : G ⧸ J) = QuotientGroup.mk (a * x)
      rw [QuotientGroup.eq]
      simpa [mul_assoc] using J.inv_mem hb
    · rintro ⟨c, ⟨k, hk, rfl⟩, hg⟩
      have hg' : (QuotientGroup.mk g : G ⧸ J) = QuotientGroup.mk (k * x) := hg
      have := QuotientGroup.eq.1 hg'.symm
      exact ⟨k, hk, _, this, by group⟩
  have hDm : MeasurableSet D := by
    rw [hD]
    exact Finset.measurableSet_biUnion _ fun c _ => (hPo c).measurableSet
  have hcont : Continuous fun g => ⟪u, π g v⟫_ℂ := continuous_const.inner (π.continuous_orbit v)
  have hPint : ∀ c, IntegrableOn (fun g => ⟪u, π g v⟫_ℂ) (P c) m := by
    intro c
    have e : P c = (fun h => c.out * h) '' (J : Set G) := by
      ext g
      constructor
      · intro hg
        refine ⟨c.out⁻¹ * g, (hPmem c _).2 (by simpa using hg), by simp⟩
      · rintro ⟨h, hh, rfl⟩
        exact (hPmem c h).1 hh
    have hc : IsCompact (P c) := by
      rw [e]
      exact hJ.image (continuous_const.mul continuous_id)
    exact hcont.continuousOn.integrableOn_compact' hc (hPo c).measurableSet
  have hind : (fun g => D.indicator (1 : G → ℂ) g * ⟪u, π g v⟫_ℂ) = D.indicator fun g => ⟪u, π g v⟫_ℂ := by
    ext g
    by_cases hg : g ∈ D <;> simp [hg]
  rw [hind, integral_indicator hDm, hD, integral_biUnion_finset _ (fun c _ => (hPo c).measurableSet) ?_
    (fun c _ => hPint c), finsum_mem_eq_finite_toFinset_sum _ hSfin, ContinuousLinearMap.sum_apply, inner_sum]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [← setInt_shift m (fun g => ⟪u, π g v⟫_ℂ) c.out hJo.measurableSet (hPo c).measurableSet (hPmem c)]
    rw [UnitaryRep.inner_map_right, ← avg π m J hJ hJo hm W hW]
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    simp only [UnitaryRep.map_mul_apply]
    exact (UnitaryRep.inner_map_right π _ _ _).symm
  · intro c _ d _ hcd
    refine Set.disjoint_left.2 fun g hg hg' => hcd ?_
    exact (hg : _ = c).symm.trans hg'

end
end UpperTheory.ConvolutionTheory.C.HopfExpansion

theorem UpperTheory.ConvolutionTheory.C.hopOloc :
    UpperTheory.ConvolutionTheory.C.HopOloc := by
  intro K _ _ n μ _ w _ _ m _ J x hJ hm u v
  let φ : Gw n w →* normOneGL (K := K) (n := n) := (MultiplicityOne.finProj K n).comp (AdelicGLn.localEmbedding w)
  have hφ : Continuous φ := MultiplicityOne.continuous_finProj.comp (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).1
  let π : UnitaryRep (Gw n w) (LL μ) := (rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom φ hφ
  have hπ : ∀ x, π x = rhoL μ w x := fun _ => rfl
  have hW : ∀ v, v ∈ fixL μ w J ↔ ∀ j ∈ J, π j v = v := by
    intro v
    simp only [fixL, fixF, Submodule.mem_iInf, LinearMap.mem_eqLocus, Subgroup.mem_map]
    constructor
    · intro h j hj
      simpa [hπ, rhoL] using h _ ⟨j, hj, rfl⟩
    · rintro h _ ⟨j, hj, rfl⟩
      simpa [hπ, rhoL] using h j hj
  exact HopfExpansion.main π m J hJ.1 hJ.2 hm (fixL μ w J) hW x u v
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.UiwPow
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

private theorem prj_prj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : Submodule ℂ H) : prj V ∘L prj V = prj V := by
  ext v
  simp only [prj, ContinuousLinearMap.comp_apply]
  exact Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)

private theorem rhoL_prj {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K))) {k : GL (Fin n) (w.adicCompletion K)} (hk : k ∈ J) :
    rhoL μ w k ∘L prj (fixL μ w J) = prj (fixL μ w J) := by
  ext1 v
  have hle : (fixL μ w J).topologicalClosure ≤
      LinearMap.eqLocus (rhoL μ w k : LL μ →ₗ[ℂ] LL μ) LinearMap.id := by
    apply Submodule.topologicalClosure_minimal
    · unfold fixL fixF rhoL
      exact iInf₂_le (AdelicGLn.localEmbedding w k) (Subgroup.mem_map_of_mem _ hk)
    · exact isClosed_eq (rhoL μ w k).continuous continuous_id
  exact hle (Submodule.starProjection_apply_mem _ v)

private theorem hop_one {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K))) : Hop μ w J 1 = prj (fixL μ w J) := by
  have hs : {c : GL (Fin n) (w.adicCompletion K) ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * 1)} =
      {QuotientGroup.mk 1} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, mul_one]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact QuotientGroup.eq.mpr (by simpa using hk)
    · rintro rfl
      exact ⟨1, J.one_mem, rfl⟩
  unfold Hop
  rw [hs, finsum_mem_singleton]
  apply rhoL_prj
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul J (1 : GL (Fin n) (w.adicCompletion K))
  rw [hh, one_mul]
  exact h.2

theorem UpperTheory.ConvolutionTheory.C.uiwPow :
    UpperTheory.ConvolutionTheory.C.UiwPow := by
  intro K _ _ n μ _ w ν hν j
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [pow_zero, zero_smul, Uiw, GroundTheory.Automorphic.Parabolic.diagPow_zero, hop_one]
    rfl
  · rw [(UpperTheory.ConvolutionTheory.Tf.uiwPow K n μ w ν ν hν hν).2.1 j hj, Uiw, Hop, ContinuousLinearMap.comp_assoc, prj_prj]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.PowIndep
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

private lemma powSum_eq_count (s : Multiset ℂ) (S : Finset ℂ) (h : ∀ z ∈ s, z ∈ S) (j : ℕ) :
    (s.map (· ^ j)).sum = ∑ z ∈ S, (s.count z : ℂ) * z ^ j := by
  classical
  rw [Finset.sum_multiset_map_count]
  have hsub : s.toFinset ⊆ S := fun z hz => h z (Multiset.mem_toFinset.1 hz)
  rw [← Finset.sum_subset hsub]
  · exact Finset.sum_congr rfl fun z _ => by simp [nsmul_eq_mul]
  · intro z _ hz
    have : s.count z = 0 := Multiset.count_eq_zero.2 fun hm => hz (Multiset.mem_toFinset.2 hm)
    simp [this]

private def powHom (z : ℂ) : Multiplicative ℕ →* ℂ where
  toFun n := z ^ n.toAdd
  map_one' := by simp
  map_mul' a b := by simp [pow_add]

private lemma powHom_injective : Function.Injective powHom := by
  intro a b h
  have := DFunLike.congr_fun h (Multiplicative.ofAdd 1)
  simpa [powHom] using this

theorem UpperTheory.ConvolutionTheory.C.powIndep :
    UpperTheory.ConvolutionTheory.C.PowIndep := by
  classical
  intro ι _ c Z hZ hev ζ
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  let S : Finset ℂ := Finset.univ.biUnion fun i => (Z i).toFinset
  let a : ℂ → ℂ := fun z => ∑ i, c i * ((Z i).count z : ℂ)
  have hmem : ∀ i, ∀ z ∈ Z i, z ∈ S := fun i z hz =>
    Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, Multiset.mem_toFinset.2 hz⟩
  have key : ∀ j, N ≤ j → ∑ z ∈ S, a z * z ^ j = 0 := by
    intro j hj
    have h0 := hN j hj
    simp only [powSum_eq_count _ S (hmem _) j, Finset.mul_sum] at h0
    rw [Finset.sum_comm] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [a, Finset.sum_mul, mul_assoc]
  have hne : ∀ z ∈ S, z ≠ 0 := by
    intro z hz h0
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hz
    exact hZ i (h0 ▸ Multiset.mem_toFinset.1 hi)
  have lin : LinearIndependent ℂ (fun z : S => (powHom z : Multiplicative ℕ → ℂ)) :=
    (linearIndependent_monoidHom (Multiplicative ℕ) ℂ).comp (fun z : S => powHom z)
      (powHom_injective.comp Subtype.val_injective)
  rw [Fintype.linearIndependent_iff] at lin
  have hb := lin (fun z => a z * (z : ℂ) ^ N) (by
    funext n
    have := key (N + n.toAdd) (Nat.le_add_right _ _)
    rw [← Finset.sum_coe_sort S] at this
    simpa [powHom, pow_add, mul_assoc, Finset.sum_apply] using this)
  have ha : a ζ = 0 := by
    by_cases hζ : ζ ∈ S
    · have := hb ⟨ζ, hζ⟩
      exact (mul_eq_zero.1 this).resolve_right (pow_ne_zero _ (hne ζ hζ))
    · refine Finset.sum_eq_zero fun i _ => ?_
      have : (Z i).count ζ = 0 := Multiset.count_eq_zero.2 fun hm => hζ (hmem i ζ hm)
      simp [this]
  rw [← ha]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  rw [Multiset.filter_eq', Multiset.card_replicate]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.ExistsPowerSums
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

section Abs

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [AddCommGroup V] [Module ℂ V]

private theorem mem_orbit_iff (I : Subgroup G) (x g : G) :
    (g : G ⧸ I) ∈ MulAction.orbit I (x : G ⧸ I) ↔ ∃ a ∈ I, ∃ b ∈ I, g = a * x * b := by
  constructor
  · rintro ⟨a, ha⟩
    have ha' : (((a : G) * x : G) : G ⧸ I) = g := ha
    exact ⟨a, a.2, _, QuotientGroup.eq.1 ha', by group⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    change ((a * x : G) : G ⧸ I) = _
    exact (QuotientGroup.mk_mul_of_mem _ hb).symm

private theorem hk_sum (ρ : Representation ℂ G V) (I : Subgroup G) (x : G)
    (h : (MulAction.orbit I (x : G ⧸ I)).Finite) (v : UpperTheory.V.Hi.fixd ρ I) :
    (UpperTheory.V.AlgebraTools.hk ρ I x v : V) = ∑ q ∈ Set.Finite.toFinset h, ρ q.out v := by
  rw [UpperTheory.V.AlgebraTools.hk, (UpperTheory.V.AlgebraTools.hkApply ℂ G V ρ I I x h).1 v, UpperTheory.V.Hi.dc,
    finsum_set_coe_eq_finsum_mem (f := fun q : G ⧸ I => ρ q.out), finsum_mem_eq_finite_toFinset_sum _ h,
    LinearMap.sum_apply]

private theorem hasTrace_hk (m : Measure G) [IsFiniteMeasureOnCompacts m] [m.IsMulLeftInvariant]
    {ρ : Representation ℂ G V} (hρ : GlobalTheory.PRep.IsSmooth ρ) {I : Subgroup G} (hIo : IsOpen (I : Set G))
    (hIc : IsCompact (I : Set G)) (hm : m I = 1) (x : G) (hx : UpperTheory.V.AlgebraTools.FinOrb I I x)
    [FiniteDimensional ℂ (UpperTheory.V.Hi.fixd ρ I)] :
    HasTrace m ρ (Set.indicator {g | ∃ a ∈ I, ∃ b ∈ I, g = a * x * b} 1)
      (LinearMap.trace ℂ _ (UpperTheory.V.AlgebraTools.hk ρ I x)) := by
  classical
  have hx' : (MulAction.orbit I (x : G ⧸ I)).Finite := hx
  set D : Set G := {g | ∃ a ∈ I, ∃ b ∈ I, g = a * x * b} with hD
  let C : G ⧸ I → Set G := fun q => (fun g => q.out⁻¹ * g) ⁻¹' (I : Set G)
  have hC : ∀ q g, g ∈ C q ↔ (g : G ⧸ I) = q := fun q g => by
    show q.out⁻¹ * g ∈ I ↔ _
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    exact eq_comm
  have hCo : ∀ q, IsOpen (C q) := fun q => hIo.preimage (continuous_const.mul continuous_id)
  have hCc : ∀ q, IsCompact (C q) := fun q => (Homeomorph.mulLeft q.out⁻¹).isCompact_preimage.2 hIc
  have hCm : ∀ q, m (C q) = 1 := fun q => by rw [← hm]; exact measure_preimage_mul m _ _
  have hU : D = ⋃ q ∈ Set.Finite.toFinset hx', C q := by
    ext g
    simp only [Set.mem_iUnion, Set.Finite.mem_toFinset, hC, exists_prop, exists_eq_right']
    exact (mem_orbit_iff I x g).symm
  have hDc : IsCompact D := by
    rw [hU]
    exact (Set.Finite.toFinset hx').isCompact_biUnion fun q _ => hCc q
  have hDm : MeasurableSet D := by
    rw [hU]
    exact Finset.measurableSet_biUnion _ fun q _ => (hCo q).measurableSet
  have hI : ∀ a ∈ I, ∀ g ∈ D, a * g ∈ D := by
    rintro a ha _ ⟨b, hb, c, hc, rfl⟩
    exact ⟨_, mul_mem ha hb, c, hc, by simp only [mul_assoc]⟩
  obtain ⟨A, hA⟩ := GlobalTheory.IwahoriTraceProof.exists_setOp m hρ hDc hDm
  have e : ∀ φ : G → ℂ, (fun g => D.indicator (1 : G → ℂ) g * φ g) = D.indicator φ := fun φ => by
    funext g
    by_cases h : g ∈ D <;> simp [h]
  have hfix : ∀ v, A v ∈ UpperTheory.V.Hi.fixd ρ I := fun v a ha => by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, sub_eq_zero, (hA v l).2]
    refine (hA v (l ∘ₗ ρ a)).2.trans ?_
    rw [← integral_indicator hDm, ← integral_indicator hDm,
      ← integral_mul_left_eq_self (D.indicator fun g => l (ρ g v)) a]
    congr 1
    funext g
    by_cases h : g ∈ D
    · simp [h, hI a ha g h]
    · have : a * g ∉ D := fun h' => h (by simpa using hI _ (inv_mem ha) _ h')
      simp [h, this]
  have hres : ∀ w : UpperTheory.V.Hi.fixd ρ I, A w = UpperTheory.V.AlgebraTools.hk ρ I x w := fun w => by
    rw [hk_sum ρ I x hx', ← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, sub_eq_zero, (hA w l).2, map_sum]
    have hsub : ∀ q ∈ Set.Finite.toFinset hx', C q ⊆ D := fun q hq => by
      rw [hU]
      exact Set.subset_biUnion_of_mem (u := C) hq
    conv_lhs => rw [hU]
    rw [integral_biUnion_finset _ (fun q _ => (hCo q).measurableSet)
      (fun p _ q _ hpq => Set.disjoint_left.2 fun g hp hq => hpq (((hC p g).1 hp).symm.trans ((hC q g).1 hq)))
      (fun q hq => (hA w l).1.mono_set (hsub q hq))]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hconst : ∀ g ∈ C q, l (ρ g w) = l (ρ q.out w) := fun g hg => by
      have h1 : q.out⁻¹ * g ∈ I := hg
      have h2 : g = q.out * (q.out⁻¹ * g) := by group
      rw [h2, map_mul, Module.End.mul_apply, w.2 _ h1]
    rw [setIntegral_congr_fun (hCo q).measurableSet hconst, setIntegral_const, measureReal_def, hCm]
    simp
  have hle : LinearMap.range A ≤ UpperTheory.V.Hi.fixd ρ I := by
    rintro _ ⟨v, rfl⟩
    exact hfix v
  refine ⟨A, fun v l => ?_, Submodule.finiteDimensional_of_le hle, ?_⟩
  · rw [e, integral_indicator hDm, integrable_indicator_iff hDm]
    exact hA v l
  haveI := Submodule.finiteDimensional_of_le hle
  let j := Submodule.inclusion hle
  let s : UpperTheory.V.Hi.fixd ρ I →ₗ[ℂ] LinearMap.range A := A.rangeRestrict ∘ₗ (UpperTheory.V.Hi.fixd ρ I).subtype
  have h1 : UpperTheory.V.AlgebraTools.hk ρ I x = j ∘ₗ s := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    exact (hres w).symm
  have h2 : A.restrict (p := LinearMap.range A) (q := LinearMap.range A)
      (fun v _ => LinearMap.mem_range_self A v) = s ∘ₗ j := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    rfl
  rw [h1, h2]
  exact (LinearMap.trace_comp_comm' s j).symm

end Abs

section Eig

private theorem exists_powerSums {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (T : Module.End ℂ W) (hT : IsUnit T) :
    ∃ Z : Multiset ℂ, 0 ∉ Z ∧ Z.card = Module.finrank ℂ W ∧
      ∀ j : ℕ, LinearMap.trace ℂ W (T ^ j) = (Z.map (· ^ j)).sum := by
  obtain ⟨u, rfl⟩ := hT
  let R : Representation ℂ (Multiplicative ℤ) W := (Units.coeHom _).comp (zpowersHom _ u)
  obtain ⟨E, -, hE⟩ := GlobalTheory.IwahoriTraceProof.exists_exponents (G := Multiplicative ℤ) _ W R rfl
  have hR : ∀ j : ℕ, R (Multiplicative.ofAdd 1 ^ j) = (u : Module.End ℂ W) ^ j := fun j => by
    rw [map_pow]
    congr 1
  refine ⟨E.map fun χ => ((χ (Multiplicative.ofAdd 1) : ℂˣ) : ℂ), ?_, ?_, fun j => ?_⟩
  · intro h
    obtain ⟨χ, -, h⟩ := Multiset.mem_map.1 h
    exact (χ (Multiplicative.ofAdd 1)).ne_zero h
  · have h1 := hE 1
    rw [map_one, Module.End.one_eq_id, LinearMap.trace_id] at h1
    have h2 : (Module.finrank ℂ W : ℂ) = (E.card : ℂ) := by
      rw [h1]
      simp
    rw [Multiset.card_map]
    exact (Nat.cast_injective h2).symm
  · rw [← hR, hE, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun χ _ => ?_
    simp

end Eig

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}

private theorem dom_pow (a : Fin n → ℤ) (ha : Antitone a) (h0 : (GLnLocal.uniformizer F : F) ≠ 0) :
    UpperTheory.V.AlgebraTools.Dom fun i => (Units.mk0 (GLnLocal.uniformizer F : F) h0) ^ a i := by
  intro i j hij
  have hp : 0 < ValuativeRel.valuation F (GLnLocal.uniformizer F : F) := GLnLocal.valuation_uniformizer_pos F
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀, Units.val_mk0]
  exact (zpow_le_zpow_iff_right_of_lt_one₀ hp (GLnLocal.valuation_uniformizer_lt_one F)).2 (ha hij)

private theorem iw_local [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
    (m : Measure (GL (Fin n) F)) [m.IsHaarMeasure] {I : Subgroup (GL (Fin n) F)}
    (hI : UpperTheory.V.AlgebraTools.iwC F n ⊤ = I) (hm : m I = 1) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) F) V) (hρ : GlobalTheory.PRep.IsSmooth ρ) (hIo : IsOpen (I : Set (GL (Fin n) F)))
    (hIc : IsCompact (I : Set (GL (Fin n) F))) (ν : Fin n → ℤ) (hν : Antitone ν)
    [FiniteDimensional ℂ (UpperTheory.V.Hi.fixd ρ I)] :
    ∃ Z : Multiset ℂ, 0 ∉ Z ∧ Z.card = Module.finrank ℂ (UpperTheory.V.Hi.fixd ρ I) ∧
      ∀ j : ℕ, HasTrace m ρ (Set.indicator {g | ∃ a ∈ I, ∃ b ∈ I, g = a * Cartan.diagPow F n (j • ν) * b} 1)
        (Z.map (· ^ j)).sum := by
  subst hI
  have h0 : (GLnLocal.uniformizer F : F) ≠ 0 := GLnLocal.uniformizer_ne_zero F
  let t : (Fin n → ℤ) → Fin n → Fˣ := fun a i => (Units.mk0 (GLnLocal.uniformizer F : F) h0) ^ a i
  have hdiag : ∀ a, Cartan.diagPow F n a = diagT F (Fin n) (t a) := fun a => by
    ext i j
    rw [val_diagT]
    simp [t, Cartan.diagPow]
  have ht : ∀ a b, t (a + b) = t a * t b := fun a b => by
    funext i
    simp [t, _root_.zpow_add]
  obtain ⟨hmul, hunit, -⟩ := UpperTheory.V.AlgebraTools.domMul F n ⊤ ℂ V ρ
  have hq : IsUnit ((GlobalTheory.SplitWeil.resCard F : ℕ) : ℂ) :=
    (Nat.cast_ne_zero.2 (GlobalTheory.SplitWeil.one_lt_resCard F).ne_bot).isUnit
  let T := UpperTheory.V.AlgebraTools.hk ρ (UpperTheory.V.AlgebraTools.iwC F n ⊤) (diagT F (Fin n) (t ν))
  have hdom : ∀ a, Antitone a → UpperTheory.V.AlgebraTools.Dom (t a) := fun a ha => dom_pow a ha h0
  have hTu : IsUnit T := hunit hq _ (hdom ν hν)
  have hone : UpperTheory.V.AlgebraTools.hk ρ (UpperTheory.V.AlgebraTools.iwC F n ⊤) (diagT F (Fin n) (t 0)) = 1 := by
    have hd0 := hdom 0 (fun _ _ _ => le_rfl)
    have h1 := hmul _ _ hd0 hd0
    rw [← ht, add_zero] at h1
    exact (hunit hq _ hd0).mul_left_cancel (h1.trans (mul_one _).symm)
  have hpow : ∀ j : ℕ, UpperTheory.V.AlgebraTools.hk ρ (UpperTheory.V.AlgebraTools.iwC F n ⊤) (diagT F (Fin n) (t (j • ν))) = T ^ j := by
    intro j
    induction j with
    | zero => simpa using hone
    | succ j ih =>
      have hj : Antitone (j • ν) := fun a b hab => by
        simpa using mul_le_mul_of_nonneg_left (hν hab) (Int.natCast_nonneg j)
      rw [pow_succ, ← ih, hmul _ _ (hdom _ hj) (hdom _ hν), ← ht, succ_nsmul]
  obtain ⟨Z, hZ0, hZc, hZ⟩ := exists_powerSums T hTu
  refine ⟨Z, hZ0, hZc, fun j => ?_⟩
  have h := hasTrace_hk m hρ hIo hIc hm (diagT F (Fin n) (t (j • ν))) ((UpperTheory.V.AlgebraTools.heckePairIwC F n ⊤).1 _)
  rw [hpow, hZ, ← hdiag] at h
  exact h

end Loc

theorem UpperTheory.ConvolutionTheory.C.iwPow :
    UpperTheory.ConvolutionTheory.C.IwPow := by
  intro K _ _ n w _ _ m _ hm σ ν hν hfd
  haveI : FiniteDimensional ℂ (UpperTheory.V.Hi.fixd σ.ρ (GlobalTheory.SmGL.iwahori (w.adicCompletion K) (Fin n))) := hfd
  exact iw_local m (UpperTheory.V.AlgebraTools.memIwC _ n ⊤).2.1 hm σ.ρ σ.smooth (GLnLocal.isOpen_iwahori _ _)
    (GLnLocal.isCompact_iwahori _ _) ν hν
end
