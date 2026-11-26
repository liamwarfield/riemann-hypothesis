module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchPow
public import Development.AutomorphicArithmetic.Foundations.Convolution.Cbcc
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TermEV

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.Outright
theorem UpperTheory.ConvolutionTheory.GM.gm : UpperTheory.ConvolutionTheory.GM.GM := UpperTheory.ConvolutionTheory.GM.gm_of_bcfl PositivityTheory.Rg.Tf.Loc.bcflUnit
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.TrBasic
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

namespace UpperTheory.Gal.InertialTypesAlt.G.FiniteTraces

private theorem finTrace_zero {V : Type} [AddCommGroup V] [Module ℂ V] :
    HasFinTrace (0 : V →ₗ[ℂ] V) 0 := by
  have key : ∀ (R : Submodule ℂ V) (h : ∀ v ∈ R, (0 : V →ₗ[ℂ] V) v ∈ R),
      LinearMap.trace ℂ R ((0 : V →ₗ[ℂ] V).restrict h) = 0 := by
    intro R h
    have e : (0 : V →ₗ[ℂ] V).restrict h = 0 := rfl
    rw [e, map_zero]
  exact ⟨by rw [LinearMap.range_zero]; infer_instance, key _ _⟩

private theorem finTrace_smul {V : Type} [AddCommGroup V] [Module ℂ V] (A : V →ₗ[ℂ] V) {c : ℂ} (b : ℂ)
    (h : HasFinTrace A c) : HasFinTrace (b • A) (b * c) := by
  by_cases hb : b = 0
  · subst hb
    rw [zero_smul, zero_mul]
    exact finTrace_zero
  obtain ⟨hf, rfl⟩ := h
  have key : ∀ (R : Submodule ℂ V) (_ : R = LinearMap.range A) (h1 : ∀ v ∈ R, (b • A) v ∈ R)
      (h2 : ∀ v ∈ LinearMap.range A, A v ∈ LinearMap.range A),
      LinearMap.trace ℂ R ((b • A).restrict h1) = b * LinearMap.trace ℂ (LinearMap.range A) (A.restrict h2) := by
    intro R hR h1 h2
    subst hR
    have e : (b • A).restrict h1 = b • A.restrict h2 := rfl
    rw [e, map_smul, smul_eq_mul]
  have hr : LinearMap.range (b • A) = LinearMap.range A := LinearMap.range_smul _ _ hb
  exact ⟨by rw [hr]; exact hf, key _ hr _ _⟩

private theorem isInt_smul {G V : Type} [Group G] [MeasurableSpace G] [AddCommGroup V] [Module ℂ V]
    {m : Measure G} {ρ : Representation ℂ G V} {f : G → ℂ} {A : V →ₗ[ℂ] V} (d : ENNReal) (hdt : d ≠ ⊤)
    (hA : IsIntegralOp m ρ f A) : IsIntegralOp (d • m) ρ f ((d.toReal : ℂ) • A) := fun v l =>
  ⟨(hA v l).1.smul_measure hdt, by
    rw [integral_smul_measure, LinearMap.smul_apply, map_smul, (hA v l).2, Complex.real_smul, smul_eq_mul]⟩

private theorem finite_comp {V : Type} [AddCommGroup V] [Module ℂ V] (A : V →ₗ[ℂ] V) (I : V ≃ₗ[ℂ] V)
    (h : FiniteDimensional ℂ (LinearMap.range A)) :
    FiniteDimensional ℂ (LinearMap.range (A ∘ₗ (I : V →ₗ[ℂ] V))) := by
  have e : LinearMap.range (A ∘ₗ (I : V →ₗ[ℂ] V)) = LinearMap.range A :=
    LinearMap.range_comp_of_range_eq_top A (LinearEquiv.range I)
  rw [e]
  exact h

end UpperTheory.Gal.InertialTypesAlt.G.FiniteTraces

open UpperTheory.Gal.InertialTypesAlt.G.FiniteTraces in
theorem UpperTheory.Gal.InertialTypesAlt.G.trBasic :
    UpperTheory.Gal.InertialTypesAlt.G.TrBasic := by
  intro G _ _ _ m τ I f
  refine ⟨?_, ?_, ?_⟩
  · rintro z ⟨A, hA, hF⟩
    exact ⟨_, A, hA, finite_comp A I hF.1, rfl⟩
  · rintro t t' ⟨A, hA, -, rfl⟩ ⟨B, hB, -, rfl⟩
    obtain rfl := hA.unique hB
    rfl
  · intro d hd
    refine ⟨?_, ?_⟩
    · rintro z ⟨A, hA, hF⟩
      exact ⟨_, isInt_smul d hd hA, finTrace_smul A _ hF⟩
    · rintro t ⟨B, hB, hF⟩
      refine ⟨_, isInt_smul d hd hB, ?_⟩
      have e : ((d.toReal : ℂ) • B) ∘ₗ (I : τ.V →ₗ[ℂ] τ.V) = (d.toReal : ℂ) • (B ∘ₗ (I : τ.V →ₗ[ℂ] τ.V)) := rfl
      rw [e]
      exact finTrace_smul _ _ hF
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.IsIntegralOpUntw
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

private theorem hasFinTrace_conj {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : V ≃ₗ[ℂ] W) {A : V →ₗ[ℂ] V} {c : ℂ} (h : HasFinTrace A c) :
    HasFinTrace ((e : V →ₗ[ℂ] W) ∘ₗ A ∘ₗ (e.symm : W →ₗ[ℂ] V)) c := by
  obtain ⟨hfd, rfl⟩ := h
  set B : W →ₗ[ℂ] W := (e : V →ₗ[ℂ] W) ∘ₗ A ∘ₗ (e.symm : W →ₗ[ℂ] V) with hB
  have hr : (LinearMap.range A).map (e : V →ₗ[ℂ] W) = LinearMap.range B := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨e x, by simp [hB]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨A (e.symm y), ⟨_, rfl⟩, by simp [hB]⟩
  let f : LinearMap.range A ≃ₗ[ℂ] LinearMap.range B :=
    (e.submoduleMap (LinearMap.range A)).trans (LinearEquiv.ofEq _ _ hr)
  refine ⟨f.finiteDimensional, ?_⟩
  rw [← LinearMap.trace_conj' _ f]
  congr 1

private theorem isIntegralOp_tw {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] {m : Measure G}
    {χ : G → ℂ} {τ τ₁ : SmIrr G} {e : τ.V ≃ₗ[ℂ] τ₁.V} (hT : TwOf χ τ τ₁ e) {f : G → ℂ} {A : τ.V →ₗ[ℂ] τ.V}
    (hA : IsIntegralOp m τ.ρ (fun g => f g * χ g) A) :
    IsIntegralOp m τ₁.ρ f ((e : τ.V →ₗ[ℂ] τ₁.V) ∘ₗ A ∘ₗ (e.symm : τ₁.V →ₗ[ℂ] τ.V)) := by
  intro w l
  have key : (fun g => f g * l (τ₁.ρ g w)) =
      fun g => f g * χ g * (l ∘ₗ (e : τ.V →ₗ[ℂ] τ₁.V)) (τ.ρ g (e.symm w)) := by
    funext g
    have := hT g (e.symm w)
    rw [LinearEquiv.apply_symm_apply] at this
    rw [← this, map_smul, map_smul, smul_eq_mul]
    simp [mul_assoc]
  obtain ⟨h₁, h₂⟩ := hA (e.symm w) (l ∘ₗ (e : τ.V →ₗ[ℂ] τ₁.V))
  rw [key]
  refine ⟨h₁, ?_⟩
  rw [← h₂]
  simp

private theorem isIntegralOp_untw {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] {m : Measure G}
    {χ : G → ℂ} {τ τ₁ : SmIrr G} {e : τ.V ≃ₗ[ℂ] τ₁.V} (hT : TwOf χ τ τ₁ e) {f : G → ℂ} {B : τ₁.V →ₗ[ℂ] τ₁.V}
    (hB : IsIntegralOp m τ₁.ρ f B) :
    IsIntegralOp m τ.ρ (fun g => f g * χ g) ((e.symm : τ₁.V →ₗ[ℂ] τ.V) ∘ₗ B ∘ₗ (e : τ.V →ₗ[ℂ] τ₁.V)) := by
  intro v l
  have key : (fun g => f g * χ g * l (τ.ρ g v)) =
      fun g => f g * (l ∘ₗ (e.symm : τ₁.V →ₗ[ℂ] τ.V)) (τ₁.ρ g (e v)) := by
    funext g
    rw [← hT g v]
    simp [mul_assoc]
  obtain ⟨h₁, h₂⟩ := hB (e v) (l ∘ₗ (e.symm : τ₁.V →ₗ[ℂ] τ.V))
  rw [key]
  refine ⟨h₁, ?_⟩
  rw [← h₂]
  simp

theorem UpperTheory.Gal.InertialTypesAlt.G.trTw :
    UpperTheory.Gal.InertialTypesAlt.G.TrTw := by
  intro G _ _ _ m χ τ τ₁ e hT f z
  refine ⟨⟨?_, ?_⟩, fun I => ⟨?_, ?_⟩⟩
  · rintro ⟨A, hA, hF⟩
    exact ⟨_, isIntegralOp_tw hT hA, hasFinTrace_conj e hF⟩
  · rintro ⟨B, hB, hF⟩
    exact ⟨_, isIntegralOp_untw hT hB, hasFinTrace_conj e.symm hF⟩
  · rintro ⟨A, hA, hF⟩
    refine ⟨_, isIntegralOp_tw hT hA, ?_⟩
    convert hasFinTrace_conj e hF using 1
    ext x
    simp
  · rintro ⟨B, hB, hF⟩
    refine ⟨_, isIntegralOp_untw hT hB, ?_⟩
    convert hasFinTrace_conj e.symm hF using 1
    ext x
    simp
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.FdFixed
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.TrEx
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

theorem UpperTheory.Gal.InertialTypesAlt.G.trEx :
    UpperTheory.Gal.InertialTypesAlt.G.TrEx := by
  intro K _ _ _ n hn π v _ _ m hm τ hτ f hf
  haveI := hm
  let μ : Measure (normOneGL (K := K) (n := n)) := Measure.haar
  obtain ⟨χ, hχ, V, hV⟩ := Dp.exTwist K n μ π hn
  obtain ⟨⟨τ₁, h₁⟩, htw⟩ := locTw K n hn π χ v τ hτ
  obtain ⟨e, he⟩ := htw τ₁ h₁
  have hocc : Occurs μ V v τ₁ :=
    (occursIff K n μ V hV.summand v τ₁).2 ((Dp.locIff K n μ (π.twist χ) V hV v τ₁).1 h₁)
  obtain ⟨h₁, h₂, h₃⟩ := occursBasics K n μ V v m hV.summand
  obtain ⟨z, hz⟩ := h₃ τ₁ hocc (fun g => f g * chiAt n χ⁻¹ v g) ((chiBasic K n χ⁻¹ v).2.2 f hf)
  have ht := (trTw _ m (chiAt n χ v) τ τ₁ e he (fun g => f g * chiAt n χ⁻¹ v g) z).1.2 hz
  have hfun : (fun g => f g * chiAt n χ⁻¹ v g * chiAt n χ v g) = f := by
    funext g
    have h := (chiBasic K n χ v).2.1 g
    rw [mul_assoc, mul_comm (chiAt n χ⁻¹ v g), h, mul_one]
  rw [hfun] at ht
  exact ⟨z, ht⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.BaseTw
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open scoped ComplexConjugate

namespace UpperTheory.Gal.InertialTypesAlt.G.StableBaseChangeTwists

private theorem test_ind {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {J : Subgroup G} (hJ : CO J)
    {χ : G → ℂ} (hχ : IsChr J χ) : Test ((J : Set G).indicator fun x => conj (χ x)) := by
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_,
    HasCompactSupport.intro hJ.1 fun x hx => Set.indicator_of_notMem hx _⟩
  by_cases hx : x ∈ (J : Set G)
  · filter_upwards [hJ.2.mem_nhds hx, (IsLocallyConstant.iff_eventually_eq _).1 hχ.1 x] with y hy hy2
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx, hy2]
  · have hcl : IsClosed (J : Set G) := Subgroup.isClosed_of_isOpen J hJ.2
    filter_upwards [hcl.isOpen_compl.mem_nhds hx] with y hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

section Loc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private theorem cmp_surj {v : Pl F} (w : PlacesOver E v) (h : ∀ u : PlacesOver E v, u = w) :
    Function.Surjective (GM.cmp (n := n) w) := by
  have hev : Function.Bijective (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w) := by
    letI : Unique (PlacesOver E v) := ⟨⟨w⟩, h⟩
    constructor
    · intro a b e
      funext u
      obtain rfl := h u
      exact e
    · intro z
      refine ⟨fun u => (h u).symm ▸ z, ?_⟩
      show ((h w).symm ▸ z : (w.1.adicCompletion E)) = z
      rfl
  let e := RingEquiv.ofBijective _ hev
  intro y
  refine ⟨mapGL n (e.symm : _ →+* _) y, ?_⟩
  exact Units.ext (Matrix.ext fun a b => e.apply_symm_apply _)

variable [IsGalois F E] {σ : E ≃ₐ[F] E} {q : Pl F} {w₀ : PlacesOver E q}

private theorem stabV (T : Ty σ n q w₀) (v : Pl F) (h : ∀ u : PlacesOver E v, u = T.mk' v)
    {a : Gw n (T.mk' v).1 →* Gw n (T.mk' v).1} (ha : IsLocGal σ (T.mk' v) a) (x : Gw n (T.mk' v).1) (hx : x ∈ T.J (T.mk' v).1) :
    a x ∈ T.J (T.mk' v).1 ∧ T.χ (T.mk' v).1 (a x) = T.χ (T.mk' v).1 x := by
  obtain ⟨g, rfl⟩ := cmp_surj (T.mk' v) h x
  letI : Unique (PlacesOver E v) := ⟨⟨T.mk' v⟩, h⟩
  have hall : ∀ u : PlacesOver E v, GM.cmp u g ∈ T.J u.1 := fun u => by
    obtain rfl := h u
    exact hx
  obtain ⟨h1, h2⟩ := T.stable v g hall
  rw [finprod_unique, finprod_unique] at h2
  have e : (default : PlacesOver E v) = T.mk' v := rfl
  rw [e] at h2
  rw [← ha]
  exact ⟨h1 _, h2⟩

end Loc

end UpperTheory.Gal.InertialTypesAlt.G.StableBaseChangeTwists

open UpperTheory.Gal.InertialTypesAlt.G.StableBaseChangeTwists in
theorem UpperTheory.Gal.InertialTypesAlt.G.baseTw :
    UpperTheory.Gal.InertialTypesAlt.G.BaseTw := by
  intro F E _ _ _ _ _ _ _ _ σ hgen hpr n hn μ _ V hV q w₀ T v hU hrk hne _ _ m hm τ s I hocc hs hI
  haveI := hm
  have hco := T.co (T.mk' v).1
  have hch := T.chr (T.mk' v).1
  have hT := test_ind hco hch
  refine ⟨hT, ?_⟩
  have h0 : m (T.J (T.mk' v).1) ≠ 0 := (hco.2.measure_pos m ⟨1, Subgroup.one_mem _⟩).ne'
  have ht : m (T.J (T.mk' v).1) ≠ ⊤ := hco.1.measure_lt_top.ne
  have hd0 : (m (T.J (T.mk' v).1))⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 ht
  have hdt : (m (T.J (T.mk' v).1))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 h0
  obtain ⟨mm, hmm⟩ : ∃ mm, mm = (m (T.J (T.mk' v).1))⁻¹ • m := ⟨_, rfl⟩
  haveI hmmH : mm.IsHaarMeasure := hmm ▸ Measure.IsHaarMeasure.smul _ hd0 hdt
  have hmm1 : mm (T.J (T.mk' v).1) = 1 := by
    rw [hmm, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 ht]
  have hback : (m (T.J (T.mk' v).1)) • mm = m := by
    rw [hmm, smul_smul, ENNReal.mul_inv_cancel h0 ht, one_smul]
  obtain ⟨e, he0, he1, he2⟩ := UpperTheory.exists_unique_eigenline_of_rankOne_occurs E n μ V hV (T.mk' v).1 τ hocc (T.J (T.mk' v).1) (T.χ (T.mk' v).1)
    hco hch hrk hne
  obtain ⟨-, -, h3⟩ := UpperTheory.ConvolutionTheory.C.occursBasics E n μ V (T.mk' v).1 mm hV
  obtain ⟨_, A, hA, -⟩ := h3 τ hocc _ hT
  obtain ⟨t, ht0, htt⟩ := UpperTheory.integralOp_eigenline_scalar_of_twist (Gw n (T.mk' v).1) mm τ I s (T.J (T.mk' v).1) (T.χ (T.mk' v).1) A e hco hch
    hmm1 hA he0 he1 he2 (stabV T v hU hs) hI
  have hsc := ((UpperTheory.Gal.InertialTypesAlt.G.trBasic _ mm τ I _).2.2 _ ht).2 t htt
  rw [hback] at hsc
  refine ⟨_, mul_ne_zero (Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨h0, ht⟩)) ht0, hsc⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.FibTrace
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

theorem UpperTheory.Gal.InertialTypesAlt.G.fibTrace :
    UpperTheory.Gal.InertialTypesAlt.G.FibTrace := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μE _ μF _ π P V Λ t hC hAt hW V₀ Λ₀ t₀ hS hAt₀ hΛ ht v _ m τ τ₀ hτ hO f z hf hz
  obtain ⟨π₀, hπ₀, -⟩ := Dp.exCusp F n μF V₀ hS
  obtain ⟨-, -, hcl, -⟩ := T.carryLift F E σ hσ hp n hn μE μF
  have hl := hcl π₀ P V₀ V Λ₀ t₀ Λ t hπ₀ hC hAt₀ hAt hΛ ht
  obtain ⟨η, hη, hiso⟩ := (R.fibre_holds F E hp n hn (.cx π₀) (.cx P) hl.1).2 (.cx π) hW
  have he : π₀.twist η = π := (Dp.isoEq F n _ _).1 hiso
  subst he
  have hτ₀ : (Cusp.cx π₀).locComp v τ₀ :=
    ((Dp.locIff F n μF π₀ V₀ hπ₀ v τ₀).trans (occursIff F n μF V₀ hπ₀.summand v τ₀).symm).2 hO
  obtain ⟨e, hTw⟩ := (locTw F n hn π₀ η v τ₀ hτ₀).2 τ hτ
  have hfe : (fun g => f g * chiAt n η v g) = f := by
    funext g
    by_cases h0 : f g = 0
    · simp [h0]
    · have h1 : chiAt n η v g = 1 := by
        rcases hη with rfl | hη
        · rfl
        · simp only [chiAt]
          rw [(hf g h0) η hη]
          rfl
      rw [h1, mul_one]
  have h := ((trTw (Gw n v) m (chiAt n η v) τ₀ τ e hTw f z).1).2 hz
  rwa [hfe] at h
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.LevEx
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

theorem UpperTheory.Gal.InertialTypesAlt.G.levEx :
    UpperTheory.Gal.InertialTypesAlt.G.LevEx := by
  intro G _ _ _ K f hK hN hf
  obtain ⟨hlc, hcs⟩ := hf
  have h1 : ∀ x : G, ∃ V : Subgroup G, IsOpen (V : Set G) ∧ ∀ a ∈ V, f (a * x) = f x := by
    intro x
    have hopen : IsOpen ((fun a : G => a * x) ⁻¹' (f ⁻¹' {f x})) :=
      (hlc.isOpen_fiber (f x)).preimage (continuous_mul_const x)
    obtain ⟨V, hV, hVs⟩ := hN _ (hopen.mem_nhds (by simp))
    exact ⟨V, hV, fun a ha => by simpa using hVs (SetLike.mem_coe.2 ha)⟩
  choose V hVo hVc using h1
  obtain ⟨t, -, hcov⟩ := hcs.isCompact.elim_nhds_subcover
    (fun x => (fun y : G => y * x⁻¹) ⁻¹' (V x : Set G))
    (fun x _ => ((hVo x).preimage (continuous_mul_const x⁻¹)).mem_nhds (by simp [one_mem]))
  have hz : ∀ y, (∀ x ∈ t, y * x⁻¹ ∉ V x) → f y = 0 := by
    intro y hy
    by_contra h
    have hm := hcov (subset_tsupport f (Function.mem_support.2 h))
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, exists_prop] at hm
    obtain ⟨x, hx, hxy⟩ := hm
    exact hy x hx hxy
  have hNU : (K : Set G) ∩ ⋂ x ∈ t, (V x : Set G) ∈ nhds (1 : G) :=
    inter_mem (hK.mem_nhds K.one_mem)
      ((Filter.biInter_finset_mem t).2 fun x _ => (hVo x).mem_nhds (V x).one_mem)
  obtain ⟨U, hU, hUs⟩ := hN _ hNU
  refine ⟨U, hU, fun u hu => (hUs hu).1, fun u hu g => ?_⟩
  have hUV : ∀ x ∈ t, u ∈ V x := fun x hx => by
    have h2 := (hUs hu).2
    simp only [Set.mem_iInter, SetLike.mem_coe] at h2
    exact h2 x hx
  by_cases hg : ∃ x ∈ t, g * x⁻¹ ∈ V x
  · obtain ⟨x, hx, hgx⟩ := hg
    have e1 := hVc x _ hgx
    have e2 := hVc x _ ((V x).mul_mem (hUV x hx) hgx)
    have r1 : g * x⁻¹ * x = g := by group
    have r2 : u * (g * x⁻¹) * x = u * g := by group
    rw [r1] at e1
    rw [r2] at e2
    rw [e1, e2]
  · push_neg at hg
    rw [hz g hg, hz (u * g)]
    intro x hx hm
    apply hg x hx
    have h3 := (V x).mul_mem ((V x).inv_mem (hUV x hx)) hm
    have r3 : u⁻¹ * (u * g * x⁻¹) = g * x⁻¹ := by group
    rwa [r3] at h3
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.PowNe
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

theorem UpperTheory.Gal.InertialTypesAlt.G.powNe :
    UpperTheory.Gal.InertialTypesAlt.G.PowNe := by
  intro Z hZ h0
  by_contra h
  rw [Filter.not_frequently] at h
  obtain ⟨ζ, hζ⟩ := Multiset.exists_mem_of_ne_zero hZ
  have h1 := UpperTheory.ConvolutionTheory.C.powIndep Unit (fun _ => 1) (fun _ => Z) (fun _ => h0)
    (h.mono fun j hj => by simpa using hj) ζ
  have h2 : ((Multiset.filter (· = ζ) Z).card : ℂ) = 0 := by simpa only [Finset.univ_unique, Finset.sum_singleton, one_mul] using h1
  have h3 : (Multiset.filter (· = ζ) Z).card = 0 := by exact_mod_cast h2
  have h4 : 0 < (Multiset.filter (· = ζ) Z).card :=
    Multiset.card_pos_iff_exists_mem.2 ⟨ζ, Multiset.mem_filter.2 ⟨hζ, rfl⟩⟩
  exact h4.ne' h3
end

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G
open UpperTheory.ConvolutionTheory.T
open scoped ComplexConjugate

private theorem fd_fixed {G V : Type} [Group G] [MeasurableSpace G] [AddCommGroup V] [Module ℂ V]
    (m : Measure G) (ρ : Representation ℂ G V) (J : Subgroup G) (hJ : MeasurableSet (J : Set G))
    (h1 : m (J : Set G) = 1) (A : V →ₗ[ℂ] V) (hA : IsIntegralOp m ρ ((J : Set G).indicator 1) A)
    (hf : FiniteDimensional ℂ (LinearMap.range A)) : FiniteDimensional ℂ (fixedVectors ρ J) := by
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range A) fun x hx => ?_
  have hAx : A x = x := by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    rw [map_sub, (hA x l).2, sub_eq_zero]
    have e : (fun g => ((J : Set G).indicator (1 : G → ℂ)) g * l (ρ g x)) =
        (J : Set G).indicator fun _ => l x := by
      funext g
      by_cases hg : g ∈ (J : Set G)
      · have hgx : ρ g x = x := hx g hg
        simp [Set.indicator_of_mem hg, hgx]
      · simp [Set.indicator_of_notMem hg]
    rw [e, integral_indicator hJ]
    simp [Measure.real, h1]
  exact ⟨x, hAx⟩

private theorem under_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} (w : PlacesOver E v) : w.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext w.2.over.symm

private theorem small {K : Type} [Field K] [NumberField K] (n : ℕ) (v : Pl K) :
    ∀ N ∈ nhds (1 : Gw n v), ∃ U : Subgroup (Gw n v), IsOpen (U : Set (Gw n v)) ∧ (U : Set (Gw n v)) ⊆ N := fun N hN => by
  obtain ⟨U, -, hU⟩ := exists_openSubgroup_isCompact_subset hN
  exact ⟨U, U.isOpen, hU⟩

private theorem scale {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (m : Measure G) (hm : m.IsHaarMeasure) (J : Subgroup G) (hJ : CO J) :
    ∃ d : ENNReal, d ≠ 0 ∧ d ≠ ⊤ ∧ (d • m).IsHaarMeasure ∧ (d • m) J = 1 := by
  have h0 : m J ≠ 0 := hJ.2.measure_ne_zero _ ⟨1, one_mem _⟩
  have hT : m J ≠ ⊤ := hJ.1.measure_lt_top.ne
  refine ⟨(m J)⁻¹, ENNReal.inv_ne_zero.2 hT, ENNReal.inv_ne_top.2 h0,
    Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 hT) (ENNReal.inv_ne_top.2 h0), ?_⟩
  simp [ENNReal.inv_mul_cancel h0 hT]

private theorem updLoc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E ≃ₐ[F] E} {n : ℕ}
    {q : Pl F} {w₀ : PlacesOver E q} (L : GM.Loc σ n q w₀) (v : Pl F) (hv : v ∈ L.S)
    (φ : GL (Fin n) (CompletionsOver E v) → ℂ) (f : Gw n v → ℂ) (c : ℂ) (UE : Subgroup (GL (Fin n) (CompletionsOver E v)))
    (UF : Subgroup (Gw n v)) (h1 : Test φ) (h2 : Test f) (h3 : GM.MatchAt σ v c φ f)
    (h4 : IsOpen (UE : Set (GL (Fin n) (CompletionsOver E v))) ∧ (UE : Set _) ⊆ unitSet E n v ∧
      IsOpen (UF : Set (Gw n v)) ∧ UF ≤ GLnLocal.integralGL (v.adicCompletion F) n)
    (h5 : (∀ u ∈ UE, ∀ g, φ (u * g) = φ g) ∧ ∀ u ∈ UF, ∀ g, f (u * g) = f g) :
    ∃ L' : GM.Loc σ n q w₀, L'.S = L.S ∧ L'.φ = Function.update L.φ v φ ∧ L'.f = Function.update L.f v f ∧
      L'.c = Function.update L.c v c ∧ L'.UE = Function.update L.UE v UE ∧ L'.UF = Function.update L.UF v UF := by
  have hq : q ≠ v := fun h => L.q_not (h ▸ hv)
  refine ⟨⟨L.S, L.q_not, L.unr, Function.update L.φ v φ, Function.update L.f v f, Function.update L.c v c,
    Function.update L.UE v UE, Function.update L.UF v UF, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_, ?_,
    fun y hy hyq => ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · by_cases h : y = v
    · subst h; simp only [Function.update_self]; exact ⟨h1.1, h1.2, h2.1, h2.2⟩
    · simp only [Function.update_of_ne h]; exact L.test y hy
  · by_cases h : y = v
    · subst h; simp only [Function.update_self]; exact h4
    · simp only [Function.update_of_ne h]; exact L.lev y hy
  · by_cases h : y = v
    · subst h; simp only [Function.update_self]; exact h5
    · simp only [Function.update_of_ne h]; exact L.inv y hy
  · by_cases h : y = v
    · subst h; simp only [Function.update_self]; exact h3
    · simp only [Function.update_of_ne h]; exact L.mat y hy
  · simp only [Function.update_of_ne hq]; exact L.at_q
  · have h : y ≠ v := fun h => hy (h ▸ hv)
    simp only [Function.update_of_ne h]; exact L.off y hy hyq

set_option maxHeartbeats 1600000 in
theorem UpperTheory.Gal.InertialTypesAlt.G.core :
    UpperTheory.Gal.InertialTypesAlt.G.Core := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μE _ π P V hC hP hW v w hv iF bF iE bE mF mE hmF hmE τ τ' hτ hτ' s₀ I₀ hs₀ hI₀
  obtain rfl := bF.measurable_eq
  obtain rfl := bE.measurable_eq
  letI : ∀ x : Pl E, MeasurableSpace (Gw n x) := fun _ => borel _
  haveI : ∀ x : Pl E, BorelSpace (Gw n x) := fun _ => ⟨rfl⟩
  letI : ∀ x : Pl F, MeasurableSpace (Gw n x) := fun _ => borel _
  haveI : ∀ x : Pl F, BorelSpace (Gw n x) := fun _ => ⟨rfl⟩
  let μF : Measure (normOneGL (K := F) (n := n)) := Measure.haar
  have hV := hC.summand
  obtain ⟨-, hAtE, -, -, hnp, θ, hθ, hst⟩ := carryLift F E σ hσ hp n hn μE μF
  obtain ⟨Λ, t, hAt⟩ := hAtE V hV
  have hVθ := (hst P V hC).1 hP
  have hOffA : OffAll F n Λ t := by
    by_contra hc
    exact hnp _ V Λ t hC hAt (famParts F E σ hσ hp n hn
      (fun m hm _ => liftAll (liftStep (coreLift UpperTheory.ConvolutionTheory.ci GM.gm)) F E σ hσ hp m hm) Λ t hc)
  have hocc' : Occurs μE V w.1 τ' := (occursIff E n μE V hV w.1 τ').2 ((Dp.locIff E n μE P V hC w.1 τ').1 hτ')
  obtain ⟨S, q, w₀, hvS, hqS, hq, hunr, hsph, hS'⟩ := pickS F E σ hσ hp n hn μE V Λ t hV hAt v
  obtain ⟨-, -, hne, huniq, -⟩ := places F E hp
  obtain ⟨T, hTS, -, htyped, hrank, c, f₀, UF, -, hL⟩ := tyEx F E σ hσ hp n hn μE V hV q w₀ hq S hqS hunr hsph
    fun u => (hne u).some
  obtain rfl : w = T.mk' v := huniq v hv _ _
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).1 htyped
  obtain ⟨k, hk, D, s, hs, νE, jE, νF, jF, b, a, aE, aF, hposition, harch, hAE, hAF, hpair, hua⟩ :=
    pickInf F E σ hσ hp n hn μE μF u hu0
  have heig : ∀ x, V ⊓ eigL μE x (T.J x) (T.χ x) ≠ ⊥ := fun x =>
    (Submodule.ne_bot_iff _).2 ⟨u, ⟨hu.1, (Submodule.mem_iInf _).1 hu.2 x⟩, hu0⟩
  have hmk : ∀ y ∈ S, (T.mk' y).1 ≠ w₀.1 := fun y hy h =>
    hqS ((by rw [← under_eq (T.mk' y), h, under_eq w₀] : y = q) ▸ hy)
  have hcoI : CO (GLnLocal.iwahori (w₀.1.adicCompletion E) n) := T.at_q w₀ ▸ T.co w₀.1
  obtain ⟨m, hm, hm1, hm2⟩ : ∃ m : ∀ x : Pl E, Measure (Gw n x), (∀ x, (m x).IsHaarMeasure) ∧
      m w₀.1 (GLnLocal.iwahori (w₀.1.adicCompletion E) n : Set (Gw n w₀.1)) = 1 ∧ m (T.mk' v).1 = mE := by
    choose m₁ hm₁ _ using fun x : Pl E => haar_norm E n x
    obtain ⟨d, -, -, hd, hd1⟩ := scale (m₁ w₀.1) (hm₁ _) _ hcoI
    refine ⟨Function.update (Function.update m₁ w₀.1 (d • m₁ w₀.1)) (T.mk' v).1 mE, fun x => ?_, ?_, Function.update_self ..⟩
    · by_cases h : x = (T.mk' v).1
      · subst h; rw [Function.update_self]; exact hmE
      · rw [Function.update_of_ne h]
        by_cases h' : x = w₀.1
        · subst h'; rw [Function.update_self]; exact hd
        · rw [Function.update_of_ne h']; exact hm₁ x
    · rw [Function.update_of_ne (hmk v hvS).symm, Function.update_self]; exact hd1
  obtain ⟨d, hd0, hdT, hdH, hd1⟩ := scale mF hmF (GLnLocal.integralGL (v.adicCompletion F) n)
    ⟨GLnLocal.isCompact_integralGL _ n, GLnLocal.isOpen_integralGL _ n⟩
  obtain ⟨m', hm', hm2'⟩ : ∃ m : ∀ x : Pl F, Measure (Gw n x), (∀ x, (m x).IsHaarMeasure ∧
      m x (GLnLocal.integralGL (x.adicCompletion F) n) = 1) ∧ m v = d • mF := by
    choose m₁ hm₁ using fun x : Pl F => haar_norm F n x
    refine ⟨Function.update m₁ v (d • mF), fun x => ?_, Function.update_self ..⟩
    by_cases h : x = v
    · subst h; rw [Function.update_self]; exact ⟨hdH, hd1⟩
    · rw [Function.update_of_ne h]; exact hm₁ x
  have hoccE : ∀ x : Pl E, ∃ ρ : SmIrr (Gw n x), Occurs μE V x ρ := fun x => by
    haveI := hm x
    exact (occursBasics E n μE V x (m x) hV).1
  obtain ⟨X, hX, hXv⟩ : ∃ X : ∀ y : Pl F, Σ ρ : SmIrr (Gw n (T.mk' y).1), (Gw n (T.mk' y).1 →* Gw n (T.mk' y).1) × (ρ.V ≃ₗ[ℂ] ρ.V),
      (∀ y, Occurs μE V (T.mk' y).1 (X y).1 ∧ (¬ GM.Split E y → IsLocGal σ (T.mk' y) (X y).2.1 ∧
        ∀ g x, (X y).2.2 ((X y).1.ρ g x) = (X y).1.ρ ((X y).2.1 g) ((X y).2.2 x))) ∧ X v = ⟨τ', s₀, I₀⟩ := by
    have hex : ∀ y : Pl F, ∃ Y : Σ ρ : SmIrr (Gw n (T.mk' y).1), (Gw n (T.mk' y).1 →* Gw n (T.mk' y).1) × (ρ.V ≃ₗ[ℂ] ρ.V),
        Occurs μE V (T.mk' y).1 Y.1 ∧ (¬ GM.Split E y → IsLocGal σ (T.mk' y) Y.2.1 ∧
          ∀ g x, Y.2.2 (Y.1.ρ g x) = Y.1.ρ (Y.2.1 g) (Y.2.2 x)) := fun y => by
      obtain ⟨ρ, hρ⟩ := hoccE (T.mk' y).1
      by_cases hy : GM.Split E y
      · exact ⟨⟨ρ, MonoidHom.id _, LinearEquiv.refl _ _⟩, hρ, fun h => absurd hy h⟩
      · obtain ⟨-, g, hg, hg'⟩ := locGalEx F E σ hp n y (T.mk' y) hy
        obtain ⟨J, hJ⟩ := (hg' μE θ hθ).2 V ρ hV hVθ hρ
        exact ⟨⟨ρ, g, J⟩, hρ, fun _ => ⟨hg, hJ⟩⟩
    choose X₁ hX₁ using hex
    refine ⟨Function.update X₁ v ⟨τ', s₀, I₀⟩, fun y => ?_, Function.update_self ..⟩
    by_cases h : y = v
    · subst h; rw [Function.update_self]; exact ⟨hocc', fun _ => ⟨hs₀, hI₀⟩⟩
    · rw [Function.update_of_ne h]; exact hX₁ y
  obtain ⟨τ₀, hτ₀⟩ := hoccE w₀.1
  obtain ⟨y₀, hy₀, hY⟩ := (twistY F E σ hσ k n hk hn μE θ hθ D s hs hposition νE νF b a aE aF harch q w₀ hq T V hV hVθ hrank).1
    ⟨u, hu, hua⟩
  obtain ⟨cE, hcE, hE⟩ := termEV F E σ hσ k n hk (hk ▸ hp) hn μE θ hθ D s hs hposition νE νF b a aE aF harch m hm q w₀ hq T V hV hVθ
    (fun y hy hy' x => ⟨hrank y hy hy' x, heig _⟩) τ₀ (fun y => (X y).1) (fun y => (X y).2.1) (fun y => (X y).2.2) hτ₀
    (fun y _ => (hX y).1) (fun y _ hy => (hX y).2 hy) y₀ hy₀
  have hYZ : T.Y μE V (fun i => OComponent μE (s i) (hs i) νF a) y₀ ≤ T.Z μE V (fun i => OComponent μE (s i) (hs i) νF a) y₀ := by
    unfold Ty.Y Ty.Z Ty.typed
    exact inf_le_inf_left _ (le_iInf₂ fun w _ => iInf_le _ w)
  replace hcE := hcE fun h => hY (le_bot_iff.1 (h ▸ hYZ))
  have hfixS : ∀ y, GM.Split E y → ∀ x : PlacesOver E y, V ⊓ fixL μE x.1 (T.J x.1) ≠ ⊥ := fun y hy x => by
    have h1 := heig x.1
    have h2 := T.chr x.1
    rw [T.triv y hy x] at h1 h2
    rwa [(eigBasic E n μE _ _ _ (T.co _) h2).2.1] at h1
  obtain ⟨ν, hν⟩ := goodEx n hn
  obtain ⟨Z₀, hZ0, hZ₀, hZ⟩ : ∃ Z : Multiset ℂ, 0 ∉ Z ∧ Z ≠ 0 ∧ ∀ j : ℕ,
      HasTrace (m w₀.1) τ₀.ρ ((GM.iwCoset w₀.1 (j • ν)).indicator 1) (Z.map (· ^ j)).sum := by
    haveI := hm w₀.1
    obtain ⟨hfx, -, -, -, -, A, hA, hfin, -⟩ := unitTrace E n μE V hV w₀.1 (m w₀.1) (hm _) τ₀ _ hτ₀ hcoI
      (T.at_q w₀ ▸ hfixS q hq w₀)
    have fd := fd_fixed (m w₀.1) τ₀.ρ _ hcoI.2.measurableSet hm1 A hA hfin
    obtain ⟨Z, h0, hcard, hZ⟩ := iwPow E n w₀.1 (m w₀.1) hm1 τ₀ ν hν.1.antitone fd
    refine ⟨Z, h0, ?_, hZ⟩
    rintro rfl
    exact hfx (Submodule.finrank_eq_zero.1 (by simpa using hcard.symm))
  let ψ : ∀ y : Pl F, Gw n (T.mk' y).1 → ℂ := fun y =>
    (T.J (T.mk' y).1 : Set (Gw n (T.mk' y).1)).indicator fun x => conj (T.χ (T.mk' y).1 x)
  have hψs : ∀ y, GM.Split E y → ψ y = (T.J (T.mk' y).1 : Set (Gw n (T.mk' y).1)).indicator 1 := fun y hy => by
    simp [ψ, T.triv y hy (T.mk' y)]
    rfl
  have hunit := fun y (hy : GM.Split E y) =>
    unitTrace E n μE V hV (T.mk' y).1 (m _) (hm _) (X y).1 (T.J _) (hX y).1 (T.co _) (hfixS y hy _)
  have hbase := fun y (hyS : y ∈ T.S) (hy : ¬ GM.Split E y) =>
    baseTw F E σ hσ hp n hn μE V hV q w₀ T y (fun x => huniq y hy _ _) (hrank y hyS hy _) (heig _) (m _) (hm _) (X y).1 (X y).2.1
      (X y).2.2 (hX y).1 ((hX y).2 hy).1 ((hX y).2 hy).2
  have htb : ∀ y : Pl F, ∃ z : ℂ, y ∈ T.S → z ≠ 0 ∧ (GM.Split E y → HasTrace (m _) (X y).1.ρ (ψ y) z) ∧
      (¬ GM.Split E y → HasTwTrace (m _) (X y).1 (X y).2.2 (ψ y) z) := fun y => by
    by_cases hyS : y ∈ T.S
    · by_cases hy : GM.Split E y
      · obtain ⟨z, h1, h2⟩ := (hunit y hy).2.2.2
        exact ⟨z, fun _ => ⟨h1, fun _ => hψs y hy ▸ h2, fun h => absurd hy h⟩⟩
      · obtain ⟨z, h1, h2⟩ := (hbase y hyS hy).2
        exact ⟨z, fun _ => ⟨h1, fun h => absurd h hy, fun _ => h2⟩⟩
    · exact ⟨0, fun h => absurd h hyS⟩
  choose tb htb using htb
  obtain ⟨L₁, hfit, -, -, -⟩ := hL ψ fun y hy => by
    have hy' := (Finset.mem_filter.1 hy).2
    rw [hψs y hy']
    exact ⟨(hunit y hy').2.1, (hunit y hy').2.2.1⟩
  have hL₁S : L₁.S = S := hfit.S_eq.trans hTS
  have hvT : v ∈ T.S := hTS ▸ hvS
  obtain ⟨⟨e, he⟩, hint, -⟩ := cmpIso F E n v (T.mk' v) fun x => huniq v hv _ _
  have hφn : ∀ y ∈ T.S, ¬ GM.Split E y → L₁.φ y = fun g => ψ y (GM.cmp (T.mk' y) g) := fun y hy hy' => by
    rw [hfit.nonsplit y hy hy', (cmpIso F E n y (T.mk' y) fun x => huniq y hy' _ _).2.2]
  obtain ⟨κ, hκ, hG⟩ := GM.gm F E σ hσ hp n hn μE μF θ hθ q w₀ hq νE νF aE aF 1 one_pos hAE hAF hpair
  set SF : Set (Pl F) := {y | y ∈ S ∨ y = q} with hSF
  set SE : Set (Pl E) := {y | y.under (𝓞 F) ∈ SF} with hSE
  have hSFf : SF.Finite := (S.finite_toSet.union (Set.finite_singleton q)).subset fun y hy => hy
  have hSEf : SE.Finite := by
    obtain ⟨𝔢, -, h𝔢, -⟩ := hG L₁ ν hν
    have heS : 𝔢.S = SE := Set.ext fun y => by rw [h𝔢.2.2.1, hL₁S]; rfl
    exact heS ▸ 𝔢.finS
  have key : ∀ U : Subgroup (Gw n v), IsOpen (U : Set (Gw n v)) → U ≤ GLnLocal.integralGL (v.adicCompletion F) n →
      ∃ B : ℕ → ℂ, ∀ (φ : Gw n (T.mk' v).1 → ℂ) (f : Gw n v → ℂ) (c₁ z r : ℂ), Test φ → Test f →
        GM.MatchAt σ v c₁ (fun g => φ (GM.cmp (T.mk' v) g)) f → (∀ g, f g ≠ 0 → g ∈ normSet E n v) → HasTrace mF τ.ρ f z →
        HasTwTrace mE τ' I₀ φ r → (∀ x ∈ U, ∀ g, f (x * g) = f g) →
        ∀ᶠ j : ℕ in atTop, cE * (Z₀.map (· ^ j)).sum * (∏ y ∈ T.S.erase v, tb y) * r = B j * (c₁ * z) := by
    intro U hU1 hU2
    obtain ⟨ι, _, V₀, ρ, bF, Z, hι, hF⟩ := sideSum F E σ n (Module.finrank F E) hn μF νF m' hm' aF q w₀ S
      (Function.update L₁.UF v U) ν hν.1.antitone
      (fun V₀ => ∃ Λ' t', At μF SF V₀ Λ' t' ∧ Λ = bcInf Λ' ∧ ∀ y ∉ SE, t y = bcSat t' y) (y₀ ^ (k + 1)) (pow_pos hy₀ _)
    have hs₁ : ∀ i (y : Pl F), ∃ z : ℂ, y ∈ S → HasTrace (m' y) (ρ i y).ρ (L₁.f y) z := fun i y => by
      by_cases hy : y ∈ S
      · haveI := (hm' y).1
        have ht := L₁.test y (hL₁S ▸ hy)
        obtain ⟨z, hz⟩ := (occursBasics F n μF (V₀ i) y (m' y) (hι i).1).2.2 _ ((hι i).2.2.2 y) (L₁.f y) ⟨ht.2.2.1, ht.2.2.2⟩
        exact ⟨z, fun _ => hz⟩
      · exact ⟨0, fun h => absurd h hy⟩
    choose s₁ hs₁ using hs₁
    refine ⟨fun j => (κ * ∏ y ∈ S.erase v, L₁.c y) * (d.toReal : ℂ) *
      ∑ i, bF i * ((Z i).map (· ^ j)).sum * ∏ y ∈ S.erase v, s₁ i y, fun φ f c₁ z r hφ hf hmat hsup hz hr hinv => ?_⟩
    obtain ⟨U', hU'1, hU'2, hU'3⟩ := levEx _ (GLnLocal.integralGL ((T.mk' v).1.adicCompletion E) n) φ
      (GLnLocal.isOpen_integralGL _ n) (small n _) hφ
    have hce : (fun g => GM.cmp (n := n) (T.mk' v) g) = e := funext fun g => (he g).symm
    have hφt : Test fun g => φ (GM.cmp (T.mk' v) g) := by
      have : (fun g => φ (GM.cmp (T.mk' v) g)) = φ ∘ e.toHomeomorph := funext fun g => congrArg φ (he g).symm
      rw [this]
      exact ⟨hφ.1.comp_continuous e.continuous, hφ.2.comp_homeomorph _⟩
    obtain ⟨L, l1, l2, l3, l4, l5, l6⟩ := updLoc L₁ v (hL₁S ▸ hvS) _ f c₁ (U'.comap (GM.cmp (T.mk' v))) U hφt hf hmat
      ⟨hU'1.preimage (show Continuous fun g => GM.cmp (n := n) (T.mk' v) g from hce ▸ e.continuous),
        fun g hg => (hint g).2 (hU'2 hg), hU1, hU2⟩
      ⟨fun x hx g => by rw [map_mul]; exact hU'3 _ hx _, hinv⟩
    have hLS : L.S = S := l1.trans hL₁S
    have hns : ∀ y ∈ T.sp, y ≠ v := fun y hy h => hv (h ▸ (Finset.mem_filter.1 hy).2)
    have hfv : FitsV T L (Function.update ψ v φ) := by
      refine ⟨l1.trans hfit.S_eq, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_, fun y hy hy' g => ?_⟩
      · by_cases h : y = v
        · subst h; rw [Function.update_self]; exact hφ
        · rw [Function.update_of_ne h]
          by_cases hy' : GM.Split E y
          · exact (hfit.test y (Finset.mem_filter.2 ⟨hy, hy'⟩)).1
          · exact (hbase y hy hy').1
      · rw [Function.update_of_ne (hns y hy)]; exact (hfit.test y hy).2
      · rw [l2, l5, Function.update_of_ne (hns y hy), Function.update_of_ne (hns y hy), Function.update_of_ne (hns y hy)]
        exact hfit.split y hy
      · rw [l2]
        by_cases h : y = v
        · subst h; rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne h, Function.update_of_ne h, hφn y hy hy']
    obtain ⟨𝔢, 𝔣, h𝔢, h𝔣, hgeo⟩ := hG L ν hν
    have heS : 𝔢.S = SE := Set.ext fun y => by rw [h𝔢.2.2.1, hLS]; rfl
    have hfS : 𝔣.S = SF := Set.ext fun y => by rw [h𝔣.2.2.1, hLS]; rfl
    obtain ⟨hAt', hc1, hc2⟩ := hS' 𝔢.S fun y => by rw [h𝔢.2.2.1, hLS]
    have hoff : OffFam F n 𝔢.S 𝔣.S Λ t := by
      rw [heS, hfS]
      exact hOffA SF hSFf
    have hz' : ∀ i, HasTrace (m' v) (ρ i v).ρ f ((d.toReal : ℂ) * z) := fun i => by
      obtain ⟨Λ', t', hA, hΛ, ht⟩ := (hι i).2.1
      rw [hm2']
      exact fibTrace F E σ hσ hp n hn μE μF π P V Λ t hC hAt hW (V₀ i) Λ' t' (hι i).1 ⟨SF, hSFf, hA⟩ hΛ
        (Filter.mem_of_superset hSEf.compl_mem_cofinite fun y hy => ht y hy) v _ τ _ hτ ((hι i).2.2.2 v) f _ hsup
        (((trBasic _ mF τ (LinearEquiv.refl _ _) f).2.2 d hdT).1 z hz)
    filter_upwards [UpperTheory.ConvolutionTheory.ci F E n _ hn hp.pos μE μF θ 𝔢 𝔣 _ hgeo Λ t hc1 hc2 hoff (y₀ ^ (k + 1)) (pow_pos hy₀ _)] with j hj
    rw [oneTerm E n _ hn μE θ 𝔢 V Λ t hV hVθ hAt' _ j,
      hE L _ hfv ν _ 𝔢 hν.1.antitone h𝔢 j _ (Function.update tb v r) (hZ j) (fun y hy => by
        rw [Function.update_of_ne (hns y hy), Function.update_of_ne (hns y hy)]
        exact (htb y (Finset.mem_filter.1 hy).1).2.1 (Finset.mem_filter.1 hy).2) (fun y hy hy' => by
        by_cases h : y = v
        · subst h
          rw [Function.update_self, Function.update_self, hm2]
          have : ∀ Y : Σ ρ : SmIrr (Gw n (T.mk' y).1), (Gw n (T.mk' y).1 →* Gw n (T.mk' y).1) × (ρ.V ≃ₗ[ℂ] ρ.V),
              Y = ⟨τ', s₀, I₀⟩ → HasTwTrace mE Y.1 Y.2.2 φ r := by rintro _ rfl; exact hr
          exact this _ hXv
        · rw [Function.update_of_ne h, Function.update_of_ne h]; exact (htb y hy).2.2 hy'), heS, hfS,
      hF L 𝔣 hLS (fun y _ => by rw [l6]) h𝔣 (fun i => Function.update (s₁ i) v ((d.toReal : ℂ) * z)) (fun i y hy => by
        rw [l3]
        by_cases h : y = v
        · subst h; rw [Function.update_self, Function.update_self]; exact hz' i
        · rw [Function.update_of_ne h, Function.update_of_ne h]; exact hs₁ i y hy) j, hLS, l4,
      Finset.prod_update_of_mem hvT, Finset.prod_update_of_mem hvS] at hj
    simp only [Finset.prod_update_of_mem hvS, Finset.sdiff_singleton_eq_erase] at hj
    have e2 : ∑ i, bF i * ((Z i).map (· ^ j)).sum * ((d.toReal : ℂ) * z * ∏ y ∈ S.erase v, s₁ i y) =
        (d.toReal : ℂ) * z * ∑ i, bF i * ((Z i).map (· ^ j)).sum * ∏ y ∈ S.erase v, s₁ i y := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e2] at hj
    linear_combination hj
  have ht₁ := L₁.test v (hL₁S ▸ hvS)
  obtain ⟨hc1, hc2⟩ := matchCut F E σ hσ hp n hn v (L₁.c v) (L₁.φ v) (L₁.f v)
  have hb1 := hc2 ⟨ht₁.2.2.1, ht₁.2.2.2⟩
  have hb2 : GM.MatchAt σ v (L₁.c v) (fun g => ψ v (GM.cmp (T.mk' v) g)) ((normSet E n v).indicator (L₁.f v)) := by
    rw [← hφn v hvT hv]
    exact @hc1 (@GM.Loc.mat _ _ _ _ _ _ _ _ _ _ _ L₁ v (hL₁S ▸ hvS))
  have hb3 : ∀ g, (normSet E n v).indicator (L₁.f v) g ≠ 0 → g ∈ normSet E n v := fun g hg => Set.mem_of_indicator_ne_zero hg
  obtain ⟨z₀, hz₀⟩ := trEx F n hn π v mF hmF τ hτ _ hb1
  have hr₀ : HasTwTrace mE τ' I₀ (ψ v) (tb v) := by
    have h := (htb v hvT).2.2 hv
    rw [hm2] at h
    have : ∀ Y : Σ ρ : SmIrr (Gw n (T.mk' v).1), (Gw n (T.mk' v).1 →* Gw n (T.mk' v).1) × (ρ.V ≃ₗ[ℂ] ρ.V),
        Y = ⟨τ', s₀, I₀⟩ → HasTwTrace mE Y.1 Y.2.2 (ψ v) (tb v) → HasTwTrace mE τ' I₀ (ψ v) (tb v) := by rintro _ rfl h; exact h
    exact this _ hXv h
  have hr0 := (htb v hvT).1
  have main : ∀ (φ : Gw n (T.mk' v).1 → ℂ) (f : Gw n v → ℂ) (c₁ z r : ℂ), Test φ → Test f →
      GM.MatchAt σ v c₁ (fun g => φ (GM.cmp (T.mk' v) g)) f → (∀ g, f g ≠ 0 → g ∈ normSet E n v) → HasTrace mF τ.ρ f z →
      HasTwTrace mE τ' I₀ φ r → L₁.c v * z₀ ≠ 0 ∧ r * (L₁.c v * z₀) = tb v * (c₁ * z) := by
    intro φ f c₁ z r hφ hf hmat hsup hz hr
    obtain ⟨U₁, a1, a2, a3⟩ := levEx _ _ f (GLnLocal.isOpen_integralGL (v.adicCompletion F) n) (small n v) hf
    obtain ⟨U₂, b1, b2, b3⟩ := levEx _ U₁ _ a1 (small n v) hb1
    obtain ⟨B, hB⟩ := key U₂ b1 (b2.trans a2)
    obtain ⟨j, h0, h1, h2⟩ := ((powNe Z₀ hZ₀ hZ0).and_eventually ((hB φ f c₁ z r hφ hf hmat hsup hz hr fun x hx => a3 x (b2 hx)).and
      (hB (ψ v) _ _ z₀ (tb v) (hbase v hvT hv).1 hb1 hb2 hb3 hz₀ hr₀ b3))).exists
    have hA : cE * (Z₀.map (· ^ j)).sum * ∏ y ∈ T.S.erase v, tb y ≠ 0 :=
      mul_ne_zero (mul_ne_zero hcE h0) (Finset.prod_ne_zero_iff.2 fun y hy => (htb y (Finset.mem_of_mem_erase hy)).1)
    refine ⟨fun h => mul_ne_zero hA hr0 (by rw [h2, h, mul_zero]), mul_left_cancel₀ hA ?_⟩
    linear_combination (L₁.c v * z₀) * h1 - (c₁ * z) * h2
  have hne0 := (main (ψ v) _ _ z₀ (tb v) (hbase v hvT hv).1 hb1 hb2 hb3 hz₀ hr₀).1
  refine ⟨tb v / (L₁.c v * z₀), div_ne_zero hr0 hne0, fun φ f c₁ z hφ hf hmat hsup hz => ?_⟩
  haveI := hmE
  obtain ⟨z', hz'⟩ := (occursBasics E n μE V (T.mk' v).1 mE hV).2.2 τ' hocc' φ hφ
  obtain ⟨r, hr⟩ := (trBasic _ mE τ' I₀ φ).1 z' hz'
  have h := (main φ f c₁ z r hφ hf hmat hsup hz hr).2
  have : tb v / (L₁.c v * z₀) * c₁ * z = r := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hne0, h]; ring
  rw [this]
  exact hr
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.WeakPow
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

open GroundTheory.Global.IdeleGroup PositivityTheory.RgJS

namespace UpperTheory.Gal.InertialTypesAlt.G.WP

variable {K : Type} [Field K] [NumberField K]

private theorem module_local (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    ((GroundTheory.Global.IdeleGroup.ideleModule K (Neutral.B1.localIdele K v x)).1 : ℝ) = ‖(x : v.adicCompletion K)‖ := by
  have : Neutral.B1.localIdele K v x = GroundTheory.Global.IdeleGroup.finiteEmbedding v x := by
    apply Units.ext
    rfl
  rw [this]
  exact GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding v x

private theorem norm_of_val (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) (n : ℤ)
    (h : Valued.v x = WithZero.exp n) : ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ n := by
  rw [FinitePlace.norm_def, h, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  simp [WithZero.log_exp]

private theorem pow_loc {χ : HChar K} {s : ℂ} (h : UpperTheory.ConvolutionTheory.T.IsPow χ s) (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    ((χ.loc v x : ℂˣ) : ℂ) = ((‖(x : v.adicCompletion K)‖ : ℝ) : ℂ) ^ s := by
  rw [← module_local]
  exact h _

private theorem pow_unr {χ : HChar K} {s : ℂ} (h : UpperTheory.ConvolutionTheory.T.IsPow χ s) (v : HeightOneSpectrum (𝓞 K)) : χ.UnrAt v := fun x hx => by
  apply Units.ext
  rw [pow_loc h, norm_of_val v _ 0 (by simpa [Formalism.L2.Host.IsUnitAt] using hx)]
  simp

private theorem pow_val {χ : HChar K} {s : ℂ} (h : UpperTheory.ConvolutionTheory.T.IsPow χ s) (v : HeightOneSpectrum (𝓞 K)) :
    ((χ.val v : ℂˣ) : ℂ) = ((Formalism.ConjugateSelfDual.normV v : ℕ) : ℂ) ^ (-s) := by
  have e : χ.val v = χ.loc v (Formalism.L2.Host.atFin v (Formalism.L2.Host.unif v)) := rfl
  have e2 : (Formalism.ConjugateSelfDual.normV v : ℕ) = Ideal.absNorm v.asIdeal := by
    rw [Formalism.ConjugateSelfDual.normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [e, pow_loc h, norm_of_val v _ (-1) (Formalism.L2.Host.unif_spec v), e2, zpow_neg_one, Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg (by positivity)]
      exact Real.pi_pos.ne), Complex.cpow_neg]
  simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [_root_.NumberField.IsTotallyComplex F] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

private theorem val_pow {χ : HChar F} {χ' : HChar E} {s : ℂ} (h : UpperTheory.ConvolutionTheory.T.IsPow χ s) (h' : UpperTheory.ConvolutionTheory.T.IsPow χ' s)
    (w : HeightOneSpectrum (𝓞 E)) (f : ℕ) (hf : Formalism.ConjugateSelfDual.normV w = Formalism.ConjugateSelfDual.normV (w.under (𝓞 F)) ^ f) :
    χ'.val w = χ.val (w.under (𝓞 F)) ^ f := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, pow_val h, pow_val h', hf, Nat.cast_pow, ← Complex.cpow_nat_mul,
    Complex.natCast_cpow_natCast_mul]

private theorem weak_twist {χ : HChar F} {χ' : HChar E} {s : ℂ} (h : UpperTheory.ConvolutionTheory.T.IsPow χ s) (h' : UpperTheory.ConvolutionTheory.T.IsPow χ' s)
    (π : CuspSub F n) (P : CuspSub E n) (H : WeakBC (Cusp.cx π).sat (Cusp.cx P).sat) :
    WeakBC (Cusp.cx (π.twist χ)).sat (Cusp.cx (P.twist χ')).sat := by
  refine Filter.Eventually.mono H fun w hw f hf => ?_
  obtain ⟨B, hB, hB'⟩ := hw f hf
  refine ⟨B.map (· * χ.val (w.under (𝓞 F))), ?_, ?_⟩
  · have := satake_twist_holds F n (CG.mk π) χ _ B (pow_unr h _) hB
    rwa [CG.twist_mk] at this
  · have := satake_twist_holds E n (CG.mk P) χ' w _ (pow_unr h' _) hB'
    rw [CG.twist_mk] at this
    change (CG.mk (P.twist χ')).HasSat w _
    convert this using 1
    simp [Multiset.map_map, val_pow h h' w f hf, mul_pow]

end UpperTheory.Gal.InertialTypesAlt.G.WP

open UpperTheory.Gal.InertialTypesAlt.G.WP in
theorem UpperTheory.Gal.InertialTypesAlt.G.weakPow :
    UpperTheory.Gal.InertialTypesAlt.G.WeakPow := by
  intro F E _ _ _ _ _ _ _ _ σ _ _ n _ z χ χ' h h' π P H
  exact weak_twist h h' π P H
end

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

theorem UpperTheory.Gal.InertialTypesAlt.G.varTrace :
    UpperTheory.Gal.InertialTypesAlt.G.VarTrace := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn π P hP hW v w hv _ _ _ _ mF mE hmF hmE τ τ' hτ hτ' s I hs hI
  let μE : Measure (normOneGL (K := E) (n := n)) := Measure.haar
  have : μE.IsHaarMeasure :=
    inferInstanceAs (Measure.haar : Measure (normOneGL (K := E) (n := n))).IsHaarMeasure
  have hTwist := UpperTheory.ConvolutionTheory.Dp.exTwist E n μE P hn
  obtain ⟨χ', ⟨z₀, hz'⟩, V, hV⟩ := hTwist
  obtain ⟨hex, htw⟩ := T.powTwist F E
  obtain ⟨χ, hz⟩ := (hex z₀).1
  obtain ⟨hi, hi', h1⟩ := htw z₀ χ χ' hz hz'
  obtain ⟨-, -, -, hconj, -⟩ := h1 n hn
  have hone : ∀ u : PlacesOver E v, u = w := fun u =>
    ((T.places F E hp).2.2.2.1 v hv) w u
  have hW' := weakPow F E σ hσ hp n hn z₀ χ χ' hz hz' π P hW
  obtain ⟨⟨τ₁, hτ₁⟩, he⟩ := locTw F n hn π χ v τ hτ
  obtain ⟨⟨τ₁', hτ₁'⟩, he'⟩ := locTw E n hn P χ' w.1 τ' hτ'
  obtain ⟨e, heT⟩ := he τ₁ hτ₁
  obtain ⟨e', heT'⟩ := he' τ₁' hτ₁'
  obtain ⟨hfix, -⟩ := matchPow F E σ hσ hp n hn z₀ χ χ' hz hz' v w hone
  obtain ⟨-, hmatch⟩ := matchPow F E σ hσ hp n hn (-z₀) χ⁻¹ χ'⁻¹ hi hi' v w hone
  have hI₁ : ∀ g x, (e'.symm.trans (I.trans e')) (τ₁'.ρ g x) = τ₁'.ρ (s g) ((e'.symm.trans (I.trans e')) x) := by
    intro g x
    obtain ⟨y, rfl⟩ := e'.surjective x
    have a := heT' g y
    have b := heT' (s g) (I y)
    rw [hfix s hs g] at b
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rw [← a, ← b, LinearEquiv.symm_apply_apply, map_smul, hI]
  obtain ⟨c, hc, H⟩ := core F E σ hσ hp n hn μE (π.twist χ) (P.twist χ') V hV
    (fun g => hconj P _ (hP g)) hW' v w hv mF mE hmF hmE τ₁ τ₁' hτ₁ hτ₁' s _ hs hI₁
  refine ⟨c, hc, fun φ f c₁ z hφ hf hM hsupp htr => ?_⟩
  have hcE : ∀ g, chiAt n χ'⁻¹ w.1 g * chiAt n χ' w.1 g = 1 := fun g => by
    rw [mul_comm]
    exact (chiBasic E n χ' w.1).2.1 g
  have hcF : ∀ g, chiAt n χ⁻¹ v g * chiAt n χ v g = 1 := fun g => by
    rw [mul_comm]
    exact (chiBasic F n χ v).2.1 g
  have eφ : (fun g => (φ g * chiAt n χ'⁻¹ w.1 g) * chiAt n χ' w.1 g) = φ := by
    funext g
    rw [mul_assoc, hcE, mul_one]
  have ef : (fun g => (f g * chiAt n χ⁻¹ v g) * chiAt n χ v g) = f := by
    funext g
    rw [mul_assoc, hcF, mul_one]
  have htr₁ : HasTrace mF τ₁.ρ (fun g => f g * chiAt n χ⁻¹ v g) z := by
    refine ((trTw _ mF _ τ τ₁ e heT _ z).1).1 ?_
    rw [ef]
    exact htr
  have hsupp₁ : ∀ g, f g * chiAt n χ⁻¹ v g ≠ 0 → g ∈ normSet E n v := fun g hg =>
    hsupp g (left_ne_zero_of_mul hg)
  have key := H (fun g => φ g * chiAt n χ'⁻¹ w.1 g) (fun g => f g * chiAt n χ⁻¹ v g) c₁ z
    ((chiBasic E n χ'⁻¹ w.1).2.2 φ hφ) ((chiBasic F n χ⁻¹ v).2.2 f hf) (hmatch c₁ φ f hM) hsupp₁ htr₁
  have := (((trTw _ mE _ τ' τ₁' e' heT' _ _).2 I).2 key)
  rwa [eφ] at this
