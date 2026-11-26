module

public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsPChartOfFramedPoint
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormPlus
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SecScalOfIsPullSec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAlgebraFacts
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevMoveOfFrOver
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculus

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCmTypeEmbeddingsIntoValuationRing
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCmTypeEmbeddingsIntoValuationRing
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem exists_ringHom_ringOfIntegers_lift {E : Type} [Field E] [NumberField E] {V K : Type} [CommRing V]
    [IsDomain V] [IsIntegrallyClosed V] [Field K] [Algebra V K] [IsFractionRing V K] (φ : 𝓞 E →+* K) :
    ∃ ψ : 𝓞 E →+* V, ∀ a, algebraMap V K (ψ a) = φ a := by
  have hint : ∀ a, ∃ x : V, algebraMap V K x = φ a := by
    intro a
    have h1 : IsIntegral ℤ a := Algebra.IsIntegral.isIntegral a
    have h2 : IsIntegral ℤ (φ a) := map_isIntegral_int φ h1
    exact IsIntegrallyClosed.isIntegral_iff.1 h2.tower_top
  choose f hf using hint
  have hinj := IsFractionRing.injective V K
  refine ⟨{ toFun := f
            map_one' := hinj (by rw [hf, map_one, map_one])
            map_mul' := fun a b => hinj (by rw [map_mul, hf, hf, hf, map_mul])
            map_zero' := hinj (by rw [hf, map_zero, map_zero])
            map_add' := fun a b => hinj (by rw [map_add (f := _), hf, hf, hf, map_add (f := _)]) }, hf⟩

theorem exists_types_valuationRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (p : ℕ) [Fact p.Prime] (X : ValExt T p), ∃ (τT : (E →+* ℂ) → (𝓞 E →+* T.V)), (∀ τ a, algebraMap T.V T.Fr (τT τ a) = io (embK c τ a)) ∧ IsTypes X io (fun τ => X.ι.comp (τT τ)) ∧ Function.Injective (fun τ => X.ι.comp (τT τ)) ∧ (∀ τ τ', τ (H.rt : E) = τ' (H.rt : E) ↔ X.ι (τT τ H.rt) = X.ι (τT τ' H.rt)) ∧ ∀ τ a, τT (ComplexEmbedding.conjugate τ) a = τT τ (H.bar a) := by
  intro E _ _ _ H l c T io p _ X
  have hinj := IsFractionRing.injective T.V T.Fr
  choose σV hσV using fun τ : E →+* ℂ =>
    exists_ringHom_ringOfIntegers_lift (V := T.V) (io.comp (embK c τ))
  have hσV' : ∀ τ a, algebraMap T.V T.Fr (σV τ a) = io (embK c τ a) := hσV
  have hT : ∀ τ a, algebraMap X.O X.C (X.ι (σV τ a)) = X.ιF (io (embK c τ a)) := by
    intro τ a
    rw [← X.comp, hσV']
  have key : ∀ τ τ' (a : 𝓞 E), τ (a : E) = τ' (a : E) ↔ X.ι (σV τ a) = X.ι (σV τ' a) := by
    intro τ τ' a
    constructor
    · intro h
      have h1 : embK c τ a = embK c τ' a := by
        apply Subtype.ext
        rw [embK_coe, embK_coe]
        exact h
      have h2 : σV τ a = σV τ' a := hinj (by rw [hσV', hσV', h1])
      rw [h2]
    · intro h
      have h1 : embK c τ a = embK c τ' a :=
        io.injective (X.ιF.injective (by rw [← hT, ← hT, h]))
      exact congrArg (fun z : c.F => (z : ℂ)) h1
  refine ⟨σV, hσV', hT, ?_, fun τ τ' => key τ τ' H.rt, fun τ a => ?_⟩
  · intro τ τ' h
    refine IsFractionRing.ringHom_ext (A := 𝓞 E) fun a => ?_
    exact (key τ τ' a).2 (RingHom.congr_fun h a)
  · have h : embK c (ComplexEmbedding.conjugate τ) a = embK c τ (H.bar a) := by
      apply Subtype.ext
      rw [embK_coe, embK_coe, ComplexEmbedding.conjugate_coe_eq, H.bar_eq,
        IsCMField.complexEmbedding_complexConj]
    exact hinj (by rw [hσV', hσV', h])

end GlobalTheory.CharDepth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCmTypeEmbeddingsIntoValuationRingStatement
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmType_embeddings_into_valuation_ring : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (p : ℕ) [Fact p.Prime] (X : ValExt T p), ∃ (τT : (E →+* ℂ) → (𝓞 E →+* T.V)), (∀ τ a, algebraMap T.V T.Fr (τT τ a) = io (embK c τ a)) ∧ IsTypes X io (fun τ => X.ι.comp (τT τ)) ∧ Function.Injective (fun τ => X.ι.comp (τT τ)) ∧ (∀ τ τ', τ (H.rt : E) = τ' (H.rt : E) ↔ X.ι (τT τ H.rt) = X.ι (τT τ' H.rt)) ∧ ∀ τ a, τT (ComplexEmbedding.conjugate τ) a = τT τ (H.bar a) := by
  first | exact @GlobalTheory.CharDepth.exists_types_valuationRing | exact GlobalTheory.CharDepth.exists_types_valuationRing | (intros; apply GlobalTheory.CharDepth.exists_types_valuationRing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralFramedPointOfLevelMove
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralFramedPointOfLevelMove
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormTies.LevelMove

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg.ChartInhab

attribute [local instance] Over.cartesianMonoidalCategory

theorem gs_of_isoMaps {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)}
    {σ : LB.Sec L'} {s : LB.Sec (L.pull F)} (h : IsoMaps w σ s) (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι)
    (k : L'.ι) (hj : F (r z) ∈ L.U j) (hk : r z ∈ L'.U k) :
    gs r z _ (s.f (fun _ => j)) = (Geo.Tor.gw w r z j k).val * gs r z _ (σ.f k) := by
  have hz : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
  have a := congrArg (gs r z _) (h (fun _ => j) k)
  exact (gs_res _ z _ hz _).symm.trans (a.trans ((gs_mul _ z _ hz _ _).trans
    (congrArg₂ (· * ·) (gs_unit _ z _ hz _) (gs_res _ z _ hz _))))

theorem integral_of_levR : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La)) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ y y' : FrPt Xo c T.Fr, levR (Xo := Xo) (c := c) g y y' → Integral T io y → Integral T io y' := by
  intro E _ _ _ H Dw l Xo c gl T io
  letI := io.toAlgebra
  rintro y y' ⟨ρ, ν, -, -, hx, hu, pm, w, p₁, p₂, hw, hs⟩
    ⟨G, t', m1, m2, ⟨ub, b₁, b₂, b₃, b₄⟩, θ, hθ, w1, w2, σ, s1, θ2, r₁, r₂, i₁, i₂, hp, hg⟩
  obtain ⟨n, hn, w', hw', tri⟩ := exists_comp_rig ν m1 y'.x hx ⟨hw.1, hw.2.1⟩ r₁
  have g' := (isGen_iff w').1 hw'.1
  obtain ⟨s', hs'⟩ := thf_secUp g' Xo.univ.t.PP.isLB t'.PP.isLB σ
  refine ⟨G, t', n, m2, ⟨ub, b₁, b₂, b₃, fun τ i => ?_⟩, θ, hθ, w', w2, σ, s', θ2, hw', r₂, ?_, i₂, hp, ?_⟩
  · obtain ⟨u', h₁, h₂⟩ := b₄ τ i
    exact ⟨u', by rw [hn, ← Category.assoc, h₁, hu], h₂⟩
  · exact fun (i : PUnit → Xo.univ.t.PP.L.ι) k => fn_ext fun p hp =>
      (gs_res _ p _ hp _).trans ((hs' _ (𝟙 _) p i k hp.1 hp.2).trans (Eq.symm ((gs_mul _ p _ hp _ _).trans
        (congrArg₂ (· * ·) (gs_unit (𝟙 _) p _ hp _) (gs_res _ p _ hp _)))))
  · intro q e₁ e₂ (J : PUnit → Xo.univ.t.PP.L.ι) hJ
    refine fn_ext fun p hp => ?_
    obtain ⟨k, hk⟩ := exists_chart t'.PP.isLB p
    obtain ⟨i, hi⟩ := exists_chart Xo.univ.t.PP.isLB (m1.φ p)
    have hp' : ν.φ (m1.φ p) ∈ Xo.univ.t.PP.L.U (J PUnit.unit) :=
      (congrArg (fun q => q p ∈ Xo.univ.t.PP.L.U (J PUnit.unit)) hn).mp (mem_pull.1 hp)
    have eg : 𝟙 _ ≫ q = (𝟙 _ ≫ toGx m1) ≫ pm := by
      rw [Category.id_comp, Category.id_comp]
      apply FramedBaseChange.pulledGroup_hom_ext
      · rw [Category.assoc, p₂, e₁, hn, ← Category.assoc, toGx_snd]
      · rw [Category.assoc, p₁, e₂, toGx_fst]
    let W : (Gx y.x).Opens := (snd (Over.mk y.x) Xo.univ.t.G).left ⁻¹ᵁ
      ((LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => J PUnit.unit), i))
    have h₁ : W ≤ pm ⁻¹ᵁ (PPx y'.x).U (fun _ => J PUnit.unit) := fun z hz => Set.mem_iInter.2 fun _ =>
      (congrArg (fun u => u z ∈ Xo.univ.t.PP.L.U (J PUnit.unit)) p₂).mpr (mem_pull.1 hz.1)
    have h₂ : W ≤ (PPx y.x).U (fun _ => i) := fun z hz => Set.mem_iInter.2 fun _ => hz.2
    have es : (𝟙 _ ≫ toGx m1) ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = 𝟙 _ ≫ m1.φ := by
      rw [Category.assoc, toGx_snd]
    have hz₀ : (𝟙 _ ≫ m1.φ) p ∈ (LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => J PUnit.unit), i) :=
      ⟨mem_pull.2 hp', hi⟩
    have hz : (𝟙 _ ≫ toGx m1) p ∈ W :=
      (congrArg (fun u => u p ∈ (LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => J PUnit.unit), i))
        es).mpr hz₀
    have e := congrArg (gs (𝟙 _ ≫ toGx m1) p W) (hs (J PUnit.unit) i W rfl le_rfl h₁ h₂)
    rw [gs_appLE pm _ _ h₁ _ p hz, gs_mul _ p W hz, gs_appLE _ _ _ _ _ p hz, gs_res _ p h₂ hz, es,
      gs_unit _ p _ hz₀] at e
    have le : (Xo.univ.t.PP.L.pull m1.φ).U (fun _ => i) ≤ toGx m1 ⁻¹ᵁ (PPx y.x).U (fun _ => i) :=
      fun z hz => le_toGx m1 i (mem_pull.1 hz)
    have k₂ : gs (𝟙 _) p _ (s1.f (fun _ => i)) = gs (𝟙 _ ≫ toGx m1) p ((PPx y.x).U (fun _ => i)) (y.s.f (fun _ => i)) :=
      (congrArg (gs (𝟙 _) p _) (hg (toGx m1) (toGx_snd m1) (toGx_fst m1) (fun _ => i) le)).trans
        (gs_appLE (toGx m1) _ _ le (𝟙 _) p (mem_pull.2 hi) _)
    have k₃ := gs_of_isoMaps i₁ _ (𝟙 _) p i k hi hk
    rw [hs' _ (𝟙 _) p J k hp hk, gs_appLE q _ _ hJ (𝟙 _) p hp, eg, e, ← k₂, k₃,
      tri _ (𝟙 _) p _ i k hp' hi hk, Units.val_mul, _root_.mul_assoc]
    rfl

end GlobalTheory.FormTies.LevelMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralFramedPointOfLevelMoveStatement
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_framedPoint_of_level_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La)) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ y y' : FrPt Xo c T.Fr, levR (Xo := Xo) (c := c) g y y' → Integral T io y → Integral T io y' := by
  first | exact @GlobalTheory.FormTies.LevelMove.integral_of_levR | exact GlobalTheory.FormTies.LevelMove.integral_of_levR | (intros; apply GlobalTheory.FormTies.LevelMove.integral_of_levR <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLocalHomValuationExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsLocalHomExtension
namespace GlobalTheory.LocalHomExtension

theorem exists_isLocalHom_extension {A B O C : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [IsLocalRing B] [CommRing O] [IsLocalRing O] [Field C]
    [IsAlgClosed C] [Algebra O C] (v : Valuation C NNReal) (hv : Valuation.Integers v O)
    (φ : A →+* B) (hφ : Function.Injective φ) (hint : φ.IsIntegral)
    (ι : A →+* O) [IsLocalHom ι]
    (hι : Function.Injective ((algebraMap O C).comp ι)) :
    ∃ ι' : B →+* O, IsLocalHom ι' ∧ ι'.comp φ = ι := by
  let : Algebra A B := φ.toAlgebra
  let : Algebra A O := ι.toAlgebra
  let : Algebra A C := ((algebraMap O C).comp ι).toAlgebra
  have : IsScalarTower A O C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr hφ
  have : Module.IsTorsionFree A C := Module.isTorsionFree_iff_algebraMap_injective.mpr hι
  have : Algebra.IsIntegral A B := ⟨hint⟩

  let f : B →ₐ[A] C := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])

  have hO : ∀ b : B, ∃ o : O, algebraMap O C o = f b := fun b => by
    have h1 : IsIntegral A (f b) := (Algebra.IsIntegral.isIntegral b).map f
    exact hv.exists_of_le_one (hv.mem_of_integral h1.tower_top)
  choose g hg using hO
  have inj := hv.hom_inj
  let ι' : B →+* O :=
    { toFun := g
      map_one' := inj (by rw [hg, map_one, map_one])
      map_mul' := fun x y => inj (by rw [hg, map_mul, map_mul, hg, hg])
      map_zero' := inj (by rw [hg, map_zero, map_zero])
      map_add' := fun x y => inj (by rw [hg, map_add (f := _), map_add (f := _), hg, hg]) }
  have hcomp : ι'.comp φ = ι := by
    ext a
    apply inj
    show algebraMap O C (g (φ a)) = algebraMap O C (ι a)
    rw [hg]
    exact f.commutes a
  refine ⟨ι', ?_, hcomp⟩

  have hA : (IsLocalRing.maximalIdeal O).comap ι = IsLocalRing.maximalIdeal A :=
    ((IsLocalRing.local_hom_TFAE ι).out 1 5).mp (inferInstance : IsLocalHom ι)
  have hp : (((IsLocalRing.maximalIdeal O).comap ι').comap (algebraMap A B)).IsMaximal := by
    rw [Ideal.comap_comap, show ι'.comp (algebraMap A B) = ι from hcomp, hA]
    exact IsLocalRing.maximalIdeal.isMaximal A
  have hpm := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap A B)
    (show (algebraMap A B).IsIntegral from hint) ((IsLocalRing.maximalIdeal O).comap ι') hp
  exact ((IsLocalRing.local_hom_tfae ι').out 1 5).mpr (IsLocalRing.eq_maximalIdeal hpm)

end GlobalTheory.LocalHomExtension
end

set_option autoImplicit false

namespace GlobalTheory.CharDepth

open IsLocalRing Formalism.L2.Pj

theorem exists_local_extension_of_integral {A B O C : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [IsLocalRing B] [CommRing O] [IsLocalRing O] [Field C] [IsAlgClosed C]
    [Algebra O C] (v : Valuation C NNReal) (hv : v.Integers O) (φ : A →+* B) (hφ : Function.Injective φ)
    (hint : φ.IsIntegral) (ι : A →+* O) [IsLocalHom ι]
    (hι : Function.Injective ((algebraMap O C).comp ι)) :
    ∃ ι' : B →+* O, IsLocalHom ι' ∧ ι'.comp φ = ι := by
  first
  | (rename_i h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 h_12 h_13 h_14 h_21; revert A B O C h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 h_12 h_13 h_14 v hv φ hφ hint ι h_21 hι; exact @_root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension)
  | exact @_root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension
  | exact _root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension
  | (apply _root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension <;> assumption)
  | (intros; apply _root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LocalHomExtension.exists_isLocalHom_extension ..)

theorem ValExt.exists_local_extension :
    ∀ (T T' : CDVR) (φ : T.V →+* T'.V), Function.Injective φ → φ.Finite → ∀ (p : ℕ) [Fact p.Prime]
      (X : ValExt T p), ∃ ι' : T'.V →+* X.O, IsLocalHom ι' ∧ ι'.comp φ = X.ι := by
  intro T T' φ hφ hfin p _ X
  haveI := X.ι_local
  refine exists_local_extension_of_integral X.v X.ints φ hφ hfin.to_isIntegral X.ι ?_
  have h : (algebraMap X.O X.C).comp X.ι = X.ιF.comp (algebraMap T.V T.Fr) := by
    ext x; exact (X.comp x).symm
  rw [h, RingHom.coe_comp]
  exact X.ιF.injective.comp (IsFractionRing.injective T.V T.Fr)

end GlobalTheory.CharDepth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmallTorsionKilledByPrimePowers
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmallTorsionKilledByPrimePowers
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.SmallTors

variable {q : ℕ} [hq : Fact q.Prime]

lemma norm_zc' (a : ℤ_[q]) : ‖zc a‖ = ‖a‖ := by
  unfold zc
  rw [norm_algebraMap']
  rfl

lemma norm_nat_coprime {m : ℕ} (hm : Nat.Coprime m q) : ‖(m : ℂ_[q])‖ = 1 := by
  have h0 : (m : ℂ_[q]) = zc (m : ℤ_[q]) := by simp [zc]
  rw [h0, norm_zc']
  have h1 : ¬ ‖((m : ℤ) : ℤ_[q])‖ < 1 := by
    rw [PadicInt.norm_int_lt_one_iff_dvd]
    have := (Nat.Prime.coprime_iff_not_dvd hq.out).1 hm.symm
    exact_mod_cast this
  push_cast at h1
  exact le_antisymm (PadicInt.norm_le_one _) (not_lt.1 h1)

lemma norm_q_pow (n : ℕ) : ‖((q : ℂ_[q])) ^ n‖ = (q : ℝ) ^ (-(n : ℤ)) := by
  have h0 : (q : ℂ_[q]) ^ n = zc ((q : ℤ_[q]) ^ n) := by simp [zc]
  rw [h0, norm_zc', PadicInt.norm_p_pow]

lemma norm_eq_one {ξ : ℂ_[q]} (h : ‖ξ - 1‖ < 1) : ‖ξ‖ = 1 := by
  have : ξ = (ξ - 1) + 1 := by ring
  rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact h.ne), norm_one]
  exact max_eq_right h.le

lemma norm_pow_sub_one {ξ : ℂ_[q]} (h : ‖ξ - 1‖ < 1) (n : ℕ) : ‖ξ ^ n - 1‖ < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : ξ ^ (n + 1) - 1 = ξ * (ξ ^ n - 1) + (ξ - 1) := by ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ h)
    rw [norm_mul, norm_eq_one h, one_mul]; exact ih

lemma norm_geom_sub {ξ : ℂ_[q]} (h : ‖ξ - 1‖ < 1) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, ξ ^ i - n‖ < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have : ∑ i ∈ Finset.range (n + 1), ξ ^ i - ((n + 1 : ℕ) : ℂ_[q])
        = (∑ i ∈ Finset.range n, ξ ^ i - n) + (ξ ^ n - 1) := by
      rw [Finset.sum_range_succ]; push_cast; ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ih (norm_pow_sub_one h n))

lemma eq_one_of_pow {ξ : ℂ_[q]} (h : ‖ξ - 1‖ < 1) {m : ℕ} (hm : Nat.Coprime m q) (h1 : ξ ^ m = 1) :
    ξ = 1 := by
  have h2 := geom_sum_mul ξ m
  rw [h1, sub_self, mul_eq_zero] at h2
  rcases h2 with h2 | h2
  · have h3 := norm_geom_sub h m
    rw [h2, zero_sub, norm_neg, norm_nat_coprime hm] at h3
    exact absurd h3 (lt_irrefl _)
  · exact sub_eq_zero.1 h2

lemma inOK_int (d : ℕ) (k : ℤ) : InOK d (k : ℂ) := ⟨k, 0, by simp⟩

lemma inOK_of_eq {d : ℕ} {x y : ℂ} (h : InOK d x) (e : x = y) : InOK d y := e ▸ h

end GlobalTheory.MomOne.SmallTors

namespace GlobalTheory.MomOne
open SmallTors

theorem smallTors : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → (∀ p p', M.Small p → M.Small p' → M.Small (p + p') ∧ M.Small (-p)) ∧ (∀ (p : ℂ) (N : ℕ), 0 < N → InOK d ((N : ℂ) * p) → M.Small p → ∃ (n : ℕ) (ζ : ℂ_[q]), ζ ^ (q ^ n) = 1 ∧ M.At ω ζ p ∧ ∀ α, InOK d α → ‖M.ι α‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → InOK d (α * p)) ∧ (∀ p, PrimeTo d q p → M.Small p → InOK d p) ∧ ∀ (p α s : ℂ), InOK d α → α ≠ 0 → PrimeTo d q s → InOK d (α * p + s - 1 / 2) → M.Small p → q ≠ 2 ∧ InOK d (s - 1 / 2) := by
  intro d q hq M ω hd hd16 hsp hL hM
  obtain ⟨hadd, hcm⟩ := GlobalTheory.T.multiplicativeCoord_add_and_complexMul q M ω hM
  obtain ⟨hex, hex', huniq, hlat, h10⟩ := GlobalTheory.T.smallPoint_multiplicativeCoordinate_existsUnique q M ω hM
  obtain ⟨⟨-, -, hring⟩, halg, -, -, hhalf, -, -⟩ := okArith d q M.ι hd hd16 hsp
  have iadd : ∀ {a b}, InOK d a → InOK d b → InOK d (a + b) := fun ha hb => (hring _ _ ha hb).1
  have imul : ∀ {a b}, InOK d a → InOK d b → InOK d (a * b) := fun ha hb => (hring _ _ ha hb).2.1
  have iconj : ∀ {a}, InOK d a → InOK d (conj a) := fun ha => (hring _ _ ha ha).2.2.2
  have one_iff : ∀ p, M.At ω 1 p ↔ InOK d p := by
    intro p
    rw [hlat 1 0 p h10, zero_sub, neg_mem_iff, hL]
  have hpow : ∀ ζ p (N : ℕ), M.At ω ζ p → M.At ω (ζ ^ N) ((N : ℂ) * p) := by
    intro ζ p N h
    induction N with
    | zero => simpa using h10
    | succ N ih =>
      have := hadd _ _ _ _ ih h
      rw [pow_succ]; push_cast; rw [add_mul, one_mul]; exact this
  have htors : ∀ ζ p (N : ℕ), M.At ω ζ p → InOK d ((N : ℂ) * p) → ζ ^ N = 1 :=
    fun ζ p N h hN => huniq _ _ _ (hpow ζ p N h) ((one_iff _).2 hN)
  have h2 : ∀ (p : ℂ) (N : ℕ), 0 < N → InOK d ((N : ℂ) * p) → M.Small p → ∃ (n : ℕ) (ζ : ℂ_[q]),
      ζ ^ (q ^ n) = 1 ∧ M.At ω ζ p ∧
        ∀ α, InOK d α → ‖M.ι α‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → InOK d (α * p) := by
    intro p N hN hNp hp
    obtain ⟨ζ, hζ⟩ := hex' p hp
    obtain ⟨n, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' q hq.out.ne_one
    have hm' : Nat.Coprime m q := ((Nat.Prime.coprime_iff_not_dvd hq.out).2 hm).symm
    have hz : ζ ^ (q ^ n) = 1 := by
      refine eq_one_of_pow (norm_pow_sub_one hζ.2.1 _) hm' ?_
      rw [← pow_mul]; exact htors _ _ _ hζ hNp
    refine ⟨n, ζ, hz, hζ, fun α hα hn => ?_⟩
    obtain ⟨⟨a, ha⟩, -⟩ := halg α hα
    have := hcm α a n 0 ζ p (fun l hl => (hL _).2 (imul hα ((hL _).1 hl))) ha
      (by rw [ha, norm_zc'] at hn; simpa using hn) hz hζ
    rw [pow_zero] at this
    exact (one_iff _).1 this
  refine ⟨?_, h2, ?_, ?_⟩
  · intro p p' hp hp'
    obtain ⟨ζ, hζ⟩ := hex' p hp
    obtain ⟨ζ', hζ'⟩ := hex' p' hp'
    refine ⟨(hadd _ _ _ _ hζ hζ').1, ?_⟩
    have hn : ‖ζ‖ = 1 := norm_eq_one hζ.2.1
    have h0 : ζ ≠ 0 := by rintro rfl; simp at hn
    have hinv : ‖ζ⁻¹ - 1‖ < 1 := by
      have : ζ⁻¹ - 1 = -(ζ⁻¹ * (ζ - 1)) := by field_simp; ring
      rw [this, norm_neg, norm_mul, norm_inv, hn, inv_one, one_mul]; exact hζ.2.1
    obtain ⟨r, hr⟩ := hex _ hinv
    have h3 := hadd _ _ _ _ hr hζ
    rw [inv_mul_cancel₀ h0, one_iff, ← hL] at h3
    exact ((hlat _ r (-p) hr).2 (by rwa [sub_neg_eq_add])).1
  · rintro p ⟨s, -, hsq, hsp⟩ hp
    obtain ⟨ζ, hζ⟩ := hex' p hp
    have := eq_one_of_pow hζ.2.1 hsq (htors _ _ _ hζ hsp)
    subst this
    exact (one_iff _).1 hζ
  · rintro p α s hα hα0 ⟨t, ht, htq, hts⟩ hin hp
    obtain ⟨-, ⟨N, hN⟩, -⟩ := halg α hα
    have hN0 : N ≠ 0 := by
      rintro rfl
      have : α * conj α = 0 := by simpa using hN.symm
      rcases mul_eq_zero.1 this with h | h
      · exact hα0 h
      · exact hα0 (by simpa using h)
    have h2t : InOK d (((2 * t : ℕ) : ℂ) * (s - 1 / 2)) :=
      inOK_of_eq (iadd (imul (inOK_int d 2) hts) (inOK_int d (-t))) (by push_cast; ring)
    have hNp : InOK d (((2 * t * N : ℕ) : ℂ) * p) := by
      refine inOK_of_eq (imul (iconj hα) (iadd (imul (inOK_int d (2 * t)) hin)
        (imul (inOK_int d (-1)) h2t))) ?_
      push_cast; rw [hN]; ring
    obtain ⟨n, ζ, -, -, hk⟩ := h2 p _ (by positivity) hNp hp
    have hβ : ∀ β, InOK d β → ‖M.ι β‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → InOK d (β * (s - 1 / 2)) := by
      intro β hβ hn
      refine inOK_of_eq (iadd (imul hβ hin) (imul (inOK_int d (-1)) (imul hα (hk β hβ hn)))) ?_
      push_cast; ring
    have hq2 : q ≠ 2 := by
      intro h
      obtain ⟨β, hβ1, hβ2, hβ3⟩ := hhalf n
      apply hβ3
      have hodd : Odd t := by
        rw [h] at htq; exact Nat.coprime_two_right.1 htq
      obtain ⟨k, hk'⟩ := hodd
      have hk2 : (t : ℂ) = 2 * k + 1 := by exact_mod_cast hk'
      refine inOK_of_eq (iadd (iadd (imul hβ1 hts) (imul (inOK_int d (-t)) (hβ β hβ1 hβ2)))
        (imul (inOK_int d (-k)) hβ1)) ?_
      push_cast; rw [hk2]; ring
    refine ⟨hq2, ?_⟩
    have hc : Nat.Coprime (2 * t) (q ^ n) := by
      refine Nat.Coprime.pow_right n (Nat.Coprime.mul_left ?_ htq)
      exact (Nat.coprime_primes Nat.prime_two hq.out).2 hq2.symm
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hc
    have hab' : (a : ℂ) * ((2 * t : ℕ) : ℂ) + b * (q : ℂ) ^ n = 1 := by exact_mod_cast hab
    have h3 := hβ ((q : ℂ) ^ n) (inOK_of_eq (inOK_int d (q ^ n)) (by push_cast; rfl))
      (by rw [map_pow, map_natCast, norm_q_pow])
    refine inOK_of_eq (iadd (imul (inOK_int d a) h2t) (imul (inOK_int d b) h3)) ?_
    linear_combination (s - 1 / 2) * hab'

end GlobalTheory.MomOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmallTorsionKilledByPrimePowersStatement
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallTorsion_killed_by_prime_powers : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → (∀ p p', M.Small p → M.Small p' → M.Small (p + p') ∧ M.Small (-p)) ∧ (∀ (p : ℂ) (N : ℕ), 0 < N → InOK d ((N : ℂ) * p) → M.Small p → ∃ (n : ℕ) (ζ : ℂ_[q]), ζ ^ (q ^ n) = 1 ∧ M.At ω ζ p ∧ ∀ α, InOK d α → ‖M.ι α‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → InOK d (α * p)) ∧ (∀ p, PrimeTo d q p → M.Small p → InOK d p) ∧ ∀ (p α s : ℂ), InOK d α → α ≠ 0 → PrimeTo d q s → InOK d (α * p + s - 1 / 2) → M.Small p → q ≠ 2 ∧ InOK d (s - 1 / 2) := by
  first | exact @GlobalTheory.MomOne.smallTors | exact GlobalTheory.MomOne.smallTors | (intros; apply GlobalTheory.MomOne.smallTors <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonemptyClosedValuedExtensionOfCDVR
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonemptyClosedValuedExtensionOfCDVR
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct

namespace GlobalTheory.CharDepth

theorem nonempty_valExt :
    ∀ (T : CDVR) (p : ℕ) [Fact p.Prime], ¬ IsUnit (p : T.V) → Nonempty (ValExt T p) := by
  intro T p hp hu
  have hp0 : (p : T.V) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hr0 : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
  have hr1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  obtain ⟨C, _, _, _, _, _, hC, hCp⟩ :=
    exists_complete_isAlgClosed_of_isDiscreteValuationRing T.V T.Fr hp0
      ((IsLocalRing.mem_maximalIdeal _).2 hu) hr0 hr1
  rw [map_natCast] at hCp
  have : CharZero T.Fr := charZero_of_injective_ringHom (IsFractionRing.injective T.V T.Fr)
  have : CharZero C := charZero_of_injective_ringHom (algebraMap T.Fr C).injective
  have hCp' : ‖(p : C)‖ = (p : ℝ)⁻¹ := by rwa [map_natCast] at hCp
  let v : Valuation C NNReal := NormedField.valuation
  have hO : v.Integers v.integer := Valuation.integer.integers v
  have hmem : ∀ x : C, ‖x‖ ≤ 1 → x ∈ v.integer := fun x hx => by
    change ‖x‖₊ ≤ 1
    exact_mod_cast hx
  have hpO : ‖algebraMap v.integer C (p : v.integer)‖ < 1 := by
    rw [map_natCast, hCp']; exact hr1
  haveI : Fact (¬ IsUnit (p : v.integer)) :=
    ⟨fun h => hpO.ne ((NormIntegers.isUnit_iff_norm_eq_one hO).1 h)⟩
  haveI := NormIntegers.isAdicComplete_span_singleton hO hpO
  haveI := NormIntegers.isLocalRing hO
  obtain ⟨j, hj⟩ := exists_padic_isometry (C := C) p hCp'
  letI : Algebra ℤ_[p] v.integer :=
    ((j.comp PadicInt.Coe.ringHom).codRestrict v.integer fun x =>
      hmem _ ((hj _).trans_le x.2)).toAlgebra
  have hf : ∀ a : T.V, ‖algebraMap T.Fr C (algebraMap T.V T.Fr a)‖ ≤ 1 := fun a => (hC _).2 ⟨a, rfl⟩
  let ι : T.V →+* v.integer :=
    ((algebraMap T.Fr C).comp (algebraMap T.V T.Fr)).codRestrict v.integer fun a => hmem _ (hf a)
  have hι : IsLocalHom ι := by
    refine ⟨fun a ha => ?_⟩
    have h1 : ‖algebraMap T.Fr C (algebraMap T.V T.Fr a)‖ = 1 :=
      (NormIntegers.isUnit_iff_norm_eq_one hO).1 ha
    have ha0 : algebraMap T.V T.Fr a ≠ 0 := fun h => by simp [h] at h1
    obtain ⟨b, hb⟩ := (hC (algebraMap T.V T.Fr a)⁻¹).1 (by rw [map_inv₀, norm_inv, h1, inv_one])
    refine IsUnit.of_mul_eq_one b (IsFractionRing.injective T.V T.Fr ?_)
    rw [map_mul, hb, mul_inv_cancel₀ ha0, map_one]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  have hpF : (p : T.Fr) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hzp := ArcQ.norm_map_eq_zpow_vV (algebraMap T.Fr C) hf hπ hpF
  have he : (vV T.V (p : T.Fr) : ℝ) ≠ 0 := by
    intro h
    have h' : vV T.V (p : T.Fr) = 0 := by exact_mod_cast h
    rw [h', zpow_zero, hCp] at hzp
    exact hr1.ne hzp
  refine ⟨{ C := C, v := v, O := v.integer, ints := hO, ι := ι, ι_local := hι,
            ιF := algebraMap T.Fr C, comp := fun _ => rfl, val := fun x hx => ?_ }⟩
  change ‖algebraMap T.Fr C x‖ = ‖(p : C)‖ ^ _
  rw [← map_natCast (algebraMap T.Fr C) p, hzp, ArcQ.norm_map_eq_zpow_vV (algebraMap T.Fr C) hf hπ hx,
    ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul (norm_nonneg _), mul_div_cancel₀ _ he]

end GlobalTheory.CharDepth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonemptyClosedValuedExtensionOfCDVRStatement
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_closedValuedExtensionOfCDVR : ∀ (T : CDVR) (p : ℕ) [Fact p.Prime], ¬ IsUnit (p : T.V) → Nonempty (ValExt T p) := by
  first | exact @GlobalTheory.CharDepth.nonempty_valExt | exact GlobalTheory.CharDepth.nonempty_valExt | (intros; apply GlobalTheory.CharDepth.nonempty_valExt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalFormActualOperatorsAlgebraicHypotheses
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalFormActualOperatorsAlgebraicHypotheses
namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem ggi_commute_siteOps {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r) :
    ∀ y ∈ TL.siteOps L, Commute L.GGi y := by
  intro y hy
  simp only [TL.siteOps, Set.mem_union, Set.mem_range] at hy
  rcases hy with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩
  · exact (L.p_GGi l).symm
  · exact (L.pb_GGi l).symm
  all_goals exact L.fns_comm _ (Or.inr (by simp)) _ (by simp)

theorem kappa_commute_of_qq {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {P : M.Par} (hP : P.OK)
    (d : Q.NFData P A) {g : A} (hg : g ∈ TL.siteOps d.L) (hq : ∀ Y, Commute (d.QQ Y 1 1) g)
    (f : M.Ty P → ℂ) : Commute (d.κ f) g := by
  classical
  obtain ⟨Y₀, hY₀⟩ := P5.Kfp.sep_real hP
  have hp : ∀ ρ, (Lagrange.interpolate Finset.univ (fun ρ : M.Ty P => M.xC P ρ (Y₀ : ℂ)) f).eval
      (M.xC P ρ (Y₀ : ℂ)) = f ρ := fun ρ =>
    Lagrange.eval_interpolate_at_node (v := fun ρ : M.Ty P => M.xC P ρ (Y₀ : ℂ)) f hY₀.injOn (Finset.mem_univ ρ)
  rw [P5.Kfp.kappa_aeval d (Y₀ : ℂ) _ f hp]
  have e : d.x (Y₀ : ℂ) = d.L.GGi * d.QQ (Y₀ : ℂ) 1 1 := by
    have h : d.QQ (Y₀ : ℂ) 1 1 = d.L.GG * d.x (Y₀ : ℂ) := rfl
    rw [h, ← mul_assoc, d.L.GGi_GG, one_mul]
  have hx : Commute (d.x (Y₀ : ℂ)) g := by
    rw [e]
    exact (ggi_commute_siteOps d.L g hg).mul_left (hq _)
  generalize Lagrange.interpolate Finset.univ (fun ρ : M.Ty P => M.xC P ρ (Y₀ : ℂ)) f = p
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _)]; exact hp.add_left hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial]
    exact (Algebra.commute_algebraMap_left a g).mul_left (hx.pow_left n)

theorem hatHyp_and_tie_of_isNF :
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
      [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
      (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r)
      (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)),
      P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → HatHyp d ∧ Comparison₂ d L st (M.sgn P l0) := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hN
  have hA : TL.AHyp L st := (Formalism.FourierDecayAlt.P.actual_algebra_facts Wp Wq P _ _ _ _ X μ L st l0 hD).1
  obtain ⟨hpl, -, hL, hQQ, -, hinv, -, -⟩ := hD
  obtain ⟨hL', hS, hR, hQ⟩ := hN
  obtain ⟨sp, sc, sci⟩ := P5.HerA.star_site_ops hL'
  have hsame : SameFns L d.L := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := hL
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13⟩ := hL'
    exact ⟨funext fun l => (a1 l).trans (b1 l).symm, funext fun l => (a2 l).trans (b2 l).symm,
      funext fun l => (a3 l).trans (b3 l).symm, funext fun l => (a4 l).trans (b4 l).symm,
      funext fun l => (a5 l).trans (b5 l).symm, funext fun l => (a6 l).trans (b6 l).symm,
      a7.trans b7.symm, a8.trans b8.symm, a9.trans b9.symm, a10.trans b10.symm, a11.trans b11.symm,
      a12.trans b12.symm, a13.trans b13.symm⟩
  have hs : M.sgn P l0 = 1 ∨ M.sgn P l0 = -1 := neg_one_pow_eq_or ℂ _
  have hst : ∀ Y, st.QQ Y = M.sgn P l0 • d.QQ Y := fun Y => by rw [hQQ Y, hQ Y]
  have hsite : TL.siteOps L = TL.siteOps d.L := by
    obtain ⟨e1, e2, e3, e4, e5, e6, -⟩ := hsame
    unfold TL.siteOps
    rw [e1, e2, e3, e4, e5, e6]
  refine ⟨⟨hpl.1, hS, hR, sp, sc, sci, fun f g hg => ?_⟩, hA, hsame, hs, hst, hinv⟩
  refine kappa_commute_of_qq hpl.1 d hg (fun Y => ?_) f
  have h := hA.qq_site Y 1 1 g (hsite ▸ hg)
  rw [hst Y, Matrix.smul_apply] at h
  rcases hs with hs | hs
  · rwa [hs, one_smul] at h
  · rw [hs, neg_smul, one_smul] at h
    exact Commute.neg_left_iff.1 h

end GlobalTheory.HatNF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalFormActualOperatorsAlgebraicHypothesesStatement
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalForm_actualOperators_algebraicHypotheses : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → HatHyp d ∧ Comparison₂ d L st (M.sgn P l0) := by
  first | exact @GlobalTheory.HatNF.hatHyp_and_tie_of_isNF | exact GlobalTheory.HatNF.hatHyp_and_tie_of_isNF | (intros; apply GlobalTheory.HatNF.hatHyp_and_tie_of_isNF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFlagCharactersLeadingMinorsColength
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFlagCharactersLeadingMinorsColength
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
open ReciprocityTheory.PGsh.Up

namespace GlobalTheory.CharDepth

theorem det_dvd_det_of_trunc_mem_span {R : Type} [CommRing R] {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (B : Matrix (Fin n) (Fin n) R)
    (h : ∀ j, (fun a : Fin n => A a.castSucc j) ∈ Submodule.span R (Set.range fun i => fun a => B a i)) :
    B.det ∣ A.det := by
  choose X hX using fun j => (Submodule.mem_span_range_iff_exists_fun R).1 (h j)
  rw [Matrix.det_succ_row A (Fin.last n)]
  refine Finset.dvd_sum fun j _ => Dvd.dvd.mul_left ?_ _
  have e : A.submatrix (Fin.last n).succAbove j.succAbove = B * Matrix.of (fun i k => X (j.succAbove k) i) := by
    ext a k
    have := congrFun (hX (j.succAbove k)) a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_apply, Matrix.submatrix_apply, Fin.succAbove_last, ← this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e, Matrix.det_mul]
  exact Dvd.intro _ rfl

theorem minor_dvd_minor {R : Type} [CommRing R] {g N : ℕ} (M : Matrix (Fin g) (Fin N) R) (ι : Fin g → Fin N)
    (hι : ∀ s (hs : s ≤ g), Submodule.span R (Set.range fun b : Fin s => fun a : Fin s =>
      M (Fin.castLE hs a) (ι (Fin.castLE hs b))) = omTr M s hs)
    (n m : ℕ) (hnm : n ≤ m) (hm : m ≤ g) :
    (Matrix.of fun a b : Fin n => M (Fin.castLE (hnm.trans hm) a) (ι (Fin.castLE (hnm.trans hm) b))).det ∣
      (Matrix.of fun a b : Fin m => M (Fin.castLE hm a) (ι (Fin.castLE hm b))).det := by
  induction m, hnm using Nat.le_induction with
  | base => exact dvd_rfl
  | succ m hnm ih =>
    refine (ih (Nat.le_of_succ_le hm)).trans (det_dvd_det_of_trunc_mem_span _ _ fun j => ?_)
    have h := hι m (Nat.le_of_succ_le hm)
    have h2 : (fun a : Fin m => M (Fin.castLE (Nat.le_of_succ_le hm) a) (ι (Fin.castLE hm j))) ∈
        omTr M m (Nat.le_of_succ_le hm) := Submodule.subset_span ⟨_, rfl⟩
    rw [← h] at h2
    exact h2

theorem exists_smul_eq_zero_of_hasLen {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] (hv : v.Integers R) {M : Type} [AddCommGroup M] [Module R M] {x : NNReal}
    (h : HasLen v R M x) (hx : x ≠ 0) : x ≤ 1 ∧ ∃ c : R, c ≠ 0 ∧ ∀ m : M, c • m = 0 := by
  obtain ⟨m, c, ⟨e⟩, hc⟩ := h
  have hc' : v (algebraMap R C (∏ i, c i)) = x := by rw [map_prod, map_prod, hc]
  refine ⟨hc' ▸ hv.map_le_one _, ∏ i, c i, ?_, fun z => ?_⟩
  · intro h0
    rw [h0, map_zero, map_zero] at hc'
    exact hx hc'.symm
  · apply e.injective
    rw [map_smul, map_zero]
    funext i
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (e z i)
    rw [Pi.smul_apply, ← hy, Pi.zero_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton.2 ((Finset.dvd_prod_of_mem c (Finset.mem_univ i)).mul_right y)

theorem exists_flag_characters (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C]
    (hv : v.Integers O) (d s : ℕ) (F : Fin d → PS O 2 d) (w : Fin s → Fin d → O) (x : NNReal)
    (h : HasAF v F w x) (hx : x ≠ 0) :
    x ≤ 1 ∧ ∃ χ : Fin s → PS O 1 d, (∀ b, IsCh F (χ b)) ∧ ∀ i : Fin s, x ≤ v (algebraMap O C
      (Matrix.of fun a b : Fin (i.val + 1) =>
        ∑ j, w (Fin.castLE i.isLt a) j * dl (χ (Fin.castLE i.isLt b)) j).det) := by
  obtain ⟨N, u, hu, hlen⟩ := h
  obtain ⟨hx1, c, hc, hkill⟩ := exists_smul_eq_zero_of_hasLen hv hlen hx
  refine ⟨hx1, ?_⟩
  let M : Matrix (Fin s) (Fin N) O := fun a k => res w (dl (u k)) a
  have hom : omTr M s le_rfl = Submodule.span O (Set.range fun k => res w (dl (u k))) := rfl
  have hspan : ∀ n (hn : n ≤ s), ∀ y : Fin n → O, c • y ∈ omTr M n hn := by
    intro n hn y
    let y' : Fin s → O := Function.extend (Fin.castLE hn) y 0
    have h1 : c • y' ∈ Submodule.span O (Set.range fun k => res w (dl (u k))) := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
      exact hkill _
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 h1
    refine (Submodule.mem_span_range_iff_exists_fun O).2 ⟨r, ?_⟩
    funext a
    have h2 := congrFun hr (Fin.castLE hn a)
    have h3 : y' (Fin.castLE hn a) = y a := (Fin.castLE_injective hn).extend_apply y 0 a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h3] at h2 ⊢
    exact h2
  obtain ⟨ι, -, hι⟩ := charThm C v O hv s N M c hc hspan
  haveI : IsDomain O := Function.Injective.isDomain _ hv.hom_inj
  have hfull := char_len hv M ι s le_rfl (hι s le_rfl)
  rw [hom] at hfull
  have hxe := hasLen_unique hv hlen hfull
  refine ⟨fun b => u (ι b), fun b => hu _, fun i => ?_⟩
  have hd := hv.le_of_dvd (minor_dvd_minor M ι hι (i.val + 1) s i.isLt le_rfl)
  rw [← hxe] at hd
  exact hd

end GlobalTheory.CharDepth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFlagCharactersLeadingMinorsColengthStatement
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flag_characters_leading_minors_colength : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (d s : ℕ) (F : Fin d → PS O 2 d) (w : Fin s → Fin d → O) (x : NNReal), HasAF v F w x → x ≠ 0 → x ≤ 1 ∧ ∃ χ : Fin s → PS O 1 d, (∀ b, IsCh F (χ b)) ∧ ∀ i : Fin s, x ≤ v (algebraMap O C (Matrix.of fun a b : Fin (i.val + 1) => ∑ j, w (Fin.castLE i.isLt a) j * dl (χ (Fin.castLE i.isLt b)) j).det) := by
  first | exact @GlobalTheory.CharDepth.exists_flag_characters | exact GlobalTheory.CharDepth.exists_flag_characters | (intros; apply GlobalTheory.CharDepth.exists_flag_characters <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LiesOverFramedOfSquareLevelMoves
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LiesOverFramedOfSquareLevelMoves
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace OverSquare

open FrameLift OverMove

theorem rel_square {A A₂ Y Y' Y₂ Y₂' : Scheme.{0}} {L : LB A} {L₂ : LB A₂} (hL : L.IsLB) (hL₂ : L₂.IsLB)
    {φ φ' : A₂ ⟶ A} {ν : A ⟶ A} {ν₂ : A₂ ⟶ A₂} (hφ : ν₂ ≫ φ' = φ ≫ ν)
    {w₀ : LB.Iso L₂ (L.pull φ)} {w' : LB.Iso L₂ (L.pull φ')} {w : LB.Iso L (L.pull ν)} {w₂ : LB.Iso L₂ (L₂.pull ν₂)}
    (hw : ∀ (Z : Scheme.{0}) (f : Z ⟶ A₂) (z : Z) i k j l, ν (φ (f z)) ∈ L.U i → φ (f z) ∈ L.U k →
      ν₂ (f z) ∈ L₂.U j → f z ∈ L₂.U l →
      gw w (f ≫ φ) z i k * gw w₀ f z k l = gw w' (f ≫ ν₂) z i j * gw w₂ f z j l)
    {q : Y ⟶ A} {q' : Y' ⟶ A} {q₂ : Y₂ ⟶ A₂} {q₂' : Y₂' ⟶ A₂} {p : Y₂ ⟶ Y} {p' : Y₂' ⟶ Y'} {pm : Y ⟶ Y'}
    {pm₂ : Y₂ ⟶ Y₂'} {σ : Y₂' ⟶ Y₂} (hσ : σ ≫ pm₂ = 𝟙 _) (hp : p ≫ q = q₂ ≫ φ) (h₂ : pm₂ ≫ q₂' = q₂ ≫ ν₂)
    (sq : pm₂ ≫ p' = p ≫ pm) {s : LB.Sec (LOne L q)} {s' : LB.Sec (LOne L q')} {s₂ : LB.Sec (LOne L₂ q₂)}
    {s₂' : LB.Sec (LOne L₂ q₂')} (H₀ : Rel w₀ p s₂ s) (H : Rel w pm s s') (H₂ : Rel w₂ pm₂ s₂ s₂') :
    Rel w' p' s₂' s' := by
  intro Z r z i j hi hj
  obtain ⟨r₀, rfl⟩ : ∃ r₀ : Z ⟶ Y₂, r = r₀ ≫ pm₂ := ⟨r ≫ σ, by rw [Category.assoc, hσ, Category.comp_id]⟩
  obtain ⟨k, hk⟩ := exists_chart hL (φ (q₂ (r₀ z)))
  obtain ⟨l, hl⟩ := exists_chart hL₂ (q₂ (r₀ z))
  have e₂ : q₂' (pm₂ (r₀ z)) = ν₂ (q₂ (r₀ z)) := pt_eq h₂ (r₀ z)
  have e₁ : q (p (r₀ z)) = φ (q₂ (r₀ z)) := pt_eq hp (r₀ z)
  have e₀ : φ' (ν₂ (q₂ (r₀ z))) = ν (φ (q₂ (r₀ z))) := pt_eq hφ (q₂ (r₀ z))
  have hj' : ν₂ (q₂ (r₀ z)) ∈ L₂.U j := e₂ ▸ (show q₂' (pm₂ (r₀ z)) ∈ L₂.U j from hj)
  have hi' : ν (φ (q₂ (r₀ z))) ∈ L.U i := by
    have : φ' (q₂' (pm₂ (r₀ z))) ∈ L.U i := hi
    rwa [e₂, e₀] at this
  have a := H Z (r₀ ≫ p) z i k (by show ν (q (p (r₀ z))) ∈ _; rw [e₁]; exact hi')
    (by show q (p (r₀ z)) ∈ _; rw [e₁]; exact hk)
  have b := H₀ Z r₀ z k l hk hl
  have c := H₂ Z r₀ z j l hj' hl
  have e := hw Z (r₀ ≫ q₂) z i k j l hi' hk hj' hl
  rw [Category.assoc r₀ pm₂ p', sq, ← Category.assoc r₀ p pm, a, b, c, ← _root_.mul_assoc, ← _root_.mul_assoc,
    ← Units.val_mul, ← Units.val_mul, Category.assoc r₀ p q, hp, ← Category.assoc r₀ q₂ φ, e,
    Category.assoc r₀ pm₂ q₂', h₂, Category.assoc r₀ q₂ ν₂]

theorem gw_square {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {S S₂ : Scheme.{0}} {t : SAB H S} {t₂ : SAB H S₂} {r r' : S₂ ⟶ S} {ρ : S ⟶ S} {ρ₂ : S₂ ⟶ S₂}
    (hu : Function.Surjective t₂.G.hom.appTop.hom)
    (m : SABMap t₂ t r) (m' : SABMap t₂ t r') (ν : SABMap t t ρ) (ν₂ : SABMap t₂ t₂ ρ₂)
    (hr : ρ₂ ≫ r' = r ≫ ρ) (hφ : ν₂.φ ≫ m'.φ = m.φ ≫ ν.φ)
    {w₀ : LB.Iso t₂.PP.L (t.PP.L.pull m.φ)} {w' : LB.Iso t₂.PP.L (t.PP.L.pull m'.φ)}
    {w : LB.Iso t.PP.L (t.PP.L.pull ν.φ)} {w₂ : LB.Iso t₂.PP.L (t₂.PP.L.pull ν₂.φ)}
    (h₀ : OverMove.RigIso m w₀) (h' : OverMove.RigIso m' w') (h : OverMove.RigIso ν w) (h₂ : OverMove.RigIso ν₂ w₂)
    (Z : Scheme.{0}) (f : Z ⟶ t₂.G.left) (z : Z) (i k : t.PP.L.ι) (j l : t₂.PP.L.ι)
    (hi : ν.φ (m.φ (f z)) ∈ t.PP.L.U i) (hk : m.φ (f z) ∈ t.PP.L.U k) (hj : ν₂.φ (f z) ∈ t₂.PP.L.U j)
    (hl : f z ∈ t₂.PP.L.U l) :
    gw w (f ≫ m.φ) z i k * gw w₀ f z k l = gw w' (f ≫ ν₂.φ) z i j * gw w₂ f z j l := by
  obtain ⟨a, Ta⟩ := exists_comp t.PP.isLB w w₀ h.1 h₀.1 t.PP.isLB t₂.PP.isLB
  obtain ⟨b, Tb⟩ := exists_comp t₂.PP.isLB w' w₂ h'.1 h₂.1 t.PP.isLB t₂.PP.isLB
  have ga := Ta.pgen_comp t.PP.isLB h.1 h₀.1
  have ra := Ta.pmaps_comp t.PP.isLB (fun _ => m.cm.e_comm) h.2 h₀.2
  have gb := Tb.pgen_comp t₂.PP.isLB h'.1 h₂.1
  have rb := Tb.pmaps_comp t₂.PP.isLB (fun _ => ν₂.cm.e_comm) h'.2 h₂.2
  have e := gw_eq_of_pmaps (S := S₂) (S₀ := S) t.PP.isLB t₂.PP.isLB t₂.G.hom (eSec t₂.G) (Over.w η[t₂.G]) hu
    hφ.symm ga gb (h₁ := m.cm.e ≫ ν.cm.e) (h₂ := ν₂.cm.e ≫ m'.cm.e)
    (by rw [m.base, m'.base, ν.base, ν₂.base]; exact hr.symm) ra rb f z i l
  have hi' : m'.φ (ν₂.φ (f z)) ∈ t.PP.L.U i :=
    (congrArg (· ∈ t.PP.L.U i) (pt_eq hφ (f z))).mpr hi
  exact (Ta Z f z i k l hi hk hl).symm.trans (e.trans (Tb Z f z i j l hi' hj hl))

end OverSquare


open FrameLift OverMove OverSquare in
theorem frOver_of_square_of_frMove : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (ρ₂ : d.Xo₂.X ⟶ d.Xo₂.X) (ν₂ : SABMap d.Xo₂.univ.t d.Xo₂.univ.t ρ₂) (r' : d.Xo₂.X ⟶ Xo.X) (m' : SABMap d.Xo₂.univ.t Xo.univ.t r'), ρ₂ ≫ r' = d.r ≫ ρ → ν₂.φ ≫ m'.φ = d.m.φ ≫ ν.φ → ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S] (y y' : FrPt Xo c S) (y₂ y₂' : FrPt d.Xo₂ d.c₂ S), FrOver d y₂ y → FrMove ρ ν y y' → FrMove ρ₂ ν₂ y₂ y₂' → FrOver { d with r := r', m := m' } y₂' y' := by
  intro E _ _ _ H Dw l Xo c n d ρ ν ρ₂ ν₂ r' m' hr hφ S _ _ _ y y' y₂ y₂' h hy hy₂
  obtain ⟨e, hu, w₀, p, hw₀, p₁, p₂, H₀⟩ := (frOver_iff d _ _).1 h
  obtain ⟨ex, eu, pm, w, a₁, a₂, hw, H₁⟩ := MoveCalc.frMove_iff_carry.1 hy
  obtain ⟨ex₂, eu₂, pm₂, w₂, b₁, b₂, hw₂, H₂⟩ := MoveCalc.frMove_iff_carry.1 hy₂
  obtain ⟨w', g', r₁', -⟩ := m'.lin
  have e' : y₂'.x ≫ r' = y'.x := by rw [ex₂, ex, Category.assoc, hr, ← Category.assoc, e]
  obtain ⟨p', -, p₁', p₂', -⟩ := exists_pm_iso m' e'
  obtain ⟨σ, hσ⟩ := MoveCalc.exists_section ν₂ ex₂ b₁ b₂
  have sq : pm₂ ≫ p' = p ≫ pm := by
    refine pm_ext ?_ ?_
    · rw [Category.assoc, p₁', ← Category.assoc, b₂, Category.assoc, hφ, Category.assoc, a₂, ← Category.assoc p, p₁,
        Category.assoc]
    · rw [Category.assoc, p₂', b₁, Category.assoc, a₁, p₂]
  have hs : Function.Surjective d.Xo₂.univ.t.G.hom.appTop.hom := (GlobalTheory.globalFns_holds _ _
    ⟨d.Xo₂.univ.t.semi.comm, d.Xo₂.univ.t.semi.smooth, d.Xo₂.univ.proper, d.Xo₂.univ.t.semi.geomConnected⟩).2
  refine (frOver_iff { d with r := r', m := m' } y₂' y').2 ⟨e', fun τ i => ?_, w', p', ⟨g', r₁'⟩, p₁', p₂', ?_⟩
  · show y₂'.u τ i ≫ m'.φ = y'.u τ i
    rw [eu₂, eu, Category.assoc, hφ, ← Category.assoc, hu]
  · exact rel_square Xo.univ.t.PP.isLB d.Xo₂.univ.t.PP.isLB hφ
      (gw_square hs d.m m' ν ν₂ hr hφ (rigIso_of d.m hw₀.1 hw₀.2) (rigIso_of m' g' r₁') (rigIso_of ν hw.1 hw.2.1)
        (rigIso_of ν₂ hw₂.1 hw₂.2.1)) hσ p₁ b₂ sq H₀ H₁ H₂

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LiesOverFramedOfSquareLevelMovesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liesOverFramed_of_square_levelMoves : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (ρ₂ : d.Xo₂.X ⟶ d.Xo₂.X) (ν₂ : SABMap d.Xo₂.univ.t d.Xo₂.univ.t ρ₂) (r' : d.Xo₂.X ⟶ Xo.X) (m' : SABMap d.Xo₂.univ.t Xo.univ.t r'), ρ₂ ≫ r' = d.r ≫ ρ → ν₂.φ ≫ m'.φ = d.m.φ ≫ ν.φ → ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S] (y y' : FrPt Xo c S) (y₂ y₂' : FrPt d.Xo₂ d.c₂ S), FrOver d y₂ y → FrMove ρ ν y y' → FrMove ρ₂ ν₂ y₂ y₂' → FrOver { d with r := r', m := m' } y₂' y' := by
  first | exact @GlobalTheory.frOver_of_square_of_frMove | exact GlobalTheory.frOver_of_square_of_frMove | (intros; apply GlobalTheory.frOver_of_square_of_frMove <;> assumption)
end
end
