module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSummableMajorantRationalVectorsLocallyUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArchimedeanRapidKernelOperatorFinsetSum
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjProperRelAmpleOfProjectiveCoordinateRep
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EndoEqOfSections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompLinearEquivIntertwining
namespace GlobalTheory.PELU

open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

theorem hermForm_pullback_matrix {g : ℕ} (Hm B : Matrix (Fin g) (Fin g) ℂ) (u v : Fin g → ℂ) :
    hermForm (Bᵀ * Hm * B.map star) u v = hermForm Hm (B *ᵥ u) (B *ᵥ v) := by
  unfold hermForm
  have e : star (B *ᵥ v) = B.map star *ᵥ star v := by
    ext i
    simp [Matrix.mulVec, dotProduct]
  rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem IsPeriod.comp_linearEquiv (O : Type) [Ring O] (bar : O → O) (D : PLat O bar) (g : ℕ)
    (ρ ρ₂ : O →+* Matrix (Fin g) (Fin g) ℂ) (P : D.La →+ (Fin g → ℂ)) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hP : GlobalTheory.PELU.IsPeriod D ρ P) (hh : ∀ a z, h (ρ a *ᵥ z) = ρ₂ a *ᵥ h z) :
    GlobalTheory.PELU.IsPeriod D ρ₂ (h.toLinearMap.toAddMonoidHom.comp P) := by
  obtain ⟨h1, h2, h3, h4, Hm, h5, h6, h7⟩ := hP
  have ev : ∀ x, (h.toLinearMap.toAddMonoidHom.comp P) x = h (P x) := fun _ => rfl
  set B : Matrix (Fin g) (Fin g) ℂ := LinearMap.toMatrix' h.symm.toLinearMap with hB
  have hBv : ∀ u, B *ᵥ u = h.symm u := fun u => by
    rw [hB, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']; rfl
  refine ⟨fun a x => ?_, ?_, ?_, ?_, Bᵀ * Hm * B.map star, ?_, fun z hz => ?_, fun x y => ?_⟩
  · rw [ev, ev, h1, hh]
  · exact h.injective.comp h2
  · let f : (h.toLinearMap.toAddMonoidHom.comp P).range → P.range := fun z =>
      ⟨h.symm z.1, by
        obtain ⟨x, hx⟩ := z.2
        exact ⟨x, by rw [← hx, ev, h.symm_apply_apply]⟩⟩
    have hc : Continuous f :=
      Continuous.subtype_mk (h.symm.toLinearMap.continuous_of_finiteDimensional.comp continuous_subtype_val) _
    have hi : Function.Injective f := fun a b e => Subtype.ext (h.symm.injective (congrArg Subtype.val e))
    exact DiscreteTopology.of_continuous_injective hc hi
  · have e : Set.range (h.toLinearMap.toAddMonoidHom.comp P) = (h.toLinearMap.restrictScalars ℝ) '' Set.range P := by
      rw [← Set.range_comp]; rfl
    rw [e, ← Submodule.map_span, h4, Submodule.map_top, LinearMap.range_eq_top]
    exact h.surjective
  · have e1 : (B.map star)ᴴ = Bᵀ := by
      ext i j; simp [Matrix.conjTranspose_apply]
    have e2 : (Bᵀ)ᴴ = B.map star := by
      ext i j; simp [Matrix.conjTranspose_apply]
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, e1, e2, h5.eq, Matrix.mul_assoc]
  · rw [hermForm_pullback_matrix, hBv]
    exact h6 _ (fun e => hz (h.symm.map_eq_zero_iff.mp e))
  · rw [hermForm_pullback_matrix, hBv, hBv, ev, ev, h.symm_apply_apply, h.symm_apply_apply, h7]

end GlobalTheory.PELU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperGroupSchemePointsValuationRingMulEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperGroupSchemePointsValuationRingMulEquiv
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.ValPts

theorem points_generic_mulEquiv : ∀ (U Ω : Type) [CommRing U] [IsDomain U] [ValuationRing U] [Field Ω] [Algebra U Ω] [IsFractionRing U Ω] (S : Scheme.{0}) (G : Over S) [GrpObj G], IsProper G.hom → ∀ u : Sp U ⟶ S, ∃ e : (Over.mk u ⟶ G) ≃* (Over.mk (spMap (algebraMap U Ω) ≫ u) ⟶ G), ∀ P, (e P).left = spMap (algebraMap U Ω) ≫ P.left := by
  intro U Ω _ _ _ _ _ _ S G _ hp u
  let V : Over.mk (spMap (algebraMap U Ω) ≫ u) ⟶ Over.mk u := Over.homMk (spMap (algebraMap U Ω)) rfl
  let φ : (Over.mk u ⟶ G) →* (Over.mk (spMap (algebraMap U Ω) ≫ u) ⟶ G) :=
    MonoidHom.mk' (V ≫ ·) fun x y => MonObj.comp_mul V x y
  have hv : ValuativeCriterion G.hom := by
    rw [IsProper.eq_valuativeCriterion] at hp
    exact hp.1.1.1
  have hb : Function.Bijective φ := by
    constructor
    · intro a b e
      have e' : spMap (algebraMap U Ω) ≫ a.left = spMap (algebraMap U Ω) ≫ b.left :=
        congrArg (fun q => q.left) e
      let Q : ValuativeCommSq G.hom :=
        { R := U, K := Ω, i₁ := spMap (algebraMap U Ω) ≫ a.left, i₂ := u,
          commSq := ⟨(Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Over.w a))⟩ }
      obtain ⟨W⟩ := hv Q
      have h1 := W.uniq ⟨a.left, rfl, Over.w a⟩
      have h2 := W.uniq ⟨b.left, e'.symm, Over.w b⟩
      exact Over.OverMorphism.ext (congrArg CommSq.LiftStruct.l (h1.trans h2.symm))
    · intro y
      let Q : ValuativeCommSq G.hom :=
        { R := U, K := Ω, i₁ := y.left, i₂ := u, commSq := ⟨Over.w y⟩ }
      obtain ⟨W⟩ := hv Q
      exact ⟨Over.homMk W.default.l W.default.fac_right, Over.OverMorphism.ext W.default.fac_left⟩
  exact ⟨MulEquiv.ofBijective φ hb, fun P => rfl⟩

end GlobalTheory.ValPts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperGroupSchemePointsValuationRingMulEquivStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_group_scheme_points_valuationRing_mulEquiv : ∀ (U Ω : Type) [CommRing U] [IsDomain U] [ValuationRing U] [Field Ω] [Algebra U Ω] [IsFractionRing U Ω] (S : Scheme.{0}) (G : Over S) [GrpObj G], IsProper G.hom → ∀ u : Sp U ⟶ S, ∃ e : (Over.mk u ⟶ G) ≃* (Over.mk (spMap (algebraMap U Ω) ≫ u) ⟶ G), ∀ P, (e P).left = spMap (algebraMap U Ω) ≫ P.left := by
  first | exact @GlobalTheory.ValPts.points_generic_mulEquiv | exact GlobalTheory.ValPts.points_generic_mulEquiv | (intros; apply GlobalTheory.ValPts.points_generic_mulEquiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPeriodMapCompInjectiveRealLinear
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPeriodMapCompInjectiveRealLinear
open Matrix GlobalTheory.PELU
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)

namespace GlobalTheory.PELU

theorem isPeriod_comp_realLinear {O : Type} [Ring O] {bar : O → O} (D : PLat O bar) {g : ℕ}
    (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (P₀ : D.La →+ (Fin g → ℂ)) (R : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ))
    (M : Matrix (Fin g) (Fin g) ℂ) (hP₀ : IsPeriod D ρ P₀) (hR : Function.Injective R)
    (hRρ : ∀ (a : O) x, R (ρ a *ᵥ P₀ x) = ρ a *ᵥ R (P₀ x)) (hM : M.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm M z z).re)
    (hE : ∀ x y, (hermForm M (R (P₀ x)) (R (P₀ y))).im = D.EF x y) :
    IsPeriod D ρ (R.toAddMonoidHom.comp P₀) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hP₀
  have hsurj : Function.Surjective R := LinearMap.injective_iff_surjective.mp hR
  let e : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) := LinearEquiv.ofInjectiveEndo R hR
  have he : ∀ z, e z = R z := fun z => rfl
  let ec := e.toContinuousLinearEquiv
  refine ⟨?_, ?_, ?_, ?_, M, hM, hpos, ?_⟩
  · intro a x
    simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, h1, hRρ]
  · exact hR.comp h2
  · let f : (R.toAddMonoidHom.comp P₀).range → P₀.range := fun z =>
      ⟨ec.symm z.1, by
        obtain ⟨z, x, rfl⟩ := z
        exact ⟨x, (e.symm_apply_apply (P₀ x)).symm⟩⟩
    have hf : Continuous f := by
      apply Continuous.subtype_mk
      exact ec.symm.continuous.comp continuous_subtype_val
    have hi : Function.Injective f := by
      intro z w h
      apply Subtype.ext
      have := congrArg (fun u : P₀.range => ec u.1) h
      simpa [f] using this
    exact DiscreteTopology.of_continuous_injective hf hi
  · have : Set.range (R.toAddMonoidHom.comp P₀) = R '' Set.range P₀ := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, h4, Submodule.map_top, LinearMap.range_eq_top]
    exact hsurj
  · intro x y
    exact hE x y

end GlobalTheory.PELU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPeriodMapCompInjectiveRealLinearStatement
open Matrix GlobalTheory.PELU
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPeriodMap_comp_injective_realLinear : ∀ {O : Type} [Ring O] {bar : O → O} (D : PLat O bar) {g : ℕ} (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (P₀ : D.La →+ (Fin g → ℂ)) (R : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)) (M : Matrix (Fin g) (Fin g) ℂ), IsPeriod D ρ P₀ → Function.Injective R → (∀ (a : O) x, R (ρ a *ᵥ P₀ x) = ρ a *ᵥ R (P₀ x)) → M.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm M z z).re) → (∀ x y, (hermForm M (R (P₀ x)) (R (P₀ y))).im = D.EF x y) → IsPeriod D ρ (R.toAddMonoidHom.comp P₀) := by
  first | exact @GlobalTheory.PELU.isPeriod_comp_realLinear | exact GlobalTheory.PELU.isPeriod_comp_realLinear | (intros; apply GlobalTheory.PELU.isPeriod_comp_realLinear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusMapOfCharHom
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
namespace TorusOfCharMap

variable {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X']

theorem ext_chV {Z : Over S} {a b : Z ⟶ splitTorus S X} (h : ∀ χ, chV a χ = chV b χ) : a = b :=
  (splitTorusPointsEquiv S X Z).injective (MonoidHom.ext fun χ => h χ.toAdd)

theorem chV_torusMap (ρ : X' →+ X) (χ : X') :
    chV (SplitTorusPow.torusMap S ρ) χ = charUnit S X (ρ χ) := by
  ext1
  rw [chV_val]
  exact SplitTorusPow.torusMap_char ρ χ

theorem chV_comp_torusMap (ρ : X' →+ X) {Z : Over S} (s : Z ⟶ splitTorus S X) (χ : X') :
    chV (s ≫ SplitTorusPow.torusMap S ρ) χ = chV s (ρ χ) := by
  unfold chV
  rw [SplitTorusPow.points_comp_torusMap]
  rfl

theorem torusMap_comp {X'' : Type} [AddCommGroup X''] (ρ : X' →+ X) (σ : X'' →+ X') :
    SplitTorusPow.torusMap S ρ ≫ SplitTorusPow.torusMap S σ = SplitTorusPow.torusMap S (ρ.comp σ) := by
  refine ext_chV fun χ => ?_
  rw [← Category.id_comp (SplitTorusPow.torusMap S ρ ≫ _), ← Category.assoc, chV_comp_torusMap,
    chV_comp_torusMap, ← Category.id_comp (SplitTorusPow.torusMap S (ρ.comp σ)), chV_comp_torusMap]
  rfl

theorem torusMap_id : SplitTorusPow.torusMap S (AddMonoidHom.id X) = 𝟙 _ := by
  refine ext_chV fun χ => ?_
  rw [← Category.id_comp (SplitTorusPow.torusMap S _), chV_comp_torusMap]
  rfl

end TorusOfCharMap

theorem splitTorus_map_of_charHom : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (X' : Type) [AddCommGroup X'] (ρ : X' →+ X), (∃ (τ : splitTorus S X ⟶ splitTorus S X'), (∀ χ, chV τ χ = charUnit S X (ρ χ))) ∧ ∀ (τ : splitTorus S X ⟶ splitTorus S X'), (∀ χ, chV τ χ = charUnit S X (ρ χ)) → IsMonHom τ ∧ (Function.Bijective ρ → IsIso τ) ∧ ∀ (Z : Over S) (s : Z ⟶ splitTorus S X) (χ : X'), chV (s ≫ τ) χ = chV s (ρ χ) := by
  intro S X _ X' _ ρ
  have key : ∀ τ : splitTorus S X ⟶ splitTorus S X', (∀ χ, chV τ χ = charUnit S X (ρ χ)) →
      τ = SplitTorusPow.torusMap S ρ := fun τ h =>
    TorusOfCharMap.ext_chV fun χ => (h χ).trans (TorusOfCharMap.chV_torusMap ρ χ).symm
  refine ⟨⟨_, TorusOfCharMap.chV_torusMap ρ⟩, fun τ h => ?_⟩
  obtain rfl := key τ h
  refine ⟨SplitTorusPow.isMonHom_torusMap ρ, fun hb => ?_, fun Z s χ => TorusOfCharMap.chV_comp_torusMap ρ s χ⟩
  let e : X' ≃+ X := AddEquiv.ofBijective ρ hb
  refine ⟨⟨SplitTorusPow.torusMap S e.symm.toAddMonoidHom, ?_, ?_⟩⟩
  · rw [TorusOfCharMap.torusMap_comp]
    convert TorusOfCharMap.torusMap_id (S := S) (X := X)
    ext x
    exact e.apply_symm_apply x
  · rw [TorusOfCharMap.torusMap_comp]
    convert TorusOfCharMap.torusMap_id (S := S) (X := X')
    ext x
    exact e.symm_apply_apply x

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAdelicThetaTransformSymplecticOfDecay
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAdelicThetaTransformSymplecticOfDecay
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

namespace GlobalTheory.ThetaTransform

theorem continuous_thV : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)]
    (ψ : AddChar (AF F) ℂ), IsTotallyReal F → IsCharAF F ψ → ∀ Φ : (Fin N → AF F) → ℂ, Decay Φ →
      Continuous (thV ψ Φ) := by
  intro F _ _ N _ ψ hF hψ Φ hΦ
  obtain ⟨hc, ⟨K, hK, hKz⟩, hdec⟩ := hΦ
  obtain ⟨hψc, hψn, -, -⟩ := hψ
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  obtain ⟨k, hk⟩ := GlobalTheory.SumMaj.summable_majorant F N hF K hK
  obtain ⟨C, hC⟩ := hdec k
  have hC0 : 0 ≤ C :=
    le_trans (mul_nonneg (norm_nonneg _) (pow_nonneg (by linarith [GlobalTheory.SumMaj.sz_nonneg (0 : Fin N → AF F)]) k))
      (hC 0)
  have hterm : ∀ ξ : Fin N → F, Continuous fun w : VA F N =>
      ψ (rat ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) * Φ (rat ξ + w.1) := by
    intro ξ
    refine Continuous.mul (hψc.comp ?_) (hc.comp (continuous_const.add continuous_fst))
    refine Continuous.add ?_ (continuous_const.mul ?_)
    · exact continuous_finsetSum _ fun i _ => continuous_const.mul ((continuous_apply i).comp continuous_snd)
    · exact continuous_finsetSum _ fun i _ =>
        ((continuous_apply i).comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)
  have heq : thV ψ Φ = fun w : VA F N => ∑' ξ : Fin N → F,
      ψ (rat ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) * Φ (rat ξ + w.1) := by
    funext w
    simp only [thV, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr]
    rfl
  rw [heq]
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨ω, hωc, hωn⟩ := exists_compact_mem_nhds x
  obtain ⟨c, hcs, hc0, hcb⟩ := hk (Prod.fst '' ω) (hωc.image continuous_fst)
  have hon : ContinuousOn (fun w : VA F N => ∑' ξ : Fin N → F,
      ψ (rat ξ ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) * Φ (rat ξ + w.1)) ω := by
    refine continuousOn_tsum (fun ξ => (hterm ξ).continuousOn) (hcs.mul_left C) fun ξ w hw => ?_
    rw [norm_mul, hψn, one_mul]
    by_cases hmem : fin (rat ξ + w.1) ∈ K
    · have h1 := hcb ξ w.1 ⟨w, hw, rfl⟩ hmem
      have h2 := hC (rat ξ + w.1)
      calc ‖Φ (rat ξ + w.1)‖ = ‖Φ (rat ξ + w.1)‖ * 1 := (mul_one _).symm
        _ ≤ ‖Φ (rat ξ + w.1)‖ * (c ξ * (1 + sz (rat ξ + w.1)) ^ k) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = c ξ * (‖Φ (rat ξ + w.1)‖ * (1 + sz (rat ξ + w.1)) ^ k) := by ring
        _ ≤ c ξ * C := mul_le_mul_of_nonneg_left h2 (hc0 ξ)
        _ = C * c ξ := mul_comm _ _
    · rw [hKz _ hmem, norm_zero]
      exact mul_nonneg hC0 (hc0 ξ)
  exact hon.continuousAt hωn

end GlobalTheory.ThetaTransform
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAdelicThetaTransformSymplecticOfDecayStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_adelicThetaTransformSymplectic_of_decay : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ), IsTotallyReal F → IsCharAF F ψ → ∀ Φ : (Fin N → AF F) → ℂ, Decay Φ → Continuous (thV ψ Φ) := by
  first | exact @GlobalTheory.ThetaTransform.continuous_thV | exact GlobalTheory.ThetaTransform.continuous_thV | (intros; apply GlobalTheory.ThetaTransform.continuous_thV <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsLogRootDiscSubLogHostPrimeLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsLogRootDiscSubLogHostPrimeLe
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine

namespace GlobalTheory

theorem rootDiscr_le_of_intermediateField {E : Type} [Field E] [NumberField E]
    (K : IntermediateField ℚ E) : rootDiscr K ≤ rootDiscr E := by
  have hdisc := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) E (𝓞 E)
  have hN : Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 E)) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact differentIdeal_ne_bot
  have htow := Module.finrank_mul_finrank ℚ K E
  set k := Module.finrank ℚ K
  set m := Module.finrank K E
  have hk : 0 < k := Module.finrank_pos
  have hm : 0 < m := Module.finrank_pos
  have ha : 0 < (discr K).natAbs := Int.natAbs_pos.mpr (discr_ne_zero K)
  have hle : (discr K).natAbs ^ m ≤ (discr E).natAbs := by
    rw [hdisc]
    exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hN)
  have hleR : ((discr K).natAbs : ℝ) ^ m ≤ ((discr E).natAbs : ℝ) := by exact_mod_cast hle
  rw [rootDiscr_def, rootDiscr_def, ← htow]
  have e1 : (((|discr K| : ℤ)) : ℝ) = ((discr K).natAbs : ℝ) := by
    rw [Nat.cast_natAbs]
  have e2 : (((|discr E| : ℤ)) : ℝ) = ((discr E).natAbs : ℝ) := by
    rw [Nat.cast_natAbs]
  rw [e1, e2]
  change _ ^ ((k : ℝ))⁻¹ ≤ _
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  calc ((discr K).natAbs : ℝ) ^ (k : ℝ)⁻¹
      = (((discr K).natAbs : ℝ) ^ m) ^ (((k * m : ℕ) : ℝ))⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1
        push_cast
        field_simp
    _ ≤ ((discr E).natAbs : ℝ) ^ (((k * m : ℕ) : ℝ))⁻¹ :=
        Real.rpow_le_rpow (by positivity) hleR (by positivity)

end GlobalTheory

namespace GlobalTheory

theorem abs_lrd_sub_log_d_le_lrd :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
      |GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E - Real.log H.d| ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E := by
  intro E _ _ _ H
  have hK := (rootDiscr_and_different_quadField E H).1
  have hle := rootDiscr_le_of_intermediateField (GlobalTheory.IndefiniteRowSideFullHecke.AdelicDegreeTameRamification.quadField H)
  rw [hK] at hle
  have hd1 : (1 : ℝ) ≤ H.d := by exact_mod_cast H.d_prime.one_lt.le
  have hs : 0 < √(H.d : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hlog0 : 0 ≤ Real.log H.d := Real.log_nonneg hd1
  have hlogs : Real.log √(H.d : ℝ) = Real.log H.d / 2 := by
    rw [Real.log_sqrt (by linarith)]
  have h2 : Real.log H.d / 2 ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E := by
    rw [← hlogs, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd]
    exact Real.log_le_log hs hle
  rw [abs_le]
  constructor <;> linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsLogRootDiscSubLogHostPrimeLeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abs_logRootDisc_sub_log_hostPrime_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), |GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E - Real.log H.d| ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E := by
  first | exact @GlobalTheory.abs_lrd_sub_log_d_le_lrd | exact GlobalTheory.abs_lrd_sub_log_d_le_lrd | (intros; apply GlobalTheory.abs_lrd_sub_log_d_le_lrd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyPosDefHermFormNearZeroMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyPosDefHermFormNearZeroMatrix
open Matrix GlobalTheory.PELU
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)

namespace GlobalTheory.PosOpen

theorem hermForm_smul_real {g : ℕ} (N : Matrix (Fin g) (Fin g) ℂ) (r : ℝ) (z : Fin g → ℂ) :
    hermForm N ((r : ℂ) • z) ((r : ℂ) • z) = ((r * r : ℝ) : ℂ) * hermForm N z z := by
  simp only [hermForm, star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  simp [Complex.conj_ofReal]
  ring

theorem posopen : ∀ {g : ℕ} (M₀ : Matrix (Fin g) (Fin g) ℂ), (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm M₀ z z).re) →
    ∀ᶠ C in nhds (0 : Matrix (Fin g) (Fin g) ℂ), (1 - C.map star * C).det ≠ 0 ∧ (1 - C * C.map star).det ≠ 0 ∧
      ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm (M₀ * (1 - C.map star * C)⁻¹) z z).re := by
  intro g M₀ hM
  have cA : Continuous fun C : Matrix (Fin g) (Fin g) ℂ => 1 - C.map star * C :=
    continuous_const.sub ((continuous_id.matrix_map continuous_star).matrix_mul continuous_id)
  have cB : Continuous fun C : Matrix (Fin g) (Fin g) ℂ => 1 - C * C.map star :=
    continuous_const.sub (continuous_id.matrix_mul (continuous_id.matrix_map continuous_star))
  have dA : Continuous fun C : Matrix (Fin g) (Fin g) ℂ => (1 - C.map star * C).det := cA.matrix_det
  have dB : Continuous fun C : Matrix (Fin g) (Fin g) ℂ => (1 - C * C.map star).det := cB.matrix_det
  have dA0 : (1 - (0 : Matrix (Fin g) (Fin g) ℂ).map star * 0).det ≠ 0 := by simp
  have dB0 : (1 - (0 : Matrix (Fin g) (Fin g) ℂ) * (0 : Matrix (Fin g) (Fin g) ℂ).map star).det ≠ 0 := by simp
  have e1 := dA.continuousAt.eventually_ne dA0
  have e2 := dB.continuousAt.eventually_ne dB0

  have cInv : ContinuousAt (fun C : Matrix (Fin g) (Fin g) ℂ => M₀ * (1 - C.map star * C)⁻¹) 0 := by
    have h1 : (fun C : Matrix (Fin g) (Fin g) ℂ => M₀ * (1 - C.map star * C)⁻¹) =
        fun C => M₀ * (((1 - C.map star * C).det)⁻¹ • (1 - C.map star * C).adjugate) := by
      funext C
      rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [h1]
    refine continuousAt_const.mul (ContinuousAt.smul (dA.continuousAt.inv₀ dA0) cA.matrix_adjugate.continuousAt)
  have cH : Continuous fun p : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) => (hermForm p.1 p.2 p.2).re :=
    Complex.continuous_re.comp (continuous_snd.dotProduct (continuous_fst.matrix_mulVec continuous_snd.star))
  have tube : ∀ᶠ C in nhds (0 : Matrix (Fin g) (Fin g) ℂ), ∀ y ∈ Metric.sphere (0 : Fin g → ℂ) 1,
      0 < (hermForm (M₀ * (1 - C.map star * C)⁻¹) y y).re := by
    refine (isCompact_sphere (0 : Fin g → ℂ) 1).eventually_forall_of_forall_eventually fun y hy => ?_
    have cF : ContinuousAt (fun p : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) =>
        (hermForm (M₀ * (1 - p.1.map star * p.1)⁻¹) p.2 p.2).re) (0, y) := by
      have : ContinuousAt (fun p : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) =>
          (M₀ * (1 - p.1.map star * p.1)⁻¹, p.2)) (0, y) :=
        (ContinuousAt.comp (x := ((0 : Matrix (Fin g) (Fin g) ℂ), y))
          (f := (Prod.fst : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) → Matrix (Fin g) (Fin g) ℂ)) cInv
          continuousAt_fst).prodMk continuousAt_snd
      exact ContinuousAt.comp (x := ((0 : Matrix (Fin g) (Fin g) ℂ), y))
        (g := fun p : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) => (hermForm p.1 p.2 p.2).re)
        (f := fun p : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) => (M₀ * (1 - p.1.map star * p.1)⁻¹, p.2))
        cH.continuousAt this
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy
    have v0 : 0 < (hermForm (M₀ * (1 - (0 : Matrix (Fin g) (Fin g) ℂ).map star * 0)⁻¹) y y).re := by
      simpa using hM y hy0
    exact cF.eventually (lt_mem_nhds v0)
  filter_upwards [e1, e2, tube] with C h1 h2 h3
  refine ⟨h1, h2, fun z hz => ?_⟩
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hu : ((‖z‖⁻¹ : ℝ) : ℂ) • z ∈ Metric.sphere (0 : Fin g → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have := h3 _ hu
  rw [hermForm_smul_real, Complex.re_ofReal_mul] at this
  exact pos_of_mul_pos_right this (by positivity)

end GlobalTheory.PosOpen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyPosDefHermFormNearZeroMatrixStatement
open Matrix GlobalTheory.PELU
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_posDef_hermForm_near_zero_matrix : ∀ {g : ℕ} (M₀ : Matrix (Fin g) (Fin g) ℂ), (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm M₀ z z).re) → ∀ᶠ C in nhds (0 : Matrix (Fin g) (Fin g) ℂ), (1 - C.map star * C).det ≠ 0 ∧ (1 - C * C.map star).det ≠ 0 ∧ ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm (M₀ * (1 - C.map star * C)⁻¹) z z).re := by
  first | exact @GlobalTheory.PosOpen.posopen | exact GlobalTheory.PosOpen.posopen | (intros; apply GlobalTheory.PosOpen.posopen; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingBirigidifiedTrivialOnAxes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubWeilProdEqOneOfToric
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Raynaud.ProdToric

theorem isMonHom_lift_id_one {S : Scheme.{0}} (G G' : Over S) [GrpObj G] [GrpObj G'] :
    IsMonHom (lift (𝟙 G) (1 : G ⟶ G')) := by
  rw [Hom.one_def]; infer_instance

theorem isMonHom_lift_one_id {S : Scheme.{0}} (G G' : Over S) [GrpObj G] [GrpObj G'] :
    IsMonHom (lift (1 : G' ⟶ G) (𝟙 G')) := by
  rw [Hom.one_def]; infer_instance

end GlobalTheory.Raynaud.ProdToric
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingBirigidifiedTrivialOnAxes
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AxisPairing

theorem weilIs_comp_eq_one_of_pull_isGen {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left)
    (hA : IsAbelianScheme A) (hP : P.IsLB) (ψ : A ⟶ G2 A) [IsMonHom ψ]
    (hg : ∃ t : (P.pull ψ.left).Gen, t.IsGen) {n : ℤ} {T : Over S} {u v : T ⟶ A}
    {c : Γ(T.left, ⊤)ˣ} (h : Out.WeilIs (G2 A) P n (u ≫ ψ) (v ≫ ψ) c) : c = 1 := by
  have hL : (P.pull ψ.left).IsLB := LB.isLB_pull hP ψ.left
  have h0 : GlobalTheory.CechPic.cls _ hL = 0 := (GlobalTheory.CechPic.cls_eq_zero_iff hL).2 hg
  have hw : LBIso (lbPow (P.pull ψ.left) 1) (P.pull ψ.left) := by
    have hp : (lbPow (P.pull ψ.left) 1).IsLB := LB.isLB_pull hL _
    refine (GlobalTheory.CechPic.cls_eq_iff hp hL).1 ?_
    rw [GlobalTheory.CechPic.cls_lbPow hL 1 hp, one_smul]
  have h1 := GlobalTheory.WeilIsogeny.weilIs_pull_hom GlobalTheory.globalFns_holds hA hL hP ψ hw h
  rw [Nat.cast_one, _root_.mul_one] at h1
  have iso : LBIso (lbPow (P.pull ψ.left) 0) ((P.pull ψ.left).pull (𝟙 A : A ⟶ A).left) := by
    apply (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_pull hL _)).1
    rw [GlobalTheory.CechPic.cls_lbPow hL, GlobalTheory.CechPic.cls_pull hL,
      Over.id_left, GlobalTheory.CechPic.pull_id, h0, zero_smul]
  have h2 := (GlobalTheory.weilIs_along_hom GlobalTheory.globalFns_holds S A A (𝟙 A)
    (P.pull ψ.left) (P.pull ψ.left) 0 n T u v c c hA hA hL hL inferInstance iso
    (by simpa using h1)).2 h1
  simpa using h2

theorem axes : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (n : ℤ) (T : Over S) (u v : T ⟶ A) (c : Γ(T.left, ⊤)ˣ), (Out.WeilIs (G2 A) P n (lift u 1) (lift v 1) c → c = 1) ∧ (Out.WeilIs (G2 A) P n (lift 1 u) (lift 1 v) c → c = 1) := by
  intro S A _ _ P hA hP h₂ h₁ n T u v c
  have := GlobalTheory.Raynaud.ProdToric.isMonHom_lift_id_one A A
  have := GlobalTheory.Raynaud.ProdToric.isMonHom_lift_one_id A A
  have e₁ : ∀ w : T ⟶ A, w ≫ lift (𝟙 A) (1 : A ⟶ A) = lift w 1 := fun w => by
    rw [comp_lift, Category.comp_id, MonObj.comp_one]
  have e₂ : ∀ w : T ⟶ A, w ≫ lift (1 : A ⟶ A) (𝟙 A) = lift 1 w := fun w => by
    rw [comp_lift, Category.comp_id, MonObj.comp_one]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← e₁ u, ← e₁ v] at h
    exact weilIs_comp_eq_one_of_pull_isGen P hA hP _ h₁ h
  · rw [← e₂ u, ← e₂ v] at h
    exact weilIs_comp_eq_one_of_pull_isGen P hA hP _ h₂ h

end GlobalTheory.AxisPairing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingBirigidifiedTrivialOnAxesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_birigidified_trivial_on_axes : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (n : ℤ) (T : Over S) (u v : T ⟶ A) (c : Γ(T.left, ⊤)ˣ), (Out.WeilIs (G2 A) P n (lift u 1) (lift v 1) c → c = 1) ∧ (Out.WeilIs (G2 A) P n (lift 1 u) (lift 1 v) c → c = 1) := by
  first | (exact @GlobalTheory.AxisPairing.axes) | (exact GlobalTheory.AxisPairing.axes) | (intros; apply GlobalTheory.AxisPairing.axes  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubTriv
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.EvenGenTorus

open TorusCube

theorem exists_ratio {S : Scheme.{0}} {H G : Over S} [GrpObj H] [IsCommMonObj H] [GrpObj G] [IsCommMonObj G]
    (i : H ⟶ G) [IsMonHom i] (L : RigLB G) (c : CubicalStr G L)
    (τ : LB.Gen (LB.LinComb L.L (K := PUnit) (fun _ => i.left) (fun _ => 1))) (hτ : τ.IsGen) :
    ∃ w : Γ((H ⊗ H ⊗ H).left, ⊤)ˣ, ∀ (T : Over S) (x y u : T ⟶ H) (z : T.left)
      (J : (T.left ⟶ G.left) → L.L.ι), Good L.L z J →
      ∀ v : (T ⟶ H) → (T.left.presheaf.stalk z)ˣ, (∀ a, v a = val τ a.left z J) →
      (v (x * y * u) * v x * v y * v u *
        (cubV c z J (x ≫ i) (y ≫ i) (u ≫ i) * v (x * y) * v (x * u) * v (y * u) * v 1)⁻¹).val =
        gs (𝟙 T.left) z ⊤ ((lift x (lift y u)).left.appTop.hom w.val) := by
  let p₀ := x3 H 0
  let p₁ := x3 H 1
  let p₂ := x3 H 2
  have P : ∀ p : G3 H ⟶ H, HasVal L.L (fun _ _ h => h (p.left ≫ i.left))
      (fun _ r z J => val τ (r ≫ p.left) z J) := fun p =>
    ⟨PUnit, inferInstance, _, _, LB.pullGen L.L (fun _ : PUnit => i.left) (fun _ => 1) τ p.left,
      DVR.pullGen_isGen _ _ _ _ hτ p.left, fun V _ k => by simp, fun Z r z J hJ => val_pull hJ _ _ _⟩
  let M := (lift (p₀ ≫ i) (lift (p₁ ≫ i) (p₂ ≫ i))).left
  have em : ∀ a b : G3 H ⟶ H, (a ≫ i) * (b ≫ i) = (a * b) ≫ i := fun a b => (MonObj.mul_comp _ _ _).symm
  have e1 : (1 : G3 H ⟶ G) = (1 : G3 H ⟶ H) ≫ i := (MonObj.one_comp _).symm
  have C : HasVal L.L (fun _ _ h => h ((p₀ * p₁ * p₂).left ≫ i.left) * (h ((p₀ * p₁).left ≫ i.left))⁻¹ *
      (h ((p₀ * p₂).left ≫ i.left))⁻¹ * (h ((p₁ * p₂).left ≫ i.left))⁻¹ * h (p₀.left ≫ i.left) *
        h (p₁.left ≫ i.left) * h (p₂.left ≫ i.left) * (h ((1 : G3 H ⟶ H).left ≫ i.left))⁻¹)
      (fun _ r z J => val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) c.t (r ≫ M) z J) :=
    ⟨thK, inferInstance, _, _, LB.pullGen L.L (thφ G (x3 G)) thε c.t M, DVR.pullGen_isGen _ _ _ _ c.isGen M,
      fun V _ h => by
        have := prod_cub (p₀ ≫ i) (p₁ ≫ i) (p₂ ≫ i) h
        rw [e1] at this
        simp only [em] at this
        simpa only [Over.comp_left] using this,
      fun Z r z J hJ => val_pull hJ _ _ _⟩
  obtain ⟨w, hw⟩ := (((((P (p₀ * p₁ * p₂)).mul (P p₀)).mul (P p₁)).mul (P p₂)).mul
    ((((C.mul (P (p₀ * p₁))).mul (P (p₀ * p₂))).mul (P (p₁ * p₂))).mul (P 1)).inv).exists_unit
    L.isLB (fun V _ k => by
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel)
  refine ⟨w, fun T x y u z J hJ v hv => ?_⟩
  refine Eq.trans ?_ (hw _ (lift x (lift y u)).left z J hJ)
  have r₀ : lift x (lift y u) ≫ p₀ = x := by simp [p₀, x3]
  have r₁ : lift x (lift y u) ≫ p₁ = y := by simp [p₁, x3]
  have r₂ : lift x (lift y u) ≫ p₂ = u := by simp [p₂, x3]
  have hM : (lift x (lift y u)).left ≫ M = (lift (x ≫ i) (lift (y ≫ i) (u ≫ i))).left := by
    simp only [M, ← Over.comp_left, comp_lift, ← Category.assoc, r₀, r₁, r₂]
  simp only [← Over.comp_left, MonObj.comp_mul, MonObj.comp_one, r₀, r₁, r₂, hv]
  rw [hM]
  rfl

theorem cube (k : Type) [Field k] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (G : Over (Spec (CommRingCat.of k))) [GrpObj G] [IsCommMonObj G] (i : splitTorus (Spec (CommRingCat.of k)) X ⟶ G)
    [IsMonHom i] (L : RigLB G) (c : CubicalStr G L)
    (τ : LB.Gen (LB.LinComb L.L (K := PUnit) (fun _ => i.left) (fun _ => 1))) (hτ : τ.IsGen)
    (T : Over (Spec (CommRingCat.of k))) (x y u : T ⟶ splitTorus (Spec (CommRingCat.of k)) X) (z : T.left)
    (J : (T.left ⟶ G.left) → L.L.ι) (hJ : Good L.L z J) :
    val τ (x * y * u).left z J * val τ x.left z J * val τ y.left z J * val τ u.left z J =
      cubV c z J (x ≫ i) (y ≫ i) (u ≫ i) * val τ (x * y).left z J * val τ (x * u).left z J *
        val τ (y * u).left z J * val τ (1 : T ⟶ splitTorus (Spec (CommRingCat.of k)) X).left z J := by
  obtain ⟨w, hw⟩ := exists_ratio i L c τ hτ
  have hT : TwoUniqueSums (X × X × X) := inferInstance
  have face : ∀ (Z : Over (Spec (CommRingCat.of k))) (a b d : Z ⟶ splitTorus (Spec (CommRingCat.of k)) X),
      (a = 1 ∨ b = 1 ∨ d = 1) → (lift a (lift b d)).left.appTop.hom w.val = 1 := by
    intro Z a b d h
    refine fn_ext fun q _ => ?_
    choose I hI using fun χ : Z.left ⟶ G.left => exists_chart L.isLB (χ q)
    have C := isCub_cubV c (show Good L.L q I from hI)
    rw [← hw Z a b d q I hI (fun a => val τ a.left q I) (fun _ => rfl), gs_eq _ q ⊤ trivial, map_one, map_one,
      Units.val_eq_one, mul_inv_eq_one]
    rcases h with rfl | rfl | rfl
    · rw [MonObj.one_comp, C.face]; simp only [_root_.one_mul, _root_.mul_one]; try ac_rfl
    · rw [MonObj.one_comp, C.face₂]; simp only [_root_.one_mul, _root_.mul_one]; try ac_rfl
    · rw [MonObj.one_comp, C.face₃]; simp only [_root_.one_mul, _root_.mul_one]; try ac_rfl
  have key := unit_eq_one k X w.val w.isUnit (face _ _ _ _ (Or.inr (Or.inl rfl))) (face _ _ _ _ (Or.inl rfl))
    (face _ _ _ _ (Or.inl rfl)) T x y u
  have := hw T x y u z J hJ _ (fun _ => rfl)
  rw [key, gs_eq _ z ⊤ trivial, map_one, map_one, Units.val_eq_one, mul_inv_eq_one] at this
  exact this

end GlobalTheory.EvenGenTorus
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedOrderOfLocalCongruenceSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedOrderOfLocalCongruenceSplit
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.Euler.HatLoc

variable {E : Type} [Field E] [NumberField E]

theorem finMult {R : Type} [CommRing R] [IsDedekindDomain R] {c : Ideal R} (hc : c ≠ ⊥) (v : HeightOneSpectrum R) :
    FiniteMultiplicity v.asIdeal c :=
  FiniteMultiplicity.of_prime_left v.prime hc

omit [NumberField E] in
theorem expIn_eq_zero {c : Ideal (OF E)} {v : HeightOneSpectrum (OF E)} (h : ¬ v.asIdeal ∣ c) : expIn c v = 0 :=
  multiplicity_eq_zero_of_not_dvd h

theorem exists_global {c : Ideal (OF E)} (hc : c ≠ ⊥) {z : Af E} (hz : ∀ v, LocIn (expIn c v) v z) :
    ∃ a : OF E, ∀ P : HeightOneSpectrum (𝓞 E),
      Valued.v (z P - iota a P) ≤ WithZero.exp (-(expIn c (P.under (OF E)) : ℤ)) := by
  classical
  choose b hb using hz
  have hfin := Ideal.finite_factors (R := OF E) hc
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := hfin.toFinset) (fun v => v.asIdeal) (expIn c)
    (fun v _ => v.prime) (fun v _ w _ h h' => h (HeightOneSpectrum.ext h')) (fun v => b v)
  refine ⟨a, fun P => ?_⟩
  have h1 : a - b (P.under (OF E)) ∈ (P.under (OF E)).asIdeal ^ expIn c (P.under (OF E)) := by
    by_cases h : (P.under (OF E)).asIdeal ∣ c
    · exact ha _ (hfin.mem_toFinset.2 h)
    · simp [expIn_eq_zero h]
  have h2 := val_iota_le_of_mem (over_under P) _ h1
  have h3 : z P - iota a P = (z P - iota (b (P.under (OF E))) P) - iota (a - b (P.under (OF E))) P := by
    rw [iota_sub, sub_coord]; ring
  rw [h3]
  exact Valuation.map_sub_le _ (hb _ P (over_under P)) h2

theorem multiplicity_map_le [IsCMField E] {c : Ideal (OF E)} (hc : c ≠ ⊥)
    (hs : ∀ v : HeightOneSpectrum (OF E), v.asIdeal ∣ c → Splits v) (P : HeightOneSpectrum (𝓞 E)) :
    multiplicity P.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) ≤ expIn c (P.under (OF E)) := by
  set k := multiplicity P.asIdeal (Ideal.map (algebraMap (OF E) (𝓞 E)) c) with hk
  have h1 : Ideal.map (algebraMap (OF E) (𝓞 E)) c ≤ P.asIdeal ^ k := Ideal.le_of_dvd (pow_multiplicity_dvd _ _)
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  have h2 : (P.under (OF E)).asIdeal ∣ c :=
    Ideal.dvd_iff_le.2 (Ideal.map_le_iff_le_comap.1 (h1.trans (Ideal.pow_le_self hpos.ne')))
  refine (finMult hc _).le_multiplicity_of_pow_dvd (Ideal.dvd_iff_le.2 fun a ha => ?_)
  exact (((GlobalTheory.CMVal.Euler.SplitPlace.split_place E _ (hs _ h2)).2 P (over_under P)).2.1 a k).1 (h1 (Ideal.mem_map_of_mem _ ha))

theorem mem_hatO_of_locIn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ →
    (∀ v : HeightOneSpectrum (OF E), v.asIdeal ∣ c → Splits v) → ∀ z : Af E, (∀ v, LocIn (expIn c v) v z) →
      z ∈ hatO c := by
  intro E _ _ _ c hc hs z hz
  obtain ⟨a, ha⟩ := exists_global hc hz
  have hN : 0 < Ideal.absNorm c := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  obtain ⟨x, y, hy, hxy⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat E _ hN).2 z
    (fun P => (hz _).val_le (over_under P))
  have hny : Ideal.absNorm c • y = iota ((Ideal.absNorm c : ℕ) : OF E) * y := by
    rw [nsmul_eq_mul, iota, map_natCast, map_natCast]
  rw [hny] at hxy
  have hc' : Ideal.map (algebraMap (OF E) (𝓞 E)) c ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hc
  have hx : x - algebraMap (OF E) (𝓞 E) a ∈ Ideal.map (algebraMap (OF E) (𝓞 E)) c := by
    rw [← Ideal.iInf_maxPowDividing_eq hc', Ideal.mem_iInf]
    intro P
    rw [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity hc']
    refine Ideal.pow_le_pow_right (multiplicity_map_le hc hs P) ?_
    rw [← P.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := E),
      ← HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← FiniteAdeleRing.algebraMap_apply]
    have h1 : algebraMap E (Af E) (algebraMap (𝓞 E) E (x - algebraMap (OF E) (𝓞 E) a)) =
        (z - iota a) - iota ((Ideal.absNorm c : ℕ) : OF E) * y := by
      rw [map_sub, map_sub, hxy]
      change algebraMap E (Af E) (x : E) - iota a = _
      ring
    rw [h1, sub_coord, sub_coord, mul_coord]
    refine Valuation.map_sub_le _ (ha P) ?_
    rw [map_mul]
    exact (mul_le_mul' (val_iota_le_of_mem (over_under P) _
      (Ideal.le_of_dvd (pow_multiplicity_dvd _ _) (Ideal.absNorm_mem c))) (hy P)).trans_eq (mul_one _)
  rw [hxy]
  refine add_mem (algebraMap_mem_hatO (mem_orderC.2 ⟨a, _, hx, ?_⟩)) (PicFin.mul_mem_hatO (Ideal.absNorm_mem c) hy)
  rw [map_sub]
  change (x : E) = algebraMap (OF E) E a + ((x : E) - algebraMap (OF E) E a)
  ring

end GlobalTheory.CMVal.Euler.HatLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedOrderOfLocalCongruenceSplitStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedOrder_of_local_congruence_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → (∀ v : HeightOneSpectrum (OF E), v.asIdeal ∣ c → Splits v) → ∀ z : Af E, (∀ v, LocIn (expIn c v) v z) → z ∈ hatO c := by
  first | exact @GlobalTheory.CMVal.Euler.HatLoc.mem_hatO_of_locIn | exact GlobalTheory.CMVal.Euler.HatLoc.mem_hatO_of_locIn | (intros; apply GlobalTheory.CMVal.Euler.HatLoc.mem_hatO_of_locIn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannRelationConverseConjAffine
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannRelationConverseConjAffine
open Matrix GlobalTheory.PELU
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)

namespace GlobalTheory.PeriodCoord

private theorem inv_mul_eq_mul_inv_of_intertwine {n : Type} [Fintype n] [DecidableEq n]
    (A B D : Matrix n n ℂ) (hA : A.det ≠ 0) (hD : D.det ≠ 0) (h : B * D = A * B) :
    A⁻¹ * B = B * D⁻¹ := by
  have hA' : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have hD' : IsUnit D.det := isUnit_iff_ne_zero.mpr hD
  calc A⁻¹ * B = A⁻¹ * (B * D) * D⁻¹ := by
          rw [Matrix.mul_assoc A⁻¹, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hD', Matrix.mul_one]
    _ = A⁻¹ * A * B * D⁻¹ := by rw [h, Matrix.mul_assoc A⁻¹ A B]
    _ = B * D⁻¹ := by rw [Matrix.nonsing_inv_mul _ hA', Matrix.one_mul]

private theorem star_dot_mulVec {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) (x y : Fin g → ℂ) :
    star (x ⬝ᵥ A *ᵥ y) = star x ⬝ᵥ A.map star *ᵥ star y := by
  simp [dotProduct, mulVec, star_sum, Finset.mul_sum]

private theorem star_mulVec' {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) (y : Fin g → ℂ) :
    star (A *ᵥ y) = A.map star *ᵥ star y := by
  funext i
  simp [mulVec, dotProduct, star_sum]

private theorem dot_left {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) (x y : Fin g → ℂ) :
    (A *ᵥ x) ⬝ᵥ y = x ⬝ᵥ Aᵀ *ᵥ y := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]

private theorem map_star_mul' {g : ℕ} (A B : Matrix (Fin g) (Fin g) ℂ) :
    (A * B).map star = A.map star * B.map star := by
  ext i j; simp [Matrix.mul_apply, star_sum]

private theorem map_star_map_star' {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) : (A.map star).map star = A := by
  ext i j; simp

private theorem conj_transpose_intertwine {g : ℕ} (M₀ C : Matrix (Fin g) (Fin g) ℂ) (hH : M₀ᴴ = M₀)
    (hS : (Cᵀ * M₀)ᵀ = Cᵀ * M₀) : (C.map star)ᵀ * Cᵀ * M₀ = M₀ * C.map star * C := by
  have f0 : M₀.map star = M₀ᵀ := by
    ext i j
    have := congrFun (congrFun hH j) i
    simpa [conjTranspose_apply] using this
  have f1 : M₀ᵀ * C = Cᵀ * M₀ := by rw [transpose_mul, transpose_transpose] at hS; exact hS
  have f1' : M₀ * C.map star = (C.map star)ᵀ * M₀ᵀ := by
    have := congrArg (fun A => A.map star) f1
    simp only [map_star_mul'] at this
    have e1 : (M₀ᵀ).map star = M₀ := by rw [transpose_map, f0, transpose_transpose]
    have e2 : (Cᵀ).map star = (C.map star)ᵀ := by rw [transpose_map]
    rw [e1, e2, f0] at this
    exact this
  rw [Matrix.mul_assoc, ← f1, ← Matrix.mul_assoc, ← f1']

theorem riemann_converse {g : ℕ} (M₀ C : Matrix (Fin g) (Fin g) ℂ) (hH : M₀ᴴ = M₀) (_hdet : M₀.det ≠ 0)
    (hS : (Cᵀ * M₀)ᵀ = Cᵀ * M₀) (hY : (1 - C.map star * C).det ≠ 0) :
    (M₀ * (1 - C.map star * C)⁻¹)ᴴ = M₀ * (1 - C.map star * C)⁻¹ ∧
      ∀ z w : Fin g → ℂ, (hermForm (M₀ * (1 - C.map star * C)⁻¹) (z + C *ᵥ star z) (w + C *ᵥ star w)).im =
        (hermForm M₀ z w).im := by
  set Y := 1 - C.map star * C with hYdef
  set M := M₀ * Y⁻¹ with hMdef
  have f2 := conj_transpose_intertwine M₀ C hH hS
  have f1 : M₀ᵀ * C = Cᵀ * M₀ := by rw [transpose_mul, transpose_transpose] at hS; exact hS
  have hYh : Yᴴ = 1 - (C.map star)ᵀ * Cᵀ := by
    rw [hYdef, conjTranspose_sub, conjTranspose_one, conjTranspose_mul]
    congr 2
    · ext i j; simp
  have hYt : Yᵀ = 1 - Cᵀ * (C.map star)ᵀ := by
    rw [hYdef, transpose_sub, transpose_one, transpose_mul]

  have ha : Mᴴ = M := by
    rw [hMdef, conjTranspose_mul, conjTranspose_nonsing_inv, hH]
    apply inv_mul_eq_mul_inv_of_intertwine _ _ _ _ hY
    · rw [hYh, hYdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, f2, Matrix.mul_assoc]
    · rw [det_conjTranspose]; exact star_ne_zero.mpr hY

  have hMbar : M.map star = Mᵀ := by
    ext i j
    have := congrFun (congrFun ha j) i
    simpa [conjTranspose_apply] using this
  have hb : M.map star * C = Cᵀ * M := by
    rw [hMbar, hMdef, transpose_mul, transpose_nonsing_inv, Matrix.mul_assoc, f1, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc]
    rw [Matrix.mul_assoc]
    apply inv_mul_eq_mul_inv_of_intertwine _ _ _ _ hY
    · rw [hYt, hYdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
        Matrix.mul_assoc Cᵀ (C.map star)ᵀ, ← Matrix.mul_assoc (C.map star)ᵀ, f2]
      simp only [Matrix.mul_assoc]
    · rw [det_transpose]; exact hY

  have hc : M = M₀ + (C.map star)ᵀ * M.map star * C := by
    have hYu : IsUnit Y.det := isUnit_iff_ne_zero.mpr hY
    rw [Matrix.mul_assoc, hb, ← Matrix.mul_assoc, hMdef, ← Matrix.mul_assoc, f2]
    have h0 : M₀ = M₀ * Y * Y⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hYu, Matrix.mul_one]
    calc M₀ * Y⁻¹ = (M₀ * Y + M₀ * C.map star * C) * Y⁻¹ := by
          rw [Matrix.mul_assoc M₀ (C.map star), ← Matrix.mul_add, hYdef, sub_add_cancel, Matrix.mul_one]
      _ = M₀ * Y * Y⁻¹ + M₀ * C.map star * C * Y⁻¹ := Matrix.add_mul _ _ _
      _ = _ := by rw [← h0]
  refine ⟨ha, fun z w => ?_⟩
  have e : hermForm M (z + C *ᵥ star z) (w + C *ᵥ star w) =
      z ⬝ᵥ M *ᵥ star w + z ⬝ᵥ (M * C.map star) *ᵥ w + star z ⬝ᵥ (Cᵀ * M) *ᵥ star w
        + star z ⬝ᵥ (Cᵀ * M * C.map star) *ᵥ w := by
    simp only [hermForm, star_add, star_mulVec', star_star, add_dotProduct, mulVec_add, dotProduct_add,
      dot_left, mulVec_mulVec, Matrix.mul_assoc]
    ring
  have e2 : star (z ⬝ᵥ (M * C.map star) *ᵥ w) = star z ⬝ᵥ (Cᵀ * M) *ᵥ star w := by
    rw [star_dot_mulVec, map_star_mul', map_star_map_star', hb]
  have e4 : star (star z ⬝ᵥ (Cᵀ * M * C.map star) *ᵥ w) = z ⬝ᵥ ((C.map star)ᵀ * M.map star * C) *ᵥ star w := by
    rw [star_dot_mulVec, map_star_mul', map_star_mul', map_star_map_star', star_star, transpose_map]
  have e1 : z ⬝ᵥ M *ᵥ star w = hermForm M₀ z w + z ⬝ᵥ ((C.map star)ᵀ * M.map star * C) *ᵥ star w := by
    conv_lhs => rw [hc]
    rw [hermForm, add_mulVec, dotProduct_add]
  rw [e, e1, ← e2, ← e4]
  simp only [Complex.add_im, Complex.star_def, Complex.conj_im]
  ring

end GlobalTheory.PeriodCoord
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannRelationConverseConjAffineStatement
open Matrix GlobalTheory.PELU
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemann_relation_converse_conjAffine : ∀ {g : ℕ} (M₀ C : Matrix (Fin g) (Fin g) ℂ), M₀ᴴ = M₀ → M₀.det ≠ 0 → (Cᵀ * M₀)ᵀ = Cᵀ * M₀ → (1 - C.map star * C).det ≠ 0 → (M₀ * (1 - C.map star * C)⁻¹)ᴴ = M₀ * (1 - C.map star * C)⁻¹ ∧ ∀ z w : Fin g → ℂ, (hermForm (M₀ * (1 - C.map star * C)⁻¹) (z + C *ᵥ star z) (w + C *ᵥ star w)).im = (hermForm M₀ z w).im := by
  first | exact @GlobalTheory.PeriodCoord.riemann_converse | exact GlobalTheory.PeriodCoord.riemann_converse | (intros; apply GlobalTheory.PeriodCoord.riemann_converse; all_goals assumption)
end
end
