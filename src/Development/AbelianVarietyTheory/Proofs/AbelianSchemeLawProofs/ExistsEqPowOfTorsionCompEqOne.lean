module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MemRangeRTensorOfForallDual
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsEqPowOfTorsionCompEqOne
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DivisibleHom

variable {S : Scheme.{0}}

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.DivisibleHom.cancel_of_flat_surjective {X Y Z : Over S} (e : X ⟶ Y) [Flat e.left]
    [Surjective e.left] {f g : Y ⟶ Z} (h : e ≫ f = e ≫ g) : f = g := by
  haveI := Flat.epi_of_flat_of_surjective e.left
  ext1
  rw [← cancel_epi e.left]
  simpa using congrArg CommaMorphism.left h

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.DivisibleHom.exists_lift_point {A A' T : Over S} (m : A' ⟶ A) [Flat m.left]
    [Surjective m.left] (y : T ⟶ A) :
    ∃ (T' : Over S) (e : T' ⟶ T) (x : T' ⟶ A'), Flat e.left ∧ Surjective e.left ∧
      x ≫ m = e ≫ y := by
  refine ⟨Over.mk (pullback.snd m.left y.left ≫ T.hom), Over.homMk (pullback.snd m.left y.left) rfl,
    Over.homMk (pullback.fst m.left y.left) ?_, ?_, ?_, ?_⟩
  · show pullback.fst m.left y.left ≫ A'.hom = pullback.snd m.left y.left ≫ T.hom
    rw [← Over.w m, ← Category.assoc, pullback.condition, Category.assoc, Over.w y]
  · show Flat (pullback.snd m.left y.left)
    infer_instance
  · show Surjective (pullback.snd m.left y.left)
    infer_instance
  · ext1
    simp [pullback.condition]

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.DivisibleHom.isMonHom_of_mul_points {G H : Over S} [GrpObj G] [GrpObj H] (e : G ⟶ H)
    (mul : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ e = (x ≫ e) * (y ≫ e)) : IsMonHom e := by
  have hone : (1 : 𝟙_ (Over S) ⟶ G) ≫ e = 1 := by
    have h := mul (𝟙_ (Over S)) 1 1
    rw [_root_.mul_one] at h
    simpa using h
  have hG : (η : 𝟙_ (Over S) ⟶ G) = 1 := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have hH : (η : 𝟙_ (Over S) ⟶ H) = 1 := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have h := mul (G ⊗ G) (fst G G) (snd G G)
  rw [Hom.mul_def, lift_fst_snd, Category.id_comp, Hom.mul_def] at h
  have ht : lift (fst G G ≫ e) (snd G G ≫ e) = e ⊗ₘ e := by ext <;> simp
  refine ⟨?_, ?_⟩
  · rw [hG, hH, hone]
  · rw [h, ht]

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.DivisibleHom.comp_mulA {A T : Over S} [GrpObj A] (x : T ⟶ A) (n : ℕ) :
    x ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A n = x ^ n := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA
  rw [comp_pow, Category.comp_id]

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.DivisibleHom.mulA_comp {A B : Over S} [GrpObj A] [GrpObj B] (u : A ⟶ B) [IsMonHom u]
    (n : ℕ) : _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A n ≫ u = u ^ n := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA
  rw [pow_comp, Category.id_comp]

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.DivisibleHom.exists_factor {A B : Over S} [GrpObj A] [IsCommMonObj A]
    [GrpObj B] (M : ℕ)
    [QuasiCompact (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left] [Flat (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left] [Surjective (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left]
    (u : A ⟶ B) [IsMonHom u] (hu : ∀ (T : Over S) (x : T ⟶ A), x ^ M = 1 → x ≫ u = 1) :
    ∃ φ : A ⟶ B, _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M ≫ φ = u := by
  have key : ∀ {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ A.left),
      g₁ ≫ (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left = g₂ ≫ (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left → g₁ ≫ u.left = g₂ ≫ u.left := by
    intro Z g₁ g₂ hg
    have hw : g₂ ≫ A.hom = g₁ ≫ A.hom := by
      rw [← Over.w (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M), ← Category.assoc, ← hg, Category.assoc]
    let x₁ : Over.mk (g₁ ≫ A.hom) ⟶ A := Over.homMk g₁ rfl
    let x₂ : Over.mk (g₁ ≫ A.hom) ⟶ A := Over.homMk g₂ hw
    have hx : x₁ ^ M = x₂ ^ M := by
      rw [← _root_.GlobalTheory.DivisibleHom.comp_mulA, ← _root_.GlobalTheory.DivisibleHom.comp_mulA]
      ext1
      simpa [x₁, x₂] using hg
    have h1 : (x₁ * x₂⁻¹) ^ M = 1 := by rw [mul_pow, inv_pow, hx, mul_inv_cancel]
    have h3 : IsMonHom.monoidHom u _ (x₁ * x₂⁻¹) = 1 := hu _ _ h1
    rw [map_mul, map_inv, mul_inv_eq_one] at h3
    simpa [x₁, x₂] using congrArg CommaMorphism.left h3
  refine ⟨Over.homMk (EffectiveEpi.desc _ _ key) ?_, ?_⟩
  · rw [← cancel_epi (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left, ← Category.assoc, EffectiveEpi.fac, Over.w u,
      Over.w (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M)]
  · ext1
    simp [EffectiveEpi.fac]

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.DivisibleHom.isMonHom_of_factor {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B]
    (M : ℕ) [Flat (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left] [Surjective (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M).left]
    (φ : A ⟶ B) [IsMonHom (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M ≫ φ)] : IsMonHom φ := by
  have hmm : ∀ (T : Over S) (a b : T ⟶ A),
      (a * b) ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M = (a ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M) * (b ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M) := by
    intro T a b
    simp only [_root_.GlobalTheory.DivisibleHom.comp_mulA, mul_pow]
  apply _root_.GlobalTheory.DivisibleHom.isMonHom_of_mul_points
  intro T x y
  obtain ⟨T₁, e₁, x', he₁, hs₁, hx'⟩ := _root_.GlobalTheory.DivisibleHom.exists_lift_point (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M) x
  haveI := he₁
  haveI := hs₁
  obtain ⟨T₂, e₂, y', he₂, hs₂, hy'⟩ :=
    _root_.GlobalTheory.DivisibleHom.exists_lift_point (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M) (e₁ ≫ y)
  haveI := he₂
  haveI := hs₂
  haveI : Flat (e₂ ≫ e₁).left := by rw [Over.comp_left]; infer_instance
  haveI : Surjective (e₂ ≫ e₁).left := by rw [Over.comp_left]; infer_instance
  have hxe : (e₂ ≫ e₁) ≫ x = (e₂ ≫ x') ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M := by
    rw [Category.assoc, ← hx', Category.assoc]
  have hye : (e₂ ≫ e₁) ≫ y = y' ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M := by
    rw [Category.assoc, ← hy']
  apply _root_.GlobalTheory.DivisibleHom.cancel_of_flat_surjective (e₂ ≫ e₁)
  calc (e₂ ≫ e₁) ≫ (x * y) ≫ φ = (((e₂ ≫ e₁) ≫ x) * ((e₂ ≫ e₁) ≫ y)) ≫ φ := by
        rw [← Category.assoc (e₂ ≫ e₁), comp_mul]
    _ = (((e₂ ≫ x') * y') ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M) ≫ φ := by rw [hxe, hye, hmm]
    _ = ((e₂ ≫ x') ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M ≫ φ) * (y' ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.mulA A M ≫ φ) := by
        rw [Category.assoc, mul_comp]
    _ = (e₂ ≫ e₁) ≫ ((x ≫ φ) * (y ≫ φ)) := by
        rw [comp_mul, ← Category.assoc (e₂ ≫ e₁) x, ← Category.assoc (e₂ ≫ e₁) y, hxe, hye]
        simp only [Category.assoc]

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.DivisibleHom.exists_eq_pow_of_torsion_comp_eq_one :
    (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV S) (n : ℕ), 1 ≤ n →
      IsFinite (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A n).left ∧ Flat (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A n).left ∧
        Surjective (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A n).left ∧
          (IsUnit (n : Γ(S, ⊤)) → Etale (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A n).left)) →
    ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV S) (B : Over S) [GrpObj B]
      [IsCommMonObj B] (M : ℕ), 1 ≤ M → ∀ u : P.A ⟶ B, IsMonHom u →
        (∀ (T : Over S) (x : T ⟶ P.A), x ^ M = 1 → x ≫ u = 1) →
          (∃ φ : P.A ⟶ B, IsMonHom φ ∧ u = φ ^ M) ∧ (u ^ M = 1 → u = 1) := by
  intro H S _ P B _ _ M hM u hu hkill
  obtain ⟨hfin, hflat, hsurj, -⟩ := H S P M hM
  haveI := hfin
  haveI := hflat
  haveI := hsurj
  haveI := hu
  obtain ⟨φ, hφ⟩ := _root_.GlobalTheory.DivisibleHom.exists_factor M u hkill
  haveI : IsMonHom (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A M ≫ φ) := by rw [hφ]; infer_instance
  haveI := _root_.GlobalTheory.DivisibleHom.isMonHom_of_factor M φ
  refine ⟨⟨φ, inferInstance, ?_⟩, fun h => ?_⟩
  · rw [← hφ, _root_.GlobalTheory.DivisibleHom.mulA_comp]
  · apply _root_.GlobalTheory.DivisibleHom.cancel_of_flat_surjective (_root_.ReciprocityTheory.ChartRestriction.G.Out.mulA P.A M)
    rw [_root_.GlobalTheory.DivisibleHom.mulA_comp, h, comp_one]

end GlobalTheory.DivisibleHom
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineOpenInfOfIsSeparated
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KuennethOne

section General

open TopologicalSpace TensorProduct

theorem lid_rTensor_lTensor {R C A B : Type} [CommRing R] [AddCommGroup C] [Module R C]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] (l : C →ₗ[R] R) (f : B →ₗ[R] A)
    (w : C ⊗[R] B) : TensorProduct.lid R A (l.rTensor A (f.lTensor C w)) =
      f (TensorProduct.lid R B (l.rTensor B w)) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem apply_lid_rTensor {R C B : Type} [CommRing R] [AddCommGroup C] [Module R C]
    [AddCommGroup B] [Module R B] (l : C →ₗ[R] R) (f : B →ₗ[R] R) (w : C ⊗[R] B) :
    f (TensorProduct.lid R B (l.rTensor B w)) = l (TensorProduct.rid R C (f.lTensor C w)) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [mul_comm]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

variable {S X Y Z : Scheme.{0}} {p : Z ⟶ X} {q : Z ⟶ Y} {iX : X ⟶ S} {iY : Y ⟶ S}
  (H : IsPullback p q iX iY) {I : Type} {V : I → Z.Opens} {φ : ∀ a b, Γ(Z, V a ⊓ V b)}

include H

theorem isAffineOpen_prod [IsAffine S] {U : X.Opens} {W : Y.Opens} (hU : IsAffineOpen U)
    (hW : IsAffineOpen W) : IsAffineOpen (p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ W) := by
  have : IsAffine _ := isAffineOpen_top S
  have : IsAffine _ := hU
  have : IsAffine _ := hW
  exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := W) (UX := U) le_top le_top
    rfl).isoPullback.hom

theorem exists_splits_preimage [IsAffine S] (hR : IsField Γ(S, ⊤)) [CompactSpace X]
    (hX : ∀ U U' : X.Opens, IsAffineOpen U → IsAffineOpen U' → IsAffineOpen (U ⊓ U'))
    (hY : ∀ U U' : Y.Opens, IsAffineOpen U → IsAffineOpen U' → IsAffineOpen (U ⊓ U'))
    (hiY : Function.Surjective iY.appTop.hom)
    {y : S ⟶ Y} (hy : y ≫ iY = 𝟙 S) {s : X ⟶ Z} (hs : s ≫ p = 𝟙 X) (hs' : s ≫ q = iX ≫ y)
    (W₀ : Y.affineOpens) (hW₀ : ⊤ ≤ y ⁻¹ᵁ W₀.1)
    (hV : ⨆ a, V a = ⊤) (hφ : IsCocycle V φ) (ρ : ∀ a, Γ(X, s ⁻¹ᵁ V a))
    (hρ : ∀ a b, (s.app (V a ⊓ V b)).hom (φ a b) =
      rs (s.preimage_mono inf_le_left) (ρ a) - rs (s.preimage_mono inf_le_right) (ρ b))
    (W : Y.affineOpens) : ∃ τ, Splits V φ (q ⁻¹ᵁ W.1) τ := by
  obtain ⟨I₀, hI₀, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp
    (show IsCompact ((⊤ : X.Opens) : Set X) by simpa using isCompact_univ)
  have := hI₀.to_subtype
  let U : I₀ → X.Opens := fun i => i.1.1
  have hU : ∀ i, IsAffineOpen (U i) := fun i => i.1.2
  have hUtop : iSup U = ⊤ := by rw [e, iSup_subtype]
  let U₂ : I₀ × I₀ → X.Opens := fun k => U k.1 ⊓ U k.2
  have hU₂ : ∀ k, IsAffineOpen (U₂ k) := fun k => hX _ _ (hU _) (hU _)
  have l1 : ∀ k : I₀ × I₀, p ⁻¹ᵁ U₂ k ≤ p ⁻¹ᵁ U k.1 := fun k => p.preimage_mono inf_le_left
  have l2 : ∀ k : I₀ × I₀, p ⁻¹ᵁ U₂ k ≤ p ⁻¹ᵁ U k.2 := fun k => p.preimage_mono inf_le_right
  choose σ hσ using fun (i : I₀) (j : Y.affineOpens) =>
    exists_splits_of_isAffineOpen hV hφ (isAffineOpen_prod H (hU i) j.2)
  choose c hc using fun (j : Y.affineOpens) (k : I₀ × I₀) =>
    exists_isDiff hV (hσ k.1 j) (hσ k.2 j) (P := p ⁻¹ᵁ U₂ k ⊓ q ⁻¹ᵁ j.1)
      (inf_le_inf_right _ (l1 k)) (inf_le_inf_right _ (l2 k))
  choose z hz using fun j : Y.affineOpens => MM_surj H hU₂ j.2 (c j)
  have hcompat : ∀ (j k : Y.affineOpens), ∃ w,
      (rsA iY (inf_le_left : j.1 ⊓ k.1 ≤ j.1)).toLinearMap.lTensor _ (z j) -
        (rsA iY inf_le_right).toLinearMap.lTensor _ (z k) - (dlt iX U).rTensor _ w = 0 := by
    intro j k
    have hW' := hY _ _ j.2 k.2
    have m1 : q ⁻¹ᵁ (j.1 ⊓ k.1) ≤ q ⁻¹ᵁ j.1 := q.preimage_mono inf_le_left
    have m2 : q ⁻¹ᵁ (j.1 ⊓ k.1) ≤ q ⁻¹ᵁ k.1 := q.preimage_mono inf_le_right
    choose d hd using fun i : I₀ => exists_isDiff hV (hσ i j) (hσ i k)
      (P := p ⁻¹ᵁ U i ⊓ q ⁻¹ᵁ (j.1 ⊓ k.1)) (inf_le_inf_left _ m1) (inf_le_inf_left _ m2)
    obtain ⟨w, hw⟩ := MM_surj H hU hW' d
    refine ⟨w, MM_inj H hU₂ hW' _ fun m => ?_⟩
    rw [map_sub, map_sub, MM_lTensor, MM_lTensor, MM_dlt]
    have a1 := congrArg (rs (inf_le_inf_left (p ⁻¹ᵁ U₂ m) m1)) (hz j m)
    have a2 := congrArg (rs (inf_le_inf_left (p ⁻¹ᵁ U₂ m) m2)) (hz k m)
    have a3 := congrArg (rs (inf_le_inf_right (q ⁻¹ᵁ (j.1 ⊓ k.1)) (l1 m))) (hw m.1)
    have a4 := congrArg (rs (inf_le_inf_right (q ⁻¹ᵁ (j.1 ⊓ k.1)) (l2 m))) (hw m.2)
    rw [rs_MM] at a1 a2 a3 a4
    rw [a1, a2, a3, a4]
    refine loc V (by rw [hV]; exact le_top) _ _ fun a => ?_
    have b1 := hc j m a (p ⁻¹ᵁ U₂ m ⊓ q ⁻¹ᵁ (j.1 ⊓ k.1) ⊓ V a)
      (inf_le_left.trans (inf_le_inf_left _ m1)) inf_le_right
    have b2 := hc k m a (p ⁻¹ᵁ U₂ m ⊓ q ⁻¹ᵁ (j.1 ⊓ k.1) ⊓ V a)
      (inf_le_left.trans (inf_le_inf_left _ m2)) inf_le_right
    have b3 := hd m.1 a (p ⁻¹ᵁ U₂ m ⊓ q ⁻¹ᵁ (j.1 ⊓ k.1) ⊓ V a)
      (inf_le_left.trans (inf_le_inf_right _ (l1 m))) inf_le_right
    have b4 := hd m.2 a (p ⁻¹ᵁ U₂ m ⊓ q ⁻¹ᵁ (j.1 ⊓ k.1) ⊓ V a)
      (inf_le_left.trans (inf_le_inf_right _ (l2 m))) inf_le_right
    simp only [map_sub, map_zero, rs_rs]
    linear_combination b1 - b2 - b3 + b4
  have hN : ∀ (N : X.Opens), N ≤ s ⁻¹ᵁ (p ⁻¹ᵁ N ⊓ q ⁻¹ᵁ W₀.1) := by
    intro N
    rw [s.preimage_inf, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hs, hs']
    exact le_inf le_rfl (le_top.trans (iX.preimage_mono hW₀))
  obtain ⟨x, hx⟩ := pull_coboundary hV s ρ hρ (fun i => p ⁻¹ᵁ U i ⊓ q ⁻¹ᵁ W₀.1)
    (fun i => σ i W₀) (fun i => hσ i W₀) U (fun i => hN _)
  have hz₀ : TensorProduct.rid _ _ ((evA y hy W₀.1 hW₀).toLinearMap.lTensor _ (z W₀)) =
      dlt iX U x := by
    funext m
    refine (section_MM H hy hs hs' U₂ W₀.1 hW₀ m _ inf_le_left inf_le_right (hN _) (z W₀)).symm.trans ?_
    rw [hz W₀ m]
    exact hx m.1 m.2 _ _ _ _ (hc W₀ m) _ inf_le_left inf_le_right _
  have hl : ∀ l : (∀ k, Fn iX (U₂ k)) →ₗ[Γ(S, ⊤)] Γ(S, ⊤), l ∘ₗ dlt iX U = 0 →
      TensorProduct.lid _ _ (l.rTensor _ (z W)) = 0 := by
    intro l hl
    let b : ∀ j : Y.affineOpens, Fn iY j.1 := fun j => TensorProduct.lid _ _ (l.rTensor _ (z j))
    obtain ⟨β, hβ⟩ := glue ⊤ (fun j : Y.affineOpens => j.1) (fun _ => le_top)
      (iSup_affineOpens_eq_top Y).ge b (by
        intro j k
        obtain ⟨w, hw⟩ := hcompat j k
        have := congrArg (fun t => TensorProduct.lid _ _ (l.rTensor _ t)) hw
        simp only [map_sub, map_zero] at this
        rw [lid_rTensor_lTensor, lid_rTensor_lTensor, ← LinearMap.rTensor_comp_apply, hl] at this
        simp only [LinearMap.rTensor_zero, LinearMap.zero_apply, map_zero, sub_zero] at this
        exact sub_eq_zero.mp this)
    obtain ⟨r, rfl⟩ := hiY β
    have hb : ∀ j : Y.affineOpens, b j = algebraMap Γ(S, ⊤) (Fn iY j.1) r := by
      intro j
      refine (hβ j).symm.trans ?_
      have : iY.appTop = iY.appLE ⊤ ⊤ le_top := iY.app_eq_appLE (U := ⊤)
      rw [this]
      exact rs_appLE iY _ _ r
    have hr : r = 0 := by
      have h1 := apply_lid_rTensor l (evA y hy W₀.1 hW₀).toLinearMap (z W₀)
      rw [hz₀, show l (dlt iX U x) = 0 from LinearMap.congr_fun hl x] at h1
      have h2 : evA y hy W₀.1 hW₀ (b W₀) = 0 := h1
      rwa [hb, AlgHom.commutes] at h2
    have := hb W
    rwa [hr, map_zero] at this
  obtain ⟨w, hw⟩ := mem_range_rTensor_of_forall_dual hR (dlt iX U) (z W) hl
  refine splits_glue (fun i => p ⁻¹ᵁ U i ⊓ q ⁻¹ᵁ W.1) (fun i => σ i W) (fun i => hσ i W)
    (fun i => MM H U W.1 i _ inf_le_left inf_le_right w) ?_ _ ?_
  · intro i k a M hi hk ha
    have hM : M ≤ p ⁻¹ᵁ U₂ (i, k) ⊓ q ⁻¹ᵁ W.1 := by
      refine le_inf ?_ (hi.trans inf_le_right)
      rw [p.preimage_inf]
      exact le_inf (hi.trans inf_le_left) (hk.trans inf_le_left)
    have b1 := hc W (i, k) a M hM ha
    rw [← hz W (i, k), rs_MM, ← hw, MM_dlt] at b1
    rw [rs_MM, rs_MM]
    exact b1.symm
  · rw [← iSup_inf_eq, ← p.preimage_iSup, hUtop]
    exact le_inf le_top le_rfl

theorem exists_splits_top [IsAffine S] [Flat iY] [CompactSpace X] [QuasiSeparatedSpace X]
    (hY : ∀ U U' : Y.Opens, IsAffineOpen U → IsAffineOpen U' → IsAffineOpen (U ⊓ U'))
    (hiX : Function.Bijective iX.appTop.hom) {t : Y ⟶ Z} (ht : t ≫ q = 𝟙 Y)
    (hV : ⨆ a, V a = ⊤) (ρ : ∀ a, Γ(Y, t ⁻¹ᵁ V a))
    (hρ : ∀ a b, (t.app (V a ⊓ V b)).hom (φ a b) =
      rs (t.preimage_mono inf_le_left) (ρ a) - rs (t.preimage_mono inf_le_right) (ρ b))
    (hτ : ∀ W : Y.affineOpens, ∃ τ, Splits V φ (q ⁻¹ᵁ W.1) τ) : ∃ χ, Splits V φ ⊤ χ := by
  choose τ hτ using hτ
  have hN : ∀ N : Y.Opens, N ≤ t ⁻¹ᵁ (q ⁻¹ᵁ N) := by
    intro N
    rw [← Scheme.Hom.comp_preimage, ht]
    exact le_rfl
  have hN' : ∀ N : Y.Opens, N ≤ (𝟙 Y : Y ⟶ Y) ⁻¹ᵁ N := fun N => le_rfl
  obtain ⟨x, hx⟩ := pull_coboundary hV t ρ hρ (fun j : Y.affineOpens => q ⁻¹ᵁ j.1) τ hτ
    (fun j => j.1) (fun j => hN _)
  refine splits_glue (fun j : Y.affineOpens => q ⁻¹ᵁ j.1) τ hτ
    (fun j => (q.appLE j.1 _ le_rfl).hom (x j)) ?_ ⊤ ?_
  · intro j k a M hj hk ha
    have hW' := hY _ _ j.2 k.2
    have m1 : q ⁻¹ᵁ (j.1 ⊓ k.1) ≤ q ⁻¹ᵁ j.1 := q.preimage_mono inf_le_left
    have m2 : q ⁻¹ᵁ (j.1 ⊓ k.1) ≤ q ⁻¹ᵁ k.1 := q.preimage_mono inf_le_right
    obtain ⟨e, he⟩ := exists_isDiff hV (hτ j) (hτ k) m1 m2
    have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := j.1 ⊓ k.1) (UX := ⊤)
      (UY := q ⁻¹ᵁ (j.1 ⊓ k.1)) le_top le_top (by simp)).1
      (isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H _ _ _ (isAffineOpen_top _) hW'
        (by simpa using isCompact_univ) (by simpa using isQuasiSeparated_univ))
    have : IsIso (iX.appLE ⊤ ⊤ le_top) := by
      have e : iX.appTop = iX.appLE ⊤ ⊤ le_top := iX.app_eq_appLE (U := ⊤)
      rw [← e]
      exact (ConcreteCategory.isIso_iff_bijective _).mpr hiX
    have hiso := po.isIso_inr_of_isIso
    obtain ⟨u, hu⟩ := (ConcreteCategory.bijective_of_isIso
      (q.appLE (j.1 ⊓ k.1) (q ⁻¹ᵁ (j.1 ⊓ k.1)) le_rfl)).2 e
    have hu' : (q.appLE (j.1 ⊓ k.1) (q ⁻¹ᵁ (j.1 ⊓ k.1)) le_rfl).hom u = e := hu
    have h1 := hx j k _ m1 m2 e he (j.1 ⊓ k.1) inf_le_left inf_le_right (hN _)
    rw [← hu', appLE_appLE t q _ ht _ _ (hN' _), id_appLE, rs_self] at h1
    have hM : M ≤ q ⁻¹ᵁ (j.1 ⊓ k.1) := by rw [q.preimage_inf]; exact le_inf hj hk
    have h2 := he a M hM ha
    rw [← hu', h1] at h2
    simp only [map_sub, appLE_rs, rs_appLE] at h2 ⊢
    exact h2.symm
  · rw [← q.preimage_iSup, iSup_affineOpens_eq_top]
    exact le_top

end General

theorem isAffineOpen_inf_of_isSeparated {X S : Scheme.{0}} [IsAffine S] (f : X ⟶ S)
    [IsSeparated f] (U U' : X.Opens) (hU : IsAffineOpen U) (hU' : IsAffineOpen U') :
    IsAffineOpen (U ⊓ U') := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  exact hU.inf hU'

theorem kuenneth_injective :
    ∀ (K : Type) [Field K] (X Y : Over (Spec (CommRingCat.of K))) (x₀ : 𝟙_ _ ⟶ X) (y₀ : 𝟙_ _ ⟶ Y), IsSeparated X.hom → QuasiCompact X.hom → IsSeparated Y.hom → QuasiCompact Y.hom → Function.Bijective X.hom.appTop.hom → Function.Bijective Y.hom.appTop.hom → ∀ (I : Type) (V : I → (X ⊗ Y).left.Opens), ⨆ a, V a = ⊤ → ∀ φ : ∀ a b, Γ((X ⊗ Y).left, V a ⊓ V b), (∀ a b d, ((X ⊗ Y).left.presheaf.map (homOfLE (inf_le_left : V a ⊓ V b ⊓ V d ≤ V a ⊓ V b)).op).hom (φ a b) + ((X ⊗ Y).left.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right : V a ⊓ V b ⊓ V d ≤ V b ⊓ V d)).op).hom (φ b d) = ((X ⊗ Y).left.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right : V a ⊓ V b ⊓ V d ≤ V a ⊓ V d)).op).hom (φ a d)) → (∃ ψ : ∀ a, Γ(X.left, (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ V a), ∀ a b, ((lift (𝟙 X) (toUnit X ≫ y₀)).left.app (V a ⊓ V b)).hom (φ a b) = (X.left.presheaf.map (homOfLE (show (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ (V a ⊓ V b) ≤ (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ V a from fun _ h => h.1)).op).hom (ψ a) - (X.left.presheaf.map (homOfLE (show (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ (V a ⊓ V b) ≤ (lift (𝟙 X) (toUnit X ≫ y₀)).left ⁻¹ᵁ V b from fun _ h => h.2)).op).hom (ψ b)) → (∃ ψ : ∀ a, Γ(Y.left, (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ V a), ∀ a b, ((lift (toUnit Y ≫ x₀) (𝟙 Y)).left.app (V a ⊓ V b)).hom (φ a b) = (Y.left.presheaf.map (homOfLE (show (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ (V a ⊓ V b) ≤ (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ V a from fun _ h => h.1)).op).hom (ψ a) - (Y.left.presheaf.map (homOfLE (show (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ (V a ⊓ V b) ≤ (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ⁻¹ᵁ V b from fun _ h => h.2)).op).hom (ψ b)) → ∃ ψ : ∀ a, Γ((X ⊗ Y).left, V a), ∀ a b, φ a b = ((X ⊗ Y).left.presheaf.map (homOfLE inf_le_left).op).hom (ψ a) - ((X ⊗ Y).left.presheaf.map (homOfLE inf_le_right).op).hom (ψ b) := by
  intro K _ X Y x₀ y₀ sX qX sY qY bX bY I V hV φ hφ ⟨ρX, hρX⟩ ⟨ρY, hρY⟩
  have H : IsPullback (fst X Y).left (snd X Y).left X.hom Y.hom :=
    IsPullback.of_hasPullback X.hom Y.hom
  have hR : IsField Γ(Spec (CommRingCat.of K), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField K)
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : QuasiSeparatedSpace X.left := (quasiSeparated_iff_quasiSeparatedSpace X.hom).mp inferInstance
  have : Flat Y.hom := inferInstance
  have hco : IsCocycle V φ := by
    intro a b d N ha hb hd
    have := congrArg (rs (le_inf (le_inf ha hb) hd)) (hφ a b d)
    rw [map_add (f := _)] at this
    exact (congrArg₂ _ (rs_rs _ _ _) (rs_rs _ _ _)).symm.trans (this.trans (rs_rs _ _ _))
  let y : Spec (CommRingCat.of K) ⟶ Y.left := y₀.left
  have hy : y ≫ Y.hom = 𝟙 _ := Over.w y₀
  have hs : (lift (𝟙 X) (toUnit X ≫ y₀)).left ≫ (fst X Y).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst]; rfl
  have hs' : (lift (𝟙 X) (toUnit X ≫ y₀)).left ≫ (snd X Y).left = X.hom ≫ y := by
    rw [← Over.comp_left, lift_snd]; rfl
  have ht : (lift (toUnit Y ≫ x₀) (𝟙 Y)).left ≫ (snd X Y).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd]; rfl
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : Y.left.affineOpens, ⊤ ≤ y ⁻¹ᵁ W₀.1 := by
    have : y default ∈ ⨆ W : Y.left.affineOpens, W.1 := by
      rw [iSup_affineOpens_eq_top]; trivial
    obtain ⟨W, hW⟩ := TopologicalSpace.Opens.mem_iSup.mp this
    refine ⟨W, fun z _ => ?_⟩
    rw [Subsingleton.elim z default]
    exact hW
  obtain ⟨χ, hχ⟩ := exists_splits_top H (isAffineOpen_inf_of_isSeparated Y.hom) bX ht hV ρY hρY
    (exists_splits_preimage H hR (isAffineOpen_inf_of_isSeparated X.hom)
      (isAffineOpen_inf_of_isSeparated Y.hom) bY.2 hy hs hs' W₀ hW₀ hV hco ρX hρX)
  refine ⟨fun a => rs (le_inf le_top le_rfl) (χ a), fun a b => ?_⟩
  have := hχ a b (V a ⊓ V b) le_top inf_le_left inf_le_right
  rw [rs_self] at this
  exact this.trans (congrArg₂ _ (rs_rs _ _ _) (rs_rs _ _ _)).symm

end GlobalTheory.KuennethOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SurjectiveAppOfIsAbelianScheme
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem eq_comp_section_of_local_rigidity {X T Y S : Scheme.{0}} (p : X ⟶ T) (ε : T ⟶ X)
    (g : X ⟶ Y) (π : T ⟶ S) (q : Y ⟶ S) [IsSeparated q] (he : ε ≫ p = 𝟙 T)
    (hg : g ≫ q = p ≫ π) (hp : IsOpenMap p)
    (hloc : ∀ (t : T) (y : Y), (∀ x : X, p x = t → g x = y) →
      ∃ V : T.Opens, t ∈ V ∧ (p ⁻¹ᵁ V).ι ≫ g = (p ⁻¹ᵁ V).ι ≫ p ≫ ε ≫ g)
    (hconn : ∀ s : S, _root_.IsPreconnected (π ⁻¹' {s}))
    (hmeet : ∀ s : S, ∃ (t : T) (y : Y), π t = s ∧ ∀ x : X, p x = t → g x = y) :
    g = p ≫ ε ≫ g := by
  have hab : g ≫ q = (p ≫ ε ≫ g) ≫ q := by
    simp only [Category.assoc, hg, reassoc_of% he]
  have hcl := isClosedImmersion_equalizer_ι_of_isSeparated q hab
  let Z : Set X := Set.range (equalizer.ι g (p ≫ ε ≫ g))
  have hZ : IsClosed Z := (equalizer.ι g (p ≫ ε ≫ g)).isClosedEmbedding.isClosed_range
  let T₀ : Set T := (p '' Zᶜ)ᶜ
  have hT₀c : IsClosed T₀ := (hp _ hZ.isOpen_compl).isClosed_compl
  have hfib : ∀ t ∈ T₀, ∀ x : X, p x = t → g x = g (ε t) := by
    intro t ht x hx
    have hxZ : x ∈ Z := by
      by_contra h
      exact ht ⟨x, h, hx⟩
    obtain ⟨z, rfl⟩ := hxZ
    rw [← hx, ← Scheme.Hom.comp_apply, equalizer.condition]
    simp only [Scheme.Hom.comp_apply]
  have hsub : ∀ V : T.Opens, (p ⁻¹ᵁ V).ι ≫ g = (p ⁻¹ᵁ V).ι ≫ p ≫ ε ≫ g → (V : Set T) ⊆ T₀ := by
    rintro V hV t ht ⟨x, hx, rfl⟩
    exact hx (range_subset_range_equalizer_ι _ hV ⟨⟨x, ht⟩, rfl⟩)
  have hT₀o : IsOpen T₀ := by
    rw [isOpen_iff_forall_mem_open]
    intro t ht
    obtain ⟨V, htV, hV⟩ := hloc t _ (hfib t ht)
    exact ⟨V, hsub V hV, V.2, htV⟩
  have hall : ∀ t : T, t ∈ T₀ := by
    intro t
    obtain ⟨t', y, ht', hy⟩ := hmeet (π t)
    obtain ⟨V, htV, hV⟩ := hloc t' y hy
    exact (hconn (π t)).subset_isClopen ⟨hT₀c, hT₀o⟩ ⟨t', ht', hsub V hV htV⟩ rfl
  refine Scheme.hom_ext_of_forall _ _ fun x ↦ ?_
  obtain ⟨V, htV, hV⟩ := hloc (p x) _ (hfib _ (hall _))
  exact ⟨p ⁻¹ᵁ V, htV, hV⟩

theorem surjective_app_of_isAbelianScheme (hG : GlobalFnsSt) {S : Scheme.{0}} (A : Over S)
    [GrpObj A] (hA : IsAbelianScheme A) (V : S.Opens) :
    Function.Surjective (A.hom.app V).hom := by
  have h1 : Function.Surjective (pullback.snd A.hom V.ι).appTop.hom :=
    (hG _ _ (TLinPf.isAb_pullback V.ι A hA)).2
  have h2 : Function.Surjective (A.hom ∣_ V).appTop.hom := by
    have e : A.hom ∣_ V = (pullbackRestrictIsoRestrict A.hom V).inv ≫ pullback.snd A.hom V.ι := rfl
    rw [e, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso
      ((pullbackRestrictIsoRestrict A.hom V).inv.app ⊤)).2.comp h1
  rw [morphismRestrict_appTop] at h2
  have h3 : Function.Surjective (A.hom.app (V.ι ''ᵁ ⊤)).hom := by
    have hb : Function.Bijective (A.left.presheaf.map
        (eqToHom (image_morphismRestrict_preimage A.hom V ⊤)).op).hom := by
      rw [eqToHom_op]
      exact ConcreteCategory.bijective_of_isIso (A.left.presheaf.map (eqToHom _))
    exact (Function.Surjective.of_comp_iff' hb _).1 h2
  rwa [V.ι_image_top] at h3

theorem rigidity_of_local_rigidity : GlobalFnsSt → (∀ (X T Y : Scheme.{0}) (p : X ⟶ T) (ε : T ⟶ X) (g : X ⟶ Y), ε ≫ p = 𝟙 T → UniversallyClosed p → (∀ V : T.Opens, Function.Surjective (p.app V).hom) → ∀ (t : T) (y : Y), (∀ x : X, p x = t → g x = y) → ∃ V : T.Opens, t ∈ V ∧ (p ⁻¹ᵁ V).ι ≫ g = (p ⁻¹ᵁ V).ι ≫ p ≫ ε ≫ g) → RigiditySt := by
  intro hG hR S A B _ _ hA hB f hf
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have := hB.proper
  let g : A ⊗ A ⟶ B := (fst A A ≫ f)⁻¹ * ((fst A A * snd A A) ≫ f)
  let ε : A ⟶ A ⊗ A := lift 1 (𝟙 A)
  let j : A ⟶ A ⊗ A := lift (𝟙 A) 1
  have h1 : (1 : A ⟶ A) ≫ f = 1 := by
    rw [Hom.one_def, Category.assoc, hf, Hom.one_def]
  have hε : ε ≫ g = f := by
    simp only [g, ε, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, lift_fst, lift_snd, h1,
      inv_one, _root_.one_mul, Category.id_comp]
  have hj : j ≫ g = 1 := by
    simp only [g, j, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, lift_fst, lift_snd,
      _root_.mul_one, inv_mul_cancel]
  have hεp : ε.left ≫ (snd A A).left = 𝟙 A.left := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have hsm : Smooth (snd A A).left := by
    change Smooth (pullback.snd A.hom A.hom); infer_instance
  have huc : UniversallyClosed (snd A A).left := by
    change UniversallyClosed (pullback.snd A.hom A.hom); infer_instance
  have hsurj : ∀ V : A.left.Opens, Function.Surjective ((snd A A).left.app V).hom := fun V ↦
    surjective_app_of_isAbelianScheme hG _ (TLinPf.isAb_pullback A.hom A hA) V
  have hη : (η[A] : 𝟙_ (Over S) ⟶ A).left ≫ A.hom = 𝟙 S := Over.w η[A]
  have hpb : IsPullback j.left A.hom (snd A A).left (η[A] : 𝟙_ (Over S) ⟶ A).left := by
    have hr : IsPullback (fst A A).left (snd A A).left A.hom A.hom := .of_hasPullback A.hom A.hom
    refine IsPullback.of_right ?_ ?_ hr
    · have : j.left ≫ (fst A A).left = 𝟙 A.left := by
        rw [← Over.comp_left, lift_fst, Over.id_left]
      rw [this, hη]
      exact IsPullback.of_id_fst
    · rw [← Over.comp_left, lift_snd, Hom.one_def, Over.comp_left]
      rfl
  have key : g.left = (snd A A).left ≫ ε.left ≫ g.left := by
    refine eq_comp_section_of_local_rigidity (snd A A).left ε.left g.left A.hom B.hom hεp
      ((Over.w g).trans (Over.w (snd A A)).symm) (snd A A).left.isOpenMap
      (hR _ _ _ _ _ _ hεp huc hsurj) (fun s ↦ (A.hom.isConnected_preimage_singleton s).2) ?_
    intro s
    refine ⟨(η[A] : 𝟙_ (Over S) ⟶ A).left s, (η[B] : 𝟙_ (Over S) ⟶ B).left s, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, hη]; rfl
    · intro x hx
      obtain ⟨z, rfl, rfl⟩ := Scheme.exists_preimage_of_isPullback hpb x s hx
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hj, Hom.one_def, Over.comp_left,
        Scheme.Hom.comp_apply]
      rfl
  have key' : g = snd A A ≫ f := by
    rw [← hε]
    exact Over.OverMorphism.ext key
  have hmul : (fst A A * snd A A) ≫ f = (fst A A ≫ f) * (snd A A ≫ f) := by
    rw [← key', mul_inv_cancel_left]
  refine ⟨hf, ?_⟩
  rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at hmul
  rw [hmul]
  congr 1

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsNoetherianModelOfSmooth
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmoothDescent

open TensorProduct

theorem exists_common_model (R B C : Type) [CommRing R] [CommRing B] [CommRing C] [Algebra R B]
    [Algebra R C] [Algebra.Smooth R B] [Algebra.Smooth R C] :
    ∃ (A B₁ C₁ : Type) (_ : CommRing A) (_ : Algebra A R) (_ : CommRing B₁) (_ : CommRing C₁)
      (_ : Algebra A B₁) (_ : Algebra A C₁), IsNoetherianRing A ∧ Algebra.Smooth A B₁ ∧
      Algebra.Smooth A C₁ ∧ Nonempty (R ⊗[A] B₁ ≃ₐ[R] B) ∧ Nonempty (R ⊗[A] C₁ ≃ₐ[R] C) := by
  obtain ⟨A₁, B₁, _, _, hA₁, _, ⟨eB⟩⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ R B
  obtain ⟨A₂, C₁, _, _, hA₂, _, ⟨eC⟩⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ R C
  let A : Subalgebra ℤ R := A₁ ⊔ A₂
  let : Algebra A₁ A := (Subalgebra.inclusion (le_sup_left : A₁ ≤ A)).toRingHom.toAlgebra
  let : Algebra A₂ A := (Subalgebra.inclusion (le_sup_right : A₂ ≤ A)).toRingHom.toAlgebra
  have : IsScalarTower A₁ A R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A₂ A R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType ℤ A := (Subalgebra.fg_iff_finiteType A).mp (hA₁.sup hA₂)
  exact ⟨A, A ⊗[A₁] B₁, A ⊗[A₂] C₁, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, Algebra.FiniteType.isNoetherianRing ℤ A, inferInstance,
    inferInstance, ⟨(Algebra.TensorProduct.cancelBaseChange A₁ A R R B₁).trans eB.symm⟩,
    ⟨(Algebra.TensorProduct.cancelBaseChange A₂ A R R C₁).trans eC.symm⟩⟩

variable {A R B₁ C₁ : Type} [CommRing A] [CommRing R] [CommRing B₁] [CommRing C₁] [Algebra A R]
  [Algebra A B₁] [Algebra A C₁]

noncomputable abbrev incl (C₁ : Type) [CommRing C₁] [Algebra A C₁] (S : Subalgebra A R) :
    S ⊗[A] C₁ →ₐ[A] R ⊗[A] C₁ :=
  Algebra.TensorProduct.map S.val (AlgHom.id A C₁)

theorem range_incl_mono {S T : Subalgebra A R} (h : S ≤ T) :
    (incl C₁ S).range ≤ (incl C₁ T).range := by
  have e : incl C₁ S = (incl C₁ T).comp
      (Algebra.TensorProduct.map (Subalgebra.inclusion h) (AlgHom.id A C₁)) :=
    Algebra.TensorProduct.ext' fun _ _ => rfl
  rw [e]
  exact AlgHom.range_comp_le_range _ _

theorem exists_fg_mem_range_incl (x : R ⊗[A] C₁) :
    ∃ S : Subalgebra A R, S.FG ∧ x ∈ (incl C₁ S).range := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨⊥, Subalgebra.fg_bot, zero_mem _⟩
  | tmul r c =>
    exact ⟨Algebra.adjoin A {r}, ⟨{r}, by simp⟩,
      (AlgHom.mem_range _).mpr ⟨⟨r, Algebra.subset_adjoin rfl⟩ ⊗ₜ c, rfl⟩⟩
  | add x y hx hy =>
    obtain ⟨S, hS, hxS⟩ := hx
    obtain ⟨T, hT, hyT⟩ := hy
    exact ⟨S ⊔ T, hS.sup hT,
      add_mem (range_incl_mono le_sup_left hxS) (range_incl_mono le_sup_right hyT)⟩

theorem exists_fg_subset_range_incl (t : Finset (R ⊗[A] C₁)) :
    ∃ S : Subalgebra A R, S.FG ∧ (t : Set (R ⊗[A] C₁)) ⊆ (incl C₁ S).range := by
  classical
  refine Finset.induction_on t ⟨⊥, Subalgebra.fg_bot, by simp⟩ ?_
  intro a t _ ih
  obtain ⟨S, hS, hSt⟩ := ih
  obtain ⟨T, hT, haT⟩ := exists_fg_mem_range_incl (C₁ := C₁) a
  refine ⟨S ⊔ T, hS.sup hT, ?_⟩
  rw [Finset.coe_insert, Set.insert_subset_iff]
  exact ⟨range_incl_mono le_sup_right haT,
    hSt.trans (SetLike.coe_subset_coe.mpr (range_incl_mono le_sup_left))⟩

theorem exists_fg_range_le [Algebra.FiniteType A B₁] (φ : B₁ →ₐ[A] R ⊗[A] C₁) :
    ∃ S : Subalgebra A R, S.FG ∧ φ.range ≤ (incl C₁ S).range := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra A B₁).FG)
  obtain ⟨S, hS, hsub⟩ := exists_fg_subset_range_incl (C₁ := C₁) (s.image φ)
  refine ⟨S, hS, ?_⟩
  rw [← Algebra.map_top, ← hs, AlgHom.map_adjoin, Algebra.adjoin_le_iff]
  rwa [Finset.coe_image] at hsub

theorem incl_injective [Module.Flat A C₁] (S : Subalgebra A R) :
    Function.Injective (incl C₁ S) :=
  Module.Flat.rTensor_preserves_injective_linearMap (M := C₁) S.val.toLinearMap
    Subtype.val_injective

theorem exists_lift {D E : Type} [CommRing D] [CommRing E] [Algebra A D] [Algebra A E]
    (φ : B₁ →ₐ[A] E) (i : D →ₐ[A] E) (hi : Function.Injective i) (h : φ.range ≤ i.range) :
    ∃ ψ : B₁ →ₐ[A] D, ∀ b, i (ψ b) = φ b := by
  let e := AlgEquiv.ofInjective i hi
  let φ' := φ.codRestrict i.range fun b => h (AlgHom.mem_range_self φ b)
  refine ⟨e.symm.toAlgHom.comp φ', fun b => ?_⟩
  have h1 : ((e (e.symm (φ' b)) : i.range) : E) = (φ' b : E) := by rw [e.apply_symm_apply]
  exact h1

theorem cancel_one_tmul (S : Subalgebra A R) (x : S ⊗[A] C₁) :
    Algebra.TensorProduct.cancelBaseChange A S R R C₁ (1 ⊗ₜ x) = incl C₁ S x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s c => simp [Algebra.TensorProduct.cancelBaseChange_tmul, incl, Algebra.smul_def]
  | add x y hx hy => rw [TensorProduct.tmul_add, map_add (f := _), hx, hy, map_add (f := _)]

theorem incl_tmul (S : Subalgebra A R) (s : S) (c : C₁) :
    incl C₁ S (s ⊗ₜ c) = (s : R) • ((1 : R) ⊗ₜ[A] c) := by
  simp [incl, TensorProduct.smul_tmul']

theorem incl_smul (S : Subalgebra A R) (s : S) (x : S ⊗[A] C₁) :
    incl C₁ S (s • x) = (s : R) • incl C₁ S x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s' c => simp [incl, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, map_add (f := _), smul_add]

noncomputable def extend (S : Subalgebra A R) {D : Type} [CommRing D] [Algebra A D] [Algebra S D]
    [IsScalarTower A S D] (ψ : B₁ →ₐ[A] D) : S ⊗[A] B₁ →ₐ[S] D :=
  Algebra.TensorProduct.lift (Algebra.ofId S D) ψ fun _ _ => Commute.all _ _

theorem extend_tmul (S : Subalgebra A R) {D : Type} [CommRing D] [Algebra A D] [Algebra S D]
    [IsScalarTower A S D] (ψ : B₁ →ₐ[A] D) (s : S) (b : B₁) :
    extend S ψ (s ⊗ₜ b) = s • ψ b := by
  simp [extend, Algebra.smul_def]

theorem incl_extend (S : Subalgebra A R) (F : R ⊗[A] B₁ →ₐ[R] R ⊗[A] C₁)
    (ψ : B₁ →ₐ[A] S ⊗[A] C₁) (h : ∀ b, incl C₁ S (ψ b) = F (1 ⊗ₜ b)) (x : S ⊗[A] B₁) :
    incl C₁ S (extend S ψ x) = F (incl B₁ S x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s b => rw [extend_tmul, incl_smul, h, incl_tmul, map_smul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]

theorem val_extend (S : Subalgebra A R) (F : R ⊗[A] B₁ →ₐ[R] R)
    (ψ : B₁ →ₐ[A] S) (h : ∀ b, S.val (ψ b) = F (1 ⊗ₜ b)) (x : S ⊗[A] B₁) :
    S.val (extend S ψ x) = F (incl B₁ S x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s b =>
    rw [extend_tmul, smul_eq_mul, map_mul, h, incl_tmul, map_smul, smul_eq_mul]
    rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]

end GlobalTheory.SmoothDescent

namespace GlobalTheory

open TensorProduct SmoothDescent

theorem exists_noetherian_model_of_smooth :
    ∀ (R B C : Type) [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] [Algebra.Smooth R B] [Algebra.Smooth R C] (f g : B →ₐ[R] C) (r : B →ₐ[R] R), ∃ (R₀ B₀ C₀ : Type) (_ : CommRing R₀) (_ : IsNoetherianRing R₀) (_ : Algebra R₀ R) (_ : CommRing B₀) (_ : CommRing C₀) (_ : Algebra R₀ B₀) (_ : Algebra R₀ C₀) (f₀ g₀ : B₀ →ₐ[R₀] C₀) (r₀ : B₀ →ₐ[R₀] R₀) (β' : TensorProduct R₀ R B₀ ≃ₐ[R] B) (δ' : TensorProduct R₀ R C₀ ≃ₐ[R] C), Module.Flat R₀ B₀ ∧ Module.Flat R₀ C₀ ∧ ∀ b : B₀, f (β' (1 ⊗ₜ b)) = δ' (1 ⊗ₜ f₀ b) ∧ g (β' (1 ⊗ₜ b)) = δ' (1 ⊗ₜ g₀ b) ∧ r (β' (1 ⊗ₜ b)) = algebraMap R₀ R (r₀ b) := by
  intro R B C _ _ _ _ _ _ _ f g r
  obtain ⟨A, B₁, C₁, _, _, _, _, _, _, hA, hB, hC, ⟨eB⟩, ⟨eC⟩⟩ := exists_common_model R B C
  let F : R ⊗[A] B₁ →ₐ[R] R ⊗[A] C₁ := (eC.symm.toAlgHom.comp f).comp eB.toAlgHom
  let G : R ⊗[A] B₁ →ₐ[R] R ⊗[A] C₁ := (eC.symm.toAlgHom.comp g).comp eB.toAlgHom
  let ρ : R ⊗[A] B₁ →ₐ[R] R := r.comp eB.toAlgHom
  let j : B₁ →ₐ[A] R ⊗[A] B₁ := Algebra.TensorProduct.includeRight
  let φF : B₁ →ₐ[A] R ⊗[A] C₁ := (F.restrictScalars A).comp j
  let φG : B₁ →ₐ[A] R ⊗[A] C₁ := (G.restrictScalars A).comp j
  let φr : B₁ →ₐ[A] R := (ρ.restrictScalars A).comp j
  obtain ⟨S₁, hS₁, h₁⟩ := exists_fg_range_le (C₁ := C₁) φF
  obtain ⟨S₂, hS₂, h₂⟩ := exists_fg_range_le (C₁ := C₁) φG
  have h₃ : φr.range.FG := by
    rw [← Algebra.map_top]
    exact Subalgebra.FG.map φr Algebra.FiniteType.out
  let S : Subalgebra A R := S₁ ⊔ S₂ ⊔ φr.range
  have : Algebra.FiniteType A S := (Subalgebra.fg_iff_finiteType S).mp ((hS₁.sup hS₂).sup h₃)
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing A S
  have hF : φF.range ≤ (incl C₁ S).range :=
    h₁.trans (range_incl_mono (le_sup_left.trans le_sup_left))
  have hG : φG.range ≤ (incl C₁ S).range :=
    h₂.trans (range_incl_mono (le_sup_right.trans le_sup_left))
  have hr : φr.range ≤ S.val.range := by
    rw [Subalgebra.range_val]
    exact le_sup_right
  obtain ⟨ψF, hψF⟩ := exists_lift φF (incl C₁ S) (incl_injective S) hF
  obtain ⟨ψG, hψG⟩ := exists_lift φG (incl C₁ S) (incl_injective S) hG
  obtain ⟨ψr, hψr⟩ := exists_lift φr S.val Subtype.val_injective hr
  refine ⟨S, S ⊗[A] B₁, S ⊗[A] C₁, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, extend S ψF, extend S ψG, extend S ψr,
    (Algebra.TensorProduct.cancelBaseChange A S R R B₁).trans eB,
    (Algebra.TensorProduct.cancelBaseChange A S R R C₁).trans eC, inferInstance, inferInstance,
    fun b => ⟨?_, ?_, ?_⟩⟩
  · rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, cancel_one_tmul, cancel_one_tmul,
      incl_extend S F ψF hψF]
    simp [F]
  · rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, cancel_one_tmul, cancel_one_tmul,
      incl_extend S G ψG hψG]
    simp [G]
  · rw [AlgEquiv.trans_apply, cancel_one_tmul]
    change _ = S.val (extend S ψr b)
    rw [val_extend S ρ ψr hψr]
    simp [ρ]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.HasEnoughRootsOfUnityGlobalSections
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem existsUnique_pairing_eq_character {H M : Type} [CommGroup H] [CommMonoid M] (N : ℕ)
    [NeZero N] [HasEnoughRootsOfUnity M N] [hfin : Finite {x : H // x ^ N = 1}]
    (W : H → H → Mˣ → Prop)
    (hex : ∀ x y : H, x ^ N = 1 → y ^ N = 1 → ∃! c, W x y c)
    (hmul : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c'))
    (hskew : ∀ x y c, W x y c → W y x c⁻¹)
    (hnd : ∀ x : H, x ^ N = 1 → (∀ y : H, y ^ N = 1 → W x y 1) → x = 1)
    (χ : {x : H // x ^ N = 1} → Mˣ)
    (hχ : ∀ x y, χ ⟨x.1 * y.1, by rw [mul_pow, x.2, y.2, _root_.one_mul]⟩ = χ x * χ y) :
    ∃! b : H, b ^ N = 1 ∧ ∀ x : {x : H // x ^ N = 1}, W x.1 b (χ x) := by
  classical
  let G : Subgroup H := (powMonoidHom N : H →* H).ker
  have hG : ∀ x : G, (x : H) ^ N = 1 := fun x => x.2
  haveI : Finite G := hfin
  choose e he huniq using fun x y : G => hex x y (hG x) (hG y)
  have hel : ∀ x x' y : G, e (x * x') y = e x y * e x' y := fun x x' y =>
    (huniq _ _ _ (hmul _ _ _ _ _ (he x y) (he x' y))).symm
  have hes : ∀ x y : G, e y x = (e x y)⁻¹ := fun x y =>
    (huniq _ _ _ (hskew _ _ _ (he x y))).symm
  have her : ∀ x y y' : G, e x (y * y') = e x y * e x y' := fun x y y' => by
    rw [hes (y * y') x, hel, hes y x, hes y' x, mul_inv]
  let Φ : G →* (G →* Mˣ) := MonoidHom.mk' (fun b => MonoidHom.mk' (fun x => e x b)
    (fun x x' => hel x x' b)) (fun b b' => MonoidHom.ext fun x => her x b b')
  have hΦ : ∀ b x, Φ b x = e x b := fun _ _ => rfl
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro b hb
    refine Subtype.ext (hnd b (hG b) fun y hy => ?_)
    have h1 : e ⟨y, hy⟩ b = 1 := by rw [← hΦ, hb]; rfl
    have h2 := he b ⟨y, hy⟩
    rwa [hes, h1, inv_one] at h2
  haveI : HasEnoughRootsOfUnity M (Monoid.exponent G) :=
    HasEnoughRootsOfUnity.of_dvd M (n := N)
      (Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (hG g))
  have hcard := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G M
  haveI : Finite (G →* Mˣ) := Nat.finite_of_card_ne_zero (hcard ▸ Nat.card_pos.ne')
  have hbij : Function.Bijective Φ := hinj.bijective_of_nat_card_le hcard.le
  let χ' : G →* Mˣ := MonoidHom.mk' (fun x => χ ⟨x.1, hG x⟩)
    (fun x y => hχ ⟨x.1, hG x⟩ ⟨y.1, hG y⟩)
  obtain ⟨b, hb⟩ := hbij.2 χ'
  refine ⟨b, ⟨hG b, fun x => ?_⟩, ?_⟩
  · have h1 : e ⟨x.1, x.2⟩ b = χ x := by rw [← hΦ, hb]; rfl
    rw [← h1]
    exact he ⟨x.1, x.2⟩ b
  · rintro b' ⟨hb', h⟩
    have : (⟨b', hb'⟩ : G) = b := by
      apply hinj
      rw [hb]
      ext1 x
      rw [hΦ]
      exact (huniq x ⟨b', hb'⟩ _ (h ⟨x.1, hG x⟩)).symm
    exact congrArg Subtype.val this

theorem finite_torsion_of_isFinite_mul (K : Type) [Field K] [IsAlgClosed K]
    (P : PolAV (Spec (CommRingCat.of K))) (N : ℕ) [IsFinite (mulA P.A N).left] :
    Finite {x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A // x ^ N = 1} := by
  haveI := P.isAb.proper
  let p := IsLocalRing.closedPoint K
  let o : P.A.left := (1 : baseOver (Spec (CommRingCat.of K)) ⟶ P.A).left p
  have hfib := Scheme.Hom.finite_preimage_singleton (mulA P.A N).left o
  haveI := hfib.to_subtype
  refine Finite.of_injective (β := (mulA P.A N).left ⁻¹' {o}) (fun x => ⟨x.1.left p, ?_⟩) ?_
  · have h : x.1 ≫ mulA P.A N = 1 := by rw [mulA, MonObj.comp_pow, Category.comp_id, x.2]
    change (x.1 ≫ mulA P.A N).left p = o
    rw [h]
  · intro x y hxy
    refine Subtype.ext (Over.OverMorphism.ext ?_)
    exact ext_of_apply_closedPoint_eq P.A.hom (Over.w x.1) (Over.w y.1) (congrArg Subtype.val hxy)

theorem hasEnoughRootsOfUnity_globalSections (K : Type) [Field K] [IsAlgClosed K] (N : ℕ)
    (hN : (N : K) ≠ 0) :
    HasEnoughRootsOfUnity Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) N := by
  haveI : NeZero (N : K) := ⟨hN⟩
  haveI : NeZero N := .of_neZero_natCast K
  let e : K ≃+* Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm
  exact MulEquiv.hasEnoughRootsOfUnity (e.toMulEquiv.restrictRootsOfUnity N)

theorem charPair_of_weil :
    WeilSt → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S), (∀ x : T ⟶ P.A, x ^ k = 1 → WeilIs P.A P.L k x x 1) ∧ (∀ (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k y x c⁻¹) ∧ ∀ (T' : Over S) (h : T' ⟶ T) (x y : T ⟶ P.A) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k x y c → WeilIs P.A P.L k (h ≫ x) (h ≫ y) (Units.map h.left.appTop.hom.toMonoidHom c)) → WeilNondegSt → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left ∧ (IsUnit (n : Γ(S, ⊤)) → Etale (mulA P.A n).left)) → CharPairSt := by
  intro hW hskew hnd hM K _ _ P N hN χ hχ
  haveI : NeZero (N : K) := ⟨hN⟩
  haveI : NeZero N := .of_neZero_natCast K
  haveI := (hM _ P N (NeZero.one_le)).1
  haveI := finite_torsion_of_isFinite_mul K P N
  haveI := hasEnoughRootsOfUnity_globalSections K N hN
  obtain ⟨hex, hmul, -, -⟩ := hW _ P N (baseOver (Spec (CommRingCat.of K)))
  exact existsUnique_pairing_eq_character N (fun x y c => WeilIs P.A P.L N x y c) hex hmul
    (hskew _ P N _).2.1 (hnd K P N hN) χ hχ

end GlobalTheory
end
