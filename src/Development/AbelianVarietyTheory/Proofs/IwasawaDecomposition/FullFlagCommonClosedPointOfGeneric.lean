module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilOfFixes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedVectorOfMemIsotypicComponent
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOscillatorActionUnitaryPolynomialBound
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeakWeilRepEqUnitSmulOscillatorRealPoints
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedNonsplitExistsConjInvolutionUniformise
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridHeckeCharactersExist

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagCommonClosedPointOfGeneric
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagCommonClosedPointOfGeneric
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

namespace GlobalTheory.FlagBundle.ClosedPt

variable {ι : Type} {m : ι → ℕ}

theorem par_zero_top {K : Type} [Field K] {g : Mat m K} (h : ∀ τ, (g τ).det ≠ 0) : Par 0 ⊤ g := fun τ =>
  ⟨fun _ _ => trivial, h τ, trivial, fun _ _ hi _ => absurd hi (Nat.not_lt_zero _)⟩

theorem map_mul_inv {R K : Type} [CommRing R] [Field K] (g : R →+* K) (N₁ N₂ : Mat m R) (τ : ι)
    (hu : IsUnit (N₂ τ).det) : (N₁.map g * (N₂.map g)⁻¹) τ = (N₁ τ * (N₂ τ)⁻¹).map g := by
  have e : (N₂ τ).map g * ((N₂ τ)⁻¹).map g = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ g.map_zero g.map_one]
  show (N₁ τ).map g * ((N₂ τ).map g)⁻¹ = _
  rw [Matrix.map_mul, Matrix.inv_eq_right_inv e]

theorem descend {R L : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Field L] [Algebra R L]
    [IsFractionRing R L] (N₁ N₂ : Mat m R)
    (h₁ : ∀ τ, (N₁.map (IsLocalRing.residue R) τ).det ≠ 0)
    (h₂ : ∀ τ, (N₂.map (IsLocalRing.residue R) τ).det ≠ 0)
    (hL : Par m ⊤ (N₁.map (algebraMap R L) * (N₂.map (algebraMap R L))⁻¹)) :
    Par m ⊤ (N₁.map (IsLocalRing.residue R) * (N₂.map (IsLocalRing.residue R))⁻¹) := by
  have hu : ∀ τ, IsUnit (N₂ τ).det := fun τ => by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    exact h₂ τ
  have hP := (par_zero_top h₁).mul (par_zero_top h₂).inv
  intro τ
  refine ⟨fun _ _ => trivial, hP.det_ne τ, trivial, fun i j hi hij => ?_⟩
  have h0 := (hL τ).2.2.2 i j hi hij
  rw [map_mul_inv _ _ _ τ (hu τ)] at h0
  rw [map_mul_inv _ _ _ τ (hu τ)]
  have h0' : algebraMap R L ((N₁ τ * (N₂ τ)⁻¹) i j) = 0 := h0
  show IsLocalRing.residue R ((N₁ τ * (N₂ τ)⁻¹) i j) = 0
  rw [(map_eq_zero_iff _ (IsFractionRing.injective R L)).1 h0', map_zero]

variable {F : Type} [Field F]

noncomputable def vals {Y : Var F} {R : Type} [CommRing R] [IsLocalRing R] (v : Sp R ⟶ Y.X) (M : Mat m Y.Fn)
    (hM : ∀ τ a b, M τ a b ∈ (ratOf Y).O (v (IsLocalRing.closedPoint R))) : Mat m R :=
  fun τ a b => RatModel.valLoc (M := ratOf Y) v _ specializes_rfl ⟨M τ a b, hM τ a b⟩

theorem map_val {Y : Var F} {R K : Type} [CommRing R] [IsLocalRing R] [Field K] (σ : R →+* K) (v : Sp R ⟶ Y.X)
    (M : Mat m Y.Fn) (hM : ∀ τ a b, M τ a b ∈ (ratOf Y).O (v (IsLocalRing.closedPoint R))) :
    M.map ((ratOf Y).val (spMap σ ≫ v)) = (vals v M hM).map σ := by
  funext τ
  ext a b
  have := RatModel.val_spMap_comp (M := ratOf Y) σ v specializes_rfl ⟨M τ a b, hM τ a b⟩
  exact this

theorem par_val {Y : Var F} {R K : Type} [CommRing R] [IsLocalRing R] [Field K] (σ : R →+* K) (v : Sp R ⟶ Y.X)
    {M : Mat m Y.Fn} (hM : Par 0 ((ratOf Y).O (v (IsLocalRing.closedPoint R))).toSubring M) :
    Par 0 ⊤ (M.map ((ratOf Y).val (spMap σ ≫ v))) :=
  Par.map_of hM _ (σ.comp (RatModel.valLoc (M := ratOf Y) v _ specializes_rfl))
    (fun x => RatModel.val_spMap_comp (M := ratOf Y) σ v specializes_rfl x)

end GlobalTheory.FlagBundle.ClosedPt

namespace GlobalTheory.FlagBundle.ClosedPt

theorem closedPt_comp {R : Type} [CommRing R] [IsLocalRing R] {Z : Scheme.{0}} (v : Sp R ⟶ Z) :
    (spMap (IsLocalRing.residue R) ≫ v) (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) =
      v (IsLocalRing.closedPoint R) := by
  refine (Scheme.Hom.comp_apply _ _ _).trans ?_
  exact congrArg v (IsLocalRing.comap_closedPoint (IsLocalRing.residue R))

theorem gen_specializes {R L : Type} [CommRing R] [IsLocalRing R] [Field L] [Algebra R L] {Z : Scheme.{0}}
    (v : Sp R ⟶ Z) (w : Sp L) : (spMap (algebraMap R L) ≫ v) w ⤳ v (IsLocalRing.closedPoint R) := by
  have h := (IsLocalRing.specializes_closedPoint (spMap (algebraMap R L) w)).map v.continuous
  convert h using 1
  exact Scheme.Hom.comp_apply _ _ _

end GlobalTheory.FlagBundle.ClosedPt


open GlobalTheory.FlagBundle.ClosedPt in
theorem GlobalTheory.FlagBundle.coBear_closedPoint : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (L : Type) [Field L] [Algebra R L] [IsFractionRing R L] (v₁ : Sp R ⟶ Y₁.X) (v₂ : Sp R ⟶ Y₂.X), v₁ ≫ f₁ = v₂ ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (spMap (algebraMap R L) ≫ v₁ ≫ f₁) (spMap (algebraMap R L) ≫ v₁) (spMap (algebraMap R L) ≫ v₂) → CoBear Eb S₁ φ₁ S₂ φ₂ (spMap (IsLocalRing.residue R) ≫ v₁ ≫ f₁) (spMap (IsLocalRing.residue R) ≫ v₁) (spMap (IsLocalRing.residue R) ≫ v₂) := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ R _ _ _ L _ _ _ v₁ v₂ e hgen
  have sub₁ := hR₁.2.1
  have sub₂ := hR₂.2.1
  have hf₁ : f₁ (v₁ (IsLocalRing.closedPoint R)) = (v₁ ≫ f₁) (IsLocalRing.closedPoint R) :=
    (Scheme.Hom.comp_apply _ _ _).symm
  have hf₂ : f₂ (v₂ (IsLocalRing.closedPoint R)) = (v₁ ≫ f₁) (IsLocalRing.closedPoint R) := by
    rw [e]; exact (Scheme.Hom.comp_apply _ _ _).symm
  obtain ⟨A, hA⟩ := Eb.nonempty ((v₁ ≫ f₁) (IsLocalRing.closedPoint R))
  obtain ⟨A₁, hA₁⟩ := S₁.nonempty (v₁ (IsLocalRing.closedPoint R))
  obtain ⟨A₂, hA₂⟩ := S₂.nonempty (v₂ (IsLocalRing.closedPoint R))
  have hM₁ := sub₁ _ A₁ hA₁ A (by rw [hf₁]; exact hA)
  have hM₂ := sub₂ _ A₂ hA₂ A (by rw [hf₂]; exact hA)

  obtain ⟨B, hB, hg, hgP, hb1, hb2⟩ := hgen
  have hA₁g : A₁ ∈ S₁.S ((spMap (algebraMap R L) ≫ v₁) (IsLocalRing.closedPoint L)) :=
    Fr.mem_of_specializes hA₁ (gen_specializes v₁ _)
  have hA₂g : A₂ ∈ S₂.S ((spMap (algebraMap R L) ≫ v₂) (IsLocalRing.closedPoint L)) :=
    Fr.mem_of_specializes hA₂ (gen_specializes v₂ _)
  have hAg : A ∈ Eb.S (((spMap (algebraMap R L) ≫ v₁) ≫ f₁) (IsLocalRing.closedPoint L)) := by
    rw [Category.assoc]
    exact Fr.mem_of_specializes hA (gen_specializes (v₁ ≫ f₁) _)
  have hBg : B ∈ Eb.S (((spMap (algebraMap R L) ≫ v₁) ≫ f₁) (IsLocalRing.closedPoint L)) := by
    rw [Category.assoc]
    exact hB
  have heq : (spMap (algebraMap R L) ≫ v₁) ≫ f₁ = (spMap (algebraMap R L) ≫ v₂) ≫ f₂ := by
    rw [Category.assoc, Category.assoc, e]
  have hH := par_val (algebraMap R L) v₁ hM₁
  have hself : Bears S₁ φ₁ A ((A₁ * (A.map φ₁)⁻¹).map ((ratOf Y₁).val (spMap (algebraMap R L) ≫ v₁)))
      (spMap (algebraMap R L) ≫ v₁) :=
    ⟨A₁, hA₁g, by rw [Mat.mul_inv hH.det_ne]; exact Par.one⟩
  obtain ⟨A₂', hA₂', hpar⟩ := GlobalTheory.T.pointCarriesFrameFlags_transfer_between_flag_bundles F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ L _ _ heq A hAg B hBg
    _ hg hself hb1 hb2

  have hsp₂ := gen_specializes (L := L) v₂ (IsLocalRing.closedPoint L)
  have hG := (Fr.mem_iff hA₂g).1 hA₂'
  have hM₂g : Par 0 ((ratOf Y₂).O ((spMap (algebraMap R L) ≫ v₂) (IsLocalRing.closedPoint L))).toSubring
      (A₂ * (A.map φ₂)⁻¹) :=
    hM₂.mono le_rfl fun _ hx => RatModel.O_le_of_specializes hsp₂ hx
  set ψ := RatModel.valHom (M := ratOf Y₂) (spMap (algebraMap R L) ≫ v₂) _
    (RatModel.range_eq_singleton _ (IsLocalRing.closedPoint L))
  have hv : ∀ x : ((ratOf Y₂).O ((spMap (algebraMap R L) ≫ v₂) (IsLocalRing.closedPoint L))).toSubring,
      (ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂) x = ψ x := fun _ => rfl
  have heqM : A₂' * (A.map φ₂)⁻¹ = (A₂' * A₂⁻¹) * (A₂ * (A.map φ₂)⁻¹) := by
    rw [mul_assoc, ← mul_assoc A₂⁻¹, Mat.inv_mul (Fr.det_ne hA₂), one_mul]
  have hmap : (A₂' * (A.map φ₂)⁻¹).map ((ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂)) =
      (A₂' * A₂⁻¹).map ((ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂)) *
        (A₂ * (A.map φ₂)⁻¹).map ((ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂)) := by
    rw [heqM]
    exact Par.map_mul_of hG hM₂g ((ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂)) ψ hv
  have hGv := Par.map_of hG ((ratOf Y₂).val (spMap (algebraMap R L) ≫ v₂)) ψ hv
  have hpar2 := hpar
  erw [hmap] at hpar2
  rw [Mat.mul_inv_rev] at hpar2
  clear hpar
  have hL := hpar2.mul hGv
  rw [mul_assoc, mul_assoc, Mat.inv_mul hGv.det_ne, mul_one] at hL
  rw [map_val (algebraMap R L) v₁ _ (fun τ a b => (hM₁ τ).1 a b),
    map_val (algebraMap R L) v₂ _ (fun τ a b => (hM₂ τ).1 a b)] at hL

  have hk₁ := par_val (IsLocalRing.residue R) v₁ hM₁
  have hk₂ := par_val (IsLocalRing.residue R) v₂ hM₂
  have hD := descend _ _ (by rw [← map_val]; exact hk₁.det_ne) (by rw [← map_val]; exact hk₂.det_ne) hL
  rw [← map_val, ← map_val] at hD
  have hAk : A ∈ Eb.S ((spMap (IsLocalRing.residue R) ≫ v₁ ≫ f₁)
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField R))) :=
    (congrArg (fun z => A ∈ Eb.S z) (closedPt_comp (v₁ ≫ f₁))).mpr hA
  have hb₁ : Bears S₁ φ₁ A ((A₁ * (A.map φ₁)⁻¹).map ((ratOf Y₁).val (spMap (IsLocalRing.residue R) ≫ v₁)))
      (spMap (IsLocalRing.residue R) ≫ v₁) :=
    ⟨A₁, (congrArg (fun z => A₁ ∈ S₁.S z) (closedPt_comp v₁)).mpr hA₁, by
      rw [Mat.mul_inv hk₁.det_ne]; exact Par.one⟩
  have hb₂ : Bears S₂ φ₂ A ((A₁ * (A.map φ₁)⁻¹).map ((ratOf Y₁).val (spMap (IsLocalRing.residue R) ≫ v₁)))
      (spMap (IsLocalRing.residue R) ≫ v₂) :=
    ⟨A₂, (congrArg (fun z => A₂ ∈ S₂.S z) (closedPt_comp v₂)).mpr hA₂, hD⟩
  exact ⟨A, hAk, _, hk₁, hb₁, hb₂⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagCommonClosedPointOfGenericStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullFlag_common_closedPoint_of_generic : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (L : Type) [Field L] [Algebra R L] [IsFractionRing R L] (v₁ : Sp R ⟶ Y₁.X) (v₂ : Sp R ⟶ Y₂.X), v₁ ≫ f₁ = v₂ ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (spMap (algebraMap R L) ≫ v₁ ≫ f₁) (spMap (algebraMap R L) ≫ v₁) (spMap (algebraMap R L) ≫ v₂) → CoBear Eb S₁ φ₁ S₂ φ₂ (spMap (IsLocalRing.residue R) ≫ v₁ ≫ f₁) (spMap (IsLocalRing.residue R) ≫ v₁) (spMap (IsLocalRing.residue R) ≫ v₂) := by
  first | exact @GlobalTheory.FlagBundle.coBear_closedPoint | exact GlobalTheory.FlagBundle.coBear_closedPoint | (intros; apply GlobalTheory.FlagBundle.coBear_closedPoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilRepresentationOneParameterGenerator
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilRepresentationOneParameterGenerator
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Lift.GenZero

theorem exists_hasDerivAt_char (s : ℝ → ℂ) (hs : ∀ t t', s (t + t') = s t * s t') (h0 : s 0 = 1)
    (hc : ContinuousAt s 0) : ∃ m : ℂ, HasDerivAt s m 0 := by
  have hcont : Continuous s := by
    refine continuous_iff_continuousAt.2 fun t₀ => ?_
    have e : s = fun t => s (t - t₀) * s t₀ := funext fun t => by rw [← hs, sub_add_cancel]
    rw [e]
    refine ContinuousAt.mul ?_ continuousAt_const
    exact ContinuousAt.comp (g := s) (f := fun t => t - t₀) (by simpa using hc) (by fun_prop)
  let g : ℝ → ℂ := fun x => ∫ y in (0 : ℝ)..x, s y
  have hg : ∀ x, HasDerivAt g (s x) x := fun x => (hcont.integral_hasStrictDerivAt 0 x).hasDerivAt
  obtain ⟨ε, hε⟩ : ∃ ε, g ε ≠ 0 := by
    by_contra hn
    push Not at hn
    have h1 : HasDerivAt g 0 0 := by
      rw [show g = fun _ => 0 from funext hn]
      exact hasDerivAt_const _ _
    have := (hg 0).unique h1
    rw [h0] at this
    exact one_ne_zero this
  have e : s = fun t => (g (t + ε) - g t) / g ε := by
    funext t
    rw [eq_div_iff hε]
    have h1 : g (t + ε) - g t = ∫ y in t..(t + ε), s y :=
      intervalIntegral.integral_interval_sub_left (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
    rw [h1]
    have h2 := intervalIntegral.integral_comp_add_left (a := 0) (b := ε) s t
    rw [add_zero] at h2
    rw [← h2]
    simp only [hs, g]
    exact (intervalIntegral.integral_const_mul _ _).symm
  have h3 : HasDerivAt (fun t => g (t + ε)) (s (0 + ε)) 0 := HasDerivAt.comp_add_const 0 ε (hg _)
  exact ⟨_, ((h3.sub (hg 0)).div_const (g ε)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => congrFun e t)⟩

theorem lie_of_path {ι : Type} [Fintype ι] [DecidableEq ι] (H X : Matrix ι ι ℂ) (m : ℝ → Matrix ι ι ℂ) (h0 : m 0 = 1)
    (hm : ∀ t, (m t)ᴴ * H * m t = H) (hX : ∀ k l, HasDerivAt (fun t => m t k l) (X k l) 0) :
    Xᴴ * H + H * X = 0 := by
  ext i j
  have h1 : HasDerivAt (fun t => ∑ l, (∑ k, star (m t k i) * H k l) * m t l j)
      (∑ l, ((∑ k, star (X k i) * H k l) * m 0 l j + (∑ k, star (m 0 k i) * H k l) * X l j)) 0 :=
    HasDerivAt.fun_sum fun l _ =>
      (HasDerivAt.fun_sum fun k _ => (hX k i).star.mul_const (H k l)).mul (hX l j)
  have e : (fun t => ∑ l, (∑ k, star (m t k i) * H k l) * m t l j) = fun _ => H i j := by
    funext t
    rw [← congrFun (congrFun (hm t) i) j]
    simp only [Matrix.mul_apply, conjTranspose_apply]
  rw [e] at h1
  have h2 := h1.unique (hasDerivAt_const _ _)
  have h3 : (Xᴴ * H * m 0 + (m 0)ᴴ * H * X) i j = 0 := by
    rw [← h2]
    simp only [Matrix.add_apply, Matrix.mul_apply, conjTranspose_apply, Finset.sum_add_distrib]
  rwa [h0, conjTranspose_one, Matrix.mul_one, Matrix.one_mul] at h3

open scoped Classical


set_option maxHeartbeats 1000000 in
open GlobalTheory.RealWeil in
theorem exists_generator : ∀ (D : D7) (θ : InfF D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → OmCont ψ S T om → ∀ γ : ℝ → GA D S × GA D T, Continuous γ → (∀ s t, γ (s + t) = γ s * γ t) → (∀ t, (γ t).1 ∈ GinfC S ∧ (γ t).2 ∈ GinfC T) → ∀ X : Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ, (∀ k l, HasDerivAt (fun t => GlobalTheory.RealWeil.mM θ S T (γ t) k l) (X k l) 0) → ∃ lam : ℂ, ∀ F : GlobalTheory.RealWeil.BB ψ S T, IsThetaFunO ψ S T F.1 → ∃ u : ℝ → GlobalTheory.RealWeil.BB ψ S T, (∀ t, ((u t).1 : WO S T → ℂ) = om (γ t) F.1) ∧ HasDerivAt u (nOp (GlobalTheory.RealWeil.rhoV hψ σ S T) (GlobalTheory.RealWeil.HM S T) X F + lam • F) 0 := by
  intro D θ σ h ψ hψ S T om hw hc γ hγ hadd hinf X hX
  have hγ0 : γ 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_left_cancel (a := γ 0) (by rw [← this, mul_one])
  have hH := isHeis_rhoB (S := S) (T := T) h hψ
  have hL := lie_of_path (HM S T) X (fun t => mM θ S T (γ t)) (by simp only [hγ0, map_one])
    (fun t => mM_unitary h.inf _) hX
  obtain ⟨κ, _, c, p, q, hq, hn⟩ := GlobalTheory.Mem.Lift.Normal.normal_quad (Ix S T) (HM S T) X HM_herm HM_det hL
  obtain ⟨Ω, hΩ, -, hd⟩ := GlobalTheory.T.hasDerivAt_oscillatorAction_unitaryPath_quadratic (Ix S T) (HM S T) HM_herm HM_det (BB ψ S T) (rhoV hψ σ S T) hH
    (GA D S × GA D T) (mM θ S T) (mM_unitary h.inf)
  obtain ⟨lam, hlam⟩ := hd γ X hγ0 hX κ c p q hq
  have sm := sm_of_theta (S := S) (T := T) h hψ
  choose s hs1 hs using fun t => GlobalTheory.T.weakWeilRep_eq_unit_smul_oscillator_real_points D θ σ h ψ hψ S T om hw Ω hΩ (γ t).1 (hinf t).1 (γ t).2 (hinf t).2
  replace hs : ∀ t (F : BB ψ S T), IsThetaFunO ψ S T F.1 → om (γ t) F.1 = s t • ((Ω (γ t) F).1 : WO S T → ℂ) := hs
  obtain ⟨-, hsmul, hsm, hone, hmul, -⟩ := hΩ
  have cs : ∀ (a : ℂ) (G : BB ψ S T), ((a • G).1 : WO S T → ℂ) = a • (G.1 : WO S T → ℂ) := fun _ _ => rfl
  have hne : ∀ t, s t ≠ 0 := fun t e => by simpa [e] using hs1 t
  have hD : ∀ F : BB ψ S T, IsThetaFunO ψ S T F.1 →
      HasDerivAt (fun t => Ω (γ t) F) (nOp (rhoV hψ σ S T) (HM S T) X F + lam • F) 0 := fun F hF =>
    hn _ _ hH F (sm F hF) ▸ hlam F (sm F hF)
  by_cases hex : ∃ F₀ : BB ψ S T, IsThetaFunO ψ S T F₀.1 ∧ F₀ ≠ 0
  swap
  · push Not at hex
    refine ⟨lam, fun F hF => ⟨fun t => Ω (γ t) F, fun t => ?_, hD F hF⟩⟩
    have e : Ω (γ t) F = 0 := by
      have := hsmul (γ t) 0 F (sm F hF)
      rw [zero_smul, zero_smul] at this
      exact (congrArg (Ω (γ t)) (hex F hF)).trans this
    rw [hs t F hF]
    beta_reduce
    rw [e]
    exact (smul_zero _).symm
  obtain ⟨F₀, hF₀, hne₀⟩ := hex
  have hΩne : ∀ g, Ω g F₀ ≠ 0 := by
    intro g e
    have h1 := hmul g⁻¹ g F₀ (sm _ hF₀)
    have h2 := hsmul g⁻¹ 0 F₀ (sm _ hF₀)
    rw [zero_smul, zero_smul] at h2
    rw [inv_mul_cancel, hone _ (sm _ hF₀), e, h2] at h1
    exact hne₀ h1
  have hth : ∀ t, IsThetaFunO ψ S T (Ω (γ t) F₀).1 := by
    intro t
    have h1 := (thetaSub ψ S T).smul_mem (s t)⁻¹ (hw.om_pres (γ t) _ hF₀)
    rw [hs t F₀ hF₀, smul_smul, inv_mul_cancel₀ (hne t), one_smul] at h1
    exact h1
  have hms : ∀ t t', s (t + t') = s t * s t' := by
    intro t t'
    have h1 := hs (t + t') F₀ hF₀
    rw [hadd, map_mul, Module.End.mul_apply, hs t' F₀ hF₀, map_smul, hs t _ (hth t'), ← hmul _ _ _ (sm _ hF₀),
      smul_smul] at h1
    have h2 : (s t' * s t) • Ω (γ t * γ t') F₀ = s (t + t') • Ω (γ t * γ t') F₀ := QB_ext fun x => by
      rw [cs, cs, h1]
    rw [← smul_left_injective ℂ (hΩne _) h2, mul_comm]
  have hs0 : s 0 = 1 := by
    have := hms 0 0
    rw [add_zero] at this
    exact mul_left_cancel₀ (hne 0) (by rw [← this, mul_one])
  obtain ⟨w, hw₀⟩ : ∃ w, (F₀.1 : WO S T → ℂ) w ≠ 0 := by
    by_contra hn'
    push Not at hn'
    exact hne₀ (QB_ext hn')
  have hcs : ContinuousAt s 0 := by
    have h1 : ContinuousAt (fun t => ev _ _ w (Ω (γ t) F₀)) 0 :=
      (ev _ _ w).continuous.continuousAt.comp (hD F₀ hF₀).continuousAt
    have h2 : ev _ _ w (Ω (γ 0) F₀) ≠ 0 := by
      rw [hγ0, hone _ (sm _ hF₀), ev_apply]
      exact hw₀
    have h3 : ContinuousAt (fun t => om (γ t) F₀.1 w) 0 := ((hc _ hF₀ w).comp hγ).continuousAt
    refine (h3.div h1 h2).congr ?_
    filter_upwards [h1.eventually_ne h2] with t ht
    rw [Pi.div_apply, div_eq_iff ht, hs t F₀ hF₀, ev_apply]
    rfl
  obtain ⟨m, hm⟩ := exists_hasDerivAt_char s hms hs0 hcs
  refine ⟨lam + m, fun F hF => ⟨fun t => s t • Ω (γ t) F, fun t => (cs _ _).trans (hs t F hF).symm, ?_⟩⟩
  have h1 := hm.smul (hD F hF)
  rw [hs0, one_smul, hγ0, hone _ (sm _ hF)] at h1
  rw [add_smul, ← add_assoc]
  exact h1

end GlobalTheory.Mem.Lift.GenZero

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilRepresentationOneParameterGeneratorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilRep_generator_realOneParameter_supNorm : ∀ (D : D7) (θ : InfF D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → OmCont ψ S T om → ∀ γ : ℝ → GA D S × GA D T, Continuous γ → (∀ s t, γ (s + t) = γ s * γ t) → (∀ t, (γ t).1 ∈ GinfC S ∧ (γ t).2 ∈ GinfC T) → ∀ X : Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ, (∀ k l, HasDerivAt (fun t => GlobalTheory.RealWeil.mM θ S T (γ t) k l) (X k l) 0) → ∃ lam : ℂ, ∀ F : GlobalTheory.RealWeil.BB ψ S T, IsThetaFunO ψ S T F.1 → ∃ u : ℝ → GlobalTheory.RealWeil.BB ψ S T, (∀ t, ((u t).1 : WO S T → ℂ) = om (γ t) F.1) ∧ HasDerivAt u (nOp (GlobalTheory.RealWeil.rhoV hψ σ S T) (GlobalTheory.RealWeil.HM S T) X F + lam • F) 0 := by
  first | exact @GlobalTheory.Mem.Lift.GenZero.exists_generator | exact GlobalTheory.Mem.Lift.GenZero.exists_generator | (intros; apply GlobalTheory.Mem.Lift.GenZero.exists_generator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PinsCardIndexRanks
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.GrpCount

section Count

variable {κ : Type} [CommRing κ] {r : ℕ}

theorem card_unitri (Fr : Fin r → Fin r → Prop) (hFr : ∀ i j, Fr i j → i < j) (H : Subgroup (GL (Fin r) κ))
    (hH : ∀ g : GL (Fin r) κ, g ∈ H ↔ (∀ i j, j < i → (g : Matrix (Fin r) (Fin r) κ) i j = 0) ∧
      (∀ i, (g : Matrix (Fin r) (Fin r) κ) i i = 1) ∧
      ∀ i j, i < j → ¬ Fr i j → (g : Matrix (Fin r) (Fin r) κ) i j = 0) :
    Nat.card H = Nat.card κ ^ Nat.card {p : Fin r × Fin r // Fr p.1 p.2} := by
  classical
  let mk : ({p : Fin r × Fin r // Fr p.1 p.2} → κ) → Matrix (Fin r) (Fin r) κ := fun f i j =>
    if i = j then 1 else if h : Fr i j then f ⟨(i, j), h⟩ else 0
  have hlow : ∀ f i j, j < i → mk f i j = 0 := by
    intro f i j hij
    have hne : i ≠ j := (ne_of_lt hij).symm
    simp only [mk, if_neg hne]
    rw [dif_neg]
    intro h
    exact absurd (hFr i j h) (not_lt.2 hij.le)
  have hdet : ∀ f, (mk f).det = 1 := by
    intro f
    rw [Matrix.det_of_upperTriangular (fun i j hij => hlow f i j hij)]
    simp [mk]
  let toG : ({p : Fin r × Fin r // Fr p.1 p.2} → κ) → GL (Fin r) κ := fun f =>
    Matrix.nonsingInvUnit (mk f) (by rw [hdet]; exact isUnit_one)
  have htoG : ∀ f, ((toG f : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) = mk f := fun f => rfl
  let e : H ≃ ({p : Fin r × Fin r // Fr p.1 p.2} → κ) :=
    { toFun := fun g p => (g.1 : Matrix (Fin r) (Fin r) κ) p.1.1 p.1.2
      invFun := fun f => ⟨toG f, (hH _).2 ⟨fun i j hij => by rw [htoG]; exact hlow f i j hij,
        fun i => by rw [htoG]; simp [mk],
        fun i j hij hn => by
          rw [htoG]
          simp only [mk, if_neg (ne_of_lt hij), dif_neg hn]⟩⟩
      left_inv := by
        intro g
        obtain ⟨h0, h1, h2⟩ := (hH g.1).1 g.2
        apply Subtype.ext
        apply Units.ext
        ext i j
        change mk (fun p => (g.1 : Matrix (Fin r) (Fin r) κ) p.1.1 p.1.2) i j = (g.1 : Matrix (Fin r) (Fin r) κ) i j
        simp only [mk]
        by_cases hij : i = j
        · subst hij; rw [if_pos rfl, h1]
        · rw [if_neg hij]
          by_cases hf : Fr i j
          · rw [dif_pos hf]
          · rw [dif_neg hf]
            rcases lt_or_gt_of_ne hij with hl | hl
            · exact (h2 i j hl hf).symm
            · exact (h0 i j hl).symm
      right_inv := by
        intro f
        funext p
        show mk f p.1.1 p.1.2 = f p
        simp only [mk, if_neg (ne_of_lt (hFr _ _ p.2)), dif_pos p.2] }
  rw [Nat.card_congr e, Nat.card_fun]

theorem card_unip : Nat.card (unip κ r) = Nat.card κ ^ Nat.card {p : Fin r × Fin r // p.1 < p.2} := by
  refine card_unitri (fun i j => i < j) (fun _ _ h => h) _ fun g => ?_
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨fun i j hij => h0 hij, h1, fun i j hij hn => absurd hij hn⟩
  · rintro ⟨h0, h1, -⟩
    exact ⟨fun i j hij => h0 i j hij, h1⟩

theorem card_unipCol (a c : ℕ) : Nat.card (unipCol κ r a c) =
    Nat.card κ ^ Nat.card {p : Fin r × Fin r // p.1 < p.2 ∧ ¬ (a ≤ p.1.val ∧ p.1.val < c ∧ p.2.val = c)} := by
  refine card_unitri (fun i j => i < j ∧ ¬ (a ≤ i.val ∧ i.val < c ∧ j.val = c)) (fun _ _ h => h.1) _ fun g => ?_
  constructor
  · rintro ⟨⟨h0, h1⟩, h2⟩
    refine ⟨fun i j hij => h0 hij, h1, fun i j hij hn => ?_⟩
    have : a ≤ i.val ∧ i.val < c ∧ j.val = c := by
      by_contra hc
      exact hn ⟨hij, hc⟩
    exact h2 i j this.1 this.2.1 this.2.2
  · rintro ⟨h0, h1, h2⟩
    refine ⟨⟨fun i j hij => h0 i j hij, h1⟩, fun i j ha hc hj => h2 i j ?_ ?_⟩
    · show i.val < j.val; omega
    · rintro ⟨-, hn⟩; exact hn ⟨ha, hc, hj⟩

theorem card_pairs_split {a c : ℕ} (hac : a ≤ c) (hc : c < r) :
    Nat.card {p : Fin r × Fin r // p.1 < p.2} =
      Nat.card {p : Fin r × Fin r // p.1 < p.2 ∧ ¬ (a ≤ p.1.val ∧ p.1.val < c ∧ p.2.val = c)} + (c - a) := by
  classical
  have hQ : Nat.card {p : Fin r × Fin r // p.1 < p.2 ∧ (a ≤ p.1.val ∧ p.1.val < c ∧ p.2.val = c)} = c - a := by
    rw [← Nat.card_fin (c - a)]
    refine Nat.card_congr
      { toFun := fun p => ⟨p.1.1.val - a, by have := p.2.2; omega⟩
        invFun := fun i => ⟨(⟨a + i.val, by have := i.2; omega⟩, ⟨c, hc⟩), by
          refine ⟨?_, ?_, ?_, rfl⟩
          · show a + i.val < c; have := i.2; omega
          · show a ≤ a + i.val; omega
          · show a + i.val < c; have := i.2; omega⟩
        left_inv := by
          rintro ⟨⟨i, j⟩, h1, h2, h3, h4⟩
          have h2' : a ≤ i.val := h2
          apply Subtype.ext
          apply Prod.ext
          · apply Fin.ext; show a + (i.val - a) = i.val; omega
          · apply Fin.ext; exact h4.symm
        right_inv := by
          intro i
          apply Fin.ext
          show a + i.val - a = i.val
          omega }
  rw [← hQ]
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun p : Fin r × Fin r => p.1 < p.2))
    (fun p : Fin r × Fin r => a ≤ p.1.val ∧ p.1.val < c ∧ p.2.val = c), Finset.filter_filter, Finset.filter_filter,
    add_comm]

theorem card_pi {ι : Type} [Fintype ι] {M : ι → Type} [∀ i, Group (M i)] (H : ∀ i, Subgroup (M i)) :
    Nat.card (Subgroup.pi Set.univ H) = ∏ i, Nat.card (H i) := by
  rw [← Nat.card_pi]
  exact Nat.card_congr ((Equiv.subtypeEquivRight fun x => by simp [Subgroup.mem_pi]).trans
    (Equiv.subtypePiEquivPi (p := fun i y => y ∈ H i)))

end Count

end GlobalTheory.Mem.GrpCount

namespace GlobalTheory.Mem.GrpCount

theorem symPos_injective {r ρ k : ℕ} (h : ρ + k ≤ r) : Function.Injective (symPos r ρ k) := by
  intro i j hij
  have hv := congrArg Fin.val hij
  simp only [symPos] at hv
  have hi := i.2
  have hj := j.2
  apply Fin.ext
  split_ifs at hv <;> rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv <;> omega

theorem index_of_lvlTie {D : D7} {G : Type} [Group G] {Q0 : Subgroup G} {ψ0 : Q0 →* D.what₂.LLˣ} {Qs : Subgroup G}
    {ψs : Qs →* D.what₂.LLˣ} {eG : G ≃* G0g D.nd} {Pg : Finset (Pl D.host.E)} {pl : (Σ k : Fin 2, D.nd.PlG k) ≃ ↥Pg}
    {res : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), kP (pl kv).1 ≃+* ZMod (D.host.g kv.1)}
    {ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) D.what₂.LL} {eC : G ≃* G0 Pg D.R.r}
    (h : LvlTie D Q0 ψ0 Qs ψs eG Pg pl res ψ eC) :
    Nat.card Q0 = Nat.card Qs * (D.host.g 0 * D.host.g 1) ^ (D.R.k * D.R.f) := by
  have hrk : D.R.rS + D.R.k < D.R.r := by
    have := D.R.two_le_m
    simp only [Ranks.rS, Ranks.r]
    omega
  let σ : Fin D.R.r ≃ Fin D.R.r :=
    Equiv.ofBijective _ (Finite.injective_iff_bijective.1 (symPos_injective hrk.le))
  have h0 : Nat.card Q0 = Nat.card (_root_.Formalism.L2.DIV.P0 Pg D.R.r ψ).H :=
    Nat.card_congr (eC.toEquiv.subtypeEquiv fun g => h.p0 g)
  let φ : G0 Pg D.R.r ≃ G0 Pg D.R.r := Equiv.piCongrRight fun PP =>
    (Units.mapEquiv (Matrix.reindexAlgEquiv (kP PP.1) (kP PP.1) σ.symm).toMulEquiv).toEquiv
  have hφ : ∀ (x : G0 Pg D.R.r) (PP : ↥Pg) (i j : Fin D.R.r),
      ((φ x PP : GL (Fin D.R.r) (kP PP.1)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)) i j =
        ((x PP : GL (Fin D.R.r) (kP PP.1)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1))
          (symPos D.R.r D.R.rS D.R.k i) (symPos D.R.r D.R.rS D.R.k j) := by
    intro x PP i j
    simp [φ, σ, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]
  have hs : Nat.card Qs = Nat.card (PsharpSym Pg D.R.r D.R.rS D.R.k ψ).H := by
    refine Nat.card_congr ((eC.toEquiv.trans φ).subtypeEquiv fun g => ?_)
    rw [h.ps g]
    constructor
    · rintro ⟨y, hy, hE⟩
      have hy' : φ (eC g) = y := by
        funext PP
        apply Units.ext
        ext i j
        rw [hφ]
        exact hE PP i j
      show φ (eC g) ∈ _
      rw [hy']
      exact hy
    · intro hm
      exact ⟨_, hm, fun PP i j => (hφ _ PP i j).symm⟩
  have hsplit := card_pairs_split (r := D.R.r) (a := D.R.rS) (c := D.R.rS + D.R.k) (by omega) hrk
  rw [Nat.add_sub_cancel_left] at hsplit
  have hP0 : Nat.card (_root_.Formalism.L2.DIV.P0 Pg D.R.r ψ).H =
      ∏ PP : ↥Pg, Nat.card (kP PP.1) ^ Nat.card {p : Fin D.R.r × Fin D.R.r // p.1 < p.2} := by
    show Nat.card (Subgroup.pi Set.univ fun PP : ↥Pg => unip (kP PP.1) D.R.r) = _
    rw [card_pi]
    exact Finset.prod_congr rfl fun PP _ => card_unip
  have hPs : Nat.card (PsharpSym Pg D.R.r D.R.rS D.R.k ψ).H =
      ∏ PP : ↥Pg, Nat.card (kP PP.1) ^ Nat.card {p : Fin D.R.r × Fin D.R.r //
        p.1 < p.2 ∧ ¬ (D.R.rS ≤ p.1.val ∧ p.1.val < D.R.rS + D.R.k ∧ p.2.val = D.R.rS + D.R.k)} := by
    show Nat.card (Subgroup.pi Set.univ fun PP : ↥Pg => unipCol (kP PP.1) D.R.r D.R.rS (D.R.rS + D.R.k)) = _
    rw [card_pi]
    exact Finset.prod_congr rfl fun PP _ => card_unipCol _ _
  have hk : ∏ PP : ↥Pg, Nat.card (kP PP.1) ^ D.R.k = (D.host.g 0 * D.host.g 1) ^ (D.R.k * D.R.f) := by
    rw [← Equiv.prod_comp pl (fun PP : ↥Pg => Nat.card (kP PP.1) ^ D.R.k)]
    have hq : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Nat.card (kP (pl kv).1) = D.host.g kv.1 := fun kv => by
      rw [Nat.card_congr (res kv).toEquiv, Nat.card_zmod]
    simp only [hq]
    rw [Fintype.prod_sigma]
    simp only [Finset.prod_const, Finset.card_univ, D.nd.card_PlG, Fin.prod_univ_two]
    ring
  rw [h0, hs, hP0, hPs, ← hk, hsplit, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun PP _ => pow_add _ _ _

end GlobalTheory.Mem.GrpCount

namespace GlobalTheory.Mem.R3

theorem pins_card_index_ranks : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type)
    (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG →
    Fintype.card G = D.what₂.restRowsFiniteGroupCard ∧ Nat.card F.P0 = Nat.card F.P1 * (D.host.g 0 * D.host.g 1) ^ (D.R.k * D.R.f) ∧
      A3.A.r = D.R.r ∧ A3.A.t = D.R.t ∧ A3.A.v0 = InfinitePlace.mk D.what₂.embLL := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG h
  obtain ⟨gramR, c0R, c0L, hT⟩ := h.char.base.fam.tie
  refine ⟨?_, ?_, hT.ranks.2.1, hT.ranks.2.2, hT.v0⟩
  · rw [← Nat.card_eq_fintype_card, Nat.card_congr (R.eG.trans cG).toEquiv, D.nd.restN_card_levelGroup_eq, Nat.card_pi,
      Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    change ∏ _y : D.nd.PlG k, Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) = _
    rw [Finset.prod_const, Finset.card_univ, D.nd.card_PlG k]
  · obtain ⟨Pg, pl, res, ψ, eC, hL, -⟩ := h.keep.psi
    exact GlobalTheory.Mem.GrpCount.index_of_lvlTie hL

end GlobalTheory.Mem.R3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedCompAtDetIdl
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open GlobalTheory.Mem.Chr hiding ordF Ideles HChar atFin unif
open Formalism.L2.Host (HChar atFin unif ordF)
open GlobalTheory.CharValCompare (IsFr)

namespace GlobalTheory.Mem.Col2.DetProj

section General

variable {E : Type} [Field E] [NumberField E]

theorem valuation_eq_exp (w : HeightOneSpectrum (𝓞 E)) (k : Eˣ) :
    w.valuation E (k : E) = WithZero.exp (-ordF w k) := by
  unfold ordF
  rw [neg_neg, WithZero.exp_log (by simp)]

variable [StarRing E] {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem ordSub_conjP (p : DecoF E n ST SG Q) (w : HeightOneSpectrum (𝓞 E)) :
    ordSub (conjPrime₂ w) (detSub p.deco.1.N) = -ordSub w (detSub p.deco.1.N) := by
  have hfull : Submodule.IsFullLattice E p.deco.1.N := by
    letI : Submodule.IsLattice E p.deco.1.N := p.deco.2.lat
    refine ⟨?_⟩
    apply top_unique
    rw [← ((Pi.basisFun E (Fin n)).map (ptFr p w)).span_eq]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨s, hs, hx⟩ := (mem_locP _ _ _).1 ((isFr_ptFr p w _).2 (CharValCompare.single_mem_stdAt w i))
    have hs0 : (algebraMap (𝓞 E) E s) ≠ 0 := by
      intro h
      have : s = 0 := (FaithfulSMul.algebraMap_injective (𝓞 E) E) (by simpa using h)
      exact hs (this ▸ w.asIdeal.zero_mem)
    have hx' : (algebraMap (𝓞 E) E s) • ptFr p w (Pi.single i 1) ∈ p.deco.1.N := by
      rwa [IsScalarTower.algebraMap_smul]
    have hm := Submodule.smul_mem (Submodule.span E (p.deco.1.N : Set (Sp E n)))
      (algebraMap (𝓞 E) E s)⁻¹ (Submodule.subset_span hx')
    rw [← mul_smul, inv_mul_cancel₀ hs0, one_smul] at hm
    simpa only [Module.Basis.map_apply, Pi.basisFun_apply, SetLike.mem_coe] using hm
  have h := CharValCompare.val_dual (P := w) ⟨p.deco.2.lat, p.deco.2.uni⟩ (isFr_ptFr p w) (isFr_ptFr p (conjPrime₂ w))
  rw [map_mul, valuation_star, CharValCompare.conjP_conjP] at h
  rw [ordSub_detSub_eq hfull (isFr_ptFr p w), ordSub_detSub_eq hfull (isFr_ptFr p (conjPrime₂ w))]
  have h' : w.valuation E ((LinearEquiv.det (ptFr p w) : Eˣ) : E) *
      (conjPrime₂ w).valuation E ((LinearEquiv.det (ptFr p (conjPrime₂ w)) : Eˣ) : E) = 1 := h
  rw [valuation_eq_exp, valuation_eq_exp, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_inj] at h'
  omega


open Classical in
theorem valued_compAt_detIdl (SB : Finset (HeightOneSpectrum (𝓞 E))) (p : DecoF E n ST SG Q)
    (w : HeightOneSpectrum (𝓞 E)) :
    Valued.v (compAt w (detIdl SB p.deco.1.N (ptFr p))) = WithZero.exp (-(if w ∈ SB then ordSub w (detSub p.deco.1.N)
      else if conjPrime₂ w ∈ SB then 0 else ((ordSub w (detSub p.deco.1.N)).toNat : ℤ))) := by
  have hfull : Submodule.IsFullLattice E p.deco.1.N := by
    letI : Submodule.IsLattice E p.deco.1.N := p.deco.2.lat
    refine ⟨?_⟩
    apply top_unique
    rw [← ((Pi.basisFun E (Fin n)).map (ptFr p w)).span_eq]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨s, hs, hx⟩ := (mem_locP _ _ _).1 ((isFr_ptFr p w _).2 (CharValCompare.single_mem_stdAt w i))
    have hs0 : (algebraMap (𝓞 E) E s) ≠ 0 := by
      intro h
      have : s = 0 := (FaithfulSMul.algebraMap_injective (𝓞 E) E) (by simpa using h)
      exact hs (this ▸ w.asIdeal.zero_mem)
    have hx' : (algebraMap (𝓞 E) E s) • ptFr p w (Pi.single i 1) ∈ p.deco.1.N := by
      rwa [IsScalarTower.algebraMap_smul]
    have hm := Submodule.smul_mem (Submodule.span E (p.deco.1.N : Set (Sp E n)))
      (algebraMap (𝓞 E) E s)⁻¹ (Submodule.subset_span hx')
    rw [← mul_smul, inv_mul_cancel₀ hs0, one_smul] at hm
    simpa only [Module.Basis.map_apply, Pi.basisFun_apply, SetLike.mem_coe] using hm
  rw [compAt_detIdl SB p.deco.2.lat]
  split_ifs
  · rw [valued_algebraMap, valuation_eq_exp, ordSub_detSub_eq hfull (isFr_ptFr p w)]
  · simp
  · rw [map_pow, valued_algebraMap, valuation_eq_exp, ordF_unif_self, ← WithZero.exp_nsmul]
    simp

theorem valued_compAt_conjP {SB : Finset (HeightOneSpectrum (𝓞 E))} (hs : ∀ P ∈ SB, conjPrime₂ P ∉ SB)
    (p : DecoF E n ST SG Q) (w : HeightOneSpectrum (𝓞 E)) :
    Valued.v (compAt w (detIdl SB p.deco.1.N (ptFr p))) =
      Valued.v (compAt (conjPrime₂ w) (detIdl SB p.deco.1.N (ptFr p))) * WithZero.exp (-ordSub w (detSub p.deco.1.N)) := by
  rw [valued_compAt_detIdl, valued_compAt_detIdl, ← WithZero.exp_add, WithZero.exp_inj, CharValCompare.conjP_conjP,
    ordSub_conjP]
  by_cases h : w ∈ SB
  · rw [if_pos h, if_neg (hs w h), if_pos h]
    omega
  · rw [if_neg h, if_neg h]
    split_ifs <;> omega

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem toDtQ_detPt : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (n : ℕ) (ST SG Q SQ : Finset (HeightOneSpectrum (𝓞 H.E)))
    (h : Q ⊆ SQ) (p : DecoF H.E n ST SG Q), LevOk H SG SQ → toDtQ H h (detPt H SQ p) = detPt H Q p := by
  intro R H n ST SG Q SQ h p hL
  classical
  have hL' := hL.mono h
  have hsub : uSG SG Q ⊆ uSG SG SQ := by
    intro P
    simp only [Finset.mem_union]
    exact Or.imp_right fun h' => h h'
  unfold detPt
  rw [toDtQ_mk]
  symm
  rw [QuotientGroup.eq, inv_mul_eq_div]
  have h0 : ∀ w (a : Ideles H.E), compAt w a ≠ 0 := fun w a => ((Group.isUnit a).map (compAt w)).ne_zero
  refine mem_KDq_of_conj hL' _ (fun w => ?_) fun P hP => ?_
  · rw [map_div, map_div, map_div₀, map_div₀]
    unfold ptIdl
    rw [valued_compAt_conjP hL.split p w, valued_compAt_conjP hL'.split p w, mul_div_mul_right _ _ WithZero.exp_ne_zero]
  · have e1 : compAt P (ptIdl H SQ p / ptIdl H Q p) = 1 := by
      rw [map_div, div_eq_one_iff_eq (h0 _ _)]
      unfold ptIdl
      rw [compAt_detIdl _ p.deco.2.lat, compAt_detIdl _ p.deco.2.lat, if_pos hP, if_pos (hsub hP)]
    have e2 : compAt (conjPrime₂ P) (ptIdl H SQ p / ptIdl H Q p) = 1 := by
      rw [map_div, div_eq_one_iff_eq (h0 _ _)]
      unfold ptIdl
      rw [compAt_detIdl _ p.deco.2.lat, compAt_detIdl _ p.deco.2.lat, if_neg (hL.split P (hsub hP)),
        if_neg (hL'.split P hP), CharValCompare.conjP_conjP, if_pos hP, if_pos (hsub hP)]
    have e3 := valued_sigR (host_cmData R H) P ((finAf H.F H.E (ptIdl H SQ p / ptIdl H Q p) : AfE H.F H.E) - 1)
    rw [map_sub (adAt _ _), adAt_finAf, e2, map_one (adAt _ _), sub_self, map_zero, Valuation.zero_iff,
      map_sub (Formalism.UG.sigR _ _), map_one (Formalism.UG.sigR _ _), map_sub (adAt _ _), map_one (adAt _ _), sub_eq_zero] at e3
    rw [e1, e3, div_one, sub_self, map_zero]
    exact zero_lt_one

end GlobalTheory.Mem.Col2.DetProj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitarySphericalIffHasSatakeInert
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitarySphericalIffHasSatakeInert
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

noncomputable section

namespace GlobalTheory.InertSatake

def transport {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] (P : G ≃ₜ* H)
    (σ : SmIrr G) : SmIrr H where
  V := σ.V
  ρ := σ.ρ.comp P.symm.toMulEquiv.toMonoidHom
  smooth v := (σ.smooth v).preimage P.symm.continuous
  irred := by
    obtain ⟨h0, h⟩ := (CuspRep.isIrreducible_iff _).1 σ.irred
    refine (CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h W fun g v hv => ?_⟩
    have := hW (P g) v hv
    change σ.ρ (P.symm (P g)) v ∈ W at this
    rwa [P.symm_apply_apply] at this

theorem transport_apply {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] (P : G ≃ₜ* H)
    (σ : SmIrr G) (g : G) (v : σ.V) : (transport P σ).ρ (P g) v = σ.ρ g v := by
  change σ.ρ (P.symm (P g)) v = _
  rw [P.symm_apply_apply]

theorem isAdmissible_transport {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (P : G ≃ₜ* H) (σ : SmIrr G) (h : IsAdmissible σ.ρ) : IsAdmissible (transport P σ).ρ := by
  refine ⟨(transport P σ).smooth, fun K ho hc => ?_⟩
  let K' : Subgroup G := K.comap P.toMulEquiv.toMonoidHom
  show FiniteDimensional ℂ (fixed (σ.ρ.comp P.symm.toMulEquiv.toMonoidHom) K)
  have e : fixed (σ.ρ.comp P.symm.toMulEquiv.toMonoidHom) K = fixed σ.ρ K' := by
    ext x
    rw [GlobalTheory.LGrp.mem_fixed, GlobalTheory.LGrp.mem_fixed]
    constructor
    · intro hx k hk
      have := hx (P k) hk
      change σ.ρ (P.symm (P k)) x = x at this
      rwa [P.symm_apply_apply] at this
    · intro hx k hk
      exact hx (P.symm k) (by change P (P.symm k) ∈ K; rwa [P.apply_symm_apply])
  rw [e]
  refine h.2 K' (ho.preimage P.continuous) ?_
  have : (K' : Set G) = P.toHomeomorph ⁻¹' (K : Set H) := rfl
  rw [this]
  exact P.toHomeomorph.isCompact_preimage.2 hc

variable {L : Type} [Field L] [TopologicalSpace L] [IsTopologicalRing L] {n : ℕ}

def conjEquiv (s : L →+* L) (b : GL (Fin n) L) (hb : cT s b.1 * 1 * b.1 = antiJ L n) :
    UJ s (1 : Matrix (Fin n) (Fin n) L) ≃ₜ* GU s n where
  toFun g := ⟨b⁻¹ * g * b, GlobalTheory.InertDoubleCoset.conj_mem_UJ s hb g.2⟩
  invFun h := ⟨b * h * b⁻¹, by simpa using GlobalTheory.InertDoubleCoset.conj_mem_UJ s (GlobalTheory.InertDoubleCoset.inv_frame s hb) h.2⟩
  left_inv g := Subtype.ext (by simp [mul_assoc])
  right_inv h := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const

end GlobalTheory.InertSatake


open GlobalTheory.InertSatake in
theorem GlobalTheory.InertSatake.sph_iff_isSat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AU E n)
    (w : HeightOneSpectrum (𝓞 E)), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → ¬ IsSplitAt w →
    (π.Sph w ↔ ∃ α, π.IsSat w α) := by
  intro E _ _ _ n π w hun hns
  obtain ⟨π, rfl⟩ := AU.mk_surjective π
  show IsUnramU π.V w ↔ ∃ α, π.IsSat w α
  constructor
  · rintro ⟨φ, hφ, h0, hfix⟩
    obtain ⟨s, ϖ, q, hs, hU⟩ := GlobalTheory.T.unramified_nonsplit_exists_conj_involution_uniformiser E w hun hns
    obtain ⟨e, he⟩ := GlobalTheory.T.fixedPlace_unitaryLocalPoints_equiv_localUnitaryGroup E n w s hs hU.2.1
    obtain ⟨b, hbK, hb⟩ := GlobalTheory.LFun.InertChart.exists_congr_antiJ hU (one_mem (GlobalTheory.LFun.KGL w (n := n)))
      (by rw [Units.val_one, cT_one])
    let P : locU n w ≃ₜ* GU s n := e.trans (conjEquiv s b hb)
    have hP : ∀ x : locU n w, ((P x : GU s n) : GL (Fin n) (w.adicCompletion E)) = b⁻¹ * cLoc w x.1 * b := fun x => by
      change b⁻¹ * (e x : GL (Fin n) _) * b = _
      rw [he]
    obtain ⟨σ0, hadm, hcomp⟩ := GlobalTheory.T.exists_admissible_localComponent_definiteUnitary E n π w
    obtain ⟨r, -, -, hr⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints E n w
    obtain ⟨-, f, hf0, hfm, hf⟩ := hcomp
    let F : σ0.ρ.IntertwiningMap (π.rep.comp (locU n w).subtype) :=
      ⟨f.codRestrict _ hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
    have hF0 : F ≠ 0 := fun h => hf0 (LinearMap.ext fun v => by
      have := congrArg Subtype.val (DFunLike.congr_fun h v)
      exact this)
    have htop := (GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor (UA E n) (locU n w) π.V σ0.V σ0.V π.rep (locU n w).subtype σ0.ρ σ0.ρ
      π.isIrreducible_rep σ0.irred σ0.irred (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1
    obtain ⟨v, hv0, hv⟩ := GlobalTheory.CuspRep.LocSph.exists_fixed_of_mem_iSup (π.rep.comp (locU n w).subtype) σ0.ρ σ0.irred
      (fun i : σ0.ρ.IntertwiningMap (π.rep.comp (locU n w).subtype) => i.toLinearMap)
      (fun i g u => Representation.IntertwiningMap.isIntertwining _ _ i g u) {x | cLoc w x.1 ∈ GlobalTheory.LFun.KGL w (n := n)} ⟨φ, hφ⟩
      (fun h => h0 (congrArg Subtype.val h)) (fun k hk => Subtype.ext (hfix k.1 k.2 hk))
      (htop ▸ Submodule.mem_top)
    let σ1 := transport P σ0
    have hsph : GlobalTheory.LGrp.IsSpherical σ1.ρ (KU s n) := by
      refine (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, hv0⟩
      obtain ⟨x, rfl⟩ := P.surjective k
      rw [transport_apply]
      refine hv x ?_
      have h1 : ((P x : GU s n) : GL (Fin n) (w.adicCompletion E)) ∈ GLint (Fin n) (intL (w.adicCompletion E)) :=
        (Set.ext_iff.1 (GlobalTheory.LFun.IntPtsUnitary.coe_KU s n) (P x)).1 hk
      have h2 : cLoc w x.1 = b * (P x : GL (Fin n) (w.adicCompletion E)) * b⁻¹ := by rw [hP]; group
      show cLoc w x.1 ∈ GlobalTheory.LFun.KGL w (n := n)
      rw [h2]
      exact mul_mem (mul_mem hbK h1) (inv_mem hbK)
    obtain ⟨α, hα⟩ := GlobalTheory.T.exists_satake_parameter_spherical_unramifiedUnitary E w ϖ s q n hU σ1.V σ1.ρ σ1.irred (isAdmissible_transport P σ0 hadm) hsph
    refine ⟨α, s, ϖ, q, hs, hU, b, hbK, by have h := hb; rw [Units.val_one, Matrix.mul_one] at h; exact h, P.toMulEquiv.toMonoidHom, hP, σ1,
      ⟨σ1.irred, f, hf0, hfm, fun x u => ?_⟩, hα⟩
    change f (σ0.ρ (P.symm (P x)) u) = _
    rw [P.symm_apply_apply]
    exact hf x u
  · rintro ⟨α, s, ϖ, q, hs, hU, b, hbK, hb, p, hp, σ, ⟨-, f, hf0, hfm, hf⟩, hsat⟩
    obtain ⟨e, he⟩ := GlobalTheory.T.fixedPlace_unitaryLocalPoints_equiv_localUnitaryGroup E n w s hs hU.2.1
    have hb1 : cT s b.1 * 1 * b.1 = antiJ _ n := by rwa [Matrix.mul_one]
    have hsurj : Function.Surjective p := fun g => by
      let P := e.trans (conjEquiv s b hb1)
      have hP : ((P (P.symm g) : GU s n) : GL (Fin n) (w.adicCompletion E)) =
          b⁻¹ * cLoc w (P.symm g).1 * b := by
        change b⁻¹ * (e _ : GL (Fin n) _) * b = _
        rw [he]
      refine ⟨P.symm g, Subtype.ext ?_⟩
      rw [hp, ← hP, P.apply_symm_apply]
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hsat.1
    have hfv : f v ≠ 0 := by
      intro h
      have hker := ((CuspRep.isIrreducible_iff _).1 σ.irred).2 (LinearMap.ker f) fun g u hu => by
        obtain ⟨x, rfl⟩ := hsurj g
        rw [LinearMap.mem_ker, hf, LinearMap.mem_ker.1 hu, map_zero]
      rcases hker with h1 | h1
      · have m : v ∈ LinearMap.ker f := LinearMap.mem_ker.2 h
        rw [h1] at m
        exact hv0 ((Submodule.mem_bot ℂ).1 m)
      · exact hf0 (LinearMap.ker_eq_top.1 h1)
    refine ⟨f v, hfm v, hfv, fun x hx hk => ?_⟩
    have hpk : p ⟨x, hx⟩ ∈ KU s n := by
      refine (Set.ext_iff.1 (GlobalTheory.LFun.IntPtsUnitary.coe_KU s n) _).2 ?_
      show ((p ⟨x, hx⟩ : GU s n) : GL (Fin n) (w.adicCompletion E)) ∈ GLint (Fin n) (intL _)
      rw [hp]
      exact mul_mem (mul_mem (inv_mem hbK) hk) hbK
    refine (hf ⟨x, hx⟩ v).symm.trans ?_
    rw [GlobalTheory.LGrp.mem_fixed.1 hv _ hpk]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitarySphericalIffHasSatakeInertStatement
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitary_spherical_iff_hasSatake_inert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AU E n) (w : HeightOneSpectrum (𝓞 E)), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → ¬ IsSplitAt w → (π.Sph w ↔ ∃ α, π.IsSat w α) := by
  first | exact @GlobalTheory.InertSatake.sph_iff_isSat | exact GlobalTheory.InertSatake.sph_iff_isSat | (intros; apply GlobalTheory.InertSatake.sph_iff_isSat <;> assumption)
end
end
