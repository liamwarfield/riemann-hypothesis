module

public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsDiffSumSmulOfIsLieComb
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrModelOfNumberFieldPlace

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}

def gen (y : (Σ k, J k) → Ω) (a : K → ℤ) (e₀ : Ω) (c : (k : K) → J k) : Ω :=
  (∏ k, y ⟨k, c k⟩ ^ a k) * e₀

def IsCls {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ} (b₀ : Fin r → E) (i : Fin r) (e : E) (t : Ω) : Prop :=
  e - t • b₀ i ∈ flagStep Ω b₀ i

def Sandwich {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G] {Li : Type} [AddCommGroup Li] [Module Ω Li]
    (M : LieModel G ξ Li) (V : Lat ξ Li) {r : ℕ} (b₀ : Fin r → Li) (m : ℕ) : Prop :=
  ∀ p : Cpt ξ, ∃ (b : Fin r → Li) (π : Fin r → Module.Dual Ω Li), (∀ i : ℕ, flagStep Ω b i = flagStep Ω b₀ i) ∧
    V.IsFrameAt b p ∧ (∀ i, (m : Ω) • b i ∈ M.lat p) ∧ (∀ i j, π i (b j) = if i = j then 1 else 0) ∧
    ∀ i, ∀ e ∈ M.lat p, (m : Ω) * π i e ∈ regAt ξ p

def gramAt {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G] {Li : Type} [AddCommGroup Li] [Module Ω Li]
    {M : LieModel G ξ Li} {y : (Σ k, J k) → Ω} (h : LieMetric M y) (z : Sp ℂ ⟶ X) {n : ℕ}
    (v : Fin n → (epsAt z ⟶ G)) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => h.ip z (v a) (v b)

def locRatio {L : Type} [Field L] [NumberField L] (a : K → ℤ) (w : (Σ k, J k) → L)
    (c : (k : K) → J k) (v : FinitePlace L) : ℝ :=
  ∏ k, ((⨆ i, v (w ⟨k, i⟩)) / v (w ⟨k, c k⟩)) ^ a k

end GlobalTheory.CompanionTheory.Ar.RootHt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSubFibreSubFib
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Sp Ω ⟶ X}
  {Li : Type} [AddCommGroup Li] [Module Ω Li] {L : Type} [Field L] [NumberField L]

def subGens (M : LieModel G ξ Li) (U : Submodule Ω Li) (z : Sp (𝓞 L) ⟶ X) {V : Type} [AddCommGroup V]
    [Module (𝓞 L) V] (MB : LieModel G z V) : Set V :=
  {x' | ∃ e ∈ U, ∃ v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G,
    M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e v ∧ (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x').left)}

def subFib (M : LieModel G ξ Li) (U : Submodule Ω Li) (z : Sp (𝓞 L) ⟶ X) {V : Type} [AddCommGroup V]
    [Module (𝓞 L) V] (MB : LieModel G z V) : Submodule (𝓞 L) V where
  carrier := {x | ∃ a : 𝓞 L, a ≠ 0 ∧ a • x ∈ Submodule.span (𝓞 L) (subGens M U z MB)}
  add_mem' := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hx
    · rw [mul_smul]; exact Submodule.smul_mem _ _ hy
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  smul_mem' := by
    rintro c x ⟨a, ha, hx⟩
    refine ⟨a, ha, ?_⟩
    rw [smul_comm]; exact Submodule.smul_mem _ _ hx

theorem mem_subFib {M : LieModel G ξ Li} {U : Submodule Ω Li} {z : Sp (𝓞 L) ⟶ X} {V : Type} [AddCommGroup V]
    [Module (𝓞 L) V] {MB : LieModel G z V} {x : V} :
    x ∈ subFib M U z MB ↔ ∃ a : 𝓞 L, a ≠ 0 ∧ a • x ∈ Submodule.span (𝓞 L) (subGens M U z MB) := Iff.rfl

theorem isSubFibre_subFib (M : LieModel G ξ Li) (U : Submodule Ω Li) (z : Sp (𝓞 L) ⟶ X) {V : Type} [AddCommGroup V]
    [Module (𝓞 L) V] (MB : LieModel G z V) : IsSubFibre M U z MB (subFib M U z MB) := fun _ => Iff.rfl

theorem subFib_mono (M : LieModel G ξ Li) {U U' : Submodule Ω Li} (h : U ≤ U') (z : Sp (𝓞 L) ⟶ X) {V : Type}
    [AddCommGroup V] [Module (𝓞 L) V] (MB : LieModel G z V) : subFib M U z MB ≤ subFib M U' z MB := by
  rintro x ⟨a, ha, hx⟩
  refine ⟨a, ha, Submodule.span_mono ?_ hx⟩
  rintro y ⟨e, he, r⟩
  exact ⟨e, h he, r⟩

theorem subFib_saturated (M : LieModel G ξ Li) (U : Submodule Ω Li) (z : Sp (𝓞 L) ⟶ X)
    (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel G z B.carrier) : B.Saturated (subFib M U z MB) := by
  rintro a x ha ⟨b, hb, hx⟩
  exact ⟨b * a, mul_ne_zero hb ha, by rwa [mul_smul]⟩

end GlobalTheory.CompanionTheory.Ar.FlagFib
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbBound
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.QuotUnif

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def AbBound {X : Scheme.{0}} (t : SAB H X) {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {Li : Type} [AddCommGroup Li] [Module Ω Li]
    {M : LieModel t.G ξ Li} {K : Type} {J : K → Type} {y : (Σ k, J k) → Ω} (h : LieMetric M y) (C : ℝ)
    (z : Sp ℂ ⟶ X) : Prop :=
  ∀ P : AbPart t z, IsPrincipal P.tB ∧ ∀ (v : epsAt (𝟙 (Sp ℂ)) ⟶ P.tK.G) (v₀ : epsAt z ⟶ t.G) (c : ℂ),
    IsTanAt _ _ v → v.left ≫ P.m.φ = v₀.left →
    HodgeIP P.tB.G P.tB.PP.L (𝟙 _) (v ≫ P.τ.q ≫ P.e.hom) (v ≫ P.τ.q ≫ P.e.hom) c → c.re ≤ C * (h.ip z v₀ v₀).re

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)}
  {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

def GoodPt (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X) : Prop :=
  ∃ τ : c.F →+* ℂ, z ≫ 𝔐.f ≫ Y.s = spMap (τ.comp (algebraMap (𝓞 c.F) c.F)) ∧
    (τ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0

end GlobalTheory.CompanionTheory.Ar.QuotUnif
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramLinearCombination
section -- merged from Development.WeilBound.CoreStatements.SesquilinearFractions.GGramComb
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf.HermitianFormSum

variable {S : Scheme.{0}}

theorem one_left (G : Over S) [GrpObj G] (Y : Over S) : (1 : Y ⟶ G).left = Y.hom ≫ (η[G] : 𝟙_ (Over S) ⟶ G).left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

theorem hermForm_sum {g n m : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a : Fin n → ℂ) (b : Fin m → ℂ)
    (W : Fin n → Fin g → ℂ) (W' : Fin m → Fin g → ℂ) :
    hermForm Hm (∑ i, a i • W i : Fin g → ℂ) (∑ j, b j • W' j : Fin g → ℂ) = ∑ i, ∑ j, a i * star (b j) * hermForm Hm (W i) (W' j) := by
  simp only [hermForm, dotProduct, mulVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.star_apply, star_sum,
    star_mul', Finset.mul_sum, Finset.sum_mul]
  have e1 : ∀ x x1, (∑ x_2 : Fin m, ∑ i : Fin n, a i * W i x * (Hm x x1 * (star (b x_2) * star (W' x_2 x1)))) =
      ∑ i : Fin n, ∑ x_2 : Fin m, a i * W i x * (Hm x x1 * (star (b x_2) * star (W' x_2 x1))) := fun x x1 => Finset.sum_comm
  simp only [e1]
  have e2 : ∀ x, (∑ x1 : Fin g, ∑ i : Fin n, ∑ x_2 : Fin m, a i * W i x * (Hm x x1 * (star (b x_2) * star (W' x_2 x1)))) =
      ∑ i : Fin n, ∑ x1 : Fin g, ∑ x_2 : Fin m, a i * W i x * (Hm x x1 * (star (b x_2) * star (W' x_2 x1))) := fun x => Finset.sum_comm
  simp only [e2]
  rw [Finset.sum_comm (f := fun (x : Fin g) (i : Fin n) => ∑ x1 : Fin g, ∑ x_2 : Fin m, a i * W i x * (Hm x x1 * (star (b x_2) * star (W' x_2 x1))))]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e3 : ∀ x, (∑ x1 : Fin g, ∑ x_2 : Fin m, a i * W i x * (Hm x x1 * (star (b x_2) * star (W' x_2 x1)))) =
      ∑ x_2 : Fin m, ∑ x1 : Fin g, a i * W i x * (Hm x x1 * (star (b x_2) * star (W' x_2 x1))) := fun x => Finset.sum_comm
  simp only [e3]
  rw [Finset.sum_comm (f := fun (x : Fin g) (x_2 : Fin m) => ∑ x1 : Fin g, a i * W i x * (Hm x x1 * (star (b x_2) * star (W' x_2 x1))))]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

end PositivityTheory.Xgf.HermitianFormSum

namespace PositivityTheory.Xgf

open PositivityTheory.Xgf.HermitianFormSum in
theorem hodge_gram_linear_combination : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (x : Sp ℂ ⟶ S) (n n' : ℕ) (v : Fin n → (epsAt x ⟶ G)) (v' : Fin n' → (epsAt x ⟶ G)) (Γ : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin n') (Fin n) ℂ), (∀ k, IsTanAt G x (v k)) → IsHodgeGram G L x v Γ → (∀ k, IsComb (A k) v (v' k)) → IsHodgeGram G L x v' (A * Γ * Aᴴ) := by
  intro S G _ L x n n' v v' Γ A hT hG hC
  obtain ⟨Q, ψ, v₁, u, Hm, χ, W, hPB, hLB, hAH, hv, hΓ⟩ := hG
  have hη : (η[Q.A] : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A).left ≫ ψ = x ≫ (η[G] : 𝟙_ (Over S) ⟶ G).left := by
    have hw : ((1 : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A).left ≫ ψ) ≫ G.hom = (Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ x)).hom := by
      rw [Category.assoc, hPB.1.w, ← Category.assoc, Over.w]
      rfl
    let a₀ : Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ x) ⟶ G := Over.homMk ((1 : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A).left ≫ ψ) hw
    have hm := hPB.2 (𝟙_ (Over (Sp ℂ))) 1 1 a₀ a₀ rfl rfl
    rw [_root_.mul_one] at hm
    have h1 : a₀ * a₀ = a₀ * 1 := by
      rw [_root_.mul_one]
      exact Over.OverMorphism.ext hm
    have h2 := congrArg (fun h => h.left) (mul_left_cancel h1)
    simp only [a₀, Over.homMk_left, one_left] at h2
    simpa using h2
  have hunit : ∀ T : Over (Sp ℂ), (1 : T ⟶ Q.A).left ≫ ψ = (1 : Over.mk (T.hom ≫ x) ⟶ G).left := by
    intro T
    rw [one_left, one_left, Category.assoc, hη]
    simp
  have hprod : ∀ (k : ℕ) (uu : Fin k → (epsR ℂ ⟶ Q.A)) (dd : Fin k → (epsAt x ⟶ G)),
      (∀ i, (dd i).left = (uu i).left ≫ ψ) → (List.ofFn dd).prod.left = (List.ofFn uu).prod.left ≫ ψ := by
    intro k
    induction k with
    | zero => intro uu dd _; simpa using (hunit (epsR ℂ)).symm
    | succ k ih =>
      intro uu dd h
      rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons]
      exact hPB.2 (epsR ℂ) _ _ _ _ (h 0) (ih _ _ fun i => h i.succ)
  have hsp : ∀ (c : ℂ), spMap (epsScaleR c) ≫ (epsR ℂ).hom = (epsR ℂ).hom := by
    intro c
    simp only [epsR, Over.mk_hom, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext z
    · simp [epsScaleR]
    · simp [epsScaleR]
  have htan : ∀ i, IsTangent (v₁ i) := by
    intro i
    apply hPB.1.hom_ext
    · rw [Category.assoc, (hv i).1, hT i, one_left, hη]
      rfl
    · rw [Category.assoc, Over.w, Over.w]
      simp only [epsR, Over.mk_hom, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have e : ((TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ := by
        ext z; simp
      erw [e, CommRingCat.ofHom_id, Spec.map_id]
      rfl
  choose u' hu' hv' using hC
  let uu : ∀ k, Fin n → (epsR ℂ ⟶ Q.A) := fun k i =>
    Over.homMk (spMap (epsScaleR (A k i)) ≫ (v₁ i).left) (by rw [Category.assoc, Over.w]; exact hsp _)
  refine ⟨Q, ψ, fun k => (List.ofFn (uu k)).prod, u, Hm, χ, fun k => ∑ i, A k i • W i, hPB, hLB, hAH,
    fun k => ⟨?_, ?_⟩, fun k l => ?_⟩
  · rw [hv' k]
    exact (hprod n (uu k) (u' k) fun i => by
      rw [hu' k i]
      show _ = (spMap (epsScaleR (A k i)) ≫ (v₁ i).left) ≫ ψ
      rw [Category.assoc, (hv i).1]
      rfl).symm
  · exact GlobalTheory.isDiff_sum_smul_of_isLieComb Q.A Q.isAb Q.L Q.g n u v₁ W (A k) _ htan (fun i => (hv i).2)
      ⟨uu k, fun i => rfl, rfl⟩
  · rw [hermForm_sum]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hΓ, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [RCLike.star_def]
    ring

end PositivityTheory.Xgf
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramLinearCombination
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.hodge_gram_linear_combination : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (x : Sp ℂ ⟶ S) (n n' : ℕ) (v : Fin n → (epsAt x ⟶ G)) (v' : Fin n' → (epsAt x ⟶ G)) (Γ : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin n') (Fin n) ℂ), (∀ k, IsTanAt G x (v k)) → IsHodgeGram G L x v Γ → (∀ k, IsComb (A k) v (v' k)) → IsHodgeGram G L x v' (A * Γ * Aᴴ) := by
  first | exact @PositivityTheory.Xgf.hodge_gram_linear_combination | exact PositivityTheory.Xgf.hodge_gram_linear_combination
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramLinearCombinationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_gram_linear_combination : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (x : Sp ℂ ⟶ S) (n n' : ℕ) (v : Fin n → (epsAt x ⟶ G)) (v' : Fin n' → (epsAt x ⟶ G)) (Γ : Matrix (Fin n) (Fin n) ℂ) (A : Matrix (Fin n') (Fin n) ℂ), (∀ k, IsTanAt G x (v k)) → IsHodgeGram G L x v Γ → (∀ k, IsComb (A k) v (v' k)) → IsHodgeGram G L x v' (A * Γ * Aᴴ) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.hodge_gram_linear_combination | exact GlobalTheory.CompanionTheory.Relay.hodge_gram_linear_combination | (intros; apply GlobalTheory.CompanionTheory.Relay.hodge_gram_linear_combination <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldPointIntegralModel
section -- merged from Development.WeilBound.CoreStatements.AmpleLineBundles.ExistsIntegralPointWithCoordinates
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CoverDenseAlt

namespace PtExt

variable {R L : Type} [CommRing R] [IsDedekindDomain R] [Field L] [Algebra R L] [IsFractionRing R L]

theorem valRing (P : Ideal R) [P.IsPrime] : ValuationRing (Localization.AtPrime P) := by
  by_cases hP : P = ⊥
  · have hF : IsField (Localization.AtPrime P) := by
      rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal]
      exact (congrArg (Ideal.map _) hP).trans Ideal.map_bot
    let := hF.toField
    exact ValuationRing.of_field _
  · have := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hP (Localization.AtPrime P)
    infer_instance

theorem local_ext {Y : Scheme.{0}} (s : Y ⟶ Spec (CommRingCat.of ℤ)) [IsProper s] (zL : Sp L ⟶ Y) (x : Sp R) :
    ∃ (W : (Sp R).Opens) (h : W.toScheme ⟶ Y), x ∈ W ∧
      ∀ u : Sp L ⟶ W.toScheme, u ≫ W.ι = spMap (algebraMap R L) → u ≫ h = zL := by
  have : x.asIdeal.IsPrime := PrimeSpectrum.isPrime x
  let T := Localization.AtPrime x.asIdeal
  have hu : ∀ y : x.asIdeal.primeCompl, IsUnit (algebraMap R L y) := fun y => by
    refine IsUnit.mk0 _ fun h0 => y.2 ?_
    have : (y : R) = 0 := IsFractionRing.injective R L (by rw [h0, map_zero])
    rw [this]
    exact x.asIdeal.zero_mem
  let : Algebra T L := (IsLocalization.lift (S := T) hu).toAlgebra
  have : IsScalarTower R T L := IsScalarTower.of_algebraMap_eq fun r => (IsLocalization.lift_eq hu r).symm
  have : IsFractionRing T L := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization x.asIdeal.primeCompl T L
  have : ValuationRing T := valRing x.asIdeal
  have hE : ValuativeCriterion.Existence s :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed s) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) s).1
  obtain ⟨⟨l⟩⟩ := hE
    { R := T, K := L, i₁ := zL, i₂ := specZIsTerminal.from _, commSq := ⟨specZIsTerminal.hom_ext _ _⟩ }
  have hl : spMap (algebraMap T L) ≫ l.l = zL := l.fac_left
  let e := Spec.stalkIso (CommRingCat.of R) x
  obtain ⟨U, hxU, f, h₁, -⟩ := spread_out_of_isGermInjective' (specZIsTerminal.from (Sp R)) s
    (x := x) (Spec.map e.inv ≫ l.l) (specZIsTerminal.hom_ext _ _)
  refine ⟨U, f, hxU, fun u hu' => ?_⟩
  have e1 : u = spMap (algebraMap T L) ≫ Spec.map e.hom ≫ U.fromSpecStalkOfMem x hxU := by
    rw [← cancel_mono U.ι, hu', Category.assoc, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      Spec.fromSpecStalk_eq, ← Spec.algebraMap_stalkIso_inv, ← Spec.map_comp, ← Spec.map_comp]
    have h2 : (CommRingCat.ofHom (algebraMap R T) ≫ e.inv) ≫ e.hom = CommRingCat.ofHom (algebraMap R T) := by
      rw [Category.assoc, e.inv_hom_id, Category.comp_id]
    refine congrArg Spec.map (Eq.symm ((congrArg (· ≫ CommRingCat.ofHom (algebraMap T L)) h2).trans ?_))
    ext r
    exact (IsScalarTower.algebraMap_apply R T L r).symm
  rw [e1, Category.assoc, Category.assoc, ← h₁, ← Spec.map_comp_assoc e.inv, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp, hl]

theorem ext_dedekind {Y : Scheme.{0}} (s : Y ⟶ Spec (CommRingCat.of ℤ)) [IsProper s] (zL : Sp L ⟶ Y) :
    ∃ z : Sp R ⟶ Y, spMap (algebraMap R L) ≫ z = zL := by
  choose W h hz hξ using fun x : Sp R => local_ext s zL x
  let gp : Sp L ⟶ Sp R := spMap (algebraMap R L)
  have hpt : ∀ y : Sp L, ∀ q : Sp R, gp y ⤳ q := by
    intro y q
    have h0 : (gp y).asIdeal = ⊥ := by
      have : y.asIdeal.IsPrime := PrimeSpectrum.isPrime y
      change Ideal.comap (algebraMap R L) y.asIdeal = ⊥
      rw [(Ideal.eq_bot_of_prime y.asIdeal), Ideal.comap_bot_of_injective _ (IsFractionRing.injective R L)]
    exact (PrimeSpectrum.le_iff_specializes _ _).1 (by
      change (gp y).asIdeal ≤ q.asIdeal
      rw [h0]; exact bot_le)
  have hd : IsDominant gp := ⟨fun q => by
    have := specializes_iff_mem_closure.1 (hpt (IsLocalRing.closedPoint L) q)
    exact closure_mono (Set.singleton_subset_iff.2 (Set.mem_range_self (f := gp) _)) this⟩
  have hx : ∀ z, ∃ x : Sp L ⟶ (W z).toScheme, x ≫ (W z).ι = gp := fun z =>
    ⟨_, IsOpenImmersion.lift_fac (W z).ι gp (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (hpt y z).mem_open (W z).2 (hz z))⟩
  choose x hx using hx
  have hW : TopologicalSpace.IsOpenCover W :=
    top_unique fun z _ => TopologicalSpace.Opens.mem_iSup.2 ⟨z, hz z⟩
  let 𝒰 := (Sp R).openCoverOfIsOpenCover W hW
  have hc : ∀ a b, pullback.fst (W a).ι (W b).ι ≫ h a = pullback.snd (W a).ι (W b).ι ≫ h b := by
    intro a b
    let m : Sp L ⟶ pullback (W a).ι (W b).ι := pullback.lift (x a) (x b) ((hx a).trans (hx b).symm)
    have e : m ≫ pullback.fst _ _ ≫ (W a).ι = gp := by rw [pullback.lift_fst_assoc, hx]
    have : IsDominant (m ≫ pullback.fst _ _ ≫ (W a).ι) := e ▸ hd
    have : IsDominant m := .of_comp_of_isOpenImmersion m (pullback.fst _ _ ≫ (W a).ι)
    have : IsReduced (pullback (W a).ι (W b).ι) := isReduced_of_isOpenImmersion (pullback.fst _ _ ≫ (W a).ι)
    refine ext_of_isDominant_of_isSeparated s (specZIsTerminal.hom_ext _ _) m ?_
    rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, hξ _ _ (hx a), hξ _ _ (hx b)]
  have he : ∀ a, (W a).ι ≫ 𝒰.glueMorphisms h hc = h a := fun a => 𝒰.ι_glueMorphisms h hc a
  let a := gp (IsLocalRing.closedPoint L)
  refine ⟨𝒰.glueMorphisms h hc, ?_⟩
  change gp ≫ _ = _
  rw [← hx a, Category.assoc, he, hξ _ _ (hx _)]

end PtExt

theorem exists_integral_point_with_coordinates : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ Small.ptsOver L (mCoordIdeal y), ∃ z : Sp (𝓞 L) ⟶ X, CoordsAt ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w := by
  classical
  intro X Ω _ K _ J _ y ξ _ hall tie L _ _ w hw
  obtain ⟨zL, ⟨-, hz⟩, -⟩ := (GlobalTheory.T.local_ring_points_existsUnique X Ω ξ K J y tie L).1 w
    (fun k => (hw.1 k).imp fun _ h => isUnit_iff_ne_zero.mpr h) hw.2
  obtain ⟨s, h1, h2, -⟩ := GlobalTheory.T.finite_type_over_integers_model X Ω ξ _ _ hall tie
  have := GlobalTheory.CompanionTheory.Ar.Flat.LocModel.isProper_of_coordTie hall tie s
  obtain ⟨z, hz'⟩ := PtExt.ext_dedekind (R := 𝓞 L) s zL
  exact ⟨z, hz' ▸ hz⟩

end CoverDenseAlt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldPointIntegralModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem algebraicPoint_extends_to_integers : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ Small.ptsOver L (mCoordIdeal y), ∃ z : Sp (𝓞 L) ⟶ X, CoordsAt ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w :=
  @CoverDenseAlt.exists_integral_point_with_coordinates

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldPointIntegralModelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.number_field_point_integral_model : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ Small.ptsOver L (mCoordIdeal y), ∃ z : Sp (𝓞 L) ⟶ X, CoordsAt ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.algebraicPoint_extends_to_integers | exact GlobalTheory.CompanionTheory.Ar.algebraicPoint_extends_to_integers | (intros; apply GlobalTheory.CompanionTheory.Ar.algebraicPoint_extends_to_integers <;> assumption)
end
end
