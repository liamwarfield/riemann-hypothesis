module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalSquaringPathWithTangentVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HformZeroRight

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTangentOfSingleAffineChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTangentOfSingleAffineChart
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef.TanLoc

theorem ev_congr {R : Type} [CommRing R] {X : Scheme.{0}} {b b' : Sp R ⟶ X} (e : b = b') {U : X.Opens}
    (h : ⊤ ≤ b ⁻¹ᵁ U) (h' : ⊤ ≤ b' ⁻¹ᵁ U) (f : Γ(X, U)) : evAt b h f = evAt b' h' f := by
  subst e; rfl

theorem coeff_one_mul {E : Type} [CommRing E] (P Q : PowerSeries E) :
    PowerSeries.coeff 1 (P * Q) = PowerSeries.constantCoeff (R := E) P * PowerSeries.coeff 1 Q +
      PowerSeries.constantCoeff (R := E) Q * PowerSeries.coeff 1 P := by
  rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ]
  simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  ring

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] {E : Type} [CommRing E] (b : Sp E ⟶ S) {n : ℕ}
  {V : S.Opens} (τ : Fin n → Γ(Lie G, V)) (w : Fin n → E)

theorem rhs_res {Ua Ub : G.left.Opens} (k : Ub ≤ Ua) {Va Vb : S.Opens} (hVa : Va ≤ V) (hVb : Vb ≤ V)
    (hab : Vb ≤ Va) (hea : Va ≤ unitSec G ⁻¹ᵁ Ua) (heb : Vb ≤ unitSec G ⁻¹ᵁ Ub) (hba : ⊤ ≤ b ⁻¹ᵁ Va)
    (hbb : ⊤ ≤ b ⁻¹ᵁ Vb) (g : Γ(G.left, Ua)) :
    ∑ i, w i * evAt b hbb (dualApp (τ i) hVb (dUnit G heb (G.left.presheaf.map (homOfLE k).op g))) =
      ∑ i, w i * evAt b hba (dualApp (τ i) hVa (dUnit G hea g)) := by
  obtain ⟨-, -, ev_res, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have h1 : dUnit G heb (G.left.presheaf.map (homOfLE k).op g) = resM _ hab (dUnit G hea g) := by
    rw [resM_dUnit]; exact dUnit_resG G heb k g
  rw [h1]
  have h2 := dualApp_resM (τ i) hVa hab (dUnit G hea g)
  rw [h2]
  exact ev_res E S b Va Vb hab hba hbb _

theorem rhs_mul (ξ : Sp (PowerSeries E) ⟶ G.left)
    (hz : spMap (PowerSeries.constantCoeff (R := E)) ≫ ξ = b ≫ unitSec G) {U₂ : G.left.Opens}
    (hU₂ : ⊤ ≤ ξ ⁻¹ᵁ U₂) {V₂ : S.Opens} (hV₂ : V₂ ≤ V) (he₂ : V₂ ≤ unitSec G ⁻¹ᵁ U₂)
    (hb₂ : ⊤ ≤ b ⁻¹ᵁ V₂) (g k : Γ(G.left, U₂)) :
    ∑ i, w i * evAt b hb₂ (dualApp (τ i) hV₂ (dUnit G he₂ (g * k))) =
      PowerSeries.constantCoeff (R := E) (evAt ξ hU₂ g) * ∑ i, w i * evAt b hb₂ (dualApp (τ i) hV₂ (dUnit G he₂ k)) +
      PowerSeries.constantCoeff (R := E) (evAt ξ hU₂ k) * ∑ i, w i * evAt b hb₂ (dualApp (τ i) hV₂ (dUnit G he₂ g)) := by
  obtain ⟨ev_map, ev_comp, -, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk
  have hc : ⊤ ≤ (b ≫ unitSec G) ⁻¹ᵁ U₂ := by
    intro x _
    show (b ≫ unitSec G) x ∈ U₂
    rw [← hz, Scheme.Hom.comp_apply]
    exact hU₂ (show _ ∈ (⊤ : (Sp (PowerSeries E)).Opens) from trivial)
  have hc' : ⊤ ≤ (spMap (PowerSeries.constantCoeff (R := E)) ≫ ξ) ⁻¹ᵁ U₂ := hz ▸ hc
  have hε : ∀ f : Γ(G.left, U₂), evAt b hb₂ ((unitSec G).appLE U₂ V₂ he₂ f) =
      PowerSeries.constantCoeff (R := E) (evAt ξ hU₂ f) := by
    intro f
    rw [← ev_comp E S G.left b (unitSec G) V₂ U₂ hb₂ hc he₂ f, ← ev_congr hz hc' hc,
      ev_map (PowerSeries E) E G.left (PowerSeries.constantCoeff (R := E)) ξ U₂ hU₂ hc' f]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dUnit_mul, map_add (f := _), LinearMap.map_smul, LinearMap.map_smul, smul_eq_mul, smul_eq_mul, map_add (f := _),
    map_mul, map_mul, hε, hε]
  ring

end GlobalTheory.Nef.TanLoc

namespace GlobalTheory.Nef


open TanLoc in
theorem hasTan_of_affine_chart : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (E : Type) [Field E] (c : E) (b : Sp E ⟶ S) (ξ : Sp (PowerSeries E) ⟶ G.left), IsPath G c b ξ → ∀ (n : ℕ) (V : S.Opens) (τ : Fin n → Γ(Lie G, V)) (w : Fin n → E) (U : G.left.Opens), IsAffineOpen U → ∀ (hU : ⊤ ≤ ξ ⁻¹ᵁ U) (V' : S.Opens) (hV : V' ≤ V) (he : V' ≤ unitSec G ⁻¹ᵁ U) (hb : ⊤ ≤ b ⁻¹ᵁ V'), (∀ f : Γ(G.left, U), PowerSeries.coeff 1 (evAt ξ hU f) = ∑ i, w i * evAt b hb (dualApp (τ i) hV (dUnit G he f))) → HasTan G b ξ τ w := by
  intro S G _ E _ c b ξ hξ n V τ w U hUa hU V' hV he hb H U₁ hU₁ V₁ hV₁ he₁ hb₁ f₁
  obtain ⟨-, -, ev_res, ev_loc, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk
  have hyU := (ev_loc (PowerSeries E) G.left ξ U).1 hU
  have hyU₁ := (ev_loc (PowerSeries E) G.left ξ U₁).1 hU₁
  obtain ⟨t, htle, hyt⟩ := hUa.exists_basicOpen_le ⟨_, hyU₁⟩ hyU
  have hk : G.left.basicOpen t ≤ U := G.left.basicOpen_le t
  have hU₂ : ⊤ ≤ ξ ⁻¹ᵁ G.left.basicOpen t := (ev_loc (PowerSeries E) G.left ξ _).2 hyt
  have hV₂ : V' ⊓ V₁ ⊓ unitSec G ⁻¹ᵁ G.left.basicOpen t ≤ V := inf_le_left.trans (inf_le_left.trans hV)
  have he₂ : V' ⊓ V₁ ⊓ unitSec G ⁻¹ᵁ G.left.basicOpen t ≤ unitSec G ⁻¹ᵁ G.left.basicOpen t := inf_le_right
  have hb₂ : ⊤ ≤ b ⁻¹ᵁ (V' ⊓ V₁ ⊓ unitSec G ⁻¹ᵁ G.left.basicOpen t) := by
    intro x hx
    refine ⟨⟨hb hx, hb₁ hx⟩, ?_⟩
    show unitSec G (b x) ∈ G.left.basicOpen t
    rw [← Scheme.Hom.comp_apply, ← hξ.zero, Scheme.Hom.comp_apply]
    exact hU₂ (show _ ∈ (⊤ : (Sp (PowerSeries E)).Opens) from trivial)
  set L₂ : Γ(G.left, G.left.basicOpen t) → E := fun g => PowerSeries.coeff 1 (evAt ξ hU₂ g) with hL₂
  set R₂ : Γ(G.left, G.left.basicOpen t) → E :=
    fun g => ∑ i, w i * evAt b hb₂ (dualApp (τ i) hV₂ (dUnit G he₂ g)) with hR₂
  set ε : Γ(G.left, G.left.basicOpen t) →+* E := (PowerSeries.constantCoeff (R := E)).comp (evAt ξ hU₂) with hε
  have Lmul : ∀ g k, L₂ (g * k) = ε g * L₂ k + ε k * L₂ g := fun g k => by
    simp only [hL₂, hε, RingHom.comp_apply, map_mul, coeff_one_mul]
  have Rmul : ∀ g k, R₂ (g * k) = ε g * R₂ k + ε k * R₂ g := fun g k =>
    rhs_mul G b τ w ξ hξ.zero hU₂ hV₂ he₂ hb₂ g k
  have hA : ∀ g : Γ(G.left, U), L₂ (G.left.presheaf.map (homOfLE hk).op g) =
      R₂ (G.left.presheaf.map (homOfLE hk).op g) := by
    intro g
    simp only [hL₂, hR₂]
    rw [ev_res (PowerSeries E) G.left ξ U _ hk hU hU₂, H g,
      rhs_res G b τ w hk hV hV₂ (inf_le_left.trans inf_le_left) he he₂ hb hb₂ g]
  have hk₁ : G.left.basicOpen t ≤ U₁ := htle
  have hB : L₂ (G.left.presheaf.map (homOfLE hk₁).op f₁) = PowerSeries.coeff 1 (evAt ξ hU₁ f₁) ∧
      R₂ (G.left.presheaf.map (homOfLE hk₁).op f₁) =
        ∑ i, w i * evAt b hb₁ (dualApp (τ i) hV₁ (dUnit G he₁ f₁)) := by
    refine ⟨?_, ?_⟩
    · simp only [hL₂]; rw [ev_res (PowerSeries E) G.left ξ U₁ _ hk₁ hU₁ hU₂]
    · exact rhs_res G b τ w hk₁ hV₁ hV₂ (inf_le_left.trans inf_le_right) he₁ he₂ hb₁ hb₂ f₁
  rw [← hB.1, ← hB.2]
  have hl := hUa.isLocalization_basicOpen t
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers t) (G.left.presheaf.map (homOfLE hk₁).op f₁)
  have hunit : IsUnit (algebraMap Γ(G.left, U) Γ(G.left, G.left.basicOpen t) (s : Γ(G.left, U))) :=
    IsLocalization.map_units _ s
  have hs' : algebraMap Γ(G.left, U) Γ(G.left, G.left.basicOpen t) = (G.left.presheaf.map (homOfLE hk).op).hom := rfl
  rw [hs'] at hs hunit
  have key := congrArg (fun z => L₂ z - R₂ z) hs
  simp only at key
  rw [Lmul, Rmul, hA a, hA s, sub_self] at key
  have hne : ε ((G.left.presheaf.map (homOfLE hk).op).hom s) ≠ 0 := (hunit.map ε).ne_zero
  have : ε ((G.left.presheaf.map (homOfLE hk).op).hom s) *
      (L₂ (G.left.presheaf.map (homOfLE hk₁).op f₁) - R₂ (G.left.presheaf.map (homOfLE hk₁).op f₁)) = 0 := by
    rw [← key]; ring
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hne)

end GlobalTheory.Nef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTangentOfSingleAffineChartStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasTangent_of_single_affineChart : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (E : Type) [Field E] (c : E) (b : Sp E ⟶ S) (ξ : Sp (PowerSeries E) ⟶ G.left), IsPath G c b ξ → ∀ (n : ℕ) (V : S.Opens) (τ : Fin n → Γ(Lie G, V)) (w : Fin n → E) (U : G.left.Opens), IsAffineOpen U → ∀ (hU : ⊤ ≤ ξ ⁻¹ᵁ U) (V' : S.Opens) (hV : V' ≤ V) (he : V' ≤ unitSec G ⁻¹ᵁ U) (hb : ⊤ ≤ b ⁻¹ᵁ V'), (∀ f : Γ(G.left, U), PowerSeries.coeff 1 (evAt ξ hU f) = ∑ i, w i * evAt b hb (dualApp (τ i) hV (dUnit G he f))) → HasTan G b ξ τ w := by
  first | exact @GlobalTheory.Nef.hasTan_of_affine_chart | exact GlobalTheory.Nef.hasTan_of_affine_chart | (intros; apply GlobalTheory.Nef.hasTan_of_affine_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFormalPathEqScalingValuationRingPath
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

private theorem top_le_comp_preimage {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) {U : Z.Opens} (h : ⊤ ≤ g ⁻¹ᵁ U) :
    ⊤ ≤ (f ≫ g) ⁻¹ᵁ U := by
  rw [Scheme.Hom.comp_preimage, top_le_iff.1 h, Scheme.Hom.preimage_top]

private theorem top_le_of_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) {U : Z.Opens} (h : ⊤ ≤ (f ≫ g) ⁻¹ᵁ U) :
    ⊤ ≤ f ⁻¹ᵁ (g ⁻¹ᵁ U) := by
  rwa [Scheme.Hom.comp_preimage] at h

private theorem top_le_preimage_inf {X Y : Scheme.{0}} (f : X ⟶ Y) {A B : Y.Opens} (hA : ⊤ ≤ f ⁻¹ᵁ A)
    (hB : ⊤ ≤ f ⁻¹ᵁ B) : ⊤ ≤ f ⁻¹ᵁ (A ⊓ B) :=
  fun y _ => ⟨hA trivial, hB trivial⟩

private theorem evAt_congr {R : Type} [CommRing R] {X : Scheme.{0}} {ξ ξ' : Sp R ⟶ X} (e : ξ = ξ') {U : X.Opens}
    (h : ⊤ ≤ ξ ⁻¹ᵁ U) (h' : ⊤ ≤ ξ' ⁻¹ᵁ U) : evAt ξ h = evAt ξ' h' := by
  subst e; rfl

private def resO {k K E : Type} [Field k] [Field K] [Algebra k K] [Field E] [Algebra k E] [Algebra K E]
    {ρ : Place k E → Place k K} (hρ : IsRes ρ) (p : Place k E) : (ρ p).O →+* p.O :=
  ((algebraMap K E).comp (ρ p).O.subtype).codRestrict p.O fun y =>
    (Valuation.mem_valuationSubring_iff _ _).2 ((hρ p y).2 ((Valuation.mem_valuationSubring_iff _ _).1 y.2))

private def constO {k E : Type} [Field k] [Field E] [Algebra k E] (p : Place k E) : k →+* p.O :=
  (algebraMap k E).codRestrict p.O fun c => by
    rw [Valuation.mem_valuationSubring_iff]
    by_cases hc : c = 0
    · simp [hc]
    · exact (p.2.2 c hc).le

theorem genPath_scaling : ∀ (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E] [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → ∀ (W : C.Modules) (r : ℕ) (i : W ⟶ Lie G) (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)) (ρ : Place k E → Place k K), IsRes ρ → ∀ (p : Place k E) (g : Matrix (Fin r) (Fin r) K), LocFrame x s (ρ p) g → ∀ (w : Fin r → E) (u : E), u ≠ 0 → p.1 u = nrm p ((g.map (algebraMap K E)).mulVec w) → ∀ ξ, IsPath G 2 (spMap (algebraMap K E) ≫ x) ξ → HasTan G (spMap (algebraMap K E) ≫ x) ξ (fun j => i.app V₀ (s j)) w → ∃ (b : Sp p.O ⟶ C) (ζ : Sp (PowerSeries p.O) ⟶ G.left), spMap p.O.subtype ≫ b = spMap (algebraMap K E) ≫ x ∧ IsPath G 2 b ζ ∧ ξ = spMap (sc p u) ≫ ζ := by
  intro k K E _ _ _ _ _ _ _ _ _ _ C _ x _ G _ hG W r i V₀ s ρ hρ p g hg w u hu hpu ξ hξ hξt
  have hsm : Smooth G.hom := hG.smooth
  have hqs : QuasiSeparated G.hom := by haveI := hG.separated; infer_instance
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap k E).injective
  obtain ⟨b₀, V, t, Vf, h₀, h₁, hxf, M, hb₀, hb₀V, -, hst, rfl⟩ := hg
  set xE := spMap (algebraMap K E) ≫ x with hxE
  let α := resO hρ p
  let φ : p.O →+* E := p.O.subtype
  let b : Sp p.O ⟶ C := spMap α ≫ b₀
  have hbx : spMap φ ≫ b = xE := by
    rw [hxE, ← hb₀]
    simp only [b, ← Category.assoc, spMap, ← Spec.map_comp]
    rfl
  letI : Algebra ℚ p.O := ((constO p).comp (algebraMap ℚ k)).toAlgebra
  have hbV : ⊤ ≤ b ⁻¹ᵁ V := top_le_comp_preimage _ _ hb₀V
  let y : Fin r → E := ((M.map (evAt x hxf)).map (algebraMap K E)).mulVec w
  let eE : Fin r → E := fun j => u⁻¹ * y j
  have heO : ∀ j, eE j ∈ p.O := by
    intro j
    rw [Valuation.mem_valuationSubring_iff]
    have hle : p.1 (y j) ≤ p.1 u := by
      rw [hpu, nrm]; exact Finset.le_sup (f := fun i => p.1 (y i)) (Finset.mem_univ j)
    have hu0 : p.1 u ≠ 0 := (Valuation.ne_zero_iff _).2 hu
    calc p.1 (eE j) = (p.1 u)⁻¹ * p.1 (y j) := by simp only [eE, map_mul, map_inv₀]
      _ ≤ (p.1 u)⁻¹ * p.1 u := by gcongr
      _ = 1 := inv_mul_cancel₀ hu0
  let e : Fin r → p.O := fun j => ⟨eE j, heO j⟩
  obtain ⟨ζ, hζ, hζt⟩ := GlobalTheory.T.exists_formalSquaringPath_with_tangentVector C G p.O hsm hqs b r V (fun j => i.app V (t j)) e hbV
  obtain ⟨U₀, hU₀a, hζU₀, -⟩ := Opens.isBasis_iff_nbhd.1 G.left.isBasis_affineOpens
    (Opens.mem_top (ζ (IsLocalRing.closedPoint (PowerSeries p.O))))
  have hζU : ⊤ ≤ ζ ⁻¹ᵁ U₀ := (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.2.2.2.1 (PowerSeries p.O) G.left ζ U₀).2 hζU₀
  have hξ'U : ⊤ ≤ (spMap (sc p u) ≫ ζ) ⁻¹ᵁ U₀ := top_le_comp_preimage _ _ hζU
  have hξ'path : IsPath G 2 xE (spMap (sc p u) ≫ ζ) := by
    have := (GlobalTheory.T.formalSquaringPaths_baseChange_and_hom.1 C G p.O E φ 2 u b ζ hζ).1
    rw [map_ofNat, hbx] at this
    exact this

  have hxEf : ⊤ ≤ xE ⁻¹ᵁ Vf := top_le_comp_preimage _ _ hxf
  have hxE0 : ⊤ ≤ xE ⁻¹ᵁ V₀ := hxEf.trans (Scheme.Hom.preimage_mono xE h₀)
  have hxEu : ⊤ ≤ xE ⁻¹ᵁ (unitSec G ⁻¹ᵁ U₀) := by
    apply top_le_of_comp
    rw [← hξ'path.zero]; exact top_le_comp_preimage _ _ hξ'U
  have hbu : ⊤ ≤ b ⁻¹ᵁ (unitSec G ⁻¹ᵁ U₀) := by
    apply top_le_of_comp
    rw [← hζ.zero]; exact top_le_comp_preimage _ _ hζU
  have hxs : ⊤ ≤ xE ⁻¹ᵁ (Vf ⊓ unitSec G ⁻¹ᵁ U₀) := top_le_preimage_inf _ hxEf hxEu
  have hb'' : ⊤ ≤ b ⁻¹ᵁ (V ⊓ unitSec G ⁻¹ᵁ U₀) := top_le_preimage_inf _ hbV hbu
  have hxE'' : ⊤ ≤ xE ⁻¹ᵁ (V ⊓ unitSec G ⁻¹ᵁ U₀) := by rw [← hbx]; exact top_le_comp_preimage _ _ hb''
  have hsub : Vf ⊓ unitSec G ⁻¹ᵁ U₀ ≤ V ⊓ unitSec G ⁻¹ᵁ U₀ := inf_le_inf_right _ h₁
  have key : ∀ f : Γ(G.left, U₀), PowerSeries.coeff 1 (evAt (spMap (sc p u) ≫ ζ) hξ'U f) =
      ∑ j, w j * evAt xE hxs (dualApp (i.app V₀ (s j)) (inf_le_left.trans h₀) (dUnit G inf_le_right f)) := by
    intro f
    have h1 := (GlobalTheory.T.formalSquaringPaths_baseChange_and_hom.1 C G p.O E φ 2 u b ζ hζ).2 r V (fun j => i.app V (t j)) e hbV U₀ hζU hζt hξ'U
      (V ⊓ unitSec G ⁻¹ᵁ U₀) inf_le_left inf_le_right hb'' f
    have hD : ∀ τ : Γ(Lie G, V), φ (evAt b hb'' (dualApp τ inf_le_left (dUnit G inf_le_right f))) =
        evAt xE hxs (dualApp τ (hsub.trans inf_le_left) (dUnit G (hsub.trans inf_le_right) f)) := by
      intro τ
      rw [← GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.1 p.O E C φ b _ hb'' (top_le_comp_preimage _ _ hb''), evAt_congr hbx _ hxE'',
        ← GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.2.2.1 E C xE _ _ hsub hxE'' hxs]
      congr 1
      have := dualApp_resM τ (inf_le_left : V ⊓ unitSec G ⁻¹ᵁ U₀ ≤ V) hsub (dUnit G inf_le_right f)
      rw [resM_dUnit] at this
      exact this.symm
    have hR : ∀ j, evAt xE hxs (dualApp (i.app V₀ (s j)) (inf_le_left.trans h₀) (dUnit G inf_le_right f)) =
        ∑ l, algebraMap K E (evAt x hxf (M l j)) * evAt xE hxs (dualApp (i.app V (t l))
          (hsub.trans inf_le_left) (dUnit G (hsub.trans inf_le_right) f)) := by
      intro j
      have e1 : dualApp (i.app V₀ (s j)) (inf_le_left.trans h₀) =
          dualApp (resM _ h₀ (i.app V₀ (s j))) (inf_le_left : Vf ⊓ unitSec G ⁻¹ᵁ U₀ ≤ Vf) :=
        (dualApp_res _ _ _).symm
      have e2 : resM _ h₀ (i.app V₀ (s j)) = ∑ l, M l j • resM _ h₁ (i.app V (t l)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← GlobalTheory.Twist.app_resM, hst, map_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Scheme.Modules.Hom.app_smul, GlobalTheory.Twist.app_resM]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [e1, e2, dualApp_sum, LinearMap.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [dualApp_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, dualApp_res]
      congr 1
      exact (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.2.2.1 E C xE Vf _ inf_le_left hxEf hxs (M l j)).trans
        (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.1 K E C (algebraMap K E) x Vf hxf hxEf (M l j))
    have he' : ∀ l, u * φ (e l) = ∑ j, algebraMap K E (evAt x hxf (M l j)) * w j := by
      intro l
      show u * (u⁻¹ * y l) = _
      rw [← _root_.mul_assoc, mul_inv_cancel₀ hu, _root_.one_mul]
      simp [y, Matrix.mulVec, dotProduct]
    refine Eq.trans h1 ?_
    simp only [hD, hR, he', Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have htan' : HasTan G xE (spMap (sc p u) ≫ ζ) (fun j => i.app V₀ (s j)) w :=
    GlobalTheory.T.hasTangent_of_single_affineChart C G E 2 xE _ hξ'path r V₀ _ w U₀ hU₀a hξ'U _ (inf_le_left.trans h₀) inf_le_right hxs key
  have hunit : ∀ j, 2 ≤ j → IsUnit ((2 : E) ^ j - 2) := by
    intro j hj
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    have h4 : 4 ≤ 2 ^ j := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
    have hc : ((2 ^ j - 2 : ℕ) : E) = 0 := by
      rw [Nat.cast_sub (by omega : 2 ≤ 2 ^ j)]; push_cast; exact h0
    rw [Nat.cast_eq_zero] at hc
    omega
  have heq : ξ = spMap (sc p u) ≫ ζ := by
    refine GlobalTheory.T.formalSquaringPath_unique_of_agree_low_degrees C G E hqs 2 2 (by norm_num) hunit xE ξ _ hξ hξ'path ?_
    intro U h h' f j hj0 hj2
    obtain rfl : j = 1 := by omega
    have hb3 : ⊤ ≤ xE ⁻¹ᵁ (V₀ ⊓ unitSec G ⁻¹ᵁ U) := by
      refine top_le_preimage_inf _ hxE0 ?_
      apply top_le_of_comp
      rw [← hξ.zero]; exact top_le_comp_preimage _ _ h
    rw [hξt U h _ inf_le_left inf_le_right hb3 f, htan' U h' _ inf_le_left inf_le_right hb3 f]
  exact ⟨b, ζ, hbx, hζ, heq⟩

end GlobalTheory.Nef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFormalPathEqScalingValuationRingPathStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFormalPath_eq_scaling_valuationRingPath : ∀ (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E] [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → ∀ (W : C.Modules) (r : ℕ) (i : W ⟶ Lie G) (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)) (ρ : Place k E → Place k K), IsRes ρ → ∀ (p : Place k E) (g : Matrix (Fin r) (Fin r) K), LocFrame x s (ρ p) g → ∀ (w : Fin r → E) (u : E), u ≠ 0 → p.1 u = nrm p ((g.map (algebraMap K E)).mulVec w) → ∀ ξ, IsPath G 2 (spMap (algebraMap K E) ≫ x) ξ → HasTan G (spMap (algebraMap K E) ≫ x) ξ (fun j => i.app V₀ (s j)) w → ∃ (b : Sp p.O ⟶ C) (ζ : Sp (PowerSeries p.O) ⟶ G.left), spMap p.O.subtype ≫ b = spMap (algebraMap K E) ≫ x ∧ IsPath G 2 b ζ ∧ ξ = spMap (sc p u) ≫ ζ := by
  first | exact @GlobalTheory.Nef.genPath_scaling | exact GlobalTheory.Nef.genPath_scaling | (intros; apply GlobalTheory.Nef.genPath_scaling <;> assumption)
end
