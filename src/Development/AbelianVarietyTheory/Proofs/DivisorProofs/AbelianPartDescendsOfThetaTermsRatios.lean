module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianPartModelOverSubfield
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIsoCarriesSharpPointsToConjugates

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsCoordPtLocal
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM GlobalTheory.Toroidal GlobalTheory.Ex
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000

noncomputable section
namespace GlobalTheory.CoordReduce



open ReciprocityTheory.ChartRestriction.G.Out in
theorem isCoordPt_map (h₂ : Laws2) {B : Scheme.{0}} (P : PolAV B) {R K : Type} [CommRing R] [CommRing K]
    (j : R →+* K) {s : Sp R ⟶ B} {x : Sp K ⟶ B} (hx : spMap j ≫ s = x) {k : ℕ} {J : Type}
    {p : J → (Over.mk s ⟶ P.A)} (hp : ∀ i, p i ^ k ^ 2 = 1) {z : Over.mk s ⟶ P.A} {w : J → R}
    (H : IsCoordPt P k p z fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (w i)) :
    IsCoordPt P k (fun i => (Over.homMk (spMap j) hx : Over.mk x ⟶ Over.mk s) ≫ p i)
      ((Over.homMk (spMap j) hx : Over.mk x ⟶ Over.mk s) ≫ z)
      fun i => (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (j (w i)) := by
  have : IsAffine (Over.mk s).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (Over.mk x).left := inferInstanceAs (IsAffine (Spec _))
  let jx : Over.mk x ⟶ Over.mk s := Over.homMk (spMap j) hx
  have Q := FullExtend.isCoordPt_move (f := 𝟙 B) (T := Over.mk x) (T₀ := Over.mk s) jx.left
    (ObjComp.isGrpPullback_id P.A) (DescendedPrincipal.lbIso_pull_id P.isLB).symm (B := Over.mk x) (𝟙 _) jx
    (Category.id_comp _) (hx.trans (Category.comp_id _).symm)
    (fun th₀ h => EmbPull.isGenSec_pullS P h₂.secBaseChangeAny jx h) (x := fun i => jx ≫ p i) (x₀ := p)
    (fun i => (Category.comp_id _).symm) (fun i => by rw [← MonObj.comp_pow, hp i, MonObj.comp_one])
    (z := jx ≫ z) (z₀ := z) (Category.comp_id _).symm H
  convert Q using 2 with a
  exact congrArg (fun q => q.hom (w a)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))

end GlobalTheory.CoordReduce
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointsDefinedOverSubfieldAbelianModel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCoordinatesScalarMulSubfieldValued
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCoordinatesScalarMulSubfieldValued
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
open GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.USep.Coords

open GlobalTheory GlobalTheory.UT.SymFrame GlobalTheory.ThetaCoord GlobalTheory.CommPairing GlobalTheory.GlobalLift GlobalTheory.VVRank GlobalTheory.CoordSep GlobalTheory.UT.CoefBasic
open GlobalTheory.TorusExt GlobalTheory.Poinc.Sep GlobalTheory.Poinc.Sep.ConjPt

variable {V : Type} [CommRing V] [IsDomain V] {D : DegPre V}

theorem psi_pow {N : ℕ} {b : 𝟙_ (Over (Sp V)) ⟶ D.P.A} (hb : b ^ N = 1) (Ψ : LB.Gen (psiLB D.P N b)) (hΨ : Ψ.IsGen)
    {κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N) (N ^ 2) 1)} (hκ : Normd κ)
    (h₁ : ∀ (T : Over (Sp V)) (z : T.left) (J), Good D.P.L z J →
      val Ψ (1 : T ⟶ D.P.A).left z J ^ N * val κ (toUnit T ≫ b).left z J = 1)
    {T : Over (Sp V)} (x : T ⟶ D.P.A) (z : T.left) (J) (hJ : Good D.P.L z J) :
    val Ψ x.left z J ^ N * val κ ((toUnit T ≫ b) * x).left z J = val κ x.left z J := by
  have key := ((((grep_gen (Y := D.P.A) Ψ hΨ (𝟙 _)).pow N).mul (grep_kap κ hκ.1 ((toUnit D.P.A ≫ b) * 𝟙 D.P.A))).mul
    (grep_kap κ hκ.1 (𝟙 D.P.A)).inv).triv GlobalTheory.abelianSchemeLaws_all.1.globalFns (fun U _ h => by
      rw [Fin.prod_univ_two, mul_pow (toUnit D.P.A ≫ b), ← MonObj.comp_pow, hb, MonObj.comp_one, _root_.one_mul]
      show (h (𝟙 _ ≫ 𝟙 _) ^ (N : ℤ) * h (𝟙 _ ≫ ((toUnit D.P.A ≫ b) * 𝟙 D.P.A).left) ^ (-(N : ℤ))) ^ N * _ * _ = _
      rw [Category.id_comp, Category.id_comp, Over.id_left]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one, ← natCast_zsmul]
      module)
    (fun y J hJ => by
      beta_reduce
      rw [Category.comp_id, Category.comp_id, normd_one hκ hJ, MonObj.comp_mul, Category.comp_id, _root_.mul_one,
        ← Category.assoc, comp_toUnit, h₁ _ y J hJ, inv_one, _root_.mul_one]) T x z J hJ
  beta_reduce at key
  rw [Category.comp_id, Category.comp_id, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit,
    mul_inv_eq_one] at key
  exact key

theorem lift_pow {m : ℕ} {T : Over (Sp V)} {y : T ⟶ D.P.A} (hy : y ^ m ^ 2 = 1)
    (θ : ThetaGrp D.P.A D.P.L ((m : ℤ) ^ 2) T) (hθ : SymLift D.P.A D.P.L ((m : ℤ) ^ 2) (m ^ 2) y θ)
    (α : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![(snd T D.P.A).left, (snd T D.P.A ^ m).left] ![(m : ℤ) ^ 2, -1]))
    (hα : α.IsGen) {κ : LB.Gen (kapLB D (𝟙 D.P.A ^ (m ^ 2)) ((m ^ 2) ^ 2) 1)} (hκ : κ.IsGen)
    (x : T ⟶ D.P.A) (z : T.left) (J) (hJ : Good D.P.L z J) :
    ((tval θ (lift (𝟙 T) x).left z J * val α (lift (𝟙 T) (y * x)).left z J) ^ (m ^ 2) ^ 2 *
      val κ (y ^ m * x ^ m).left z J) ^ m ^ 2 =
      (val α (lift (𝟙 T) x).left z J ^ (m ^ 2) ^ 2 * val κ (x ^ m).left z J) ^ m ^ 2 := by
  obtain rfl := hθ.pt_eq
  have hL := D.P.isLB
  have G := ((((grep_gen (Y := T ⊗ D.P.A) θ.φ θ.isGen (𝟙 _)).mul
    (grep_gen α hα (translT D.P.A θ.pt).left)).pow ((m ^ 2) ^ 2)).mul
      (grep_kap κ hκ ((fst T D.P.A ≫ θ.pt) ^ m * snd T D.P.A ^ m))).mul
    (((grep_gen α hα (𝟙 _)).pow ((m ^ 2) ^ 2)).mul (grep_kap κ hκ (snd T D.P.A ^ m))).inv
  obtain ⟨K, _, φ, ε, s, hs, h₁, h₂⟩ := G
  obtain ⟨a, ha⟩ := SymLiftOdd.exists_const hL (fst T D.P.A).left (lift (𝟙 T) (1 : T ⟶ D.P.A)).left
    (by rw [← Over.comp_left, lift_fst]; rfl) (SymLiftOdd.surj_fst GlobalTheory.abelianSchemeLaws_all.1.globalFns D.P.isAb T)
    (fun U _ h => (h₁ U h).trans (by
      have e₁ : (translT D.P.A θ.pt).left ≫ (snd T D.P.A).left = ((fst T D.P.A ≫ θ.pt) * snd T D.P.A).left := by
        rw [← Over.comp_left, translT, lift_snd]; rfl
      have e₂ : (translT D.P.A θ.pt).left ≫ (snd T D.P.A ^ m).left =
          ((fst T D.P.A ≫ θ.pt) ^ m * snd T D.P.A ^ m).left := by
        rw [← Over.comp_left, MonObj.comp_pow, translT, lift_snd, ← mul_pow]; rfl
      have e₃ : ((fst T D.P.A ≫ θ.pt) ^ m * snd T D.P.A ^ m) ^ m ^ 2 = (snd T D.P.A ^ m) ^ m ^ 2 := by
        rw [mul_pow, ← pow_mul, mul_comm m, pow_mul, ← MonObj.comp_pow, hy, MonObj.comp_one, one_pow, _root_.one_mul]
      beta_reduce
      rw [Fin.prod_univ_two, Fin.prod_univ_two, Fin.prod_univ_two, e₃]
      show (h (𝟙 _ ≫ (snd T D.P.A).left) ^ ((m : ℤ) ^ 2) *
          h (𝟙 _ ≫ ((fst T D.P.A ≫ θ.pt) * snd T D.P.A).left) ^ (-((m : ℤ) ^ 2)) *
        (h ((translT D.P.A θ.pt).left ≫ (snd T D.P.A).left) ^ ((m : ℤ) ^ 2) *
          h ((translT D.P.A θ.pt).left ≫ (snd T D.P.A ^ m).left) ^ (-1 : ℤ))) ^ _ * _ *
        ((h (𝟙 _ ≫ (snd T D.P.A).left) ^ ((m : ℤ) ^ 2) * h (𝟙 _ ≫ (snd T D.P.A ^ m).left) ^ (-1 : ℤ)) ^ _ * _)⁻¹ = _
      rw [e₁, e₂, Category.id_comp, Category.id_comp, Category.id_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one, ← natCast_zsmul]
      push_cast
      module)) hs
  let f : (T ⟶ D.P.A) → (T.left.presheaf.stalk z)ˣ := fun x =>
    val α (lift (𝟙 T) x).left z J ^ (m ^ 2) ^ 2 * val κ (x ^ m).left z J
  have key : ∀ x : T ⟶ D.P.A, tval θ (lift (𝟙 T) x).left z J ^ (m ^ 2) ^ 2 * f (θ.pt * x) =
      gm (𝟙 T.left) z ⊤ a * f x := fun x => by
    have e := (h₂ T (lift (𝟙 T) x) z J hJ).symm.trans (ha _ _ z J hJ)
    beta_reduce at e
    rw [lift_fst_left, Category.comp_id, lift_translT, Category.id_comp,
      MonObj.comp_mul, MonObj.comp_pow, MonObj.comp_pow, lift_snd, ← Category.assoc, lift_fst, Category.id_comp,
      mul_inv_eq_iff_eq_mul, mul_pow, _root_.mul_assoc] at e
    simp only [f]
    rw [mul_pow θ.pt]
    exact e
  have hp : ∏ j ∈ Finset.range (m ^ 2), tval θ (lift (𝟙 T) (θ.pt ^ j * x)).left z J = 1 := by
    have c := val_corr hJ hθ.pow_eq (lift (𝟙 T) x).left
    rw [ThetaPullback.val_powGen θ _ _ hJ, val_one] at c
    rw [← c, Finset.prod_range]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [lift_translT, Category.id_comp]
    rfl
  have tel : ∀ n : ℕ, (∏ j ∈ Finset.range n, tval θ (lift (𝟙 T) (θ.pt ^ j * x)).left z J) ^ (m ^ 2) ^ 2 *
      f (θ.pt ^ n * x) = gm (𝟙 T.left) z ⊤ a ^ n * f x := fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_range_succ, mul_pow, _root_.mul_assoc, pow_succ' θ.pt, _root_.mul_assoc θ.pt, key,
        mul_left_comm, ih, pow_succ', _root_.mul_assoc]
  have ha1 := tel (m ^ 2)
  rw [hp, hy, one_pow, _root_.one_mul, _root_.one_mul, eq_comm, mul_eq_right] at ha1
  have k := congrArg (· ^ m ^ 2) (key x)
  simp only [f] at k
  rw [mul_pow (gm _ _ _ _), ha1, _root_.one_mul, mul_pow θ.pt, ← _root_.mul_assoc, ← mul_pow] at k
  exact k

theorem exists_scalar {K R : Type} [Field K] [CommRing R] (φ : K →+* R) (hφ : Function.Injective φ) (k₀ : Subfield K)
    [IsAlgClosed k₀] {M : ℕ} (hM : 1 ≤ M) {I : Type} (v : I → K) (Λ : R)
    (h : ∀ i, ∃ r ∈ k₀, φ (v i) ^ M = Λ * φ r) :
    ∃ (l : K) (r : I → K), (∀ i, r i ∈ k₀) ∧ ∀ i, v i = l * r i := by
  by_cases h0 : ∀ i, v i = 0
  · exact ⟨0, fun _ => 0, fun _ => k₀.zero_mem, fun i => by rw [h0, zero_mul]⟩
  obtain ⟨i₀, hi₀⟩ := not_forall.1 h0
  obtain ⟨r₀, m₀, e₀⟩ := h i₀
  have hr₀ : r₀ ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_zero, ← map_pow, map_eq_zero_iff φ hφ] at e₀
    exact pow_ne_zero M hi₀ e₀
  refine ⟨v i₀, fun i => v i / v i₀, fun i => ?_, fun i => (mul_div_cancel₀ _ hi₀).symm⟩
  obtain ⟨r, m₁, e₁⟩ := h i
  have e : v i ^ M * r₀ = r * v i₀ ^ M := hφ (by
    rw [map_mul, map_mul, map_pow, map_pow, e₀, e₁]; ring)
  refine Frames.mem_of_pow_mem k₀ hM (x := v i / v i₀) ?_
  rw [div_pow, (div_eq_div_iff (pow_ne_zero M hi₀) hr₀).2 e]
  exact k₀.div_mem m₁ m₀

theorem coords_scalar [IsLocalRing V] [IsNoetherianRing V] [IsIntegrallyClosed V] (D : DegPre V) {m : ℕ} (hm : 1 ≤ m)
    {X C : Type} [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V) (mo : X → V) (a : D.X)
    (hmo : mo (e.symm (m • a)) ≠ 0) (c₀ : C) (hu : IsUnit (u (e.symm (m • a)) c₀))
    (hT : IsThetaTerms D (m ^ 2) e (fun mu c => u mu c * mo mu))
    {K : Type} [Field K] [IsAlgClosed K] (ev : V →+* K) (k₀ : Subfield K) [IsAlgClosed k₀]
    (hr : ∀ c, ∃ r ∈ k₀, ev (u (e.symm (m • a)) c) = r * ev (u (e.symm (m • a)) c₀))
    {I : Type} (y : I → (Over.mk (spMap ev) ⟶ D.P.A)) (hy : ∀ i, y i ^ m ^ 2 = 1) (v : I → K)
    (H : GlobalTheory.Ex.IsCoordPt D.P m y (toUnit _ ≫ D.c a) (fun i => GlobalTheory.Ex.fnOf (v i))) :
    ∃ (l : K) (r : I → K), (∀ i, r i ∈ k₀) ∧ ∀ i, v i = l * r i := by
  have hL := D.P.isLB
  have hN : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm
  set mu := e.symm (m • a) with hmu
  have hc : ∀ n : ℕ, D.c (n • a) = D.c a ^ n := fun n => by
    induction n with
    | zero =>
      have h := D.c_add 0 0
      rw [add_zero] at h
      rw [zero_smul, pow_zero]
      exact mul_eq_left.1 h.symm
    | succ n ih => rw [succ_nsmul, D.c_add, ih, pow_succ]; rfl
  have hχ : D.c (e mu) = D.c a ^ m := by rw [hmu, e.apply_symm_apply, hc]
  obtain ⟨th, g, b, w, h₁, h₂, h₃, h₄, h₅, -⟩ := hT
  have hb : ∀ c, b c ^ m ^ 2 = 1 := fun c => (Frames.torsion_of_nsmul (g c) (b c) (h₁ c) (h₂ c)).2
  obtain ⟨θ, hθ⟩ := exists_genAll D.P
  choose Ψ hΨ nΨ vΨ using fun c => exists_psi hN (g c) (b c) (h₁ c) (h₂ c) (w c) (h₄ c)
  obtain ⟨ρ, A, cross, hA⟩ := exists_vals hθ (m ^ 2) (e mu) (th.s (e mu)) g b h₁ w Ψ hΨ (fun c => vΨ c (e mu)) _ (h₅ mu)
  obtain ⟨κ, hκ⟩ := exists_kap (D := D) GlobalTheory.abelianSchemeLaws_all.1.mulPull (m ^ 2)
  have hv : ∀ c, ∃ r ∈ k₀, ev ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom (A c)) =
      r * ev ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom (A c₀)) := fun c => by
    obtain ⟨r, r₁, r₂⟩ := hr c
    have x := cross c c₀
    rw [mul_pow, mul_pow, mul_right_comm, mul_right_comm (u mu c₀ ^ m ^ 2)] at x
    have x' := congrArg ev (mul_right_cancel₀ (pow_ne_zero _ hmo) x)
    rw [map_mul, map_mul, map_pow, map_pow, r₂] at x'
    refine ⟨r ^ m ^ 2, k₀.pow_mem r₁ _, mul_left_cancel₀ (pow_ne_zero (m ^ 2) (hu.map ev).ne_zero) (x'.symm.trans ?_)⟩
    ring
  obtain ⟨-, -, t, s₁, α, τ, U, s₂, -, hα, -, hs₁, hU, hs₂, hval⟩ := H
  obtain ⟨k, hk⟩ := hθ K (spMap ev) t
  let T : Over (Sp V) := Over.mk (spMap ev)
  obtain ⟨p⟩ : Nonempty T.left := inferInstanceAs (Nonempty (PrimeSpectrum K))
  obtain ⟨J, hJ⟩ := exists_good' hL p
  have alg : ∀ {R : Type} [CommRing R] (N : ℕ) (v k t A A₀ r : R) (τ P α Ψ ρ κ κ' : Rˣ), v * τ.val = P.val * (k * t) →
      A = t ^ N * (Ψ * ρ ^ N).val → A = r * A₀ → Ψ ^ N * κ' = κ → (P ^ N ^ 2 * κ') ^ N = (α ^ N ^ 2 * κ) ^ N →
      v ^ N ^ 3 = (((α * τ⁻¹ * ρ⁻¹).val * k) ^ N ^ 3 * A₀ ^ N ^ 2) * r ^ N ^ 2 := by
    intro R _ N v k t A A₀ r τ P α Ψ ρ κ κ' a₁ a₂ a₃ a₄ a₅
    have a₆ : (P * τ⁻¹) ^ N ^ 3 = (α * τ⁻¹ * ρ⁻¹) ^ N ^ 3 * (Ψ * ρ ^ N) ^ N ^ 2 := by
      subst a₄
      have a := congrArg Additive.ofMul a₅
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow, ← natCast_zsmul] at a ⊢
      push_cast at a ⊢
      linear_combination (norm := module) a
    have a₇ : v = (P * τ⁻¹).val * (k * t) := by
      rw [Units.val_mul, mul_right_comm, ← a₁, Units.mul_inv_cancel_right]
    rw [_root_.mul_assoc, ← mul_pow A₀, mul_comm A₀, ← a₃, a₂, a₇, mul_pow, ← Units.val_pow_eq_pow_val, a₆,
      Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
    ring
  refine exists_scalar (GlobalTheory.RatioVal.germConst K p) (RingHom.injective _) k₀ (M := (m ^ 2) ^ 3) (Nat.one_le_pow _ _ hN) v
    (@id (T.left.presheaf.stalk p) (((val α (lift (𝟙 T) (toUnit T ≫ D.c a)).left p J * (val τ (𝟙 T.left) p J)⁻¹ *
      (val ρ T.hom p J)⁻¹).val * gs (𝟙 T.left) p ⊤ k) ^ (m ^ 2) ^ 3 * (@id (T.left.presheaf.stalk p) <| GlobalTheory.RatioVal.germConst K p
        (ev ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom (A c₀)))) ^ (m ^ 2) ^ 2)) fun i => ?_
  obtain ⟨c, hc'⟩ := h₃ K (spMap ev) (y i ^ m) (by rw [← pow_mul, mul_comm m, pow_mul, hy, one_pow])
  obtain ⟨r, r₁, r₂⟩ := hv c
  refine ⟨r ^ (m ^ 2) ^ 2, k₀.pow_mem r₁ _, ?_⟩
  have ez : (toUnit T ≫ D.c a) ^ m = toUnit T ≫ D.c (e mu) := by rw [hχ, MonObj.comp_pow]
  have e₁ := sv_value (hval i) hJ
  rw [sv_act (hU i).pt_eq (hs₂ i) _ hJ, sv_mulPull hs₁ _ hJ, hk _ _ p J hJ, lift_fst_left, ← Over.comp_left, lift_snd,
    Category.id_comp, mul_pow, ez, hc', ← _root_.mul_assoc, ← Units.val_mul] at e₁
  have e₂ := (GlobalTheory.RatioVal.gs_specMap ev p _).symm.trans (hA c T p J hJ)
  have e₃ := psi_pow (hb c) (Ψ c) (hΨ c) hκ (nΨ c κ hκ) (toUnit T ≫ D.c (e mu)) p J hJ
  have e₄ := lift_pow (hy i) (U i) (hU i) α hα hκ.1 (toUnit T ≫ D.c a) p J hJ
  rw [ez, hc'] at e₄
  rw [map_pow]
  exact alg _ _ _ _ _ _ _ _ _ _ _ _ _ _ ((congrArg (· * _) (GlobalTheory.RatioVal.gs_id_const p (v i)).symm).trans e₁.symm) e₂
    ((congrArg _ r₂).trans (map_mul _ _ _)) e₃ e₄

end GlobalTheory.USep.Coords

open NumberField ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef GlobalTheory GlobalTheory.USep

theorem GlobalTheory.USep.coords_scalar_mul_rational : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (I : Type) (y : I → (Over.mk (spMap ev) ⟶ D.P.A)), (∀ i, y i ^ (n ^ j) ^ 2 = 1) → ∀ (a : D.X) (z : Over.mk (spMap ev) ⟶ D.P.A), z.left = spMap ev ≫ (D.c a).left → ∃ (v : I → K) (l : K) (r : I → K), GlobalTheory.Ex.IsCoordPt D.P (n ^ j) y z (fun i => GlobalTheory.Ex.fnOf (v i)) ∧ (∀ i, r i ∈ k₀) ∧ ∀ i, v i = l * r i := by
  intro g n hn hodd
  refine ⟨0, fun j _ V₁ _ _ _ hV hunit D _ X C _ e u mo hu hT K _ _ ev k₀ hk₀ hr I y hy a z hz => ?_⟩
  haveI : IsNoetherianRing V₁ := hV.1
  haveI : IsIntegrallyClosed V₁ := hV.2.1
  have hm : 1 ≤ n ^ j := Nat.one_le_pow _ _ hn.pos
  have hK : ((n ^ j : ℕ) : K) ≠ 0 := by
    have := ((hunit (n ^ j) (by omega)).map ev).ne_zero
    rwa [map_natCast] at this
  obtain rfl : z = toUnit _ ≫ D.c a := Over.OverMorphism.ext hz
  obtain ⟨v, hv⟩ := (GlobalTheory.CoordSep.coord_exists_unique_separate GlobalTheory.abelianSchemeLaws_all.1 K (Sp V₁) D.P (spMap ev)
    (n ^ j) hodd.pow hK I y hy).1 (toUnit _ ≫ D.c a)
  obtain ⟨hmo, c₀, hc₀⟩ := hu (e.symm ((n ^ j) • a))
  obtain ⟨l, r, h₁, h₂⟩ := Coords.coords_scalar D hm e u mo a hmo c₀ hc₀ hT ev k₀ (fun c => hr _ c c₀ hc₀) y hy v hv
  exact ⟨v, l, r, hv, h₁, h₂⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCoordinatesScalarMulSubfieldValuedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionCoordinates_scalar_mul_subfieldValued : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (I : Type) (y : I → (Over.mk (spMap ev) ⟶ D.P.A)), (∀ i, y i ^ (n ^ j) ^ 2 = 1) → ∀ (a : D.X) (z : Over.mk (spMap ev) ⟶ D.P.A), z.left = spMap ev ≫ (D.c a).left → ∃ (v : I → K) (l : K) (r : I → K), GlobalTheory.Ex.IsCoordPt D.P (n ^ j) y z (fun i => GlobalTheory.Ex.fnOf (v i)) ∧ (∀ i, r i ∈ k₀) ∧ ∀ i, v i = l * r i := by
  first | exact @GlobalTheory.USep.coords_scalar_mul_rational | exact GlobalTheory.USep.coords_scalar_mul_rational | (intros; apply GlobalTheory.USep.coords_scalar_mul_rational <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolAVPointDefinedOverOfCoordsProportional
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolAVPointDefinedOverOfCoordsProportional
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem defOver_of_coord_proportional : ∀ (K : Type) [Field K] [IsAlgClosed K] (k₀ : Subfield K), IsAlgClosed k₀ →
    ∀ (P₀ : PolAV (Sp k₀)) (m : ℕ), Odd m → 3 ≤ m → (m : K) ≠ 0 →
    ∀ (z : Over.mk (spMap k₀.subtype) ⟶ P₀.A) (v : {y : Over.mk (spMap k₀.subtype) ⟶ P₀.A // y ^ m ^ 2 = 1} → K)
      (l : K) (r : {y : Over.mk (spMap k₀.subtype) ⟶ P₀.A // y ^ m ^ 2 = 1} → K),
      GlobalTheory.Ex.IsCoordPt P₀ m (fun i => i.1) z (fun i => GlobalTheory.Ex.fnOf (v i)) → (∀ i, r i ∈ k₀) →
      (∀ i, v i = l * r i) → GlobalTheory.Poinc.Sep.DefOver k₀ z.left := by
  intro K _ _ k₀ hk₀ P₀ m hm hm3 hmK z v l r H hr hv
  classical
  let Ix := {y : Over.mk (spMap k₀.subtype) ⟶ P₀.A // y ^ m ^ 2 = 1}
  have Lw := GlobalTheory.abelianSchemeLaws_all
  have hm1 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hm2K : ((m ^ 2 : ℕ) : K) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hmK
  have hcard := (Lw.1.mulN (Sp k₀) P₀ (m ^ 2) hm1).2.2.2.2 K (spMap k₀.subtype) hm2K
  have hfin : Finite Ix := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (by omega))

  have hσs : ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → spMap σ.toRingHom ≫ spMap k₀.subtype = spMap k₀.subtype := by
    intro σ hσ
    simp only [spMap, ← Spec.map_comp]
    congr 2
    ext w
    exact hσ _ w.2

  have hfix : ∀ (σ : K ≃+* K) (hσ : ∀ a ∈ k₀, σ a = a) (y : Ix),
      (Over.homMk (spMap σ.toRingHom) (hσs σ hσ) : Over.mk (spMap k₀.subtype) ⟶ Over.mk (spMap k₀.subtype)) ≫ y.1 = y.1 := by
    intro σ hσ y
    have hdef : DefOver k₀ y.1.left := by
      refine defOver_of_finite_orbit K k₀ hk₀ _ _ ((Set.finite_range fun y' : Ix => y'.1.left).subset ?_)
      rintro _ ⟨τ, hτ, rfl⟩
      refine ⟨⟨(Over.homMk (spMap τ.toRingHom) (hσs τ hτ) : Over.mk (spMap k₀.subtype) ⟶ Over.mk (spMap k₀.subtype)) ≫ y.1, ?_⟩, ?_⟩
      · rw [← MonObj.comp_pow, y.2, MonObj.comp_one]
      · rfl
    obtain ⟨y₀, hy₀⟩ := hdef
    apply Over.OverMorphism.ext
    show spMap σ.toRingHom ≫ y.1.left = y.1.left
    rw [← hy₀, ← Category.assoc, hσs σ hσ]

  obtain ⟨-, U₂, -, U₄⟩ := CoordSep.coord_exists_unique_separate Lw.1 K (Sp k₀) P₀ (spMap k₀.subtype) m hm hmK Ix
    (fun i => i.1) (fun i => i.2)
  have hall : ∀ y : Over.mk (spMap k₀.subtype) ⟶ P₀.A, y ^ m ^ 2 = 1 → ∃ i : Ix, i.1 = y := fun y hy => ⟨⟨y, hy⟩, rfl⟩
  have hv0 : v ≠ 0 := (U₄ hm3 hall z z v H H).2
  have hl : l ≠ 0 := by
    intro h0
    apply hv0
    funext i
    rw [hv i, h0, zero_mul, Pi.zero_apply]
  have horb : ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → spMap σ.toRingHom ≫ z.left = z.left := by
    intro σ hσ
    let h : Over.mk (spMap k₀.subtype) ⟶ Over.mk (spMap k₀.subtype) := Over.homMk (spMap σ.toRingHom) (hσs σ hσ)
    have H2 := CoordReduce.isCoordPt_map Lw.2 P₀ σ.toRingHom (hσs σ hσ) (p := fun i : Ix => i.1)
      (fun i => i.2) (w := v) H
    have hp : (fun i : Ix => h ≫ i.1) = fun i => i.1 := funext fun i => hfix σ hσ i
    change GlobalTheory.Ex.IsCoordPt P₀ m (fun i : Ix => h ≫ i.1) (h ≫ z) (fun i => GlobalTheory.Ex.fnOf (σ (v i))) at H2
    rw [hp] at H2
    have hσl : σ l ≠ 0 := (map_ne_zero σ).2 hl
    have H3 : GlobalTheory.Ex.IsCoordPt P₀ m (fun i : Ix => i.1) (h ≫ z) (fun i => GlobalTheory.Ex.fnOf (v i)) := by
      refine (U₂ (h ≫ z) (fun i => σ (v i)) v H2).2 ⟨Units.mk0 (l / σ l) (div_ne_zero hl hσl), ?_⟩
      funext i
      simp only [Units.val_mk0, Pi.smul_apply, smul_eq_mul]
      rw [hv i, map_mul, hσ _ (hr i)]
      field_simp
    have := (U₄ hm3 hall (h ≫ z) z v H3 H).1
    have e2 := congrArg CommaMorphism.left this
    exact e2
  refine defOver_of_finite_orbit K k₀ hk₀ _ z.left ((Set.finite_singleton z.left).subset ?_)
  rintro _ ⟨σ, hσ, rfl⟩
  exact horb σ hσ

end GlobalTheory.Poinc.Sep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolAVPointDefinedOverOfCoordsProportionalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polAV_point_defined_over_of_coords_proportional : ∀ (K : Type) [Field K] [IsAlgClosed K] (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (P₀ : PolAV (Sp k₀)) (m : ℕ), Odd m → 3 ≤ m → (m : K) ≠ 0 → ∀ (z : Over.mk (spMap k₀.subtype) ⟶ P₀.A) (v : {y : Over.mk (spMap k₀.subtype) ⟶ P₀.A // y ^ m ^ 2 = 1} → K) (l : K) (r : {y : Over.mk (spMap k₀.subtype) ⟶ P₀.A // y ^ m ^ 2 = 1} → K), GlobalTheory.Ex.IsCoordPt P₀ m (fun i => i.1) z (fun i => GlobalTheory.Ex.fnOf (v i)) → (∀ i, r i ∈ k₀) → (∀ i, v i = l * r i) → GlobalTheory.Poinc.Sep.DefOver k₀ z.left := by
  first | exact @GlobalTheory.Poinc.Sep.defOver_of_coord_proportional | exact GlobalTheory.Poinc.Sep.defOver_of_coord_proportional | (intros; apply GlobalTheory.Poinc.Sep.defOver_of_coord_proportional <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointsDefinedOverSubfieldAbelianModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.USep

theorem points_defOver : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (B₀ : Over (Sp k₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left) (B' : Over (Sp K)) [GrpObj B'] (π₁ : B'.left ⟶ D.P.A.left) (π₀ : B'.left ⟶ B₀.left) (w : LB.Iso (D.P.L.pull π₁) (M₀.pull π₀)), IsAbelianScheme B₀ → M₀.IsLB → IsGrpPullback B' D.P.A (spMap ev) π₁ → IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ → w.IsGen → ∀ (a : D.X) (x : Sp K ⟶ B'.left), x ≫ B'.hom = 𝟙 _ → x ≫ π₁ = spMap ev ≫ (D.c a).left → GlobalTheory.Poinc.Sep.DefOver k₀ (x ≫ π₀) := by
  intro g n hn hodd
  obtain ⟨j₁, hC⟩ := GlobalTheory.T.torsionCoordinates_scalar_mul_subfieldValued g n hn hodd
  refine ⟨max j₁ 1, ?_⟩
  intro j hj V₁ _ _ _ hCN hunit D hg X C _ e u mo hmo hT K _ _ ev k₀ hk₀ hrat B₀ _ _ M₀ B' _ π₁ π₀ w hB₀ hM₀ h₁ h₀ hw a x hx hxa
  have hj₁ : j₁ ≤ j := le_trans (le_max_left _ _) hj
  have hj1 : 1 ≤ j := le_trans (le_max_right _ _) hj
  have hmodd : Odd (n ^ j) := hodd.pow
  have hn3 : 3 ≤ n := by
    have h2 := hn.two_le
    rcases Nat.lt_or_ge n 3 with h | h
    · have : n = 2 := by omega
      subst this; exact absurd hodd (by decide)
    · exact h
  have hm3 : 3 ≤ n ^ j := le_trans hn3 (by
    calc n = n ^ 1 := (pow_one n).symm
      _ ≤ n ^ j := Nat.pow_le_pow_right hn.pos hj1)
  have hmK : ((n ^ j : ℕ) : K) ≠ 0 := by
    have h := (hunit (n ^ j) (by positivity)).map ev
    rw [map_natCast] at h
    exact h.ne_zero
  haveI : IsNoetherianRing V₁ := hCN.1
  haveI : IsCommMonObj D.P.A := D.P.isAb.comm
  haveI : IsCommMonObj B' := GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback h₁
  let P' : PolAV (Sp K) :=
    { A := B'
      isAb :=
        { comm := inferInstance
          smooth := MorphismProperty.of_isPullback (P := @Smooth) h₁.1 D.P.isAb.smooth
          proper := MorphismProperty.of_isPullback (P := @IsProper) h₁.1 D.P.isAb.proper
          geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) h₁.1 D.P.isAb.geomConnected }
      g := D.P.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h₁.1 D.P.smoothDim
      L := D.P.L.pull π₁
      isLB := pull_isLB D.P.isLB _
      rigid := GlobalTheory.PolBaseChange.rigidified_pull h₁ D.P.rigid
      sym := GlobalTheory.PolBaseChange.sym_pull h₁ D.P.sym
      ample := by
        haveI := D.P.isAb.proper
        exact GlobalTheory.AmpleBaseChange.relAmple_of_isPullback D.P.isLB D.P.ample h₁.1
      ktriv := kTriv_pull h₁ D.P.isLB (pull_isLB D.P.isLB _)
        ((isGen_iff _).1 (GlobalTheory.TorsionTauCompare.isGen_refl (pull_isLB D.P.isLB π₁))) D.P.ktriv }
  have hw' : LBIso P'.L (M₀.pull π₀) := ⟨w, hw⟩
  have hSym : Out.Sym B₀ M₀ := (GlobalTheory.PolDescent.rigidified_sym_kTriv_descend k₀ K k₀.subtype B₀ B' π₀ M₀ P'.L hB₀ h₀
    hM₀ P'.isLB hw').2.1 P'.sym
  have h₀' : IsGrpPullback P'.A B₀ (spMap (algebraMap k₀ K)) π₀ := h₀
  set_option synthInstance.maxHeartbeats 400000 in
  have : Flat (spMap k₀.subtype) := Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  let P₀ : PolAV (Sp k₀) :=
    { A := B₀, isAb := hB₀, g := P'.g,
      smoothDim := GlobalTheory.CM.smoothOfRelativeDimension_of_fibre k₀ K k₀.subtype B₀ P'.A.left π₀ P'.A.hom P'.g hB₀ h₀.1
        P'.smoothDim,
      L := M₀, isLB := hM₀, rigid := ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_local M₀ hM₀ _ _, sym := hSym,
      ample := GlobalTheory.AmpleDescent.relAmple_of_faithfullyFlat k₀ K B₀ P'.A π₀ M₀ P'.L hB₀ h₀' hM₀ P'.isLB hw' P'.ample,
      ktriv := GlobalTheory.AmpleDescent.kTriv_of_pull h₀ hM₀ P'.isLB hw' P'.ktriv }
  obtain ⟨Φ₀, hΦ₀⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback (G := B₀) (G' := B') h₀
    (𝟙 (Sp K)) (spMap k₀.subtype) (Category.id_comp _)
  obtain ⟨Φ₁, hΦ₁⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback (G := D.P.A) (G' := B') h₁
    (𝟙 (Sp K)) (spMap ev) (Category.id_comp _)
  let t₀ : Sp K ⟶ Sp k₀ := spMap k₀.subtype
  let t₁ : Sp K ⟶ Sp V₁ := spMap ev
  let Ix := {y : Over.mk t₀ ⟶ B₀ // y ^ (n ^ j) ^ 2 = 1}
  let X' : Ix → (baseOver (Sp K) ⟶ B') := fun i => Φ₀.symm i.1
  have hX' : ∀ i, X' i ^ (n ^ j) ^ 2 = 1 := fun i => Φ₀.injective (by
    rw [map_pow, MulEquiv.apply_symm_apply, i.2, map_one])
  let z' : baseOver (Sp K) ⟶ B' := Over.homMk x hx
  let yD : Ix → (Over.mk t₁ ⟶ D.P.A) := fun i => Φ₁ (X' i)
  have hyD : ∀ i, yD i ^ (n ^ j) ^ 2 = 1 := fun i => by
    simp only [yD]; rw [← map_pow, hX' i, map_one]
  have hzD : (Φ₁ z').left = t₁ ≫ (D.c a).left := by
    rw [hΦ₁]; simp [t₁, z', hxa]
  obtain ⟨vD, l, r, hvD, hr, hvr⟩ := hC j hj₁ V₁ hCN hunit D hg X C e u mo hmo hT K ev k₀ hk₀ hrat
    Ix yD hyD a (Φ₁ z') hzD
  have HD := GlobalTheory.FullExtend.isCoordPt_move (f := spMap ev) (T := baseOver (Sp K)) (T₀ := Over.mk t₁) (𝟙 _)
    (P₀ := D.P) (P := P') (φ := π₁) h₁ (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB D.P.isLB π₁)) (B := Over.mk t₁)
    (𝟙 _) (𝟙 _) (by simp) (by simp [t₁])
    (fun th₀ h => GlobalTheory.ThetaCoord.isGenSec_pullS D.P.isLB (𝟙 _) (𝟙 _) (by simp) h) (x := X') (x₀ := yD)
    (fun i => (Category.id_comp _).trans (hΦ₁ _)) hX' (z := z') (z₀ := Φ₁ z') ((Category.id_comp _).trans (hΦ₁ z')) hvD
  obtain ⟨v₀, hv₀⟩ := (GlobalTheory.CoordSep.coord_exists_unique_separate GlobalTheory.abelianSchemeLaws_all.1 K (Sp k₀) P₀ t₀ (n ^ j)
    hmodd hmK Ix (fun i => i.1) (fun i => i.2)).1 (Φ₀ z')
  have H0 := GlobalTheory.FullExtend.isCoordPt_move (f := spMap k₀.subtype) (T := baseOver (Sp K)) (T₀ := Over.mk t₀) (𝟙 _)
    (P₀ := P₀) (P := P') (φ := π₀) h₀ hw' (B := Over.mk t₀) (𝟙 _) (𝟙 _) (by simp) (by simp [t₀])
    (fun th₀ h => GlobalTheory.ThetaCoord.isGenSec_pullS hM₀ (𝟙 _) (𝟙 _) (by simp) h) (x := X') (x₀ := fun i => i.1)
    (fun i => (Category.id_comp _).trans ((congrArg Over.Hom.left (Φ₀.apply_symm_apply i.1)).symm.trans (hΦ₀ _)))
    hX' (z := z') (z₀ := Φ₀ z') ((Category.id_comp _).trans (hΦ₀ z')) hv₀
  have HD' : GlobalTheory.Ex.IsCoordPt P' (n ^ j) X' z' (fun i => GlobalTheory.Ex.fnOf (vD i)) := by
    convert HD using 2 with i
    simp
  have H0' : GlobalTheory.Ex.IsCoordPt P' (n ^ j) X' z' (fun i => GlobalTheory.Ex.fnOf (v₀ i)) := by
    convert H0 using 2 with i
    simp
  obtain ⟨-, U₂, -, -⟩ := GlobalTheory.CoordSep.coord_exists_unique_separate GlobalTheory.abelianSchemeLaws_all.1 K (Sp K) P' (𝟙 _)
    (n ^ j) hmodd hmK Ix X' hX'
  obtain ⟨c, hc⟩ := (U₂ z' v₀ vD H0').1 HD'
  have hv₀r : ∀ i, v₀ i = ((c⁻¹ : Kˣ) * l) * r i := fun i => by
    have := congrFun hc i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [_root_.mul_assoc, ← hvr i, this, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
  have hD := GlobalTheory.T.polAV_point_defined_over_of_coords_proportional K k₀ hk₀ P₀ (n ^ j) hmodd hm3 hmK (Φ₀ z') v₀ _ r hv₀ hr hv₀r
  rwa [hΦ₀] at hD

end GlobalTheory.USep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointsDefinedOverSubfieldAbelianModelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPoints_defined_over_subfield_abelianModel : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (B₀ : Over (Sp k₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left) (B' : Over (Sp K)) [GrpObj B'] (π₁ : B'.left ⟶ D.P.A.left) (π₀ : B'.left ⟶ B₀.left) (w : LB.Iso (D.P.L.pull π₁) (M₀.pull π₀)), IsAbelianScheme B₀ → M₀.IsLB → IsGrpPullback B' D.P.A (spMap ev) π₁ → IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ → w.IsGen → ∀ (a : D.X) (x : Sp K ⟶ B'.left), x ≫ B'.hom = 𝟙 _ → x ≫ π₁ = spMap ev ≫ (D.c a).left → GlobalTheory.Poinc.Sep.DefOver k₀ (x ≫ π₀) := by
  first | exact @GlobalTheory.USep.points_defOver | exact GlobalTheory.USep.points_defOver | (intros; apply GlobalTheory.USep.points_defOver <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartDescendsOfThetaTermsRatios
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.USep

theorem descAt_of_thetaTerms : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → DescAt D ev k₀ := by
  intro g n hn hodd
  obtain ⟨j₁, h₁⟩ := GlobalTheory.T.polarisedAbelianPart_model_over_subfield g n hn hodd
  obtain ⟨j₂, h₂⟩ := GlobalTheory.T.torsionPoints_defined_over_subfield_abelianModel g n hn hodd
  refine ⟨max j₁ j₂, ?_⟩
  intro j hj V₁ _ _ _ hCN hunit D hg X C _ e u mo hmo hT K _ _ ev k₀ hk₀ hr
  obtain ⟨B₀, iG₀, iC₀, M₀, B', iG', π₁, π₀, w, hA, hM, hp1, hp0, hw⟩ :=
    h₁ j (le_trans (le_max_left _ _) hj) V₁ hCN hunit D hg X C e u mo hmo hT K ev k₀ hk₀ hr
  have hP := h₂ j (le_trans (le_max_right _ _) hj) V₁ hCN hunit D hg X C e u mo hmo hT K ev k₀ hk₀ hr
    B₀ M₀ B' π₁ π₀ w hA hM hp1 hp0 hw
  have hsq : ∀ a : D.X, (spMap ev ≫ (D.c a).left) ≫ D.P.A.hom = 𝟙 (Sp K) ≫ spMap ev := by
    intro a
    rw [Category.assoc, Over.w (D.c a)]
    simp
  let c' : D.X → (Sp K ⟶ B'.left) := fun a => hp1.1.lift (spMap ev ≫ (D.c a).left) (𝟙 _) (hsq a)
  have hc1 : ∀ a, c' a ≫ B'.hom = 𝟙 _ := fun a => hp1.1.lift_snd _ _ _
  have hc2 : ∀ a, c' a ≫ π₁ = spMap ev ≫ (D.c a).left := fun a => hp1.1.lift_fst _ _ _
  choose c₀ hc₀ using fun a => hP a (c' a) (hc1 a) (hc2 a)
  exact ⟨B₀, iG₀, iC₀, M₀, c₀, B', iG', π₁, π₀, w, c', hA, hM, hp1, hp0, hw, fun a => ⟨hc1 a, hc2 a, (hc₀ a).symm⟩⟩

end GlobalTheory.USep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartDescendsOfThetaTermsRatiosStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianPart_descends_of_thetaTerms_ratios : ∀ (g n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.P.g = g → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D ((n ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → DescAt D ev k₀ := by
  first | exact @GlobalTheory.USep.descAt_of_thetaTerms | exact GlobalTheory.USep.descAt_of_thetaTerms | (intros; apply GlobalTheory.USep.descAt_of_thetaTerms <;> assumption)
end
