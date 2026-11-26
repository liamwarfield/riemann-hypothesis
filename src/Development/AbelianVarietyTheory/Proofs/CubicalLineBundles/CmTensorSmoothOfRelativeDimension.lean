module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LamPtClauses
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInNormalFormAndArchimedeanConstant
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsAbelianSchemeModelOfIsogenyDedekind
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfRangeSubset
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSymplecticCoordinatesOfIsPeriod

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmTensorSmoothOfRelativeDimension
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmTensorSmoothOfRelativeDimension
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.TenDim

theorem finrank_fibre (O M k : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] [Field k] [Algebra O k] :
    Module.finrank k (k ⊗[O] M) = Module.finrank O M := by
  have : Module.FinitePresentation O M := Module.finitePresentation_of_projective O M
  have key : ∀ (K : Type) [Field K] [Algebra O K], Module.finrank K (K ⊗[O] M) =
      Module.rankAtStalk M (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O) := fun K _ _ => by
    have h := Module.rankAtStalk_baseChange (R := O) (M := M) (S := K) ⟨⊥, Ideal.isPrime_bot⟩
    rw [Module.rankAtStalk_eq_finrank_of_free] at h
    exact h.trans ((Module.isLocallyConstant_rankAtStalk (R := O) (M := M)).apply_eq_of_preconnectedSpace _ _)
  rw [key k, ← key (FractionRing O), (TensorProduct.isBaseChange O M (FractionRing O)).finrank_eq]

theorem exists_isLieBasis {k : Type} [Field k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G] {n : ℕ}
    (h : SmoothOfRelativeDimension n G.hom) : ∃ v : Fin n → (epsR k ⟶ G), IsLieBasis v := by
  obtain ⟨x, hx⟩ := ObjDim.univChart_of_relativeDimension G h
  exact ⟨_, Chart.basis_of_chart (G := G) hx⟩

theorem dim_eq_field {k O M : Type} [Field k] [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] {G A : Over (Sp k)} [GrpObj G] [IsCommMonObj G]
    [GrpObj A] [IsCommMonObj A] {a : OAct O G} {b : OAct O A} (t : Serre.IsTensor A b G a M)
    (hG : SmoothOfRelativeDimension 1 G.hom) {n : ℕ} (hA : SmoothOfRelativeDimension n A.hom) :
    n = Module.finrank O M := by
  obtain ⟨v, hv⟩ := exists_isLieBasis G hG
  obtain ⟨w, hw⟩ := exists_isLieBasis A hA
  have h1 : Module.finrank k (Serre.Lie a) = 1 :=
    (Module.finrank_eq_card_basis (Serre.Lie.basis a hv)).trans (Fintype.card_fin 1)
  have hb : Function.Bijective (algebraMap k (Module.End k (Serre.Lie a))) := by
    have := Module.Finite.of_basis (Serre.Lie.basis a hv)
    rw [← Algebra.finrank_eq_one_iff_bijective_algebraMap, Module.finrank_linearMap, h1]
  let e := RingEquiv.ofBijective _ hb
  let τ : O →+* k := e.symm.toRingHom.comp (Module.toModuleEnd k (Serre.Lie a))
  have hτ : Serre.Lie.eig a τ = ⊤ := eq_top_iff.2 fun u _ => Serre.Lie.mem_eig_iff.2 fun x =>
    (LinearMap.congr_fun (e.apply_symm_apply (Module.toModuleEnd k (Serre.Lie a) x)) u).symm
  letI : Algebra O k := τ.toAlgebra
  have e' := t.lieEquivScalar b (N := k)
    ((Serre.Lie.basis a hv).equivFun ≪≫ₗ LinearEquiv.funUnique (Fin 1) k k).symm hτ
  rw [← finrank_fibre O M k, e'.finrank_eq, Module.finrank_eq_card_basis (Serre.Lie.basis b hw),
    Fintype.card_fin]

theorem smoothOfRelativeDimension {S : Scheme.{0}} {O M : Type} [CommRing O] [IsDomain O] [AddCommGroup M]
    [Module O M] [Module.Finite O M] [Module.Projective O M] {G A : Over S} [GrpObj G] [IsCommMonObj G]
    [GrpObj A] [IsCommMonObj A] {a : OAct O G} {b : OAct O A} (t : Serre.IsTensor A b G a M)
    (hab : IsAbelianScheme G) (hG : SmoothOfRelativeDimension 1 G.hom) :
    SmoothOfRelativeDimension (Module.finrank O M) A.hom := by
  have hA : IsAbelianScheme A := t.isAbelianScheme hab
  have := hA.smooth
  have := hA.geomConnected
  choose n W hW hd using H1.exists_dim A.hom
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension (Module.finrank O M)) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension (Module.finrank O M)) W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  let k := A.left.residueField y
  let z : Sp k ⟶ A.left := A.left.fromSpecResidueField y
  have hz : ∀ u, z u = y := fun u => Scheme.fromSpecResidueField_apply y _
  let x : Sp k ⟶ S := z ≫ A.hom
  have : ConnectedSpace ↥(pullback A.hom x) :=
    GeometricallyConnected.geometrically_connectedSpace (f := A.hom) x _ _ (IsPullback.of_hasPullback _ _)
  let z' : Sp k ⟶ pullback A.hom x := pullback.lift z (𝟙 _) (Category.id_comp _).symm
  obtain ⟨m, hm⟩ := exists_dim_of_preconnected (pullback.snd A.hom x) (z' (default : PrimeSpectrum k))
  have e₁ : n y = m := H1.dim_base (IsPullback.of_hasPullback _ _) (hd y) hm (z' (default : PrimeSpectrum k)) (by
    have e : z' ≫ pullback.fst A.hom x = z := pullback.lift_fst _ _ _
    have e' := (congrArg (fun q : Sp k ⟶ A.left => q (default : PrimeSpectrum k)) e).trans (hz _)
    exact (congrArg (fun u => u ∈ W y) e').mpr (hW y))
  have hG' : SmoothOfRelativeDimension 1 (pullback.snd G.hom x) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hG
  have hdim := dim_eq_field (t.pullback x) hG' hm
  have hdim' : n y = Module.finrank O M := e₁.trans hdim
  rw [← hdim']
  exact hd y

end GlobalTheory.CM.TenDim

namespace GlobalTheory.CM

theorem tensor_smoothOfRelativeDimension :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (D : Datum H) (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (b : OAct (OK H) A), Nonempty (Serre.IsTensor A b C.P.A C.act D.La) → SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) A.hom := by
  rintro E _ _ _ H R _ ω C D A _ _ b ⟨t⟩
  obtain ⟨h1, h2, h3⟩ := (OK_isDedekindDomain_and_projective E H).2.2.2.2.2 D.La D.fin D.proj
  rw [← D.rank, ← h3]
  exact TenDim.smoothOfRelativeDimension t C.P.isAb (C.dim ▸ C.P.smoothDim)

end GlobalTheory.CM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmTensorSmoothOfRelativeDimensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmTensor_smoothOfRelativeDimension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (D : Datum H) (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (b : OAct (OK H) A), Nonempty (Serre.IsTensor A b C.P.A C.act D.La) → SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) A.hom := by
  first | exact @GlobalTheory.CM.tensor_smoothOfRelativeDimension | exact GlobalTheory.CM.tensor_smoothOfRelativeDimension | (intros; apply GlobalTheory.CM.tensor_smoothOfRelativeDimension <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueCmHermitianLatticeForm
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueCmHermitianLatticeForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def kFun {H : Host E} (D : Datum H) (ε : ℤˣ) (x y : D.La) : OK H :=
  (((ε : ℤ) * (D.EF (H.w0 • x) y - D.EF x y) : ℤ) : OK H) + (((ε : ℤ) * D.EF x y : ℤ) : OK H) * wK H

theorem kFun_coe {H : Host E} (D : Datum H) (ε : ℤˣ) (x y : D.La) : ((kFun D ε x y : OK H) : 𝓞 E) =
    (((ε : ℤ) * (D.EF (H.w0 • x) y - D.EF x y) : ℤ) : 𝓞 E) + (((ε : ℤ) * D.EF x y : ℤ) : 𝓞 E) * H.w0 := by
  simp only [kFun, wK, Subalgebra.coe_add, Subalgebra.coe_mul, SubringClass.coe_intCast]

theorem kform_w0_sq (H : Host E) : H.w0 * H.w0 = H.w0 - (((1 + H.d) / 4 : ℕ) : 𝓞 E) := by
  have h := congrArg (fun a : OK H => (a : 𝓞 E)) (GlobalTheory.T.integers_of_cm_field_conj_structure E H).2.2.2.1
  simp only [wK, Subalgebra.coe_add, SubmonoidClass.coe_pow, SubringClass.coe_natCast] at h
  linear_combination h

theorem kform_bar_w0 (H : Host E) : H.bar H.w0 = 1 - H.w0 := by
  obtain ⟨br, h1, h2, -⟩ := (GlobalTheory.T.integers_of_cm_field_conj_structure E H).2.2.1
  have h := congrArg (fun a : OK H => (a : 𝓞 E)) h2
  simp only [Subalgebra.coe_add, h1, Subalgebra.coe_one] at h
  simp only [wK] at h
  linear_combination h

theorem kform_skew {H : Host E} (D : Datum H) (x y : D.La) : D.EF y x = - D.EF x y := by
  have h := D.alt (x + y)
  simp only [map_add (f := _), LinearMap.add_apply, D.alt] at h
  linarith

theorem kFun_add_left {H : Host E} (D : Datum H) (ε : ℤˣ) (x x' y : D.La) :
    kFun D ε (x + x') y = kFun D ε x y + kFun D ε x' y := by
  simp only [kFun, smul_add, map_add (f := _), LinearMap.add_apply]
  push_cast; ring

theorem kFun_add_right {H : Host E} (D : Datum H) (ε : ℤˣ) (x y y' : D.La) :
    kFun D ε x (y + y') = kFun D ε x y + kFun D ε x y' := by
  simp only [kFun, map_add (f := _)]
  push_cast; ring

theorem kFun_zsmul {H : Host E} (D : Datum H) (ε : ℤˣ) (m : ℤ) (x y : D.La) :
    kFun D ε (m • x) y = (m : OK H) * kFun D ε x y := by
  simp only [kFun, smul_comm H.w0 m x, map_zsmul, LinearMap.smul_apply, smul_eq_mul]
  push_cast; ring

theorem kFun_w0 {H : Host E} (D : Datum H) (ε : ℤˣ) (x y : D.La) :
    kFun D ε (H.w0 • x) y = wK H * kFun D ε x y := by
  apply Subtype.ext
  have hw : H.w0 • H.w0 • x = H.w0 • x - (((1 + H.d) / 4 : ℕ) : ℤ) • x := by
    rw [smul_smul, kform_w0_sq, sub_smul, Nat.cast_smul_eq_nsmul, natCast_zsmul]
  have h2 := kform_w0_sq H
  rw [Subalgebra.coe_mul, kFun_coe, kFun_coe, hw]
  simp only [map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, wK]
  generalize ((1 + H.d) / 4 : ℕ) = N at *
  push_cast
  linear_combination (-((ε : ℤ) : 𝓞 E) * (D.EF x y : 𝓞 E)) * h2

theorem kFun_smul {H : Host E} (D : Datum H) (ε : ℤˣ) (a : OK H) (x y : D.La) :
    kFun D ε (a • x) y = a * kFun D ε x y := by
  obtain ⟨⟨m, n⟩, rfl, -⟩ := (GlobalTheory.T.integers_of_cm_field_conj_structure E H).2.1 a
  have : ((m : OK H) + (n : OK H) * wK H) • x = m • x + n • H.w0 • x := by
    rw [add_smul, mul_smul, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]; rfl
  simp only
  rw [this, kFun_add_left, kFun_zsmul, kFun_zsmul, kFun_w0]; ring

def kLin {H : Host E} (D : Datum H) (ε : ℤˣ) : D.La →ₗ[OK H] D.La →+ OK H where
  toFun x := AddMonoidHom.mk' (kFun D ε x) (kFun_add_right D ε x)
  map_add' x x' := by ext1 y; exact kFun_add_left D ε x x' y
  map_smul' a x := by ext1 y; exact kFun_smul D ε a x y

theorem kLin_apply {H : Host E} (D : Datum H) (ε : ℤˣ) (x y : D.La) : kLin D ε x y = kFun D ε x y := rfl

theorem kform_coeff_unique (H : Host E) {a b c d : ℤ}
    (h : (a : OK H) + (b : OK H) * wK H = (c : OK H) + (d : OK H) * wK H) : a = c ∧ b = d := by
  have := ((GlobalTheory.T.integers_of_cm_field_conj_structure E H).2.1 ((a : OK H) + (b : OK H) * wK H)).unique (y₁ := (a, b)) (y₂ := (c, d)) rfl h
  exact Prod.mk.inj this

theorem kLin_perfect {H : Host E} (D : Datum H) (ε : ℤˣ) (f : D.La →ₗ[OK H] OK H) :
    ∃! y, ∀ x, f x = kLin D ε x y := by
  have hε : (ε : ℤ) * ε = 1 := by rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  choose c hc using fun a => ((GlobalTheory.T.integers_of_cm_field_conj_structure E H).2.1 a).exists
  let b : D.La →+ ℤ := AddMonoidHom.mk' (fun x => -(ε : ℤ) * (c (f x)).2) (by
    intro x x'
    have : (((c (f (x + x'))).1 : ℤ) : OK H) + ((c (f (x + x'))).2 : OK H) * wK H =
        (((c (f x)).1 + (c (f x')).1 : ℤ) : OK H) + (((c (f x)).2 + (c (f x')).2 : ℤ) : OK H) * wK H := by
      rw [← hc, map_add (f := _)]
      have h1 := hc (f x)
      have h2 := hc (f x')
      push_cast
      linear_combination h1 + h2
    rw [(kform_coeff_unique H this).2]; ring)
  obtain ⟨y, hy⟩ := D.unimod.2 b.toIntLinearMap
  have hb : ∀ x, (ε : ℤ) * D.EF x y = (c (f x)).2 := by
    intro x
    rw [kform_skew, hy]
    change (ε : ℤ) * -(-(ε : ℤ) * (c (f x)).2) = _
    linear_combination (c (f x)).2 * hε
  have hint : ∀ x, ∃ m : ℤ, f x - kFun D ε x y = m := by
    intro x
    refine ⟨(c (f x)).1 - (ε : ℤ) * (D.EF (H.w0 • x) y - D.EF x y), ?_⟩
    have h1 := hc (f x)
    rw [kFun, hb]
    push_cast
    linear_combination h1
  refine ⟨y, fun x => ?_, fun y' hy' => ?_⟩
  · obtain ⟨m, hm⟩ := hint x
    obtain ⟨m', hm'⟩ := hint (wK H • x)
    rw [map_smul, kFun_smul, smul_eq_mul, ← mul_sub, hm] at hm'
    have : ((0 : ℤ) : OK H) + (m : OK H) * wK H = (m' : OK H) + ((0 : ℤ) : OK H) * wK H := by
      push_cast; linear_combination hm'
    rw [(kform_coeff_unique H this).2] at hm
    rw [kLin_apply, ← sub_eq_zero, hm, Int.cast_zero]
  · apply D.unimod.1
    ext x
    have h1 := (hc (f x)).symm.trans (hy' x)
    have h2 := (kform_coeff_unique H h1).2
    rw [kform_skew D x y', kform_skew D x y]
    have h3 := hb x
    linear_combination (ε : ℤ) * (h2 + h3) + (D.EF x y' - D.EF x y) * hε

theorem exists_kForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (ε : ℤˣ), ∃ h : D.La →ₗ[OK H] D.La →+ OK H, IsKForm D ε (fun x y => h x y) ∧ (∀ h' : D.La → D.La → OK H, IsKForm D ε h' → h' = fun x y => h x y) ∧ (∀ x y, ((h y x : OK H) : 𝓞 E) = H.bar (h x y : OK H)) ∧ (∀ (s : 𝓞 E) x y, h (s • x) y = h x (H.bar s • y)) ∧ (∀ x, ((h x x : OK H) : 𝓞 E) = (((ε : ℤ) * D.EF (H.w0 • x) x : ℤ) : 𝓞 E)) ∧ (∀ f : D.La →ₗ[OK H] OK H, ∃! y, ∀ x, f x = h x y) ∧ ∃ (n : ℕ) (x y : Fin n → D.La), ∀ a, a = ∑ i, h a (y i) • x i := by
  intro E _ _ _ H D ε
  refine ⟨kLin D ε, kFun_coe D ε, fun h' hh => ?_, fun x y => ?_, fun s x y => ?_, fun x => ?_,
    kLin_perfect D ε, ?_⟩
  · funext x y
    exact Subtype.ext ((hh x y).trans (kFun_coe D ε x y).symm)
  · have h1 : D.EF (H.w0 • y) x = D.EF (H.w0 • x) y - D.EF x y := by
      rw [D.adj, kform_bar_w0, sub_smul, one_smul, map_sub, kform_skew D x y, kform_skew D (H.w0 • x) y]
      ring
    rw [kLin_apply, kLin_apply, kFun_coe, kFun_coe, h1, kform_skew D x y, map_add (f := _), map_mul, map_intCast,
      map_intCast, kform_bar_w0]
    push_cast; ring
  · rw [kLin_apply, kLin_apply, kFun, kFun, smul_comm H.w0 s x, D.adj, D.adj s]
  · rw [kLin_apply, kFun_coe, D.alt]
    push_cast; ring
  · obtain ⟨h1, h2, -⟩ := (GlobalTheory.T.integers_of_cm_field_conj_structure E H).2.2.2.2.2 D.La D.fin D.proj
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' (OK H) D.La
    obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
    choose y hy using fun i : Fin n => (kLin_perfect D ε ((LinearMap.proj i).comp s)).exists
    refine ⟨n, fun i => π (Pi.single i 1), y, fun a => ?_⟩
    have ha : π (s a) = a := LinearMap.congr_fun hs a
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← ha, ← Finset.univ_sum_single (s a), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hy, ← map_smul, ← Pi.single_smul, smul_eq_mul, _root_.mul_one]
    rfl

end GlobalTheory.CM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueCmHermitianLatticeFormStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_cmHermitianLatticeForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (ε : ℤˣ), ∃ h : D.La →ₗ[OK H] D.La →+ OK H, IsKForm D ε (fun x y => h x y) ∧ (∀ h' : D.La → D.La → OK H, IsKForm D ε h' → h' = fun x y => h x y) ∧ (∀ x y, ((h y x : OK H) : 𝓞 E) = H.bar (h x y : OK H)) ∧ (∀ (s : 𝓞 E) x y, h (s • x) y = h x (H.bar s • y)) ∧ (∀ x, ((h x x : OK H) : 𝓞 E) = (((ε : ℤ) * D.EF (H.w0 • x) x : ℤ) : 𝓞 E)) ∧ (∀ f : D.La →ₗ[OK H] OK H, ∃! y, ∀ x, f x = h x y) ∧ ∃ (n : ℕ) (x y : Fin n → D.La), ∀ a, a = ∑ i, h a (y i) • x i := by
  first | exact @GlobalTheory.CM.exists_kForm | exact GlobalTheory.CM.exists_kForm | (intros; apply GlobalTheory.CM.exists_kForm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsTenBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM

theorem isTen_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (D : Datum H) (h : D.La → D.La → OK H) (T : PAT H (Sp R)) (t : IsTen C D h T) (R' : Type) [CommRing R'] (ω' : R') (C' : Ell H R' ω') (f : R →+* R') (φ : C'.P.A.left ⟶ C.P.A.left) (T' : PAT H (Sp R')) (m : SABMap T'.t T.t (spMap f)), EllMap C' C f φ → ∃ t' : IsTen C' D h T', ∀ a, (t'.ten.tmul a).left ≫ m.φ = φ ≫ (t.ten.tmul a).left := by
  intro E _ _ _ H R _ ω C D h T t R' _ ω' C' f φ T' m hC
  obtain ⟨-, ⟨-, hφ, iC⟩, -, hact⟩ := hC
  have hφ' : Serre.IsLinearPullback C'.act C.act (spMap f) φ := ⟨hφ, hact⟩
  have hψ : Serre.IsLinearPullback (Serre.comapAct T'.t.act (algebraMap (OK H) (𝓞 E)))
      (Serre.comapAct T.t.act (algebraMap (OK H) (𝓞 E))) (spMap f) m.φ := ⟨m.cart, fun c => m.act _⟩
  have iT : LBIso (T.t.PP.L.pull m.φ) T'.t.PP.L :=
    LBIso.symm (show LBIso T'.t.PP.L (T.t.PP.L.pull m.φ) from m.lin.imp fun _ h => h.1)
  have e := fun a => t.ten.baseChange_tmul hφ' hψ a
  refine ⟨⟨t.ten.baseChange hφ' hψ, fun s a => ?_, fun a b => ?_⟩, e⟩
  · refine Over.OverMorphism.ext (m.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    refine (e (s • a)).trans ?_
    rw [t.lin, Over.comp_left, Over.comp_left, Category.assoc, m.act s, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ (T.t.act.act s).left) (e a).symm
  · exact lamEq_baseChange _ _ (spMap f) C.P.A C.P.A T.t.G C.P.A C'.P.A C'.P.A T'.t.G C'.P.A φ φ m.φ φ
      hφ.1.w hφ.1.w m.cart hφ T.t.PP.L C.P.L T'.t.PP.L C'.P.L T.t.PP.isLB C.P.isLB T'.t.PP.isLB C'.P.isLB iT iC
      _ _ _ _ _ _ _ _ (e a) (e b) (hact _) ((Category.id_comp _).trans (Category.comp_id _).symm) (t.lam a b)

end GlobalTheory.CM

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsKroneckerCmLogPeriodEqConst
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CM

namespace GlobalTheory.LamF

theorem exists_kronecker_logOm_re (E : Type) [Field E] [NumberField E] {d d' : ℕ} (h : d' = d) [Fact d.Prime]
    [NeZero d] (hd : d % 4 = 3) :
    ∃ (_ : NeZero d') (χ : DirichletCharacter ℂ d'), IsKroneckerChar χ ∧ (GlobalTheory.CM.logOm E χ).re =
      Real.eulerMascheroniConstant + Real.log (2 * Real.pi / rootDiscr E) -
        (deriv (DirichletCharacter.LFunction ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ))) 1 /
          DirichletCharacter.LFunction ((quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)) 1).re := by
  subst h
  exact ⟨inferInstance, _, isKroneckerChar_quadraticChar hd, by
    rw [GlobalTheory.CM.logOm, Complex.sub_re, Complex.ofReal_re]⟩

theorem exists_kronecker_logOm_eq : ∀ (D : D7) (Q : Par D), Q.PinHost → ∀ large₂ : SizeData₂ D,
    ∃ (_ : NeZero Q.H.d) (χ : DirichletCharacter ℂ Q.H.d),
      IsKroneckerChar χ ∧ (GlobalTheory.CM.logOm D.host.E χ).re = large₂.logOm := by
  intro D Q hp large₂
  haveI : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩
  haveI : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩
  have hd : D.host.d % 4 = 3 := by
    have := Q.H.d_mod
    rw [hp.1] at this
    omega
  obtain ⟨i, χ, hχ, e⟩ := exists_kronecker_logOm_re D.host.E hp.1 hd
  refine ⟨i, χ, hχ, e.trans ?_⟩
  have hv : 2 * Real.pi / rootDiscr D.host.E = Real.pi / D.host.v := by
    rw [Formalism.BasicNotions.Host.v, Formalism.BasicNotions.Host.rdE, rootDiscr_def, Int.cast_abs, one_div, div_div_eq_mul_div, mul_comm]
  rw [hv, SizeData₂.logOm, large₂.logDerivative_at_one_eq]
  rfl

end GlobalTheory.LamF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPosKeyArchAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section
namespace GlobalTheory.LamF.KeyArch

theorem pos_of_isArchNorm (hU : ThetaUnifAV) (x : KeyIn ℂ) {nth nη : ℝ} (h : KeyPow.IsArchNorm x nth nη) :
    0 < nth ∧ 0 < nη := by
  obtain ⟨u, Hm, W, χ, θ, Fd, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := h
  obtain ⟨u', τ, M, a, b, c, -, -, -, -, -, -, -, -, -, -, e⟩ :=
    keyIn_normal_form_and_archimedean_constant hU x u Hm W χ θ Fd nth nη h₁ h₂ h₃ h₄ h₅ h₆ h₇
  have p₁ : 0 ≤ nth :=
    h₆ ▸ div_nonneg (MeasureTheory.integral_nonneg fun z => by positivity) ENNReal.toReal_nonneg
  have p₂ : 0 ≤ nη := h₇ ▸ by positivity
  have hne : ‖M.det ^ 4 / c ^ 8‖ * nth ^ 4 * nη ^ 2 ≠ 0 := by
    rw [e]; have := Real.pi_pos; positivity
  have q₁ := right_ne_zero_of_mul (left_ne_zero_of_mul hne)
  have q₂ := right_ne_zero_of_mul hne
  exact ⟨p₁.lt_of_ne' fun h0 => q₁ (by rw [h0]; norm_num), p₂.lt_of_ne' fun h0 => q₂ (by rw [h0]; norm_num)⟩

theorem exists_pos_keyArchAt : ThetaUnifAV → ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (σ : K →+* ℂ), ∃ t n : ℝ, 0 < t ∧ 0 < n ∧ ∀ T abelian₂ : MLine K, T.n σ = t → abelian₂.n σ = n → KeyArchAt x T abelian₂ σ := by
  intro hU K _ _ x σ
  obtain ⟨x', hx⟩ := KeyPow.exists_keyPB x σ
  obtain ⟨nth, nη, h⟩ := KeyPow.exists_isArchNorm hU x'
  obtain ⟨p₁, p₂⟩ := pos_of_isArchNorm hU x' h
  obtain ⟨u, Hm, W, χ, θ, Fd, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := h
  refine ⟨Real.sqrt nth, Real.sqrt nη⁻¹, Real.sqrt_pos.2 p₁, Real.sqrt_pos.2 (inv_pos.2 p₂), fun T abelian₂ hT hL =>
    ⟨x', u, Hm, W, χ, θ, Fd, hx, h₁, h₂, h₃, h₄, h₅, ?_, ?_⟩⟩
  · rw [hT, Real.sq_sqrt p₁.le, h₆]
  · rw [hL, Real.sq_sqrt (inv_pos.2 p₂).le, h₇, inv_div]

end GlobalTheory.LamF.KeyArch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGenOfFieldExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.FieldTriv

theorem exists_gen_of_isPullback {k k' : Type} [Field k] [Field k'] (β : k →+* k') {X X' : Scheme.{0}}
    (f : X ⟶ Sp k) [IsProper f] [GeometricallyIntegral f] (π : X' ⟶ X) (p : X' ⟶ Sp k')
    (H : IsPullback π p f (spMap β)) {N : LB X} (hN : N.IsLB) (t : (N.pull π).Gen) (ht : t.IsGen) :
    ∃ u : N.Gen, u.IsGen := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : IsIntegral X' := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
  have : IsIso p.appTop := ProperFunctions.isIso_appTop_baseChange_of_field H
  have hflat : β.Flat := by
    let _ := β.toAlgebra
    exact inferInstanceAs (Module.Flat k k')
  have lift : ∀ x : X, ∃ y, π y = x := fun x => by
    obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback H x (⊥ : PrimeSpectrum k')
      (Subsingleton.elim (α := PrimeSpectrum k) _ _)
    exact ⟨y, hy⟩
  obtain ⟨σ, hσ⟩ := GenericTriv.exists_sec_isUnit β hflat f π p H
    (ConcreteCategory.bijective_of_isIso p.appTop).2 hN t ht
  have hu : ∀ i, IsUnit (σ.f i) := fun i => X.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => by
    obtain ⟨y, rfl⟩ := lift x
    have := hσ y i hx
    rw [gs_stalkMap π y _ hx, isUnit_map_iff] at this
    exact (congrArg IsUnit (gs_eq (𝟙 X) (π y) (N.U i) hx _)).mp this
  exact ⟨⟨fun i => (hu i).unit⟩, fun i i' => Units.ext (σ.compat i i')⟩

theorem exists_gen_of_field_extension : ∀ (k k' : Type) [Field k] [Field k'] (β : k →+* k') (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → ∀ (X' : Scheme.{0}) (π : X' ⟶ A.left) (p : X' ⟶ Sp k'), IsPullback π p A.hom (spMap β) → ∀ N : LB A.left, N.IsLB → (∃ t : LB.Gen (N.pull π), t.IsGen) → ∃ t : LB.Gen N, t.IsGen := by
  intro k k' _ _ β A _ hA X' π p H N hN ⟨t, ht⟩
  have := hA.proper
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth hA.geomConnected
  exact exists_gen_of_isPullback β A.hom π p H hN t ht

end GlobalTheory.FieldTriv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EllMapCancelAndSabMapCancel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.Factor

theorem dualMapR_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R'') :
    Chart.dualMapR (f'.comp f) = (Chart.dualMapR f').comp (Chart.dualMapR f) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [Chart.dualMapR]

theorem ellMap_cancel {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R R' R'' : Type} [CommRing R]
    [CommRing R'] [CommRing R''] {f : R →+* R'} {f' : R' →+* R''} {ω : R} {ω' : R'} {ω'' : R''} {C : Ell H R ω}
    {C' : Ell H R' ω'} {C'' : Ell H R'' ω''} {φ : C'.P.A.left ⟶ C.P.A.left} {ψ : C''.P.A.left ⟶ C.P.A.left}
    (h : EllMap C' C f φ) (k : EllMap C'' C (f'.comp f) ψ) :
    ∃ φ' : C''.P.A.left ⟶ C'.P.A.left, EllMap C'' C' f' φ' ∧ φ' ≫ φ = ψ := by
  obtain ⟨hω, ⟨hg, hp, hL⟩, hv, ha⟩ := h
  obtain ⟨kω, ⟨kg, kp, kL⟩, kv, ka⟩ := k
  rw [← spMap_comp_spMap] at kp
  have w : ψ ≫ C.P.A.hom = (C''.P.A.hom ≫ spMap f') ≫ spMap f := by rw [kp.1.w, Category.assoc]
  obtain ⟨l, h₁, h₂⟩ : ∃ l : C''.P.A.left ⟶ C'.P.A.left, l ≫ φ = ψ ∧ l ≫ C'.P.A.hom = C''.P.A.hom ≫ spMap f' :=
    ⟨hp.1.lift _ _ w, hp.1.lift_fst _ _ w, hp.1.lift_snd _ _ w⟩
  subst h₁
  refine ⟨l, ⟨hω ▸ kω, ⟨kg.trans hg.symm, hp.cancel kp h₂, ?_⟩, ?_, fun a => ?_⟩, rfl⟩
  · have e : LBIso (C.P.L.pull (l ≫ φ)) (C'.P.L.pull l) :=
      LBIso.chartPull (chartPullSame C.P.L _ _ _ l fun _ => rfl) (Geo.Tor.chartPullPull C'.P.L l l rfl) hL
    exact LBIso.trans (pull_isLB C'.P.isLB _) (pull_isLB C.P.isLB _) C''.P.isLB e.symm kL
  · unfold IsVecOver at hv kv ⊢
    apply hp.1.hom_ext
    · rw [Category.assoc, kv, Category.assoc, hv, dualMapR_comp, ← spMap_comp_spMap, Category.assoc]
    · rw [Category.assoc, h₂, ← Category.assoc, Over.w C''.v, Category.assoc, Over.w C'.v]
      refine (spMap_comp_spMap _ _).trans (Eq.trans ?_ (spMap_comp_spMap _ _).symm)
      congr 1
      ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · apply hp.1.hom_ext
    · rw [Category.assoc, ka, Category.assoc, Category.assoc, ha]
    · rw [Category.assoc, h₂, ← Category.assoc, Over.w, Category.assoc, Over.w, h₂]

theorem ellMap_cancel_and_sabMap_cancel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' R'' : Type) [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R''),
  (∀ (ω : R) (ω' : R') (ω'' : R'') (C : Ell H R ω) (C' : Ell H R' ω') (C'' : Ell H R'' ω'') (φ : C'.P.A.left ⟶ C.P.A.left) (ψ : C''.P.A.left ⟶ C.P.A.left), EllMap C' C f φ → EllMap C'' C (f'.comp f) ψ → ∃ φ' : C''.P.A.left ⟶ C'.P.A.left, EllMap C'' C' f' φ' ∧ φ' ≫ φ = ψ) ∧
  ∀ (S : Scheme.{0}) (y : Sp R' ⟶ S) (y' : Sp R'' ⟶ S) (t : SAB H S) (t' : SAB H (Sp R')) (t'' : SAB H (Sp R'')) (m : SABMap t' t y) (n : SABMap t'' t y'), spMap f' ≫ y = y' → ∃ m' : SABMap t'' t' (spMap f'), m'.φ ≫ m.φ = n.φ := by
  intro E _ _ _ H R R' R'' _ _ _ f f'
  refine ⟨fun _ _ _ _ _ _ _ _ h k => ellMap_cancel h k, fun S y y' t t' t'' m n e => ?_⟩
  subst e
  obtain ⟨m', h⟩ := ObjMaps.exists_sab_cancel m n
  exact ⟨m', h.symm⟩

end GlobalTheory.CM.Factor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LocZeroTranslDiffComp
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.TripleProd

open GlobalTheory.CechPic

section Local

variable {Y Y' B B' : Scheme.{0}}

def LocZero (π : Y ⟶ B) (c : Pic Y) : Prop :=
  ∀ p : B, ∃ V : B.Opens, p ∈ V ∧ pull (π ⁻¹ᵁ V).ι c = 0

theorem pull_eq_zero_of_range {W : Y.Opens} {c : Pic Y} (H : pull W.ι c = 0) (h : Y' ⟶ Y) (hW : ∀ y, h y ∈ W) :
    pull h c = 0 := by
  have hr : Set.range h ⊆ Set.range W.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hW y
  rw [← IsOpenImmersion.lift_fac W.ι h hr, pull_comp, H, map_zero]

theorem LocZero.sub {π : Y ⟶ B} {c d : Pic Y} (H : LocZero π c) (H' : LocZero π d) : LocZero π (c - d) := by
  intro p
  obtain ⟨V, hV, t⟩ := H p
  obtain ⟨V', hV', t'⟩ := H' p
  refine ⟨V ⊓ V', ⟨hV, hV'⟩, ?_⟩
  rw [map_sub, pull_eq_zero_of_range t (π ⁻¹ᵁ (V ⊓ V')).ι fun y => y.2.1,
    pull_eq_zero_of_range t' (π ⁻¹ᵁ (V ⊓ V')).ι fun y => y.2.2, sub_zero]

theorem LocZero.pull_over {π : Y ⟶ B} {c : Pic Y} (H : LocZero π c) {π' : Y' ⟶ B} (h : Y' ⟶ Y) (sq : h ≫ π = π') :
    LocZero π' (pull h c) := by
  subst sq
  intro p
  obtain ⟨V, hV, t⟩ := H p
  refine ⟨V, hV, ?_⟩
  rw [← pull_comp]
  exact pull_eq_zero_of_range t _ fun y => y.2

theorem locZero_base (π : Y ⟶ B) (c : Pic B) : LocZero π (pull π c) := by
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  intro p
  obtain ⟨i, hi⟩ := exists_chart hL p
  refine ⟨L.U i, hi, ?_⟩
  rw [← pull_comp]
  exact (cls_eq_zero_iff (pull_isLB hL _)).2
    (BoxKernel.gen_of_chart (pull_isLB hL _) (fun _ => i) fun y => mem_pull.2 y.2)

theorem locZero_iff (π : Y ⟶ B) {N : LB Y} (hN : N.IsLB) :
    (∀ p : B, ∃ V : B.Opens, p ∈ V ∧ ∃ c : LB.Gen (N.pull (π ⁻¹ᵁ V).ι), c.IsGen) ↔ LocZero π (cls N hN) :=
  forall_congr' fun _ => exists_congr fun _ => and_congr_right fun _ =>
    (cls_eq_zero_iff (pull_isLB hN _)).symm

end Local

section Kernel

variable {S : Scheme.{0}} {A G H : Over S} [GrpObj A] [GrpObj G] [GrpObj H]

theorem cls_translDiff {L : LB A.left} (hL : L.IsLB) {T : Over S} (x : T ⟶ A) :
    cls (Out.translDiff A L x) (LB.isLB_linComb hL _ _) =
      pull ((fst T A ≫ x) * snd T A).left (cls L hL) - pull (snd T A).left (cls L hL) := by
  refine (cls_linComb hL _ _ _).trans ?_
  rw [Fin.sum_univ_two]
  show (1 : ℤ) • pull ((fst T A ≫ x) * snd T A).left (cls L hL) + (-1 : ℤ) • pull (snd T A).left (cls L hL) = _
  rw [one_zsmul, neg_one_zsmul, sub_eq_add_neg]

theorem locZero_translDiff_comp {N : LB A.left} {L : LB G.left} (hN : N.IsLB) (hL : L.IsLB) (b : Pic H.left)
    (p : A ⟶ G) (q : A ⟶ H) [IsMonHom p] [IsMonHom q] (u : G ⟶ A) (hp : u ≫ p = 𝟙 G) (hq : u ≫ q = 1)
    (e : cls N hN = pull p.left (cls L hL) + pull q.left b) {T : Over S} (x : T ⟶ A)
    (hx : LocZero (fst T A).left (cls (Out.translDiff A N x) (LB.isLB_linComb hN _ _))) :
    LocZero (fst T G).left (cls (Out.translDiff G L (x ≫ p)) (LB.isLB_linComb hL _ _)) := by
  have H₁ := hx.pull_over (π' := (fst T G).left) (T ◁ u).left (congrArg (fun q => q.left) (whiskerLeft_fst T u))
  have H₂ := (H₁.sub (locZero_base (fst T G).left (pull (x ≫ q).left b))).sub
    (locZero_base (fst T G).left (-pull (1 : T ⟶ H).left b))
  have e₁ : T ◁ u ≫ ((fst T A ≫ x) * snd T A) ≫ p = (fst T G ≫ x ≫ p) * snd T G := by
    rw [MonObj.mul_comp, MonObj.comp_mul, Category.assoc, whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, hp,
      Category.comp_id]
  have e₂ : T ◁ u ≫ ((fst T A ≫ x) * snd T A) ≫ q = fst T G ≫ x ≫ q := by
    rw [MonObj.mul_comp, MonObj.comp_mul, Category.assoc, whiskerLeft_fst_assoc, whiskerLeft_snd_assoc, hq,
      MonObj.comp_one, _root_.mul_one]
  have e₃ : T ◁ u ≫ snd T A ≫ p = snd T G := by rw [whiskerLeft_snd_assoc, hp, Category.comp_id]
  have e₄ : T ◁ u ≫ snd T A ≫ q = fst T G ≫ (1 : T ⟶ H) := by
    rw [whiskerLeft_snd_assoc, hq, MonObj.comp_one, MonObj.comp_one]
  convert H₂ using 1
  rw [cls_translDiff hL, cls_translDiff hN, e]
  simp only [map_sub, map_add (f := _), map_neg, ← pull_comp, ← Over.comp_left, e₁, e₂, e₃, e₄]
  abel

theorem kTriv_prod {N : LB (G ⊗ H).left} {L : LB G.left} {L' : LB H.left} (hN : N.IsLB) (hL : L.IsLB)
    (hL' : L'.IsLB) (e : cls N hN = pull (fst G H).left (cls L hL) + pull (snd G H).left (cls L' hL'))
    (hK : Out.KTriv G L) (hK' : Out.KTriv H L') : Out.KTriv (G ⊗ H) N := by
  intro R _ t x hx
  have hx' := (locZero_iff _ (LB.isLB_linComb hN _ _)).1 hx
  have h₁ : x ≫ fst G H = 1 := hK R t _ ((locZero_iff _ (LB.isLB_linComb hL _ _)).2
    (locZero_translDiff_comp hN hL _ (fst G H) (snd G H) (lift (𝟙 G) 1) (lift_fst _ _) (lift_snd _ _) e x hx'))
  have h₂ : x ≫ snd G H = 1 := hK' R t _ ((locZero_iff _ (LB.isLB_linComb hL' _ _)).2
    (locZero_translDiff_comp hN hL' _ (snd G H) (fst G H) (lift 1 (𝟙 H)) (lift_snd _ _) (lift_fst _ _)
      (e.trans (add_comm _ _)) x hx'))
  show x = 1
  apply CartesianMonoidalCategory.hom_ext
  · rw [h₁, MonObj.one_comp]
  · rw [h₂, MonObj.one_comp]

end Kernel

section Cube

variable {S : Scheme.{0}} {A G : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj G] [IsCommMonObj G] {n : ℕ}

def cubeCls {T : Over S} (x : Fin n → (T ⟶ G)) (c : Pic G.left) : Pic T.left :=
  ∑ I : ULift.{0} (Finset (Fin n)), ((-1 : ℤ) ^ (n - I.down.card)) • pull (psum G x I.down).left c

theorem cls_cubeLB {T : Over S} (x : Fin n → (T ⟶ G)) {L : LB G.left} (hL : L.IsLB) :
    cls (cubeLB G x L) (LB.isLB_linComb hL _ _) = cubeCls x (cls L hL) :=
  cls_linComb hL _ _ _

theorem pull_cubeCls {T T' : Over S} (ρ : T' ⟶ T) (x : Fin n → (T ⟶ G)) (c : Pic G.left)
    (y : Fin n → (T' ⟶ G)) (h : ∀ i, y i = ρ ≫ x i) : cubeCls y c = pull ρ.left (cubeCls x c) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [cubeCls, cubeCls, map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, ← pull_comp, PrimNorm.psum_pre ρ x y h]

end Cube

section Triple

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S) {T : Over S}

end Triple

end GlobalTheory.TripleProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HomExtDvrOfCardTorsion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem homExtDvr_of_card_torsion : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → HomExtDvr := by
  intro h
  exact homExtDvr_iff.2 (GlobalTheory.existsUnique_hom_extension_semiAbelian_dvr
    (GlobalTheory.AbelianSubgroupFinite.finite_of_no_torsion h))

end GlobalTheory.CM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPureVectorsPeriodsSpan
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem span_pure_periods_eq_top {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe) {p q : ℕ} (Z : CMLat hP p q) :
    Submodule.span ℂ {v : Fin g → ℂ | ∃ (ε : ℤˣ) (a : PureType.lat hP (((ε : ℤ) : ℂ) * H.rt0)), Pe a = v} = ⊤ := by
  set W := Submodule.span ℂ {v : Fin g → ℂ | ∃ (ε : ℤˣ) (a : PureType.lat hP (((ε : ℤ) : ℂ) * H.rt0)), Pe a = v}
  obtain ⟨n, hn, h⟩ := Z.span
  have key : ∀ a, Pe a ∈ W := by
    intro a
    obtain ⟨x, hx⟩ := h a
    have h1 : (n : ℂ) • Pe a ∈ W := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, hx, map_sum]
      refine W.sum_mem fun j _ => Submodule.subset_span ?_
      have h2 := Z.pure j (x j)
      rcases j with j | j
      · exact ⟨1, ⟨_, by simpa using h2⟩, rfl⟩
      · exact ⟨-1, ⟨_, by simpa using h2⟩, rfl⟩
    exact (W.smul_mem_iff (Nat.cast_ne_zero.2 hn.ne')).1 h1
  have h3 : Submodule.span ℝ (Set.range Pe) ≤ W.restrictScalars ℝ :=
    Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact key a)
  rw [hP.2.2.2.1] at h3
  exact eq_top_iff.2 fun v _ => h3 Submodule.mem_top

theorem exists_pure_vectors_periods_span :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Pe : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty Pe) (p q : ℕ) (Z : CMLat hP p q), ∃ (ε : Fin (Module.finrank ℚ E / 2 * (D.p + D.q)) → ℤˣ) (a : ∀ i, PureType.lat hP (((ε i : ℤ) : ℂ) * H.rt0)), ∀ z : Fin g → ℂ, ∃ c : Fin (Module.finrank ℚ E / 2 * (D.p + D.q)) → ℂ, z = ∑ i, c i • Pe (a i) := by
  intro E _ _ _ H D g ty Pe hP p q Z
  have h1 := (FibreExp.free_finite_finrank_of_isPeriod hP).2.2
  rw [datum_finrank_int D] at h1
  have hs := span_pure_periods_eq_top hP Z
  have h2 := Submodule.exists_fun_fin_finrank_span_eq ℂ
    {v : Fin g → ℂ | ∃ (ε : ℤˣ) (a : PureType.lat hP (((ε : ℤ) : ℂ) * H.rt0)), Pe a = v}
  rw [hs, finrank_top, Module.finrank_fin_fun] at h2
  have hg : Module.finrank ℚ E / 2 * (D.p + D.q) = g := by omega
  rw [hg]
  obtain ⟨f, hf, hsp, -⟩ := h2
  choose ε a ha using hf
  refine ⟨ε, a, fun z => ?_⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hsp ▸ Submodule.mem_top (x := z))
  exact ⟨c, by simp [ha, hc]⟩

end GlobalTheory.CM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LeftEqOfIsLieCombSingle
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF.LetterEigen

theorem prod_ofFn_eq_single {M : Type*} [Monoid M] :
    ∀ {n : ℕ} (u : Fin n → M) (i : Fin n), (∀ j, j ≠ i → u j = 1) → (List.ofFn u).prod = u i
  | 0, _, i, _ => i.elim0
  | n + 1, u, i, h => by
    rw [List.ofFn_succ, List.prod_cons]
    refine Fin.cases (motive := fun i => (∀ j, j ≠ i → u j = 1) →
      u 0 * (List.ofFn fun k : Fin n => u k.succ).prod = u i) (fun h => ?_) (fun i h => ?_) i h
    · have hprod : (List.ofFn fun k : Fin n => u k.succ).prod = 1 :=
        List.prod_eq_one (List.forall_mem_ofFn_iff.mpr fun k => h _ (Fin.succ_ne_zero k))
      rw [hprod, _root_.mul_one]
    · rw [h 0 (Fin.succ_ne_zero i).symm, _root_.one_mul]
      exact prod_ofFn_eq_single (fun k : Fin n => u k.succ) i
        (fun j hj => h _ (fun e => hj (Fin.succ_injective _ e)))

theorem left_eq_of_isLieComb_single {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n : ℕ}
    {v : Fin n → (epsR R ⟶ G)} (hv : ∀ i, IsTangent (v i)) (i : Fin n) (t : R) {w : epsR R ⟶ G}
    (hw : IsLieComb (Pi.single i t) v w) : w.left = spMap (epsScaleR t) ≫ (v i).left := by
  obtain ⟨u, hu, rfl⟩ := hw
  rw [prod_ofFn_eq_single u i, hu i, Pi.single_eq_same]
  intro j hj
  have h0 := (LieMultiple.isLieComb_one_iff (0 : R) (v j) 1).1
    ((LieMultiple.lieMultiple_calculus R G G (v j) 1 1 0 0).2.2.2.2.2 (hv j))
  apply Over.OverMorphism.ext
  rw [hu j, Pi.single_eq_of_ne hj, h0]

theorem exists_scale_of_eigen {K : Type} [Field K] [NumberField K] {A B : Over (Sp (𝓞 K))} {A' B' : Over (Sp K)}
    [GrpObj A'] [GrpObj B'] {n : ℕ} {v : Fin n → (epsR K ⟶ A')} (hv : ∀ i, IsTangent (v i)) (i : Fin n) (t : K)
    (φA : A'.left ⟶ A.left) (φB : B'.left ⟶ B.left) (α : A ⟶ A) (β : B ⟶ B) (F : A ⟶ B) (hF : α ≫ F = F ≫ β)
    {w₁ : epsR K ⟶ A'} (hw₁ : IsLieComb (Pi.single i t) v w₁) (he : (v i).left ≫ φA ≫ α.left = w₁.left ≫ φA)
    {w : epsR K ⟶ B'} (hw : w.left ≫ φB = (v i).left ≫ φA ≫ F.left) :
    ∃ w' : epsR K ⟶ B', IsLieComb ![t] ![w] w' ∧ w.left ≫ φB ≫ β.left = w'.left ≫ φB := by
  have hc : IsLieComb ![t] ![w] (Chart.spMap (Chart.scaleD t) ≫ w) :=
    (LieMultiple.isLieComb_one_iff_comp t w _).2 rfl
  refine ⟨_, hc, ?_⟩
  have hF' : α.left ≫ F.left = F.left ≫ β.left := by
    rw [← Over.comp_left, hF, Over.comp_left]
  rw [(LieMultiple.isLieComb_one_iff t w _).1 hc, Category.assoc, hw, reassoc_of% hw, ← hF', reassoc_of% he,
    left_eq_of_isLieComb_single hv i t hw₁, Category.assoc]

theorem letter_eigen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (l : Level H) (c : Coeff l) (nΨ n' f : ℕ) (o : LamObj c nΨ n') (La : ℝ), LamObjGood o f La → ∀ L : LamLetters o, L.IsGood → ∀ (b : E →+* ℂ) (i : Fin (L.m b)) (w : epsR o.K₁ ⟶ o.xB.P.A), L.IsLetter (L.e ⟨b, i⟩) w → ∀ a : 𝓞 E, ∃ w' : epsR o.K₁ ⟶ o.xB.P.A, IsLieComb ![labK c o.K₁ b (a : E)] ![w] w' ∧ w.left ≫ o.φB ≫ (o.oa.act a).left = w'.left ≫ o.φB := by
  intro E _ _ _ _ H l c nΨ n' f o La ho L hL b i w hw a
  obtain ⟨-, -, -, -, -, -, -, -, -, hΨ, h', eΨ, e', -⟩ := ho
  have hb := hL.2.1 b i
  unfold LamLetters.IsLetter at hw
  generalize L.src (L.e ⟨b, i⟩) = s at hb hw
  rcases s with q | q
  · obtain ⟨w₁, h₁, h₂⟩ := hΨ a q.2
    obtain ⟨rfl, -⟩ := hb
    exact exists_scale_of_eigen o.xΨ.basis.1 q.2 _ _ _ _ _ _ (eΨ q.1 a) h₁ h₂ hw
  · obtain ⟨w₁, h₁, h₂⟩ := h' a q.2
    obtain ⟨rfl, -⟩ := hb
    exact exists_scale_of_eigen o.x'.basis.1 q.2 _ _ _ _ _ _ (e' q.1 a) h₁ h₂ hw

end GlobalTheory.LamF.LetterEigen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolarisedAbelianSchemePowerStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polarisedAbelianScheme_power : ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (n : ℕ), ∃ (Q : Out.PolAV (Sp R)) (_ : Out.IsPowGrp Q.A P.A n), Q.g = n * P.g := by
  first | exact @GlobalTheory.CM.exists_polAV_isPowGrp | exact GlobalTheory.CM.exists_polAV_isPowGrp | (intros; apply GlobalTheory.CM.exists_polAV_isPowGrp <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.GramStdBasisPosDefAndHq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem gram_stdBasis_posDef_and_hq :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (h : HermFam K (Fin n → K)) (s : K →+* ℂ), (h.gram s (fun i => Pi.single i 1) : Matrix (Fin n) (Fin n) ℂ).PosDef ∧ ∀ c, ReciprocityTheory.MultiplicativeHeights.hq (h.gram s (fun i => Pi.single i 1)) (ReciprocityTheory.MultiplicativeHeights.embVec s c) = (h.form s c c).re := by
  intro K _ _ n h s
  refine ⟨h.posDef s n _ ?_, fun c => ?_⟩
  · have hb := (Pi.basisFun K (Fin n)).linearIndependent
    have he : (⇑(Pi.basisFun K (Fin n)) : Fin n → Fin n → K) = fun i => Pi.single i 1 := by
      funext i; exact Pi.basisFun_apply K (Fin n) i
    rwa [he] at hb
  · have hc : c = ∑ i, c i • (Pi.single i 1 : Fin n → K) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    have hx := h.form_expand s c (fun i => Pi.single i 1)
    rw [← hc] at hx
    rw [hx, ReciprocityTheory.MultiplicativeHeights.hq]
    congr 1
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, ReciprocityTheory.MultiplicativeHeights.embVec, Pi.star_apply,
      Complex.star_def]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm

end GlobalTheory.LamF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveAppTopOfSection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.TrivDedekind

theorem surjective_appTop_of_section {K : Type} [Field K] {Y : Scheme.{0}} [IsIntegral Y] (p : Y ⟶ Sp K)
    [UniversallyClosed p] (e : Sp K ⟶ Y) (he : e ≫ p = 𝟙 _) : Function.Surjective p.appTop.hom := by
  have hF : IsField Γ(Y, ⊤) := isField_of_universallyClosed K p
  let _ := hF.toField
  have hinj : Function.Injective e.appTop.hom := e.appTop.hom.injective
  have hc : ∀ a, e.appTop.hom (p.appTop.hom a) = a := fun a => by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, he]
    simp
  exact fun c => ⟨e.appTop.hom c, hinj (hc _)⟩

theorem exists_gen_of_generic : ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (X' : Scheme.{0}) (π : X' ⟶ A.left) (p : X' ⟶ Sp K), IsPullback π p A.hom (spMap (algebraMap R K)) → ∀ N : LB A.left, N.IsLB → (∃ t : LB.Gen (N.pull (eSec A)), t.IsGen) → (∃ t : LB.Gen (N.pull π), t.IsGen) → ∃ t : LB.Gen N, t.IsGen := by
  intro R K _ _ _ _ _ A _ hA X' π p H N hN ⟨ρ, hρ⟩ ⟨t, ht⟩
  have := hA.smooth
  have := hA.proper
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth hA.geomConnected
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : QuasiSeparatedSpace A.left := quasiSeparatedSpace_of_quasiSeparated A.hom
  have : IsIntegral X' := DvrModel.isIntegral_of_geometricallyIntegral H
  have : UniversallyClosed p := MorphismProperty.of_isPullback H inferInstance
  have he : eSec A ≫ A.hom = 𝟙 _ := Over.w η[A]
  exact GenericTriv.exists_gen_of_fibre (algebraMap R K) (IsFractionRing.injective R K) A.hom (eSec A) he π p H
    (surjective_appTop_of_section p (H.lift (spMap (algebraMap R K) ≫ eSec A) (𝟙 _)
      (by rw [Category.assoc, he]; simp)) (H.lift_snd _ _ _)) hN ρ hρ t ht

end GlobalTheory.TrivDedekind
end
