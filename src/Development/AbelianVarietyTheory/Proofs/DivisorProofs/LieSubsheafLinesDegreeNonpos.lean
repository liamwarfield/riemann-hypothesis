module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidOfIsSemiAbelian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFormalPathEqScalingValuationRingPath

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRationalFormalPathOfIntegralAllPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedDenominatorAlongValuationPath
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedDenominatorAlongValuationPath
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem den_along_path : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (p : Place k E) (u : E) (Y : Scheme.{0}) (ζ : Sp (PowerSeries p.O) ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ (spMap (sc p u) ≫ ζ) ⁻¹ᵁ U) (f : Γ(Y, U)), ∃ e ψ : PowerSeries p.O, PowerSeries.constantCoeff e ≠ 0 ∧ (⊤ ≤ ζ ⁻¹ᵁ U → e = 1) ∧ sc p u e * evAt (spMap (sc p u) ≫ ζ) h f = sc p u ψ := by
  intro k E _ _ _ p u Y ζ U h f
  obtain ⟨hcomp, -, hres, hloc, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk
  by_cases hU : ⊤ ≤ ζ ⁻¹ᵁ U
  · refine ⟨1, evAt ζ hU f, by simp, fun _ => rfl, ?_⟩
    rw [map_one, _root_.one_mul, hcomp (PowerSeries p.O) (PowerSeries E) Y (sc p u) ζ U hU h f]
  · obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hy0, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (ζ (IsLocalRing.closedPoint (PowerSeries p.O)))) isOpen_univ
    have hζ0 : ⊤ ≤ ζ ⁻¹ᵁ U₀ := (hloc _ _ _ _).2 hy0
    have hη0 : ⊤ ≤ (spMap (sc p u) ≫ ζ) ⁻¹ᵁ U₀ := fun x _ => hζ0 (Set.mem_univ ((spMap (sc p u)) x))
    have hyU := (hloc _ _ _ _).1 h
    have hyU₀ := (hloc _ _ _ _).1 hη0
    obtain ⟨t, htU, hyt⟩ := hU₀.exists_basicOpen_le (V := U) ⟨_, hyU⟩ hyU₀
    have hηt : ⊤ ≤ (spMap (sc p u) ≫ ζ) ⁻¹ᵁ Y.basicOpen t := (hloc _ _ _ _).2 hyt
    haveI := hU₀.isLocalization_basicOpen t
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hmk⟩ := IsLocalization.mk'_surjective (Submonoid.powers t)
      (Y.presheaf.map (homOfLE htU).op f)
    have hspec := IsLocalization.mk'_spec Γ(Y, Y.basicOpen t) a (⟨t ^ n, n, rfl⟩ : Submonoid.powers t)
    simp only at hmk
    rw [hmk] at hspec
    have hle : Y.basicOpen t ≤ U₀ := Y.basicOpen_le t
    have key : evAt (spMap (sc p u) ≫ ζ) hηt (Y.presheaf.map (homOfLE htU).op f) *
        evAt (spMap (sc p u) ≫ ζ) hηt (Y.presheaf.map (homOfLE hle).op (t ^ n)) =
        evAt (spMap (sc p u) ≫ ζ) hηt (Y.presheaf.map (homOfLE hle).op a) := by
      rw [← map_mul]; exact congrArg _ hspec
    have h1 := hres _ _ _ _ _ htU h hηt f
    have h2 := hres _ _ _ _ _ hle hη0 hηt (t ^ n)
    have h3 := hres _ _ _ _ _ hle hη0 hηt a
    have hu : IsUnit (evAt (spMap (sc p u) ≫ ζ) hηt (Y.presheaf.map (homOfLE hle).op t)) :=
      (Y.toRingedSpace.isUnit_res_basicOpen t).map _
    refine ⟨evAt ζ hζ0 (t ^ n), evAt ζ hζ0 a, ?_, fun h' => absurd h' hU, ?_⟩
    · intro h0
      have hu' : IsUnit (sc p u (evAt ζ hζ0 (t ^ n))) := by
        rw [← hcomp (PowerSeries p.O) (PowerSeries E) Y (sc p u) ζ U₀ hζ0 hη0, ← h2, map_pow, map_pow]
        exact hu.pow n
      rw [PowerSeries.isUnit_iff_constantCoeff] at hu'
      apply hu'.ne_zero
      rw [sc, RingHom.comp_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale,
        PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
      simp
    · rw [← hcomp (PowerSeries p.O) (PowerSeries E) Y (sc p u) ζ U₀ hζ0 hη0, ← hcomp (PowerSeries p.O) (PowerSeries E) Y (sc p u) ζ U₀ hζ0 hη0, ← h1, ← h2, ← h3, ← key]
      exact mul_comm _ _

end GlobalTheory.Nef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedDenominatorAlongValuationPathStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bounded_denominator_along_valuationPath : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (p : Place k E) (u : E) (Y : Scheme.{0}) (ζ : Sp (PowerSeries p.O) ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ (spMap (sc p u) ≫ ζ) ⁻¹ᵁ U) (f : Γ(Y, U)), ∃ e ψ : PowerSeries p.O, PowerSeries.constantCoeff e ≠ 0 ∧ (⊤ ≤ ζ ⁻¹ᵁ U → e = 1) ∧ sc p u e * evAt (spMap (sc p u) ≫ ζ) h f = sc p u ψ := by
  first | exact @GlobalTheory.Nef.den_along_path | exact GlobalTheory.Nef.den_along_path | (intros; apply GlobalTheory.Nef.den_along_path <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRationalFormalPathOfRationalExpansions
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRationalFormalPathOfRationalExpansions
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem isRatPath_of_isRat : ∀ (F : Type) [Field F] (Y : Scheme.{0}) (ξ : Sp (PowerSeries F) ⟶ Y),
    (∀ (U : Y.Opens), IsAffineOpen U → ∀ (h : ⊤ ≤ ξ ⁻¹ᵁ U) (f : Γ(Y, U)), IsRat (evAt ξ h f)) → IsRatPath ξ := by
  intro F _ Y ξ hrat
  obtain ⟨h1, -, -, h4, h5, h6, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk
  obtain ⟨U, hUa, hy, -⟩ := (Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens)
    (show ξ (IsLocalRing.closedPoint (PowerSeries F)) ∈ (⊤ : Y.Opens) from trivial)
  have hξ : ⊤ ≤ ξ ⁻¹ᵁ U := (h4 _ Y ξ U).2 hy
  set ψ := evAt ξ hξ
  set ιR := algebraMap (RatFunc F) (LaurentSeries F)
  set ιP := algebraMap (PowerSeries F) (LaurentSeries F)
  have hR : Function.Injective ιR := ιR.injective
  have hmem : ∀ f, (ιP.comp ψ) f ∈ ιR.range := fun f => by
    obtain ⟨ρ, hρ⟩ := (isRat_iff_exists_ratFunc F (ψ f)).1 (hrat U hUa hξ f)
    exact ⟨ρ, hρ⟩
  let e := RingEquiv.ofBijective ιR.rangeRestrict ⟨fun a b hab => hR (congrArg Subtype.val hab), ιR.rangeRestrict_surjective⟩
  let φ : Γ(Y, U) →+* RatFunc F := e.symm.toRingHom.comp ((ιP.comp ψ).codRestrict ιR.range hmem)
  have hφ : ∀ f, ιR (φ f) = ιP (ψ f) := fun f => by
    have := congrArg Subtype.val (e.apply_symm_apply ((ιP.comp ψ).codRestrict ιR.range hmem f))
    exact this
  obtain ⟨β, hβ, hβφ⟩ := h6 (RatFunc F) Y U hUa φ
  refine ⟨β, ?_⟩
  have ha : ⊤ ≤ (spMap ιR ≫ β) ⁻¹ᵁ U := fun x _ => hβ (Set.mem_univ ((spMap ιR) x))
  have hb : ⊤ ≤ (spMap ιP ≫ ξ) ⁻¹ᵁ U := fun x _ => hξ (Set.mem_univ ((spMap ιP) x))
  refine h5 (LaurentSeries F) Y _ _ U hUa ha hb ?_
  refine RingHom.ext fun f => ?_
  rw [h1 _ _ Y ιR β U hβ ha f, h1 _ _ Y ιP ξ U hξ hb f, hβφ]
  exact hφ f

end GlobalTheory.Nef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRationalFormalPathOfRationalExpansionsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRationalFormalPath_of_rationalExpansions : ∀ (F : Type) [Field F] (Y : Scheme.{0}) (ξ : Sp (PowerSeries F) ⟶ Y), (∀ (U : Y.Opens), IsAffineOpen U → ∀ (h : ⊤ ≤ ξ ⁻¹ᵁ U) (f : Γ(Y, U)), IsRat (evAt ξ h f)) → IsRatPath ξ := by
  first | exact @GlobalTheory.Nef.isRatPath_of_isRat | exact GlobalTheory.Nef.isRatPath_of_isRat | (intros; apply GlobalTheory.Nef.isRatPath_of_isRat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRationalPowerSeriesOfAdelicIntegralPositiveRad
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HankelDeterminantIntegralOfQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HankelDeterminantIntegralOfQuotient
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

open PowerSeries Finset

theorem hankelInt_sumLemma {F : Type} [Field F] (E Q : PowerSeries F) (n : ℕ) (i : Fin (n + 1)) (s : ℕ) :
    ∑ l : Fin (n + 1), (if (l : ℕ) ≤ i then coeff ((i : ℕ) - l) E else 0) * coeff ((l : ℕ) + s) Q =
      coeff ((i : ℕ) + s) ((trunc ((i : ℕ) + 1) E : PowerSeries F) * Q) := by
  have hi : (i : ℕ) + 1 ≤ n + 1 := by omega
  rw [Fin.sum_univ_eq_sum_range (fun l => (if l ≤ (i : ℕ) then coeff ((i : ℕ) - l) E else 0) * coeff (l + s) Q) (n + 1)]
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hf : (range (n + 1)).filter (fun l => l ≤ (i : ℕ)) = range ((i : ℕ) + 1) := by
    ext l; simp only [mem_filter, mem_range]; omega
  rw [hf, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => coeff a (trunc ((i : ℕ) + 1) E : PowerSeries F) * coeff b Q)]
  simp only [Polynomial.coeff_coe, coeff_trunc, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hg : (range ((i : ℕ) + s).succ).filter (fun a => a < (i : ℕ) + 1) = range ((i : ℕ) + 1) := by
    ext l; simp only [mem_filter, mem_range, Nat.succ_eq_add_one]; omega
  rw [hg, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [mem_range] at hl
  rw [show (i : ℕ) - ((i : ℕ) + 1 - 1 - l) = l by omega, show (i : ℕ) + 1 - 1 - l + s = (i : ℕ) + s - l by omega]

theorem hankel_integral : ∀ (O F : Type) [CommRing O] [Field F] (ι : O →+* F) (e ψ : PowerSeries O) (φ : PowerSeries F) (n : ℕ), PowerSeries.map ι e * φ = PowerSeries.map ι ψ → ∃ z : O, ι z = ι (PowerSeries.constantCoeff e) ^ (2 * (n + 1)) * hankel (fun i => PowerSeries.coeff i φ) n := by
  intro O F _ _ ι e ψ φ n h
  set E := PowerSeries.map ι e with hE
  set P : ℕ → PowerSeries F := fun i => (trunc (i + 1) E : PowerSeries F) with hP
  let N : Matrix (Fin (n + 1)) (Fin (n + 1)) O := Matrix.of fun i j =>
    coeff ((i : ℕ) + j) ((trunc ((i : ℕ) + 1) e : PowerSeries O) * ψ - (e - (trunc ((j : ℕ) + 1) e : PowerSeries O)) * ψ)
  let T : Matrix (Fin (n + 1)) (Fin (n + 1)) F := Matrix.of fun i l =>
    if (l : ℕ) ≤ i then coeff ((i : ℕ) - l) E else 0
  let H : Matrix (Fin (n + 1)) (Fin (n + 1)) F := Matrix.of fun i j => coeff ((i : ℕ) + j) φ
  have hmapP : ∀ k, PowerSeries.map ι (trunc k e : PowerSeries O) = (trunc k E : PowerSeries F) := by
    intro k; ext m; simp only [hE, coeff_map, Polynomial.coeff_coe, coeff_trunc]; split_ifs <;> simp
  have hX : ∀ i : ℕ, X ^ (i + 1) ∣ E - P i := by
    intro i; rw [X_pow_dvd_iff]; intro m hm
    simp [hP, Polynomial.coeff_coe, coeff_trunc, hm]
  have hdiv : ∀ i j : ℕ, coeff (i + j) ((E - P i) * (E - P j) * φ) = 0 := by
    intro i j
    have h3 : X ^ (i + 1 + (j + 1)) ∣ (E - P i) * (E - P j) * φ := by
      rw [pow_add]; exact Dvd.dvd.mul_right (mul_dvd_mul (hX i) (hX j)) φ
    exact X_pow_dvd_iff.mp h3 _ (by omega)
  have hent : N.map ι = T * H * T.transpose := by
    ext i j
    have inner : ∀ l : Fin (n + 1), ∑ m, H l m * T.transpose m j = coeff ((l : ℕ) + j) (P j * φ) := by
      intro l
      rw [Nat.add_comm (l : ℕ) (j : ℕ)]
      refine Eq.trans ?_ (hankelInt_sumLemma E φ n j l)
      refine sum_congr rfl fun m _ => ?_
      simp only [H, T, Matrix.of_apply, Matrix.transpose_apply]; rw [mul_comm, add_comm (l : ℕ)]
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    simp only [Matrix.mul_apply, inner]
    rw [show (∑ x, T i x * coeff ((x : ℕ) + j) (P j * φ)) = coeff ((i : ℕ) + j) (P i * (P j * φ)) from hankelInt_sumLemma E (P j * φ) n i j]
    simp only [Matrix.map_apply, N, Matrix.of_apply]
    have key : PowerSeries.map ι ((trunc ((i : ℕ) + 1) e : PowerSeries O) * ψ - (e - (trunc ((j : ℕ) + 1) e : PowerSeries O)) * ψ)
        = P i * (P j * φ) - (E - P i) * (E - P j) * φ := by
      rw [map_sub, map_mul, map_mul, map_sub, hmapP, hmapP, ← h, ← hE]
      simp only [hP]; ring
    rw [← coeff_map, key, map_sub, hdiv, sub_zero]
  have hT : T.det = ι (constantCoeff e) ^ (n + 1) := by
    rw [Matrix.det_of_lowerTriangular T ?_]
    · simp [T, E, Finset.prod_const]
    · intro i j hij
      have hij' : i < j := hij
      have h1 : ¬ j ≤ i := not_le.mpr hij'
      have h2 : ¬ ((j : ℕ) ≤ i) := h1
      simp [T, h1, h2]
  refine ⟨N.det, ?_⟩
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hent, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hT]
  show _ = _ * H.det
  ring

end GlobalTheory.Nef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HankelDeterminantIntegralOfQuotientStatement
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hankelDeterminant_integral_of_quotient : ∀ (O F : Type) [CommRing O] [Field F] (ι : O →+* F) (e ψ : PowerSeries O) (φ : PowerSeries F) (n : ℕ), PowerSeries.map ι e * φ = PowerSeries.map ι ψ → ∃ z : O, ι z = ι (PowerSeries.constantCoeff e) ^ (2 * (n + 1)) * hankel (fun i => PowerSeries.coeff i φ) n := by
  first | exact @GlobalTheory.Nef.hankel_integral | exact GlobalTheory.Nef.hankel_integral | (intros; apply GlobalTheory.Nef.hankel_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRatOfHankelEventuallyZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRatOfHankelEventuallyZero
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef.Kron

open Polynomial

variable {F : Type} [Field F] (c : ℕ → F)

def ev : F[X] →ₗ[F] F := Polynomial.lsum fun i => c i • LinearMap.id

theorem ev_monomial (n : ℕ) (a : F) : ev c (monomial n a) = c n * a := by
  simp [ev, Polynomial.lsum_apply]

theorem ev_expand (q p : F[X]) (n : ℕ) (hp : p.natDegree < n) :
    ev c (q * p) = ∑ j ∈ Finset.range n, p.coeff j * ev c (q * X ^ j) := by
  conv_lhs => rw [p.as_sum_range' n hp]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← C_mul_X_pow_eq_monomial, show q * (C (p.coeff j) * X ^ j) = p.coeff j • (q * X ^ j) by
    rw [smul_eq_C_mul]; ring, map_smul, smul_eq_mul]

theorem ev_zero_of_lt (q p : F[X]) (s : ℕ) (h : ∀ j < s, ev c (q * X ^ j) = 0)
    (hp : p.natDegree < s) : ev c (q * p) = 0 := by
  rw [ev_expand c q p s hp]
  exact Finset.sum_eq_zero fun j hj => by rw [h j (Finset.mem_range.1 hj), mul_zero]

theorem ev_top (q p : F[X]) (s : ℕ) (h : ∀ j < s, ev c (q * X ^ j) = 0)
    (hp : p.natDegree ≤ s) : ev c (q * p) = p.coeff s * ev c (q * X ^ s) := by
  rw [ev_expand c q p (s + 1) (Nat.lt_succ_of_le hp), Finset.sum_range_succ,
    Finset.sum_eq_zero fun j hj => by rw [h j (Finset.mem_range.1 hj), mul_zero], zero_add]

theorem ev_X_pow_mul (m : ℕ) (q : F[X]) :
    ev c (q * X ^ m) = ∑ j ∈ Finset.range (q.natDegree + 1), q.coeff j * c (m + j) := by
  rw [mul_comm, ev_expand c _ q _ (Nat.lt_succ_self _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← pow_add, ← monomial_one_right_eq_X_pow, ev_monomial, mul_one]

theorem exists_kill (n : ℕ) (h : hankel c n = 0) :
    ∃ r : F[X], r ≠ 0 ∧ r.natDegree ≤ n ∧ ∀ j ≤ n, ev c (r * X ^ j) = 0 := by
  classical
  unfold hankel at h
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  refine ⟨∑ k : Fin (n + 1), monomial (k : ℕ) (v k), ?_, ?_, ?_⟩
  · intro h0
    apply hv0
    funext k
    have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p k) h0
    simpa [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial_apply, Finsupp.single_apply, Fin.val_inj] using this
  · exact natDegree_sum_le_of_forall_le _ _ fun k _ =>
      (natDegree_monomial_le _).trans (Nat.lt_succ_iff.1 k.2)
  · intro j hj
    have := congrFun hv ⟨j, Nat.lt_succ_of_le hj⟩
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_mul, map_sum, ← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [monomial_mul_X_pow, ev_monomial, add_comm]

theorem exists_annihilator (N : ℕ) (hN : ∀ n, N ≤ n → hankel c n = 0) :
    ∃ q : F[X], q ≠ 0 ∧ ∀ j, ev c (q * X ^ j) = 0 := by
  classical
  have hex : ∃ d, ∃ q : F[X], q ≠ 0 ∧ q.natDegree = d ∧ d ≤ N ∧ ∀ j ≤ N, ev c (q * X ^ j) = 0 := by
    obtain ⟨r, hr0, hrd, hr⟩ := exists_kill c N (hN N le_rfl)
    exact ⟨_, r, hr0, rfl, hrd, hr⟩
  obtain ⟨q0, hq00, hq0d, hdN, hq0⟩ := Nat.find_spec hex
  have hmin : ∀ r : F[X], r ≠ 0 → r.natDegree < Nat.find hex → ¬ ∀ j ≤ N, ev c (r * X ^ j) = 0 :=
    fun r hr0 hrd hr => Nat.find_min hex hrd ⟨r, hr0, rfl, by omega, hr⟩
  have hlc : (q0.leadingCoeff)⁻¹ ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero.2 hq00)
  obtain ⟨q, hqm, hqd, hqe⟩ : ∃ q : F[X], q.Monic ∧ q.natDegree = Nat.find hex ∧
      ∀ j, ev c (q * X ^ j) = (q0.leadingCoeff)⁻¹ * ev c (q0 * X ^ j) := by
    refine ⟨q0 * C (q0.leadingCoeff)⁻¹, monic_mul_leadingCoeff_inv hq00, ?_, fun j => ?_⟩
    · rw [natDegree_mul_C hlc, hq0d]
    · rw [show q0 * C (q0.leadingCoeff)⁻¹ * X ^ j = (q0.leadingCoeff)⁻¹ • (q0 * X ^ j) by
        rw [smul_eq_C_mul]; ring, map_smul, smul_eq_mul]
  refine ⟨q, hqm.ne_zero, ?_⟩
  by_contra hne
  push_neg at hne
  have hs : ev c (q * X ^ Nat.find hne) ≠ 0 := Nat.find_spec hne
  have hlt : ∀ j < Nat.find hne, ev c (q * X ^ j) = 0 := fun j hj => by
    by_contra h; exact Nat.find_min hne hj h
  generalize Nat.find hne = s at hs hlt
  generalize Nat.find hex = d at hmin hqd hdN
  have hNs : N < s := by
    by_contra h
    push_neg at h
    apply hs
    rw [hqe, hq0 s h, mul_zero]
  obtain ⟨r, hr0, hrd, hr⟩ := exists_kill c s (hN s hNs.le)
  have hrk : ∀ p : F[X], p.natDegree ≤ s → ev c (r * p) = 0 := fun p hp => by
    rw [ev_top c r p s (fun j hj => hr j hj.le) hp, hr s le_rfl, mul_zero]
  obtain ⟨r0, r1, hdiv, hr0deg⟩ : ∃ r0 r1 : F[X], r0 + q * r1 = r ∧ r0.degree < q.degree :=
    ⟨_, _, modByMonic_add_div r q, degree_modByMonic_lt r hqm⟩
  subst hdiv
  have hr0s : r0.natDegree < s := by
    by_cases hz : r0 = 0
    · rw [hz, natDegree_zero]; omega
    · have := natDegree_lt_natDegree hz hr0deg; omega
  by_cases h1 : r1 = 0
  · subst h1
    rw [mul_zero, add_zero] at hr0 hrd hr
    apply hmin r0 hr0 (hqd ▸ natDegree_lt_natDegree hr0 hr0deg)
    intro j hj
    exact hr j (by omega)
  · have hdeg : d + r1.natDegree ≤ s := by
      rw [← hqd, ← natDegree_mul hqm.ne_zero h1]
      have : q * r1 = r0 + q * r1 - r0 := by ring
      rw [this]
      exact (natDegree_sub_le _ _).trans (max_le hrd hr0s.le)
    have key := hrk (q * X ^ (s - d - r1.natDegree))
      (by rw [natDegree_mul_X_pow _ hqm.ne_zero, hqd]; omega)
    rw [add_mul, map_add (f := _)] at key
    have h0 : ev c (r0 * (q * X ^ (s - d - r1.natDegree))) = 0 := by
      rw [show r0 * (q * X ^ (s - d - r1.natDegree)) = q * (r0 * X ^ (s - d - r1.natDegree)) by ring]
      apply ev_zero_of_lt c q _ s hlt
      by_cases hz : r0 = 0
      · rw [hz, zero_mul, natDegree_zero]; omega
      · rw [natDegree_mul_X_pow _ hz]
        have := natDegree_lt_natDegree hz hr0deg
        omega
    have hne1 : r1 * q ≠ 0 := mul_ne_zero h1 hqm.ne_zero
    have hs' : s = (r1 * q).natDegree + (s - d - r1.natDegree) := by
      rw [natDegree_mul h1 hqm.ne_zero, hqd]; omega
    have hcoef : (r1 * q * X ^ (s - d - r1.natDegree)).coeff s = r1.leadingCoeff := by
      have := coeff_mul_X_pow (r1 * q) (s - d - r1.natDegree) (r1 * q).natDegree
      rw [← hs'] at this
      rw [this, coeff_natDegree, leadingCoeff_mul, hqm.leadingCoeff, mul_one]
    have h2 : ev c (q * r1 * (q * X ^ (s - d - r1.natDegree))) = r1.leadingCoeff * ev c (q * X ^ s) := by
      rw [show q * r1 * (q * X ^ (s - d - r1.natDegree)) = q * (r1 * q * X ^ (s - d - r1.natDegree)) by ring,
        ev_top c q _ s hlt (by rw [natDegree_mul_X_pow _ hne1]; omega), hcoef]
    rw [h0, h2, zero_add] at key
    exact hs ((mul_eq_zero.1 key).resolve_left (leadingCoeff_ne_zero.2 h1))

theorem isRat_of_ann (φ : PowerSeries F) (q : F[X]) (hq : q ≠ 0)
    (h : ∀ j, ev (fun i => PowerSeries.coeff i φ) (q * X ^ j) = 0) : IsRat φ := by
  classical
  let R : F[X] := ∑ k ∈ Finset.range (q.natDegree + 1), C (q.coeff k) * X ^ (q.natDegree - k)
  refine ⟨PowerSeries.trunc q.natDegree ((R : PowerSeries F) * φ), R, ?_, ?_⟩
  · intro h0
    have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p 0) h0
    simp only [R, Polynomial.finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
    rw [Finset.sum_eq_single q.natDegree] at this
    · simp only [Nat.sub_self, if_true] at this
      exact hq (leadingCoeff_eq_zero.1 this)
    · intro k hk hkd
      have := Finset.mem_range.1 hk
      rw [if_neg (by omega)]
    · intro hk; exact absurd (Finset.self_mem_range_succ _) hk
  · ext n
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs with hn
    · rfl
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + q.natDegree := ⟨n - q.natDegree, by omega⟩
      have hR : (R : PowerSeries F) = ∑ k ∈ Finset.range (q.natDegree + 1),
          PowerSeries.C (q.coeff k) * PowerSeries.X ^ (q.natDegree - k) := by
        show Polynomial.coeToPowerSeries.ringHom R = _
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        simp [Polynomial.coeToPowerSeries.ringHom_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hR, Finset.sum_mul, map_sum, ← h m, ev_X_pow_mul]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' := Finset.mem_range.1 hk
      rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos (by omega)]
      rw [show m + q.natDegree - (q.natDegree - k) = m + k by omega]

end GlobalTheory.Nef.Kron

namespace GlobalTheory.Nef

theorem isRat_of_hankel_eventually_zero : ∀ (F : Type) [Field F] (φ : PowerSeries F) (N : ℕ),
    (∀ n, N ≤ n → hankel (fun i => PowerSeries.coeff i φ) n = 0) → IsRat φ := by
  intro F _ φ N hN
  obtain ⟨q, hq, h⟩ := Kron.exists_annihilator _ N hN
  exact Kron.isRat_of_ann φ q hq h

end GlobalTheory.Nef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRatOfHankelEventuallyZeroStatement
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRat_of_hankel_eventually_eq_zero : ∀ (F : Type) [Field F] (φ : PowerSeries F) (N : ℕ), (∀ n, N ≤ n → hankel (fun i => PowerSeries.coeff i φ) n = 0) → IsRat φ := by
  first | exact @GlobalTheory.Nef.isRat_of_hankel_eventually_zero | exact GlobalTheory.Nef.isRat_of_hankel_eventually_zero | (intros; apply GlobalTheory.Nef.isRat_of_hankel_eventually_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRationalPowerSeriesOfAdelicIntegralPositiveRad
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RatCrit

variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem hankel_pow_mul (a : F) (c : ℕ → F) (n : ℕ) :
    hankel (fun i => a ^ i * c i) n = a ^ (n * (n + 1)) * hankel c n := by
  have hM : (Matrix.of fun i j : Fin (n + 1) => a ^ ((i : ℕ) + j) * c (i + j)) =
      Matrix.diagonal (fun i : Fin (n + 1) => a ^ (i : ℕ)) * (Matrix.of fun i j : Fin (n + 1) => c (i + j)) *
        Matrix.diagonal (fun i : Fin (n + 1) => a ^ (i : ℕ)) := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.of_apply, pow_add]
    ring
  unfold hankel
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]
  have hs : (∑ i : Fin (n + 1), (i : ℕ)) * 2 = n * (n + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => i) (n + 1), Finset.sum_range_id_mul_two]
    simp [mul_comm]
  rw [← hs, pow_mul]
  ring

theorem ord_mul' (v : Place k F) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    ord v (x * y) = ord v x + ord v y := by
  unfold ord
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx) ((Valuation.ne_zero_iff _).2 hy)]
  ring

theorem ord_pow' (v : Place k F) (x : F) (m : ℕ) : ord v (x ^ m) = m * ord v x := by
  unfold ord
  rw [map_pow, WithZero.log_pow, nsmul_eq_mul]
  ring

theorem ord_of_eq_one (v : Place k F) {x : F} (h : v.1 x = 1) : ord v x = 0 := by
  simp [ord, h]

end GlobalTheory.RatCrit

namespace GlobalTheory.RatCrit

variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem ord_hankel_ge (v : Place k F) (φ : PowerSeries F) (u : F) (e ψ : PowerSeries v.O) (hu : u ≠ 0)
    (he0 : PowerSeries.constantCoeff e ≠ 0)
    (heq : sc v u e * φ = sc v u ψ) (n : ℕ) (hH : hankel (fun i => PowerSeries.coeff i φ) n ≠ 0) :
    ((n * (n + 1) : ℕ) : ℤ) * ord v u - ((2 * (n + 1) : ℕ) : ℤ) * ord v ((PowerSeries.constantCoeff e : v.O) : F) ≤
      ord v (hankel (fun i => PowerSeries.coeff i φ) n) := by
  have hr : ∀ f : PowerSeries F, PowerSeries.rescale u⁻¹ (PowerSeries.rescale u f) = f := by
    intro f; ext m
    simp only [PowerSeries.coeff_rescale, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hu, one_pow, one_mul]
  have h1 : PowerSeries.map v.O.subtype e * PowerSeries.rescale u⁻¹ φ = PowerSeries.map v.O.subtype ψ := by
    have := congrArg (PowerSeries.rescale u⁻¹) heq
    simpa only [sc, RingHom.comp_apply, map_mul, hr] using this
  obtain ⟨z, hz⟩ := GlobalTheory.T.hankelDeterminant_integral_of_quotient v.O F v.O.subtype e ψ (PowerSeries.rescale u⁻¹ φ) n h1
  have h2 : (fun i => PowerSeries.coeff i φ) = fun i => u ^ i * PowerSeries.coeff i (PowerSeries.rescale u⁻¹ φ) := by
    funext i
    rw [PowerSeries.coeff_rescale, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hu, one_pow, one_mul]
  set c : F := ((PowerSeries.constantCoeff e : v.O) : F) with hc
  set H := hankel (fun i => PowerSeries.coeff i φ) n with hHdef
  set H0 := hankel (fun i => PowerSeries.coeff i (PowerSeries.rescale u⁻¹ φ)) n with hH0
  have h3 : H = u ^ (n * (n + 1)) * H0 := by rw [hHdef, h2, hankel_pow_mul]
  have hz' : (z : F) = c ^ (2 * (n + 1)) * H0 := hz
  have h4 : c ^ (2 * (n + 1)) * H = u ^ (n * (n + 1)) * (z : F) := by rw [h3, hz']; ring
  have hH0 : H0 ≠ 0 := by
    intro h; exact hH (by rw [h3, h, mul_zero])
  have hcne : c ≠ 0 := by
    intro h; apply he0; ext; simpa [hc] using h
  have hzne : (z : F) ≠ 0 := by rw [hz']; exact mul_ne_zero (pow_ne_zero _ hcne) hH0
  have hz1 : 0 ≤ ord v (z : F) :=
    ((GlobalTheory.T.functionFieldPlaceOrder_calculus k F v).2.2.1 _ hzne).1 ((Valuation.mem_valuationSubring_iff _ _).1 z.2)
  have h5 := congrArg (ord v) h4
  rw [ord_mul' v (pow_ne_zero _ hcne) hH, ord_mul' v (pow_ne_zero _ hu) hzne, ord_pow', ord_pow'] at h5
  linarith

end GlobalTheory.RatCrit

namespace GlobalTheory.RatCrit

theorem isRat_of_adelic : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (φ : PowerSeries F) (u : Place k F → F) (e ψ : ∀ v : Place k F, PowerSeries v.O), (∀ v, u v ≠ 0) → {v | ord v (u v) ≠ 0}.Finite → 0 < ∑ᶠ v, ord v (u v) → (∀ v, PowerSeries.constantCoeff (e v) ≠ 0) → {v | ¬ IsUnit (PowerSeries.constantCoeff (e v))}.Finite → (∀ v, sc v (u v) (e v) * φ = sc v (u v) (ψ v)) → IsRat φ := by
  intro k F _ _ _ _ _ hFF φ u e ψ hu0 hufin hdeg he0 hefin heq
  classical
  set c : Place k F → F := fun v => ((PowerSeries.constantCoeff (e v) : v.O) : F) with hc
  have hcunit : ∀ v, IsUnit (PowerSeries.constantCoeff (e v)) → v.1 (c v) = 1 := by
    intro v h
    obtain ⟨a, ha⟩ := h
    have h1 := ValuationSubring.valuation_unit v.O a
    rw [ha] at h1
    exact (Valuation.isEquiv_valuation_valuationSubring v.1).eq_one_iff_eq_one.2 h1
  set δ := ∑ᶠ v, ord v (c v) with hδ
  set D := ∑ᶠ v, ord v (u v) with hD
  apply GlobalTheory.T.isRat_of_hankel_eventually_eq_zero F φ ((2 * δ).toNat + 1)
  intro n hn
  by_contra hH
  obtain ⟨hHfin, hHsum⟩ := GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k F hFF _ hH
  set H := hankel (fun i => PowerSeries.coeff i φ) n with hHdef
  let T : Finset (Place k F) := hufin.toFinset ∪ hefin.toFinset ∪ hHfin.toFinset
  have sU : Function.support (fun v => ord v (u v)) ⊆ (T : Set (Place k F)) := by
    intro v hv
    simp only [T, Finset.coe_union, Set.Finite.coe_toFinset]
    exact Or.inl (Or.inl hv)
  have sC : Function.support (fun v => ord v (c v)) ⊆ (T : Set (Place k F)) := by
    intro v hv
    simp only [T, Finset.coe_union, Set.Finite.coe_toFinset]
    refine Or.inl (Or.inr ?_)
    intro h
    exact hv (ord_of_eq_one v (hcunit v h))
  have sH : Function.support (fun v => ord v H) ⊆ (T : Set (Place k F)) := by
    intro v hv
    simp only [T, Finset.coe_union, Set.Finite.coe_toFinset]
    refine Or.inr ?_
    intro h
    exact hv (ord_of_eq_one v h)
  rw [finsum_eq_sum_of_support_subset _ sH] at hHsum
  rw [finsum_eq_sum_of_support_subset _ sC] at hδ
  rw [finsum_eq_sum_of_support_subset _ sU] at hD
  have hsum : ∑ v ∈ T, (((n * (n + 1) : ℕ) : ℤ) * ord v (u v) - ((2 * (n + 1) : ℕ) : ℤ) * ord v (c v)) ≤
      ∑ v ∈ T, ord v H :=
    Finset.sum_le_sum fun v _ => ord_hankel_ge v φ (u v) (e v) (ψ v) (hu0 v) (he0 v) (heq v) n hH
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hD, ← hδ, hHsum] at hsum
  have hn' : 2 * δ + 1 ≤ (n : ℤ) := by
    have := Int.self_le_toNat (2 * δ)
    omega
  have hD1 : 1 ≤ D := hdeg
  push_cast at hsum
  have h6 : (n + 1 : ℤ) * (n * D - 2 * δ) ≤ 0 := by linarith [hsum]
  have h7 : (n : ℤ) * D - 2 * δ ≤ 0 := by
    by_contra h8
    push_neg at h8
    have : (0 : ℤ) < (n + 1 : ℤ) * (n * D - 2 * δ) := mul_pos (by positivity) h8
    linarith
  have h9 : (n : ℤ) ≤ n * D := by nlinarith [(Nat.cast_nonneg n : (0 : ℤ) ≤ n)]
  linarith

end GlobalTheory.RatCrit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRationalPowerSeriesOfAdelicIntegralPositiveRadStatement
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRational_powerSeries_of_adelicIntegral_positiveRadius : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (φ : PowerSeries F) (u : Place k F → F) (e ψ : ∀ v : Place k F, PowerSeries v.O), (∀ v, u v ≠ 0) → {v | ord v (u v) ≠ 0}.Finite → 0 < ∑ᶠ v, ord v (u v) → (∀ v, PowerSeries.constantCoeff (e v) ≠ 0) → {v | ¬ IsUnit (PowerSeries.constantCoeff (e v))}.Finite → (∀ v, sc v (u v) (e v) * φ = sc v (u v) (ψ v)) → IsRat φ := by
  first | exact @GlobalTheory.RatCrit.isRat_of_adelic | exact GlobalTheory.RatCrit.isRat_of_adelic | (intros; apply GlobalTheory.RatCrit.isRat_of_adelic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRationalFormalPathOfIntegralAllPlaces
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

namespace GlobalTheory.Nef

private theorem isLocalHom_constantCoeff_ps (O : Type) [CommRing O] [IsLocalRing O] :
    IsLocalHom (PowerSeries.constantCoeff (R := O)) :=
  ⟨fun _ ha => PowerSeries.isUnit_iff_constantCoeff.2 ha⟩

private theorem constantCoeff_comp_sc {k E : Type} [Field k] [Field E] [Algebra k E] (p : Place k E) (u : E) :
    (PowerSeries.constantCoeff (R := E)).comp (sc p u) = p.O.subtype.comp (PowerSeries.constantCoeff (R := p.O)) := by
  refine RingHom.ext fun a => ?_
  show PowerSeries.constantCoeff (PowerSeries.rescale u (PowerSeries.map p.O.subtype a)) = _
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, _root_.one_mul,
    PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rfl

private theorem spMap_comp_spMap {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [spMap, spMap, spMap, CommRingCat.ofHom_comp, Spec.map_comp]

private theorem evAt_eq_of_eq {R : Type} [CommRing R] {X : Scheme.{0}} {a b : Sp R ⟶ X} (e : a = b) {U : X.Opens}
    (h : ⊤ ≤ a ⁻¹ᵁ U) (h' : ⊤ ≤ b ⁻¹ᵁ U) : evAt a h = evAt b h' := by
  subst e; rfl

theorem isRatPath_of_integral_at_places : ∀ (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E] [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (G : Over C) [GrpObj G] (ξ : Sp (PowerSeries E) ⟶ G.left) (u : Place k E → E), (∀ p, u p ≠ 0) → {p | ord p (u p) ≠ 0}.Finite → 0 < ∑ᶠ p, ord p (u p) → (∀ p : Place k E, ∃ (b : Sp p.O ⟶ C) (ζ : Sp (PowerSeries p.O) ⟶ G.left), spMap p.O.subtype ≫ b = spMap (algebraMap K E) ≫ x ∧ IsPath G 2 b ζ ∧ ξ = spMap (sc p (u p)) ≫ ζ) → IsRatPath ξ := by
  intro k K E _ _ _ _ _ _ _ _ _ _ C _ x hx G _ ξ u hu0 hfin hpos hloc
  choose b ζ hb hpath hξ using hloc
  have hFF : IsFF k E := (GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext k K (GlobalTheory.T.isFunctionFieldOfOneVariable_of_genericPointOfCurve k K C x hx)).2 E
  obtain ⟨p₀, -⟩ : ∃ p, ord p (u p) ≠ 0 := by
    by_contra hc
    push_neg at hc
    rw [finsum_eq_zero_of_forall_eq_zero hc] at hpos
    exact lt_irrefl _ hpos
  apply GlobalTheory.T.isRationalFormalPath_of_rationalExpansions E G.left ξ
  intro U _ h f
  set V : C.Opens := unitSec G ⁻¹ᵁ U with hV
  have hVne : (V : Set C).Nonempty := by
    let q : Sp E := IsLocalRing.closedPoint E
    refine ⟨(spMap p₀.O.subtype ≫ b p₀) q, ?_⟩
    have h2 : spMap (PowerSeries.constantCoeff (R := E)) ≫ ξ = spMap p₀.O.subtype ≫ b p₀ ≫ unitSec G := by
      rw [hξ p₀, ← Category.assoc, spMap_comp_spMap, constantCoeff_comp_sc, ← spMap_comp_spMap, Category.assoc,
        (hpath p₀).zero]
    have h3 : (spMap (PowerSeries.constantCoeff (R := E)) ≫ ξ) q ∈ U := h trivial
    rw [h2] at h3
    exact h3
  have hfinb := GlobalTheory.T.finite_places_centre_outside_open k K E C x hx V hVne
  have hUp : ∀ p, ⊤ ≤ (spMap (sc p (u p)) ≫ ζ p) ⁻¹ᵁ U := fun p => hξ p ▸ h
  choose e ψ he0 he1 heq using fun p => GlobalTheory.T.exists_bounded_denominator_along_valuationPath k E p (u p) G.left (ζ p) U (hUp p) f
  have key : ∀ p, ⊤ ≤ (b p) ⁻¹ᵁ V → ⊤ ≤ (ζ p) ⁻¹ᵁ U := by
    intro p hp
    haveI := isLocalHom_constantCoeff_ps p.O
    rw [GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.2.2.2.1 (PowerSeries p.O) G.left (ζ p) U]
    rw [← (IsLocalRing.comap_closedPoint (PowerSeries.constantCoeff (R := p.O)) :
      spMap (PowerSeries.constantCoeff (R := p.O)) (IsLocalRing.closedPoint p.O) = _)]
    show (spMap (PowerSeries.constantCoeff (R := p.O)) ≫ ζ p) (IsLocalRing.closedPoint p.O) ∈ U
    rw [(hpath p).zero]
    exact hp trivial
  refine GlobalTheory.T.isRational_powerSeries_of_adelicIntegral_positiveRadius k E hFF (evAt ξ h f) u e ψ hu0 hfin hpos he0 ?_ ?_
  · refine hfinb.subset fun p hp => ⟨b p, hb p, fun hbV => hp ?_⟩
    rw [he1 p (key p hbV), map_one]
    exact isUnit_one
  · intro p
    rw [evAt_eq_of_eq (hξ p) h (hUp p)]
    exact heq p

end GlobalTheory.Nef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRationalFormalPathOfIntegralAllPlacesStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRationalFormalPath_of_integral_allPlaces : ∀ (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E] [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (G : Over C) [GrpObj G] (ξ : Sp (PowerSeries E) ⟶ G.left) (u : Place k E → E), (∀ p, u p ≠ 0) → {p | ord p (u p) ≠ 0}.Finite → 0 < ∑ᶠ p, ord p (u p) → (∀ p : Place k E, ∃ (b : Sp p.O ⟶ C) (ζ : Sp (PowerSeries p.O) ⟶ G.left), spMap p.O.subtype ≫ b = spMap (algebraMap K E) ≫ x ∧ IsPath G 2 b ζ ∧ ξ = spMap (sc p (u p)) ≫ ζ) → IsRatPath ξ := by
  first | exact @GlobalTheory.Nef.isRatPath_of_integral_at_places | exact GlobalTheory.Nef.isRatPath_of_integral_at_places | (intros; apply GlobalTheory.Nef.isRatPath_of_integral_at_places <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentConstantPathEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentConstantPathEqZero
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

namespace GlobalTheory.Nef

theorem tan_triv_eq_zero : ∀ (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E] [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → ∀ (W : C.Modules) (r : ℕ) (i : W ⟶ Lie G), Mono i → ∀ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)), (V₀ : Set C).Nonempty → IsFrame s → ∀ w : Fin r → E, HasTan G (spMap (algebraMap K E) ≫ x) (triv G (spMap (algebraMap K E) ≫ x)) (fun j => i.app V₀ (s j)) w → w = 0 := by
  intro k K E _ _ _ _ _ _ _ _ _ _ C _ x hx G _ hG W r i hi V₀ s hV₀ hs w hw
  haveI := hG
  haveI := hi
  haveI : IsIntegral C := LieSemineg.isIntegral_curve hx.1.1 hx.1.2.2
  haveI : Smooth G.hom := hG.smooth
  obtain ⟨h₀, -, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_generic_injective_fraction K C x hx.2.1 V₀ hV₀
  have hp₀ : x (IsLocalRing.closedPoint K) ∈ V₀ := (GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.2.2.2.1 K C x V₀).1 h₀
  obtain ⟨U₁, n, om, hpU₁, hom⟩ := exists_isFrame_omega G (x (IsLocalRing.closedPoint K))
  obtain ⟨V', U, hpV', hV'le, c⟩ := GlobalTheory.Conormal.exists_isChart (he := sec_hom η[G])
    (show x (IsLocalRing.closedPoint K) ∈ V₀ ⊓ U₁ from ⟨hp₀, hpU₁⟩)
  have hV : V' ≤ V₀ := hV'le.trans inf_le_left
  have hVU : V' ≤ U₁ := hV'le.trans inf_le_right
  obtain ⟨hx', hinj, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_generic_injective_fraction K C x hx.2.1 V' ⟨_, hpV'⟩
  have hb : ⊤ ≤ (spMap (algebraMap K E) ≫ x) ⁻¹ᵁ V' := fun z _ => hx' (Set.mem_univ _)
  have hev : ∀ g : Γ(C, V'), evAt (spMap (algebraMap K E) ≫ x) hb g = algebraMap K E (evAt x hx' g) :=
    fun g => GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.1 K E C (algebraMap K E) x V' hx' hb g
  have key : ∀ f : Γ(G.left, U), ∑ j, w j * algebraMap K E (evAt x hx'
      (dualApp (i.app V₀ (s j)) hV (dUnit G c.le f))) = 0 := by
    intro f
    have h2 : ⊤ ≤ ((spMap (algebraMap K E) ≫ x) ≫ unitSec G) ⁻¹ᵁ U := fun z _ => c.le (hb (Set.mem_univ z))
    have hU : ⊤ ≤ (triv G (spMap (algebraMap K E) ≫ x)) ⁻¹ᵁ U := fun z _ => h2 (Set.mem_univ _)
    have := hw U hU V' hV c.le hb f
    simp only [hev] at this
    rw [← this]
    have e1 : evAt (triv G (spMap (algebraMap K E) ≫ x)) hU f = PowerSeries.C (R := E) (evAt _ h2 f) :=
      GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk.1 E (PowerSeries E) G.left (PowerSeries.C (R := E)) _ U h2 hU f
    rw [e1]
    simp
  have key2 : ∀ e' : Γ(omega G, V'), ∑ j, w j * algebraMap K E (evAt x hx'
      (dualApp (i.app V₀ (s j)) hV e')) = 0 := by
    intro e'
    obtain ⟨f, rfl⟩ := c.d_surjective (sec_hom η[G]) e'
    exact key f
  haveI : Nonempty V' := ⟨⟨_, hpV'⟩⟩
  let N : Matrix (Fin r) (Fin n) Γ(C, V') := fun j a => dualApp (i.app V₀ (s j)) hV (resM (omega G) hVU (om a))
  have hN : LinearIndependent Γ(C, V') N.row := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hl : (∑ j, g j • resM (Lie G) hV (i.app V₀ (s j))) = 0 := by
      refine hom.dual_ext hVU (fun a => ?_)
      have := congrFun hg a
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Matrix.row, N] at this
      rw [dualApp_sum, LinearMap.sum_apply, dualApp_zero, LinearMap.zero_apply]
      simpa only [dualApp_smul, LinearMap.smul_apply, smul_eq_mul, dualApp_res, GlobalTheory.LB.resG_self] using this
    have hs' : ∑ j, g j • resM W hV (s j) = 0 := by
      apply QCoh.injective_app_of_mono i V'
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_zero, Scheme.Modules.Hom.app_smul, Twist.app_resM]
      exact hl
    have hli := (hs.basis hV).linearIndependent
    rw [hs.coe_basis hV, Fintype.linearIndependent_iff] at hli
    exact hli g hs'
  obtain ⟨σ, hσ⟩ := LieSemineg.exists_det_ne_zero N hN
  let φ : Γ(C, V') →+* E := (algebraMap K E).comp (evAt x hx')
  have hφ : Function.Injective φ := (algebraMap K E).injective.comp hinj
  have hA : ((N.submatrix id σ).map φ).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact fun h => hσ (hφ (h.trans (map_zero φ).symm))
  refine Matrix.eq_zero_of_vecMul_eq_zero hA ?_
  funext a
  simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Matrix.submatrix_apply, id, Pi.zero_apply, N, φ,
    RingHom.comp_apply]
  exact key2 _

end GlobalTheory.Nef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentConstantPathEqZeroStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_constantPath_eq_zero : ∀ (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E] [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → ∀ (W : C.Modules) (r : ℕ) (i : W ⟶ Lie G), Mono i → ∀ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)), (V₀ : Set C).Nonempty → IsFrame s → ∀ w : Fin r → E, HasTan G (spMap (algebraMap K E) ≫ x) (triv G (spMap (algebraMap K E) ≫ x)) (fun j => i.app V₀ (s j)) w → w = 0 := by
  first | exact @GlobalTheory.Nef.tan_triv_eq_zero | exact GlobalTheory.Nef.tan_triv_eq_zero | (intros; apply GlobalTheory.Nef.tan_triv_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSubsheafLinesDegreeNonpos
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem linesLE_zero_of_sub_lie : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → ∀ (W : C.Modules) (r : ℕ) (i : W ⟶ Lie G), Mono i → ∀ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)) (g : Place k K → Matrix (Fin r) (Fin r) K), (V₀ : Set C).Nonempty → IsFrame s → admitted g → (∀ v, LocFrame x s v (g v)) → LinesLE g 0 := by
  intro k K _ _ _ _ _ C _ x hx G _ hG W r i hi V₀ s g hV₀ hs hg hloc
  intro E _ _ _ _ _ ρ hρ w hw
  simp only [zero_mul]
  by_contra hpos
  push_neg at hpos
  have hpos' : 0 < degLine (pullAd ρ g) w := by exact_mod_cast hpos
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap k E).injective
  letI : Algebra ℚ E := DivisionRing.toRatAlgebra

  have hne : Nonempty (Place k E) := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp [degLine, finsum_of_isEmpty] at hpos'
  obtain ⟨p₀⟩ := hne
  obtain ⟨b₀, V, t, V', h₀, h₁, hxV, M, -, -, -, -, -⟩ := hloc (ρ p₀)
  set b : Sp E ⟶ C := spMap (algebraMap K E) ≫ x with hb
  have hbV : ⊤ ≤ b ⁻¹ᵁ V₀ := by
    intro z _
    have hz := h₀ (hxV (show (spMap (algebraMap K E)).base z ∈ (⊤ : (Sp K).Opens) from trivial))
    show b.base z ∈ V₀
    simpa [hb] using hz
  haveI : QuasiSeparated G.hom := inferInstance
  obtain ⟨ξ, hξ, htan⟩ := GlobalTheory.T.exists_formalSquaringPath_with_tangentVector C G E hG.smooth inferInstance b r V₀ (fun j => i.app V₀ (s j)) w hbV

  have hvec : ∀ p : Place k E, (pullAd ρ g p).mulVec w ≠ 0 := by
    intro p h
    have hdet : (pullAd ρ g p).det ≠ 0 := by
      simp only [pullAd]
      have e := RingHom.map_det (algebraMap K E) (g (ρ p))
      rw [RingHom.mapMatrix_apply] at e
      rw [← e]
      exact (map_ne_zero _).mpr (hg.1 (ρ p))
    exact hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨w, hw, h⟩)
  have hu : ∀ p : Place k E, ∃ u : E, u ≠ 0 ∧ p.1 u = nrm p ((pullAd ρ g p).mulVec w) ∧
      ordVec p ((pullAd ρ g p).mulVec w) = ord p u := by
    intro p
    obtain ⟨j, hj0, hj1, hj2, -⟩ := ((GlobalTheory.T.functionFieldPlaceOrder_calculus k E p).2.2.2.2.2.2.1) r _ (hvec p)
    exact ⟨_, hj0, hj1.symm, hj2⟩
  choose u hu0 hu1 hu2 using hu
  have hsum : ∑ᶠ p, ord p (u p) = degLine (pullAd ρ g) w := by
    unfold degLine; exact finsum_congr fun p => (hu2 p).symm
  have hfin : {p | ord p (u p) ≠ 0}.Finite := by
    by_contra hinf
    have : ∑ᶠ p, ord p (u p) = 0 := finsum_of_infinite_support (by simpa [Function.support] using hinf)
    omega
  have hint := fun p => GlobalTheory.T.genericFormalPath_eq_scaling_valuationRingPath k K E C x hx G hG W r i V₀ s ρ hρ p (g (ρ p)) (hloc (ρ p)) w (u p) (hu0 p) (hu1 p) ξ hξ htan
  have hrat := GlobalTheory.T.isRationalFormalPath_of_integral_allPlaces k K E C x hx G ξ u hu0 hfin (by omega) hint
  have htriv : ξ = triv G b := GlobalTheory.T.rationalSquaringPathsRigid_of_isSemiAbelian C G hG E b ξ hξ hrat
  rw [htriv] at htan
  exact hw (GlobalTheory.T.tangent_constantPath_eq_zero k K E C x hx G hG W r i hi V₀ s hV₀ hs w htan)

end GlobalTheory.Nef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSubsheafLinesDegreeNonposStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_subsheaf_lines_degree_nonpos : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → ∀ (W : C.Modules) (r : ℕ) (i : W ⟶ Lie G), Mono i → ∀ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)) (g : Place k K → Matrix (Fin r) (Fin r) K), (V₀ : Set C).Nonempty → IsFrame s → admitted g → (∀ v, LocFrame x s v (g v)) → LinesLE g 0 := by
  first | exact @GlobalTheory.Nef.linesLE_zero_of_sub_lie | exact GlobalTheory.Nef.linesLE_zero_of_sub_lie | (intros; apply GlobalTheory.Nef.linesLE_zero_of_sub_lie <;> assumption)
end
