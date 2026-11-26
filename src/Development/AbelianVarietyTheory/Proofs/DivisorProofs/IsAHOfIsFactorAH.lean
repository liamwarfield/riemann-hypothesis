module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanBdLeSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClearDenominatorsFramePolynomialAtPrime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPointEigenbasisChangeDetIntegralAlmostAllPrime
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairWithSectionsRepresentsTensor

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusRM

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

def IsFactorAH (u : HolUnif A L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) : Prop :=
  Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧
    ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i →
      u.fr i z = χ l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) * u.fr i (z + l)

theorem isFactorAH_of_isAH {u : HolUnif A L g} {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (h : u.IsAH Hm χ) : IsFactorAH u Hm χ :=
  ⟨h.1, h.2.2.1, h.2.2.2⟩

theorem isAH_of_isFactorAH {u : HolUnif A L g} {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (h : IsFactorAH u Hm χ) (pos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) : u.IsAH Hm χ :=
  ⟨h.1, pos, h.2.1, h.2.2⟩

end GlobalTheory.TorusRM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyWeightSectionProducts
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CuspMulUnit

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem pow_mem_secZ' {ex : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ GlobalTheory.AllWt.secZ Xo c ex) (n : ℕ) :
    f ^ n ∈ GlobalTheory.AllWt.secZ Xo c (n • ex) := by
  induction n with
  | zero => rw [pow_zero, zero_smul]; exact GlobalTheory.AllWt.one_mem_secZ
  | succ n ih => rw [pow_succ, succ_nsmul]; exact GlobalTheory.AllWt.mul_mem_secZ ih hf

theorem eq_of_mem_secZ {e e' : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ GlobalTheory.AllWt.secZ Xo c e)
    (hf' : f ∈ GlobalTheory.AllWt.secZ Xo c e') (h0 : f ≠ 0) : e = e' := by
  classical
  by_contra hne
  apply h0
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  funext p y
  let u0 : (c.F)ˣ := Units.mk0 2 two_ne_zero
  let t : Ix Dw → (p.R)ˣ := Pi.mulSingle i (Units.map (algebraMap c.F p.R : c.F →* p.R) u0)
  have hw : ∀ d : Ix Dw → ℤ, ((∏ j, t j ^ d j : (p.R)ˣ) : p.R) = algebraMap c.F p.R ((2 : c.F) ^ d i) := by
    intro d
    rw [Finset.prod_eq_single i]
    · simp only [t, Pi.mulSingle_eq_same, ← map_zpow, Units.coe_map, MonoidHom.coe_coe, Units.val_zpow_eq_zpow_val,
        u0, Units.val_mk0]
    · intro j _ hj
      simp [t, Pi.mulSingle_eq_of_ne hj]
    · simp
  obtain ⟨y', hy'⟩ := GlobalTheory.SecSeparation.exists_frBor y t
  have e1 := hf.2 p t y y' hy'
  have e2 := hf'.2 p t y y' hy'
  rw [hw] at e1 e2
  have hne2 : (2 : c.F) ^ e i - (2 : c.F) ^ e' i ≠ 0 := by
    intro h
    apply hi
    have h1 : algebraMap ℚ c.F ((2 : ℚ) ^ e i) = algebraMap ℚ c.F ((2 : ℚ) ^ e' i) := by
      rw [map_zpow₀, map_zpow₀, map_ofNat]
      exact sub_eq_zero.1 h
    exact zpow_right_injective₀ (by norm_num) (by norm_num) ((algebraMap ℚ c.F).injective h1)
  have hu : IsUnit (algebraMap c.F p.R ((2 : c.F) ^ e i - (2 : c.F) ^ e' i)) := (IsUnit.mk0 _ hne2).map _
  show f p y = 0
  refine hu.mul_right_eq_zero.1 ?_
  rw [map_sub, sub_mul, ← e1, ← e2, sub_self]

end GlobalTheory.CuspMulUnit

namespace GlobalTheory.CuspMulUnit

theorem fj_mul_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r)
    (hE : 1 < Module.finrank ℚ E / 2) {la la' : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r} {P Q : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ}
    (hP : P ∈ X.SS la) (hQ : X.IsSec la' Q) (ξ : Fin r → E) (hξ : X.IsIso ξ) (x) (hx : x ∈ X.dom) :
    X.fj (la + la') ξ 0 (P * Q) x = 0 := by
  have hPs := hP.1.1
  have hm := ReciprocityTheory.ChartRestriction.G.FD.coefficientConvolution_holds (E := E) r X la la' P Q hPs hQ (GlobalTheory.CuspFrom.isModerate _ hE hPs)
    (GlobalTheory.CuspFrom.isModerate _ hE hQ) ξ hξ x hx 0
  have hz : ∀ ν, X.fj la ξ ν P x * X.fj la' ξ (0 - ν) Q x = 0 := by
    intro ν
    by_cases h1 : X.fj la ξ ν P x = 0
    · rw [h1, zero_mul]
    by_cases h2 : X.fj la' ξ (0 - ν) Q x = 0
    · rw [h2, mul_zero]
    exfalso
    have a1 := GlobalTheory.CuspFrom.freqNonneg _ hE hPs ξ hξ ν x hx h1
    have a2 := GlobalTheory.CuspFrom.freqNonneg _ hE hQ ξ hξ (0 - ν) x hx h2
    have hν : ν = 0 := funext fun τ => le_antisymm (by have := a2 τ; simp at this; exact this) (a1 τ)
    subst hν
    exact h1 (hP.2 ξ hξ x hx)
  simp only [hz] at hm
  exact hm.unique hasSum_zero


end GlobalTheory.CuspMulUnit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenomFramePolynomialsCmPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePolynomialCoeffIntegralAlmostAllPrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePolynomialCoeffIntegralAlmostAllPrimes
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
open GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.CoeffInt

theorem coeff_valuation_le_one_almost_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ), e none = 0 →
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 z.K)), ∀ p ∉ S,
      ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) →
      ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) z.K, (∀ (y' : FrPt Xo c z.K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K) (s : z.Kˣ),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) (s : z.K) z.y y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
        ∀ μ, p.valuation z.K (AddMonoidAlgebra.coeff G μ) ≤ 1 := by
  intro E _ _ _ H Dw l Xo c _ z f La hz e k he
  classical
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.cmPoint_eigenbasis_change_det_integral_almost_all_primes E H Dw l Xo c z f La hz
  have hfin : (⋃ j, {p : IsDedekindDomain.HeightOneSpectrum (𝓞 z.K) |
      FractionalIdeal.count z.K p (z.ℓ j).I ≠ 0}).Finite :=
    Set.finite_iUnion fun j => Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors (z.ℓ j).I)
  refine ⟨S₁ ∪ hfin.toFinset, fun p hp F hF hv G hG μ => ?_⟩
  simp only [Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.mem_iUnion, Set.mem_setOf_eq, not_exists,
    not_not] at hp
  obtain ⟨hp1, hp2⟩ := hp
  have hgen : ∀ j, Formalism.L2.LamCM.IsLocGen p (1 : z.K) (z.ℓ j).I := fun j =>
    ⟨one_ne_zero, by rw [FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one, hp2 j]⟩
  obtain ⟨T, iK, hT, hiK⟩ := GlobalTheory.T.exists_completeDVR_completion_integral_iff z.K p
  obtain ⟨M⟩ := (GlobalTheory.T.exists_cmPoint_localModel_over_dvr E H Dw l Xo c z T iK).1 fun a => (hiK _).2 (p.valuation_le_one a)
  let io : c.F →+* T.Fr := iK.comp (algebraMap c.F z.K)
  letI := io.toAlgebra
  let φ : z.K →ₐ[c.F] T.Fr := { iK with commutes' := fun _ => rfl }
  obtain ⟨yT, hyT⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ φ z.y
  have hyx : yT.x = spMap iK ≫ z.x := by rw [hyT.1, hz.2.2.2.1]
  obtain ⟨g, hg, hgL⟩ := (GlobalTheory.T.exists_integralEigenbasis_of_frame_at_localModel E H Dw l Xo c T io M.G.t M.t'.t _ M.m1 M.m2 yT hyx).1
  obtain ⟨s, hsS⟩ := GlobalTheory.T.exists_unit_integral_generator_principal_local_model E H Dw l Xo c T io M.G M.t'.t _ M.m1 M.m2 yT hyx
  obtain ⟨y', hy', -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c T.Fr yT g s hg
  have hL := hgL _ _ hy'
  have hS := hsS _ _ hy'
  have hinv : ∀ b j i, (g b)⁻¹ j i ∈ Set.range (algebraMap T.V T.Fr) := fun b j i => by
    have := GlobalTheory.T.lieLetter_integral_in_integral_eigenbasis E H Dw l Xo c z f La hz p T iK M hiK φ yT y' g s rfl hyT hy' hg hL b j i 1 (hgen _)
    rwa [map_one, _root_.one_mul] at this
  have hR : ∀ x : T.Fr, x ∈ Set.range (algebraMap T.V T.Fr) ↔ x ∈ (algebraMap T.V T.Fr).range :=
    fun x => (RingHom.mem_range).symm
  have hdetinv : ∀ b, ((g b).det)⁻¹ ∈ (algebraMap T.V T.Fr).range := fun b => by
    choose N hN using hinv b
    have e1 : (g b)⁻¹ = (Matrix.of N).map (algebraMap T.V T.Fr) := by
      ext j i; exact (hN j i).symm
    have e2 : ((g b).det)⁻¹ = ((g b)⁻¹).det := by
      rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    rw [e2, e1]
    exact ⟨(Matrix.of N).det, by rw [RingHom.map_det]; rfl⟩
  have hall := (hR _).1 (hS₁ p hp1 T iK hT hiK M φ yT y' g s rfl hyT hy' hg hL)
  have hdet : ∀ b, (g b).det ∈ (algebraMap T.V T.Fr).range := fun b => by
    have hne : (∏ b' ∈ Finset.univ.erase b, (g b').det) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun b' _ => (hg b').ne_zero
    have e3 : (g b).det = (∏ b', (g b').det) * ∏ b' ∈ Finset.univ.erase b, ((g b').det)⁻¹ := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ b), Finset.prod_inv_distrib, _root_.mul_assoc,
        mul_inv_cancel₀ hne, _root_.mul_one]
    rw [e3]
    exact Subring.mul_mem _ hall (Subring.prod_mem _ fun b' _ => hdetinv b')
  have hτ : (∏ b, (g b).det ^ k b) ∈ (algebraMap T.V T.Fr).range :=
    Subring.prod_mem _ fun b _ => Subring.pow_mem _ (hdet b) _
  obtain ⟨w, hw⟩ := GlobalTheory.T.framePolynomial_coeff_bounded_by_determinants E H Dw l Xo c z f La hz e k he p T iK hT hiK M φ yT y' g s rfl hyT hy' s.ne_zero hg hL
    hS (fun _ _ => 1) (fun b j i => by rw [_root_.one_mul]; exact hinv b j i) F hF hv G
    (fun y' Y hY hch => hG y' Y 1 hY (by rw [Units.val_one]; exact hch)) μ
  simp only [one_pow, Finset.prod_const_one, _root_.mul_one] at hw
  refine (hiK _).1 ((hR _).2 ?_)
  rw [hw]
  exact Subring.mul_mem _ hτ (RingHom.mem_range_self _ _)

end GlobalTheory.CoeffInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePolynomialCoeffIntegralAlmostAllPrimesStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framePolynomial_coeff_integral_almost_all_primes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ), e none = 0 →
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 z.K)), ∀ p ∉ S,
      ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) →
      ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) z.K, (∀ (y' : FrPt Xo c z.K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K) (s : z.Kˣ),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) (s : z.K) z.y y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
        ∀ μ, p.valuation z.K (AddMonoidAlgebra.coeff G μ) ≤ 1 := by
  first | exact @GlobalTheory.CoeffInt.coeff_valuation_le_one_almost_all | exact GlobalTheory.CoeffInt.coeff_valuation_le_one_almost_all | (intros; apply GlobalTheory.CoeffInt.coeff_valuation_le_one_almost_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenomFramePolynomialsCmPoint
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)

namespace GlobalTheory.LatFull.CMInt

theorem exists_coeff_denom_intWt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ), e none = 0 →
    ∃ t : 𝓞 z.K, t ≠ 0 ∧ ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) →
      ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) z.K,
        (∀ (y' : FrPt Xo c z.K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K) (s : z.Kˣ),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) (s : z.K) z.y y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
        ∀ μ, IsIntegral ℤ ((t : z.K) * AddMonoidAlgebra.coeff G μ) := by
  intro E _ _ _ H Dw l Xo c _ z f La hz e k he0
  classical
  obtain ⟨S, hS⟩ := GlobalTheory.T.framePolynomial_coeff_integral_almost_all_primes E H Dw l Xo c z f La hz e k he0
  choose x hx0 hx using GlobalTheory.T.exists_clear_denominators_framePolynomial_at_prime E H Dw l Xo c z f La hz e k he0
  refine ⟨∏ p ∈ S, x p, Finset.prod_ne_zero_iff.2 fun p _ => hx0 p, fun F hF hv G hG μ => ?_⟩
  have hint : ∀ r : 𝓞 z.K, ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 z.K), p.valuation z.K (r : z.K) ≤ 1 :=
    fun r p => p.valuation_le_one r
  have hv1 : ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 z.K),
      p.valuation z.K (((∏ q ∈ S, x q : 𝓞 z.K) : z.K) * AddMonoidAlgebra.coeff G μ) ≤ 1 := by
    intro p
    by_cases hp : p ∈ S
    · rw [← Finset.mul_prod_erase S x hp]
      have e1 : (((x p * ∏ q ∈ S.erase p, x q : 𝓞 z.K)) : z.K) * AddMonoidAlgebra.coeff G μ =
          ((∏ q ∈ S.erase p, x q : 𝓞 z.K) : z.K) * (((x p : 𝓞 z.K) : z.K) * AddMonoidAlgebra.coeff G μ) := by
        push_cast; ring
      rw [e1, map_mul]
      exact mul_le_one' (hint _ p) (hx p F hF hv G hG μ)
    · rw [map_mul]
      exact mul_le_one' (hint _ p) (hS p hp F hF hv G hG μ)
  obtain ⟨r, hr⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one z.K _ hv1
  rw [← hr]
  exact RingOfIntegers.isIntegral_coe r

end GlobalTheory.LatFull.CMInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenomFramePolynomialsCmPointStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_commonDenom_framePolynomials_cmPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ), e none = 0 →
    ∃ t : 𝓞 z.K, t ≠ 0 ∧ ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) →
      ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) z.K,
        (∀ (y' : FrPt Xo c z.K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K) (s : z.Kˣ),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) (s : z.K) z.y y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
        ∀ μ, IsIntegral ℤ ((t : z.K) * AddMonoidAlgebra.coeff G μ) := by
  first | exact @GlobalTheory.LatFull.CMInt.exists_coeff_denom_intWt | exact GlobalTheory.LatFull.CMInt.exists_coeff_denom_intWt | (intros; apply GlobalTheory.LatFull.CMInt.exists_coeff_denom_intWt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundlePullbackGrpPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundlePullbackGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem lbIso_lam_pull_of_isGrpPullback : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G₁ : Over S') [GrpObj G₁] [IsCommMonObj G₁] (β : G₁.left ⟶ G.left), IsGrpPullback G₁ G f β → ∃ β₂ : (G2 G₁).left ⟶ (G2 G).left, Geo.Tor.IsSquare β β₂ ∧ ∀ (L : LB G.left) (N : LB G₁.left) (X : Scheme.{0}) (Q : LB X) (h : (G2 G).left ⟶ X), L.IsLB → N.IsLB → Q.IsLB → LBIso N (L.pull β) → LBIso (abelian₂ G L) (Q.pull h) → LBIso (abelian₂ G₁ N) (Q.pull (β₂ ≫ h)) := by
  intro S S' f G _ _ G₁ _ _ β hpb
  let U : Over.mk ((G2 G₁).hom ≫ f) ⟶ G2 G := lift (pushPt hpb.1.w (fst G₁ G₁)) (pushPt hpb.1.w (snd G₁ G₁))
  have hU1 : U ≫ fst G G = pushPt hpb.1.w (fst G₁ G₁) := lift_fst _ _
  have hU2 : U ≫ snd G G = pushPt hpb.1.w (snd G₁ G₁) := lift_snd _ _
  refine ⟨U.left, ⟨congrArg (fun z => z.left) hU1, congrArg (fun z => z.left) hU2⟩, ?_⟩
  intro L N X Q h hL hN hQ hNL hLam
  have hx : ∀ i, pushPt hpb.1.w (x2 G₁ i) = U ≫ x2 G i := by
    intro i
    fin_cases i
    · exact hU1.symm
    · exact hU2.symm
  have e₁ : LBIso ((abelian₂ G L).pull U.left) (abelian₂ G₁ N) :=
    GlobalTheory.CM.TripleModel.lbIso_cube_pull hpb hL hN hNL.symm (x2 G₁) (x2 G) U hx
  have hLamL : (abelian₂ G L).IsLB := DVR.linComb_isLB _ hL _ _
  have e₂ : LBIso ((abelian₂ G L).pull U.left) (Q.pull (U.left ≫ h)) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (abelian₂ G L) U.left U.left rfl)
      (chartPullSame Q (fun _ => U.left ≫ h) (fun _ => h) (fun _ => 1) U.left fun _ => rfl) hLam
  exact LBIso.trans (DVR.linComb_isLB _ hN _ _) (pull_isLB hLamL _) (pull_isLB hQ _) e₁.symm e₂

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundlePullbackGrpPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mumfordBundle_pullback_grpPullback : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G₁ : Over S') [GrpObj G₁] [IsCommMonObj G₁] (β : G₁.left ⟶ G.left), IsGrpPullback G₁ G f β → ∃ β₂ : (G2 G₁).left ⟶ (G2 G).left, Geo.Tor.IsSquare β β₂ ∧ ∀ (L : LB G.left) (N : LB G₁.left) (X : Scheme.{0}) (Q : LB X) (h : (G2 G).left ⟶ X), L.IsLB → N.IsLB → Q.IsLB → LBIso N (L.pull β) → LBIso (abelian₂ G L) (Q.pull h) → LBIso (abelian₂ G₁ N) (Q.pull (β₂ ≫ h)) := by
  first | exact @GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback | exact GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback | (intros; apply GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConjSeq

variable (p : ℕ) [Fact p.Prime]

abbrev frobR (R : Type) [CommRing R] (hR : (p : R) = 0) : R →+* R :=
  GlobalTheory.SS.FrobField.powHom R p 1 Fact.out hR

theorem frobR_apply (R : Type) [CommRing R] (hR : (p : R) = 0) (x : R) : frobR p R hR x = x ^ p :=
  congrArg (x ^ ·) (pow_one p)

theorem frob_sp (R : Type) [CommRing R] (hR : (p : R) = 0) (h : (p : Γ(Sp R, ⊤)) = 0) :
    GlobalTheory.VB.frob (Sp R) p h = spMap (frobR p R hR) :=
  GlobalTheory.SS.FrobField.absFrob_spec R p 1 Fact.out h _ fun _ ↦ rfl

theorem frob_comp_hom (R : Type) [CommRing R] (hR : (p : R) = 0) {X : Scheme.{0}} (f : X ⟶ Sp R)
    (h : (p : Γ(X, ⊤)) = 0) : GlobalTheory.VB.frob X p h ≫ f = f ≫ spMap (frobR p R hR) := by
  have h0 : (p : Γ(Sp R, ⊤)) = 0 := GlobalTheory.SS.FrobField.cast_zero_sp R hR
  have hn : GlobalTheory.VB.frob X p h ≫ f = f ≫ GlobalTheory.VB.frob (Sp R) p h0 :=
    GlobalTheory.SS.FrobField.absFrob_nat f p 1 Fact.out h h0
  rw [hn, frob_sp p R hR h0]

theorem cast_left (R : Type) [CommRing R] (hR : (p : R) = 0) (A : Over (Sp R)) :
    (p : Γ(A.left, ⊤)) = 0 :=
  GlobalTheory.SS.FrobField.cast_zero_of_hom A.hom (GlobalTheory.SS.FrobField.cast_zero_sp R hR)

theorem frobMor (R : Type) [CommRing R] (hR : (p : R) = 0) (A : Over (Sp R)) [GrpObj A]
    (h : (p : Γ(A.left, ⊤)) = 0) :
    GrpMor (dp0 R) (𝟙 _) A (dp0 R) (𝟙 _) A (frobR p R hR) (spMap (frobR p R hR))
      (GlobalTheory.VB.frob A.left p h) := by
  refine { dp := isDPMorphism_of_eq_bot _ rfl _ _, base := ?_,
           w := frob_comp_hom p R hR A.hom h, mul := ?_ }
  · simp
  · intro T x y x₀ y₀ hx hy
    have hT : (p : Γ(T.left, ⊤)) = 0 := cast_left p R hR T
    have hn (f : T.left ⟶ A.left) :
        GlobalTheory.VB.frob T.left p hT ≫ f = f ≫ GlobalTheory.VB.frob A.left p h :=
      GlobalTheory.SS.FrobField.absFrob_nat f p 1 Fact.out hT h
    let j : Over.mk (T.hom ≫ spMap (frobR p R hR)) ⟶ T :=
      Over.homMk (GlobalTheory.VB.frob T.left p hT) (by simpa using frob_comp_hom p R hR T.hom hT)
    have ex : x₀ = j ≫ x := Over.OverMorphism.ext (by
      simp only [hx, Over.comp_left, Over.homMk_left, j, hn])
    have ey : y₀ = j ≫ y := Over.OverMorphism.ext (by
      simp only [hy, Over.comp_left, Over.homMk_left, j, hn])
    subst ex ey
    rw [← MonObj.comp_mul]
    simp only [Over.comp_left, Over.homMk_left, j]
    exact hn (x * y).left

def frobDR (R : Type) [CommRing R] (hR : (p : R) = 0) (A : Over (Sp R)) [GrpObj A] :
    primDR A →ₛₗ[frobR p R hR] primDR A :=
  (frobMor p R hR A (cast_left p R hR A)).pull

def conjDR (R : Type) [CommRing R] (hR : (p : R) = 0) (A : Over (Sp R)) [GrpObj A] :
    Submodule R (primDR A) :=
  Submodule.span R (Set.range (frobDR p R hR A))

end GlobalTheory.ConjSeq

namespace GlobalTheory.DeRhamSheaf

open Limits

variable {T : Scheme.{0}} (A : Over T) [GrpObj A]

end GlobalTheory.DeRhamSheaf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.ThetaOne

open GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

variable {V₁ : Type} [CommRing V₁] [IsDomain V₁]

abbrev toF (F : Type) [Field F] [Algebra (FractionRing V₁) F] : V₁ →+* F :=
  (algebraMap (FractionRing V₁) F).comp (algebraMap V₁ (FractionRing V₁))

theorem tF_hom (F : Type) [Field F] [Algebra (FractionRing V₁) F] :
    jFK (R := V₁) F ≫ jK V₁ = Spec.map (CommRingCat.ofHom (toF (V₁ := V₁) F)) := by
  rw [jFK, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem prB_hom' (D : DegPre V₁) (F : Type) [Field F] [Algebra (FractionRing V₁) F] :
    (DegPre.prB D F).left ≫ D.P.A.hom = famBase D F ≫ Spec.map (CommRingCat.ofHom (toF (V₁ := V₁) F)) := by
  rw [← tF_hom]
  exact (Over.w (DegPre.prB D F)).trans (Over.w (fst (TF (R := V₁) F) D.P.A)).symm

def termF (D : DegPre V₁) (F : Type) [Field F] [Algebra (FractionRing V₁) F] (k : ℕ) (α : D.X) :
    SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB α) (DegPre.famε k)) →ₛₗ[toF (V₁ := V₁) F] FamTerm D F k α :=
  pullOver D.P.L _ (prB_hom' D F) (famφ_prB D F α)

def pullTo (D : DegPre V₁) {R' : Type} [CommRing R'] (f : V₁ →+* R') :
    SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)) →ₛₗ[f]
      SecOver (fst (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left
        (LB.LinComb D.P.L (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left ≫ D.famφB 0 i)
          (DegPre.famε 1)) :=
  pullOver D.P.L _ ((Over.w (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A)).trans
    (Over.w (fst (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A)).symm) (fun _ => rfl)

theorem isPullSecLC_pullTo (D : DegPre V₁) {R' : Type} [CommRing R'] (f : V₁ →+* R')
    (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) :
    IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left
      θ (pullTo D f θ) := fun _ => rfl

abbrev OneBasisAt (D : DegPre V₁) {R' : Type} [CommRing R'] (f : V₁ →+* R')
    (θ' : LB.Sec (LB.LinComb D.P.L (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left ≫ D.famφB 0 i)
      (DegPre.famε 1))) : Prop :=
  IsSecBasis (T := Over.mk (Spec.map (CommRingCat.ofHom f))) (A := D.P.A) _ (fun _ : Fin 1 => θ')

theorem exists_theta [IsLocalRing V₁] (hV : IsCN V₁) (D : DegPre V₁) :
    ∃ θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)),
      ∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
        IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
        OneBasisAt D f θ' := by
  haveI : IsNoetherianRing V₁ := hV.1
  obtain ⟨m, b, hm, hb⟩ := GlobalTheory.twistBaseChange V₁ D 1 le_rfl 0
  obtain rfl : m = 1 := hm.trans (one_pow _)
  refine ⟨b 0, fun R' _ f θ' h => ?_⟩
  exact hb R' f (fun _ => θ') (fun i => by rw [Subsingleton.elim i 0]; exact h)

theorem exists_ne_zero (D : DegPre V₁) {K : Type} [Field K] (f : V₁ →+* K) θ' (h : OneBasisAt D f θ') :
    ∃ j, θ'.f j ≠ 0 := by
  by_contra hc
  push_neg at hc
  obtain ⟨r, -, hu⟩ := h θ'
  have h1 := hu (fun _ => 1) (fun j => by rw [Fin.sum_univ_one, map_one, map_one, _root_.one_mul])
  have h0 := hu (fun _ => 0) (fun j => by rw [Fin.sum_univ_one, map_zero, map_zero, MulZeroClass.zero_mul, hc j])
  have e10 := congrFun (h1.trans h0.symm) 0
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv e10
  simp at this

theorem basis_BF (D : DegPre V₁) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (hθ : ∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
      IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
      OneBasisAt D f θ')
    (F : Type) [Field F] [Algebra (FractionRing V₁) F] :
    IsSecBasis (T := TF (R := V₁) F) (A := D.P.A) _
      (fun _ : Fin 1 => (termF D F 1 0 θ : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F 0) (DegPre.famε 1)))) := by
  have gen : ∀ (t : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of V₁)), t = Spec.map (CommRingCat.ofHom (toF (V₁ := V₁) F)) →
      ∀ (hp : (snd (Over.mk t) D.P.A).left ≫ D.P.A.hom =
          (fst (Over.mk t) D.P.A).left ≫ Spec.map (CommRingCat.ofHom (toF (V₁ := V₁) F)))
        (φ : Fin 4 → ((Over.mk t ⊗ D.P.A).left ⟶ D.P.A.left))
        (hφ : ∀ i, φ i = (snd (Over.mk t) D.P.A).left ≫ D.famφB 0 i),
      IsSecBasis (T := Over.mk t) (A := D.P.A) _
        (fun _ : Fin 1 => (pullOver D.P.L (DegPre.famε 1) hp hφ θ : LB.Sec (LB.LinComb D.P.L φ (DegPre.famε 1)))) := by
    rintro t rfl hp φ hφ
    obtain rfl : φ = fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom (toF (V₁ := V₁) F)))) D.P.A).left ≫ D.famφB 0 i :=
      funext hφ
    exact hθ F (toF F) _ (isPullSecLC_pullTo D _ θ)
  exact gen _ (tF_hom F) (prB_hom' D F) _ (famφ_prB D F 0)

theorem existsUnique_scalar (D : DegPre V₁) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (hθ : ∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
      IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
      OneBasisAt D f θ')
    (F : Type) [Field F] [Algebra (FractionRing V₁) F] (th : Fam D F 1) :
    ∃! c : F, famProj D F 1 0 th = c • termF D F 1 0 θ := by
  obtain ⟨r, hr, hu⟩ := basis_BF D θ hθ F (th.s 0)
  let e := (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv
  refine ⟨e (r 0), SecOps.sec_ext fun j => ?_, fun c hc => ?_⟩
  · refine (hr j).trans ?_
    rw [Fin.sum_univ_one]
    show _ = resTop _ ((famBase D F).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (e (r 0)))) * _
    rw [show (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (e (r 0)) = r 0 from e.symm_apply_apply (r 0)]
    rfl
  · have h2 := hu (fun _ => e.symm c) (fun j => by
      rw [Fin.sum_univ_one]
      exact congrArg (fun s : FamTerm D F 1 0 => LB.Sec.f s j) hc)
    have h3 := congrFun h2 0
    rw [← h3]
    exact (e.apply_symm_apply c).symm

theorem fe_from_zero (hG : GlobalFnsSt) (D : DegPre V₁) (F : Type) [Field F] [Algebra (FractionRing V₁) F]
    (th : Fam D F 1) (mu : D.X) :
    ∃ u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F 1 0 mu) (DegPre.deltaε 1)), u.IsGen ∧
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (DegPre.famMult D F 1 mu 0) ∧
      GeneratorPullback.SecRel D.P.L (DegPre.famφ D F (0 + 1 • mu)) (DegPre.famε 1) (th.s (0 + 1 • mu))
        (DegPre.famφ D F 0) (DegPre.famε 1) (th.s 0) (DegPre.trF D F mu).left
        (DegPre.deltaφ D F 1 0 mu) (DegPre.deltaε 1) u := by
  obtain ⟨u, hu, hc⟩ := (gen_fe (D := D) (F := F) hG 1 mu 0).1
  exact ⟨u, hu, hc, th.fe mu 0 u hu hc⟩

theorem eq_of_term_zero (hG : GlobalFnsSt) (D : DegPre V₁) (F : Type) [Field F] [Algebra (FractionRing V₁) F]
    {th th' : Fam D F 1} (h : th.s 0 = th'.s 0) : th = th' := by
  refine fam_ext fun β => ?_
  have key : ∀ x, x = 0 + 1 • β → ∀ j, (th.s x).f j = (th'.s x).f j := by
    rintro x rfl j
    have hL := D.P.isLB
    obtain ⟨u, hu, hc⟩ := (gen_fe (D := D) (F := F) hG 1 β 0).1
    refine sec_ext_val hL (fun y J hJ => ?_) j
    rw [(secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (th.fe β 0 u hu hc) _ _ y J hJ,
      (secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (th'.fe β 0 u hu hc) _ _ y J hJ, h]
  exact key β (by rw [zero_add, one_smul])

theorem c_zero (D : DegPre V₁) : D.c 0 = (1 : 𝟙_ _ ⟶ D.P.A) := by
  have h := D.c_add 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem main [IsLocalRing V₁] (hV : IsCN V₁) (D : DegPre V₁) :
    ∃ θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)),
      (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
        IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
        OneBasisAt D f θ') ∧
      (∀ (K : Type) [Field K] (f : V₁ →+* K), ∃ j, (pullTo D f θ).f j ≠ 0) ∧
      (∀ (F : Type) [Field F] [Algebra (FractionRing V₁) F] (th : Fam D F 1),
        ∃! c : F, famProj D F 1 0 th = c • termF D F 1 0 θ) ∧
      (∀ (F : Type) [Field F] [Algebra (FractionRing V₁) F] (th : Fam D F 1) (mu : D.X),
        ∃ u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F 1 0 mu) (DegPre.deltaε 1)), u.IsGen ∧
          LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (DegPre.famMult D F 1 mu 0) ∧
          GeneratorPullback.SecRel D.P.L (DegPre.famφ D F (0 + 1 • mu)) (DegPre.famε 1) (th.s (0 + 1 • mu))
            (DegPre.famφ D F 0) (DegPre.famε 1) (th.s 0) (DegPre.trF D F mu).left
            (DegPre.deltaφ D F 1 0 mu) (DegPre.deltaε 1) u) ∧
      (∀ (F : Type) [Field F] [Algebra (FractionRing V₁) F] (th th' : Fam D F 1), th.s 0 = th'.s 0 → th = th') := by
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  obtain ⟨θ, hθ⟩ := exists_theta hV D
  exact ⟨θ, hθ, fun K _ f => exists_ne_zero D f _ (hθ K f _ (isPullSecLC_pullTo D f θ)),
    fun F _ _ th => existsUnique_scalar D θ hθ F th, fun F _ _ th mu => fe_from_zero hG D F th mu,
    fun F _ _ _ _ h => eq_of_term_zero hG D F h⟩

end GlobalTheory.Poinc.ThetaOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetNumberQuotientBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultAddMultConj
set_option autoImplicit false

namespace GlobalTheory.ConjugateMultiplicitySum

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem conj_eq_iff {z w : ℂ} {d : ℕ} (hd : 0 < d) (hz : z ^ 2 = -(d : ℂ)) (hw : w ^ 2 = -(d : ℂ)) :
    starRingEnd ℂ z = w ↔ ¬ z = w := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hre : z.re * z.re - z.im * z.im = -(d : ℝ) := by
    have := congrArg Complex.re hz
    simpa [pow_two] using this
  have him : z.re * z.im = 0 := by
    have := congrArg Complex.im hz
    simp [pow_two] at this
    linarith
  have hre0 : z.re = 0 := by
    rcases mul_eq_zero.1 him with h | h
    · exact h
    · rw [h] at hre
      nlinarith [mul_self_nonneg z.re]
  have hc : starRingEnd ℂ z = -z := by
    apply Complex.ext <;> simp [hre0]
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hre
    exact hd.ne' hre
  rw [hc]
  constructor
  · intro h1 h2
    apply hz0
    have : (2 : ℂ) * z = 0 := by linear_combination h2 - h1
    simpa using this
  · intro h
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hz.trans hw.symm) with h1 | h1
    · exact absurd h1 h
    · rw [h1, neg_neg]

theorem mult_add_mult_conj {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    (τ : E →+* ℂ) : Datum.mult D τ + Datum.mult D (conjEmb τ) = D.p + D.q := by
  have hsq : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    have h := congrArg (fun a : 𝓞 E => τ (algebraMap (𝓞 E) E a)) H.rt_sq
    simpa using h
  have key : conjEmb τ (H.rt : E) = H.rt0 ↔ ¬ τ (H.rt : E) = H.rt0 :=
    conj_eq_iff H.d_prime.pos hsq H.sqrt_neg_disc_sq
  unfold Datum.mult
  by_cases h : τ (H.rt : E) = H.rt0
  · rw [if_pos h, if_neg (fun h' => key.1 h' h)]
  · rw [if_neg h, if_pos (key.2 h), add_comm]

end GlobalTheory.ConjugateMultiplicitySum
end

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RefSum.NumPt

theorem jet_real {f m r t b g dF R : ℝ} (hf0 : 0 ≤ f) (hm0 : 0 ≤ m) (hr0 : 0 ≤ r) (hd0 : 0 ≤ dF)
    (ht : 11 ≤ t) (hf : f ≤ t) (hm : m ≤ t) (hr : r ≤ t) (hb : t ^ 7 ≤ b) (hd : dF ≤ f * r * (2 * (2 * b) + 1))
    (hR : R ≤ b) (hg : b ^ 8 ≤ g) :
    4 * dF + 4 ≤ g ∧ dF * (2 * Real.sqrt (2 * f * m)) < g ∧
      R * (2 * f * m) ^ 3 * (r * (2 * f * m) / 4 + 2 * dF ^ 2) / g ≤ 1 / 2500 := by
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hp : ∀ n : ℕ, n ≤ 7 → t ^ n ≤ b := fun n hn => (pow_le_pow_right₀ ht1 hn).trans hb
  have h100 : 100 ≤ b := by nlinarith [hp 2 (by norm_num)]
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hfr : f * r ≤ t ^ 2 := by rw [sq]; exact mul_le_mul hf hr hr0 (by linarith)
  have hfm : f * m ≤ t ^ 2 := by rw [sq]; exact mul_le_mul hf hm hm0 (by linarith)
  have ht2 : 0 ≤ t ^ 2 := by positivity
  have h5 : 5 * t ^ 2 ≤ b := by
    have : t ^ 3 = t * t ^ 2 := by ring
    nlinarith [hp 3 (by norm_num)]
  have hdb : dF ≤ b ^ 2 := by
    have h1 : f * r * (2 * (2 * b) + 1) ≤ t ^ 2 * (5 * b) := mul_le_mul hfr (by linarith) (by linarith) ht2
    nlinarith
  have hN0 : 0 ≤ 2 * f * m := by positivity
  have hN : 2 * f * m ≤ b := by nlinarith
  have hN3 : (2 * f * m) ^ 3 ≤ b := by
    have h1 : (2 * f * m) ^ 3 ≤ (2 * t ^ 2) ^ 3 := pow_le_pow_left₀ hN0 (by linarith) 3
    have h2 : t ^ 7 = t * t ^ 6 := by ring
    have h3 : (2 * t ^ 2) ^ 3 = 8 * t ^ 6 := by ring
    have h4 : 0 ≤ t ^ 6 := by positivity
    nlinarith
  have hrb : r ≤ b := hr.trans (by simpa using hp 1 (by norm_num))
  have hs : Real.sqrt (2 * f * m) ≤ b := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hq : ∀ n : ℕ, 100 * b ^ n ≤ b ^ (n + 1) := fun n => by
    rw [pow_succ, mul_comm]; exact mul_le_mul_of_nonneg_left h100 (by positivity)
  have e2 : 1 ≤ b ^ 2 := one_le_pow₀ hb1
  have q2 := hq 2
  have q3 := hq 3
  have q4 := hq 4
  have q5 := hq 5
  have q6 := hq 6
  have q7 := hq 7
  norm_num at q2 q3 q4 q5 q6 q7
  refine ⟨by linarith, ?_, ?_⟩
  · have h1 : dF * (2 * Real.sqrt (2 * f * m)) ≤ b ^ 2 * (2 * b) :=
      mul_le_mul hdb (by linarith) (by positivity) (by positivity)
    have h2 : b ^ 2 * (2 * b) = 2 * b ^ 3 := by ring
    linarith
  · rw [div_le_iff₀ (by linarith)]
    have h1 : r * (2 * f * m) ≤ b ^ 2 := by rw [sq]; exact mul_le_mul hrb hN hN0 (by linarith)
    have h2 : dF ^ 2 ≤ b ^ 4 := by
      have := pow_le_pow_left₀ hd0 hdb 2
      rwa [← pow_mul] at this
    have h3 : R * (2 * f * m) ^ 3 ≤ b * b := mul_le_mul hR hN3 (by positivity) (by linarith)
    have h4 : R * (2 * f * m) ^ 3 * (r * (2 * f * m) / 4 + 2 * dF ^ 2) ≤ b * b * (3 * b ^ 4) :=
      mul_le_mul h3 (by linarith) (by positivity) (by positivity)
    have h5 : b * b * (3 * b ^ 4) = 3 * b ^ 6 := by ring
    linarith

theorem finrank_host (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := D.host.finrank_E'

theorem jetNum_of_sizes {D : D7} {L : SizeData₂ D} (S : SizesAt L) {dF : ℕ}
    (hd : (dF : ℝ) ≤ D.R.f * D.R.r * (2 * (2 * L.sc.b) + 1)) : JetNum D dF (1 / 2500) := by
  obtain ⟨-, -, -, -, -, sC, sQD, -, -, -, -, -, -, -, -, -, -, -, -, -, sG, -⟩ := S
  obtain ⟨-, -, -, -, -, -, h1, h2⟩ := sQD
  have a1 := D.R.two_le_m
  have a2 := D.R.m_add_three_le_k
  have a3 : D.R.r + 5 ≤ D.R.t := D.R.rank_add_five_le
  have a4 : D.R.f ≤ D.R.k := D.R.f_le_k
  have a5 : D.R.k ≤ D.R.r ∧ D.R.m ≤ D.R.r ∧ 6 ≤ D.R.r := by unfold Ranks.r; omega
  have ht : (11 : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : 11 ≤ D.R.t)
  have hf : (D.R.f : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : D.R.f ≤ D.R.t)
  have hm : (D.R.m : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : D.R.m ≤ D.R.t)
  have hr : (D.R.r : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : D.R.r ≤ D.R.t)
  have hk : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hL : 0 ≤ L.sc.L := Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp hL
  have hsb : Real.sqrt L.sc.b ≤ L.sc.b := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hq : (1 : ℝ) ≤ D.host.q := by exact_mod_cast D.host.hyp.1.one_lt.le
  have hd' : (1 : ℝ) ≤ D.host.d := by exact_mod_cast D.host.hyp.2.1.one_lt.le
  have hn : (1 : ℝ) ≤ D.R.n := by exact_mod_cast D.R.ord_pos
  have hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by nlinarith
  have hs : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hc : D.host.rdE ≤ szCond L := by
    unfold szCond
    have h0 : (0 : ℝ) ≤ D.host.QS := Nat.cast_nonneg _
    have : (D.host.QS : ℝ) * Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ D.host.QS * ((D.host.q : ℝ) * D.host.d) :=
      mul_le_mul_of_nonneg_left hs h0
    nlinarith [mul_nonneg h0 (Real.sqrt_nonneg ((D.host.q : ℝ) * D.host.d))]
  have hc1 : (1 : ℝ) ≤ szCond L := h1.trans hc
  have ht1 : (1 : ℝ) ≤ D.R.t := by linarith
  have sC' : szCond L ^ 36 * (D.R.t : ℝ) ^ 150 ≤ L.sc.b := le_trans sC hsb
  have hb : (D.R.t : ℝ) ^ 7 ≤ L.sc.b :=
    ((pow_le_pow_right₀ ht1 (by norm_num)).trans (le_mul_of_one_le_left (by positivity) (one_le_pow₀ hc1))).trans sC'
  have hrd : D.host.rdE ^ 2 ≤ L.sc.b :=
    (((pow_le_pow_left₀ (by linarith) hc 2).trans (pow_le_pow_right₀ hc1 (by norm_num))).trans
      (le_mul_of_one_le_right (by positivity) (one_le_pow₀ ht1))).trans sC'
  have hR : rr0 D ≤ L.sc.b := by
    have hn1 : (1 : ℝ) ≤ Module.finrank ℚ D.host.E := by exact_mod_cast Module.finrank_pos
    have e : |(NumberField.discr D.host.E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ D.host.E) = D.host.rdE ^ 2 := by
      unfold Formalism.BasicNotions.Host.rdE
      rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
      congr 1
      push_cast
      ring
    unfold rr0
    rw [e]
    exact (div_le_self (by positivity) (by linarith)).trans hrd
  intro k
  have hg : L.sc.b ^ 8 ≤ (D.host.g k : ℝ) :=
    (pow_le_pow_left₀ (by linarith) (le_mul_of_one_le_left (by linarith) hk) 8).trans (sG k k).1
  obtain ⟨c1, c2, c3⟩ := jet_real (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    ht hf hm hr hb hd hR hg
  exact ⟨by exact_mod_cast c1, c2, c3⟩

section Cols

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem mult_add_mult_conj (D : Datum H) (τ : E →+* ℂ) :
    D.mult τ + D.mult (ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ) = D.p + D.q :=
  _root_.GlobalTheory.ConjugateMultiplicitySum.mult_add_mult_conj D τ

theorem two_mul_rank_le_nCol (Dw : Datum H) : 2 * (Dw.p + Dw.q) ≤ nCol Dw := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h := mult_add_mult_conj Dw τ
  have hle : ∀ σ, Dw.mult σ ≤ Fintype.card (Lt1 Dw) := fun σ => by
    have := Fintype.card_le_of_injective (fun i : Fin (Dw.mult σ) => (⟨σ, i⟩ : Lt1 Dw))
      (@sigma_mk_injective _ (fun τ => Fin (Dw.mult τ)) σ)
    rwa [Fintype.card_fin] at this
  have h1 := hle τ
  have h2 := hle (ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ)
  unfold nCol
  omega

end Cols

theorem log_g_le {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (hL : 1 ≤ L.sc.L) (hf : 1 ≤ D.R.f) (hr : 1 ≤ D.R.r) :
    Real.log (D.host.g 0) + Real.log (D.host.g 1) ≤ (2 + 2 * P.CYL) * zBase L ^ 12 := by
  obtain ⟨Y, h1, -, h3, h4⟩ := P.g_Y
  have hk : (0 : ℝ) < D.R.k := by exact_mod_cast (by have := D.R.m_add_three_le_k; omega : 0 < D.R.k)
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hY : 0 < Y := lt_of_lt_of_le (by positivity) h1
  have hg : ∀ i, Real.log (D.host.g i) ≤ L.sc.L + P.CYL * L.sc.L := fun i => by
    have a := Real.log_le_log (hY.trans_le (h4 i).1) (h4 i).2
    rw [Real.log_mul two_ne_zero hY.ne'] at a
    have := Real.log_two_lt_d9
    linarith
  have hf' : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hr' : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr
  have hZ : L.sc.L ≤ zBase L := le_mul_of_one_le_left (by linarith) (one_le_mul_of_one_le_of_one_le hf' hr')
  have hZ' : L.sc.L ≤ zBase L ^ 12 := hZ.trans (le_self_pow₀ (hL.trans hZ) (by norm_num))
  have := mul_le_mul_of_nonneg_left hZ' (show 0 ≤ 2 + 2 * P.CYL by linarith [P.CYL_pos])
  linarith [hg 0, hg 1]

end GlobalTheory.RefSum.NumPt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisOfPolAVPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisOfPolAVPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem hypS_polAV_pullback : ∀ {S S' : Scheme.{0}} (P : PolAV S) (P' : PolAV S') (f : S' ⟶ S) (ψ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f ψ → LBIso P'.L (P.L.pull ψ) → HypS P.A P.L → HypS P'.A P'.L :=
  fun {S S'} P P' f ψ h hb hS =>
    GlobalTheory.SymBaseChange.hypS_baseChange S S' P.A P'.A f ψ P.L P'.L P.isLB P'.isLB h hb hS

end GlobalTheory.Poinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisOfPolAVPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleSymmetryHypothesis_of_polAV_pullback : ∀ {S S' : Scheme.{0}} (P : PolAV S) (P' : PolAV S') (f : S' ⟶ S) (ψ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f ψ → LBIso P'.L (P.L.pull ψ) → HypS P.A P.L → HypS P'.A P'.L := by
  first | exact @GlobalTheory.Poinc.hypS_polAV_pullback | exact GlobalTheory.Poinc.hypS_polAV_pullback | (intros; apply GlobalTheory.Poinc.hypS_polAV_pullback <;> assumption)
end
end
