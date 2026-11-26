module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdditiveCharacterSuperdiagTrivial

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericCharacterTrivialSuperdiagonalOffException
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleIdempotentSmulMemLatticeCompletionAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleIdempotentSmulMemLatticeCompletionAtPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

namespace GlobalTheory.FinPlLoc

theorem idem_smul_mem_latMul_at : ∀ (D : D7) (S : HSp D) (𝔞 : Set D.host.E) (L : GlobalTheory.FinPl.Lat S) (v : GlobalTheory.FinPl.Pl D) (z : Fin S.rank → AE D), z ∈ GlobalTheory.FinPl.latMul S 𝔞 L (fun _ => True) → GlobalTheory.FinPlLoc.idem D (· = v) • z ∈ GlobalTheory.FinPl.latMul S 𝔞 L (· = v) := by
  intro D S 𝔞 L v z hz
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hαi, -, a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨ePl D (· = v) * α, fun w => ?_, fun w hw => ?_, a, ha, x, hx, ?_⟩
    · rw [map_mul]
      exact mul_mem (ePl_int _ w) (hαi w)
    · rw [map_mul, evalV_ePl, if_neg hw, zero_mul]
    · funext i
      rw [Pi.smul_apply, smul_eq_mul]
      unfold idem
      rw [Algebra.TensorProduct.tmul_mul_tmul, ← pairA_mul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg y _ h => rw [smul_neg]; exact neg_mem h

end GlobalTheory.FinPlLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleIdempotentSmulMemLatticeCompletionAtPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adeleIdempotent_smul_mem_latticeCompletionAtPlace : ∀ (D : D7) (S : HSp D) (𝔞 : Set D.host.E) (L : GlobalTheory.FinPl.Lat S) (v : GlobalTheory.FinPl.Pl D) (z : Fin S.rank → AE D), z ∈ GlobalTheory.FinPl.latMul S 𝔞 L (fun _ => True) → GlobalTheory.FinPlLoc.idem D (· = v) • z ∈ GlobalTheory.FinPl.latMul S 𝔞 L (· = v) := by
  first | exact @GlobalTheory.FinPlLoc.idem_smul_mem_latMul_at | exact GlobalTheory.FinPlLoc.idem_smul_mem_latMul_at | (intros; apply GlobalTheory.FinPlLoc.idem_smul_mem_latMul_at <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AuxiliaryWittIsotropicCoordinateEqPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AuxiliaryWittIsotropicCoordinateEqPairing
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.AscFin

theorem coeff_monic_poly_sum {K R : Type} [CommRing K] [CommRing R] (φ : K →+* R) {n : ℕ} (u s : K) (h : s * u = 1)
    (b : Fin n → K) (G : Matrix (Fin n) (Fin n) K) (x : Fin n → R) :
    φ u * ∑ l, φ (∑ k, (s * b k) * G k l) * x l = ∑ k, ∑ l, φ (b k) * φ (G k l) * x l := by
  have hus : φ u * φ s = 1 := by rw [← map_mul, mul_comm, h, map_one]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  linear_combination (φ (b k) * φ (G k l) * x l) * hus

private theorem cT_sig_eq_conjTranspose' {D : D7} {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) M = Mᴴ := rfl

private theorem cA_incA_apply_eq_incA_star {D : D7} (e : D.host.E) : cA D (incA D e) = incA D (star e) := rfl

theorem incA_neg_xi0_pow_mul_pX_mulVec_eq_sum : ∀ {D : D7} {A B B₀ : HSp D} {c ρ : ℕ} (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ), c = 2 * ρ → IsAuxiliaryVectorWittDec a d → ∀ (i : Fin ρ) (hi : 2 * ρ - 1 - i.1 < c) (x : Fin B.rank → AE D), incA D ((-D.host.xi0) ^ (i.1 + 1)) * (d.pX *ᵥ x) i = ∑ k, ∑ l, cA D (incA D (a.a k ⟨2 * ρ - 1 - i.1, hi⟩)) * incA D (B.gram k l) * x l := by
  intro D A B B₀ c ρ a d hc hA i hi x
  obtain ⟨h2, he, s, he'⟩ := hA
  have hle : ρ ≤ c := by omega
  have hj : ∀ hle : ρ ≤ c, (Fin.castLE hle i).rev = (⟨2 * ρ - 1 - i.1, hi⟩ : Fin c) := fun hle => by
    ext
    simp only [Fin.val_rev, Fin.coe_castLE]
    omega
  have g1 := congrFun (congrFun a.gram ⟨2 * ρ - 1 - i.1, hi⟩) (Fin.castLE hle i)
  have g2 := congrFun (congrFun d.e'e i) i
  rw [he, he'] at g2
  simp only [antiDiagonalSignGramMatrix, cT_sig_eq_conjTranspose', Matrix.mul_apply, Matrix.conjTranspose_apply, colsOf, star_mul', Matrix.one_apply_eq, hj,
    Fin.coe_castLE] at g1 g2
  rw [if_pos (by omega), if_neg (fun h => by have := congrArg Fin.val h; simp only [Fin.coe_castLE] at this; omega)] at g1
  have g3 : ∑ l, (∑ k, star (s i) * star (a.a k ⟨2 * ρ - 1 - i.1, hi⟩) * HSpace.gram B k l) *
      ((-D.host.xi0) ^ (i.1 + 1) * a.a l (Fin.castLE hle i)) =
      star (s i) * (-D.host.xi0) ^ (i.1 + 1) *
        ∑ l, (∑ k, star (a.a k ⟨2 * ρ - 1 - i.1, hi⟩) * HSpace.gram B k l) * a.a l (Fin.castLE hle i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [mul_assoc (star (s i)), ← Finset.mul_sum]
    ring
  have key : star (s i) * (-D.host.xi0) ^ (i.1 + 1) = 1 := by
    linear_combination g2 - g3 - (star (s i) * (-D.host.xi0) ^ (i.1 + 1)) * g1
  simp only [HypDec.pX, HypDec.qX, GlobalTheory.MixModel.rat, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, he', colsOf, star_mul', hj, cA_incA_apply_eq_incA_star]
  exact coeff_monic_poly_sum (incA D) _ _ key (fun k => star (a.a k ⟨2 * ρ - 1 - i.1, hi⟩)) (HSpace.gram B) x

end GlobalTheory.AscFin

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AuxiliaryWittIsotropicCoordinateEqPairingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.auxiliaryWittIsotropicCoordinate_eq_pairing : ∀ {D : D7} {A B B₀ : HSp D} {c ρ : ℕ} (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ), c = 2 * ρ → IsAuxiliaryVectorWittDec a d → ∀ (i : Fin ρ) (hi : 2 * ρ - 1 - i.1 < c) (x : Fin B.rank → AE D), incA D ((-D.host.xi0) ^ (i.1 + 1)) * (d.pX *ᵥ x) i = ∑ k, ∑ l, cA D (incA D (a.a k ⟨2 * ρ - 1 - i.1, hi⟩)) * incA D (B.gram k l) * x l := by
  first | exact @GlobalTheory.AscFin.incA_neg_xi0_pow_mul_pX_mulVec_eq_sum | exact GlobalTheory.AscFin.incA_neg_xi0_pow_mul_pX_mulVec_eq_sum | (intros; apply GlobalTheory.AscFin.incA_neg_xi0_pow_mul_pX_mulVec_eq_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleIdempotentMulIntegralOfUnitFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleIdempotentMulIntegralOfUnitFactor
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.UnitAtPl

open GlobalTheory.FinPlLoc (idem ePl evalV_ePl ePl_int idem_mem_idAt idem_mul_self finPart_pair)

variable {D : D7}

theorem evalV_inv_mem (x : GlobalTheory.FinPl.Pl D) (c : 𝓞 D.host.F) (hc : c ∉ x.asIdeal) :
    evalV D.host.F x (algebraMap D.host.F (Af D.host.F) ((c : D.host.F))⁻¹) ∈ x.adicCompletionIntegers D.host.F := by
  rw [AlgHom.commutes, HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : x.intValuation c = 1 := HeightOneSpectrum.intValuation_eq_one_iff.2 hc
  have h2 := HeightOneSpectrum.valuation_of_algebraMap (K := D.host.F) x c
  rw [h1] at h2
  show Valued.v ((((c : D.host.F))⁻¹ : D.host.F) : x.adicCompletion D.host.F) ≤ 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀]
  have : HeightOneSpectrum.valuation D.host.F x (c : D.host.F) = 1 := h2
  rw [this, inv_one]

theorem inv_ePl_int (x : GlobalTheory.FinPl.Pl D) (c : 𝓞 D.host.F) (hc : c ∉ x.asIdeal) :
    ((c : D.host.F))⁻¹ • ePl D (· = x) ∈ intAf D.host.F := by
  intro w
  rw [Algebra.smul_def, map_mul, evalV_ePl]
  split_ifs with h
  · subst h; rw [mul_one]; exact evalV_inv_mem w c hc
  · rw [mul_zero]; exact zero_mem _

theorem tmul_one_mul_mem {γ : Af D.host.F} (hγ : γ ∈ intAf D.host.F) {w : Af D.host.F ⊗[D.host.F] D.host.E}
    (hw : w ∈ intAE D) : (γ ⊗ₜ[D.host.F] (1 : D.host.E)) * w ∈ intAE D := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    refine AddSubgroup.subset_closure ⟨γ * α, fun v => ?_, o, rfl⟩
    rw [map_mul]
    exact mul_mem (hγ v) (hα v)
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem finPart_idem_inv (x : GlobalTheory.FinPl.Pl D) (c : 𝓞 D.host.F) :
    finPart D (idem D (· = x) * incA D ((c : D.host.F) : D.host.E)⁻¹) =
      (((c : D.host.F))⁻¹ • ePl D (· = x)) ⊗ₜ[D.host.F] (1 : D.host.E) := by
  have h0 : idem D (· = x) * incA D ((c : D.host.F) : D.host.E)⁻¹ =
      pairA D.host.F 0 (ePl D (· = x)) ⊗ₜ[D.host.F] ((c : D.host.F) : D.host.E)⁻¹ := by
    change (pairA D.host.F 0 (ePl D (· = x)) ⊗ₜ[D.host.F] (1 : D.host.E)) *
      ((1 : AF D.host.F) ⊗ₜ[D.host.F] ((c : D.host.F) : D.host.E)⁻¹) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have h1 : ((c : D.host.F) : D.host.E)⁻¹ = ((c : D.host.F))⁻¹ • (1 : D.host.E) := by
    rw [Algebra.smul_def, map_inv₀, mul_one]; rfl
  rw [h0, finPart_pair, h1, TensorProduct.tmul_smul, TensorProduct.smul_tmul']

theorem idem_mul_mem_of_unit : ∀ (D : D7) (v : GlobalTheory.FinPl.Pl D) (u : 𝓞 D.host.F), u ∉ v.asIdeal → ∀ z : AE D, GlobalTheory.FinPlLoc.idem D (· = v) * incA D ((u : D.host.F) : D.host.E) * z ∈ intAt D (· = v) → GlobalTheory.FinPlLoc.idem D (· = v) * z ∈ intAt D (· = v) := by
  intro D v u hu z hz
  have hu0 : ((u : D.host.F) : D.host.E) ≠ 0 := by
    intro h
    apply hu
    have h' : (u : D.host.F) = 0 := by exact_mod_cast h
    have h'' : u = 0 := by exact_mod_cast h'
    rw [h'']; exact zero_mem _
  have hinc : incA D ((u : D.host.F) : D.host.E)⁻¹ * incA D ((u : D.host.F) : D.host.E) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hu0, map_one]
  have key : idem D (· = v) * z = (idem D (· = v) * incA D ((u : D.host.F) : D.host.E)⁻¹) *
      (idem D (· = v) * incA D ((u : D.host.F) : D.host.E) * z) := by
    calc idem D (· = v) * z = (idem D (· = v) * idem D (· = v)) *
        (incA D ((u : D.host.F) : D.host.E)⁻¹ * incA D ((u : D.host.F) : D.host.E)) * z := by
          rw [idem_mul_self, hinc, mul_one]
      _ = _ := by ring
  refine ⟨Ideal.mul_mem_right _ _ (idem_mem_idAt _), ?_⟩
  rw [key, (finPart D).map_mul, finPart_idem_inv]
  exact tmul_one_mul_mem (inv_ePl_int v u hu) hz.2

end GlobalTheory.UnitAtPl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleIdempotentMulIntegralOfUnitFactorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adeleIdempotent_mul_integral_of_unit_factor : ∀ (D : D7) (v : GlobalTheory.FinPl.Pl D) (u : 𝓞 D.host.F), u ∉ v.asIdeal → ∀ z : AE D, GlobalTheory.FinPlLoc.idem D (· = v) * incA D ((u : D.host.F) : D.host.E) * z ∈ intAt D (· = v) → GlobalTheory.FinPlLoc.idem D (· = v) * z ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.UnitAtPl.idem_mul_mem_of_unit | exact GlobalTheory.UnitAtPl.idem_mul_mem_of_unit | (intros; apply GlobalTheory.UnitAtPl.idem_mul_mem_of_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitMemSpanStaircaseIdealProducts
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitMemSpanStaircaseIdealProducts
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.StairUnit

theorem exists_mem_modul_notMem {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) (v : GlobalTheory.FinPl.Pl D)
    (hv : v ∉ P.S0) : ∃ u : 𝓞 D.host.F, u ∉ v.asIdeal ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) u ∈ P.modul sc := by
  have h : ∀ v' : GlobalTheory.FinPl.Pl D, ∃ x : 𝓞 D.host.F, x ∉ v.asIdeal ∧ (v' ∈ P.S0 → x ∈ v'.asIdeal) := by
    intro v'
    by_cases h' : v' ∈ P.S0
    · have hn : ¬ v'.asIdeal ≤ v.asIdeal := fun hle =>
        hv (HeightOneSpectrum.ext (v'.isMaximal.eq_of_le v.isPrime.ne_top hle) ▸ h')
      obtain ⟨x, hx, hx'⟩ := Set.not_subset.1 hn
      exact ⟨x, hx', fun _ => hx⟩
    · exact ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, fun h => absurd h h'⟩
  choose x hx hx' using h
  refine ⟨∏ v' ∈ P.S0, x v' ^ P.depth sc v', fun hu => ?_, ?_⟩
  · haveI := v.isPrime
    obtain ⟨v', -, h'⟩ := Ideal.IsPrime.prod_mem_iff.1 hu
    exact hx v' (v.isPrime.mem_of_pow_mem _ h')
  · rw [map_prod]
    refine Ideal.prod_mem_prod fun v' h' => ?_
    rw [map_pow]
    refine Ideal.pow_mem_pow ?_ _
    have h1 : x v' ∈ ((P.w v').under (𝓞 D.host.F)).asIdeal := by rw [P.under_w h']; exact hx' v' h'
    exact h1

theorem mem_span_of_mem_mul {E : Type} [Field E] [NumberField E] [StarRing E] {A B A' B' C : FractionalIdeal (𝓞 E)⁰ E}
    (hA : ∀ x ∈ A', star x ∈ A) (hB : ∀ x ∈ B', star x ∈ B) {t : E} (ht : t ∈ A' * B' * C) :
    t ∈ Submodule.span (𝓞 E) {t : E | ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, t = star (a * b) * c} := by
  refine FractionalIdeal.mul_induction_on ht (fun x hx c hc => ?_) fun x y => Submodule.add_mem _
  refine FractionalIdeal.mul_induction_on (C := fun x => x * c ∈ Submodule.span (𝓞 E)
    {t : E | ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, t = star (a * b) * c}) hx (fun a ha b hb => ?_) fun x y hx hy => ?_
  · exact Submodule.subset_span ⟨_, hA a ha, _, hB b hb, c, hc, by rw [star_mul', star_star, star_star]⟩
  · rw [add_mul]; exact Submodule.add_mem _ hx hy

theorem exists_unit_mem_span : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (ρ : ℕ) (p : Fin (2 * ρ + 2 - 1)) (q : Fin (2 * ρ + 1 - 1)), p.1 + q.1 = 2 * ρ → ∀ v : GlobalTheory.FinPl.Pl D, v ∉ G.pl.S0 → ∃ u : 𝓞 D.host.F, u ∉ v.asIdeal ∧ ((u : D.host.F) : D.host.E) ∈ Submodule.span (𝓞 D.host.E) {t : D.host.E | ∃ a ∈ D.host.AA, ∃ c' ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q, ∃ c ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) p, t = D.host.conj (a * c') * c} := by
  intro D T L sc G ρ p q hpq v hv
  obtain ⟨u, hu, hum⟩ := exists_mem_modul_notMem G.pl sc v hv
  refine ⟨u, hu, ?_⟩
  have hs : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  obtain ⟨hAA, hAAc⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1
  obtain ⟨hA, hconj⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L G.pl sc
  have hne : ∀ {I J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E}, I ≠ 0 → (∀ x, x ∈ J ↔ star x ∈ I) → J ≠ 0 := by
    intro I J hI hJ h0
    apply hI
    rw [FractionalIdeal.eq_zero_iff] at h0 ⊢
    intro y hy
    have h2 := h0 _ ((hJ (star y)).2 (by rwa [star_star]))
    rwa [star_eq_zero] at h2
  have hAb := hne hA hconj
  have hAAb := hne hAA hAAc
  have hB : ∀ x ∈ (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q.rev)⁻¹,
      star x ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q := by
    intro x hx
    have h1 := (GlobalTheory.ChiGrid.stairId_ne_zero_and_mem_rev_iff D _ _ hA hconj _ q.rev).2 (star x)
    rw [Fin.rev_rev, star_star] at h1
    exact h1.2 hx
  have key : D.host.AAbar * (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q.rev)⁻¹ *
      stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) p =
      ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
    have hq := q.2
    have e1 : 2 * ρ + 1 - 1 - q.rev.1 = q.1 + 1 := by rw [Fin.val_rev]; omega
    have e2 : q.rev.1 + 1 = p.1 := by rw [Fin.val_rev]; omega
    have e3 : 2 * ρ + 2 - 1 - p.1 = q.1 + 1 := by omega
    have e4 : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
        D.host.AAbar * (G.pl.stAbar sc)⁻¹ := by
      rw [Places.stAbar, mul_inv, inv_inv, mul_inv_cancel_left₀ hAAb]
    unfold stairId
    rw [e1, e2, e3, e4, pow_succ (G.pl.stAbar sc) p.1]
    have h1 : G.pl.stA sc ^ (q.1 + 1) ≠ 0 := pow_ne_zero _ hA
    have h2 : G.pl.stAbar sc ^ p.1 ≠ 0 := pow_ne_zero _ hAb
    field_simp
  have hmem : ((u : D.host.F) : D.host.E) ∈
      ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :=
    (FractionalIdeal.mem_coeIdeal _).2 ⟨_, hum, rfl⟩
  rw [← key] at hmem
  have h := mem_span_of_mem_mul (fun x hx => (hAAc x).1 hx) hB hmem
  simp only [hs] at h
  exact h

end GlobalTheory.StairUnit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitMemSpanStaircaseIdealProductsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_mem_span_staircaseIdeal_products : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (ρ : ℕ) (p : Fin (2 * ρ + 2 - 1)) (q : Fin (2 * ρ + 1 - 1)), p.1 + q.1 = 2 * ρ → ∀ v : GlobalTheory.FinPl.Pl D, v ∉ G.pl.S0 → ∃ u : 𝓞 D.host.F, u ∉ v.asIdeal ∧ ((u : D.host.F) : D.host.E) ∈ Submodule.span (𝓞 D.host.E) {t : D.host.E | ∃ a ∈ D.host.AA, ∃ c' ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q, ∃ c ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) p, t = D.host.conj (a * c') * c} := by
  first | exact @GlobalTheory.StairUnit.exists_unit_mem_span | exact GlobalTheory.StairUnit.exists_unit_mem_span | (intros; apply GlobalTheory.StairUnit.exists_unit_mem_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianPairingSelfDualCompletionIntegralAtPlac
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianPairingSelfDualCompletionIntegralAtPlac
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.LatPairInt

variable {D : D7}

theorem cA_tmul (p : AF D.host.F) (t : D.host.E) :
    cA D (p ⊗ₜ[D.host.F] t) = p ⊗ₜ[D.host.F] (star t) :=
  rfl

theorem intAt_zero (P : GlobalTheory.FinPl.Pl D → Prop) : (0 : AE D) ∈ intAt D P :=
  ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩

theorem intAt_add {P : GlobalTheory.FinPl.Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) :
    a + b ∈ intAt D P :=
  ⟨add_mem ha.1 hb.1, by rw [map_add]; exact add_mem ha.2 hb.2⟩

theorem intAt_neg {P : GlobalTheory.FinPl.Pl D → Prop} {a : AE D} (ha : a ∈ intAt D P) : -a ∈ intAt D P :=
  ⟨neg_mem ha.1, by rw [map_neg]; exact neg_mem ha.2⟩

theorem pair_mul (α β : Af D.host.F) :
    pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) :=
  Prod.ext (by show (0 : Ainf D.host.F) * 0 = 0; rw [zero_mul]) rfl

theorem term_eq (p q : AF D.host.F) (a g b : D.host.E) :
    cA D (p ⊗ₜ[D.host.F] a) * incA D g * (q ⊗ₜ[D.host.F] b) = (p * q) ⊗ₜ[D.host.F] (star a * g * b) := by
  rw [cA_tmul]
  change (p ⊗ₜ[D.host.F] star a) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] g) * (q ⊗ₜ[D.host.F] b) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem pairing_mem (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (hL : IsSelfDualC S L) (P : GlobalTheory.FinPl.Pl D → Prop)
    (z w : Fin S.rank → AE D) (hz : z ∈ latV S L P) (hw : w ∈ latV S L P) :
    (∑ k, ∑ l, cA D (w k) * incA D (S.gram k l) * z l) ∈ intAt D P := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hαi, hα, a, ha, x, hx, rfl⟩ := hz
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨β, hβi, hβ, a', ha', x', hx', rfl⟩ := hw
      rw [Set.mem_singleton_iff] at ha ha'
      subst ha ha'
      obtain ⟨b, hb⟩ := (hL.2 x).1 hx x' hx'
      have e : (∑ k, ∑ l, cA D (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x' k)) * incA D (S.gram k l) *
          (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x l))) =
          pairA D.host.F 0 (β * α) ⊗ₜ[D.host.F] (b : D.host.E) := by
        rw [hb, TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [term_eq, pair_mul, one_mul, one_mul]
      show (∑ k, ∑ l, cA D (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x' k)) * incA D (S.gram k l) *
          (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x l))) ∈ intAt D P
      rw [e]
      refine ⟨GlobalTheory.FinPlLoc.pair_mem_idAt P _ (fun v hv => by rw [map_mul, hα v hv, mul_zero]) _, ?_⟩
      rw [GlobalTheory.FinPlLoc.finPart_pair]
      refine AddSubgroup.subset_closure ⟨β * α, fun v => ?_, b, rfl⟩
      rw [map_mul]; exact mul_mem (hβi v) (hαi v)
    | zero =>
      simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero]
      exact intAt_zero P
    | add w₁ w₂ _ _ h₁ h₂ =>
      simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]
      exact intAt_add h₁ h₂
    | neg w _ h =>
      simp only [Pi.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]
      exact intAt_neg h
  | zero =>
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    exact intAt_zero P
  | add z₁ z₂ _ _ h₁ h₂ =>
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    exact intAt_add h₁ h₂
  | neg z _ h =>
    simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    exact intAt_neg h

theorem pairing_mem_at : ∀ (D : D7) (S : HSp D) (L : GlobalTheory.FinPl.Lat S), IsSelfDualC S L → ∀ (v : GlobalTheory.FinPl.Pl D) (z w : Fin S.rank → AE D), z ∈ latV S L (· = v) → w ∈ latV S L (· = v) → (∑ k, ∑ l, cA D (w k) * incA D (S.gram k l) * z l) ∈ intAt D (· = v) :=
  fun _ S L hL v z w hz hw => pairing_mem S L hL (· = v) z w hz hw

end GlobalTheory.LatPairInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianPairingSelfDualCompletionIntegralAtPlacStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianPairing_selfDual_completion_integral_at_place : ∀ (D : D7) (S : HSp D) (L : GlobalTheory.FinPl.Lat S), IsSelfDualC S L → ∀ (v : GlobalTheory.FinPl.Pl D) (z w : Fin S.rank → AE D), z ∈ latV S L (· = v) → w ∈ latV S L (· = v) → (∑ k, ∑ l, cA D (w k) * incA D (S.gram k l) * z l) ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.LatPairInt.pairing_mem_at | exact GlobalTheory.LatPairInt.pairing_mem_at | (intros; apply GlobalTheory.LatPairInt.pairing_mem_at <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericCharacterTrivialSuperdiagonalOffException
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.UniOff

open GlobalTheory.FinPlLoc (idem idem_mem_idAt idem_mem_intAt idem_mul_self cA_idem mem_idAt_iff ePl ePl_int evalV_ePl)

theorem intAt_neg {D : D7} {v : GlobalTheory.FinPl.Pl D} {z : AE D} (h : z ∈ intAt D (· = v)) : -z ∈ intAt D (· = v) :=
  ⟨neg_mem h.1, by rw [map_neg]; exact neg_mem h.2⟩

theorem intAt_add {D : D7} {v : GlobalTheory.FinPl.Pl D} {z w : AE D} (h : z ∈ intAt D (· = v)) (h' : w ∈ intAt D (· = v)) :
    z + w ∈ intAt D (· = v) :=
  ⟨add_mem h.1 h'.1, by rw [map_add]; exact add_mem h.2 h'.2⟩

theorem idem_incA_mem {D : D7} (v : GlobalTheory.FinPl.Pl D) (o : 𝓞 D.host.E) :
    idem D (· = v) * incA D (o : D.host.E) ∈ intAt D (· = v) := by
  refine ⟨Ideal.mul_mem_right _ _ (idem_mem_idAt _), ?_⟩
  rw [map_mul, GlobalTheory.IdeleAA.finPart_incA]
  unfold idem
  rw [GlobalTheory.FinPlLoc.finPart_pair, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  exact AddSubgroup.subset_closure ⟨ePl D (· = v), ePl_int _, o, rfl⟩

theorem idem_incA {D : D7} (P : GlobalTheory.FinPl.Pl D → Prop) (e : D.host.E) :
    idem D P * incA D e = pairA D.host.F 0 (ePl D P) ⊗ₜ[D.host.F] e := by
  unfold idem
  show (pairA D.host.F 0 (ePl D P) ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem gen_mem {D : D7} (S : HSp D) (𝔞 : Set D.host.E) (L : GlobalTheory.FinPl.Lat S) (v : GlobalTheory.FinPl.Pl D)
    (P : GlobalTheory.FinPl.Pl D → Prop) (hP : ∀ w, ¬ P w → w ≠ v) {a : D.host.E} (ha : a ∈ 𝔞) {x : Fin S.rank → D.host.E}
    (hx : x ∈ L) : (fun m => idem D (· = v) * incA D (a * x m)) ∈ GlobalTheory.FinPl.latMul S 𝔞 L P := by
  apply AddSubgroup.subset_closure
  refine ⟨ePl D (· = v), ePl_int _, fun w hw => by rw [evalV_ePl, if_neg (hP w hw)], a, ha, x, hx, ?_⟩
  funext m
  exact idem_incA _ _

theorem col_mem {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    (p : Fin c) {t : D.host.E} (ht : t ∈ 𝔟 p) : (fun m => t * d.a m p) ∈ d.lat Λ 𝔟 := by
  classical
  refine ⟨0, Λ.zero_mem, Pi.single p t, fun q => ?_, ?_⟩
  · by_cases hq : q = p
    · subst hq; simpa using ht
    · rw [Pi.single_eq_of_ne hq]; exact (𝔟 q).zero_mem
  · funext m
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]

theorem uni_off : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (M : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))), M ∈ latRow G (2 * ρ + 1) → ∀ i j : Fin ρ, j.1 = i.1 + 1 → ∀ v : GlobalTheory.FinPl.Pl D, v ∉ G.pl.S0 → ∀ o ∈ intAt D (· = v), psiE W.ψ (o * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j) = 1 := by
  intro D _ T L _ _ sc G W _ _ F hF ρ h M hM i j hij v hv o ho
  classical
  have h1 : 1 ≤ 2 * ρ + 2 := by omega
  have h1' : 1 ≤ 2 * ρ + 1 := by omega
  have h2' : 2 * ρ + 1 ≤ D.R.m := by omega
  obtain ⟨hleB, heB, -, -⟩ := hF.hB ρ h

  obtain ⟨α, hα⟩ := GlobalTheory.IdeleAA.exists_idele_AA D W.ψ W.ψ_std
  obtain ⟨hA, hψ⟩ := hα v

  have sdV : IsSelfDualC (G.V (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 2) 0)) :=
    (G.isV (X := .grid (2 * ρ + 2) 0) ⟨h, Nat.zero_le _⟩ fun j hj => by
      obtain ⟨h3, -⟩ := Node.grid.inj hj; omega).sd
  have sdW : IsSelfDualC (G.V (.grid (2 * ρ + 1) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) :=
    (G.isV (X := .grid (2 * ρ + 1) 0) ⟨h2', Nat.zero_le _⟩ fun j hj => by
      obtain ⟨h3, -⟩ := Node.grid.inj hj; omega).sd
  have hMlat := (GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ (isSelfDualC_neg sdV) sdW (fun _ => True) M).1 hM.1

  set aB := (G.colDec (2 * ρ + 2) h1 h).a with haB
  set aJ := (G.colDec (2 * ρ + 1) h1' h2').a with haJ
  set p : Fin (2 * ρ + 2 - 1) := Fin.castLE (by omega) j with hp
  have hq : 2 * ρ - 1 - i.1 < 2 * ρ + 1 - 1 := by omega
  set q : Fin (2 * ρ + 1 - 1) := ⟨2 * ρ - 1 - i.1, hq⟩ with hqdef
  set colB : Fin (G.V (.grid (2 * ρ + 2) 0)).rank → AE D := fun l => incA D (aB l p) with hcolB
  set g : AE D := ∑ k, ∑ l, cA D (incA D (aJ k q)) * incA D ((G.V (.grid (2 * ρ + 1) 0)).gram k l) * (M *ᵥ colB) l
    with hg

  have hcol : ∀ k, (M ⬝ (F.dB ρ h).jX) k j = incA D ((-D.host.xi0) ^ (j.1 + 1)) * (M *ᵥ colB) k := by
    intro k
    simp only [Matrix.mul_apply, GlobalTheory.MixModel.HypDec.jX, heB, Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [GlobalTheory.MixModel.rat, Matrix.map_apply, colsOf, hcolB, map_mul, map_pow, hp]
    ring
  have hN : ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j = incA D (-D.host.xi0) * g := by
    have e1 : ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j = ((F.dJ ρ h).pX *ᵥ fun k => (M ⬝ (F.dB ρ h).jX) k j) i := rfl
    have e2 := GlobalTheory.T.auxiliaryWittIsotropicCoordinate_eq_pairing (G.colDec (2 * ρ + 1) h1' h2') (F.dJ ρ h) (by omega) (hF.hJ ρ h) i hq
      (fun k => (M ⬝ (F.dB ρ h).jX) k j)
    rw [← e1] at e2
    simp only [hcol] at e2
    have e3 : incA D ((-D.host.xi0) ^ (i.1 + 1)) * (incA D (-D.host.xi0) * g) =
        ∑ k, ∑ l, cA D (incA D (aJ k q)) * incA D ((G.V (.grid (2 * ρ + 1) 0)).gram k l) *
          (incA D ((-D.host.xi0) ^ (j.1 + 1)) * (M *ᵥ colB) l) := by
      rw [hg, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      have hp1 : (-D.host.xi0) ^ (j.1 + 1) = (-D.host.xi0) ^ (i.1 + 1) * (-D.host.xi0) := by rw [hij, pow_succ]
      rw [hp1, map_mul]
      ring
    have hunit : incA D (((-D.host.xi0) ^ (i.1 + 1))⁻¹) * incA D ((-D.host.xi0) ^ (i.1 + 1)) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ (pow_ne_zero _ (neg_ne_zero.2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero)), map_one]
    calc ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j
        = (incA D (((-D.host.xi0) ^ (i.1 + 1))⁻¹) * incA D ((-D.host.xi0) ^ (i.1 + 1))) *
          ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j := by rw [hunit, one_mul]
      _ = incA D (((-D.host.xi0) ^ (i.1 + 1))⁻¹) * (incA D ((-D.host.xi0) ^ (i.1 + 1)) *
          (incA D (-D.host.xi0) * g)) := by rw [mul_assoc, e2, ← e3]
      _ = incA D (-D.host.xi0) * g := by rw [← mul_assoc, hunit, one_mul]

  set Φ : D.host.E → AE D := fun t => ((α⁻¹ : (AE D)ˣ) : AE D) * cA D ((α⁻¹ : (AE D)ˣ) : AE D) *
    (idem D (· = v) * incA D t * g) with hΦ
  have hgen : ∀ t ∈ {t : D.host.E | ∃ a ∈ D.host.AA, ∃ c' ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q, ∃ c ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) p, t = D.host.conj (a * c') * c}, Φ t ∈ intAt D (· = v) := by
    rintro t ⟨a, ha, c', hc', c, hc, rfl⟩
    have hxB : (fun m => c * aB m p) ∈ G.Λ (.grid (2 * ρ + 2) 0) := by
      have e := G.sp.colLat (2 * ρ + 2) h1 h
      show _ ∈ (vtxOf L G.sp.Vs (2 * ρ + 2) 0).lat
      rw [e]
      exact col_mem (G.colDec (2 * ρ + 2) h1 h) _ _ p hc
    have hxJ : (fun m => c' * aJ m q) ∈ G.Λ (.grid (2 * ρ + 1) 0) := by
      have e := G.sp.colLat (2 * ρ + 1) h1' h2'
      show _ ∈ (vtxOf L G.sp.Vs (2 * ρ + 1) 0).lat
      rw [e]
      exact col_mem (G.colDec (2 * ρ + 1) h1' h2') _ _ q hc'
    set y : Fin (G.V (.grid (2 * ρ + 2) 0)).rank → AE D := fun m => idem D (· = v) * incA D (1 * (c * aB m p)) with hy
    have hyT : y ∈ latV (G.V (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 2) 0)) (fun _ => True) :=
      gen_mem _ {1} _ v _ (fun w hw => absurd trivial hw) rfl hxB
    set w : Fin (G.V (.grid (2 * ρ + 1) 0)).rank → AE D := fun m => idem D (· = v) * incA D (a * (c' * aJ m q)) with hw
    have hwv : w ∈ latA (G.V (.grid (2 * ρ + 1) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) :=
      gen_mem _ {a | a ∈ D.host.AA} _ v _ (fun w hw => hw) ha hxJ
    have hMy : M *ᵥ y ∈ latA (G.V (.grid (2 * ρ + 1) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) (fun _ => True) := hMlat.2 y hyT
    have hMy' := GlobalTheory.T.adeleIdempotent_smul_mem_latticeCompletionAtPlace D _ _ _ v _ hMy
    have hyy : idem D (· = v) • (M *ᵥ y) = M *ᵥ y := by
      rw [← Matrix.mulVec_smul]
      congr 1
      funext k
      simp [hy, smul_eq_mul, ← mul_assoc, idem_mul_self]
    rw [hyy] at hMy'
    have z1 := (hA _ _ _).1 hMy'
    have z2 := (hA _ _ _).1 hwv
    have hP := GlobalTheory.T.hermitianPairing_selfDual_completion_integral_at_place D _ _ sdW v _ _ z1 z2
    have hw' : ∀ k, cA D ((((α⁻¹ : (AE D)ˣ) : AE D) • w) k) = cA D ((α⁻¹ : (AE D)ˣ) : AE D) * idem D (· = v) *
        incA D (D.host.conj (a * c')) * cA D (incA D (aJ k q)) := by
      intro k
      simp only [hw, Pi.smul_apply, smul_eq_mul, map_mul, cA_idem, GlobalTheory.IdeleAA.cA_incA]
      ring
    have hz' : ∀ l, (((α⁻¹ : (AE D)ˣ) : AE D) • (M *ᵥ y)) l = ((α⁻¹ : (AE D)ˣ) : AE D) * (idem D (· = v) * incA D c) *
        (M *ᵥ colB) l := by
      intro l
      rw [Pi.smul_apply, smul_eq_mul]
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, hy, hcolB]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [one_mul, map_mul]
      ring
    have hI := idem_mul_self (D := D) (· = v)
    convert hP using 1
    simp only [hw', hz', hΦ, hg, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    linear_combination (-(((α⁻¹ : (AE D)ˣ) : AE D) * cA D ((α⁻¹ : (AE D)ˣ) : AE D) * incA D (D.host.conj a) * incA D (D.host.conj c') *
      incA D c * (cA D (incA D (aJ k q)) * incA D ((G.V (.grid (2 * ρ + 1) 0)).gram k l) * (M *ᵥ colB) l))) * hI
  have hspan : ∀ t ∈ Submodule.span (𝓞 D.host.E) {t : D.host.E | ∃ a ∈ D.host.AA, ∃ c' ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q, ∃ c ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) p, t = D.host.conj (a * c') * c}, Φ t ∈ intAt D (· = v) := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem t ht => exact hgen t ht
    | zero =>
      have : Φ 0 = 0 := by simp only [hΦ, map_zero, mul_zero, zero_mul]
      rw [this]; exact ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩
    | add x y _ _ hx hy =>
      have : Φ (x + y) = Φ x + Φ y := by simp only [hΦ, map_add (f := _)]; ring
      rw [this]; exact intAt_add hx hy
    | smul o x _ hx =>
      have hI := idem_mul_self (D := D) (· = v)
      have : Φ (o • x) = (idem D (· = v) * incA D (o : D.host.E)) * Φ x := by
        rw [Algebra.smul_def]
        simp only [hΦ, map_mul]
        linear_combination (-(((α⁻¹ : (AE D)ˣ) : AE D) * cA D ((α⁻¹ : (AE D)ˣ) : AE D) *
          incA D (algebraMap (𝓞 D.host.E) D.host.E o) * incA D x * g)) * hI
      rw [this]; exact GlobalTheory.IdeleAA.intAt_mul (idem_incA_mem v o) hx
  obtain ⟨u, hu, hus⟩ := GlobalTheory.T.exists_unit_mem_span_staircaseIdeal_products G ρ p q (by simp [hp, hqdef]; omega) v hv
  have hz : idem D (· = v) * (((α⁻¹ : (AE D)ˣ) : AE D) * cA D ((α⁻¹ : (AE D)ˣ) : AE D) * g) ∈ intAt D (· = v) := by
    refine GlobalTheory.T.adeleIdempotent_mul_integral_of_unit_factor D v u hu _ ?_
    have := hspan _ hus
    simp only [hΦ] at this
    convert this using 1; ring

  have hs : idem D (· = v) * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j ∈ idAt D (· = v) :=
    Ideal.mul_mem_right _ _ (idem_mem_idAt _)
  have key : incA D D.host.xi0⁻¹ * ((α⁻¹ : (AE D)ˣ) : AE D) * cA D ((α⁻¹ : (AE D)ˣ) : AE D) *
      (idem D (· = v) * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j) ∈ intAt D (· = v) := by
    have hx0 : incA D D.host.xi0⁻¹ * incA D (-D.host.xi0) = -1 := by
      rw [← map_mul, mul_neg, inv_mul_cancel₀ GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero, map_neg, map_one]
    rw [hN]
    convert intAt_neg hz using 1
    linear_combination (((α⁻¹ : (AE D)ˣ) : AE D) * cA D ((α⁻¹ : (AE D)ˣ) : AE D) * idem D (· = v) * g) * hx0
  have hoid : idem D (· = v) * o = o := (mem_idAt_iff _ o).1 ho.1
  have := (hψ _ hs).2 key o ho
  rw [← hoid]
  convert this using 2
  ring

end GlobalTheory.UniOff
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericCharacterTrivialSuperdiagonalOffExceptionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericCharacter_trivial_superdiagonal_off_exceptional : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (M : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))), M ∈ latRow G (2 * ρ + 1) → ∀ i j : Fin ρ, j.1 = i.1 + 1 → ∀ v : GlobalTheory.FinPl.Pl D, v ∉ G.pl.S0 → ∀ o ∈ intAt D (· = v), psiE W.ψ (o * ((F.dJ ρ h).pX ⬝ (M ⬝ (F.dB ρ h).jX)) i j) = 1 := by
  first | exact @GlobalTheory.UniOff.uni_off | exact GlobalTheory.UniOff.uni_off | (intros; apply GlobalTheory.UniOff.uni_off <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericCharacterTrivialBesselStepUnitriangular
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.UniBF

private theorem psiE_add_mul {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (a b : AE D) :
    psiE ψ (a + b) = psiE ψ a * psiE ψ b := by
  simp only [psiE, map_add (f := _), AddChar.map_add_eq_mul]

private theorem psiE_zero_one {D : D7} (ψ : AddChar (AF D.host.F) ℂ) : psiE ψ (0 : AE D) = 1 := by
  simp only [psiE, map_zero, AddChar.map_zero_eq_one]

theorem psiUni_pcBF : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u : UX D ρ,
    MxAt (fun _ => True) (u.1.1 - 1) → xZero (F.dJ ρ h) ⬝ u.1.1 - xZero (F.dJ ρ h) ∈ (pcBF W F ρ h).A₁ →
    psiUni W.ψ u.1 = 1 := by
  intro D hq T L μ0 hL sc G W Mv hM F hF ρ h u hu hx
  have hA := GlobalTheory.T.genericCharacter_trivial_superdiagonal_off_exceptional D hq T L μ0 hL sc G W Mv hM F hF ρ h
  have hB := GlobalTheory.T.additive_character_superdiag_trivial D hq T L μ0 hL sc G W Mv hM F hF ρ h
  set N : Mx D ρ ρ := u.1.1 - 1 with hNdef
  have hx' : (F.dB ρ h).extX _ ((F.dJ ρ h).jX ⬝ N) ∈ latRow G (2 * ρ + 1) := by
    have e : xZero (F.dJ ρ h) ⬝ u.1.1 - xZero (F.dJ ρ h) = (F.dJ ρ h).jX ⬝ N := by
      rw [hNdef, Matrix.mul_sub, Matrix.mul_one]; rfl
    rw [← e]; exact hx
  have hN : (F.dJ ρ h).pX ⬝ ((F.dB ρ h).extX _ ((F.dJ ρ h).jX ⬝ N) ⬝ (F.dB ρ h).jX) = N := by
    rw [HypDec.extX_apply, Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one, ← Matrix.mul_assoc, HypDec.pX_jX,
      Matrix.one_mul]
  have key : ∀ i j : Fin ρ, j.1 = i.1 + 1 → psiE W.ψ (u.1.1 i j) = 1 := fun i j hij => by
    have hne : i ≠ j := fun e => by rw [e] at hij; omega
    have e1 : u.1.1 i j = N i j := by rw [hNdef, Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero]
    rw [e1]
    refine GlobalTheory.FinPl.PsiUnit.psiE_eq_one_of_local W.ψ W.ψ_std.1.1 (hu i j) fun v _ => ?_
    have ho := GlobalTheory.FinPlLoc.idem_mem_intAt (D := D) (· = v)
    by_cases hv : v ∈ G.pl.S0
    · have := hB _ hx' i j hij v hv _ ho
      rwa [hN] at this
    · have := hA _ hx' i j hij v hv _ ho
      rwa [hN] at this
  unfold psiUni upSum
  refine Finset.sum_induction _ (fun x => psiE W.ψ x = 1) (fun a b ha hb => by rw [psiE_add_mul, ha, hb, one_mul])
    (psiE_zero_one W.ψ) fun i _ => ?_
  refine Finset.sum_induction _ (fun x => psiE W.ψ x = 1) (fun a b ha hb => by rw [psiE_add_mul, ha, hb, one_mul])
    (psiE_zero_one W.ψ) fun j _ => ?_
  split_ifs with hij
  · exact key i j hij
  · exact psiE_zero_one W.ψ

end GlobalTheory.AscFin.UniBF

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericCharacterTrivialBesselStepUnitriangularStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericCharacter_trivial_besselStep_unitriangular : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u : UX D ρ, MxAt (fun _ => True) (u.1.1 - 1) → xZero (F.dJ ρ h) ⬝ u.1.1 - xZero (F.dJ ρ h) ∈ (pcBF W F ρ h).A₁ → psiUni W.ψ u.1 = 1 := by
  first | exact @GlobalTheory.AscFin.UniBF.psiUni_pcBF | exact GlobalTheory.AscFin.UniBF.psiUni_pcBF | (intros; apply GlobalTheory.AscFin.UniBF.psiUni_pcBF <;> assumption)
end
