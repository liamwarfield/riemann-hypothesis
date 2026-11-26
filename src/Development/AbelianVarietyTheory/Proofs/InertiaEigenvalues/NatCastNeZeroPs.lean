module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
public import Formalism.LocalToGlobal.UnitaryNorms.CharShare
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraInductionCharacterRestrictionDecomp

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastNeZeroPs
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

section Defs

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]


variable (l) in
def LTo0 {ι : Type} (w : ι → Wq l a) : Prop := ∀ r : ℕ, ∀ᶠ n in cofinite, (l : Wq l a) ^ r ∣ w n

variable (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  (e : ℕ)

def SdSet : Set (ZMod a → K⟦X⟧) :=
  {F | ∃ w : ℕ → Wq l a, LTo0 l w ∧
    ∀ τ n, ((n / e).factorial : K) * coeff n (F τ) = algebraMap O K (emb t τ (w n))}

def Sd : Subring (ZMod a → K⟦X⟧) := Subring.closure (SdSet t K e)

def PPSet : Set (ZMod a → K⟦X⟧⟦X⟧) :=
  {F | ∃ w : ℕ × ℕ → Wq l a, LTo0 l w ∧
    ∀ τ i n, ((i.factorial * (n / e).factorial : ℕ) : K) * coeff n (coeff i (F τ)) =
      algebraMap O K (emb t τ (w (i, n)))}

def PPd : Subring (ZMod a → K⟦X⟧⟦X⟧) := Subring.closure (PPSet t K e)

def inclS : (Wq l a)⟦X⟧ →+* (ZMod a → K⟦X⟧) :=
  Pi.ringHom fun τ => (A O K).val.toRingHom.comp ((Pi.evalRingHom (fun _ : ZMod a => A O K) τ).comp (toAc t K))

theorem inclS_apply (x : (Wq l a)⟦X⟧) (τ : ZMod a) : inclS t K x τ = (toAc t K x τ : K⟦X⟧) := rfl

variable {K}

def frob2 (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧) : (ZMod a → K⟦X⟧⟦X⟧) →+* (ZMod a → K⟦X⟧⟦X⟧) :=
  Pi.ringHom fun τ => φ₂.comp (Pi.evalRingHom (fun _ : ZMod a => K⟦X⟧⟦X⟧) (τ - 1))


variable (a K) in
def constP : (ZMod a → K⟦X⟧) →+* (ZMod a → K⟦X⟧⟦X⟧) :=
  Pi.ringHom fun τ => (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).comp (Pi.evalRingHom (fun _ : ZMod a => K⟦X⟧) τ)


variable (a) in
def shP (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) : (ZMod a → K⟦X⟧) →+* (ZMod a → K⟦X⟧⟦X⟧) :=
  Pi.ringHom fun τ => sh.comp (Pi.evalRingHom (fun _ : ZMod a => K⟦X⟧) τ)


variable (a K) in
def diag : (ZMod a → K⟦X⟧⟦X⟧) →+* (ZMod a → K⟦X⟧) :=
  Pi.ringHom fun τ => (constantCoeff : K⟦X⟧⟦X⟧ →+* K⟦X⟧).comp (Pi.evalRingHom (fun _ : ZMod a => K⟦X⟧⟦X⟧) τ)

end Defs

theorem tf_pi {R : Type} [CommRing R] [IsDomain R] {n a : ℕ} (hn : (n : R) ≠ 0) (x : ZMod a → R)
    (h : (n : ZMod a → R) * x = 0) : x = 0 := funext fun τ => by
  have h1 := congrFun h τ
  simp only [Pi.mul_apply, Pi.natCast_apply, Pi.zero_apply] at h1
  exact (mul_eq_zero.1 h1).resolve_left hn

theorem natCast_ne_zero_ps {R : Type} [CommRing R] {n : ℕ} (h : (n : R) ≠ 0) : (n : R⟦X⟧) ≠ 0 := fun h' =>
  h (by simpa using congrArg (constantCoeff : R⟦X⟧ →+* R) h')

theorem tf_sub {R : Type} [CommRing R] {n : ℕ} (s : Subring R) (htf : ∀ x : R, (n : R) * x = 0 → x = 0)
    (x : ↥s) (h : (n : ↥s) * x = 0) : x = 0 := Subtype.ext (htf _ (by simpa using congrArg Subtype.val h))

theorem nzd_of_tf {R : Type} [CommRing R] {n : ℕ} (htf : ∀ x : R, (n : R) * x = 0 → x = 0) :
    (n : R) ∈ nonZeroDivisors R :=
  mem_nonZeroDivisors_iff.2 ⟨htf, fun x hx => htf x (by rw [mul_comm]; exact hx)⟩

theorem bdd_self {R : Type} [CommRing R] (n : ℕ) : ∃ m : ℕ, ∀ x : R ⧸ Ideal.span {(n : R)},
    (∃ k : ℕ, (n : R ⧸ Ideal.span {(n : R)}) ^ k * x = 0) → (n : R ⧸ Ideal.span {(n : R)}) ^ m * x = 0 := by
  refine ⟨1, fun x _ => ?_⟩
  have h : (n : R ⧸ Ideal.span {(n : R)}) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(n : R)})), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  rw [h, pow_one, zero_mul]

variable {l : ℕ} [hl : Fact l.Prime]

theorem isUnit_delta_l {A : Type} [CommRing A] (D : Delta l A) (htf : ∀ x : A, (l : A) * x = 0 → x = 0)
    [IsAdicComplete (Ideal.span {(l : A)}) A] : IsUnit (D.δ l) := by
  have h1 : D.δ l = 1 - (l : A) ^ (l - 1) := by
    rw [← sub_eq_zero]
    apply htf
    have h := D.φ_eq (l : A)
    rw [map_natCast] at h
    have h2 : (l : A) ^ l = (l : A) * (l : A) ^ (l - 1) := by
      rw [← pow_succ']; congr 1; have := hl.out.one_lt; omega
    linear_combination -h - h2
  rw [h1]
  have hm : -(l : A) ^ (l - 1) ∈ Ideal.span {(l : A)} := (Ideal.neg_mem_iff _).2
    (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ (by have := hl.out.one_lt; omega))
  have := Ideal.mem_jacobson_bot.1 (IsAdicComplete.le_jacobson_bot _ hm) 1
  rwa [mul_one, neg_add_eq_sub] at this

section Sh

variable {K : Type} [NormedField K] [CharZero K] (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧)
  (hsh : ∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f)
include hsh

theorem constantCoeff_sh (f : K⟦X⟧) : constantCoeff (sh f) = f := by
  simpa using hsh f 0

theorem sh_X : sh X = C X + X := by
  ext i : 1
  have h := hsh X i
  rcases i with _ | _ | i
  · simpa using h
  · simp [coeff_C, coeff_X]
    simpa [derivative_X] using h
  · have h3 : ((i + 2).factorial : K⟦X⟧) ≠ 0 := natCast_ne_zero_ps (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
    have h4 : (PowerSeries.derivative (R := K))^[i + 2] X = 0 := by
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, derivative_X]
      rw [derivative_one]
      exact iterate_derivative_zero
    rw [h4] at h
    rw [(mul_eq_zero.1 h).resolve_left h3]
    simp [coeff_C, coeff_X]

theorem constantCoeff_φ₂ (l : ℕ) [Fact l.Prime] (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hφC : ∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f))
    (hφsh : ∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) (G : K⟦X⟧⟦X⟧) :
    constantCoeff (φ₂ G) = frob K l (constantCoeff G) := by
  have hX : φ₂ X = sh (X ^ l) - C (X ^ l) := by
    have h : (X : K⟦X⟧⟦X⟧) = sh X - C X := by rw [sh_X sh hsh]; ring
    rw [h, map_sub, hφsh, hφC, frob_X]
  conv_lhs => rw [eq_shift_mul_X_add_const G]
  rw [map_add (f := _), map_mul, hX, hφC, map_add (f := _), map_mul, map_sub, constantCoeff_sh sh hsh, constantCoeff_C,
    constantCoeff_C, sub_self, mul_zero, zero_add]

end Sh

section Maps

variable {a : ℕ} [NeZero a] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (t : Wq l a →ₐ[ℤ_[l]] O) (e : ℕ)

theorem frob_toAc (x : (Wq l a)⟦X⟧) (τ : ZMod a) :
    frob K l (toAc t K x (τ - 1) : K⟦X⟧) = (toAc t K (frobS l a x) τ : K⟦X⟧) := by
  ext n
  have : coeff n (frobS l a x) = if l ∣ n then sigma l a (coeff (n / l) x) else 0 := by
    simp only [frobS, RingHom.comp_apply, coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coeff_expand]
    split_ifs <;> simp
  rw [coeff_frob, coeff_toAc, coeff_toAc, this]
  split_ifs
  · rw [emb_sigma]
  · simp

theorem constP_mem {F : ZMod a → K⟦X⟧} (hF : F ∈ SdSet t K e) : constP a K F ∈ PPSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  refine ⟨fun p => if p.1 = 0 then w p.2 else 0, fun r => ?_, fun τ i n => ?_⟩
  · have h := hw r
    rw [Filter.eventually_cofinite] at h ⊢
    refine (h.image fun n => ((0 : ℕ), n)).subset ?_
    rintro ⟨i, n⟩ hin
    by_cases hi : i = 0
    · subst hi; exact ⟨n, by simpa using hin, rfl⟩
    · simp [hi] at hin
  · change ((i.factorial * (n / e).factorial : ℕ) : K) * coeff n (coeff i (C (F τ))) = _
    rw [coeff_C]
    by_cases hi : i = 0
    · subst hi; simpa using hF τ n
    · simp [hi]

theorem diag_mem {F : ZMod a → K⟦X⟧⟦X⟧} (hF : F ∈ PPSet t K e) : diag a K F ∈ SdSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  refine ⟨fun n => w (0, n), fun r => ?_, fun τ n => ?_⟩
  · have h := hw r
    rw [Filter.eventually_cofinite] at h ⊢
    exact h.preimage (fun _ _ _ _ h => by simpa using h)
  · have h := hF τ 0 n
    simp only [Nat.factorial_zero, one_mul, coeff_zero_eq_constantCoeff] at h
    exact h

end Maps

end GlobalTheory.CrysPrism
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPreframeBoundedPoles
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobRowIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.HeightInt

theorem frob_row_integral : ∀ (l : ℕ) [Fact l.Prime] (κ : Type) [Fintype κ] (x : κ → WCb l)
    (c : κ → κ → Ainf l), (∀ j, frobW l (x j) = ∑ i, x i * inclW l (c i j)) →
    ∀ j, ∃ a : Ainf l, x j = inclW l a := by
  intro l _ κ _ x c h j
  let Z : Matrix Unit κ (WCb l) := Matrix.of fun _ i => x i
  have hZ : Z.map (frobW l) = (1 : Matrix Unit Unit (Ainf l)).map (inclW l) * Z *
      (Matrix.of c).map (inclW l) + (0 : Matrix Unit κ (Ainf l)).map (inclW l) := by
    ext1 u k
    simp only [Matrix.map_apply, Matrix.map_one (inclW l) (map_zero _) (map_one _), Matrix.one_mul,
      Matrix.map_zero (inclW l) (map_zero _), add_zero, Matrix.mul_apply, Matrix.of_apply, Z]
    exact h k
  obtain ⟨a, ha⟩ := GlobalTheory.FrobInt.frobenius_integrality l Unit κ Z 1 (Matrix.of c) 0 hZ () j
  exact ⟨a, ha.symm⟩

end GlobalTheory.HeightInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPreframeBoundedPoles
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

theorem pre_bounded_poles : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Pre bk N d ρ), ∃ Y Y' : Matrix (Fin d) (Fin d) (Ainf l), Y.map (inclW l) = inclW l τ ^ N • F.T ∧ Y * Y' = τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) := by
  intro l _ K bk τ hτ N d ρ F
  classical
  obtain ⟨hU, -⟩ := GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ
  have hφt : frobW l (inclW l τ) = bk.evW bk.E * inclW l τ := by
    rw [frobW_inclW, hτ.1, map_mul]; rfl
  have he : IsUnit (bk.evW bk.E) := by
    have h := hU.map (frobW l)
    rw [hφt] at h
    exact isUnit_of_mul_isUnit_left h
  have hdet : IsUnit F.T.det := (Matrix.isUnit_iff_isUnit_det _).1 F.unit
  have hTTi : F.T * F.T⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hTiT : F.T⁻¹ * F.T = 1 := Matrix.nonsing_inv_mul _ hdet
  have hmapmul : ∀ M M' : Matrix (Fin d) (Fin d) (WCb l), (M * M').map (frobW l) = M.map (frobW l) * M'.map (frobW l) :=
    fun M M' => Matrix.map_mul (f := (frobW l).toRingHom)
  have h1 : F.T⁻¹.map (frobW l) * F.T.map (frobW l) = 1 := by
    rw [← hmapmul, hTiT]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have hAA : F.A.map bk.evW * F.A'.map bk.evW = bk.evW bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (WCb l)) := by
    rw [← Matrix.map_mul, F.A_mul]
    ext i j
    simp [Matrix.one_apply]
    split_ifs <;> simp

  have hφTi : bk.evW bk.E ^ N • F.T⁻¹.map (frobW l) = F.A'.map bk.evW * F.T⁻¹ := by
    have k1 : (bk.evW bk.E ^ N • F.T.map (frobW l)) * F.A'.map bk.evW * F.T⁻¹ =
        bk.evW bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (WCb l)) := by
      rw [F.φ, Matrix.mul_assoc F.T, hAA, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hTTi]
    have k2 := congrArg (fun M => F.T⁻¹.map (frobW l) * M) k1
    simp only [Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_one] at k2
    have k3 : bk.evW bk.E ^ N • (bk.evW bk.E ^ N • F.T⁻¹.map (frobW l)) =
        bk.evW bk.E ^ N • (F.A'.map bk.evW * F.T⁻¹) := by
      rw [smul_smul, ← pow_add, show N + N = 2 * N by ring, ← k2]
    exact (he.pow N).smul_left_cancel.1 k3
  have hY : ∀ i j, ∃ a : Ainf l, inclW l τ ^ N * F.T i j = inclW l a := by
    intro i
    refine GlobalTheory.HeightInt.frob_row_integral l (Fin d) (fun j => inclW l τ ^ N * F.T i j)
      (fun k j => bk.ev (F.A k j)) ?_
    intro j
    have e1 := congrFun (congrFun F.φ i) j
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.mul_apply, smul_eq_mul] at e1
    rw [map_mul, map_pow, hφt, mul_pow, mul_comm (bk.evW bk.E ^ N), mul_assoc, e1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc]; rfl
  have hY' : ∀ i j, ∃ a : Ainf l, inclW l τ ^ N * F.T⁻¹ i j = inclW l a := by
    intro i j
    refine GlobalTheory.HeightInt.frob_row_integral l (Fin d) (fun k => inclW l τ ^ N * F.T⁻¹ k j)
      (fun k i => bk.ev (F.A' i k)) ?_ i
    intro i
    have e1 := congrFun (congrFun hφTi i) j
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.mul_apply, smul_eq_mul] at e1
    rw [map_mul, map_pow, hφt, mul_pow, mul_comm (bk.evW bk.E ^ N), mul_assoc, e1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm (bk.evW (F.A' i k)), mul_assoc]; rfl
  choose Y hYe using hY
  choose Y' hY'e using hY'
  refine ⟨Matrix.of Y, Matrix.of Y', ?_, ?_⟩
  · ext i j
    simp [Matrix.smul_apply, hYe]
  · refine Matrix.ext fun i j => ?_
    apply inclW_injective
    have e2 := congrFun (congrFun hTTi i) j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.of_apply, map_sum, map_mul, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] at e2 ⊢
    simp only [← hYe, ← hY'e]
    calc ∑ k, inclW l τ ^ N * F.T i k * (inclW l τ ^ N * F.T⁻¹ k j)
        = inclW l τ ^ (2 * N) * ∑ k, F.T i k * F.T⁻¹ k j := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; ring
      _ = _ := by rw [e2]; split_ifs <;> simp [map_pow]

end GlobalTheory.BKLim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPreframeBoundedPolesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinPreframe_bounded_poles : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Pre bk N d ρ), ∃ Y Y' : Matrix (Fin d) (Fin d) (Ainf l), Y.map (inclW l) = inclW l τ ^ N • F.T ∧ Y * Y' = τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) := by
  first | exact @GlobalTheory.BKLim.pre_bounded_poles | exact GlobalTheory.BKLim.pre_bounded_poles | (intros; apply GlobalTheory.BKLim.pre_bounded_poles <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanOfPowMul
set_option synthInstance.maxHeartbeats 400000
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GalStep

variable {l : ℕ} [Fact l.Prime]

def galD (g : GQ l) : Per.BdRp l →ₐ[ℤ_[l]] Per.BdRp l where
  toRingHom := Per.σDp g
  commutes' z := (GlobalTheory.MemLoc.ActLaws.σDp_aDp g _).trans (congrArg (GlobalTheory.MemLoc.aDp l) ((galA g).commutes z))

variable (O : Type) [CommRing O] [Algebra ℤ_[l] O]

def galOD (g : GQ l) : OD l O →ₐ[O] OD l O := Algebra.TensorProduct.map (AlgHom.id _ _) (galD g)

variable {O}

theorem TWact_smul_of {G Qp LL R : Type} [Group G] [TopologicalSpace G] [Field Qp] [Field LL] [Algebra Qp LL] [Algebra O LL]
    [TopologicalSpace LL] [CommRing R] [Algebra O R] (f : R →ₐ[O] R) (T : LocLat G Qp LL O) (g : G) (r : R)
    (z : TW R T) : TWact f T g (r • z) = f r • TWact f T g z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul x y =>
    simp only [TWact, TensorProduct.smul_tmul', TensorProduct.map_tmul, AlgHom.toLinearMap_apply, smul_eq_mul,
      map_mul]
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

def rhoD {LL : FinExt l} {ι : Type} (T : QLat LL)
    (jD : (ι → OD l ↥(OL LL)) ≃ₗ[OD l ↥(OL LL)] TW (OD l ↥(OL LL)) T) (g : Gl l)
    (y : ι → OD l ↥(OL LL)) : ι → OD l ↥(OL LL) :=
  jD.symm (TWact (galOD ↥(OL LL) (sQ l g)) T g (jD y))


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem TWact_galOD_smul {LL : FinExt l} (T : QLat LL) (h : GQ l) (g : Gl l) (c : OD l ↥(OL LL))
    (z : TW (OD l ↥(OL LL)) T) :
    TWact (galOD ↥(OL LL) h) T g (c • z) = galOD ↥(OL LL) h c • TWact (galOD ↥(OL LL) h) T g z :=
  TWact_smul_of (galOD ↥(OL LL) h) T g c z


set_option synthInstance.maxHeartbeats 400000 in
theorem rhoD_smul {LL : FinExt l} {ι : Type} (T : QLat LL)
    (jD : (ι → OD l ↥(OL LL)) ≃ₗ[OD l ↥(OL LL)] TW (OD l ↥(OL LL)) T) (g : Gl l) (c : OD l ↥(OL LL))
    (y : ι → OD l ↥(OL LL)) : rhoD T jD g (c • y) = galOD ↥(OL LL) (sQ l g) c • rhoD T jD g y := by
  have h1 : jD (c • y) = c • jD y := jD.map_smul c y
  have h2 := TWact_galOD_smul T (sQ l g) g c (jD y)
  have h3 := jD.symm.map_smul (galOD ↥(OL LL) (sQ l g) c) (TWact (galOD ↥(OL LL) (sQ l g)) T g (jD y))
  exact (congrArg (fun z => jD.symm (TWact (galOD ↥(OL LL) (sQ l g)) T g z)) h1).trans
    ((congrArg jD.symm h2).trans h3)

variable {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type}


open Classical in
open Classical in
variable (O) in
def hatR (f : K⟦X⟧) : Ahat O K l e := if h : f ∈ Rpi O K l e then toHat O K l e ⟨f, h⟩ else 0

theorem hatR_of_mem {f : K⟦X⟧} (h : f ∈ Rpi O K l e) : hatR O f = toHat O K l e ⟨f, h⟩ := by
  rw [hatR, dite_eq_left h]

def YD (v : Vec K a ι) : ι → OD l O := fun i => ϖ.iD t K (fun τ => hatR O (v τ i))


variable (K) in
def ED : OD l O := ϖ.iD t K (fun _ => Ehat O K l e)

end GlobalTheory.GalStep

namespace GlobalTheory.GalStep
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
variable {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mem_Rpi_of_mem_Man {P : PhiMod O K l e a ι} {v : Vec K a ι} (hv : v ∈ P.Man) (τ : ZMod a) (i : ι) :
    v τ i ∈ Rpi O K l e :=
  mem_tot.1 (P.mem_Man.1 hv) τ i

theorem YD_add {P : PhiMod O K l e a ι} {v v' : Vec K a ι} (hv : v ∈ P.Man) (hv' : v' ∈ P.Man) :
    YD t ϖ (v + v') = YD t ϖ v + YD t ϖ v' := by
  funext i
  simp only [YD, Pi.add_apply]
  rw [← map_add (f := _)]
  congr 1
  funext τ
  rw [Pi.add_apply, hatR_of_mem (O := O) (add_mem (mem_Rpi_of_mem_Man hv τ i) (mem_Rpi_of_mem_Man hv' τ i)),
    hatR_of_mem (O := O) (mem_Rpi_of_mem_Man hv τ i), hatR_of_mem (O := O) (mem_Rpi_of_mem_Man hv' τ i), ← map_add]
  rfl

theorem YD_E_pow_smul {P : PhiMod O K l e a ι} {v : Vec K a ι} (hv : v ∈ P.Man) (k : ℕ) :
    YD t ϖ (E K l e ^ k • v) = ED K t ϖ ^ k • YD t ϖ v := by
  funext i
  simp only [YD, ED, Pi.smul_apply, smul_eq_mul]
  rw [← map_pow, ← map_mul]
  congr 1
  funext τ
  have hE : E K l e ∈ Rpi O K l e := E_mem (K := K) l e _
  rw [Pi.mul_apply, Pi.pow_apply, hatR_of_mem (O := O) (mul_mem (pow_mem hE k) (mem_Rpi_of_mem_Man hv τ i)),
    hatR_of_mem (O := O) (mem_Rpi_of_mem_Man hv τ i), ← toHat_E, ← map_pow, ← map_mul]
  rfl

theorem iD_eq_YD {P : PhiMod O K l e a ι} {v : Vec K a ι} (hv : v ∈ P.Man) (i : ι) (w : ZMod a → Ahat O K l e)
    (hw : ∀ τ, algebraMap _ (AhatE O K l e) (w τ) = hat O l e (v τ i)) : ϖ.iD t K w = YD t ϖ v i := by
  simp only [YD]
  congr 1
  funext τ
  rw [hatR_of_mem (O := O) (mem_Rpi_of_mem_Man hv τ i)]
  apply algebraMap_AhatE_injective l e
  rw [hw τ]
  exact hat_coe_Rpi l e ⟨v τ i, mem_Rpi_of_mem_Man hv τ i⟩

end GlobalTheory.GalStep

namespace GlobalTheory.GalStep

theorem mem_span_of_pow_mul {R : Type} [CommRing R] {d : R} (hd : ∀ y : R, d * y = 0 → y = 0) (p n : ℕ) {y : R}
    (h : d ^ p * y ∈ Ideal.span {d ^ (p + n)}) : y ∈ Ideal.span {d ^ n} := by
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 h
  have h0 : d ^ p * (y - z * d ^ n) = 0 := by rw [mul_sub, ← hz, pow_add]; ring
  have h1 : ∀ p : ℕ, ∀ y : R, d ^ p * y = 0 → y = 0 := by
    intro p
    induction p with
    | zero => intro y h; simpa using h
    | succ p ih => intro y h; exact ih y (hd _ (by rw [← h, pow_succ]; ring))
  have := h1 p _ h0
  rw [sub_eq_zero] at this
  exact Ideal.mem_span_singleton'.2 ⟨z, this.symm⟩
end GlobalTheory.GalStep

namespace GlobalTheory.GalStep
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
variable {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι]

theorem tail_step (P : PhiMod O K l e a ι) (hnz : ∀ y : OD l O, ED K t ϖ * y = 0 → y = 0)
    (hman : ∀ α : ℕ, (∀ v ∈ P.L, E K l e ^ α • v ∈ P.M) →
      ∀ w ∈ P.Mext (invL l (S O K e)), E K l e ^ α • P.xiExt w ∈ P.Man)
    (hdesc : ∀ (i : ℕ) (w : Vec K a ι), w ∈ P.Mext (invL l (S O K e)) →
      (fun τ j => descN K i (w τ j)) ∈ P.Mext (invL l (S O K e)))
    (α β₀ n : ℕ) (hα : ∀ v ∈ P.L, E K l e ^ α • v ∈ P.M) {m : Vec K a ι} (hm : m ∈ P.M)
    (hn : E K l e ^ n • P.EN m ∈ P.Man) {wx : Vec K a ι} (hwx : wx ∈ P.Mext (invL l (S O K e)))
    (hwxdef : P.xiExt wx = E K l e ^ (β₀ + n) • m) (j : ι)
    (hD1 : ED K t ϖ * YD t ϖ (E K l e ^ α • P.xiExt (fun τ k => descN K 1 (wx τ k))) j ∈
      Ideal.span {ED K t ϖ ^ (α + (β₀ + n))}) :
    YD t ϖ (E K l e ^ n • P.EN m) j ∈ Ideal.span {ED K t ϖ ^ n} := by
  obtain ⟨x, hxdef⟩ : ∃ x, x = E K l e ^ (β₀ + n) • m := ⟨_, rfl⟩
  rw [← hxdef] at hwxdef
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = α + (β₀ + n) := ⟨_, rfl⟩
  rw [← hγ] at hD1
  have hwx1 : (fun τ k => descN K 1 (wx τ k)) = fun τ k => N K (wx τ k) := by
    funext τ k
    simp [descN, descPochhammer_one]
  have hconn : P.xiExt (fun τ k => descN K 1 (wx τ k)) = P.conn x := by
    rw [hwx1, ← P.conn_xiExt, hwxdef]
  have hcM : E K l e ^ α • P.conn x ∈ P.Man := by
    rw [← hconn]
    exact hman α hα _ (hdesc 1 wx hwx)
  have hE : E K l e ∈ Rpi O K l e := E_mem l e _
  have hD1' : YD t ϖ (E K l e ^ (α + 1) • P.conn x) j ∈ Ideal.span {ED K t ϖ ^ γ} := by
    have h1 := congrFun (YD_E_pow_smul t ϖ hcM 1) j
    rw [smul_smul, ← pow_add, add_comm 1 α, Pi.smul_apply, smul_eq_mul, pow_one] at h1
    rw [h1]
    rwa [hconn] at hD1
  have hNE : N K (E K l e) ∈ Rpi O K l e := N_mem (derivative_mem_R l hE)
  obtain ⟨y1, hy1def⟩ : ∃ y1, y1 = (((β₀ + n : ℕ) : PowerSeries K) * N K (E K l e)) • m := ⟨_, rfl⟩
  have hy1 : y1 ∈ P.Man := hy1def ▸ P.smul_mem_Man (mul_mem (natCast_mem _ _) hNE) (P.M_le_Man hm)
  have hkey : E K l e ^ (α + 1) * N K (E K l e ^ (β₀ + n)) =
      E K l e ^ γ * (((β₀ + n : ℕ) : PowerSeries K) * N K (E K l e)) := by
    rw [hγ]
    rcases Nat.eq_zero_or_pos (β₀ + n) with h0 | h0
    · rw [h0, pow_zero, Derivation.map_one_eq_zero, Nat.cast_zero]
      ring
    · obtain ⟨b, hb⟩ : ∃ b, β₀ + n = b + 1 := ⟨β₀ + n - 1, by omega⟩
      rw [hb, Derivation.leibniz_pow, Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul]
      push_cast
      ring
  have hdec : E K l e ^ (α + 1) • P.conn x = E K l e ^ γ • y1 + E K l e ^ γ • P.EN m := by
    funext τ i
    rw [hxdef, P.conn_smul, hy1def, P.EN_apply]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hγ] at hkey ⊢
    linear_combination (m τ i) * hkey
  have hγM : E K l e ^ γ • y1 ∈ P.Man := P.smul_mem_Man (pow_mem hE γ) hy1
  have hENM : E K l e ^ γ • P.EN m ∈ P.Man := by
    have h1 : E K l e ^ (α + 1) • P.conn x ∈ P.Man := by
      rw [pow_succ, mul_comm, mul_smul]
      exact P.smul_mem_Man hE hcM
    have h2 : E K l e ^ γ • P.EN m = E K l e ^ (α + 1) • P.conn x - E K l e ^ γ • y1 := by
      rw [hdec]
      abel
    rw [h2]
    exact sub_mem h1 hγM
  have hsum := congrFun (YD_add t ϖ hγM hENM) j
  rw [← hdec, Pi.add_apply] at hsum
  have hy1' : YD t ϖ (E K l e ^ γ • y1) j ∈ Ideal.span {ED K t ϖ ^ γ} := by
    rw [YD_E_pow_smul t ϖ hy1 γ, Pi.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hEN : YD t ϖ (E K l e ^ γ • P.EN m) j ∈ Ideal.span {ED K t ϖ ^ γ} := by
    have h1 : YD t ϖ (E K l e ^ γ • P.EN m) j =
        YD t ϖ (E K l e ^ (α + 1) • P.conn x) j - YD t ϖ (E K l e ^ γ • y1) j := by
      rw [hsum]
      ring
    rw [h1]
    exact sub_mem hD1' hy1'
  have hsplit : E K l e ^ γ • P.EN m = E K l e ^ (α + β₀) • (E K l e ^ n • P.EN m) := by
    rw [smul_smul, ← pow_add, hγ, add_assoc]
  rw [hsplit, YD_E_pow_smul t ϖ hn (α + β₀), Pi.smul_apply, smul_eq_mul, hγ, ← add_assoc] at hEN
  exact mem_span_of_pow_mul hnz (α + β₀) n hEN
end GlobalTheory.GalStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TotallyComplexHostE
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary

namespace GlobalTheory.BlockCharInf

open Formalism.L2.Host Formalism.FrobeniusOrbits

theorem hasInfQ_mul' {L I : Type} [Field L] [NumberField L] [Fintype I] {φ : I → L →+* ℂ} {χ χ' : HChar L}
    {a a' : I → ℚ} (h : χ.HasInfQ φ a) (h' : χ'.HasInfQ φ a') : (χ * χ').HasInfQ φ (a + a') := by
  obtain ⟨n, hn, h⟩ := h
  obtain ⟨n', hn', h'⟩ := h'
  refine ⟨n + n', fun i => by simp [hn, hn', mul_add], fun k => ?_⟩
  rw [HChar.inf_mul, Units.val_mul, h k, h' k, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hne : φ i k ≠ 0 := by simp
  rw [Pi.add_apply, zpow_add₀ (div_ne_zero hne (by exact_mod_cast norm_ne_zero_iff.2 hne))]

theorem hasInfQ_inv' {L I : Type} [Field L] [NumberField L] [Fintype I] {φ : I → L →+* ℂ} {χ : HChar L}
    {a : I → ℚ} (h : χ.HasInfQ φ a) : (χ⁻¹).HasInfQ φ (-a) := by
  obtain ⟨n, hn, h⟩ := h
  refine ⟨-n, fun i => by simp [hn], fun k => ?_⟩
  rw [HChar.inf_inv, Units.val_inv_eq_inv_val, h k, ← Finset.prod_inv_distrib]
  simp

instance totallyComplexHostE {R : Ranks} (H : Formalism.BasicNotions.Host R) : IsTotallyComplex H.E := by
  haveI := H.isCMField_hostE
  infer_instance

theorem liftIdx_succ (D : D7) (i : D.nd.Loc) : (liftIdx D i).1 + 1 = D.nd.j i := by
  have := D.nd.j_range i
  simp only [liftIdx]
  omega

theorem block_hasInfQ (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch) (μ : D.what₂.Tup)
    (j : Fin D.R.m) :
    (Tp.tup μ j * C.eta⁻¹).HasInfQ (embPsi D.host) (fun g => -eExp D j g - 1 / 2) := by
  obtain ⟨n, hn, ho⟩ := Tp.xi_fin μ
  have h1 : (Tp.tup μ j).HasInfQ (embPsi D.host) (fun g => -eExp D j g) :=
    (C.isMu0 j).inf.mul_triv (HChar.inf_eq_one_of_order hn ho)
  have h2 : (C.eta⁻¹).HasInfQ (embPsi D.host) (-(fun _ => 1 / 2)) :=
    hasInfQ_inv' ⟨fun _ => 1, fun _ => by norm_num, C.isEta.inf⟩
  convert hasInfQ_mul' h1 h2 using 1
  funext g
  change -eExp D j g - 1 / 2 = -eExp D j g + -(1 / 2)
  ring

theorem main : ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D) (nch : NChoice D) (Tp : Formalism.L2.Host.TupTied D C nch),
    Formalism.L2.Host.NCharTied D C nch Tp → BlockCharParam D := by
  intro D C nch Tp N i ρ
  have he : (N.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1 = Tp.tup (D.nd.mu i) (liftIdx D i) * C.eta⁻¹ := by
    rw [N.tw, N.muC i (liftIdx D i) (liftIdx_succ D i), N.etaTinv]
  have hI := block_hasInfQ D C nch Tp (D.nd.mu i) (liftIdx D i)
  rw [← he] at hI
  obtain ⟨h1, h2⟩ := N.infG _ _ hI (D.eTau ρ)
  have hval : eExp D (liftIdx D i) (D.eTau ρ) = (D.hc ρ).e (liftIdx D i) := by
    simp [eExp]
  have hconj : embOver D ρ true = (starRingEnd ℂ).comp (embPsi D.host (D.eTau ρ)) :=
    RingHom.ext fun x => GlobalTheory.JumpDictionaryFoundation.embOver_true_apply D ρ x
  constructor
  · have e0 : embOver D ρ false = embPsi D.host (D.eTau ρ) := rfl
    rw [e0, h1, hval]
  · rw [hconj, h2, hval]
    push_cast
    congr 1
    ring

end GlobalTheory.BlockCharInf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopologicalClosureZpowersSupInertia
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.FrobGen
open GlobalTheory.MemLoc GlobalTheory.MemLoc.FrobLaws

theorem exists_gen_of_isOpen {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (J : Subgroup G) [J.Normal] (g : G) (U : Subgroup G) (hU : IsOpen (U : Set G))
    (hg : (Subgroup.zpowers g ⊔ J).topologicalClosure = ⊤) :
    ∃ φ : U, (Subgroup.zpowers φ ⊔ J.subgroupOf U).topologicalClosure = ⊤ := by
  let π : G →* G ⧸ J := QuotientGroup.mk' J
  let S : AddSubgroup ℤ :=
    { carrier := {n | π g ^ n ∈ U.map π}
      add_mem' := fun {a b} ha hb => by
        show π g ^ (a + b) ∈ U.map π
        rw [zpow_add]; exact mul_mem ha hb
      zero_mem' := by
        show π g ^ (0 : ℤ) ∈ U.map π
        rw [zpow_zero]; exact one_mem _
      neg_mem' := fun {a} ha => by
        show π g ^ (-a) ∈ U.map π
        rw [zpow_neg]; exact inv_mem ha }
  obtain ⟨f, hf⟩ := S.isAddCyclic_iff_exists_zmultiples_eq.mp S.isAddCyclic
  have hf : S = AddSubgroup.closure {f} := by rw [← hf, AddSubgroup.zmultiples_eq_closure]
  have hfS : f ∈ S := by rw [hf]; exact AddSubgroup.subset_closure rfl
  obtain ⟨φ, hφU, hφ⟩ : π g ^ f ∈ U.map π := hfS
  refine ⟨⟨φ, hφU⟩, ?_⟩
  have hd : Dense ((Subgroup.zpowers g ⊔ J : Subgroup G) : Set G) := by
    rw [dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, hg, Subgroup.coe_top]
  have hd2 := hd.preimage (f := (Subtype.val : U → G)) hU.isOpenMap_subtype_val
  apply SetLike.coe_injective
  rw [Subgroup.topologicalClosure_coe, Subgroup.coe_top, ← dense_iff_closure_eq]
  refine hd2.mono fun y hy => ?_
  have h1 : π y ∈ (Subgroup.zpowers g ⊔ J).map π := ⟨y, hy, rfl⟩
  have h2 : J.map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  rw [Subgroup.map_sup, h2, sup_bot_eq, MonoidHom.map_zpowers] at h1
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h1
  have hnS : n ∈ S := by
    show π g ^ n ∈ U.map π
    rw [hn]; exact ⟨y, y.2, rfl⟩
  rw [hf, AddSubgroup.mem_closure_singleton] at hnS
  obtain ⟨k, rfl⟩ := hnS
  have h3 : π ((φ ^ k)⁻¹ * y) = 1 := by
    rw [map_mul, map_inv, map_zpow, hφ, ← hn, ← zpow_mul, smul_eq_mul, mul_comm f k, inv_mul_cancel]
  have h4 : (φ ^ k)⁻¹ * (y : G) ∈ J := by
    rw [← QuotientGroup.ker_mk' J]; exact h3
  have h5 : y = (⟨φ, hφU⟩ : U) ^ k * ((((⟨φ, hφU⟩ : U) ^ k))⁻¹ * y) := by
    rw [mul_inv_cancel_left]
  rw [SetLike.mem_coe, h5]
  refine Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers _ _) ?_
  rw [Subgroup.mem_subgroupOf]
  simpa using h4

variable {l : ℕ} [hl : Fact l.Prime]

theorem root_mem_Kur {ζ : Om l} {m : ℕ} (hm : 0 < m) (hlm : ¬ l ∣ m) (h : ζ ^ m = 1) :
    ζ ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, h⟩

theorem normal_fix : (MaximalUnramifiedExtension l).fixingSubgroup.Normal := by
  refine ⟨fun σ hσ h => ?_⟩
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  intro x hx
  obtain ⟨m, hm, hlm, H⟩ := exists_level hx
  refine H _ 1 fun ζ hζ => ?_
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply,
    hσ _ (root_mem_Kur hm hlm (by rw [← map_pow, hζ, map_one])), ← AlgEquiv.mul_apply,
    mul_inv_cancel]

theorem norm_sub_lt {σ : GQ l} (hσ : σ ∈ (MaximalUnramifiedExtension l).fixingSubgroup) (x : Om l) (hx : ‖x‖ ≤ 1) :
    ‖σ x - x‖ < 1 := by
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
  have key : ∀ y : Om l, ‖y‖ < 1 → ‖σ y - y‖ < 1 := fun y hy => by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_gal]; exact hy
    · rw [norm_neg]; exact hy
  rcases hx.lt_or_eq with h | h
  · exact key x h
  · obtain ⟨ζ, m, hm, hlm, hζ, hn⟩ := FrobLaws.exists_root (l := l) x h
    have := key _ hn
    rw [map_sub, hσ ζ (root_mem_Kur hm hlm hζ)] at this
    simpa using this

theorem exists_gen_top :
    ∃ g : GQ l, (Subgroup.zpowers g ⊔ (MaximalUnramifiedExtension l).fixingSubgroup).topologicalClosure = ⊤ := by
  obtain ⟨σ, hσ⟩ := exists_frobenius_Kur l
  obtain ⟨g, hg⟩ := exists_ext σ
  refine ⟨g, ?_⟩
  let H : ClosedSubgroup (GQ l) :=
    ⟨(Subgroup.zpowers g ⊔ (MaximalUnramifiedExtension l).fixingSubgroup).topologicalClosure,
      Subgroup.isClosed_topologicalClosure _⟩
  have h1 := InfiniteGalois.fixingSubgroup_fixedField H
  have h2 : IntermediateField.fixedField (H : Subgroup (GQ l)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hK : x ∈ MaximalUnramifiedExtension l := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup (MaximalUnramifiedExtension l), IntermediateField.mem_fixedField_iff]
      exact fun f hf => hx f (Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_right hf))
    have hgx : g x = x := hx g (Subgroup.le_topologicalClosure _
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers g)))
    obtain ⟨c, hc⟩ := (frob_laws l σ hσ).2.2 ⟨x, hK⟩ (Subtype.ext (by rw [← hg]; exact hgx))
    rw [IntermediateField.mem_bot]
    exact ⟨c, congrArg Subtype.val hc⟩
  rw [h2, IntermediateField.fixingSubgroup_bot] at h1
  exact h1.symm

end GlobalTheory.FrobGen

theorem GlobalTheory.exists_topologicalClosure_zpowers_sup_inertia (l : ℕ) [Fact l.Prime] (K : FinExt l) :
    ∃ φ : ↥(GK K), (Subgroup.zpowers φ ⊔ IK K).topologicalClosure = ⊤ := by
  obtain ⟨g, hg⟩ := GlobalTheory.FrobGen.exists_gen_top (l := l)
  haveI := GlobalTheory.FrobGen.normal_fix (l := l)
  haveI := K.2
  obtain ⟨φ, hφ⟩ := GlobalTheory.FrobGen.exists_gen_of_isOpen _ g (GK K) K.1.fixingSubgroup_isOpen hg
  refine ⟨φ, eq_top_iff.2 (hφ ▸ ?_)⟩
  refine Subgroup.topologicalClosure_minimal _ ?_ (Subgroup.isClosed_topologicalClosure _)
  refine le_trans (sup_le_sup_left (fun σ hσ => ?_) _) (Subgroup.le_topologicalClosure _)
  exact Subgroup.subset_closure fun x hx => GlobalTheory.FrobGen.norm_sub_lt hσ x hx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinTwoHomsERegularAssociated
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinTwoHomsERegularAssociated
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem mem_nonZeroDivisors_of_invertible_span {A : Type} [CommRing A] {I : Ideal A}
    (hI : Module.Invertible A ↥I) {d : A} (hd : I = Ideal.span {d}) : d ∈ nonZeroDivisors A := by
  have hdI : d ∈ I := hd ▸ Ideal.mem_span_singleton_self d
  let φ : A →ₗ[A] ↥I := LinearMap.toSpanSingleton A ↥I ⟨d, hdI⟩
  have hs : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    rw [hd] at hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    exact ⟨a, Subtype.ext (by simp [φ])⟩
  have hb := Module.Invertible.bijective_of_surjective hs
  refine mem_nonZeroDivisors_iff.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · refine hb.1 (?_ : φ a = φ 0)
    exact Subtype.ext (by simp [φ]; linear_combination ha)
  · refine hb.1 (?_ : φ a = φ 0)
    exact Subtype.ext (by simp [φ]; linear_combination ha)

theorem associated_of_span_eq {A : Type} [CommRing A] {d d' : A} (hd : d ∈ nonZeroDivisors A)
    (h : Ideal.span {d} = Ideal.span {d'}) : Associated d d' := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (h ▸ Ideal.mem_span_singleton_self d)
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (h.symm ▸ Ideal.mem_span_singleton_self d')
  have hab : a * b = 1 := by
    have : d * (a * b - 1) = 0 := by linear_combination a * hb + ha
    exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff.1 hd).1 _ this)
  exact ⟨⟨b, a, by rw [mul_comm]; exact hab, hab⟩, by rw [Units.val_mk, mul_comm]; exact hb⟩

theorem hf_E_pair : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (f g : Hom bk.prism B),
    BK.hf f bk.E ∈ nonZeroDivisors B.A ∧ Associated (BK.hf f bk.E) (BK.hf g bk.E) ∧
      BK.hf f bk.E ∣ BK.hf g X - BK.hf f X := by
  intro l _ K bk B f g
  obtain ⟨hfI, hfX⟩ := GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk B f
  obtain ⟨hgI, hgX⟩ := GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk B g
  have hreg := mem_nonZeroDivisors_of_invertible_span B.inv hfI
  refine ⟨hreg, associated_of_span_eq hreg (hfI.symm.trans hgI), ?_⟩
  rw [← Ideal.mem_span_singleton, ← hfI]
  exact Ideal.Quotient.eq.1 (hgX.trans hfX.symm)

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinTwoHomsERegularAssociatedStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_two_homs_E_regular_associated : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), BK.hf f bk.E ∈ nonZeroDivisors B.A ∧ Associated (BK.hf f bk.E) (BK.hf g bk.E) ∧ BK.hf f bk.E ∣ BK.hf g X - BK.hf f X := by
  first | exact @GlobalTheory.BSP.hf_E_pair | exact GlobalTheory.BSP.hf_E_pair | (intros; apply GlobalTheory.BSP.hf_E_pair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraRestrictionTwoBlockCuspidalEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraRestrictionTwoBlockCuspidalEqZero
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq

theorem list_sum_posNat {ι : Type} (L : List ι) (f : ι → ℂ) (hf : ∀ p ∈ L, ∃ n : ℕ, 0 < n ∧ f p = n) :
    ∃ m : ℕ, (L.map f).sum = m ∧ (L ≠ [] → 0 < m) := by
  induction L with
  | nil => exact ⟨0, by simp, fun h => absurd rfl h⟩
  | cons p L ih =>
    obtain ⟨n, hn, hp⟩ := hf p (List.mem_cons_self ..)
    obtain ⟨m, hm, -⟩ := ih fun q hq => hf q (List.mem_cons_of_mem _ hq)
    refine ⟨n + m, ?_, fun _ => by omega⟩
    simp [List.map_cons, List.sum_cons, hp, hm]

theorem res_cusp_eq_zero : ∀ (g : ℕ) [Fact g.Prime] (d a : ℕ) (χ : Gn g d → ℂ), IsCusp χ → 0 < a → a < d →
    ∀ x y, res a (d - a) χ x y = 0 := by
  intro g _ d a χ hχ ha had x y
  obtain ⟨-, hirr, hc⟩ := hχ
  have hchar : IsChar χ := by
    obtain ⟨V, -, hV⟩ := hirr
    exact ⟨V, hV⟩
  obtain ⟨L, hL, hres⟩ := (GlobalTheory.T.harishChandra_induction_character_restriction_decomp g a (d - a) d (by omega)).2 χ hchar
  have hpos : ∀ p ∈ L, ∃ n : ℕ, 0 < n ∧ (fun p : (Gn g a → ℂ) × (Gn g (d - a) → ℂ) => p.1 1 * p.2 1) p = n := by
    intro p hp
    obtain ⟨d₁, hd₁, h₁⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree (Gn g a) 0 p.1).2.1 (hL p hp).1
    obtain ⟨d₂, hd₂, h₂⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree (Gn g (d - a)) 0 p.2).2.1 (hL p hp).2
    exact ⟨d₁ * d₂, Nat.mul_pos hd₁ hd₂, by simp [h₁, h₂]⟩
  obtain ⟨m, hm, hmpos⟩ := list_sum_posNat L _ hpos
  have hL0 : L = [] := by
    by_contra hne
    have h0 : res a (d - a) χ 1 1 = 0 := hc a ha had
    rw [hres, hm] at h0
    have := hmpos hne
    exact absurd (by exact_mod_cast h0 : m = 0) (by omega)
  rw [hres, hL0]
  simp

end GlobalTheory.GLq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraRestrictionTwoBlockCuspidalEqZeroStatement
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraRestrictionTwoBlock_cuspidal_eq_zero : ∀ (g : ℕ) [Fact g.Prime] (d a : ℕ) (χ : Gn g d → ℂ), IsCusp χ → 0 < a → a < d → ∀ x y, res a (d - a) χ x y = 0 := by
  first | exact @GlobalTheory.GLq.res_cusp_eq_zero | exact GlobalTheory.GLq.res_cusp_eq_zero | (intros; apply GlobalTheory.GLq.res_cusp_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatPowDvdPerPowMod
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

theorem flatPow_dvd_perPow_mod : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ →
    ∀ (M n : ℕ), ∃ (c : ℕ) (y : Ainf l), (l : Ainf l) ^ n ∣ bk.ev X ^ c - τ ^ M * y := by
  intro l _ K bk τ hτ M n
  have hU : IsUnit (inclW l (τ ^ M)) := by
    rw [map_pow]
    exact (GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ).1.pow M
  obtain ⟨m, t, h⟩ := GlobalTheory.BSP.BddDen.main l K bk (τ ^ M) hU n
  refine ⟨m, t, ?_⟩
  have : bk.ev X ^ m - τ ^ M * t = -(t * τ ^ M - bk.ev X ^ m) := by ring
  rw [this]
  exact (dvd_neg).2 h

end GlobalTheory.BKLim
end
end
