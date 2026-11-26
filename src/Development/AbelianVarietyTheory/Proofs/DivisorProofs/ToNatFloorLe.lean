module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSelfDualAdelicFrameLevelOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFormsFiniteStabilisers
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ColumnDataLaws
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GeneralDiagonalMatrix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfIsONFr
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUnique

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToNatFloorLe
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdelicScalar.SizeBounds

theorem one_le_rdE (D : D7) : (1 : ℝ) ≤ D.host.rdE := by
  unfold Formalism.BasicNotions.Host.rdE
  apply Real.one_le_rpow
  · have h := NumberField.discr_ne_zero D.host.E
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs h
  · positivity

theorem one_le_b (D : D7) (i : Fin D.R.m) (b : ℝ) (h : Sizes D i b) : 1 ≤ b := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Sizes at h
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := by
    rw [← Fintype.card_pos_iff, D.what₂.card_Tau]
    show 0 < 2 * D.R.ord
    have h1 := D.R.two_le_m
    have h2 := D.R.m_le_f
    omega
  obtain ⟨-, -, -, hb⟩ := h.1 τ
  have hq := (D.hc τ).gap_be i
  have hr : ((((D.R.t : ℚ) + 3) / 2 : ℚ) : ℝ) ≤ (((D.hc τ).e i - (D.hc τ).b i : ℚ) : ℝ) := by
    exact_mod_cast hq
  push_cast at hr
  have habs := abs_le.mp (hb i)
  have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  linarith [habs.1, habs.2]

theorem lam_bounds (D : D7) (i : Fin D.R.m) (b : ℝ) (h : Sizes D i b) (τ : D.what₂.Tau) (n : ℕ) :
    -b ≤ ((Formalism.L2.NTheta.lamAt (D.hc τ) n : ℚ) : ℝ) + (((D.hc τ).e i : ℚ) : ℝ) ∧
      ((Formalism.L2.NTheta.lamAt (D.hc τ) n : ℚ) : ℝ) + (((D.hc τ).e i : ℚ) : ℝ) ≤ 3 * b := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Sizes at h
  obtain ⟨he0, he2, hv, hb⟩ := h.1 τ
  have hb0 : (0 : ℝ) ≤ b := by linarith
  unfold Formalism.L2.NTheta.lamAt
  split_ifs with h1 h2
  · obtain ⟨hv0, hv1⟩ := hv ⟨n, h1⟩
    constructor <;> linarith
  · have habs := abs_le.mp (hb ⟨n - (D.R.k - 1), h2⟩)
    push_cast
    constructor <;> linarith [habs.1, habs.2]
  · push_cast
    constructor <;> linarith

theorem toNat_floor_le (x : ℚ) (c : ℝ) (hc : 0 ≤ c) (hx : (x : ℝ) ≤ c) : ((⌊x⌋.toNat : ℕ) : ℝ) ≤ c := by
  rcases le_or_gt ⌊x⌋ 0 with h0 | h0
  · rw [Int.toNat_of_nonpos h0]
    simpa using hc
  · have h1 : ((⌊x⌋.toNat : ℕ) : ℤ) = ⌊x⌋ := Int.toNat_of_nonneg h0.le
    have h2 : ((⌊x⌋.toNat : ℕ) : ℝ) = ((⌊x⌋ : ℤ) : ℝ) := by exact_mod_cast h1
    rw [h2]
    have h3 : ((⌊x⌋ : ℤ) : ℝ) ≤ ((x : ℚ) : ℝ) := by exact_mod_cast Int.floor_le x
    linarith

theorem aPl_le (D : D7) (i : Fin D.R.m) (b : ℝ) (h : Sizes D i b) (p : ℕ) (τ : D.what₂.Tau) (n : ℕ) :
    (aPl D i p τ n : ℝ) ≤ 3 * b := by
  have hlam := (lam_bounds D i b h τ n).2
  have hb1 := one_le_b D i b h
  unfold aPl
  split_ifs with hn
  · apply toNat_floor_le _ _ (by linarith)
    push_cast
    have hnp : (n : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hn
    have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
    linarith
  · simp only [Nat.cast_zero]
    linarith

theorem aMi_le (D : D7) (i : Fin D.R.m) (b : ℝ) (h : Sizes D i b) (p q : ℕ) (τ : D.what₂.Tau) (n : ℕ) :
    (aMi D i p q τ n : ℝ) ≤ 3 * b := by
  have hlam := (lam_bounds D i b h τ (p + (q - n) - 1)).1
  have hb1 := one_le_b D i b h
  unfold aMi
  split_ifs with hn
  · apply toNat_floor_le _ _ (by linarith)
    push_cast
    have hqn : (0 : ℝ) ≤ ((q - n : ℕ) : ℝ) := Nat.cast_nonneg _
    have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
    linarith
  · simp only [Nat.cast_zero]
    linarith

theorem degAt_le (D : D7) (i : Fin D.R.m) (b : ℝ) (h : Sizes D i b) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) :
    (degAt D i σ ρ : ℝ) ≤ 3 * (D.R.r : ℝ) * b := by
  have hb1 := one_le_b D i b h
  have hi := i.isLt
  have hs := D.sp.W_sigval ((i : ℕ) + 1) (by omega) (by omega) (tauE D ρ)
  have hP : ∀ n, ((aPlAt D i σ ρ n : ℕ) : ℝ) ≤ 3 * b := fun n => aPl_le D i b h _ _ n
  have hM : ∀ n, ((aMiAt D i σ ρ n : ℕ) : ℝ) ≤ 3 * b := fun n => aMi_le D i b h _ _ _ n
  have h1 := Finset.sum_le_sum (s := Finset.range (pW D i ρ)) (fun n _ => hP n)
  have h2 := Finset.sum_le_sum (s := Finset.range (qW D i ρ)) (fun n _ => hM n)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1 h2
  have hr : (pW D i ρ : ℝ) + (qW D i ρ : ℝ) = (D.R.r : ℝ) := by
    have hn : pW D i ρ + qW D i ρ = D.R.r := by
      simp only [pW, qW, Wc, hs]
      unfold Formalism.BasicNotions.Ranks.sigW Formalism.BasicNotions.Ranks.r
      dsimp only
      omega
    exact_mod_cast hn
  unfold degAt
  push_cast
  calc _ ≤ (pW D i ρ : ℝ) * (3 * b) + (qW D i ρ : ℝ) * (3 * b) := add_le_add h1 h2
    _ = 3 * (D.R.r : ℝ) * b := by rw [← hr]; ring

theorem sizes : ∀ (D : D7) (i : Fin D.R.m) (b : ℝ), Sizes D i b → (5.5 : ℝ) ≤ Lp D b ∧ Real.log (D.R.nV : ℝ) ≤ Lp D b ∧ 0 ≤ b ∧ Real.log (3 * (D.R.r : ℝ) * b + 2) ≤ 2 * Lp D b ∧ ∀ (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau), (degAt D i σ ρ : ℝ) ≤ 3 * (D.R.r : ℝ) * b := by
  intro D i b h
  have hb1 := one_le_b D i b h
  have hrd := one_le_rdE D
  have hnV : (1 : ℝ) ≤ (D.R.nV : ℝ) := by
    have h1 := D.R.t_odd.pos
    have h2 : 1 ≤ D.R.nV := by
      unfold Formalism.BasicNotions.Ranks.nV
      omega
    exact_mod_cast h2
  have hk5 : 5 ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    have := D.R.two_le_m
    omega
  have hrk : D.R.r ≤ 2 * D.R.k := by
    have := D.R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega
  have hk : (5 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast hk5
  have hr2 : (D.R.r : ℝ) ≤ 2 * (D.R.k : ℝ) := by exact_mod_cast hrk
  have hgl := h.2
  have hg0 := hgl 0
  have hg1 := hgl 1
  set y : ℝ := (D.R.k : ℝ) * b with hy
  have hy5 : 5 ≤ y := by nlinarith
  have hy8 : y ^ 3 ≤ y ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hyy : 25 ≤ y * y := by nlinarith
  have hy3 : 25 * y ≤ y ^ 3 := by nlinarith [mul_le_mul_of_nonneg_right hyy (by linarith : (0 : ℝ) ≤ y)]
  have hyP : (390625 : ℝ) ≤ y ^ 8 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5) hy5 8
    norm_num at this
    linarith
  have hg1' : (1 : ℝ) ≤ (D.host.g 1 : ℝ) := by linarith
  have hg0' : (0 : ℝ) ≤ (D.host.g 0 : ℝ) := Nat.cast_nonneg _
  have hbr : (1 : ℝ) ≤ b * D.host.rdE := one_le_mul_of_one_le_of_one_le hb1 hrd
  have hG : (D.host.g 0 : ℝ) ≤ (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) := le_mul_of_one_le_right hg0' hg1'
  have hA : (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) ≤ b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) :=
    le_mul_of_one_le_left (by positivity) hbr
  have hB : b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ≤
      b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ) :=
    le_mul_of_one_le_right (by positivity) hnV
  have hC : (1 : ℝ) ≤ b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := by linarith
  have hD : (D.R.nV : ℝ) ≤ b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ) :=
    le_mul_of_one_le_left (by positivity) hC
  have hX : y ^ 8 ≤ b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ) := by linarith
  have hL : Lp D b = Real.log (b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ)) := rfl
  have hXpos : 0 < b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ) := by linarith
  have he6 : Real.exp (5.5 : ℝ) ≤ 729 := by
    have h1 : Real.exp (5.5 : ℝ) ≤ Real.exp 6 := Real.exp_le_exp.mpr (by norm_num)
    have h2 : Real.exp 6 = Real.exp 1 ^ 6 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h3 : Real.exp 1 ^ 6 ≤ (3 : ℝ) ^ 6 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith [Real.exp_one_lt_d9]) 6
    norm_num at h3
    linarith
  have h55 : (5.5 : ℝ) ≤ Lp D b := by
    rw [hL]
    calc (5.5 : ℝ) = Real.log (Real.exp 5.5) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) (by linarith)
  refine ⟨h55, ?_, by linarith, ?_, fun σ ρ => degAt_le D i b h σ ρ⟩
  · rw [hL]
    exact Real.log_le_log (by linarith) hD
  · have hb0 : (0 : ℝ) ≤ b := by linarith
    have hrb : (D.R.r : ℝ) * b ≤ (2 * (D.R.k : ℝ)) * b := mul_le_mul_of_nonneg_right hr2 hb0
    have h32 : 3 * (D.R.r : ℝ) * b + 2 ≤ b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ) := by
      nlinarith
    have hpos : 0 < 3 * (D.R.r : ℝ) * b + 2 := by positivity
    have hlog := Real.log_le_log hpos h32
    rw [← hL] at hlog
    linarith

end GlobalTheory.AdelicScalar.SizeBounds
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero
noncomputable section

open MvPolynomial Formalism.BasicNotions.TH

namespace GlobalTheory.CharPair

variable (P Q R S : ℕ)

abbrev Mdl : Type := MvPolynomial (Fin P × Fin Q) ℂ

def mR (a : Fin P) (b : Fin Q) : Pol P Q R 0 :=
  ∑ c : Fin R, X (Sum.inl a, Sum.inl c) * X (Sum.inr b, Sum.inl c)

def mS (a : Fin P) (b : Fin Q) : Pol P Q 0 S :=
  ∑ c : Fin S, X (Sum.inl a, Sum.inr c) * X (Sum.inr b, Sum.inr c)

def detR (h : P ≤ R) : Pol P Q R 0 :=
  (Matrix.of fun a c : Fin P => (X (Sum.inl a, Sum.inl (Fin.castLE h c)) : Pol P Q R 0)).det

def detS (h : Q ≤ S) : Pol P Q 0 S :=
  (Matrix.of fun b c : Fin Q => (X (Sum.inr b, Sum.inr (Fin.castLE h c)) : Pol P Q 0 S)).det

def embR (h : P ≤ R) (k : ℕ) : Mdl P Q →ₗ[ℂ] Pol P Q R 0 :=
  LinearMap.mulRight ℂ (detR P Q R h ^ k) ∘ₗ (aeval fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2).toLinearMap

def embS (h : Q ≤ S) (k' : ℕ) : Mdl P Q →ₗ[ℂ] Pol P Q 0 S :=
  LinearMap.mulRight ℂ (detS P Q S h ^ k') ∘ₗ (aeval fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2).toLinearMap

variable {P Q}

abbrev mulM (a : Fin P) (b : Fin Q) : Module.End ℂ (Mdl P Q) := LinearMap.mulLeft ℂ (X (a, b))

abbrev derM (a : Fin P) (b : Fin Q) : Module.End ℂ (Mdl P Q) := (pderiv (a, b)).toLinearMap

variable (P Q)

def opR (k : ℕ) : Ix P Q → Ix P Q → Module.End ℂ (Mdl P Q)
  | .inl a, .inr b => mulM a b
  | .inr b, .inl a => -(∑ a', ∑ b', mulM a' b' * derM a' b * derM a b' + ((R + k : ℕ) : ℂ) • derM a b)
  | .inl a, .inl a' => ∑ b, mulM a b * derM a' b + (if a = a' then (k : ℂ) + (R : ℂ) / 2 else 0) • 1
  | .inr b, .inr b' => -(∑ a, mulM a b' * derM a b) - (if b = b' then (R : ℂ) / 2 else 0) • 1

def opS (k' : ℕ) : Ix P Q → Ix P Q → Module.End ℂ (Mdl P Q)
  | .inl a, .inr b => -mulM a b
  | .inr b, .inl a => ∑ a', ∑ b', mulM a' b' * derM a' b * derM a b' + ((S + k' : ℕ) : ℂ) • derM a b
  | .inl a, .inl a' => -(∑ b, mulM a b * derM a' b) - (if a = a' then (S : ℂ) / 2 else 0) • 1
  | .inr b, .inr b' => ∑ a, mulM a b' * derM a b + (if b = b' then (k' : ℂ) + (S : ℂ) / 2 else 0) • 1

def actR (k : ℕ) : Mat P Q →ₗ[ℂ] Module.End ℂ (Mdl P Q) :=
  ∑ i, ∑ j, (Matrix.entryLinearMap ℂ ℂ i j).smulRight (opR P Q R k i j)

theorem actR_apply (k : ℕ) (Z : Mat P Q) : actR P Q R k Z = ∑ i, ∑ j, Z i j • opR P Q R k i j := by
  simp [actR, LinearMap.sum_apply]

theorem detR_ne_zero (P Q R : ℕ) (h : P ≤ R) : detR P Q R h ≠ 0 := by
  let g : Fin P × Fin P → Ix P Q × Ix R 0 := fun ac => (Sum.inl ac.1, Sum.inl (Fin.castLE h ac.2))
  have hf : Function.Injective g := by
    rintro ⟨a, c⟩ ⟨a', c'⟩ hac
    simp only [g, Prod.mk.injEq, Sum.inl.injEq] at hac
    exact Prod.ext hac.1 (Fin.castLE_injective h hac.2)
  have : detR P Q R h = rename g (Matrix.det (Matrix.mvPolynomialX (Fin P) (Fin P) ℂ)) := by
    rw [detR, ← AlgHom.coe_toRingHom, RingHom.map_det]; congr 1; ext a c; simp [g, Matrix.mvPolynomialX]
  rw [this]; intro h0
  exact Matrix.det_mvPolynomialX_ne_zero _ _ ((map_eq_zero_iff _ (rename_injective _ hf)).1 h0)

theorem detS_ne_zero (P Q S : ℕ) (h : Q ≤ S) : detS P Q S h ≠ 0 := by
  let g : Fin Q × Fin Q → Ix P Q × Ix 0 S := fun bc => (Sum.inr bc.1, Sum.inr (Fin.castLE h bc.2))
  have hf : Function.Injective g := by
    rintro ⟨b, c⟩ ⟨b', c'⟩ hbc
    simp only [g, Prod.mk.injEq, Sum.inr.injEq] at hbc
    exact Prod.ext hbc.1 (Fin.castLE_injective h hbc.2)
  have : detS P Q S h = rename g (Matrix.det (Matrix.mvPolynomialX (Fin Q) (Fin Q) ℂ)) := by
    rw [detS, ← AlgHom.coe_toRingHom, RingHom.map_det]; congr 1; ext b c; simp [g, Matrix.mvPolynomialX]
  rw [this]; intro h0
  exact Matrix.det_mvPolynomialX_ne_zero _ _ ((map_eq_zero_iff _ (rename_injective _ hf)).1 h0)

end GlobalTheory.CharPair

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSumVanishesOfParabolicSums
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PelUniformisedGeometricFree
open MeasureTheory Matrix
open scoped Classical

noncomputable section

namespace GlobalTheory.OrbDesc

variable {H : Type} [Group H]

theorem mk_out_of_le {T P L : Subgroup H} (hTP : T ≤ P) (x : H) :
    DoubleCoset.mk P L (Quotient.out (DoubleCoset.mk T L x)) = DoubleCoset.mk P L x := by
  obtain ⟨t, ht, l, hl, h⟩ := DoubleCoset.mk_out_eq_mul T L x
  rw [h, DoubleCoset.eq]
  exact ⟨t⁻¹, P.inv_mem (hTP ht), l⁻¹, L.inv_mem hl, by group⟩

theorem locPart_inf_conj {T P L : Subgroup H} (hTP : T ≤ P) {p : H} (hp : p ∈ P) (y : H) :
    GlobalTheory.LKLoc.locPart T (P ⊓ L.map (MulAut.conj y).toMonoidHom) p = GlobalTheory.LKLoc.locPart T L (p * y) := by
  unfold GlobalTheory.LKLoc.locPart
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hg, k, ⟨_, l, hl, rfl⟩, rfl⟩
    exact ⟨hg, l, hl, by group⟩
  · rintro ⟨hg, l, hl, rfl⟩
    refine ⟨hg, y * l * y⁻¹, ⟨?_, l, hl, rfl⟩, by group⟩
    have e : y * l * y⁻¹ = p⁻¹ * (p * y * l * (p * y)⁻¹) * p := by group
    rw [e]
    exact P.mul_mem (P.mul_mem (P.inv_mem hp) (hTP hg)) hp

theorem dsum_eq_zero_of_par (H : Type) [Group H] (T P L U : Subgroup H) (Ψ : H → ℂ) (hTP : T ≤ P)
    (hT : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s) (hΨl : ∀ t ∈ T, ∀ x, Ψ (t * x) = Ψ x)
    (hΨr : ∀ l ∈ L, ∀ x, Ψ (x * l) = Ψ x)
    (hy : ∀ y : H, dsum T (P ⊓ L.map (MulAut.conj y).toMonoidHom) U
      (fun x => if x ∈ P then Ψ (x * y) else 0) = 0) :
    dsum T L U Ψ = 0 := by
  set F : DoubleCoset.Quotient (T : Set H) (L : Set H) → ℂ := fun q => wt T L U Ψ (Quotient.out q) with hF
  set π : DoubleCoset.Quotient (T : Set H) (L : Set H) → DoubleCoset.Quotient (P : Set H) (L : Set H) :=
    fun q => DoubleCoset.mk P L (Quotient.out q) with hπ
  have hdef : dsum T L U Ψ = ∑ᶠ q, F q := rfl
  rw [hdef]
  by_cases hfin : (Function.support F).Finite
  swap
  · exact finsum_of_infinite_support hfin
  rw [finsum_eq_sum F hfin, ← Finset.sum_fiberwise_of_maps_to (g := π)
    (t := hfin.toFinset.image π) (fun _ h => Finset.mem_image_of_mem _ h)]
  refine Finset.sum_eq_zero fun r _ => ?_
  obtain ⟨y, rfl⟩ : ∃ y, DoubleCoset.mk P L y = r := ⟨Quotient.out r, DoubleCoset.out_eq' _⟩
  set Ly := P ⊓ L.map (MulAut.conj y).toMonoidHom with hLy
  have hLyP : ∀ k ∈ Ly, k ∈ P := fun k hk => (Subgroup.mem_inf.1 hk).1
  set G : DoubleCoset.Quotient (T : Set H) (Ly : Set H) → ℂ :=
    fun q => wt T Ly U (fun x => if x ∈ P then Ψ (x * y) else 0) (Quotient.out q) with hG
  set φ : DoubleCoset.Quotient (T : Set H) (Ly : Set H) → DoubleCoset.Quotient (T : Set H) (L : Set H) :=
    fun q => DoubleCoset.mk T L (Quotient.out q * y) with hφ
  set A : Set (DoubleCoset.Quotient (T : Set H) (Ly : Set H)) := {q | Quotient.out q ∈ P} with hA
  have h0 : ∑ᶠ q, G q = 0 := hy y
  have hsuppG : Function.support G ⊆ A := by
    intro q hq
    by_contra hn
    have hn' : Quotient.out q ∉ P := hn
    apply hq
    show wt T Ly U (fun x => if x ∈ P then Ψ (x * y) else 0) (Quotient.out q) = 0
    simp only [wt, if_neg hn', mul_zero]
  have hGF : ∀ q ∈ A, G q = F (φ q) := by
    intro q hq
    have hq' : Quotient.out q ∈ P := hq
    show wt T Ly U (fun x => if x ∈ P then Ψ (x * y) else 0) (Quotient.out q) =
      wt T L U Ψ (Quotient.out (DoubleCoset.mk T L (Quotient.out q * y)))
    rw [wt_out U hT hΨl hΨr]
    simp only [wt, if_pos hq', hLy, locPart_inf_conj hTP hq' y]
  have hinj : Set.InjOn φ A := by
    intro q₁ h₁ q₂ h₂ h
    obtain ⟨t, ht, l, hl, e⟩ := (@DoubleCoset.eq _ _ T L _ _).1 h
    rw [← DoubleCoset.out_eq' q₁, ← DoubleCoset.out_eq' q₂, DoubleCoset.eq]
    refine ⟨t, ht, y * l * y⁻¹, Subgroup.mem_inf.2 ⟨?_, l, hl, rfl⟩, ?_⟩
    · have e' : y * l * y⁻¹ = (t * Quotient.out q₁)⁻¹ * Quotient.out q₂ := by
        rw [show Quotient.out q₂ = t * (Quotient.out q₁ * y) * l * y⁻¹ by rw [← e]; group]
        group
      rw [e']
      exact P.mul_mem (P.inv_mem (P.mul_mem (hTP ht) h₁)) h₂
    · rw [show Quotient.out q₂ = t * (Quotient.out q₁ * y) * l * y⁻¹ by rw [← e]; group]
      group
  have himg : φ '' A = {q | π q = DoubleCoset.mk P L y} := by
    ext q
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨q', hq', rfl⟩
      simp only [hπ, hφ, mk_out_of_le hTP, DoubleCoset.eq]
      exact ⟨(Quotient.out q')⁻¹, P.inv_mem hq', 1, L.one_mem, by group⟩
    · intro hq
      obtain ⟨p, hp, l, hl, e⟩ := (@DoubleCoset.eq _ _ P L _ _).1 hq
      obtain ⟨t, ht, k, hk, ek⟩ := DoubleCoset.mk_out_eq_mul T Ly p⁻¹
      refine ⟨DoubleCoset.mk T Ly p⁻¹, ?_, ?_⟩
      · show Quotient.out (DoubleCoset.mk T Ly p⁻¹) ∈ P
        rw [ek]
        exact P.mul_mem (P.mul_mem (hTP ht) (P.inv_mem hp)) (hLyP k hk)
      · obtain ⟨_, l', hl', rfl⟩ := Subgroup.mem_inf.1 hk
        simp only [hφ]
        rw [ek, ← DoubleCoset.out_eq' q, DoubleCoset.eq]
        refine ⟨t⁻¹, T.inv_mem ht, l'⁻¹ * l⁻¹, L.mul_mem (L.inv_mem hl') (L.inv_mem hl), ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [e]
        group
  have hGA : ∑ᶠ q, G q = ∑ᶠ q ∈ A, G q := by
    rw [← finsum_mem_inter_support, Set.inter_eq_right.2 hsuppG, finsum_mem_support]
  rw [← h0, hGA, finsum_mem_congr rfl hGF,
    ← finsum_mem_image hinj, himg]
  refine (finsum_mem_eq_sum_of_inter_support_eq F ?_).symm
  ext q
  simp [Finset.mem_filter, Set.Finite.mem_toFinset]
  tauto

end GlobalTheory.OrbDesc
end
end

open MeasureTheory Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_sum_vanishes_of_parabolic_sums : ∀ (H : Type) [Group H] (T P L U : Subgroup H) (Ψ : H → ℂ), T ≤ P →
  (∀ s ∈ T, ∀ t ∈ T, s * t = t * s) → (∀ t ∈ T, ∀ x, Ψ (t * x) = Ψ x) → (∀ l ∈ L, ∀ x, Ψ (x * l) = Ψ x) →
  (∀ y : H, GlobalTheory.OrbDesc.dsum T (P ⊓ L.map (MulAut.conj y).toMonoidHom) U (fun x => if x ∈ P then Ψ (x * y) else 0) = 0) →
  GlobalTheory.OrbDesc.dsum T L U Ψ = 0 := by
  first | (exact @GlobalTheory.OrbDesc.dsum_eq_zero_of_par) | (exact GlobalTheory.OrbDesc.dsum_eq_zero_of_par) | (intros; apply GlobalTheory.OrbDesc.dsum_eq_zero_of_par  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetBlockConj
open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdTh
open GlobalTheory.SW hiding Level
open GlobalTheory.IndefiniteRowSideFullHecke.VacuumCharacterDeterminant (detPos detNeg vacChar)
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameEquiv.CompactMove

section Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} (X : Data E r)
  (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r)

theorem thR_of_perC (x x' : Frame X.Ψ r) (M : Matrix (Fin g) (Fin g) ℂ) (hM : IsUnit M.det)
    (h : ∀ u, (fun j => perC X x' u (idx j)) = M *ᵥ fun j => perC X x u (idx j))
    (φ : TF n g) (v : WR X n) :
    thR X bas idx φ x' v = (M.det⁻¹) ^ (n / 2) * thR X bas idx φ x v := by
  have hP : ∀ s, perMat X bas idx s x' = M * perMat X bas idx s x := by
    intro s
    ext i k
    exact congrFun (h fun (τ : X.Ψ) => Data.emb τ.1 (bas (Pi.single (s k) 1))) i
  have hH : hMat X bas idx x' = hMat X bas idx x * M⁻¹ := by
    rw [hMat, hP, Matrix.mul_inv_rev, hMat]
  have hT : tauMat X bas idx x' = tauMat X bas idx x := by
    rw [tauMat, hH, hP, Matrix.mul_assoc, ← Matrix.mul_assoc M⁻¹, nonsing_inv_mul _ hM, Matrix.one_mul, tauMat]
  have hI : imInv X bas idx x' = imInv X bas idx x := by rw [imInv, imInv, hT]
  have hz : ∀ b, hMat X bas idx x' *ᵥ zR X idx x' v b = hMat X bas idx x *ᵥ zR X idx x v b := by
    intro b
    have : zR X idx x' v b = M *ᵥ zR X idx x v b := h fun τ => v τ b
    rw [this, hH, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hM, Matrix.mul_one]
  simp only [thR, gaussR, GlobalTheory.Dict.hx, thA, hz, hT, hI]
  rw [hH, det_mul, det_nonsing_inv, Ring.inverse_eq_inv', mul_pow]
  ring

theorem thR_block (x x' : Frame X.Ψ r) (b : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (hb : ∀ τ, IsUnit (b τ).det)
    (hxb : ∀ τ, mat x' τ = mat x τ * b τ) (hc : ∀ τ, b τ * prFst r X.p0 = prFst r X.p0 * b τ)
    (φ : TF n g) (v : WR X n) :
    thR X bas idx φ x' v = (∏ τ, (((1 - prFst r X.p0) * b τ + prFst r X.p0).det /
      (prFst r X.p0 * b τ + (1 - prFst r X.p0)).det) ^ (n / 2)) * thR X bas idx φ x v := by
  classical
  set P := prFst r X.p0 with hP
  let N : X.Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ => P * (b τ)ᵀ + (1 - P) * (b τ)⁻¹
  have hN : ∀ τ, (N τ).det ≠ 0 ∧ (N τ).det = (P * b τ + (1 - P)).det / ((1 - P) * b τ + P).det := fun τ =>
    det_tr_inv_block P (1 - P) (b τ) (hb τ) (by abel) (by
      rw [hP, prFst, diagonal_mul_diagonal]; congr 1; funext a; split_ifs <;> simp) (hc τ) (by
      rw [hP, prFst, diagonal_transpose])
  let e : Fin g ≃ Fin r × X.Ψ := idx.trans (Equiv.prodComm _ _)
  have hdet : ((blockDiagonal N).submatrix e e).det = ∏ τ, (N τ).det := by
    rw [det_submatrix_equiv_self, det_blockDiagonal]
  have main := thR_of_perC X bas idx x x' ((blockDiagonal N).submatrix e e)
    (by rw [hdet]; exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun τ _ => (hN τ).1)) (fun u => by
      funext j
      have h1 : ((blockDiagonal N).submatrix e e *ᵥ fun j => perC X x u (idx j)) j =
          ∑ p : Fin r × X.Ψ, blockDiagonal N (e j) p * perC X x u p.swap := by
        rw [← e.sum_comp]
        rfl
      rw [h1, Fintype.sum_prod_type]
      refine (perC_block X x x' (idx j).1 (b _) (hb _) (hxb _) (hc _) u (idx j).2).trans ?_
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_eq_single (idx j).1]
      · exact congrArg (· * _) (blockDiagonal_apply_eq N (idx j).2 c (idx j).1).symm
      · intro τ _ hτ
        have : blockDiagonal N (e j) (c, τ) = 0 := blockDiagonal_apply_ne N (idx j).2 c hτ.symm
        rw [this, zero_mul]
      · simp) φ v
  rw [main, hdet, Finset.prod_pow, ← Finset.prod_inv_distrib]
  congr 2
  exact Finset.prod_congr rfl fun τ _ => by rw [(hN τ).2, inv_div]

end Classical

theorem det_block_conj {r : ℕ} (P m : Matrix (Fin r) (Fin r) ℂ) (hPP : P * P = P) (hP : Pᴴ = P)
    (hP' : P.map conj = P) (hc : m * P = P * m) (hm : mᴴ * m = 1) :
    (P * m.map conj + (1 - P)).det = (P * m + (1 - P)).det⁻¹ := by
  have h1 : (P * m + (1 - P))ᴴ * (P * m + (1 - P)) = 1 := by
    have a1 : mᴴ * (P * m) = P := by rw [← hc, ← Matrix.mul_assoc, hm, Matrix.one_mul]
    have a2 : ∀ y : Matrix (Fin r) (Fin r) ℂ, P * (P * y) = P * y := fun y => by rw [← Matrix.mul_assoc, hPP]
    simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hP,
      Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc, a1, a2, hPP]
    abel
  have h2 : P * m.map conj + (1 - P) = (starRingEnd ℂ).mapMatrix (P * m + (1 - P)) := by
    rw [map_add (f := _), map_mul, map_sub, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hP']
  have h3 := congrArg det h1
  rw [det_mul, det_conjTranspose, det_one] at h3
  rw [h2, ← RingHom.map_det]
  exact eq_inv_of_mul_eq_one_left h3

theorem blocks {r p : ℕ} (G B k : Matrix (Fin r) (Fin r) ℂ) (S : Matrix (Fin r) (Fin r) ℂ)
    (hS : S = (2 : ℂ) • prFst r p - 1) (hSS : S * S = 1) (hB : Bᴴ * G * B = S) (hk : kᴴ * G * k = G)
    (hc : k * (B * S * B⁻¹) = B * S * B⁻¹ * k) :
    ∃ m : Matrix (Fin r) (Fin r) ℂ, IsUnit (m.map conj).det ∧ k * B = B * m ∧
      m.map conj * prFst r p = prFst r p * m.map conj ∧
      ((1 - prFst r p) * m.map conj + prFst r p).det / (prFst r p * m.map conj + (1 - prFst r p)).det =
        detPos (B * S * B⁻¹) k * (detNeg (B * S * B⁻¹) k)⁻¹ := by
  have hu := GlobalTheory.Ker.ONBasis.isUnit_det hSS hB
  have hPP : prFst r p * prFst r p = prFst r p := by
    rw [prFst, diagonal_mul_diagonal]; congr 1; funext a; split_ifs <;> simp
  have hPc : (prFst r p).map conj = prFst r p := by
    ext a c
    simp only [prFst, map_apply, diagonal_apply]
    split_ifs <;> simp
  have hPH : (prFst r p)ᴴ = prFst r p := by
    rw [prFst, diagonal_conjTranspose]; congr 1; funext a; simp only [Pi.star_apply]; split_ifs <;> simp
  generalize prFst r p = P at *
  have e0 : B * S * B⁻¹ * B = B * S := by rw [Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]
  generalize B * S * B⁻¹ = s at *
  obtain ⟨h1, h2, h3⟩ := block_of_inv P B k (-s) hu (by rw [Matrix.neg_mul, e0, hS])
    (by rw [Matrix.neg_mul, ← Matrix.mul_assoc, ← hc, Matrix.mul_assoc, e0, hS, Matrix.mul_assoc])
  have hkB : k * B = B * (B⁻¹ * (k * B)) := (mul_nonsing_inv_cancel_left _ _ hu).symm
  generalize B⁻¹ * (k * B) = m at *
  have hmS : m * S = S * m := by
    rw [hS, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, h1, Matrix.mul_one, Matrix.one_mul]
  have hm1 : mᴴ * S * m = S := by
    calc mᴴ * S * m = (B * m)ᴴ * G * (B * m) := by
          rw [← hB, conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Bᴴ * (kᴴ * G * k) * B := by rw [← hkB, conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = S := by rw [hk, hB]
  have hm : mᴴ * m = 1 := by
    calc mᴴ * m = mᴴ * S * m * S := by
          rw [Matrix.mul_assoc, hmS, Matrix.mul_assoc, ← Matrix.mul_assoc S, hSS, Matrix.one_mul]
      _ = 1 := by rw [hm1, hSS]
  have d1 := det_block_conj P m hPP hPH hPc h1 hm
  have d2 := det_block_conj (1 - P) m
    (by rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hPP]; abel)
    (by rw [conjTranspose_sub, conjTranspose_one, hPH])
    (by
      change (starRingEnd ℂ).mapMatrix (1 - P) = _
      rw [map_sub, map_one, RingHom.mapMatrix_apply, hPc])
    (by rw [Matrix.mul_sub, Matrix.sub_mul, h1, Matrix.mul_one, Matrix.one_mul]) hm
  rw [sub_sub_cancel] at d2
  refine ⟨m, ?_, hkB, ?_, ?_⟩
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (Matrix.isUnit_det_of_left_inverse hm).map _
  · rw [← hPc, ← Matrix.map_mul, ← Matrix.map_mul, h1]
  · rw [d1, d2, ← h2, ← h3, detNeg, detPos, detPos]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_neg,
      Matrix.neg_mul, Matrix.mul_one, Matrix.one_mul, hc, sub_neg_eq_add, ← sub_eq_add_neg]
    rw [div_eq_mul_inv, inv_inv, mul_comm]

theorem Th_mvB (D : D7) (S T : HSp D) (C : GlobalTheory.Ker.Ctx S T) (B : C.Bas) (hB : C.IsB B) (k : GA D T)
    (_hk : k ∈ GinfC T)
    (hc : ∀ τ, compAt C.θ τ (Formalism.L2.Theta.mt T k) * C.sB B τ = C.sB B τ * compAt C.θ τ (Formalism.L2.Theta.mt T k))
    (φ : TF S.rank C.g) (hφ : GlobalTheory.SW.IsSB φ) :
    C.Th (C.xB (C.mvB k B)) φ = vacChar C.θ T (C.sB B) S.rank (fun _ => 0) k • C.Th (C.xB B) φ := by
  have hdom : ∀ A, C.IsB A → C.xB A ∈ C.X.dom := fun A hA =>
    GlobalTheory.Ker.ONBasis.mem_dom C.X (GlobalTheory.Ker.ONBasis.isONFr_xB C hA)
  have z1 := (GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ (hdom _ hB) φ hφ).1
  have z2 := (GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ (hdom _ (GlobalTheory.Ker.ONBasis.isB_mvB C hB k)) φ hφ).1
  obtain ⟨-, l1, l2⟩ := GlobalTheory.ThetaSpace.theta_space_laws D S T C
  refine (l1 _ _ z2.1 ((l2 _ z1.1).1 _)).2 fun w hw => ?_
  choose m m1 m2 m3 m4 using fun τ => blocks (p := C.X.p0) (gramAt D T τ) (B τ)
    (compAt C.θ τ (Formalism.L2.Theta.mt T k)) (sgnM C.X) (sgnM_eq C.X) (GlobalTheory.Ker.ONBasis.sgnM_sq C.X) (hB τ)
    (GlobalTheory.Ker.ONBasis.compAt_unitary C τ k) (hc τ)
  rw [z2.2 w hw, Pi.smul_apply, z1.2 w hw, smul_eq_mul,
    thR_block C.X C.bas C.idx (C.xB B) (C.xB (C.mvB k B)) (fun σ => (m (C.m.e.symm σ)).map conj)
      (fun σ => m1 _) (fun σ => ?_) (fun σ => m3 _)]
  · congr 1
    rw [← C.m.e.prod_comp, vacChar]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Equiv.symm_apply_apply, m4, zero_add, zero_sub, _root_.zpow_neg, zpow_natCast, zpow_natCast, mul_pow, inv_pow]
    rfl
  · obtain ⟨τ, rfl⟩ := C.m.e.surjective σ
    rw [GlobalTheory.Ker.ONBasis.mat_xB, GlobalTheory.Ker.ONBasis.mat_xB, Equiv.symm_apply_apply, ← Matrix.map_mul, ← m2]
    rfl

end GlobalTheory.FrameEquiv.CompactMove

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjCentralizerLeBlockDiagonalLevi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjCentralizerLeBlockDiagonalLevi
open MeasureTheory Matrix
open scoped Classical

noncomputable section
open Polynomial

namespace GlobalTheory.OrbDesc

theorem commute_aeval_of_commute {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {F f : Module.End K V} (h : Commute F f) (p : K[X]) : Commute F (aeval f p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _)]; exact hp.add_right hq
  | monomial n c =>
    rw [aeval_monomial]
    exact (Algebra.commute_algebraMap_right c F).mul_right (h.pow_right n)

theorem natDegree_pos_of_not_isUnit {K : Type} [Field K] {p : K[X]} (hp0 : p ≠ 0)
    (hp : ¬ IsUnit p) : 0 < p.natDegree := by
  by_contra h
  push_neg at h
  apply hp
  rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_eq_natDegree hp0]
  simp only [Nat.cast_eq_zero]
  omega

theorem exists_conj_cent_le_blockLevi : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (γ : GL ι K),
  (γ : Matrix ι ι K).charpoly.Separable → ¬ Irreducible (γ : Matrix ι ι K).charpoly →
  ∃ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a ∧ 0 < b ∧ ∃ c : GL ι K,
    GlobalTheory.BCT.twCent (MonoidHom.id (GL ι K)) (c⁻¹ * γ * c) ≤ GlobalTheory.OrbDesc.blockLevi e := by
  intro K _ ι _ _ _ γ hsep hirr
  set M : Matrix ι ι K := (γ : Matrix ι ι K) with hMdef
  have hχ0 : M.charpoly ≠ 0 := M.charpoly_monic.ne_zero
  have hχu : ¬ IsUnit M.charpoly := by
    intro hu
    have h1 := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [Matrix.charpoly_natDegree_eq_dim] at h1
    exact Fintype.card_ne_zero h1
  obtain ⟨p, q, hpq, hp, hq⟩ : ∃ p q, M.charpoly = p * q ∧ ¬ IsUnit p ∧ ¬ IsUnit q := by
    by_contra hc
    push_neg at hc
    exact hirr (irreducible_iff.mpr ⟨hχu, fun p q h => by
      by_contra h'
      push_neg at h'
      exact h'.2 (hc p q h h'.1)⟩)
  have hcop : IsCoprime p q := (hpq ▸ hsep).isCoprime
  have hp0 : p ≠ 0 := by rintro rfl; rw [zero_mul] at hpq; exact hχ0 hpq
  have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hpq; exact hχ0 hpq
  have hpd := natDegree_pos_of_not_isUnit hp0 hp
  have hqd := natDegree_pos_of_not_isUnit hq0 hq
  let f : Module.End K (ι → K) := Matrix.toLin' M
  have haev : ∀ r : K[X], aeval f r = Matrix.toLin' (aeval M r) := fun r =>
    aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := K) (n := ι)) M r
  have hχf : aeval f M.charpoly = 0 := by rw [haev, Matrix.aeval_self_charpoly, map_zero]
  set V₁ := LinearMap.ker (aeval f p) with hV₁
  set V₂ := LinearMap.ker (aeval f q) with hV₂
  have hc : IsCompl V₁ V₂ := ⟨Polynomial.disjoint_ker_aeval_of_isCoprime f hcop, by
    rw [codisjoint_iff, Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime f hcop, ← hpq, hχf,
      LinearMap.ker_zero]⟩
  have hcharf : LinearMap.charpoly f = M.charpoly := Matrix.charpoly_toLin' M
  have hdvd : M.charpoly ∣ minpoly K f := by
    have := GlobalTheory.UnitLemma.charpoly_dvd_minpoly_of_separable f (by rw [hcharf]; exact hsep)
    rwa [hcharf] at this
  have hV1 : V₁ ≠ ⊥ := by
    intro h
    have h2 : V₂ = ⊤ := by
      have := hc.sup_eq_top
      rwa [h, bot_sup_eq] at this
    have h3 : aeval f q = 0 := LinearMap.ker_eq_top.mp h2
    have h4 := Polynomial.natDegree_le_of_dvd (hdvd.trans (minpoly.dvd K f h3)) hq0
    rw [hpq, Polynomial.natDegree_mul hp0 hq0] at h4
    omega
  have hV2 : V₂ ≠ ⊥ := by
    intro h
    have h2 : V₁ = ⊤ := by
      have := hc.sup_eq_top
      rwa [h, sup_bot_eq] at this
    have h3 : aeval f p = 0 := LinearMap.ker_eq_top.mp h2
    have h4 := Polynomial.natDegree_le_of_dvd (hdvd.trans (minpoly.dvd K f h3)) hp0
    rw [hpq, Polynomial.natDegree_mul hp0 hq0] at h4
    omega
  let φ := Submodule.prodEquivOfIsCompl V₁ V₂ hc
  let b1 := Module.finBasis K V₁
  let b2 := Module.finBasis K V₂
  let b0 := (b1.prod b2).map φ
  let e : ι ≃ Fin (Module.finrank K V₁) ⊕ Fin (Module.finrank K V₂) :=
    (b0.indexEquiv (Pi.basisFun K ι)).symm
  let bb := b0.reindex e.symm
  have hbb : ∀ i, bb i = b0 (e i) := fun i => by
    simp [bb, Module.Basis.reindex_apply]
  have hbbr : ∀ v i, bb.repr v i = b0.repr v (e i) := fun v i => by
    simp [bb, Module.Basis.repr_reindex_apply]
  have hmem1 : ∀ k, b0 (Sum.inl k) ∈ V₁ := fun k => by
    simp [b0, φ, Submodule.coe_prodEquivOfIsCompl']
  have hmem2 : ∀ k, b0 (Sum.inr k) ∈ V₂ := fun k => by
    simp [b0, φ, Submodule.coe_prodEquivOfIsCompl']
  have hrep1 : ∀ v ∈ V₁, ∀ k, b0.repr v (Sum.inr k) = 0 := fun v hv k => by
    have : φ.symm v = (⟨v, hv⟩, 0) := Submodule.prodEquivOfIsCompl_symm_apply_left V₁ V₂ hc ⟨v, hv⟩
    simp [b0, Module.Basis.map_repr, this]
  have hrep2 : ∀ v ∈ V₂, ∀ k, b0.repr v (Sum.inl k) = 0 := fun v hv k => by
    have : φ.symm v = (0, ⟨v, hv⟩) := Submodule.prodEquivOfIsCompl_symm_apply_right V₁ V₂ hc ⟨v, hv⟩
    simp [b0, Module.Basis.map_repr, this]
  let std := Pi.basisFun K ι
  let c : GL ι K := ⟨std.toMatrix bb, bb.toMatrix std,
    Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩
  refine ⟨_, _, e, Module.finrank_pos_iff.mpr ?_, Module.finrank_pos_iff.mpr ?_, c, ?_⟩
  · exact Submodule.nontrivial_iff_ne_bot.mpr hV1
  · exact Submodule.nontrivial_iff_ne_bot.mpr hV2
  intro g hg
  have hg' : g * (c⁻¹ * γ * c) = (c⁻¹ * γ * c) * g := hg
  have hN : (c * g * c⁻¹) * γ = γ * (c * g * c⁻¹) := by
    calc (c * g * c⁻¹) * γ = c * (g * (c⁻¹ * γ * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * γ * c) * g) * c⁻¹ := by rw [hg']
      _ = γ * (c * g * c⁻¹) := by group
  let F : Module.End K (ι → K) := Matrix.toLin' ((c * g * c⁻¹ : GL ι K) : Matrix ι ι K)
  have hC : Commute F f := by
    show Matrix.toLin' ((c * g * c⁻¹ : GL ι K) : Matrix ι ι K) ∘ₗ Matrix.toLin' (γ : Matrix ι ι K)
      = Matrix.toLin' (γ : Matrix ι ι K) ∘ₗ Matrix.toLin' ((c * g * c⁻¹ : GL ι K) : Matrix ι ι K)
    rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, ← Units.val_mul, ← Units.val_mul, hN]
  have hF1 : ∀ v ∈ V₁, F v ∈ V₁ := fun v hv => by
    rw [hV₁, LinearMap.mem_ker] at hv ⊢
    have := LinearMap.congr_fun (commute_aeval_of_commute hC p).eq v
    simp only [Module.End.mul_apply, hv, map_zero] at this
    exact this.symm
  have hF2 : ∀ v ∈ V₂, F v ∈ V₂ := fun v hv => by
    rw [hV₂, LinearMap.mem_ker] at hv ⊢
    have := LinearMap.congr_fun (commute_aeval_of_commute hC q).eq v
    simp only [Module.End.mul_apply, hv, map_zero] at this
    exact this.symm
  have hg2 : g = c⁻¹ * (c * g * c⁻¹) * c := by group
  have hgm : (g : Matrix ι ι K) = bb.toMatrix std * ((c * g * c⁻¹ : GL ι K) : Matrix ι ι K) * std.toMatrix bb := by
    conv_lhs => rw [hg2]
    rfl
  have hgF : (g : Matrix ι ι K) = LinearMap.toMatrix bb bb F := by
    rw [hgm, ← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix bb std bb std F,
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  have hz : ∀ i j, side e i ≠ side e j → (g : Matrix ι ι K) i j = 0 := by
    intro i j hij
    rw [hgF, LinearMap.toMatrix_apply, hbb, hbbr]
    cases hi : e i with
    | inl k =>
      cases hj : e j with
      | inl k' => simp [side, hi, hj] at hij
      | inr k' => exact hrep2 _ (hF2 _ (hmem2 k')) k
    | inr k =>
      cases hj : e j with
      | inl k' => exact hrep1 _ (hF1 _ (hmem1 k')) k
      | inr k' => simp [side, hi, hj] at hij
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · show (g : Matrix ι ι K).BlockTriangular (side e)
    intro i j hlt
    apply hz
    intro heq
    rw [heq] at hlt
    exact lt_irrefl _ hlt
  · show (g : Matrix ι ι K).BlockTriangular (fun i => OrderDual.toDual (side e i))
    intro i j hlt
    apply hz
    intro heq
    simp only [] at hlt
    rw [heq] at hlt
    exact lt_irrefl _ hlt

end GlobalTheory.OrbDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjCentralizerLeBlockDiagonalLeviStatement
open MeasureTheory Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_centralizer_le_blockDiagonalLevi : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (γ : GL ι K),
  (γ : Matrix ι ι K).charpoly.Separable → ¬ Irreducible (γ : Matrix ι ι K).charpoly →
  ∃ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a ∧ 0 < b ∧ ∃ c : GL ι K,
    GlobalTheory.BCT.twCent (MonoidHom.id (GL ι K)) (c⁻¹ * γ * c) ≤ GlobalTheory.OrbDesc.blockLevi e := by
  first | (exact @GlobalTheory.OrbDesc.exists_conj_cent_le_blockLevi) | (exact GlobalTheory.OrbDesc.exists_conj_cent_le_blockLevi) | (intros; apply GlobalTheory.OrbDesc.exists_conj_cent_le_blockLevi  <;> assumption)
end
end
