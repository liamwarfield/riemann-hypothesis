module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PDeltaEx
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pDeltaEx :
    DeltaEx := by
  intro E _ _ _ bar hbar ω tr nm htr hnm hD M hcop t ht hgen hpos τ₀
  obtain ⟨hti, e, he, hez⟩ := hgen
  have hbω : bar ω = (tr : 𝓞 E) - ω := eq_sub_of_add_eq' htr
  have hnm' : ω * ((tr : 𝓞 E) - ω) = (nm : 𝓞 E) := by rw [← hbω]; exact hnm
  set u : 𝓞 E := 2 * ω - (tr : 𝓞 E) with hu
  set D : ℤ := tr ^ 2 - 4 * nm with hDdef
  have huu : u * u = (D : 𝓞 E) := by
    rw [hu, hDdef]; push_cast; linear_combination (-4 : 𝓞 E) * hnm'
  have huuE : (u : E) * (u : E) = (D : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) huu
    simpa using this
  have huE : (u : E) = 2 * (ω : E) - (tr : E) := by
    rw [hu]; norm_cast
  have h1 : (IsCMField.complexConj E) (ω : E) = (tr : E) - ω := by
    rw [← hbar ω, hbω]; norm_cast
  have hconj : (IsCMField.complexConj E) (u : E) = -(u : E) := by
    rw [huE, map_sub, map_mul, h1, map_intCast, map_ofNat]; ring
  have hτu : ∀ τ : E →+* ℂ, (τ u).re = 0 := by
    intro τ
    have h := IsCMField.complexEmbedding_complexConj E τ (u : E)
    rw [hconj, map_neg] at h
    have h2 := congrArg Complex.re h
    simp at h2
    linarith
  have hτt : ∀ τ : E →+* ℂ, (τ t).im = 0 := by
    intro τ
    have h := IsCMField.complexEmbedding_complexConj E τ t
    rw [ht] at h
    have h2 := congrArg Complex.im h
    simp at h2
    linarith
  have hu0 : (τ₀ u).im ≠ 0 := by
    intro h
    have h0 : τ₀ u = 0 := Complex.ext (hτu τ₀) h
    have h3 := congrArg τ₀ huuE
    rw [map_mul, h0, zero_mul, map_intCast] at h3
    have : D = 0 := by exact_mod_cast h3.symm
    linarith
  obtain ⟨c, hc, hcs⟩ : ∃ c : ℤ, c * c = 1 ∧ (c : ℝ) * (τ₀ u).im < 0 := by
    rcases lt_or_gt_of_ne hu0 with h | h
    · exact ⟨1, by norm_num, by simpa using h⟩
    · exact ⟨-1, by norm_num, by simpa using h⟩
  have hcE : (c : E) * (c : E) = 1 := by exact_mod_cast hc
  have hDabs : ((D.natAbs : ℕ) : E) = -((u : E) * (u : E)) := by
    rw [huuE]
    have : ((D.natAbs : ℕ) : ℤ) = -D := Int.ofNat_natAbs_of_nonpos hD.le
    have h2 := congrArg (fun k : ℤ => (k : E)) this
    simpa using h2
  refine ⟨(c : E) * t * u, ?_, ⟨?_, e * D.natAbs, ?_, ?_⟩, ?_⟩
  · rw [map_mul, map_mul, map_intCast, ht, hconj]; ring
  · intro x
    obtain ⟨m, hm⟩ := hti ((c : 𝓞 E) * u * x)
    refine ⟨m, ?_⟩
    have hcast : (((c : 𝓞 E) * u * x : 𝓞 E) : E) = (c : E) * u * x := by norm_cast
    rw [hcast] at hm
    rw [← hm]; congr 1; ring
  · have h2 : Int.gcd D (M : ℤ) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcop
    have h3 : Nat.Coprime D.natAbs M := by
      simpa [Int.gcd, Nat.Coprime] using h2
    exact Nat.Coprime.mul_left he h3
  · intro z hz
    obtain ⟨x, hx⟩ := hez z hz
    refine ⟨-(c : 𝓞 E) * u * x, ?_⟩
    have hcast : ((-(c : 𝓞 E) * u * x : 𝓞 E) : E) = -(c : E) * u * x := by norm_cast
    rw [hcast]
    push_cast
    linear_combination ((D.natAbs : ℕ) : E) * hx + (t * (x : E)) * hDabs + (t * (u : E) * (u : E) * (x : E)) * hcE
  · intro τ hτ
    have hτu' : τ u = τ₀ u := by
      rw [huE, map_sub, map_mul, map_sub, map_mul, hτ, map_intCast, map_intCast, map_ofNat, map_ofNat]
    rw [map_mul, map_mul, map_intCast, hτu']
    simp only [Complex.mul_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, hτt τ, hτu τ₀]
    nlinarith [mul_neg_of_pos_of_neg (hpos τ) hcs]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ExistsClose
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private lemma exists_close {E : Type} [Field E] [NumberField E] (c : InfinitePlace E → E) :
    ∃ x : E, ∀ v : InfinitePlace E, v (x - c v) < 1 / 2 := by
  have hd := InfinitePlace.denseRange_algebraMap_pi E
  obtain ⟨x, hx⟩ := hd.exists_dist_lt (fun v : InfinitePlace E => WithAbs.toAbs v.1 (c v))
    (by norm_num : (0:ℝ) < 1/2)
  refine ⟨x, fun v => ?_⟩
  have h1 := (dist_le_pi_dist _ _ v).trans_lt hx
  rw [dist_comm, dist_eq_norm] at h1
  exact h1

theorem UpperTheory.Gal.W2.Seed.pCEx :
    CEx := by
  intro E _ _ _ τ₀ M hM
  classical
  obtain ⟨x, hx⟩ := exists_close (E := E) (fun v => if v = InfinitePlace.mk τ₀ then -1 else 1)
  have hbound : ∀ τ : E →+* ℂ,
      |(τ x).re - (if InfinitePlace.mk τ = InfinitePlace.mk τ₀ then -1 else 1)| < 1 / 2 := by
    intro τ
    have h : ‖τ (x - (if InfinitePlace.mk τ = InfinitePlace.mk τ₀ then -1 else 1))‖ < 1 / 2 :=
      hx (InfinitePlace.mk τ)
    refine lt_of_le_of_lt ?_ h
    split_ifs with hτ
    · have := Complex.abs_re_le_norm (τ x - -1)
      simpa using this
    · have := Complex.abs_re_le_norm (τ x - 1)
      simpa using this
  have hxalg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy0, hyint⟩ := IsAlgebraic.exists_integral_multiple hxalg
  set z : E := y • (y • x) with hzdef
  have hz : IsIntegral ℤ z := hyint.smul y
  have hyR : (y : ℝ) ≠ 0 := by exact_mod_cast hy0
  have hy2 : 0 < (y : ℝ) ^ 2 := by positivity
  have hτz : ∀ τ : E →+* ℂ, (τ z).re = (y : ℝ) ^ 2 * (τ x).re := by
    intro τ
    simp [hzdef, zsmul_eq_mul]
    ring
  set w : E := z + IsCMField.complexConj E z with hwdef
  have hw : IsIntegral ℤ w := hz.add (map_isIntegral_int (IsCMField.complexConj E) hz)
  have hτw : ∀ τ : E →+* ℂ, (τ w).re = 2 * (τ z).re := by
    intro τ
    simp [hwdef, IsCMField.complexEmbedding_complexConj]
    ring
  have hneg : (τ₀ w).re < 0 := by
    have hb := hbound τ₀
    rw [if_pos rfl] at hb
    have := (abs_lt.mp hb).2
    rw [hτw, hτz]
    nlinarith
  have hpos : ∀ τ : E →+* ℂ, InfinitePlace.mk τ ≠ InfinitePlace.mk τ₀ → 0 < (τ w).re := by
    intro τ hτ
    have hb := hbound τ
    rw [if_neg hτ] at hb
    have := (abs_lt.mp hb).1
    rw [hτw, hτz]
    nlinarith
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / ((M : ℝ) * -(τ₀ w).re))
  have hKM : 1 < (M : ℝ) * K * -(τ₀ w).re := by
    have hd : 0 < (M : ℝ) * -(τ₀ w).re := by nlinarith
    rw [div_lt_iff₀ hd] at hK
    nlinarith
  let wO : 𝓞 E := ⟨w, (mem_integralClosure_iff ℤ E).mpr hw⟩
  have hcoe : (((1 : 𝓞 E) + (M : 𝓞 E) * ((K : 𝓞 E) * wO) : 𝓞 E) : E) = 1 + (M : E) * ((K : E) * w) := by
    push_cast
    rfl
  have hre : ∀ τ : E →+* ℂ, (τ (1 + (M : E) * ((K : E) * w))).re = 1 + (M : ℝ) * K * (τ w).re := by
    intro τ
    simp
    ring
  refine ⟨1 + (M : 𝓞 E) * ((K : 𝓞 E) * wO), ?_, ?_, ?_, (K : 𝓞 E) * wO, rfl⟩
  · rw [hcoe]
    simp [hwdef, add_comm]
  · rw [hcoe, hre]
    linarith
  · intro τ hτ
    rw [hcoe, hre]
    have := hpos τ hτ
    have : 0 ≤ (M : ℝ) * K * (τ w).re := by positivity
    linarith
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCodiffUnit
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pCodiffUnit :
    UnitMod → CodiffUnit := by
  intro hU E _ _ M hMpos y t hy ht hloc
  obtain ⟨_, e, he, hye⟩ := hy
  by_cases hM1 : M = 1
  · refine ⟨ht, 0, by simp [hM1], fun z _ => ⟨0, by simp⟩⟩
  let A : Ideal (𝓞 E) :=
    { carrier := {a | ∀ z : E, InCodiff z → ∃ x : 𝓞 E, (a : E) * z = t * x}
      add_mem' := by
        intro a b ha hb z hz
        obtain ⟨x1, h1⟩ := ha z hz
        obtain ⟨x2, h2⟩ := hb z hz
        exact ⟨x1 + x2, by push_cast; rw [add_mul, h1, h2, mul_add]⟩
      zero_mem' := by
        intro z _
        exact ⟨0, by simp⟩
      smul_mem' := by
        intro c a ha z hz
        obtain ⟨x, hx⟩ := ha z hz
        refine ⟨c * x, ?_⟩
        simp only [smul_eq_mul]
        push_cast
        rw [mul_assoc, hx]
        ring }
  have hA : ∀ a : 𝓞 E, a ∈ A → ∀ z : E, InCodiff z → ∃ x : 𝓞 E, (a : E) * z = t * x :=
    fun a ha => ha
  have htop : A ⊔ Ideal.span {((M : ℕ) : 𝓞 E)} = ⊤ := by
    by_contra hne
    obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hne
    have hMP : ((M : ℕ) : 𝓞 E) ∈ P :=
      hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    obtain ⟨s, u, _, huP, hsu⟩ := hloc P hPmax hMP
    have heP : ((e : ℕ) : 𝓞 E) ∉ P := by
      intro heP
      obtain ⟨p, q, hpq⟩ := Nat.isCoprime_iff_coprime.mpr he
      have h1 : ((p : 𝓞 E) * ((e : ℕ) : 𝓞 E) + (q : 𝓞 E) * ((M : ℕ) : 𝓞 E)) = 1 := by
        have := congrArg (fun n : ℤ => (n : 𝓞 E)) hpq
        push_cast at this
        exact this
      apply hPmax.ne_top
      rw [Ideal.eq_top_iff_one, ← h1]
      exact P.add_mem (P.mul_mem_left _ heP) (P.mul_mem_left _ hMP)
    have hue : u * ((e : ℕ) : 𝓞 E) ∉ P := by
      intro hmem
      rcases hPmax.isPrime.mem_or_mem hmem with h | h
      · exact huP h
      · exact heP h
    apply hue
    apply hle
    apply Ideal.mem_sup_left
    intro z hz
    obtain ⟨x, hx⟩ := hye z hz
    refine ⟨s * x, ?_⟩
    push_cast
    rw [mul_assoc, hx, ← mul_assoc, ← hsu]
    ring
  have hone : (1 : 𝓞 E) ∈ A ⊔ Ideal.span {((M : ℕ) : 𝓞 E)} := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨a, haA, m, hm, ham⟩ := Submodule.mem_sup.mp hone
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hm
  by_cases ha0 : a = 0
  · exfalso
    apply hM1
    have hunit : IsUnit ((M : ℕ) : 𝓞 E) :=
      isUnit_iff_exists_inv.mpr ⟨b, by rw [ha0, zero_add] at ham; rw [mul_comm]; exact ham⟩
    have hspan : Ideal.span {((M : ℕ) : 𝓞 E)} = ⊤ := Ideal.span_singleton_eq_top.mpr hunit
    have hn := Ideal.absNorm_span_natCast (S := 𝓞 E) M
    rw [hspan, Ideal.absNorm_top] at hn
    have hpos : Module.finrank ℤ (𝓞 E) ≠ 0 := Module.finrank_pos.ne'
    rcases Nat.pow_eq_one.mp hn.symm with h | h
    · exact h
    · exact absurd h hpos
  obtain ⟨e', he', c', hc'⟩ := hU E M a (-b) ha0 (by linear_combination ham)
  refine ⟨ht, e', he', fun z hz => ?_⟩
  obtain ⟨x, hx⟩ := hA a haA z hz
  refine ⟨c' * x, ?_⟩
  have hcoe : ((e' : ℕ) : E) = (a : E) * (c' : E) := by
    have := congrArg (fun w : 𝓞 E => (w : E)) hc'
    push_cast at this
    exact this.symm
  rw [hcoe, mul_comm (a : E), mul_assoc, hx]
  push_cast
  ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRepAdj
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pRepAdj :
    RepAdj := by
  intro E _ _ _ A n rep hrep x a b
  obtain ⟨β, h1, h2⟩ := hrep
  have key : ∀ z w, LinearMap.BilinForm.baseChange ℚ (A.EF n) z w =
      Algebra.trace ℚ E (A.δ * ∑ i, (A.hd n i : E) * β z i * IsCMField.complexConj E (β w i)) := by
    have hσq : ∀ (q : ℚ) (b : E), IsCMField.complexConj E (q • b) = q • IsCMField.complexConj E b := by
      intro q b
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      simp
    have hEF : ∀ v u : Fin n → 𝓞 E, ((A.EF n v u : ℤ) : ℚ) =
        Algebra.trace ℚ E (A.δ * ∑ i, (A.hd n i : E) * v i * IsCMField.complexConj E (u i)) := by
      intro v u
      simp only [Arith.EF, LinearMap.mk₂_apply, A.trd_spec]
      push_cast
      simp only [A.bar_eq]
    intro z w
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp [ha, hb, add_mul, Finset.sum_add_distrib, mul_add]
    | tmul q v =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp [ha, hb, mul_add, Finset.sum_add_distrib]
      | tmul r u =>
        rw [LinearMap.BilinForm.baseChange_tmul]
        have e1 : q ⊗ₜ[ℤ] v = q • ((1:ℚ) ⊗ₜ[ℤ] v) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        have e2 : r ⊗ₜ[ℤ] u = r • ((1:ℚ) ⊗ₜ[ℤ] u) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [e1, e2, map_smul, map_smul]
        simp only [Pi.smul_apply, h1, hσq]
        have hS : ∑ x, (A.hd n x : E) * q • (v x : E) * r • IsCMField.complexConj E (u x : E) =
            (q * r) • ∑ x, (A.hd n x : E) * v x * IsCMField.complexConj E (u x : E) := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [Algebra.smul_def, map_mul]
          ring
        rw [hS, mul_smul_comm, map_smul, ← hEF, zsmul_eq_mul, smul_eq_mul]
        ring
  have hreal : ∀ i, IsCMField.complexConj E (A.hd n i : E) = A.hd n i := by
    intro i
    have hc : IsCMField.complexConj E (A.c : E) = A.c := by
      rw [← A.bar_eq, A.c_real]
    simp only [Arith.hd, Arith.dg]
    split_ifs <;> simp [hc]
  have hc0 : (A.c : E) ≠ 0 := by
    intro h
    have := A.c_neg
    rw [h, map_zero] at this
    simp at this
  have hne : ∀ i, (A.hd n i : E) ≠ 0 := by
    intro i
    simp only [Arith.hd, Arith.dg]
    split_ifs <;> simp [hc0]
  rw [key, key, h2, h2]
  congr 2
  generalize β a = p
  generalize β b = s
  have hD : ∀ d : Fin n → E, (∀ m, d m ≠ 0) → (diagonal d)⁻¹ = diagonal (fun m => (d m)⁻¹) := by
    intro d hd
    apply Matrix.inv_eq_left_inv
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext m
    exact inv_mul_cancel₀ (hd m)
  have hx : ∀ j, (MulOpposite.unop ((hermStar (A.H n) (by
      simp only [Arith.H, Matrix.det_diagonal]
      exact Finset.prod_ne_zero_iff.mpr fun i _ => hne i)) x) *ᵥ s) j =
      (A.hd n j : E)⁻¹ * ∑ k, IsCMField.complexConj E (x k j) * A.hd n k * s k := by
    intro j
    simp only [hermStar, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op, Arith.H]
    rw [Matrix.diagonal_map (map_zero _)]
    simp only [Function.comp_def, RingHom.coe_coe, hreal]
    rw [hD _ hne, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
    rw [show ∀ d : Fin n → E, diagonal d *ᵥ s = fun m => d m * s m from fun d => funext (Matrix.mulVec_diagonal d s)]
    simp only [Matrix.mulVec, dotProduct, transpose_apply, map_apply, RingHom.coe_coe]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp only [hx]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, map_inv₀, map_sum, hreal, IsCMField.complexConj_apply_apply, Matrix.mulVec, dotProduct]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  have := hne j
  field_simp
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PFormOKSt
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private theorem trace_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (z : E) :
    Algebra.trace ℚ E (IsCMField.complexConj E z) = Algebra.trace ℚ E z :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) z

private theorem hd_bar {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (i : Fin n) :
    A.bar (A.hd n i) = A.hd n i := by
  unfold Arith.hd Arith.dg
  split_ifs <;> simp [A.c_real]

private theorem hd_ne {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (i : Fin n) :
    ((A.hd n i : 𝓞 E) : E) ≠ 0 := by
  have := A.c_ne
  unfold Arith.hd Arith.dg
  split_ifs <;> simp [this]

private theorem delta_ne {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) : A.δ ≠ 0 := by
  intro h
  have := A.δ_sign A.τ₀ rfl
  simp [h] at this

private theorem alternatingMap_sub_base_eq_alternating_sum_removeNth {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ)
    (x : Fin n → 𝓞 E) : A.EF n x x = 0 := by
  rw [Arith.EF_apply]
  set s : 𝓞 E := ∑ i, A.hd n i * x i * A.bar (x i) with hs
  have hbs : A.bar s = s := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hs, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, hd_bar, A.bar_bar]
    ring
  have hc : IsCMField.complexConj E ((s : 𝓞 E) : E) = (s : E) := by
    rw [← A.bar_eq, hbs]
  have h1 : Algebra.trace ℚ E (A.δ * (s : E)) = - Algebra.trace ℚ E (A.δ * (s : E)) := by
    conv_lhs => rw [← trace_cj, map_mul, A.δ_im, hc, neg_mul, map_neg]
  have h2 : ((A.trd s : ℤ) : ℚ) = 0 := by
    rw [A.trd_spec]
    linarith
  exact_mod_cast h2

private theorem laurent_adjoin_eq_of_image_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) :
    Function.Injective (A.EF n) := by
  refine (injective_iff_map_eq_zero (A.EF n)).2 fun x hx => ?_
  funext i
  by_contra hne
  have hxi : ((x i : 𝓞 E) : E) ≠ 0 := by
    intro h
    exact hne (RingOfIntegers.coe_eq_zero_iff.1 h)
  have hw : A.δ * ((A.hd n i : 𝓞 E) : E) * (x i : E) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (delta_ne A) (hd_ne A n i)) hxi
  have hint : ∀ b : 𝓞 E, Algebra.trace ℚ E (A.δ * ((A.hd n i : 𝓞 E) : E) * (x i : E) * (b : E)) = 0 := by
    intro b
    have h0 : A.EF n x (Pi.single i (A.bar b)) = 0 := by rw [hx]; rfl
    rw [Arith.EF_apply] at h0
    have h1 : (∑ j, A.hd n j * x j * A.bar ((Pi.single i (A.bar b) : Fin n → 𝓞 E) j)) =
        A.hd n i * x i * b := by
      rw [Finset.sum_eq_single i]
      · simp [A.bar_bar]
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj]
      · simp
    rw [h1] at h0
    have h2 := A.trd_spec (A.hd n i * x i * b)
    rw [h0] at h2
    simp only [Int.cast_zero] at h2
    rw [h2]
    congr 1
    push_cast
    ring
  obtain ⟨b, hb⟩ : ∃ b : E, Algebra.trace ℚ E (A.δ * ((A.hd n i : 𝓞 E) : E) * (x i : E) * b) ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hw ((traceForm_nondegenerate ℚ E).1 _ fun b => by simpa [Algebra.traceForm_apply] using hall b)
  obtain ⟨m, hm, hy⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic b))
  obtain ⟨c, hc⟩ : ∃ c : 𝓞 E, (c : E) = (m : ℚ) • b := by
    refine ⟨⟨m • b, hy⟩, ?_⟩
    show m • b = (m : ℚ) • b
    rw [zsmul_eq_mul, Algebra.smul_def]
    simp
  have h3 := hint c
  rw [hc, mul_smul_comm, map_smul, smul_eq_mul] at h3
  rcases mul_eq_zero.1 h3 with h5 | h5
  · exact hm (by exact_mod_cast h5)
  · exact hb h5

theorem UpperTheory.Gal.W2.Seed.pFormOKSt :
    FormOKSt := by
  intro E _ _ _ A n
  refine ⟨alternatingMap_sub_base_eq_alternating_sum_removeNth A n, laurent_adjoin_eq_of_image_eq A n, fun b x y => ?_⟩
  rw [Arith.EF_apply, Arith.EF_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, A.bar_bar]
  ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PIdemEx
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private lemma crtPrimes (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime) (f : ℕ → ℤ) :
    ∃ R : ℤ, ∀ q ∈ T, (q : ℤ) ∣ R - f q := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a T ha ih =>
    obtain ⟨R₀, hR₀⟩ := ih (fun q hq => hT q (Finset.mem_insert_of_mem hq))
    have hap : a.Prime := hT a (Finset.mem_insert_self a T)
    have hcop : IsCoprime (a : ℤ) (∏ q ∈ T, (q : ℤ)) := by
      refine IsCoprime.prod_right (fun q hq => ?_)
      have hqp : q.Prime := hT q (Finset.mem_insert_of_mem hq)
      have hne : a ≠ q := fun h => ha (h ▸ hq)
      exact Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hap hqp).mpr hne)
    obtain ⟨u, v, huv⟩ := hcop
    refine ⟨R₀ + v * (∏ q ∈ T, (q : ℤ)) * (f a - R₀), fun q hq => ?_⟩
    rcases Finset.mem_insert.mp hq with rfl | hq'
    · refine ⟨-u * (f q - R₀), ?_⟩
      linear_combination (f q - R₀) * huv
    · have h1 : (q : ℤ) ∣ ∏ q ∈ T, (q : ℤ) := Finset.dvd_prod_of_mem (fun q : ℕ => (q : ℤ)) hq'
      obtain ⟨k, hk⟩ := h1
      obtain ⟨l, hl⟩ := hR₀ q hq'
      refine ⟨l + v * k * (f a - R₀), ?_⟩
      rw [hk]
      linear_combination hl

private lemma primeDvdOfMem {A : Type} [CommRing A] (P : Ideal A) (hP : P.IsPrime) (M : ℕ) (hM : 0 < M)
    (h : (M : A) ∈ P) : ∃ q : ℕ, q.Prime ∧ q ∣ M ∧ (q : A) ∈ P := by
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    by_cases h1 : M = 1
    · subst h1
      exact absurd ((Ideal.eq_top_iff_one P).mpr (by simpa using h)) hP.ne_top
    · have hq : M.minFac.Prime := Nat.minFac_prime h1
      obtain ⟨m, hm⟩ := Nat.minFac_dvd M
      have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [h0] at hm; omega
        · exact h0
      have hlt : m < M := by
        have := hq.two_le
        rw [hm]
        nlinarith
      have hmem : ((M.minFac : A)) * (m : A) ∈ P := by
        have : (M : A) = ((M.minFac : A)) * (m : A) := by
          conv_lhs => rw [hm]
          push_cast
          rfl
        rwa [this] at h
      rcases hP.mem_or_mem hmem with h2 | h2
      · exact ⟨M.minFac, hq, Nat.minFac_dvd M, h2⟩
      · obtain ⟨q, hq', hqm, hqP⟩ := ih m hlt hm0 h2
        exact ⟨q, hq', hqm.trans ⟨M.minFac, by rw [mul_comm]; exact hm⟩, hqP⟩

private lemma localInv (q : ℕ) (hq : q.Prime) (tr nm r : ℤ) (hD : ¬ (q : ℤ) ∣ tr ^ 2 - 4 * nm)
    (hr : (q : ℤ) ∣ r ^ 2 - tr * r + nm) : ∃ s : ℤ, (q : ℤ) ∣ s * (tr - 2 * r) - 1 := by
  have hpr : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hnd : ¬ (q : ℤ) ∣ tr - 2 * r := by
    intro h
    apply hD
    have h2 : (q : ℤ) ∣ (tr - 2 * r) ^ 2 - 4 * (r ^ 2 - tr * r + nm) :=
      dvd_sub (dvd_pow h two_ne_zero) (Dvd.dvd.mul_left hr 4)
    have h3 : (tr - 2 * r) ^ 2 - 4 * (r ^ 2 - tr * r + nm) = tr ^ 2 - 4 * nm := by ring
    rwa [h3] at h2
  have hco : IsCoprime (q : ℤ) (tr - 2 * r) := (Prime.coprime_iff_not_dvd hpr).mpr hnd
  obtain ⟨a, b, hab⟩ := hco
  refine ⟨b, -a, ?_⟩
  linear_combination hab

theorem UpperTheory.Gal.W2.Seed.pIdemEx :
    IdemEx := by
  intro E _ _ bar ω tr nm _ hsum hprod M hM hloc
  have hex : ∀ q : ℕ, q.Prime → q ∣ M → ∃ r s : ℤ, (q : ℤ) ∣ r ^ 2 - tr * r + nm ∧
      (q : ℤ) ∣ s * (tr - 2 * r) - 1 := by
    intro q hq hqM
    obtain ⟨hD, r, hr⟩ := hloc q hq hqM
    obtain ⟨s, hs⟩ := localInv q hq tr nm r hD hr
    exact ⟨r, s, hr, hs⟩
  choose! r s hr hs using hex
  have hT : ∀ q ∈ M.primeFactors, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors hq
  obtain ⟨R, hR⟩ := crtPrimes M.primeFactors hT r
  obtain ⟨S, hS⟩ := crtPrimes M.primeFactors hT s
  have hbar : bar ω = (tr : 𝓞 E) - ω := by rw [← hsum]; ring
  refine ⟨(S : 𝓞 E) * (ω - (R : 𝓞 E)), fun P hP hMP => ?_⟩
  obtain ⟨q, hq, hqM, hqP⟩ := primeDvdOfMem P hP.isPrime M hM hMP
  have hqf : q ∈ M.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqM, hM.ne'⟩
  have castMem : ∀ z : ℤ, (q : ℤ) ∣ z → (z : 𝓞 E) ∈ P := by
    rintro z ⟨k, rfl⟩
    push_cast
    exact Ideal.mul_mem_right _ _ hqP
  obtain ⟨a, ha⟩ := hR q hqf
  obtain ⟨b, hb⟩ := hS q hqf
  obtain ⟨c, hc⟩ := hr q hq hqM
  obtain ⟨e, he⟩ := hs q hq hqM
  have h1 : (q : ℤ) ∣ S * (tr - 2 * R) - 1 := by
    refine ⟨b * (tr - 2 * R) + e - 2 * s q * a, ?_⟩
    linear_combination (tr - 2 * R) * hb + he - 2 * s q * ha
  have h2 : (q : ℤ) ∣ R ^ 2 - tr * R + nm := by
    refine ⟨a * (R + r q - tr) + c, ?_⟩
    linear_combination (R + r q - tr) * ha + hc
  have hbe : bar ((S : 𝓞 E) * (ω - (R : 𝓞 E))) = (S : 𝓞 E) * ((tr : 𝓞 E) - ω - (R : 𝓞 E)) := by
    rw [map_mul, map_sub, map_intCast, map_intCast, hbar]
  rw [hbe]
  constructor
  · have := castMem _ h1
    push_cast at this
    convert this using 1
    ring
  · have := Ideal.mul_mem_left P ((S : 𝓞 E) ^ 2) (castMem _ h2)
    push_cast at this
    convert this using 1
    have hp : ω * ((tr : 𝓞 E) - ω) = (nm : 𝓞 E) := by rw [← hbar]; exact hprod
    linear_combination (S : 𝓞 E) ^ 2 * hp
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PQuadEx
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed.QuadraticExtensions

private lemma sq_in_Zq (q : ℕ) [Fact q.Prime] (d g d0 : ℕ) (hg : 0 < g) (hd : g ^ 2 * d0 = d)
    (h : IsSquare (-(d : ℚ_[q]))) : ∃ z : ℤ_[q], z ^ 2 = -(d0 : ℤ_[q]) := by
  obtain ⟨y, hy⟩ := h
  have hg0 : (g : ℚ_[q]) ≠ 0 := by exact_mod_cast hg.ne'
  have hd' : (d : ℚ_[q]) = (g : ℚ_[q]) ^ 2 * d0 := by rw [← hd]; push_cast; ring
  rw [hd'] at hy
  have hx : (y / g) ^ 2 = -(d0 : ℚ_[q]) := by
    rw [div_pow, div_eq_iff (pow_ne_zero 2 hg0)]
    linear_combination -hy
  have hxn : ‖y / (g : ℚ_[q])‖ ≤ 1 := by
    have h1 : ‖y / (g : ℚ_[q])‖ ^ 2 ≤ 1 := by
      rw [← norm_pow, hx, norm_neg]
      have : ‖((d0 : ℤ_[q]) : ℚ_[q])‖ ≤ 1 := PadicInt.norm_le_one _
      simpa using this
    by_contra hc
    push_neg at hc
    nlinarith
  let z : ℤ_[q] := ⟨y / g, hxn⟩
  have hzc : (z : ℚ_[q]) = y / g := rfl
  refine ⟨z, ?_⟩
  have hc : ((z ^ 2 : ℤ_[q]) : ℚ_[q]) = ((-(d0 : ℤ_[q]) : ℤ_[q]) : ℚ_[q]) := by
    push_cast
    rw [hzc]
    exact hx
  first
    | exact PadicInt.ext hc
    | exact Subtype.ext hc
    | exact PadicInt.coe_injective hc

private lemma not_dvd (q : ℕ) [hq : Fact q.Prime] (d0 : ℕ) (hsq : Squarefree d0) (z : ℤ_[q])
    (hz : z ^ 2 = -(d0 : ℤ_[q])) : ¬ q ∣ d0 := by
  intro hdvd
  have hnorm : ‖z‖ ^ 2 = ‖((d0 : ℤ) : ℤ_[q])‖ := by
    rw [← norm_pow, hz, norm_neg, Int.cast_natCast]
  have hd1 : ‖((d0 : ℤ) : ℤ_[q])‖ < 1 :=
    (PadicInt.norm_int_lt_one_iff_dvd _).mpr (by exact_mod_cast hdvd)
  have hz1 : ‖z‖ < 1 := by
    by_contra hc
    push_neg at hc
    nlinarith [norm_nonneg z]
  obtain ⟨w, rfl⟩ := (PadicInt.norm_lt_one_iff_dvd z).mp hz1
  have hle : ‖((d0 : ℤ) : ℤ_[q])‖ ≤ (q : ℝ) ^ (-(2 : ℕ) : ℤ) := by
    rw [← hnorm, norm_mul, PadicInt.norm_p, mul_pow]
    have hw := PadicInt.norm_le_one w
    have he : (q : ℝ) ^ (-(2 : ℕ) : ℤ) = ((q : ℝ)⁻¹) ^ 2 := by
      rw [_root_.zpow_neg, zpow_natCast, inv_pow]
    rw [he]
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (norm_nonneg w) hw)
  have h2 := PadicInt.norm_int_le_pow_iff_dvd.mp hle
  have h3 : q ^ 2 ∣ d0 := by exact_mod_cast h2
  rw [sq] at h3
  exact (Nat.Prime.one_lt hq.out).ne' (Nat.isUnit_iff.mp (hsq q h3))

private lemma root_mod (q : ℕ) [Fact q.Prime] (d0 : ℕ) (z : ℤ_[q])
    (hz : z ^ 2 = -(d0 : ℤ_[q])) : ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 + d0 := by
  refine ⟨((PadicInt.toZMod z).val : ℤ), ?_⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).1
  have h := congrArg (PadicInt.toZMod (p := q)) hz
  simp only [map_pow, map_neg, map_natCast] at h
  push_cast
  rw [ZMod.natCast_zmod_val, h]
  ring

private lemma two_case [Fact (Nat.Prime 2)] (d0 : ℕ) (hodd : ¬ 2 ∣ d0) (z : ℤ_[2])
    (hz : z ^ 2 = -(d0 : ℤ_[2])) : d0 % 8 = 7 := by
  have h := congrArg (PadicInt.toZModPow 3 : ℤ_[2] →+* ZMod (2 ^ 3)) hz
  rw [map_pow, map_neg, map_natCast] at h
  generalize (PadicInt.toZModPow 3 : ℤ_[2] →+* ZMod (2 ^ 3)) z = a at h
  revert a
  show ∀ a : ZMod 8, a ^ 2 = -((d0 : ZMod 8)) → d0 % 8 = 7
  rw [← ZMod.natCast_mod d0 8]
  have hlt := Nat.mod_lt d0 (by norm_num : 8 > 0)
  have hodd : d0 % 2 = 1 := by omega
  interval_cases h8 : d0 % 8
  all_goals first | omega | decide

private lemma not_dvd_four (q : ℕ) (hq : q.Prime) (h2 : q ≠ 2) : ¬ (q : ℤ) ∣ 4 := by
  intro h
  have h' : q ∣ 2 ^ 2 := by exact_mod_cast h
  exact h2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h'))

private lemma root_odd (q : ℕ) (hq : q.Prime) (h2 : q ≠ 2) (d0 m : ℕ) (hm : d0 + 1 = 4 * m) (r0 : ℤ)
    (hr : (q : ℤ) ∣ r0 ^ 2 + d0) : ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 - 1 * r + m := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, q + 1 = 2 * k := by
    rcases hq.eq_two_or_odd' with h | ⟨j, hj⟩
    · exact absurd h h2
    · exact ⟨j + 1, by omega⟩
  refine ⟨(r0 + 1) * k, ?_⟩
  have hpz : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have h4 : (q : ℤ) ∣ 4 * (((r0 + 1) * k) ^ 2 - 1 * ((r0 + 1) * k) + m) := by
    obtain ⟨c, hc⟩ := hr
    have hk' : (2 * k : ℤ) = q + 1 := by exact_mod_cast hk.symm
    have hm' : (4 * m : ℤ) = d0 + 1 := by exact_mod_cast hm.symm
    refine ⟨c + (r0 + 1) * (2 * r0 + (r0 + 1) * q), ?_⟩
    linear_combination ((r0 + 1) ^ 2 * (2 * (k : ℤ) + q + 1) - 2 * (r0 + 1)) * hk' + hm' + hc
  rcases hpz.dvd_or_dvd h4 with h | h
  · exact absurd h (not_dvd_four q hq h2)
  · exact h

end UpperTheory.Gal.W2.Seed.QuadraticExtensions

open UpperTheory.Gal.W2.Seed.QuadraticExtensions in
theorem UpperTheory.Gal.W2.Seed.pQuadEx :
    QuadEx := by
  intro d hd
  obtain ⟨d0, g, hgd, hsq⟩ := Nat.sq_mul_squarefree d
  have hg : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h | h
    · subst h; simp at hgd; omega
    · exact h
  have hd0 : 0 < d0 := by
    rcases Nat.eq_zero_or_pos d0 with h | h
    · subst h; simp at hgd; omega
    · exact h
  have hgq : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  have hdq : (d : ℚ) = (g : ℚ) ^ 2 * d0 := by rw [← hgd]; push_cast; ring
  by_cases h43 : d0 % 4 = 3
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, d0 + 1 = 4 * m := ⟨(d0 + 1) / 4, by omega⟩
    have hdisc : (1 : ℤ) ^ 2 - 4 * (m : ℤ) = -(d0 : ℤ) := by
      have : ((d0 : ℤ) + 1) = 4 * (m : ℤ) := by exact_mod_cast hm
      linarith
    refine ⟨1, m, 1 / (g : ℚ), ?_, ?_, ?_⟩
    · rw [hdisc]; omega
    · rw [hdisc, hdq]; push_cast; field_simp
    · intro q _ hsqr
      obtain ⟨z, hz⟩ := sq_in_Zq q d g d0 hg hgd hsqr
      have hnd := not_dvd q d0 hsq z hz
      refine ⟨?_, ?_⟩
      · rw [hdisc, dvd_neg]
        intro h
        exact hnd (by exact_mod_cast h)
      · by_cases hq2 : q = 2
        · subst hq2
          have h7 := two_case d0 hnd z hz
          refine ⟨0, ?_⟩
          have : (m : ℤ) % 2 = 0 := by omega
          push_cast
          omega
        · obtain ⟨r0, hr0⟩ := root_mod q d0 z hz
          exact root_odd q (Fact.out) hq2 d0 m hm r0 hr0
  · refine ⟨0, d0, 2 / (g : ℚ), ?_, ?_, ?_⟩
    · omega
    · rw [hdq]; push_cast; field_simp; ring
    · intro q _ hsqr
      obtain ⟨z, hz⟩ := sq_in_Zq q d g d0 hg hgd hsqr
      have hnd := not_dvd q d0 hsq z hz
      refine ⟨?_, ?_⟩
      · by_cases hq2 : q = 2
        · subst hq2
          have h7 := two_case d0 hnd z hz
          omega
        · have hq : q.Prime := Fact.out
          have hpz : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
          intro h
          have h' : (q : ℤ) ∣ 4 * (d0 : ℤ) := by
            have : (0 : ℤ) ^ 2 - 4 * (d0 : ℤ) = -(4 * (d0 : ℤ)) := by ring
            rw [this, dvd_neg] at h
            exact h
          rcases hpz.dvd_or_dvd h' with h4 | h4
          · exact not_dvd_four q hq hq2 h4
          · exact hnd (by exact_mod_cast h4)
      · obtain ⟨r0, hr0⟩ := root_mod q d0 z hz
        exact ⟨r0, by simpa using hr0⟩
end
