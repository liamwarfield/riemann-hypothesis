module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NormOneApproximationAtLevelPrimes
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryMatrixEqProdQuasiReflections
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryGroupWeakApproximationAtPrimes

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitaryCorrectionCongruentOneAtLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNormOneReflectionCorrectionAtLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNatSmulMem
namespace GlobalTheory.NatMulIntegral

open NumberField

theorem exists_nat_mul_isIntegral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * a) := by
  have h1 : IsAlgebraic ℚ a := Algebra.IsAlgebraic.isAlgebraic a
  have h2 : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr h1
  obtain ⟨y, hy, hi⟩ := h2.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  rw [zsmul_eq_mul] at hi
  have hc : ((y.natAbs : ℕ) : E) = ((y.natAbs : ℤ) : E) := (Int.cast_natCast _).symm
  rcases Int.natAbs_eq y with h | h
  · rw [hc, ← h]
    exact hi
  · have h' : (y.natAbs : ℤ) = -y := by omega
    rw [hc, h', Int.cast_neg, neg_mul]
    exact hi.neg

theorem nat_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E)) (d : ℕ) {x : Fin n → E} (hx : x ∈ L) :
    (d : E) • x ∈ L := by
  rw [Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hx d

theorem exists_nat_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (y : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ (d : E) • y ∈ L := by
  have hy : y ∈ Submodule.span E (L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨d, hd, hdx⟩ := hx
    obtain ⟨e, he, hez⟩ := hz
    refine ⟨d * e, Nat.mul_pos hd he, ?_⟩
    have h1 := nat_smul_mem L e hdx
    have h2 := nat_smul_mem L d hez
    have : ((d * e : ℕ) : E) • (x + z) = (e : E) • (d : E) • x + (d : E) • (e : E) • z := by
      rw [smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (e : E)]
    rw [this]
    exact L.add_mem h1 h2
  | smul a x _ hx =>
    obtain ⟨d, hd, hdx⟩ := hx
    obtain ⟨e, he, hea⟩ := exists_nat_mul_isIntegral a
    refine ⟨d * e, Nat.mul_pos hd he, ?_⟩
    let b : RingOfIntegers E := ⟨(e : E) * a, hea⟩
    have h1 : b • (d : E) • x ∈ L := L.smul_mem b hdx
    have : ((d * e : ℕ) : E) • a • x = b • (d : E) • x := by
      rw [← algebraMap_smul E b]
      change _ = ((e : E) * a) • (d : E) • x
      rw [smul_smul, smul_smul, Nat.cast_mul]
      congr 1
      ring
    rw [this]
    exact h1

end GlobalTheory.NatMulIntegral
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNormOneReflectionCorrectionAtLevel
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep

theorem exists_nat_smul_mem_of_span {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (y : Fin n → E) : ∃ d : ℕ, 0 < d ∧ (d : E) • y ∈ L := by
  first
  | exact @_root_.GlobalTheory.NatMulIntegral.exists_nat_smul_mem
  | exact _root_.GlobalTheory.NatMulIntegral.exists_nat_smul_mem
  | (apply _root_.GlobalTheory.NatMulIntegral.exists_nat_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMulIntegral.exists_nat_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMulIntegral.exists_nat_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMulIntegral.exists_nat_smul_mem ..)

theorem exists_nat_smul_map_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (φ : (Fin n → E) →ₗ[E] (Fin n → E)) : ∃ d : ℕ, 0 < d ∧ ∀ v ∈ L, (d : E) • φ v ∈ L := by
  classical
  choose d hd hdL using exists_nat_smul_mem_of_span L hL
  obtain ⟨S, hS⟩ := hfg
  refine ⟨∏ s ∈ S, d (φ s), Finset.prod_pos fun s _ => hd _, ?_⟩
  intro v hv
  rw [← hS] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.prod_erase_mul S _ (Finset.mem_coe.1 hx), Nat.cast_mul, mul_smul,
      Nat.cast_smul_eq_nsmul E (∏ s ∈ S.erase x, d (φ s))]
    exact L.toAddSubmonoid.nsmul_mem (hdL _) _
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _), smul_add]
    exact L.add_mem hx hy
  | smul a x _ hx =>
    have h1 : φ (a • x) = (a : E) • φ x := φ.map_smul (a : E) x
    rw [h1, smul_comm]
    exact L.smul_mem a hx

theorem exists_refl_correction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (x : Fin n → E) (u : E) (N D : ℕ), hermE c G x x ≠ 0 → u * c u = 1 → 0 < N → 0 < D → ∃ u' : E, u' * c u' = 1 ∧ CongAt L N D (refl c G x (u' / u)) ∧ ∃ s : 𝓞 E, SplitOr c N s ∧ ∀ v ∈ L, s • (refl c G x u' *ᵥ v) ∈ L ∧ s • (refl c G x u'⁻¹ *ᵥ v) ∈ L := by
  intro F E _ _ _ _ _ c n G hG L hfg hL x u N D hx hu hN hD
  have hap := (GlobalTheory.UnRep.ReflLaws.refl_laws F E c n G hG x hx).1
  let φ : (Fin n → E) →ₗ[E] (Fin n → E) :=
    { toFun := fun v => (hermE c G v x / hermE c G x x) • x
      map_add' := by
        intro v w
        rw [← add_smul, ← add_div]
        congr 2
        simp [hermE, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro a v
        rw [RingHom.id_apply, smul_smul, ← mul_div_assoc]
        congr 2
        simp [hermE, Finset.mul_sum, mul_assoc] }
  obtain ⟨d, hd, hdL⟩ := exists_nat_smul_map_mem L hfg hL φ
  have hap' : ∀ a v, refl c G x a *ᵥ v = v + (a - 1) • φ v := by
    intro a v
    rw [hap]
    show _ = v + (a - 1) • ((hermE c G v x / hermE c G x x) • x)
    rw [smul_smul, mul_div_assoc]
  obtain ⟨u', hu', ⟨t, ht, b, hb⟩, s, hs, ⟨b₁, hb₁⟩, b₂, hb₂⟩ :=
    GlobalTheory.T.normOne_approximation_at_level_primes F E c hG.1 hG.2.1 u N (D * d) hu hN (Nat.mul_pos hD hd)
  have key : ∀ (a : E) (b : 𝓞 E), (s : E) * (a - 1) = ((D * d : ℕ) : E) * (b : E) →
      ∀ v ∈ L, s • (refl c G x a *ᵥ v) ∈ L := by
    intro a b hb v hv
    rw [hap', smul_add]
    refine L.add_mem (L.smul_mem s hv) ?_
    have : s • ((a - 1) • φ v) = ((D : 𝓞 E) * b) • ((d : E) • φ v) := by
      show (s : E) • ((a - 1) • φ v) = (((D : 𝓞 E) * b : 𝓞 E) : E) • ((d : E) • φ v)
      rw [smul_smul, smul_smul, hb]
      congr 1
      push_cast
      ring
    rw [this]
    exact L.smul_mem _ (hdL v hv)
  refine ⟨u', hu', ⟨t, ht, fun v hv => ⟨b • ((d : E) • φ v), L.smul_mem b (hdL v hv), ?_⟩⟩,
    s, hs, fun v hv => ⟨key _ _ hb₁ v hv, key _ _ hb₂ v hv⟩⟩
  rw [hap', add_sub_cancel_left, ← Nat.cast_smul_eq_nsmul E t, ← Nat.cast_smul_eq_nsmul E D]
  show _ = (D : E) • ((b : E) • ((d : E) • φ v))
  rw [smul_smul, smul_smul, smul_smul, hb]
  congr 1
  push_cast
  ring

end GlobalTheory.UnRep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNormOneReflectionCorrectionAtLevelStatement
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_norm_one_reflection_correction_at_level : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (x : Fin n → E) (u : E) (N D : ℕ), hermE c G x x ≠ 0 → u * c u = 1 → 0 < N → 0 < D → ∃ u' : E, u' * c u' = 1 ∧ CongAt L N D (refl c G x (u' / u)) ∧ ∃ s : 𝓞 E, SplitOr c N s ∧ ∀ v ∈ L, s • (refl c G x u' *ᵥ v) ∈ L ∧ s • (refl c G x u'⁻¹ *ᵥ v) ∈ L := by
  first | exact @GlobalTheory.UnRep.exists_refl_correction | exact GlobalTheory.UnRep.exists_refl_correction | (intros; apply GlobalTheory.UnRep.exists_refl_correction <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsNsmulMem
open NumberField

namespace GlobalTheory.IntegralMultipleOfVectors

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ (e : ℕ) (b : RingOfIntegers E), 0 < e ∧ (e : E) * a = algebraMap (RingOfIntegers E) E b := by
  have h : IsAlgebraic ℤ a :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨y, hy, hi⟩ := h.exists_integral_multiple
  have hi' : IsIntegral ℤ ((y.natAbs : E) * a) := by
    rcases Int.natAbs_eq y with h1 | h1
    · have : (y.natAbs : E) * a = y • a := by
        conv_rhs => rw [h1]
        simp
      rw [this]; exact hi
    · have : (y.natAbs : E) * a = -(y • a) := by
        conv_rhs => rw [h1]
        simp
      rw [this]; exact hi.neg
  exact ⟨y.natAbs, ⟨_, hi'⟩, Int.natAbs_pos.mpr hy, rfl⟩

theorem exists_nsmul_mem {E : Type} [Field E] {n : ℕ} [NumberField E]
    (L : Submodule (RingOfIntegers E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (w : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ d • w ∈ L := by
  have hw : w ∈ Submodule.span E (L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, hd, hx⟩ := hx
    obtain ⟨e, he, hy⟩ := hy
    refine ⟨d * e, Nat.mul_pos hd he, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact nsmul_mem hx e
    · rw [mul_smul]; exact nsmul_mem hy d
  | smul a x _ hx =>
    obtain ⟨d, hd, hx⟩ := hx
    obtain ⟨e, b, he, hb⟩ := exists_nat_mul_integral a
    refine ⟨e * d, Nat.mul_pos he hd, ?_⟩
    have : (e * d) • a • x = b • d • x := by
      rw [← algebraMap_smul E b, ← hb]
      ext i
      simp
      ring
    rw [this]
    exact L.smul_mem b hx

theorem exists_nsmul_mulVec_mem {E : Type} [Field E] {n : ℕ} [NumberField E]
    (L : Submodule (RingOfIntegers E) (Fin n → E)) (hfg : L.FG)
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (M : Matrix (Fin n) (Fin n) E) :
    ∃ d : ℕ, 0 < d ∧ ∀ v ∈ L, d • M.mulVec v ∈ L := by
  classical
  obtain ⟨s, hs⟩ := hfg
  choose f hf hmem using fun v => exists_nsmul_mem L hL (M.mulVec v)
  refine ⟨∏ v ∈ s, f v, Finset.prod_pos fun v _ => hf v, fun v hv => ?_⟩
  have hv' : v ∈ Submodule.span (RingOfIntegers E) (s : Set (Fin n → E)) := by
    rw [hs]; exact hv
  clear hv
  induction hv' using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.prod_erase_mul s f (Finset.mem_coe.mp hx), mul_smul]
    exact nsmul_mem (hmem x) _
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Matrix.mulVec_add, smul_add]
    exact L.add_mem hx hy
  | smul a x _ hx =>
    rw [← algebraMap_smul E a, Matrix.mulVec_smul, algebraMap_smul, smul_comm]
    exact L.smul_mem a hx

end GlobalTheory.IntegralMultipleOfVectors
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitaryCorrectionCongruentOneAtLevel
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep.Correct

variable {E : Type} [Field E] {n : ℕ}

theorem exists_nat_mulVec_mem [NumberField E] (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (M : Matrix (Fin n) (Fin n) E) :
    ∃ d : ℕ, 0 < d ∧ ∀ v ∈ L, d • (M *ᵥ v) ∈ L := by
  first
  | exact @_root_.GlobalTheory.IntegralMultipleOfVectors.exists_nsmul_mulVec_mem
  | exact _root_.GlobalTheory.IntegralMultipleOfVectors.exists_nsmul_mulVec_mem
  | (apply _root_.GlobalTheory.IntegralMultipleOfVectors.exists_nsmul_mulVec_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralMultipleOfVectors.exists_nsmul_mulVec_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralMultipleOfVectors.exists_nsmul_mulVec_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralMultipleOfVectors.exists_nsmul_mulVec_mem ..)

theorem congAt_mul {L : Submodule (𝓞 E) (Fin n → E)} {N D : ℕ} {A B : Matrix (Fin n) (Fin n) E}
    (hA : CongAt L N D A) (hB : CongAt L N D B) : CongAt L N D (A * B) := by
  obtain ⟨t₁, c₁, h₁⟩ := hA
  obtain ⟨t₂, c₂, h₂⟩ := hB
  refine ⟨t₁ * t₂, Nat.Coprime.mul_left c₁ c₂, fun v hv => ?_⟩
  obtain ⟨w₂, hw₂, e₂⟩ := h₂ v hv
  have hy : t₂ • (B *ᵥ v) ∈ L := by
    have : t₂ • (B *ᵥ v) = t₂ • v + D • w₂ := by rw [← e₂, smul_sub]; abel
    rw [this]
    exact L.add_mem (nsmul_mem hv _) (nsmul_mem hw₂ _)
  obtain ⟨w₁, hw₁, e₁⟩ := h₁ _ hy
  refine ⟨w₁ + t₁ • w₂, L.add_mem hw₁ (nsmul_mem hw₂ _), ?_⟩
  rw [smul_add, smul_comm D t₁, ← e₁, ← e₂, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
  module

theorem congAt_conj [CharZero E] {L : Submodule (𝓞 E) (Fin n → E)} {N D d e : ℕ} (he : 0 < e)
    {A R R' : Matrix (Fin n) (Fin n) E} (hRR : R * R' = 1)
    (hR : ∀ v ∈ L, d • (R *ᵥ v) ∈ L) (hR' : ∀ v ∈ L, e • (R' *ᵥ v) ∈ L)
    (hA : CongAt L N (D * d * e) A) : CongAt L N D (R * A * R') := by
  obtain ⟨t, ct, h⟩ := hA
  refine ⟨t, ct, fun v hv => ?_⟩
  obtain ⟨w, hw, e₁⟩ := h _ (hR' v hv)
  refine ⟨_, hR w hw, ?_⟩
  have e₂ := congrArg (fun z => R *ᵥ z) e₁
  simp only [Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hRR, Matrix.one_mulVec] at e₂
  have he' : (e : E) ≠ 0 := Nat.cast_ne_zero.2 he.ne'
  apply smul_right_injective (Fin n → E) he'
  simp only [Nat.cast_smul_eq_nsmul]
  rw [Matrix.mul_assoc]
  linear_combination (exp := 1) e₂

theorem splitOr_mul {F : Type} [Field F] [Algebra F E] {c : E ≃ₐ[F] E} {N : ℕ} {s t : 𝓞 E}
    (hs : SplitOr c N s) (ht : SplitOr c N t) : SplitOr c N (s * t) :=
  ⟨mul_ne_zero hs.1 ht.1, fun P hP h => (hP.mem_or_mem h).elim (hs.2 P hP) (ht.2 P hP)⟩

theorem smul_mul_mem {L : Submodule (𝓞 E) (Fin n → E)} {s t : 𝓞 E} {A B : Matrix (Fin n) (Fin n) E}
    (hA : ∀ v ∈ L, s • (A *ᵥ v) ∈ L) (hB : ∀ v ∈ L, t • (B *ᵥ v) ∈ L) (v : Fin n → E) (hv : v ∈ L) :
    (s * t) • ((A * B) *ᵥ v) ∈ L := by
  have := hA _ (hB v hv)
  rwa [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← mul_smul] at this

theorem exists_unitary_correction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (γ₀ : GL (Fin n) E) (N D : ℕ), IsUnE c G γ₀.1 → 0 < N → 0 < D → ∃ γ : GL (Fin n) E, IsUnE c G γ.1 ∧ CongAt L N D (γ * γ₀⁻¹).1 ∧ ∃ s : 𝓞 E, SplitOr c N s ∧ ∀ v ∈ L, s • (γ.1 *ᵥ v) ∈ L ∧ s • ((γ⁻¹).1 *ᵥ v) ∈ L := by
  intro F E _ _ _ _ _ c n G hG L hfg hL γ₀ N D hγ₀ hN hD
  obtain ⟨l, hl, hprod⟩ := GlobalTheory.T.unitaryMatrix_eq_prod_quasiReflections F E c n G hG _ hγ₀
  clear hγ₀
  induction l generalizing γ₀ D with
  | nil =>
    have h1 : γ₀ = 1 := Units.ext (by simpa using hprod)
    subst h1
    refine ⟨1, fun x y => by simp, ⟨1, by simp, fun v _ => ⟨0, L.zero_mem, by simp⟩⟩, 1,
      ⟨one_ne_zero, fun P hP h => absurd ((Ideal.eq_top_iff_one P).2 h) hP.ne_top⟩, fun v hv => ?_⟩
    simpa using hv
  | cons p l ih =>
    obtain ⟨x, u⟩ := p
    obtain ⟨hx, hu⟩ := hl (x, u) List.mem_cons_self
    simp only at hx hu
    obtain ⟨-, r1, rmul, run⟩ := GlobalTheory.T.unitaryQuasiReflection_laws F E c n G hG x hx
    have hu0 : u ≠ 0 := left_ne_zero_of_mul_eq_one hu
    let R : (a : E) → a ≠ 0 → GL (Fin n) E := fun a ha =>
      ⟨refl c G x a, refl c G x a⁻¹, by rw [rmul, mul_inv_cancel₀ ha, r1],
        by rw [rmul, inv_mul_cancel₀ ha, r1]⟩
    obtain ⟨d, hd, hRd⟩ := exists_nat_mulVec_mem L hfg hL (R u hu0).1
    obtain ⟨e, he, hRe⟩ := exists_nat_mulVec_mem L hfg hL ((R u hu0)⁻¹).1
    obtain ⟨γ₁, hγ₁, hc₁, s₁, hs₁, hL₁⟩ := ih ((R u hu0)⁻¹ * γ₀) (D * d * e)
      (Nat.mul_pos (Nat.mul_pos hD hd) he) (fun p hp => hl p (List.mem_cons_of_mem _ hp)) (by
        rw [Units.val_mul, hprod, List.map_cons, List.prod_cons, ← mul_assoc]
        change _ = _
        have : ((R u hu0)⁻¹).1 * refl c G x u = 1 := (R u hu0).inv_mul
        rw [this, one_mul])
    obtain ⟨u', hu', hc', s', hs', hL'⟩ := GlobalTheory.T.exists_norm_one_reflection_correction_at_level F E c n G hG L hfg hL x u N D hx hu hN hD
    have hu'0 : u' ≠ 0 := left_ne_zero_of_mul_eq_one hu'
    refine ⟨R u' hu'0 * γ₁, ?_, ?_, s' * s₁, splitOr_mul hs' hs₁, fun v hv => ⟨?_, ?_⟩⟩
    · intro y z
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact (run u' hu' _ _).trans (hγ₁ y z)
    · have hconj := congAt_conj he (R u hu0).mul_inv hRd hRe hc₁
      have h := congAt_mul hc' hconj
      have e1 : refl c G x (u' / u) = (R u' hu'0 * (R u hu0)⁻¹).1 := by
        rw [div_eq_mul_inv, ← rmul]; rfl
      rw [e1, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul] at h
      convert h using 2
      group
    · rw [Units.val_mul]
      exact smul_mul_mem (fun v hv => (hL' v hv).1) (fun v hv => (hL₁ v hv).1) v hv
    · rw [mul_inv_rev, Units.val_mul, mul_comm s']
      exact smul_mul_mem (fun v hv => (hL₁ v hv).2) (fun v hv => (hL' v hv).2) v hv

end GlobalTheory.UnRep.Correct
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitaryCorrectionCongruentOneAtLevelStatement
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_correction_congruent_one_at_level : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (γ₀ : GL (Fin n) E) (N D : ℕ), IsUnE c G γ₀.1 → 0 < N → 0 < D → ∃ γ : GL (Fin n) E, IsUnE c G γ.1 ∧ CongAt L N D (γ * γ₀⁻¹).1 ∧ ∃ s : 𝓞 E, SplitOr c N s ∧ ∀ v ∈ L, s • (γ.1 *ᵥ v) ∈ L ∧ s • ((γ⁻¹).1 *ᵥ v) ∈ L := by
  first | exact @GlobalTheory.UnRep.Correct.exists_unitary_correction | exact GlobalTheory.UnRep.Correct.exists_unitary_correction | (intros; apply GlobalTheory.UnRep.Correct.exists_unitary_correction <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalUnitarySplitDenominator
noncomputable section

namespace GlobalTheory.UnRep.LatForm

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix nonZeroDivisors

theorem exists_dvd_coprime_mul_pow (N : ℕ) (m : ℕ) (hm : 0 < m) :
    ∃ j u : ℕ, u.Coprime N ∧ m ∣ u * N ^ j := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases h : Nat.gcd m N = 1
    · exact ⟨0, m, h, by simp⟩
    · obtain ⟨m', hm'⟩ := Nat.gcd_dvd_left m N
      have hg : 0 < Nat.gcd m N := Nat.gcd_pos_of_pos_left _ hm
      have hm'0 : 0 < m' := Nat.pos_of_ne_zero (by rintro rfl; simp at hm'; omega)
      have hlt : m' < m := by
        have : 2 ≤ Nat.gcd m N := by omega
        nlinarith
      obtain ⟨j, u, hu, hd⟩ := ih m' hlt hm'0
      refine ⟨j + 1, u, hu, ?_⟩
      rw [hm', pow_succ, ← mul_assoc, mul_comm (Nat.gcd m N)]
      exact Nat.mul_dvd_mul hd (Nat.gcd_dvd_right m N)

theorem inv_integral {V : Type} [AddCommGroup V] (Λ : AddSubgroup V) (k k' : V →+ V)
    (hk : ∀ z, k' (k z) = z) (N t m : ℕ) (ht : t.Coprime N) (hm : 0 < m)
    (h1 : ∀ z ∈ Λ, ∃ w ∈ Λ, t • (k z - z) = N • w) (h2 : ∀ z ∈ Λ, m • k' z ∈ Λ) :
    ∃ t' : ℕ, t'.Coprime N ∧ ∀ z ∈ Λ, t' • k' z ∈ Λ := by
  have key : ∀ j : ℕ, ∀ z ∈ Λ, ∃ y ∈ Λ, ∃ w ∈ Λ, t ^ j • k' z = y + N ^ j • k' w := by
    intro j
    induction j with
    | zero => intro z hz; exact ⟨0, Λ.zero_mem, z, hz, by simp⟩
    | succ j ih =>
      intro z hz
      obtain ⟨y, hy, w, hw, e⟩ := ih z hz
      obtain ⟨w', hw', e'⟩ := h1 w hw
      have e2 : t • k' w = t • w + N • k' (-w') := by
        have := congrArg k' e'
        rw [map_nsmul, map_nsmul, map_sub, hk, smul_sub] at this
        rw [map_neg, smul_neg, ← this]; abel
      refine ⟨t • y + N ^ j • t • w, Λ.add_mem (Λ.nsmul_mem hy _) (Λ.nsmul_mem (Λ.nsmul_mem hw _) _),
        -w', Λ.neg_mem hw', ?_⟩
      rw [pow_succ', mul_smul, e, smul_add, smul_comm t (N ^ j), e2, smul_add, pow_succ, mul_smul, add_assoc]
  obtain ⟨j, u, hu, q, hq⟩ := exists_dvd_coprime_mul_pow N m hm
  refine ⟨u * t ^ j, Nat.Coprime.mul_left hu (Nat.Coprime.pow_left _ ht), fun z hz => ?_⟩
  obtain ⟨y, hy, w, hw, e⟩ := key j z hz
  rw [mul_smul, e, smul_add, ← mul_smul, hq, mul_comm, mul_smul]
  exact Λ.add_mem (Λ.nsmul_mem hy _) (Λ.nsmul_mem (h2 w hw) _)

theorem exists_mem_primes {E : Type} [Field E] [NumberField E] (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) :
    ∃ s ∈ I, s ≠ 0 ∧ ∀ P : Ideal (𝓞 E), P.IsPrime → s ∈ P → I ≤ P := by
  classical
  have hI0 : I ∈ (Ideal (𝓞 E))⁰ := mem_nonZeroDivisors_of_ne_zero hI
  set h := Fintype.card (ClassGroup (𝓞 E)) with hh
  have hpos : h ≠ 0 := Fintype.card_ne_zero
  have h1 : ClassGroup.mk0 ((⟨I, hI0⟩ : (Ideal (𝓞 E))⁰) ^ h) = 1 := by
    rw [map_pow, pow_card_eq_one]
  have h2 : (I ^ h).IsPrincipal := (ClassGroup.mk0_eq_one_iff (pow_mem hI0 h)).1 h1
  obtain ⟨s, hs⟩ := h2
  have hs' : I ^ h = Ideal.span {s} := hs
  refine ⟨s, Ideal.pow_le_self hpos (hs' ▸ Ideal.mem_span_singleton_self s), ?_, fun P hP hsP => ?_⟩
  · rintro rfl
    exact pow_ne_zero h hI (by rw [hs']; simp)
  · exact (Ideal.IsPrime.pow_le_iff hpos).1 (by rw [hs']; exact (Ideal.span_singleton_le_iff_mem _).2 hsP)

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem fm_mul (A B : Matrix (Fin n) (Fin n) E) : fm F (A * B) = fm F A * fm F B :=
  Matrix.map_mul (f := (Algebra.TensorProduct.includeRight :
    E →ₐ[F] FiniteAdeleRing (𝓞 F) F ⊗[F] E).toRingHom)

theorem fm_one : fm F (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (by simp) rfl

theorem fm_mulVec_pure (M : Matrix (Fin n) (Fin n) E) (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    fm F M *ᵥ (fun i => a ⊗ₜ[F] x i) = fun i => a ⊗ₜ[F] (M *ᵥ x) i := by
  funext i
  simp [fm, Matrix.mulVec, dotProduct, TensorProduct.tmul_sum]

theorem congAtA_of_congAt (L : Submodule (𝓞 E) (Fin n → E)) (N D : ℕ) (δ : Matrix (Fin n) (Fin n) E)
    (h : CongAt L N D δ) : CongAtA F L N D (fm F δ) := by
  obtain ⟨t, ht, h⟩ := h
  refine ⟨t, ht, fun z hz => ?_⟩
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    obtain ⟨w, hw, e⟩ := h x hx
    refine ⟨fun i => a ⊗ₜ[F] w i, AddSubgroup.subset_closure ⟨a, ha, w, hw, rfl⟩, ?_⟩
    rw [fm_mulVec_pure]
    funext i
    have := congrArg (fun y : Fin n → E =>
      (TensorProduct.mk F (FiniteAdeleRing (𝓞 F) F) E a) (y i)) e
    simpa only [Pi.smul_apply, Pi.sub_apply, map_nsmul, map_sub, TensorProduct.mk_apply] using this
  | zero => exact ⟨0, AddSubgroup.zero_mem _, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨w, hw, e⟩ := ihx
    obtain ⟨w', hw', e'⟩ := ihy
    refine ⟨w + w', AddSubgroup.add_mem _ hw hw', ?_⟩
    rw [smul_add, ← e, ← e', Matrix.mulVec_add, ← smul_add]; congr 1; abel
  | neg x _ ih =>
    obtain ⟨w, hw, e⟩ := ih
    refine ⟨-w, AddSubgroup.neg_mem _ hw, ?_⟩
    rw [smul_neg, ← e, Matrix.mulVec_neg, ← smul_neg]; congr 1; abel

theorem smul_fm_mem (L : Submodule (𝓞 E) (Fin n → E)) (s : 𝓞 E) (M : Matrix (Fin n) (Fin n) E)
    (h : ∀ v ∈ L, s • (M *ᵥ v) ∈ L) : ∀ z ∈ hat F (L : Set (Fin n → E)),
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • (fm F M *ᵥ z) ∈ hat F (L : Set (Fin n → E)) := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, _, h x hx, ?_⟩
    rw [fm_mulVec_pure]
    funext i
    simp [Algebra.smul_def]
  | zero => simp
  | add x y _ _ ihx ihy => rw [Matrix.mulVec_add, smul_add]; exact AddSubgroup.add_mem _ ihx ihy
  | neg x _ ih => rw [Matrix.mulVec_neg, smul_neg]; exact AddSubgroup.neg_mem _ ih

theorem smul_mem_hat (L : Submodule (𝓞 E) (Fin n → E)) (s : 𝓞 E) :
    ∀ z ∈ hat F (L : Set (Fin n → E)),
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • z ∈ hat F (L : Set (Fin n → E)) := by
  intro z hz
  have := smul_fm_mem (F := F) L s 1 (fun v hv => by simpa using L.smul_mem s hv) z hz
  rwa [fm_one, Matrix.one_mulVec] at this

theorem congAtA_mul (L : Submodule (𝓞 E) (Fin n → E)) (N D : ℕ) (a b : Matrix (Fin n) (Fin n) (RA F E))
    (ha : CongAtA F L N D a) (hb : CongAtA F L N D b) : CongAtA F L N D (a * b) := by
  obtain ⟨t, ht, ha⟩ := ha
  obtain ⟨u, hu, hb⟩ := hb
  refine ⟨t * u, Nat.Coprime.mul_left ht hu, fun z hz => ?_⟩
  obtain ⟨w, hw, e⟩ := hb z hz
  obtain ⟨w', hw', e'⟩ := ha (u • z + D • w)
    (AddSubgroup.add_mem _ (AddSubgroup.nsmul_mem _ hz _) (AddSubgroup.nsmul_mem _ hw _))
  refine ⟨w' + t • w, AddSubgroup.add_mem _ hw' (AddSubgroup.nsmul_mem _ hw _), ?_⟩
  have e1 : u • z + D • w = u • (b *ᵥ z) := by rw [← e, smul_sub]; abel
  rw [e1, Matrix.mulVec_smul, Matrix.mulVec_mulVec] at e'
  rw [smul_add, ← e', smul_comm D t, ← e, ← smul_add, mul_smul]
  congr 1
  rw [smul_sub, smul_sub]; abel

def denIdeal (L : Submodule (𝓞 E) (Fin n → E)) (M : Matrix (Fin n) (Fin n) (RA F E)) : Ideal (𝓞 E) where
  carrier := {s | ∀ z ∈ hat F (L : Set (Fin n → E)),
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • (M *ᵥ z) ∈ hat F (L : Set (Fin n → E))}
  add_mem' := by
    intro a b ha hb z hz
    have := AddSubgroup.add_mem _ (ha z hz) (hb z hz)
    rw [← add_smul, ← TensorProduct.tmul_add] at this
    exact this
  zero_mem' := by intro z hz; simp
  smul_mem' := by
    intro a b hb z hz
    have := smul_mem_hat L a _ (hb z hz)
    rw [← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul] at this
    exact this

theorem one_tmul_natCast_smul (m : ℕ) (z : Fin n → RA F E) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (((m : 𝓞 E)) : E)) • z = m • z := by
  have : ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (((m : 𝓞 E)) : E)) = (m : RA F E) := by
    have h : (((m : 𝓞 E)) : E) = (m : E) := by simp
    rw [h]
    exact map_natCast (Algebra.TensorProduct.includeRight :
      E →ₐ[F] FiniteAdeleRing (𝓞 F) F ⊗[F] E) m
  rw [this, Nat.cast_smul_eq_nsmul]

theorem one_tmul_natCast_mul_smul (m : ℕ) (s : 𝓞 E) (z : Fin n → RA F E) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ((((m : 𝓞 E) * s : 𝓞 E)) : E)) • z =
      m • ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • z := by
  rw [← one_tmul_natCast_smul, ← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl

theorem exists_rep_split_denominator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → Module.finrank F E = 2 → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (g : GL (Fin n) (RA F E)) (N : ℕ), IsUnA c G g.1 → 0 < N → ∃ γ : GL (Fin n) E, IsUnE c G γ.1 ∧ CongAtA F L N N (fm F γ.1 * g.1) ∧ ∃ s : 𝓞 E, SplitOff c N s ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • ((fm F γ.1 * g.1) *ᵥ z) ∈ hat F (L : Set (Fin n → E)) ∧ ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • (((g⁻¹).1 * fm F (γ⁻¹).1) *ᵥ z) ∈ hat F (L : Set (Fin n → E)) := by
  intro F E _ _ _ _ _ c n G hG h2 L hL hL' g N hg hN
  obtain ⟨-, hden, -⟩ := GlobalTheory.T.idempotent_adeles_and_small_adelic_matrices F E n L hL hL'
  obtain ⟨d₁, hd₁, H₁⟩ := hden g.1
  obtain ⟨d₂, hd₂, H₂⟩ := hden (g⁻¹).1
  have hN' : 0 < N * (d₁ * d₂) := by positivity
  obtain ⟨γ₀, hγ₀, hc₀⟩ := GlobalTheory.T.unitaryGroup_weak_approximation_at_primes F E c n G hG h2 L hL hL' g _ _ hg hN' hN'
  obtain ⟨γ, hγ, hc₁, s₁, hs₁, hs⟩ := GlobalTheory.T.exists_unitary_correction_congruent_one_at_level F E c n G hG L hL hL' γ₀ _ _ hγ₀ hN' hN'
  have hc := congAtA_mul L _ _ _ _ (congAtA_of_congAt (F := F) L _ _ _ hc₁) hc₀
  have hγγ : fm F (γ * γ₀⁻¹).1 * (fm F γ₀.1 * g.1) = fm F γ.1 * g.1 := by
    rw [← mul_assoc, ← fm_mul, ← Units.val_mul, inv_mul_cancel_right]
  rw [hγγ] at hc
  obtain ⟨t, ht, hc⟩ := hc
  set k := fm F γ.1 * g.1 with hk
  set k' := (g⁻¹).1 * fm F (γ⁻¹).1 with hk'
  have hkk : k' * k = 1 := by
    rw [hk, hk', mul_assoc, ← mul_assoc (fm F _), ← fm_mul, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, fm_one, one_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  obtain ⟨m, hm, Hm⟩ := hden k'
  obtain ⟨t', ht', H'⟩ := inv_integral (hat F (L : Set (Fin n → E))) (Matrix.mulVecLin k).toAddMonoidHom
    (Matrix.mulVecLin k').toAddMonoidHom
    (fun z => by
      change k' *ᵥ (k *ᵥ z) = z
      rw [Matrix.mulVec_mulVec, hkk, Matrix.one_mulVec]) _ t m ht hm hc Hm
  refine ⟨γ, hγ, ⟨t, Nat.Coprime.coprime_mul_right_right ht, fun z hz => ?_⟩, ?_⟩
  · obtain ⟨w, hw, e⟩ := hc z hz
    exact ⟨(d₁ * d₂) • w, AddSubgroup.nsmul_mem _ hw _, by rw [e, mul_smul]⟩
  have a1 : ((t * t' : ℕ) : 𝓞 E) ∈ denIdeal L k ⊓ denIdeal L k' := by
    constructor
    · intro z hz
      obtain ⟨w, hw, e⟩ := hc z hz
      rw [one_tmul_natCast_smul, mul_comm, mul_smul]
      refine AddSubgroup.nsmul_mem _ ?_ _
      have : t • (k *ᵥ z) = t • z + (N * (d₁ * d₂)) • w := by rw [← e, smul_sub]; abel
      rw [this]
      exact AddSubgroup.add_mem _ (AddSubgroup.nsmul_mem _ hz _) (AddSubgroup.nsmul_mem _ hw _)
    · intro z hz
      rw [one_tmul_natCast_smul, mul_smul]
      exact AddSubgroup.nsmul_mem _ (H' z hz) _
  have a2 : ((d₁ * d₂ : ℕ) : 𝓞 E) * s₁ ∈ denIdeal L k ⊓ denIdeal L k' := by
    constructor
    · intro z hz
      have := smul_fm_mem (F := F) L s₁ γ.1 (fun v hv => (hs v hv).1) _ (H₁ z hz)
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, smul_comm] at this
      rw [one_tmul_natCast_mul_smul, mul_comm, mul_smul]
      exact AddSubgroup.nsmul_mem _ this _
    · intro z hz
      have := H₂ _ (smul_fm_mem (F := F) L s₁ (γ⁻¹).1 (fun v hv => (hs v hv).2) _ hz)
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec] at this
      rw [one_tmul_natCast_mul_smul, mul_smul]
      exact AddSubgroup.nsmul_mem _ this _
  have hne : denIdeal L k ⊓ denIdeal L k' ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at a2
    exact mul_ne_zero (Nat.cast_ne_zero.2 (by positivity)) hs₁.1 a2
  obtain ⟨s, hsI, hs0, hsP⟩ := exists_mem_primes _ hne
  refine ⟨s, ⟨hs0, fun P hP h => ?_⟩, fun z hz => ⟨hsI.1 z hz, hsI.2 z hz⟩⟩
  have b1 := hsP P hP h a1
  have b2 := hsP P hP h a2
  have hcop : IsCoprime ((t * t' : ℕ) : 𝓞 E) ((N * (d₁ * d₂) : ℕ) : 𝓞 E) :=
    Nat.Coprime.cast (Nat.Coprime.mul_left ht ht')
  have hnot : ((N * (d₁ * d₂) : ℕ) : 𝓞 E) ∉ P := by
    intro hh
    obtain ⟨x, y, e⟩ := hcop
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 (e ▸ P.add_mem (P.mul_mem_left x b1) (P.mul_mem_left y hh)))
  refine ⟨?_, fun hh => hnot (by rw [Nat.cast_mul]; exact P.mul_mem_right _ hh)⟩
  rcases hP.mem_or_mem b2 with h1 | h1
  · exact (hnot (by rw [Nat.cast_mul]; exact P.mul_mem_left _ h1)).elim
  · exact (hs₁.2 P hP h1).resolve_right hnot

end GlobalTheory.UnRep.LatForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalUnitarySplitDenominatorStatement
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_unitary_split_denominator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → Module.finrank F E = 2 → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (g : GL (Fin n) (RA F E)) (N : ℕ), IsUnA c G g.1 → 0 < N → ∃ γ : GL (Fin n) E, IsUnE c G γ.1 ∧ CongAtA F L N N (fm F γ.1 * g.1) ∧ ∃ s : 𝓞 E, SplitOff c N s ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • ((fm F γ.1 * g.1) *ᵥ z) ∈ hat F (L : Set (Fin n → E)) ∧ ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • (((g⁻¹).1 * fm F (γ⁻¹).1) *ᵥ z) ∈ hat F (L : Set (Fin n → E)) := by
  first | exact @GlobalTheory.UnRep.LatForm.exists_rep_split_denominator | exact GlobalTheory.UnRep.LatForm.exists_rep_split_denominator | (intros; apply GlobalTheory.UnRep.LatForm.exists_rep_split_denominator <;> assumption)
end
