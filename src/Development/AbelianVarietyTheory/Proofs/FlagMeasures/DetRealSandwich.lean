module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeDedekindZetaRealValueAndLeZetaPow
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingOfBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TranslatedLatticeAtInfinityFullCovolumeDual

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetRealSandwich
namespace GlobalTheory.DeterminantRealSandwich

open Matrix

noncomputable def rowAct {j : ℕ} (C : Matrix (Fin j) (Fin j) ℂ) :
    (Fin j → Fin j → ℂ) →ₗ[ℂ] (Fin j → Fin j → ℂ) :=
  LinearMap.pi fun a => Matrix.toLin' C ∘ₗ LinearMap.proj a

theorem det_rowAct {j : ℕ} (C : Matrix (Fin j) (Fin j) ℂ) :
    LinearMap.det (rowAct C) = C.det ^ j := by
  unfold rowAct
  rw [LinearMap.det_pi (fun _ : Fin j => Matrix.toLin' C)]
  simp [LinearMap.det_toLin']

def swapIdx (j : ℕ) : (Fin j → Fin j → ℂ) ≃ₗ[ℂ] (Fin j → Fin j → ℂ) where
  toFun h := fun a b => h b a
  invFun h := fun a b => h b a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def sandwich {j : ℕ} (A B : Matrix (Fin j) (Fin j) ℂ) :
    (Fin j → Fin j → ℂ) →ₗ[ℂ] (Fin j → Fin j → ℂ) :=
  rowAct Bᵀ ∘ₗ ((swapIdx j).toLinearMap ∘ₗ rowAct A ∘ₗ (swapIdx j).symm.toLinearMap)

theorem det_sandwich {j : ℕ} (A B : Matrix (Fin j) (Fin j) ℂ) :
    LinearMap.det (sandwich A B) = B.det ^ j * A.det ^ j := by
  unfold sandwich
  rw [LinearMap.det_comp, LinearMap.det_conj, det_rowAct, det_rowAct, Matrix.det_transpose]

theorem sandwich_apply {j : ℕ} (A B : Matrix (Fin j) (Fin j) ℂ) (h : Fin j → Fin j → ℂ)
    (a b : Fin j) : sandwich A B h a b = (A * Matrix.of h * B) a b := by
  simp [sandwich, rowAct, swapIdx, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]

theorem det_real_sandwich {j : ℕ} (A B : Matrix (Fin j) (Fin j) ℂ) :
    LinearMap.det ((sandwich A B).restrictScalars ℝ) = (‖A.det‖ ^ 2 * ‖B.det‖ ^ 2) ^ j := by
  rw [LinearMap.det_restrictScalars, det_sandwich, Algebra.norm_complex_apply, map_mul, map_pow,
    map_pow, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, mul_pow, mul_comm]

theorem det_real_family (ι : Type) [Fintype ι] (j : ℕ) (A B : ι → Matrix (Fin j) (Fin j) ℂ)
    (L : (ι → Fin j → Fin j → ℂ) →ₗ[ℝ] ι → Fin j → Fin j → ℂ)
    (hL : ∀ (h : ι → Fin j → Fin j → ℂ) (w : ι),
      Matrix.of (L h w) = A w * Matrix.of (h w) * B w) :
    LinearMap.det L = ∏ w : ι, (‖(A w).det‖ ^ 2 * ‖(B w).det‖ ^ 2) ^ j := by
  have e : L = LinearMap.pi fun w =>
      ((sandwich (A w) (B w)).restrictScalars ℝ) ∘ₗ LinearMap.proj w := by
    refine LinearMap.ext fun h => funext fun w => funext fun a => funext fun b => ?_
    have h1 : L h w a b = (A w * Matrix.of (h w) * B w) a b := by
      rw [← hL h w]; rfl
    rw [h1, ← sandwich_apply]
    rfl
  rw [e, LinearMap.det_pi (fun w => (sandwich (A w) (B w)).restrictScalars ℝ)]
  exact Finset.prod_congr rfl fun w _ => det_real_sandwich _ _

end GlobalTheory.DeterminantRealSandwich
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BiorthogonalBlockFramesTriangular
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BiorthogonalBlockFramesTriangular
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov

theorem mul_eq_zero_of_mulVec_mulVec {p q n : ℕ} {A : Matrix (Fin p) (Fin n) ℂ}
    {B : Matrix (Fin n) (Fin q) ℂ} (h : ∀ x, A *ᵥ (B *ᵥ x) = 0) : A * B = 0 := by
  ext i j
  have hx := congrFun (h (Pi.single j 1)) i
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at hx
  simpa using hx

theorem Biorth.col_mem {n m : ℕ} {W : ℕ → Submodule ℂ (Fin n → ℂ)} {r : ℕ → ℕ}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) ℂ}
    (hT : Biorth r m T T') (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → T' b *ᵥ y = 0)
    (s k : ℕ) (hk : s < k) (x : Fin (r s) → ℂ) : T s *ᵥ x ∈ W k := by
  rw [hW]
  intro b hb
  rw [Matrix.mulVec_mulVec, hT.2.1 b s (by omega), Matrix.zero_mulVec]

theorem Biorth.mul_eq_block {n m p q : ℕ} {W : ℕ → Submodule ℂ (Fin n → ℂ)} {r : ℕ → ℕ}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) ℂ}
    (hT : Biorth r m T T') (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → T' b *ᵥ y = 0)
    (b : ℕ) {A : Matrix (Fin p) (Fin n) ℂ} {B : Matrix (Fin n) (Fin q) ℂ}
    (hA : ∀ y ∈ W b, A *ᵥ y = 0) (hB : ∀ x, B *ᵥ x ∈ W (b + 1)) :
    A * B = (A * T b) * (T' b * B) := by
  have hAT : ∀ c, c < b → A * T c = 0 := fun c hc =>
    mul_eq_zero_of_mulVec_mulVec fun x => hA _ (Biorth.col_mem hT hW c b hc x)
  have hTB : ∀ c, b < c → T' c * B = 0 := fun c hc =>
    mul_eq_zero_of_mulVec_mulVec fun x => (hW (b + 1) _).1 (hB x) c (by omega)
  calc A * B = A * (∑ c ∈ Finset.range m, T c * T' c) * B := by rw [hT.2.2, Matrix.mul_one]
    _ = ∑ c ∈ Finset.range m, (A * T c) * (T' c * B) := by
      rw [Matrix.mul_sum, Matrix.sum_mul]
      simp only [Matrix.mul_assoc]
    _ = (A * T b) * (T' b * B) := by
      apply Finset.sum_eq_single b
      · intro c _ hcb
        rcases lt_or_gt_of_ne hcb with hc | hc
        · rw [hAT c hc, Matrix.zero_mul]
        · rw [hTB c hc, Matrix.mul_zero]
      · intro hb

        have hTb : T b = 0 := by
          rw [← Matrix.one_mul (T b), ← hT.2.2, Matrix.sum_mul]
          apply Finset.sum_eq_zero
          intro c hc
          rw [Matrix.mul_assoc, hT.2.1 c b (by rintro rfl; exact hb hc), Matrix.mul_zero]
        rw [hTb, Matrix.mul_zero, Matrix.zero_mul]

theorem blockFrames_triangular (n m : ℕ) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (r : ℕ → ℕ)
    (T U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ) (T' U' : ∀ b, Matrix (Fin (r b)) (Fin n) ℂ)
    (hT : Biorth r m T T') (hU : Biorth r m U U')
    (hWT : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → T' b *ᵥ y = 0)
    (hWU : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → U' b *ᵥ y = 0) :
    (∀ b, (U' b * T b) * (T' b * U b) = 1) ∧ ∀ c, ∀ Y ∈ lowers W c, ∀ b,
      U' b * Y * U (b + c + 1) =
        (U' b * T b) * (T' b * Y * T (b + c + 1)) * (T' (b + c + 1) * U (b + c + 1)) := by
  refine ⟨fun b => ?_, fun c Y hY b => ?_⟩
  · rw [← Biorth.mul_eq_block hT hWT b (fun y hy => (hWU b y).1 hy b le_rfl)
      (fun x => Biorth.col_mem hU hWU b (b + 1) (by omega) x)]
    exact hU.1 b
  · have hY' : ∀ b', ∀ y ∈ W (b' + c + 1), Y *ᵥ y ∈ W b' := mem_lowers.1 hY
    have e1 : U' b * (Y * U (b + c + 1)) = (U' b * T b) * (T' b * (Y * U (b + c + 1))) :=
      Biorth.mul_eq_block hT hWT b (fun y hy => (hWU b y).1 hy b le_rfl) (fun x => by
        rw [← Matrix.mulVec_mulVec]
        exact hY' (b + 1) _ (Biorth.col_mem hU hWU (b + c + 1) (b + 1 + c + 1) (by omega) x))
    have e2 : (T' b * Y) * U (b + c + 1) =
        ((T' b * Y) * T (b + c + 1)) * (T' (b + c + 1) * U (b + c + 1)) :=
      Biorth.mul_eq_block hT hWT (b + c + 1)
        (fun y hy => by
          rw [← Matrix.mulVec_mulVec]
          exact (hWT b _).1 (hY' b y hy) b le_rfl)
        (fun x => Biorth.col_mem hU hWU (b + c + 1) (b + c + 1 + 1) (by omega) x)
    calc U' b * Y * U (b + c + 1) = U' b * (Y * U (b + c + 1)) := Matrix.mul_assoc _ _ _
      _ = (U' b * T b) * (T' b * (Y * U (b + c + 1))) := e1
      _ = (U' b * T b) * ((T' b * Y) * U (b + c + 1)) := by rw [Matrix.mul_assoc (T' b)]
      _ = _ := by rw [e2]; simp only [Matrix.mul_assoc]

end GlobalTheory.RadCov
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BiorthogonalBlockFramesTriangularStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.biorthogonal_block_frames_triangular : ∀ (n m : ℕ) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (r : ℕ → ℕ) (T U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ) (T' U' : ∀ b, Matrix (Fin (r b)) (Fin n) ℂ), Biorth r m T T' → Biorth r m U U' → (∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → T' b *ᵥ y = 0) → (∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → U' b *ᵥ y = 0) → (∀ b, (U' b * T b) * (T' b * U b) = 1) ∧ ∀ c, ∀ Y ∈ lowers W c, ∀ b, U' b * Y * U (b + c + 1) = (U' b * T b) * (T' b * Y * T (b + c + 1)) * (T' (b + c + 1) * U (b + c + 1)) := by
  first | exact @GlobalTheory.RadCov.blockFrames_triangular | exact GlobalTheory.RadCov.blockFrames_triangular | (intros; apply GlobalTheory.RadCov.blockFrames_triangular <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSkewIntegerNormCoprimePrime
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSkewIntegerNormCoprimePrime
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov.SkewUnit

theorem exists_sub_notMem {R : Type} [CommRing R] [IsDedekindDomain R] (σ : R →+* R)
    (hσ : ∀ x, σ (σ x) = x) {p : R} (hp : p ≠ 0) (hσp : σ p = p)
    (h : ∀ P : Ideal R, P.IsMaximal → ∃ θ, θ - σ θ ∉ P) :
    ∃ θ, ∀ P : Ideal R, P.IsMaximal → p ∈ P → θ - σ θ ∉ P := by
  classical
  have hfin : {P : Ideal R | P.IsMaximal ∧ p ∈ P}.Finite := by
    have h1 := (Ideal.finite_factors (I := Ideal.span {p}) (by simpa using hp)).image
      (fun v => v.asIdeal)
    refine h1.subset ?_
    rintro P ⟨hP, hpP⟩
    have hne : P ≠ ⊥ := fun h0 => hp (by simpa [h0] using hpP)
    exact ⟨⟨P, hP.isPrime, hne⟩, by
      simpa [Ideal.dvd_span_singleton] using hpP, rfl⟩
  have : Finite {P : Ideal R // P.IsMaximal ∧ p ∈ P} := hfin.to_subtype
  let x : Ideal R → R := fun P => Classical.epsilon (fun θ => θ - σ θ ∉ P)
  obtain ⟨r, hr⟩ := Ideal.exists_forall_sub_mem_ideal
    (ι := {P : Ideal R // P.IsMaximal ∧ p ∈ P}) (I := fun P => P.1)
    (fun P Q hPQ => by
      have := P.2.1
      have := Q.2.1
      exact Ideal.isCoprime_iff_sup_eq.2
        (Ideal.IsMaximal.coprime_of_ne P.2.1 Q.2.1 (fun e => hPQ (Subtype.ext e))))
    (fun P => x P.1)
  refine ⟨r, fun P hP hpP hmem => ?_⟩
  have hsurj : Function.Surjective σ := fun y => ⟨σ y, hσ y⟩
  have := hP
  have hQ : (P.comap σ).IsMaximal := Ideal.comap_isMaximal_of_surjective σ hsurj
  have hpQ : p ∈ P.comap σ := by rw [Ideal.mem_comap, hσp]; exact hpP
  have hx : x (P.comap σ) = x P := by
    have : (fun θ => θ - σ θ ∉ P.comap σ) = (fun θ => θ - σ θ ∉ P) := by
      funext θ
      rw [Ideal.mem_comap, map_sub, hσ, ← neg_sub, Ideal.neg_mem_iff]
    simp only [x, this]
  have h1 : r - x P ∈ P := hr ⟨P, hP, hpP⟩
  have h2 : r - x (P.comap σ) ∈ P.comap σ := hr ⟨_, hQ, hpQ⟩
  rw [hx, Ideal.mem_comap, map_sub] at h2
  have h3 : x P - σ (x P) ∉ P := Classical.epsilon_spec (h P hP)
  apply h3
  have : x P - σ (x P) = (r - σ r) - (r - x P) + (σ r - σ (x P)) := by ring
  rw [this]
  exact add_mem (sub_mem hmem h1) h2

theorem prod_norm_sq {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {ι : Type} [Fintype ι]
    (φ : ι → E →+* ℂ) (hφ : Function.Bijective (fun v => InfinitePlace.mk (φ v))) (δ : 𝓞 E) :
    ∏ v, ‖φ v (δ : E)‖ ^ 2 = ((Algebra.norm ℤ δ).natAbs : ℝ) := by
  have h1 := InfinitePlace.prod_eq_abs_norm (δ : E)
  rw [← hφ.prod_comp (fun w => w (δ : E) ^ w.mult)] at h1
  simp only [IsTotallyComplex.mult_eq, InfinitePlace.apply] at h1
  rw [h1, ← Algebra.coe_norm_int, Nat.cast_natAbs]
  push_cast
  rfl

theorem exists_skew_norm_coprime : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (ι : Type) [Fintype ι] (φ : ι → E →+* ℂ), Function.Bijective (fun v => InfinitePlace.mk (φ v)) → ∀ p : ℕ, p.Prime → ∃ (δ : 𝓞 E) (N : ℕ), star (δ : E) = -(δ : E) ∧ ¬ p ∣ N ∧ ∏ v, ‖φ v (δ : E)‖ ^ 2 = N := by
  intro E _ _ _ hE ι _ φ hφ p hp
  have := hE.1
  let σ : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (starRingEnd E)
  have hσ : ∀ x, ((σ x : 𝓞 E) : E) = star (x : E) := fun x => rfl
  have hσσ : ∀ x, σ (σ x) = x := fun x => RingOfIntegers.ext (by rw [hσ, hσ, star_star])
  obtain ⟨θ, hθ⟩ := exists_sub_notMem σ hσσ (p := (p : 𝓞 E)) (by exact_mod_cast hp.ne_zero)
    (map_natCast σ p) (fun P hP => by
      obtain ⟨θ, t, ht, hm⟩ := hE.2.2 P hP
      have : σ θ = t := RingOfIntegers.ext (by rw [hσ]; exact ht.symm)
      exact ⟨θ, by rwa [this]⟩)
  refine ⟨θ - σ θ, (Algebra.norm ℤ (θ - σ θ)).natAbs, ?_, ?_, prod_norm_sq φ hφ _⟩
  · rw [← hσ, map_sub σ, hσσ, ← neg_sub θ]
    exact map_neg (algebraMap (𝓞 E) E) _
  · intro hd
    rw [← Ideal.absNorm_span_singleton] at hd
    obtain ⟨P, hP, hu, hdv⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm
      (Nat.prime_iff_prime_int.1 hp) _ (Int.natCast_dvd_natCast.2 hd)
    refine hθ P hP ?_ (Ideal.dvd_span_singleton.1 hdv)
    have : (p : ℤ) ∈ Ideal.under ℤ P := hu ▸ Ideal.mem_span_singleton_self _
    simpa [Ideal.mem_comap] using this

end GlobalTheory.RadCov.SkewUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSkewIntegerNormCoprimePrimeStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_skew_integer_norm_coprime_prime : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (ι : Type) [Fintype ι] (φ : ι → E →+* ℂ), Function.Bijective (fun v => InfinitePlace.mk (φ v)) → ∀ p : ℕ, p.Prime → ∃ (δ : 𝓞 E) (N : ℕ), star (δ : E) = -(δ : E) ∧ ¬ p ∣ N ∧ ∏ v, ‖φ v (δ : E)‖ ^ 2 = N := by
  first | exact @GlobalTheory.RadCov.SkewUnit.exists_skew_norm_coprime | exact GlobalTheory.RadCov.SkewUnit.exists_skew_norm_coprime | (intros; apply GlobalTheory.RadCov.SkewUnit.exists_skew_norm_coprime <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnipotentDimEqSumPairs
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnipotentDimEqSumPairs
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadicalDimSum

theorem two_mul_pairs_add_sq {ι : Type} [LinearOrder ι] (s : Finset ι) (f : ι → ℕ) :
    2 * (∑ i ∈ s, ∑ k ∈ s.filter (fun k => i < k), f i * f k) + ∑ i ∈ s, f i ^ 2 = (∑ i ∈ s, f i) ^ 2 := by
  classical
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have hna : a ∉ s := fun h => lt_irrefl a (ha a h)
    have h2 : (insert a s).filter (fun k => a < k) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact lt_irrefl _
      · exact not_lt.mpr (ha x hx).le
    have h3 : ∑ i ∈ s, ∑ k ∈ (insert a s).filter (fun k => i < k), f i * f k
        = ∑ i ∈ s, ∑ k ∈ s.filter (fun k => i < k), f i * f k + (∑ i ∈ s, f i) * f a := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.filter_insert, if_pos (ha i hi), Finset.sum_insert (by simp [hna])]
      ring
    simp only [Finset.sum_insert hna]
    rw [h2, Finset.sum_empty, h3,
      show (f a + ∑ i ∈ s, f i) ^ 2 = f a ^ 2 + 2 * (∑ i ∈ s, f i) * f a + (∑ i ∈ s, f i) ^ 2 by ring,
      ← ih]
    ring

theorem sum_shift_eq (N : ℕ) (r : ℕ → ℕ) (hr : ∀ b, N ≤ b → r b = 0) (b : ℕ) :
    ∑ c ∈ range N, r (b + c + 1) = ∑ k ∈ (range N).filter (fun k => b < k), r k := by
  have e : ∑ c ∈ range N, r (b + c + 1) = ∑ k ∈ Ico (b + 1) (b + 1 + N), r k := by
    rw [Finset.sum_Ico_eq_sum_range, show b + 1 + N - (b + 1) = N by omega]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    congr 1
    omega
  rw [e]
  symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    simp only [Finset.mem_Ico]
    omega
  · intro k hk hk'
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, not_and, not_lt] at hk hk'
    apply hr
    by_contra h
    exact absurd (hk' (by omega)) (by omega)

theorem dimN_eq_sum_pairs : ∀ (n a : ℕ) (j : Fin a → ℕ) (r : ℕ → ℕ), (∀ i : Fin a, r i = j i ∧ r (2 * a - i) = j i) → r a = n - 2 * ∑ i, j i → (∀ b, 2 * a + 1 ≤ b → r b = 0) → dimN n j = ∑ c ∈ Finset.range (2 * a + 1), ∑ b ∈ Finset.range (2 * a + 1), r b * r (b + c + 1) := by
  intro n a j r hj ha hz
  have hpairs : ∑ c ∈ range (2 * a + 1), ∑ b ∈ range (2 * a + 1), r b * r (b + c + 1)
      = ∑ b ∈ range (2 * a + 1), ∑ k ∈ (range (2 * a + 1)).filter (fun k => b < k), r b * r k := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [← Finset.mul_sum, ← Finset.mul_sum, sum_shift_eq (2 * a + 1) r hz b]
  have hsum : ∑ b ∈ range (2 * a + 1), r b = 2 * ∑ i, j i + (n - 2 * ∑ i, j i) := by
    have h : ∑ b ∈ range (2 * a + 1), r b = ∑ i : Fin a, (r i + r (2 * a - i)) + r a :=
      GlobalTheory.DoubledFlag.sum_range_double a r
    rw [h, ha]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [(hj i).1, (hj i).2]
    ring
  have hsq : ∑ b ∈ range (2 * a + 1), r b ^ 2 = 2 * ∑ i, j i ^ 2 + (n - 2 * ∑ i, j i) ^ 2 := by
    have h : ∑ b ∈ range (2 * a + 1), r b ^ 2 = ∑ i : Fin a, (r i ^ 2 + r (2 * a - i) ^ 2) + r a ^ 2 :=
      GlobalTheory.DoubledFlag.sum_range_double a (fun b => r b ^ 2)
    rw [h, ha]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [(hj i).1, (hj i).2]
    ring
  have h1 := two_mul_pairs_add_sq (range (2 * a + 1)) r
  have h2 := two_mul_pairs_add_sq (univ : Finset (Fin a)) j
  rw [hsum, hsq] at h1
  rw [hpairs, GlobalTheory.FlagMeas.dimN]
  nlinarith [h1, h2]

end GlobalTheory.RadicalDimSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnipotentDimEqSumPairsStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicFlagUnipotentDim_eq_sum_pairs : ∀ (n a : ℕ) (j : Fin a → ℕ) (r : ℕ → ℕ), (∀ i : Fin a, r i = j i ∧ r (2 * a - i) = j i) → r a = n - 2 * ∑ i, j i → (∀ b, 2 * a + 1 ≤ b → r b = 0) → dimN n j = ∑ c ∈ Finset.range (2 * a + 1), ∑ b ∈ Finset.range (2 * a + 1), r b * r (b + c + 1) := by
  first | exact @GlobalTheory.RadicalDimSum.dimN_eq_sum_pairs | exact GlobalTheory.RadicalDimSum.dimN_eq_sum_pairs | (intros; apply GlobalTheory.RadicalDimSum.dimN_eq_sum_pairs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealComplexSpanOrthonormalSkewFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealComplexSpanOrthonormalSkewFamily
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.SkewSpan

theorem skew_conj {n : ℕ} (ε : Fin n → Bool) {B : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.REAL.inG ε B) : Formalism.REAL.Jm ε * Bᴴ * Formalism.REAL.Jm ε = -B := by
  have h' : Bᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * B) := eq_neg_of_add_eq_zero_left h
  rw [Matrix.mul_assoc, h', Matrix.mul_neg, ← Matrix.mul_assoc, Formalism.REAL.Jm_mul_self,
    Matrix.one_mul]

theorem trace_twisted {n : ℕ} (ε : Fin n → Bool) {B : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.REAL.inG ε B) (X : Matrix (Fin n) (Fin n) ℂ) :
    (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε * Bᴴ).trace = - starRingEnd ℂ (X * Bᴴ).trace := by
  have h1 : (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε * Bᴴ).trace
      = (Xᴴ * (Formalism.REAL.Jm ε * Bᴴ * Formalism.REAL.Jm ε)).trace := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have h2 : starRingEnd ℂ (X * Bᴴ).trace = (Xᴴ * B).trace := by
    rw [starRingEnd_apply, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm]
  rw [h1, h2, skew_conj ε h, Matrix.mul_neg, Matrix.trace_neg]

theorem real_span (n d : ℕ) (ε : Fin n → Bool) (B : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (s : Set (Fin d)) (hB : ∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0)
    (hG : ∀ i, Formalism.REAL.inG ε (B i)) :
    (∀ X, (X ∈ Submodule.span ℂ (B '' s) ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (B '' s)) ∧
    (∀ X ∈ Submodule.span ℂ (B '' s), ∀ i, i ∉ s → (X * (B i)ᴴ).trace = 0) ∧
    ∀ X i, (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε * (B i)ᴴ).trace
      = - starRingEnd ℂ (X * (B i)ᴴ).trace := by
  have h2 : ∀ X ∈ Submodule.span ℂ (B '' s), ∀ i, i ∉ s → (X * (B i)ᴴ).trace = 0 := by
    intro X hX i hi
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      rw [hB, if_neg]
      rintro rfl
      exact hi hk
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.add_mul, Matrix.trace_add, hx, hy, add_zero]
    | smul c x _ hx => rw [Matrix.smul_mul, Matrix.trace_smul, hx, smul_zero]
  have hexp : ∀ X ∈ Submodule.span ℂ (B '' s), X = ∑ i, (X * (B i)ᴴ).trace • B i := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      simp [hB]
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Matrix.add_mul, Matrix.trace_add, add_smul, Finset.sum_add_distrib]
      rw [← hx, ← hy]
    | smul c x _ hx =>
      simp only [Matrix.smul_mul, Matrix.trace_smul, smul_assoc, ← Finset.smul_sum]
      rw [← hx]
  refine ⟨fun X => ⟨?_, ?_⟩, h2, fun X i => trace_twisted ε (hG i) X⟩
  · rintro ⟨hX, hXG⟩
    rw [hexp X hX]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : i ∈ s
    · have h3 := trace_twisted ε (hG i) X
      rw [skew_conj ε hXG, Matrix.neg_mul, Matrix.trace_neg, neg_inj] at h3
      have h4 : (X * (B i)ᴴ).trace = (((X * (B i)ᴴ).trace.re : ℝ) : ℂ) :=
        (Complex.conj_eq_iff_re.mp h3.symm).symm
      rw [h4, Complex.coe_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    · rw [h2 X hX i hi, zero_smul]
      exact Submodule.zero_mem _
  · intro hX
    refine ⟨Submodule.span_le_restrictScalars ℝ ℂ _ hX, ?_⟩
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      exact hG k
    | zero => simp [Formalism.REAL.inG]
    | add x y _ _ hx hy =>
      unfold Formalism.REAL.inG at *
      rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hx, hy,
        add_zero]
    | smul c x _ hx =>
      unfold Formalism.REAL.inG at *
      rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add,
        hx, smul_zero]

end GlobalTheory.SkewSpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealComplexSpanOrthonormalSkewFamilyStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_complex_span_orthonormal_skew_family : ∀ (n d : ℕ) (ε : Fin n → Bool) (B : Fin d → Matrix (Fin n) (Fin n) ℂ) (s : Set (Fin d)), (∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0) → (∀ i, Formalism.REAL.inG ε (B i)) → (∀ X, (X ∈ Submodule.span ℂ (B '' s) ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (B '' s)) ∧ (∀ X ∈ Submodule.span ℂ (B '' s), ∀ i, i ∉ s → (X * (B i)ᴴ).trace = 0) ∧ ∀ X i, (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε * (B i)ᴴ).trace = - starRingEnd ℂ (X * (B i)ᴴ).trace := by
  first | exact @GlobalTheory.SkewSpan.real_span | exact GlobalTheory.SkewSpan.real_span | (intros; apply GlobalTheory.SkewSpan.real_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HomLatticeCovolumeEmbeddingFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HomLatticeCovolumeEmbeddingFamily
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

noncomputable section

namespace GlobalTheory.HomCovolumeFamily

attribute [local instance] GlobalTheory.HomCovolume.haar_two GlobalTheory.HomCovolume.haar_three

theorem exists_twist {E : Type} [Field E] (φ : E →+* ℂ) :
    ∃ σ : ℂ ≃ₐ[ℝ] ℂ, (∀ x, ‖σ x‖ = ‖x‖) ∧ ∀ x, (InfinitePlace.mk φ).embedding x = σ (φ x) := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · exact ⟨AlgEquiv.refl, fun _ => rfl, fun x => by rw [h]; rfl⟩
  · exact ⟨Complex.conjAe, fun x => by simp, fun x => by rw [h]; rfl⟩

theorem det_map_twist {j : ℕ} (σ : ℂ ≃ₐ[ℝ] ℂ) (A : Matrix (Fin j) (Fin j) ℂ) :
    (A.map σ).det = σ A.det := by
  have := RingHom.map_det (σ : ℂ →+* ℂ) A
  rw [RingHom.mapMatrix_apply] at this
  exact this.symm

theorem map_inv_twist {j : ℕ} (σ : ℂ ≃ₐ[ℝ] ℂ) (A : Matrix (Fin j) (Fin j) ℂ) (hA : A.det ≠ 0) :
    (A⁻¹).map σ = (A.map σ)⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hA.isUnit, Matrix.map_one _ (map_zero _) (map_one _)]

variable {E : Type} [Field E] [NumberField E]

theorem detNorm_twist {ι : Type} [Fintype ι] (e : ι ≃ InfinitePlace E) (σ : ι → ℂ ≃ₐ[ℝ] ℂ)
    (hσ : ∀ v x, ‖σ v x‖ = ‖x‖) {j : ℕ} (G : ι → Matrix (Fin j) (Fin j) ℂ) :
    detNorm E j (fun w => Matrix.of.symm ((G (e.symm w)).map (σ (e.symm w)))⁻¹) =
      (∏ v, ‖(G v).det‖ ^ 2)⁻¹ := by
  change ∏ w, ‖(Matrix.of (Matrix.of.symm ((G (e.symm w)).map (σ (e.symm w)))⁻¹)).det‖ ^ 2 = _
  rw [← Finset.prod_inv_distrib, ← e.prod_comp]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', norm_inv,
    inv_pow, det_map_twist, hσ]

theorem covAt_eq (hE : IsTotallyComplex E) {j : ℕ} (Λ : Submodule (𝓞 E) (Fin j → E))
    (hΛ : Submodule.IsFullLattice E Λ) (g : MatInf E j) (hg : 0 < detNorm E j g) :
    covAt E j (latAt E j Λ g) = covStd j Λ / detNorm E j g := by
  obtain ⟨κ, -, h⟩ := (GlobalTheory.LatFacts.lattice_facts E hE j).1 Λ hΛ
  have h1 : detNorm E j (fun _ a b => if a = b then 1 else 0) = 1 := by
    have h2 : (Matrix.of fun a b : Fin j => if a = b then (1 : ℂ) else 0) = 1 := rfl
    simp only [detNorm, h2, Matrix.det_one, norm_one, one_pow, Finset.prod_const_one]
  have h3 : covStd j Λ = κ := ((h _ (h1.symm ▸ one_pos)).2.1.trans (congrArg (κ / ·) h1)).trans (div_one κ)
  rw [(h g hg).2.1, h3]

theorem homCovolume_family : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (ι : Type) [Fintype ι] (φ : ι → E →+* ℂ), Function.Bijective (fun v => InfinitePlace.mk (φ v)) → ∀ (r s : ℕ) (Λ : Submodule (𝓞 E) (Fin r → E)) (Λ' : Submodule (𝓞 E) (Fin s → E)), Submodule.IsFullLattice E Λ → Submodule.IsFullLattice E Λ' → ∀ (G : ι → Matrix (Fin r) (Fin r) ℂ) (G' : ι → Matrix (Fin s) (Fin s) ℂ), (∀ v, (G v).det ≠ 0) → (∀ v, (G' v).det ≠ 0) → ∀ L : Submodule ℤ (ι → Fin r → Fin s → ℂ), (∀ z, z ∈ L ↔ ∃ T : Matrix (Fin r) (Fin s) E, (∀ y ∈ Λ', T *ᵥ y ∈ Λ) ∧ ∀ v, Matrix.of (z v) = G v * T.map (φ v) * (G' v)⁻¹) → ∃ _ : DiscreteTopology L, IsZLattice ℝ L ∧ ZLattice.covolume L volume = (covStd r Λ * ∏ v, ‖(G v).det‖ ^ 2) ^ s * (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * s) / (covStd s Λ' * ∏ v, ‖(G' v).det‖ ^ 2)) ^ r := by
  intro E _ _ hE ι _ φ hφ r s Λ Λ' hΛ hΛ' G G' hG hG' L hL
  let e : ι ≃ InfinitePlace E := Equiv.ofBijective _ hφ
  choose σ hσ hσφ using fun v => exists_twist (φ v)
  have he : ∀ v x, (e v).embedding x = σ v (φ v x) := hσφ
  let Φ : (ι → Fin r → Fin s → ℂ) ≃ₗ[ℝ] (InfinitePlace E → Fin r → Fin s → ℂ) :=
    { toFun := fun z w i k => σ (e.symm w) (z (e.symm w) i k)
      invFun := fun y v i k => (σ v).symm (y (e v) i k)
      map_add' := fun _ _ => by ext; simp
      map_smul' := fun c z => funext fun w => funext fun i => funext fun k =>
        (σ (e.symm w)).toLinearEquiv.map_smul c (z (e.symm w) i k)
      left_inv := fun _ => by ext; simp
      right_inv := fun _ => by ext; simp }
  have hΦ : ∀ z v i k, Φ z (e v) i k = σ v (z v i k) := fun z v i k => by
    change σ (e.symm (e v)) (z (e.symm (e v)) i k) = _
    rw [e.symm_apply_apply]
  have hmp : MeasurePreserving Φ.toContinuousLinearEquiv volume volume := by
    refine GlobalTheory.HomCovolume.measurePreserving_of_ball _ _ _ (fun x => ?_) ?_
    · simp only [pi_norm_le_iff_of_nonneg zero_le_one]
      change (∀ w i k, ‖Φ x w i k‖ ≤ 1) ↔ _
      rw [e.forall_congr_right.symm]
      simp only [hΦ, hσ]
    · simp [volume_pi_closedBall _ zero_le_one, Fintype.card_congr e]
  have hD : 0 < ∏ v, ‖(G v).det‖ ^ 2 := Finset.prod_pos fun v _ => pow_pos (norm_pos_iff.2 (hG v)) _
  have hD' : 0 < ∏ v, ‖(G' v).det‖ ^ 2 := Finset.prod_pos fun v _ => pow_pos (norm_pos_iff.2 (hG' v)) _
  have hn := detNorm_twist e σ hσ G
  have hn' := detNorm_twist e σ hσ G'
  have hp := hn ▸ inv_pos.2 hD
  have hp' := hn' ▸ inv_pos.2 hD'
  let L' : Submodule ℤ (InfinitePlace E → Fin r → Fin s → ℂ) :=
    L.comap (Φ.symm.toLinearMap.restrictScalars ℤ)
  have hLL : ∀ z, z ∈ L ↔ Φ z ∈ L' := fun z => by
    change _ ↔ Φ.symm (Φ z) ∈ L
    rw [Φ.symm_apply_apply]
  have hmain := GlobalTheory.HomCovolume.homCovolume E hE r s Λ Λ' hΛ hΛ' _ _ hp hp' L' (fun y => by
    obtain ⟨z, rfl⟩ := Φ.surjective y
    rw [← hLL, hL]
    refine exists_congr fun T => and_congr Iff.rfl ?_
    rw [← e.forall_congr_right]
    refine forall_congr' fun v => ?_
    have h1 : Matrix.of (Φ z (e v)) = (Matrix.of (z v)).map (σ v) := by
      ext i k; exact hΦ z v i k
    have h2 : T.map (e v).embedding = (T.map (φ v)).map (σ v) := by
      ext i k; exact he v _
    have h3 : IsUnit ((G v).map (σ v)).det := by
      rw [det_map_twist]; exact ((map_ne_zero _).2 (hG v)).isUnit
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.symm_apply_apply, h1, h2,
      Matrix.nonsing_inv_nonsing_inv _ h3, ← map_inv_twist _ _ (hG' v), ← Matrix.map_mul, ← Matrix.map_mul]
    exact (Matrix.map_injective (σ v).injective).eq_iff.symm)
  rw [covAt_eq hE Λ hΛ _ hp, covAt_eq hE Λ' hΛ' _ hp', hn, hn', div_inv_eq_mul, div_inv_eq_mul] at hmain
  exact GlobalTheory.HomCovolume.HasCov.of_measurePreserving Φ.toContinuousLinearEquiv hmp hLL hmain

end GlobalTheory.HomCovolumeFamily
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HomLatticeCovolumeEmbeddingFamilyStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homLatticeCovolume_embedding_family : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (ι : Type) [Fintype ι] (φ : ι → E →+* ℂ), Function.Bijective (fun v => InfinitePlace.mk (φ v)) → ∀ (r s : ℕ) (Λ : Submodule (𝓞 E) (Fin r → E)) (Λ' : Submodule (𝓞 E) (Fin s → E)), Submodule.IsFullLattice E Λ → Submodule.IsFullLattice E Λ' → ∀ (G : ι → Matrix (Fin r) (Fin r) ℂ) (G' : ι → Matrix (Fin s) (Fin s) ℂ), (∀ v, (G v).det ≠ 0) → (∀ v, (G' v).det ≠ 0) → ∀ L : Submodule ℤ (ι → Fin r → Fin s → ℂ), (∀ z, z ∈ L ↔ ∃ T : Matrix (Fin r) (Fin s) E, (∀ y ∈ Λ', T *ᵥ y ∈ Λ) ∧ ∀ v, Matrix.of (z v) = G v * T.map (φ v) * (G' v)⁻¹) → ∃ _ : DiscreteTopology L, IsZLattice ℝ L ∧ ZLattice.covolume L volume = (covStd r Λ * ∏ v, ‖(G v).det‖ ^ 2) ^ s * (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * s) / (covStd s Λ' * ∏ v, ‖(G' v).det‖ ^ 2)) ^ r := by
  first | exact @GlobalTheory.HomCovolumeFamily.homCovolume_family | exact GlobalTheory.HomCovolumeFamily.homCovolume_family | (intros; apply GlobalTheory.HomCovolumeFamily.homCovolume_family <;> first | assumption | exact Submodule.IsFullLattice.toIsLattice)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryLeadingTermOfSkewLayer
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryLeadingTermOfSkewLayer
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov

theorem exists_unitary_of_skew_layer (R K : Type) [CommRing R] [Field K] [StarRing K]
    [Algebra R K] (n m : ℕ) (J : Matrix (Fin n) (Fin n) K)
    (A : ℕ → Submodule R (Matrix (Fin n) (Fin n) K)) (w : R)
    (hJ : Jᴴ = J) (hdet : J.det ≠ 0)
    (hw : algebraMap R K w + star (algebraMap R K w) = 1)
    (hA : ∀ c, A (c + 1) ≤ A c) (hm : A m = ⊥)
    (hmul : ∀ c, ∀ X ∈ A c, ∀ Y ∈ A 0, X * Y ∈ A (c + 1) ∧ Y * X ∈ A (c + 1))
    (_hadj : ∀ c, ∀ X ∈ A c, J⁻¹ * Xᴴ * J ∈ A c)
    (c : ℕ) (X : Matrix (Fin n) (Fin n) K) (hX : X ∈ A c) (hskew : J⁻¹ * Xᴴ * J = -X) :
    ∃ Y ∈ A (c + 1), (1 + X + Y)ᴴ * J * (1 + X + Y) = J := by
  classical
  have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hdet
  have cL : ∀ B : Matrix (Fin n) (Fin n) K, J * (J⁻¹ * B) = B :=
    fun B => Matrix.mul_nonsing_inv_cancel_left J B hu
  have cL' : ∀ B : Matrix (Fin n) (Fin n) K, J⁻¹ * (J * B) = B :=
    fun B => Matrix.nonsing_inv_mul_cancel_left J B hu
  have cR : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hu
  have cR' : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hu
  have hJi : (J⁻¹)ᴴ = J⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hJ]
  have hanti : Antitone A := antitone_nat_of_succ_le hA
  have to0 : ∀ {d : ℕ} {M : Matrix (Fin n) (Fin n) K}, M ∈ A d → M ∈ A 0 :=
    fun h => hanti (Nat.zero_le _) h
  have smem : ∀ (r : R) {d : ℕ} {M : Matrix (Fin n) (Fin n) K}, M ∈ A d →
      algebraMap R K r • M ∈ A d := by
    intro r d M h
    rw [algebraMap_smul]
    exact (A d).smul_mem r h
  set β : K := algebraMap R K w with hβ
  have hst : star β = 1 - β := by rw [← hw]; ring

  have key : ∀ k : ℕ, ∃ Y ∈ A (c + 1),
      J⁻¹ * (1 + X + Y)ᴴ * J * (1 + X + Y) - 1 ∈ A (c + 1 + k) := by
    intro k
    induction k with
    | zero =>
      refine ⟨0, (A (c + 1)).zero_mem, ?_⟩
      have hX' : Xᴴ = -(J * (X * J⁻¹)) := by
        calc Xᴴ = J * ((J⁻¹ * Xᴴ * J) * J⁻¹) := by
              simp only [mul_assoc, cR, mul_one, cL]
          _ = -(J * (X * J⁻¹)) := by rw [hskew]; simp only [neg_mul, mul_neg]
      have h0 : J⁻¹ * (1 + X + 0)ᴴ * J * (1 + X + 0) - 1 = -(X * X) := by
        simp only [add_zero, Matrix.conjTranspose_add, Matrix.conjTranspose_one, hX']
        simp only [mul_add, add_mul, mul_one, one_mul, mul_neg, neg_mul, mul_assoc, cL', cR']
        abel
      rw [h0, Nat.add_zero]
      exact (A (c + 1)).neg_mem (hmul c X hX X (to0 hX)).1
    | succ k ih =>
      obtain ⟨Y, hY, hE⟩ := ih
      set g := 1 + X + Y with hg
      set E := J⁻¹ * gᴴ * J * g - 1 with hEdef
      have hEE : E * E ∈ A (c + 1 + (k + 1)) := (hmul (c + 1 + k) E hE E (to0 hE)).1
      have hEEE : E * (E * E) ∈ A (c + 1 + (k + 1)) :=
        (hmul (c + 1 + k) E hE (E * E) (to0 hEE)).1
      refine ⟨Y - β • (g * E), ?_, ?_⟩
      · have hEc : E ∈ A (c + 1) := hanti (by omega) hE
        have hgE : g * E ∈ A (c + 1) := by
          rw [hg, add_mul, add_mul, one_mul]
          exact add_mem (add_mem hEc (hmul c X hX E (to0 hE)).1)
            (hanti (by omega) (hmul (c + 1) Y hY E (to0 hE)).1)
        exact sub_mem hY (smem w hgE)
      · have hgeq : 1 + X + (Y - β • (g * E)) = g - β • (g * E) := by rw [hg]; abel
        rw [hgeq]

        have hEH : J⁻¹ * Eᴴ * J = E := by
          rw [hEdef]
          simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
            Matrix.conjTranspose_conjTranspose, hJi, hJ, sub_mul, mul_sub, mul_one, mul_assoc, cR']
        have h1 : J⁻¹ * (Eᴴ * (gᴴ * J)) = E * (J⁻¹ * (gᴴ * J)) := by
          calc J⁻¹ * (Eᴴ * (gᴴ * J)) = (J⁻¹ * Eᴴ * J) * (J⁻¹ * (gᴴ * J)) := by
                simp only [mul_assoc, cL]
            _ = E * (J⁻¹ * (gᴴ * J)) := by rw [hEH]
        have hP' : J⁻¹ * (g - β • (g * E))ᴴ * J
            = J⁻¹ * (gᴴ * J) - star β • (E * (J⁻¹ * (gᴴ * J))) := by
          simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
            mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_assoc, h1]
        have hPg0 : J⁻¹ * (gᴴ * (J * g)) = 1 + E := by
          rw [hEdef]; simp only [mul_assoc]; abel
        have hPg : ∀ M, J⁻¹ * (gᴴ * (J * (g * M))) = M + E * M := by
          intro M
          rw [hEdef]; simp only [sub_mul, one_mul, mul_assoc]; abel
        have hid : J⁻¹ * (g - β • (g * E))ᴴ * J * (g - β • (g * E)) - 1
            = (β - β * β - 1) • (E * E) + (β - β * β) • (E * (E * E)) := by
          rw [hP']
          simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, mul_assoc, hPg, hPg0,
            mul_add, mul_one, smul_add, hst]
          module
        have s1 : β - β * β - 1 = algebraMap R K (w - w * w - 1) := by simp [hβ]
        have s2 : β - β * β = algebraMap R K (w - w * w) := by simp [hβ]
        rw [hid, s1, s2]
        exact add_mem (smem _ hEE) (smem _ hEEE)
  obtain ⟨Y, hY, hEm⟩ := key m
  refine ⟨Y, hY, ?_⟩
  have hz : J⁻¹ * (1 + X + Y)ᴴ * J * (1 + X + Y) - 1 ∈ A m := hanti (by omega) hEm
  rw [hm, Submodule.mem_bot, sub_eq_zero] at hz
  calc (1 + X + Y)ᴴ * J * (1 + X + Y)
      = J * (J⁻¹ * (1 + X + Y)ᴴ * J * (1 + X + Y)) := by simp only [mul_assoc, cL]
    _ = J := by rw [hz, mul_one]

end GlobalTheory.RadCov
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryLeadingTermOfSkewLayerStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_leading_term_of_skew_layer : ∀ (R K : Type) [CommRing R] [Field K] [StarRing K] [Algebra R K] (n m : ℕ) (J : Matrix (Fin n) (Fin n) K) (A : ℕ → Submodule R (Matrix (Fin n) (Fin n) K)) (w : R), Jᴴ = J → J.det ≠ 0 → algebraMap R K w + star (algebraMap R K w) = 1 → (∀ c, A (c + 1) ≤ A c) → A m = ⊥ → (∀ c, ∀ X ∈ A c, ∀ Y ∈ A 0, X * Y ∈ A (c + 1) ∧ Y * X ∈ A (c + 1)) → (∀ c, ∀ X ∈ A c, J⁻¹ * Xᴴ * J ∈ A c) → ∀ c, ∀ X ∈ A c, J⁻¹ * Xᴴ * J = -X → ∃ Y ∈ A (c + 1), (1 + X + Y)ᴴ * J * (1 + X + Y) = J := by
  first | exact @GlobalTheory.RadCov.exists_unitary_of_skew_layer | exact GlobalTheory.RadCov.exists_unitary_of_skew_layer | (intros; apply GlobalTheory.RadCov.exists_unitary_of_skew_layer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdLayerHeightQuotientsEqSq
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdLayerHeightQuotientsEqSq
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.HtProd

theorem prod_shift_eq (N : ℕ) (F : ℕ → ℕ → ℝ) (hF : ∀ b b', N ≤ b' → F b b' = 1) :
    ∏ c ∈ Finset.range N, ∏ b ∈ Finset.range N, F b (b + c + 1) =
      ∏ b ∈ Finset.range N, ∏ b' ∈ Finset.range N, if b < b' then F b b' else 1 := by
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [← Finset.prod_filter]
  have h1 : ∏ c ∈ Finset.range N, F b (b + c + 1) = ∏ x ∈ Finset.Ico (b + 1) (b + 1 + N), F b x := by
    rw [Finset.prod_Ico_eq_prod_range]
    simp only [Nat.add_sub_cancel_left]
    refine Finset.prod_congr rfl fun c _ => ?_
    congr 1
    omega
  rw [h1]
  symm
  apply Finset.prod_subset
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hx ⊢
    omega
  · intro x hx hx'
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hx hx'
    exact hF _ _ (by omega)

theorem prod_range_split (a : ℕ) (g : ℕ → ℝ) :
    ∏ b ∈ Finset.range (2 * a + 1), g b = (∏ i : Fin a, g i) * g a * ∏ i : Fin a, g (2 * a - i) := by
  have e : 2 * a + 1 = (a + 1) + a := by omega
  rw [e, Finset.prod_range_add, Finset.prod_range_succ, Fin.prod_univ_eq_prod_range g a,
    Fin.prod_univ_eq_prod_range (fun i => g (2 * a - i)) a, ← Finset.prod_range_reflect (fun i => g (2 * a - i)) a]
  congr 1
  refine Finset.prod_congr rfl fun x hx => ?_
  rw [Finset.mem_range] at hx
  congr 1
  omega

theorem prod_symm_split {a : ℕ} (P : Fin a → Fin a → ℝ) (hP : ∀ i k, P i k = P k i) :
    ∏ i, ∏ k, P i k = (∏ i, ∏ k, if i < k then P i k else 1) ^ 2 * ∏ i, P i i := by
  have h1 : ∀ i k, P i k = (if i < k then P i k else 1) * (if k < i then P k i else 1) *
      (if i = k then P i k else 1) := by
    intro i k
    rcases lt_trichotomy i k with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.mpr h.le, hP i k]
  rw [Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun k _ => h1 i k]
  simp only [Finset.prod_mul_distrib]
  rw [Finset.prod_comm (f := fun i k => if k < i then P k i else 1), sq]
  simp

theorem htProd : ∀ (n f a : ℕ) (j : Fin a → ℕ) (r : ℕ → ℕ) (τ : Fin a → ℝ) (h : ℕ → ℝ),
    (∀ i : Fin a, r i = j i ∧ r (2 * a - i) = j i) → r a = n - 2 * ∑ i, j i →
    (∀ b, 2 * a + 1 ≤ b → r b = 0) →
    (∀ i : Fin a, 0 < τ i ∧ h i = τ i ^ (2 * f * j i) ∧ h (2 * a - i) = (τ i ^ (2 * f * j i))⁻¹) →
    h a = 1 → (∀ b, 2 * a + 1 ≤ b → h b = 1) →
    ∏ c ∈ Finset.range (2 * a + 1), ∏ b ∈ Finset.range (2 * a + 1),
      h b ^ r (b + c + 1) / h (b + c + 1) ^ r b = layerProd n f j τ id ^ 2 := by
  intro n f a j r τ h hr hra hr0 hτ ha h1
  rw [prod_shift_eq (2 * a + 1) (fun b b' => h b ^ r b' / h b' ^ r b)
    (fun b b' hb => by simp [hr0 b' hb, h1 b' hb])]
  unfold layerProd
  rw [← hra]
  simp only [prod_range_split, id]
  have c1 : ∀ i : Fin a, (i : ℕ) < a := fun i => i.2
  have c2 : ∀ i k : Fin a, (i : ℕ) < 2 * a - k := fun i k => by omega
  have c3 : ∀ k : Fin a, ¬ a < (k : ℕ) := fun k => by omega
  have c4 : ∀ k : Fin a, a < 2 * a - k := fun k => by omega
  have c5 : ∀ i k : Fin a, ¬ 2 * a - i < (k : ℕ) := fun i k => by omega
  have c6 : ∀ i : Fin a, ¬ 2 * a - i < a := fun i => by omega
  have c7 : ∀ i k : Fin a, (2 * a - i < 2 * a - k) ↔ k < i := fun i k => by
    rw [Fin.lt_def]; omega
  have c8 : ∀ i k : Fin a, ((i : ℕ) < k) ↔ i < k := fun i k => Iff.rfl
  simp only [c1, c2, c3, c4, c5, c6, c7, c8, lt_irrefl, if_true, if_false, ha,
    fun i => (hr i).1, fun i => (hr i).2, fun i => (hτ i).2.1, fun i => (hτ i).2.2,
    Finset.prod_const_one, one_mul, mul_one, one_pow, div_one, Finset.prod_mul_distrib,
    Finset.prod_filter]
  have d1 : ∀ i k : Fin a, (τ i ^ (2 * f * j i)) ^ j k / (τ k ^ (2 * f * j k)) ^ j i =
      (τ i / τ k) ^ (2 * j i * j k * f) := fun i k => by
    rw [div_pow, ← pow_mul, ← pow_mul]
    congr 2 <;> ring
  have d2 : ∀ i k : Fin a, (τ i ^ (2 * f * j i)) ^ j k / (τ k ^ (2 * f * j k))⁻¹ ^ j i =
      (τ i * τ k) ^ (2 * j i * j k * f) := fun i k => by
    rw [inv_pow, div_inv_eq_mul, mul_pow, ← pow_mul, ← pow_mul]
    congr 2 <;> ring
  have d3 : ∀ i k : Fin a, (τ i ^ (2 * f * j i))⁻¹ ^ j k / (τ k ^ (2 * f * j k))⁻¹ ^ j i =
      (τ k / τ i) ^ (2 * j k * j i * f) := fun i k => by
    rw [← d1, inv_pow, inv_pow, div_inv_eq_mul, mul_comm, div_eq_mul_inv]
  have d4 : ∀ i : Fin a, (τ i ^ (2 * f * j i)) ^ r a = τ i ^ (2 * j i * r a * f) := fun i => by
    rw [← pow_mul]
    congr 1
    ring
  have d5 : ∀ i : Fin a, 1 / (τ i ^ (2 * f * j i))⁻¹ ^ r a = τ i ^ (2 * j i * r a * f) := fun i => by
    rw [← d4, inv_pow, one_div, inv_inv]
  have d6 : ∀ i : Fin a, (τ i * τ i) ^ (2 * j i * j i * f) = ((τ i ^ 2) ^ (j i ^ 2 * f)) ^ 2 := fun i => by
    rw [← sq, ← pow_mul (τ i ^ 2)]
    congr 1
    ring
  simp only [d1, d2, d3, d4, d5]
  rw [Finset.prod_comm (f := fun i k => if k < i then (τ k / τ i) ^ (2 * j k * j i * f) else 1),
    prod_symm_split (fun i k => (τ i * τ k) ^ (2 * j i * j k * f))
      (fun i k => by rw [mul_comm (τ i)]; congr 1; ring)]
  simp only [d6, Finset.prod_pow]
  ring

end GlobalTheory.HtProd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdLayerHeightQuotientsEqSqStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_layer_height_quotients_eq_sq : ∀ (n f a : ℕ) (j : Fin a → ℕ) (r : ℕ → ℕ) (τ : Fin a → ℝ) (h : ℕ → ℝ), (∀ i : Fin a, r i = j i ∧ r (2 * a - i) = j i) → r a = n - 2 * ∑ i, j i → (∀ b, 2 * a + 1 ≤ b → r b = 0) → (∀ i : Fin a, 0 < τ i ∧ h i = τ i ^ (2 * f * j i) ∧ h (2 * a - i) = (τ i ^ (2 * f * j i))⁻¹) → h a = 1 → (∀ b, 2 * a + 1 ≤ b → h b = 1) → ∏ c ∈ Finset.range (2 * a + 1), ∏ b ∈ Finset.range (2 * a + 1), h b ^ r (b + c + 1) / h (b + c + 1) ^ r b = layerProd n f j τ id ^ 2 := by
  first | exact @GlobalTheory.HtProd.htProd | exact GlobalTheory.HtProd.htProd | (intros; apply GlobalTheory.HtProd.htProd <;> assumption)
end
end
