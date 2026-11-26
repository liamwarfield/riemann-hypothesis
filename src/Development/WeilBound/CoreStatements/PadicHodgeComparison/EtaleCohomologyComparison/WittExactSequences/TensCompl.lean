module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeThirdProperty
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientOfEigencharacter
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColSqOfKerBasic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockDeterminantLaw
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousAtOfSqBound

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConstOfRhoEq
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.BMid

theorem exists_const_of_rho_eq : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [CommRing K] (K₁ : Type) [CommRing K₁] (K₂ : Type) [CommRing K₂] (K₃ : Type) [CommRing K₃] (f g : K) (i₁ : Polynomial K →+* K₁) (i₂ : Polynomial K →+* K₂) (i₃ : K[T;T⁻¹] →+* K₃) (ρ₁ : K₁ →+* K₃) (ρ₂ : K₂ →+* K₃), Pf p K → PQ p i₁ (Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g}) → PQ p i₂ (Ideal.span {Polynomial.C g - Polynomial.X * Polynomial.C f}) → PQ p i₃ (Ideal.span {LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g}) → (∀ α, ρ₁ (i₁ α) = i₃ (Polynomial.toLaurent α)) → (∀ β, ρ₂ (i₂ β) = i₃ (LaurentPolynomial.invert (Polynomial.toLaurent β))) → ∀ (b₁ : K₁) (b₂ : K₂), ρ₁ b₁ = ρ₂ b₂ → ∃ a : K, i₁ (Polynomial.C a) = b₁ ∧ i₂ (Polynomial.C a) = b₂ := by
  intro p _ K _ K₁ _ K₂ _ K₃ _ f g i₁ i₂ i₃ ρ₁ ρ₂ hK h₁ h₂ h₃ hρ₁ hρ₂ b₁ b₂ hb
  obtain ⟨k₁, α₁, hα₁⟩ := h₁.2 b₁
  obtain ⟨k₂, α₂, hα₂⟩ := h₂.2 b₂
  have e₁ : b₁ ^ p ^ (k₁ + k₂) = i₁ (α₁ ^ p ^ k₂) := by
    rw [pow_add, pow_mul, hα₁, map_pow]
  have e₂ : b₂ ^ p ^ (k₁ + k₂) = i₂ (α₂ ^ p ^ k₁) := by
    rw [add_comm, pow_add, pow_mul, hα₂, map_pow]
  generalize α₁ ^ p ^ k₂ = α at e₁
  generalize α₂ ^ p ^ k₁ = β at e₂
  generalize k₁ + k₂ = m at e₁ e₂
  have h30 : i₃ (Polynomial.toLaurent α - LaurentPolynomial.invert (Polynomial.toLaurent β)) = 0 := by
    rw [map_sub, ← hρ₁, ← hρ₂, ← e₁, ← e₂, map_pow, map_pow, hb, sub_self]
  obtain ⟨k, hk⟩ := (h₃.3 _).1 h30
  have hchar : (p : K[T;T⁻¹]) = 0 := by
    rw [← map_natCast (LaurentPolynomial.C : K →+* K[T;T⁻¹]) p, hK.1, map_zero]
  obtain ⟨Fr, hFr⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p (K[T;T⁻¹]) hchar k
  have hx : (Polynomial.toLaurent α - LaurentPolynomial.invert (Polynomial.toLaurent β)) ^ p ^ k =
      Polynomial.toLaurent (α ^ p ^ k) - LaurentPolynomial.invert (Polynomial.toLaurent (β ^ p ^ k)) := by
    rw [← hFr, map_sub, hFr, hFr, map_pow, map_pow, map_pow]
  rw [hx] at hk
  obtain ⟨c, hc₁, hc₂⟩ := GlobalTheory.CompanionTheory.LaurSplit.exists_const_of_mem_span K f g _ _ hk
  have hz₁ : i₁ (α ^ p ^ k - Polynomial.C c) = 0 := (h₁.3 _).2 ⟨0, by simpa using hc₁⟩
  have hz₂ : i₂ (β ^ p ^ k - Polynomial.C c) = 0 := (h₂.3 _).2 ⟨0, by simpa using hc₂⟩
  rw [map_sub, sub_eq_zero, map_pow, ← e₁, ← pow_mul, ← pow_add] at hz₁
  rw [map_sub, sub_eq_zero, map_pow, ← e₂, ← pow_mul, ← pow_add] at hz₂
  obtain ⟨a, ha⟩ := (GlobalTheory.CompanionTheory.PerfectRing.pf_facts p K hK).2.2.1 (m + k) c
  have inj₁ := (GlobalTheory.CompanionTheory.PerfectRing.pf_facts p K₁ h₁.1).2.2.2.1
  have inj₂ := (GlobalTheory.CompanionTheory.PerfectRing.pf_facts p K₂ h₂.1).2.2.2.1
  refine ⟨a, inj₁ (m + k) _ _ ?_, inj₂ (m + k) _ _ ?_⟩
  · rw [← map_pow, ← map_pow, ha, hz₁]
  · rw [← map_pow, ← map_pow, ha, hz₂]

end GlobalTheory.CompanionTheory.BMid
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AicValOfIsColim
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Colim

theorem iota_tr {A : Type} [CommRing A] {G : ℕ → Type} [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)]
    {f : ∀ n, G n →ₐ[A] G (n + 1)} {L : Type} [CommRing L] [Algebra A L] {ι : ∀ n, G n →ₐ[A] L}
    (hc : IsColim f ι) (n : ℕ) : ∀ (k : ℕ) (x : G n), ι (n + k) (tr f n k x) = ι n x
  | 0, _ => rfl
  | k + 1, x => by
    show ι (n + k + 1) (f (n + k) (tr f n k x)) = ι n x
    rw [hc.comm, iota_tr hc n k x]

theorem aic_of_isColim {A : Type} [CommRing A] {G : ℕ → Type} [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)]
    {f : ∀ n, G n →ₐ[A] G (n + 1)} {L : Type} [CommRing L] [Algebra A L] {ι : ∀ n, G n →ₐ[A] L}
    (hc : IsColim f ι) (hA : ∀ n, AICm (f n : G n →+* G (n + 1))) : AIC L := by
  intro P hP hd
  obtain ⟨n, y, hy⟩ := hc.surj P.natDegree (fun i => P.coeff i)
  set Q : Polynomial (G n) := Polynomial.X ^ P.natDegree + ∑ i : Fin P.natDegree, Polynomial.C (y i) * Polynomial.X ^ (i : ℕ) with hQ
  have hQm : Q.Monic := Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt y)
  have hmap : Q.map (ι n : G n →+* L) = P := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hQ, Polynomial.map_add (f := _), Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, RingHom.coe_coe, hy]
    conv_rhs => rw [hP.as_sum]
    rw [Fin.sum_univ_eq_sum_range (fun i => Polynomial.C (P.coeff i) * Polynomial.X ^ i) P.natDegree]
  have hQd : 0 < Q.natDegree := by
    have := Polynomial.natDegree_map_le (f := (ι n : G n →+* L)) (p := Q)
    rw [hmap] at this; omega
  obtain ⟨x, hx⟩ := hA n Q hQm hQd
  refine ⟨ι (n + 1) x, ?_⟩
  have h2 : (Q.map (f n : G n →+* G (n + 1))).map (ι (n + 1) : G (n + 1) →+* L) = P := by
    rw [Polynomial.map_map, ← hmap]; congr 1; ext z; simp [hc.comm]
  rw [← h2]
  exact Polynomial.IsRoot.map (ι (n + 1) : G (n + 1) →+* L) hx

theorem val_of_isColim {A : Type} [CommRing A] (π : A) {G : ℕ → Type} [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)]
    {f : ∀ n, G n →ₐ[A] G (n + 1)} {L : Type} [CommRing L] [Algebra A L] {ι : ∀ n, G n →ₐ[A] L}
    (hc : IsColim f ι) (hV : ∀ n, VALm (algebraMap A (G n) π) (f n : G n →+* G (n + 1))) :
    VAL (algebraMap A L π) := by
  intro u v ⟨N, hN⟩
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hN
  obtain ⟨n, y, hy⟩ := hc.surj 4 ![a, b, u, v]
  have h0 := hy 0; have h1 := hy 1; have h2 := hy 2; have h3 := hy 3
  simp only [Matrix.cons_val] at h0 h1 h2 h3
  obtain ⟨k, hk⟩ := hc.ker n 1 (fun _ => y 0 * y 2 + y 1 * y 3 - algebraMap A (G n) π ^ N)
    (fun _ => by simp [h0, h1, h2, h3, hab])
  have hk0 := hk 0
  set m := n + k
  set t := tr f n k
  have hspan : algebraMap A (G m) π ^ N ∈ Ideal.span {t (y 2), t (y 3)} := by
    refine Ideal.mem_span_pair.mpr ⟨t (y 0), t (y 1), ?_⟩
    have := hk0
    simp only [map_sub, map_add (f := _), map_mul, map_pow, AlgHom.commutes] at this
    exact (sub_eq_zero.mp this)
  obtain ⟨e, he, he1, he2⟩ := hV m (t (y 2)) (t (y 3)) ⟨N, hspan⟩
  have hu : ι (m + 1) (f m (t (y 2))) = u := by rw [hc.comm, iota_tr hc n k, h2]
  have hv : ι (m + 1) (f m (t (y 3))) = v := by rw [hc.comm, iota_tr hc n k, h3]
  refine ⟨ι (m + 1) e, he.map (ι (m + 1)), ?_, ?_⟩
  · rw [Ideal.mem_span_singleton] at he1 ⊢
    have := map_dvd (ι (m + 1)) he1
    simpa [map_mul, hu, hv] using this
  · rw [Ideal.mem_span_singleton] at he2 ⊢
    have := map_dvd (ι (m + 1)) he2
    simpa [map_mul, map_sub, hu, hv] using this

theorem aic_val_of_isColim : ∀ (A : Type) [CommRing A] (π : A) (G : ℕ → Type) [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)] (f : ∀ n, G n →ₐ[A] G (n + 1))(L : Type) [CommRing L] [Algebra A L] (ι : ∀ n, G n →ₐ[A] L), IsColim f ι → (∀ n, AICm (f n : G n →+* G (n + 1))) → (∀ n, VALm (algebraMap A (G n) π) (f n : G n →+* G (n + 1))) → AIC L ∧ VAL (algebraMap A L π) :=
  fun _ _ π _ _ _ _ _ _ _ _ hc hA hV => ⟨aic_of_isColim hc hA, val_of_isColim π hc hV⟩
end GlobalTheory.CompanionTheory.Colim
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SolvAtStage
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.SeqColim

theorem map_tr {A : Type} [CommRing A] {G : ℕ → Type} [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)]
    (f : ∀ n, G n →ₐ[A] G (n + 1)) {L : Type} [CommRing L] [Algebra A L] (ι : ∀ n, G n →ₐ[A] L)
    (h : IsColim f ι) (n : ℕ) : ∀ (k : ℕ) (x : G n), ι (n + k) (tr f n k x) = ι n x
  | 0, x => rfl
  | k + 1, x => by
      show ι (n + k + 1) (f (n + k) (tr f n k x)) = ι n x
      rw [h.comm, map_tr f ι h n k x]

theorem pf_of_stages (p : ℕ) {A : Type} [CommRing A] {G : ℕ → Type} [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)]
    (f : ∀ n, G n →ₐ[A] G (n + 1)) {L : Type} [CommRing L] [Algebra A L] (ι : ∀ n, G n →ₐ[A] L)
    (h : IsColim f ι) (hG : ∀ n, Pf p (G n)) : Pf p L := by
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (ι 0) (hG 0).char
    simpa using this
  · intro x y hxy
    obtain ⟨n, z, hz⟩ := h.surj 2 ![x, y]
    have h0 : ι n (z 0 ^ p - z 1 ^ p) = 0 := by
      have e0 := hz 0
      have e1 := hz 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1
      simp [map_sub, map_pow, e0, e1, hxy]
    obtain ⟨k, hk⟩ := h.ker n 1 (fun _ => z 0 ^ p - z 1 ^ p) (fun _ => h0)
    have hk0 := hk 0
    simp only [map_sub, map_pow, sub_eq_zero] at hk0
    have heq := (hG (n + k)).bij.1 hk0
    have e0 := hz 0
    have e1 := hz 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1
    have := congrArg (ι (n + k)) heq
    rw [map_tr f ι h, map_tr f ι h, e0, e1] at this
    exact this
  · intro x
    obtain ⟨n, z, hz⟩ := h.surj 1 (fun _ => x)
    obtain ⟨w, hw⟩ := (hG n).bij.2 (z 0)
    refine ⟨ι n w, ?_⟩
    simp only at hw ⊢
    rw [← map_pow, hw, hz 0]

theorem solv_at_stage {A : Type} [CommRing A] {G : ℕ → Type} [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)]
    (f : ∀ n, G n →ₐ[A] G (n + 1)) {L : Type} [CommRing L] [Algebra A L] (ι : ∀ n, G n →ₐ[A] L)
    (h : IsColim f ι) (m n : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A) (hs : Solv L a c) :
    ∃ N, Solv (G N) a c := by
  obtain ⟨y, hy⟩ := hs
  obtain ⟨N₀, z, hz⟩ := h.surj n y
  have hd : ∀ i, ι N₀ ((∑ j, a i j • z j) - algebraMap A (G N₀) (c i)) = 0 := by
    intro i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_smul, AlgHom.commutes, hz, hy i, sub_self]
  obtain ⟨k, hk⟩ := h.ker N₀ m _ hd
  refine ⟨N₀ + k, fun j => tr f N₀ k (z j), fun i => ?_⟩
  have := hk i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_sum, map_smul, AlgHom.commutes, sub_eq_zero] at this
  exact this

end GlobalTheory.CompanionTheory.SeqColim

namespace GlobalTheory.CompanionTheory

theorem colim_pf : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](G : ℕ → Type) [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)] (f : ∀ n, G n →ₐ[A] G (n + 1))(L : Type) [CommRing L] [Algebra A L] (ι : ∀ n, G n →ₐ[A] L), IsColim f ι → ((∀ n, Pf p (G n)) → Pf p L) ∧ ∀ (m n : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A), Solv L a c → ∃ N, Solv (G N) a c := by
  intro p _ A _ G _ _ f L _ _ ι h
  exact ⟨SeqColim.pf_of_stages p f ι h, fun m n a c hs => SeqColim.solv_at_stage f ι h m n a c hs⟩

end GlobalTheory.CompanionTheory
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BijectiveAlgebraMapZero
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Coproduct

theorem bijective_algebraMap_zero {A B K : Type} [CommRing A] [CommRing B] [CommRing K]
    [Algebra A B] [Algebra A K] {ι : Fin 0 → (B →ₐ[A] K)} (h : IsWP ι) :
    Function.Bijective (algebraMap A K) := by
  obtain ⟨z, hz, -⟩ := h.ex A (RingHom.id A) (fun i => i.elim0) (fun i => i.elim0)
  have hzx : ∀ a, z (algebraMap A K a) = a := fun a => by
    simpa using congrArg (fun f : A →+* A => f a) hz
  have hid : (algebraMap A K).comp z = RingHom.id K := by
    refine h.uniq K _ _ ?_ (fun i => i.elim0)
    ext a
    simp [hzx]
  refine Function.bijective_iff_has_inverse.mpr ⟨z, hzx, fun k => ?_⟩
  simpa using congrArg (fun f : K →+* K => f k) hid

theorem bijective_one {A B K : Type} [CommRing A] [CommRing B] [CommRing K]
    [Algebra A B] [Algebra A K] {ι : Fin 1 → (B →ₐ[A] K)} (h : IsWP ι) :
    Function.Bijective (ι 0) := by
  obtain ⟨z, hz, hy⟩ := h.ex B (algebraMap A B) (fun _ => RingHom.id B)
    (fun _ => RingHom.id_comp _)
  have hzi : ∀ b, z (ι 0 b) = b := fun b => by
    simpa using congrArg (fun f : B →+* B => f b) (hy 0)
  have hza : ∀ a, z (algebraMap A K a) = algebraMap A B a := fun a => by
    simpa using congrArg (fun f : A →+* B => f a) hz
  have hid : ((ι 0 : B →ₐ[A] K) : B →+* K).comp z = RingHom.id K := by
    refine h.uniq K _ _ ?_ (fun i => ?_)
    · ext a
      simp [hza]
    · obtain rfl : i = 0 := Subsingleton.elim _ _
      ext b
      simp [hzi]
  refine Function.bijective_iff_has_inverse.mpr ⟨z, hzi, fun k => ?_⟩
  simpa using congrArg (fun f : K →+* K => f k) hid

theorem exists_coface {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)]
    (ι : ∀ n, Fin n → (B →ₐ[A] K n)) (h : ∀ n, IsWP (ι n)) :
    ∃ δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1)),
      ∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i) := by
  have key : ∀ (n : ℕ) (k : Fin (n + 1)), ∃ d : K n →ₐ[A] K (n + 1),
      ∀ i, d.comp (ι n i) = ι (n + 1) (k.succAbove i) := by
    intro n k
    obtain ⟨z, hz, hy⟩ := (h n).ex (K (n + 1)) (algebraMap A (K (n + 1)))
      (fun i => (ι (n + 1) (k.succAbove i) : B →+* K (n + 1)))
      (fun i => by ext a; simp)
    refine ⟨{ z with commutes' := fun a => congrArg (fun f : A →+* K (n + 1) => f a) hz },
      fun i => ?_⟩
    ext b
    exact congrArg (fun f : B →+* K (n + 1) => f b) (hy i)
  choose δ hδ using key
  exact ⟨δ, hδ⟩

theorem coproduct_low_and_coface : ∀ (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (ι : ∀ n, Fin n → (B →ₐ[A] K n)), (∀ n, IsWP (ι n)) → Function.Bijective (algebraMap A (K 0)) ∧ Function.Bijective (ι 1 0) ∧ ∃ δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1)), ∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i) := by
  intro A _ B _ _ K _ _ ι h
  exact ⟨bijective_algebraMap_zero (h 0), bijective_one (h 1), exists_coface K ι h⟩

end GlobalTheory.CompanionTheory.Coproduct
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplVal
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.ComplVal

theorem side {T : Type} [CommRing T] (t : T) (hu : ∀ x : T, IsUnit (1 + t * x))
    (f f' a b w E : T) (N : ℕ) (hE : E * E = E) (hab : a * f + b * f' = t ^ N)
    (hw : E * f = t ^ (N + 1) * w) : ∃ c, c * f' = E * f := by
  obtain ⟨v, hv⟩ := (hu (-(w * a))).exists_left_inv
  have key : (1 + t * -(w * a)) * (E * f) = E * t * w * b * f' := by
    linear_combination E * hw - E * t * w * hab - f * hE
  exact ⟨v * (E * t * w * b), by linear_combination -v * key + E * f * hv⟩

theorem mid {T : Type} [CommRing T] (P Q E f F f' F' k v v' u' : T) (hP : P * P = P) (hQ : Q * Q = Q)
    (hA : P * f = P * F * v) (hB : Q * f' = Q * F' * v') (hu : v' * u' = 1)
    (hk : k * F' = P * Q * E * F) : ∃ c, c * f' = P * Q * E * f := by
  exact ⟨v * k * Q * u', by
    linear_combination v * k * u' * hB + v * k * Q * F' * hu + v * Q * hk + v * P * E * F * hQ - Q * E * hA⟩

theorem core {T : Type} [CommRing T] (t : T) (hu : ∀ x : T, IsUnit (1 + t * x))
    (f f' F F' a b s s' c c' d d' k k' E₁ E₂ E : T) (N : ℕ)
    (h₁ : E₁ * E₁ = E₁) (h₂ : E₂ * E₂ = E₂) (hE : E * E = E)
    (hab : a * f + b * f' = t ^ N)
    (hs : s * t ^ (N + 2) = f - F) (hs' : s' * t ^ (N + 2) = f' - F')
    (hc : c * t ^ (N + 1) = E₁ * F) (hc' : c' * t ^ (N + 1) = E₂ * F')
    (hd : d * F = (1 - E₁) * t ^ (N + 1)) (hd' : d' * F' = (1 - E₂) * t ^ (N + 1))
    (hk : k * F' = (1 - E₁) * (1 - E₂) * E * F)
    (hk' : k' * F = (1 - E₁) * (1 - E₂) * (1 - E) * F') :
    ∃ e : T, IsIdempotentElem e ∧ e * f ∈ Ideal.span {f'} ∧ (1 - e) * f' ∈ Ideal.span {f} := by
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.CompanionTheory.ComplVal.side t hu f f' a b (c + E₁ * s * t) E₁ N h₁ hab
    (by linear_combination -E₁ * hs - hc)
  obtain ⟨c₂, hc₂⟩ := GlobalTheory.CompanionTheory.ComplVal.side t hu f' f b a (c' + E₂ * s' * t) E₂ N h₂
    (by linear_combination hab) (by linear_combination -E₂ * hs' - hc')
  have hP : (1 - E₁) * (1 - E₁) = 1 - E₁ := by linear_combination h₁
  have hQ : (1 - E₂) * (1 - E₂) = 1 - E₂ := by linear_combination h₂
  have hA : (1 - E₁) * f = (1 - E₁) * F * (1 + t * (s * d)) := by
    linear_combination -(1 - E₁) * hs - s * t ^ (N + 2) * h₁ - s * t * (1 - E₁) * hd
  have hB : (1 - E₂) * f' = (1 - E₂) * F' * (1 + t * (s' * d')) := by
    linear_combination -(1 - E₂) * hs' - s' * t ^ (N + 2) * h₂ - s' * t * (1 - E₂) * hd'
  obtain ⟨u₁, hu₁⟩ := (hu (s' * d')).exists_right_inv
  obtain ⟨u₂, hu₂⟩ := (hu (s * d)).exists_right_inv
  obtain ⟨c₃, hc₃⟩ := GlobalTheory.CompanionTheory.ComplVal.mid (1 - E₁) (1 - E₂) E f F f' F' k (1 + t * (s * d))
    (1 + t * (s' * d')) u₁ hP hQ hA hB hu₁ hk
  obtain ⟨c₄, hc₄⟩ := GlobalTheory.CompanionTheory.ComplVal.mid (1 - E₂) (1 - E₁) (1 - E) f' F' f F k' (1 + t * (s' * d'))
    (1 + t * (s * d)) u₂ hQ hP hB hA hu₂ (by linear_combination hk')
  refine ⟨E₁ + (1 - E₁) * (1 - E₂) * E, ?_, ?_, ?_⟩
  · show (E₁ + (1 - E₁) * (1 - E₂) * E) * (E₁ + (1 - E₁) * (1 - E₂) * E) = E₁ + (1 - E₁) * (1 - E₂) * E
    linear_combination (1 - 2 * (1 - E₂) * E + (1 - E₂) ^ 2 * E ^ 2) * h₁ + (1 - E₁) * E ^ 2 * h₂
      + (1 - E₁) * (1 - E₂) * hE
  · exact Ideal.mem_span_singleton'.2 ⟨c₁ + c₃, by linear_combination hc₁ + hc₃⟩
  · exact Ideal.mem_span_singleton'.2 ⟨(1 - E₁) * c₂ + c₄, by linear_combination (1 - E₁) * hc₂ + hc₄⟩

theorem compl_val : ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T), CrystallineSemistableComparison.D.IsCompl π g → VAL π → VAL (g π) := by
  intro B _ T _ π g hC hV
  unfold CrystallineSemistableComparison.D.VAL at hV ⊢
  have := hC.compl
  have hJ : g π ∈ (⊥ : Ideal T).jacobson :=
    IsAdicComplete.le_jacobson_bot (I := Ideal.span {g π}) (Ideal.mem_span_singleton_self (g π))
  have hu : ∀ x : T, IsUnit (1 + g π * x) := fun x => by
    rw [add_comm]; exact Ideal.mem_jacobson_bot.1 hJ x
  intro f₀ f₁ hN
  obtain ⟨N, hN⟩ := hN
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 hN
  obtain ⟨x₁, hx₁⟩ := hC.surj (N + 2) f₀
  obtain ⟨x₂, hx₂⟩ := hC.surj (N + 2) f₁
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hx₁
  obtain ⟨s', hs'⟩ := Ideal.mem_span_singleton'.1 hx₂
  obtain ⟨e₁, he₁, h1a, h1b⟩ := hV x₁ (π ^ (N + 1)) ⟨N + 1, Ideal.mem_span_pair.2 ⟨0, 1, by ring⟩⟩
  obtain ⟨e₂, he₂, h2a, h2b⟩ := hV x₂ (π ^ (N + 1)) ⟨N + 1, Ideal.mem_span_pair.2 ⟨0, 1, by ring⟩⟩
  obtain ⟨c₀, hc₀⟩ := Ideal.mem_span_singleton'.1 h1a
  obtain ⟨d₀, hd₀⟩ := Ideal.mem_span_singleton'.1 h1b
  obtain ⟨c₁, hc₁⟩ := Ideal.mem_span_singleton'.1 h2a
  obtain ⟨d₁, hd₁⟩ := Ideal.mem_span_singleton'.1 h2b
  obtain ⟨P, hPdef⟩ : ∃ P : B, P = (1 - e₁) * (1 - e₂) := ⟨_, rfl⟩
  have hPP : P * P = P := by
    rw [hPdef]; linear_combination (1 - e₂) ^ 2 * he₁.eq + (1 - e₁) * he₂.eq
  have hPe : P * (1 - e₁) = P := by
    rw [hPdef]; linear_combination (1 - e₂) * he₁.eq
  obtain ⟨e, he, ha, hb⟩ := hV (P * x₁ + (1 - P)) (P * x₂) ⟨N + 1, Ideal.mem_span_pair.2
    ⟨P * d₀ + (1 - P) * π ^ (N + 1), 0, by
      linear_combination P * hd₀ + π ^ (N + 1) * hPe
        + (d₀ * x₁ - d₀ - π ^ (N + 1) * x₁ + π ^ (N + 1)) * hPP⟩⟩
  obtain ⟨m, hm⟩ := Ideal.mem_span_singleton'.1 ha
  obtain ⟨m', hm'⟩ := Ideal.mem_span_singleton'.1 hb
  have hkB : m * P * x₂ = (1 - e₁) * (1 - e₂) * e * x₁ := by
    linear_combination P * hm - (m * x₂ - e * x₁ + e) * hPP + e * x₁ * hPdef
  have hk'B : m' * P * x₁ = (1 - e₁) * (1 - e₂) * (1 - e) * x₂ := by
    linear_combination P * hm' - (m' * x₁ - m' - (1 - e) * x₂) * hPP + (1 - e) * x₂ * hPdef
  have i₁ : g e₁ * g e₁ = g e₁ := by rw [← map_mul, he₁.eq]
  have i₂ : g e₂ * g e₂ = g e₂ := by rw [← map_mul, he₂.eq]
  have i₃ : g e * g e = g e := by rw [← map_mul, he.eq]
  have hc : g c₀ * g π ^ (N + 1) = g e₁ * g x₁ := by
    have h := congrArg g hc₀; simp only [map_mul, map_pow] at h; linear_combination h
  have hc' : g c₁ * g π ^ (N + 1) = g e₂ * g x₂ := by
    have h := congrArg g hc₁; simp only [map_mul, map_pow] at h; linear_combination h
  have hd : g d₀ * g x₁ = (1 - g e₁) * g π ^ (N + 1) := by
    have h := congrArg g hd₀; simp only [map_mul, map_pow, map_sub, map_one] at h; linear_combination h
  have hd' : g d₁ * g x₂ = (1 - g e₂) * g π ^ (N + 1) := by
    have h := congrArg g hd₁; simp only [map_mul, map_pow, map_sub, map_one] at h; linear_combination h
  have hk : g m * g P * g x₂ = (1 - g e₁) * (1 - g e₂) * g e * g x₁ := by
    have h := congrArg g hkB; simp only [map_mul, map_sub, map_one] at h; linear_combination h
  have hk' : g m' * g P * g x₁ = (1 - g e₁) * (1 - g e₂) * (1 - g e) * g x₂ := by
    have h := congrArg g hk'B; simp only [map_mul, map_sub, map_one] at h; linear_combination h
  exact GlobalTheory.CompanionTheory.ComplVal.core (g π) hu f₀ f₁ (g x₁) (g x₂) a b s s' (g c₀) (g c₁) (g d₀) (g d₁)
    (g m * g P) (g m' * g P) (g e₁) (g e₂) (g e) N i₁ i₂ i₃ hab hs hs' hc hc' hd hd' hk hk'

end GlobalTheory.CompanionTheory.ComplVal
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIsWP
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.AlgCoproduct

theorem exists_isWP : ∀ (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (n : ℕ),
    ∃ (K : Type) (_ : CommRing K) (_ : Algebra A K) (ι : Fin n → (B →ₐ[A] K)), IsWP ι := by
  intro A _ B _ _ n
  induction n with
  | zero =>
    refine ⟨A, inferInstance, inferInstance, fun i => i.elim0, ?_⟩
    constructor
    · intro T _ x y _
      exact ⟨x, by ext a; rfl, fun i => i.elim0⟩
    · intro T _ z z' h _
      exact h
  | succ n ih =>
    obtain ⟨K, _, _, ι, hι⟩ := ih
    refine ⟨B ⊗[A] K, inferInstance, inferInstance,
      Fin.cons Algebra.TensorProduct.includeLeft
        (fun i => (Algebra.TensorProduct.includeRight).comp (ι i)), ?_⟩
    constructor
    · intro T _ x y hy
      obtain ⟨z, hz, hzi⟩ := hι.ex T x (fun i => y i.succ) (fun i => hy i.succ)
      letI : Algebra A T := x.toAlgebra
      let f : B →ₐ[A] T := { y 0 with commutes' := fun a => RingHom.congr_fun (hy 0) a }
      let g : K →ₐ[A] T := { z with commutes' := fun a => RingHom.congr_fun hz a }
      refine ⟨(Algebra.TensorProduct.productMap f g).toRingHom, ?_, ?_⟩
      · ext a
        exact (Algebra.TensorProduct.productMap f g).commutes a
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · ext b
          simp [f, g]
        · ext b
          have := RingHom.congr_fun (hzi j) b
          simpa [f, g] using this
    · intro T _ z z' h hi
      have hB : ∀ b : B, z (b ⊗ₜ[A] 1) = z' (b ⊗ₜ[A] 1) := fun b => by
        simpa using RingHom.congr_fun (hi 0) b
      have hK : (z.comp (Algebra.TensorProduct.includeRight : K →ₐ[A] B ⊗[A] K).toRingHom) =
          z'.comp (Algebra.TensorProduct.includeRight : K →ₐ[A] B ⊗[A] K).toRingHom := by
        refine hι.uniq T _ _ ?_ (fun i => ?_)
        · ext a
          have := RingHom.congr_fun h a
          simpa [Algebra.TensorProduct.algebraMap_apply] using this
        · ext b
          simpa using RingHom.congr_fun (hi i.succ) b
      refine RingHom.ext fun t => ?_
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul b k =>
        have h1 : b ⊗ₜ[A] k = (b ⊗ₜ[A] (1 : K)) * ((1 : B) ⊗ₜ[A] k) := by simp
        have h2 : z ((1 : B) ⊗ₜ[A] k) = z' ((1 : B) ⊗ₜ[A] k) := RingHom.congr_fun hK k
        rw [h1, map_mul, map_mul, hB, h2]
      | add a b ha hb => simp [ha, hb]

end GlobalTheory.CompanionTheory.AlgCoproduct
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DirectedSystemTrR
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.ColimEx

variable {A : Type} [CommRing A] {G : ℕ → Type} [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)]
  (f : ∀ n, G n →ₐ[A] G (n + 1))

def trA (i j : ℕ) (h : i ≤ j) : G i →ₐ[A] G j :=
  Nat.leRecOn (motive := fun k => G i →ₐ[A] G k) h (fun {k} g => (f k).comp g)
    (AlgHom.id A (G i))

theorem trA_self (i : ℕ) (h : i ≤ i) : trA f i i h = AlgHom.id A (G i) :=
  Nat.leRecOn_self (motive := fun k => G i →ₐ[A] G k) _

theorem trA_succ (i k : ℕ) (h : i ≤ k) (h2 : i ≤ k + 1) :
    trA f i (k + 1) h2 = (f k).comp (trA f i k h) :=
  Nat.leRecOn_succ (motive := fun k => G i →ₐ[A] G k) h _

theorem trA_trans (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) (x : G i) :
    trA f j k hjk (trA f i j hij x) = trA f i k (hij.trans hjk) x := by
  induction k, hjk using Nat.le_induction with
  | base => rw [trA_self]; rfl
  | succ k hjk ih =>
    rw [trA_succ f j k hjk, trA_succ f i k (hij.trans hjk)]
    simp only [AlgHom.comp_apply, ih]

theorem tr_eq_trA (n k : ℕ) (x : G n) : tr f n k x = trA f n (n + k) (Nat.le_add_right n k) x := by
  induction k with
  | zero =>
    show tr f n 0 x = trA f n n (Nat.le_refl n) x
    rw [trA_self]; rfl
  | succ k ih =>
    have h := trA_succ f n (n + k) (Nat.le_add_right n k) (Nat.le_add_right n (k + 1))
    show f (n + k) (tr f n k x) = trA f n (n + k + 1) (Nat.le_add_right n (k + 1)) x
    rw [h, AlgHom.comp_apply, ih]

def trR (i j : ℕ) (h : i ≤ j) : G i →+* G j := (trA f i j h).toRingHom

instance directedSystem_trR : DirectedSystem G fun i j h => trR f i j h where
  map_self i x := by simp [trR, trA_self]
  map_map k j i hij hjk x := trA_trans f i j k hij hjk x

abbrev Lim := Ring.DirectLimit G fun i j h => trR f i j h

instance : Algebra A (Lim f) :=
  ((Ring.DirectLimit.of G (fun i j h => trR f i j h) 0).comp (algebraMap A (G 0))).toAlgebra

def ι (n : ℕ) : G n →ₐ[A] Lim f :=
  { Ring.DirectLimit.of G (fun i j h => trR f i j h) n with
    commutes' := fun a => by
      show Ring.DirectLimit.of G (fun i j h => trR f i j h) n (algebraMap A (G n) a) =
        Ring.DirectLimit.of G (fun i j h => trR f i j h) 0 (algebraMap A (G 0) a)
      rw [← Ring.DirectLimit.of_f (G := G) (f := fun i j h => trR f i j h) (Nat.zero_le n)
        (algebraMap A (G 0) a)]
      simp [trR] }

theorem ι_apply (n : ℕ) (x : G n) :
    ι f n x = Ring.DirectLimit.of G (fun i j h => trR f i j h) n x := rfl

theorem ι_trA (i j : ℕ) (h : i ≤ j) (x : G i) : ι f j (trA f i j h x) = ι f i x := by
  rw [ι_apply, ι_apply]
  exact Ring.DirectLimit.of_f (G := G) (f := fun i j h => trR f i j h) h x

theorem ι_tr (n k : ℕ) (x : G n) : ι f (n + k) (tr f n k x) = ι f n x := by
  rw [tr_eq_trA, ι_trA]

theorem isColim : IsColim f (ι f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n x
    have := ι_tr f n 1 x
    simpa [tr] using this
  · intro m x
    choose n y hy using fun i => Ring.DirectLimit.exists_of (x i)
    refine ⟨Finset.univ.sup n, fun i => trA f (n i) _ (Finset.le_sup (Finset.mem_univ i)) (y i),
      fun i => ?_⟩
    rw [ι_trA, ι_apply, hy]
  · intro n m y hy
    have h0 : ∀ i, ∃ j, ∃ hij : n ≤ j, trR f n j hij (y i) = 0 := fun i =>
      Ring.DirectLimit.of.zero_exact (f' := fun i j h => trR f i j h) (hy i)
    choose j hj hz using h0
    refine ⟨Finset.univ.sup fun i => j i - n, fun i => ?_⟩
    have hle : j i ≤ n + Finset.univ.sup fun i => j i - n := by
      have := Finset.le_sup (f := fun i => j i - n) (Finset.mem_univ i)
      omega
    rw [tr_eq_trA, ← trA_trans f n (j i) _ (hj i) hle]
    have : trA f n (j i) (hj i) (y i) = 0 := hz i
    rw [this, map_zero]

end GlobalTheory.CompanionTheory.ColimEx

theorem GlobalTheory.CompanionTheory.ColimEx.exists_isColim : ∀ (A : Type) [CommRing A](G : ℕ → Type) [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)] (f : ∀ n, G n →ₐ[A] G (n + 1)), ∃ (L : Type) (_ : CommRing L) (_ : Algebra A L), ∃ ι : ∀ n, G n →ₐ[A] L, IsColim f ι :=
  fun A _ G _ _ f => ⟨GlobalTheory.CompanionTheory.ColimEx.Lim f, inferInstance, inferInstance, GlobalTheory.CompanionTheory.ColimEx.ι f,
    GlobalTheory.CompanionTheory.ColimEx.isColim f⟩
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TmulEqZeroOfMemSpan
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.TensCompl

theorem tmul_eq_zero_of_mem_span {R N A : Type} [CommRing R] [AddCommGroup N] [Module R N]
    [CommRing A] [Algebra R A] (c : R) (M : ℕ) (hN : ∀ x : N, c ^ M • x = 0) (n : N) (a : A)
    (ha : a ∈ Ideal.span {algebraMap R A c ^ M}) : n ⊗ₜ[R] a = 0 := by
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  have : b * algebraMap R A c ^ M = c ^ M • b := by
    rw [Algebra.smul_def, map_pow, mul_comm]
  rw [this, ← smul_tmul, hN, zero_tmul]

theorem main : ∀ (R : Type) [CommRing R] (r : ℕ → R) (M : ℕ) (N : Type) [AddCommGroup N] [Module R N](B : Type) [CommRing B] [Algebra R B] (T : Type) [CommRing T] [Algebra R T] (g : B →ₐ[R] T), (∀ x : N, r 0 ^ M • x = 0) → (∀ y : T, ∃ x, y - g x ∈ Ideal.span {algebraMap R T (r 0) ^ M}) → (∀ x : B, g x ∈ Ideal.span {algebraMap R T (r 0) ^ M} → ∀ k, r k • x ∈ Ideal.span {algebraMap R B (r 0) ^ M}) → Function.Surjective (g.toLinearMap.lTensor N) ∧ ∀ w : N ⊗[R] B, g.toLinearMap.lTensor N w = 0 → ∀ k, r k • w = 0 := by
  intro R _ r M N _ _ B _ _ T _ _ g h1 h2 h3
  constructor
  · intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul n y =>
      obtain ⟨x, hx⟩ := h2 y
      refine ⟨n ⊗ₜ x, ?_⟩
      have h0 := tmul_eq_zero_of_mem_span (r 0) M h1 n _ hx
      rw [tmul_sub, sub_eq_zero] at h0
      rw [h0]
      simp
    | add a b ha hb =>
      obtain ⟨a', rfl⟩ := ha
      obtain ⟨b', rfl⟩ := hb
      exact ⟨a' + b', map_add _ _ _⟩
  · intro w hw k
    choose s hs using h2
    let I : Ideal T := Ideal.span {algebraMap R T (r 0) ^ M}
    let P : Submodule R B := (Ideal.span {algebraMap R B (r 0) ^ M}).restrictScalars R
    have key : ∀ x : B, g x ∈ I → r k • x ∈ P := fun x hx => h3 x hx k
    have hadd : ∀ y y' : T, r k • s (y + y') - (r k • s y + r k • s y') ∈ P := by
      intro y y'
      rw [← smul_add, ← smul_sub]
      apply key
      have e : g (s (y + y') - (s y + s y')) =
          (y - g (s y)) + (y' - g (s y')) - (y + y' - g (s (y + y'))) := by
        simp only [map_sub, map_add (f := _)]; ring
      rw [e]
      exact I.sub_mem (I.add_mem (hs y) (hs y')) (hs _)
    have hsmul : ∀ (c : R) (y : T), r k • s (c • y) - c • (r k • s y) ∈ P := by
      intro c y
      rw [smul_comm c, ← smul_sub]
      apply key
      have e : g (s (c • y) - c • s y) =
          algebraMap R T c * (y - g (s y)) - (c • y - g (s (c • y))) := by
        rw [map_sub, map_smul, mul_sub, ← Algebra.smul_def, ← Algebra.smul_def]; abel
      rw [e]
      exact I.sub_mem (I.mul_mem_left _ (hs y)) (hs _)
    let L : T →ₗ[R] B ⧸ P :=
      { toFun := fun y => P.mkQ (r k • s y)
        map_add' := fun y y' => by
          rw [← map_add (f := _)]
          exact (Submodule.Quotient.eq P).mpr (hadd y y')
        map_smul' := fun c y => by
          simp only [RingHom.id_apply]
          rw [← map_smul]
          exact (Submodule.Quotient.eq P).mpr (hsmul c y) }
    let F : (B ⧸ P) →ₗ[R] N →ₗ[R] N ⊗[R] B :=
      P.liftQ (TensorProduct.mk R N B).flip (by
        intro b hb
        rw [LinearMap.mem_ker]
        ext n
        exact tmul_eq_zero_of_mem_span (r 0) M h1 n b hb)
    let Φ : N ⊗[R] T →ₗ[R] N ⊗[R] B := TensorProduct.lift (F ∘ₗ L).flip
    have hΦ : ∀ (n : N) (y : T), Φ (n ⊗ₜ y) = n ⊗ₜ (r k • s y) := fun n y => by
      simp [Φ, F, L]
    have hcomp : ∀ v : N ⊗[R] B, Φ (g.toLinearMap.lTensor N v) = r k • v := by
      intro v
      induction v using TensorProduct.induction_on with
      | zero => simp
      | tmul n b =>
        rw [LinearMap.lTensor_tmul, hΦ, ← tmul_smul, ← sub_eq_zero, ← tmul_sub, ← smul_sub]
        apply tmul_eq_zero_of_mem_span (r 0) M h1 n
        apply key
        have e : g (s (g b) - b) = -(g b - g (s (g b))) := by
          simp only [map_sub]; ring
        have e' : (g.toLinearMap) b = g b := rfl
        rw [e', e]
        exact I.neg_mem (hs _)
      | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, smul_add]
    rw [← hcomp w, hw, map_zero]

end GlobalTheory.CompanionTheory.TensCompl
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WpHomotopy
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.WpHomotopy

theorem wp_homotopy : ∀ (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (ι : ∀ n, Fin n → (B →ₐ[A] K n)) (δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1))), (∀ n, IsWP (ι n)) → (∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i)) → ∃ H : ∀ n, K (n + 1) →ₗ[A] B ⊗[A] K n, (∀ z, H 0 (alt (δ 0) z) = (1 : B) ⊗ₜ[A] z) ∧ ∀ n z, (alt (δ n)).lTensor B (H n z) + H (n + 1) (alt (δ (n + 1)) z) = (1 : B) ⊗ₜ[A] z := by
  intro A _ B _ _ K _ _ ι δ hW hδ
  have huniq : ∀ (m : ℕ) (T : Type) [CommRing T] [Algebra A T] (f g : K m →ₐ[A] T),
      (∀ i, f.comp (ι m i) = g.comp (ι m i)) → f = g := by
    intro m T _ _ f g hfg
    have key := (hW m).uniq T (f : K m →+* T) (g : K m →+* T)
      (by ext a; simp)
      (fun i => by
        ext b
        exact DFunLike.congr_fun (hfg i) b)
    ext x
    exact DFunLike.congr_fun key x
  have hex : ∀ n, ∃ h : K (n + 1) →ₐ[A] B ⊗[A] K n,
      h.comp (ι (n + 1) 0) = Algebra.TensorProduct.includeLeft ∧
      ∀ i : Fin n, h.comp (ι (n + 1) i.succ) =
        (Algebra.TensorProduct.includeRight : K n →ₐ[A] B ⊗[A] K n).comp (ι n i) := by
    intro n
    obtain ⟨z, hz, hzi⟩ := (hW (n + 1)).ex (B ⊗[A] K n) (algebraMap A (B ⊗[A] K n))
      (Fin.cons (α := fun _ => B →+* B ⊗[A] K n)
        ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] K n) : B →+* B ⊗[A] K n)
        (fun i => (((Algebra.TensorProduct.includeRight : K n →ₐ[A] B ⊗[A] K n).comp (ι n i) :
          B →ₐ[A] B ⊗[A] K n) : B →+* B ⊗[A] K n)))
      (by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · ext a; simp
        · ext a; simp)
    refine ⟨{ z with commutes' := fun a => DFunLike.congr_fun hz a }, ?_, fun i => ?_⟩
    · ext b
      simpa using DFunLike.congr_fun (hzi 0) b
    · ext b
      simpa using DFunLike.congr_fun (hzi i.succ) b
  choose h hl hr using hex
  have h0 : ∀ n, (h n).comp (δ n 0) = (Algebra.TensorProduct.includeRight : K n →ₐ[A] B ⊗[A] K n) := by
    intro n
    refine huniq n _ _ _ (fun i => ?_)
    rw [AlgHom.comp_assoc, hδ, Fin.succAbove_zero]
    exact hr n i
  have hs : ∀ n (k : Fin (n + 1)), (h (n + 1)).comp (δ (n + 1) k.succ) =
      (Algebra.TensorProduct.map (AlgHom.id A B) (δ n k)).comp (h n) := by
    intro n k
    refine huniq (n + 1) _ _ _ (fun i => ?_)
    rw [AlgHom.comp_assoc, hδ, AlgHom.comp_assoc]
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [Fin.succ_succAbove_zero, hl, hl]
      ext b
      simp
    · rw [Fin.succ_succAbove_succ, hr, hr, ← AlgHom.comp_assoc]
      have e := hδ n k j
      ext b
      have e' := DFunLike.congr_fun e b
      simp only [AlgHom.comp_apply] at e' ⊢
      simp [e']
  refine ⟨fun n => (h n).toLinearMap, fun z => ?_, fun n z => ?_⟩
  · have e := DFunLike.congr_fun (h0 0) z
    simpa [alt] using e
  · have e0 := DFunLike.congr_fun (h0 (n + 1)) z
    have es : ∀ k : Fin (n + 1), h (n + 1) (δ (n + 1) k.succ z) =
        ((δ n k).toLinearMap.lTensor B) (h n z) := by
      intro k
      have e := DFunLike.congr_fun (hs n k) z
      simp only [AlgHom.comp_apply] at e
      rw [e]
      generalize h n z = t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    have a1 : alt (δ (n + 1)) z = δ (n + 1) 0 z +
        ∑ k : Fin (n + 1), -((-1 : ℤ) ^ (k : ℕ) • δ (n + 1) k.succ z) := by
      simp [alt, Fin.sum_univ_succ, LinearMap.sum_apply, pow_succ]
    have a2 : ∀ t : B ⊗[A] K n, (alt (δ n)).lTensor B t =
        ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) • ((δ n k).toLinearMap.lTensor B) t := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        simp only [alt, LinearMap.lTensor_tmul, LinearMap.sum_apply, LinearMap.smul_apply,
          TensorProduct.tmul_sum, TensorProduct.tmul_smul]
      | add x y hx hy =>
        simp only [map_add (f := _), hx, hy, smul_add, Finset.sum_add_distrib]
    show (alt (δ n)).lTensor B (h n z) + h (n + 1) (alt (δ (n + 1)) z) = (1 : B) ⊗ₜ[A] z
    have e1 : h (n + 1) (δ (n + 1) 0 z) = (1 : B) ⊗ₜ[A] z := by
      simpa using e0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [a1, a2, map_add (f := _), e1, map_sum, add_left_comm, ← Finset.sum_add_distrib]
    have : ∀ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) • ((δ n k).toLinearMap.lTensor B) (h n z) +
        h (n + 1) (-((-1 : ℤ) ^ (k : ℕ) • δ (n + 1) k.succ z)) = 0 := by
      intro k
      rw [map_neg, map_zsmul, es k, add_neg_cancel]
    rw [Finset.sum_congr rfl (fun k _ => this k)]
    simp

end GlobalTheory.CompanionTheory.WpHomotopy
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsComplExistsUnique
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueCompEq
namespace GlobalTheory.CompanionTheory.PfCompl

open Ideal

variable {B T T₁ : Type*} [CommRing B] [CommRing T] [CommRing T₁]

theorem exists_level_hom (π : B) (g : B →+* T) (x : B →+* T₁) (M : ℕ)
    (hsurj : ∀ y : T, ∃ b, y - g b ∈ span {g π ^ M})
    (hinj : ∀ b, g b ∈ span {g π ^ M} → b ∈ span {π ^ M}) :
    ∃ f : T →+* T₁ ⧸ (span {x π}) ^ M,
      ∀ y b, y - g b ∈ span {g π ^ M} → f y = Ideal.Quotient.mk _ (x b) := by
  have hIJ : span {π ^ M} ≤ (span {g π ^ M}).comap g := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]
    exact Ideal.mem_span_singleton_self _
  have hxK : span {π ^ M} ≤ ((span {x π}) ^ M).comap x := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]
    exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) M
  have hinj' : Function.Injective (Ideal.quotientMap (span {g π ^ M}) g hIJ) := by
    refine Ideal.quotientMap_injective' ?_
    intro b hb
    exact hinj b (Ideal.mem_comap.1 hb)
  have hsurj' : Function.Surjective (Ideal.quotientMap (span {g π ^ M}) g hIJ) := by
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨b, hb⟩ := hsurj y
    exact ⟨Ideal.Quotient.mk _ b, by rw [Ideal.quotientMap_mk]; exact (Ideal.Quotient.eq.2 hb).symm⟩
  let e := RingEquiv.ofBijective _ ⟨hinj', hsurj'⟩
  refine ⟨(Ideal.quotientMap _ x hxK).comp (e.symm.toRingHom.comp (Ideal.Quotient.mk _)), ?_⟩
  intro y b hy
  have h1 : e (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk (span {g π ^ M}) y := by
    show Ideal.quotientMap _ g hIJ (Ideal.Quotient.mk _ b) = _
    rw [Ideal.quotientMap_mk]
    exact (Ideal.Quotient.eq.2 hy).symm
  have h2 : e.symm (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk (span {π ^ M}) b := by
    rw [← h1, RingEquiv.symm_apply_apply]
  show Ideal.quotientMap _ x hxK (e.symm (Ideal.Quotient.mk _ y)) = _
  rw [h2, Ideal.quotientMap_mk]

theorem mk_eq_of_comp_eq (π : B) (g : B →+* T) (x : B →+* T₁) (ψ : T →+* T₁)
    (hψ : ψ.comp g = x) (M : ℕ) (y : T) (b : B) (hy : y - g b ∈ span {g π ^ M}) :
    Ideal.Quotient.mk ((span {x π}) ^ M) (ψ y) = Ideal.Quotient.mk _ (x b) := by
  have hb : x b = ψ (g b) := (DFunLike.congr_fun hψ b).symm
  have hπ : ψ (g π) = x π := DFunLike.congr_fun hψ π
  rw [Ideal.Quotient.eq, hb, ← map_sub]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hy
  rw [← ht, map_mul, map_pow, hπ]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) M)

theorem existsUnique_comp_eq (π : B) (g : B →+* T)
    (hsurj : ∀ (M : ℕ) (y : T), ∃ b, y - g b ∈ span {g π ^ M})
    (hinj : ∀ (M : ℕ) (b : B), g b ∈ span {g π ^ M} → b ∈ span {π ^ M})
    (x : B →+* T₁) (hc : IsAdicComplete (span {x π}) T₁) :
    ∃! ψ : T →+* T₁, ψ.comp g = x := by
  have key : ∀ a c : T₁,
      (∀ n : ℕ, Ideal.Quotient.mk (span {x π} ^ n) a = Ideal.Quotient.mk _ c) → a = c := by
    intro a c h
    have h0 := IsHausdorff.haus' (I := span {x π}) (a - c) fun n => by
      rw [SModEq.sub_mem, sub_zero, Ideal.smul_eq_mul, Ideal.mul_top]
      exact Ideal.Quotient.eq.1 (h n)
    exact sub_eq_zero.1 h0
  choose f hf using fun n => exists_level_hom π g x n (hsurj n) (hinj n)
  have hle : ∀ {m n : ℕ}, m ≤ n → ∀ z : T, z ∈ span {g π ^ n} → z ∈ span {g π ^ m} := by
    intro m n h z hz
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    refine Ideal.mem_span_singleton'.2 ⟨t * g π ^ (n - m), ?_⟩
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel h]
  have hcompat : ∀ {m n : ℕ} (h : m ≤ n),
      (Ideal.Quotient.factorPow (span {x π}) h).comp (f n) = f m := by
    intro m n h
    ext y
    obtain ⟨b, hb⟩ := hsurj n y
    rw [RingHom.comp_apply, hf n y b hb, hf m y b (hle h _ hb)]
    first
      | rfl
      | exact Ideal.Quotient.factor_mk _ _
      | simp [Ideal.Quotient.factorPow]
  refine ⟨IsAdicComplete.liftRingHom _ f hcompat, ?_, ?_⟩
  · ext b
    apply key
    intro n
    rw [RingHom.comp_apply, IsAdicComplete.mk_liftRingHom, hf n (g b) b (by simp)]
  · intro ψ hψ
    ext y
    apply key
    intro n
    rw [IsAdicComplete.mk_liftRingHom]
    obtain ⟨b, hb⟩ := hsurj n y
    rw [hf n y b hb]
    exact mk_eq_of_comp_eq π g x ψ hψ n y b hb

end GlobalTheory.CompanionTheory.PfCompl
end

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PfCompl

theorem isCompl_existsUnique :
    ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T), IsCompl π g →
      ∀ (T₁ : Type) [CommRing T₁] (x : B →+* T₁), IsAdicComplete (Ideal.span {x π}) T₁ →
        ∃! ψ : T →+* T₁, ψ.comp g = x := by
  intro B _ T _ π g h T₁ _ x hc
  exact existsUnique_comp_eq π g h.surj h.inj x hc

end GlobalTheory.CompanionTheory.PfCompl
end

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial
namespace CrystallineSemistableComparison.D.Leaf

theorem pf_facts : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A], Pf p A → (∃ F : A ≃+* A, ∀ x, F x = x ^ p) ∧ (∀ (x : A) (n : ℕ), x ^ n = 0 → x = 0) ∧ (∀ (k : ℕ) (x : A), ∃ y, y ^ p ^ k = x) ∧ (∀ (k : ℕ) (x y : A), x ^ p ^ k = y ^ p ^ k → x = y) ∧ ∀ r : ℕ → A, IsRt p r → (∀ k, ∃ c, r k = c * r (k + 1) * r (k + 1)) ∧ (∀ k, r k ^ p ^ k = r 0) ∧ ∀ (N : ℕ) (x : A), r 0 ^ N * x = 0 → ∀ k, r k * x = 0 := GlobalTheory.CompanionTheory.PerfectRing.pf_facts

theorem wp_pf : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : Type) [CommRing K] [Algebra A K] (n : ℕ) (ι : Fin n → (B →ₐ[A] K)), IsWP ι → Pf p A → Pf p B → Pf p K := GlobalTheory.CompanionTheory.PerfectRing.wp_pf

theorem pq_ex : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] (I : Ideal S), (p : S) = 0 → ∃ (T : Type) (_ : CommRing T) (i : S →+* T), PQ p i I := GlobalTheory.CompanionTheory.PerfClos.exists_PQ

theorem pq_lift : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] (T : Type) [CommRing T] (T₁ : Type) [CommRing T₁] (i : S →+* T) (I : Ideal S) (φ : S →+* T₁), PQ p i I → Pf p T₁ → (∀ x ∈ I, φ x = 0) → ∃! ψ : T →+* T₁, ψ.comp i = φ := GlobalTheory.CompanionTheory.PerfectRing.pq_lift

theorem bc_poly : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : Type) [CommRing K] [Algebra A K] (i : Polynomial A →ₐ[A] B) (h : Polynomial A), Pf p A → Pf p K → PQ p (i : Polynomial A →+* B) (Ideal.span {h}) → ∃ i₁ : Polynomial K →+* B ⊗[A] K, PQ p i₁ (Ideal.span {h.map (algebraMap A K)}) ∧ (∀ a, i₁ (Polynomial.C a) = (1 : B) ⊗ₜ[A] a) ∧ i₁ Polynomial.X = i Polynomial.X ⊗ₜ[A] (1 : K) := GlobalTheory.CompanionTheory.Perfection.pq_baseChange_polynomial

theorem bc_laur : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : Type) [CommRing K] [Algebra A K] (i : A[T;T⁻¹] →ₐ[A] B) (f g : A), Pf p A → Pf p K → PQ p (i : A[T;T⁻¹] →+* B) (Ideal.span {LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g}) → ∃ i₁ : K[T;T⁻¹] →+* B ⊗[A] K, PQ p i₁ (Ideal.span {LaurentPolynomial.C (algebraMap A K f) - LaurentPolynomial.T 1 * LaurentPolynomial.C (algebraMap A K g)}) ∧ (∀ a, i₁ (LaurentPolynomial.C a) = (1 : B) ⊗ₜ[A] a) ∧ ∀ n : ℤ, i₁ (LaurentPolynomial.T n) = i (LaurentPolynomial.T n) ⊗ₜ[A] (1 : K) := GlobalTheory.CompanionTheory.PerfBC.bc_laur

theorem b_inj : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [CommRing K] (K₁ : Type) [CommRing K₁] (K₂ : Type) [CommRing K₂] (f g : K) (i₁ : Polynomial K →+* K₁) (i₂ : Polynomial K →+* K₂) (r : ℕ → K) (N : ℕ), Pf p K → IsRt p r → r 0 ^ N ∈ Ideal.span {f, g} → PQ p i₁ (Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g}) → PQ p i₂ (Ideal.span {Polynomial.C g - Polynomial.X * Polynomial.C f}) → ∀ a : K, i₁ (Polynomial.C a) = 0 → i₂ (Polynomial.C a) = 0 → ∀ k, r k * a = 0 := GlobalTheory.CompanionTheory.PerfectRing.b_inj

theorem b_mid : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [CommRing K] (K₁ : Type) [CommRing K₁] (K₂ : Type) [CommRing K₂] (K₃ : Type) [CommRing K₃] (f g : K) (i₁ : Polynomial K →+* K₁) (i₂ : Polynomial K →+* K₂) (i₃ : K[T;T⁻¹] →+* K₃) (ρ₁ : K₁ →+* K₃) (ρ₂ : K₂ →+* K₃), Pf p K → PQ p i₁ (Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g}) → PQ p i₂ (Ideal.span {Polynomial.C g - Polynomial.X * Polynomial.C f}) → PQ p i₃ (Ideal.span {LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g}) → (∀ α, ρ₁ (i₁ α) = i₃ (Polynomial.toLaurent α)) → (∀ β, ρ₂ (i₂ β) = i₃ (LaurentPolynomial.invert (Polynomial.toLaurent β))) → ∀ (b₁ : K₁) (b₂ : K₂), ρ₁ b₁ = ρ₂ b₂ → ∃ a : K, i₁ (Polynomial.C a) = b₁ ∧ i₂ (Polynomial.C a) = b₂ := GlobalTheory.CompanionTheory.BMid.exists_const_of_rho_eq

theorem b_surj : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [CommRing K] (K₁ : Type) [CommRing K₁] (K₂ : Type) [CommRing K₂] (K₃ : Type) [CommRing K₃] (f g : K) (i₁ : Polynomial K →+* K₁) (i₂ : Polynomial K →+* K₂) (i₃ : K[T;T⁻¹] →+* K₃) (ρ₁ : K₁ →+* K₃) (ρ₂ : K₂ →+* K₃), Pf p K → PQ p i₁ (Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g}) → PQ p i₂ (Ideal.span {Polynomial.C g - Polynomial.X * Polynomial.C f}) → PQ p i₃ (Ideal.span {LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g}) → (∀ α, ρ₁ (i₁ α) = i₃ (Polynomial.toLaurent α)) → (∀ β, ρ₂ (i₂ β) = i₃ (LaurentPolynomial.invert (Polynomial.toLaurent β))) → ∀ y : K₃, ∃ (b₁ : K₁) (b₂ : K₂), y = ρ₁ b₁ - ρ₂ b₂ := GlobalTheory.CompanionTheory.PerfectRing.b_surj

theorem mv_prod : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B₁ : Type) [CommRing B₁] [Algebra A B₁] (B₂ : Type) [CommRing B₂] [Algebra A B₂] (D : Type) [CommRing D] [Algebra A D] (r : ℕ → A) (ρ₁ : B₁ →ₐ[A] D) (ρ₂ : B₂ →ₐ[A] D), IsRt p r → Pf p D → (∀ y, ∃ b₁ b₂, y = ρ₁ b₁ - ρ₂ b₂) → (∀ (K : Type) [CommRing K] [Algebra A K], Pf p K → (∀ a : K, ((1 : B₁) ⊗ₜ[A] a) = 0 → ((1 : B₂) ⊗ₜ[A] a) = 0 → ∀ k, r k • a = 0) ∧ ∀ (w₁ : B₁ ⊗[A] K) (w₂ : B₂ ⊗[A] K), Algebra.TensorProduct.map ρ₁ (AlgHom.id A K) w₁ = Algebra.TensorProduct.map ρ₂ (AlgHom.id A K) w₂ → ∃ a : K, w₁ = (1 : B₁) ⊗ₜ[A] a ∧ w₂ = (1 : B₂) ⊗ₜ[A] a) → Cov p r (B₁ × B₂) := GlobalTheory.CompanionTheory.SnakeCov.mv_prod

theorem cov_cmp : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (r : ℕ → A), (∀ (m n : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A), Solv B a c → ∃ (B₁ : Type) (_ : CommRing B₁) (_ : Algebra A B₁), Cov p r B₁ ∧ Solv B₁ a c) → Cov p r B := GlobalTheory.CompanionTheory.CovCmp.cov_of_solv

theorem cov_mono : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (r : ℕ → A), Cov p r A ∧ ∀ (B : Type) [CommRing B] [Algebra A B] (B₁ : Type) [CommRing B₁] [Algebra A B₁] (φ : B →ₐ[A] B₁), Cov p r B₁ → Cov p r B := GlobalTheory.CompanionTheory.CovMono.cov_mono

theorem cov_comp : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B](B₁ : Type) [CommRing B₁] [Algebra A B₁] [Algebra B B₁] [IsScalarTower A B B₁] (r : ℕ → A), Pf p A → Pf p B → IsRt p r → Cov p r B → Cov p (fun k => algebraMap A B (r k)) B₁ → Cov p r B₁ := GlobalTheory.CompanionTheory.CovComp.cov_comp

theorem cov_root : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (r : ℕ → A) (P : Polynomial A), Pf p A → P.Monic → 0 < P.natDegree → ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧ ∃ x : B, Polynomial.aeval x P = 0 := GlobalTheory.CompanionTheory.CovRoot.cov_root

theorem big_step : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (r : ℕ → A) (𝓔 : Set (Set (MvPolynomial (Fin 3) A))), Pf p A → (∀ J : Set (Set (MvPolynomial (Fin 3) A)), J.Finite → J ⊆ 𝓔 → ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧ ∀ E ∈ J, Pt (algebraMap A B) E) → ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧ (∀ E ∈ 𝓔, Pt (algebraMap A B) E) ∧ ∀ (T : Type) [CommRing T] (x : A →+* T), Pf p T → (∀ E ∈ 𝓔, Pt x E) → ∃ y : B →+* T, y.comp (algebraMap A B) = x := GlobalTheory.CompanionTheory.BigStep.big_step

theorem colim_ex : ∀ (A : Type) [CommRing A](G : ℕ → Type) [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)] (f : ∀ n, G n →ₐ[A] G (n + 1)), ∃ (L : Type) (_ : CommRing L) (_ : Algebra A L), ∃ ι : ∀ n, G n →ₐ[A] L, IsColim f ι := GlobalTheory.CompanionTheory.ColimEx.exists_isColim

theorem colim_pf : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](G : ℕ → Type) [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)] (f : ∀ n, G n →ₐ[A] G (n + 1))(L : Type) [CommRing L] [Algebra A L] (ι : ∀ n, G n →ₐ[A] L), IsColim f ι → ((∀ n, Pf p (G n)) → Pf p L) ∧ ∀ (m n : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A), Solv L a c → ∃ N, Solv (G N) a c := GlobalTheory.CompanionTheory.colim_pf

theorem colim_test : ∀ (A : Type) [CommRing A] (π : A) (G : ℕ → Type) [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)] (f : ∀ n, G n →ₐ[A] G (n + 1))(L : Type) [CommRing L] [Algebra A L] (ι : ∀ n, G n →ₐ[A] L), IsColim f ι → (∀ n, AICm (f n : G n →+* G (n + 1))) → (∀ n, VALm (algebraMap A (G n) π) (f n : G n →+* G (n + 1))) → AIC L ∧ VAL (algebraMap A L π) := GlobalTheory.CompanionTheory.Colim.aic_val_of_isColim

theorem tors_quot : ∀ (p : ℕ) [Fact p.Prime] (B : Type) [CommRing B] (π : B), Pf p B → ∃ (B₁ : Type) (_ : CommRing B₁) (q : B →+* B₁), Function.Surjective q ∧ Pf p B₁ ∧ q π ∈ nonZeroDivisors B₁ ∧ (∀ x, q x = 0 ↔ π * x = 0) ∧ (AIC B → AIC B₁) ∧ (VAL π → VAL (q π)) := GlobalTheory.CompanionTheory.PerfectRing.tors_quot

theorem compl_ex : ∀ (B : Type) [CommRing B] (π : B), ∃ (T : Type) (_ : CommRing T) (g : B →+* T), IsCompl π g := GlobalTheory.CompanionTheory.AdicCompl.exists_isCompl

theorem compl_reg : ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T), IsCompl π g → π ∈ nonZeroDivisors B → g π ∈ nonZeroDivisors T := GlobalTheory.CompanionTheory.ComplReg.isCompl_nonZeroDivisor

theorem compl_pf : ∀ (p : ℕ) [Fact p.Prime] (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T), IsCompl π g → Pf p B → Pf p T := GlobalTheory.CompanionTheory.PerfectRing.pf_of_isCompl

theorem compl_univ : ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T), IsCompl π g → ∀ (T₁ : Type) [CommRing T₁] (x : B →+* T₁), IsAdicComplete (Ideal.span {x π}) T₁ → ∃! ψ : T →+* T₁, ψ.comp g = x := GlobalTheory.CompanionTheory.PfCompl.isCompl_existsUnique

theorem compl_val : ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T), IsCompl π g → VAL π → VAL (g π) := GlobalTheory.CompanionTheory.ComplVal.compl_val

theorem compl_aic : ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T), IsCompl π g → π ∈ nonZeroDivisors B → AIC B → VAL π → AIC T := GlobalTheory.CompanionTheory.Completion.aic_of_isCompl

theorem wp_ex : ∀ (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (n : ℕ), ∃ (K : Type) (_ : CommRing K) (_ : Algebra A K) (ι : Fin n → (B →ₐ[A] K)), IsWP ι := GlobalTheory.CompanionTheory.AlgCoproduct.exists_isWP

theorem wp_cof : ∀ (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (ι : ∀ n, Fin n → (B →ₐ[A] K n)), (∀ n, IsWP (ι n)) → Function.Bijective (algebraMap A (K 0)) ∧ Function.Bijective (ι 1 0) ∧ ∃ δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1)), ∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i) := GlobalTheory.CompanionTheory.Coproduct.coproduct_low_and_coface

theorem wp_dd : ∀ (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (ι : ∀ n, Fin n → (B →ₐ[A] K n)) (δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1))), (∀ n, IsWP (ι n)) → (∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i)) → ∀ n z, alt (δ (n + 1)) (alt (δ n) z) = 0 := GlobalTheory.CompanionTheory.WpCoface.alt_alt

theorem wp_htpy : ∀ (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (ι : ∀ n, Fin n → (B →ₐ[A] K n)) (δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1))), (∀ n, IsWP (ι n)) → (∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i)) → ∃ H : ∀ n, K (n + 1) →ₗ[A] B ⊗[A] K n, (∀ z, H 0 (alt (δ 0) z) = (1 : B) ⊗ₜ[A] z) ∧ ∀ n z, (alt (δ n)).lTensor B (H n z) + H (n + 1) (alt (δ (n + 1)) z) = (1 : B) ⊗ₜ[A] z := GlobalTheory.CompanionTheory.WpHomotopy.wp_homotopy

theorem ami_exact : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (r : ℕ → A), Pf p A → Cov p r B → ∀ (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (d : ∀ n, K n →ₗ[A] K (n + 1)) (H : ∀ n, K (n + 1) →ₗ[A] B ⊗[A] K n), (∀ n, Pf p (K n)) → (∀ n z, d (n + 1) (d n z) = 0) → ((∀ z, H 0 (d 0 z) = (1 : B) ⊗ₜ[A] z) ∧ ∀ n z, (d n).lTensor B (H n z) + H (n + 1) (d (n + 1) z) = (1 : B) ⊗ₜ[A] z) → (∀ z, d 0 z = 0 → ∀ k, r k • z = 0) ∧ ∀ n z, d (n + 1) z = 0 → ∀ k, r k • z ∈ LinearMap.range (d n) := GlobalTheory.CompanionTheory.Dblock.AmiExact.exact_of_contraction

theorem tens_exact : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] (r : ℕ → R) (N : Type) [AddCommGroup N] [Module R N] (K₀ : Type) [AddCommGroup K₀] [Module R K₀] (K₁ : Type) [AddCommGroup K₁] [Module R K₁] (K₂ : Type) [AddCommGroup K₂] [Module R K₂] (K₃ : Type) [AddCommGroup K₃] [Module R K₃] (d₀ : K₀ →ₗ[R] K₁) (d₁ : K₁ →ₗ[R] K₂) (d₂ : K₂ →ₗ[R] K₃), IsRt p r → (∀ z, d₂ (d₁ z) = 0) → (∀ z, d₁ z = 0 → ∀ k, r k • z ∈ LinearMap.range d₀) → (∀ z, d₂ z = 0 → ∀ k, r k • z ∈ LinearMap.range d₁) → (∀ (a : R) (x : K₃), a ≠ 0 → a • x = 0 → ∀ k, r k • x = 0) → ∀ w : N ⊗[R] K₁, d₁.lTensor N w = 0 → ∀ k, r k • w ∈ LinearMap.range (d₀.lTensor N) := GlobalTheory.CompanionTheory.Dblock.smul_mem_range_lTensor_of_lTensor_eq_zero

theorem tens_compl : ∀ (R : Type) [CommRing R] (r : ℕ → R) (M : ℕ) (N : Type) [AddCommGroup N] [Module R N](B : Type) [CommRing B] [Algebra R B] (T : Type) [CommRing T] [Algebra R T] (g : B →ₐ[R] T), (∀ x : N, r 0 ^ M • x = 0) → (∀ y : T, ∃ x, y - g x ∈ Ideal.span {algebraMap R T (r 0) ^ M}) → (∀ x : B, g x ∈ Ideal.span {algebraMap R T (r 0) ^ M} → ∀ k, r k • x ∈ Ideal.span {algebraMap R B (r 0) ^ M}) → Function.Surjective (g.toLinearMap.lTensor N) ∧ ∀ w : N ⊗[R] B, g.toLinearMap.lTensor N w = 0 → ∀ k, r k • w = 0 := GlobalTheory.CompanionTheory.TensCompl.main

theorem wp_rel : ∀ (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (ι : ∀ n, Fin n → (B →ₐ[A] K n)) (δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1))), (∀ n, IsWP (ι n)) → (∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i)) → ∀ (n : ℕ) (k : Fin (n + 2)) (i : Fin (n + 1)), (δ (n + 1) (k.succAbove i)).comp (δ n (i.predAbove k)) = (δ (n + 1) k).comp (δ n i) := GlobalTheory.CompanionTheory.WpCoface.coface_rel

end CrystallineSemistableComparison.D.Leaf
