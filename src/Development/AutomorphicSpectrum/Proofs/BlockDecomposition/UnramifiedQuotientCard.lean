module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.VecClose

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuotientCard
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuotientCard
open PositivityTheory.PfSWUS.Loc

namespace GlobalTheory.CompanionTheory.UnrDens

private def mulPow {R : Type} [CommRing R] (ϖ : R) (k : ℕ) : R →+ R ⧸ lev ϖ (k + 1) :=
  ((Ideal.Quotient.mk (lev ϖ (k + 1))).toAddMonoidHom).comp (AddMonoidHom.mulLeft (ϖ ^ k))

private theorem mulPow_apply {R : Type} [CommRing R] (ϖ : R) (k : ℕ) (a : R) :
    mulPow ϖ k a = Ideal.Quotient.mk (lev ϖ (k + 1)) (ϖ ^ k * a) := rfl

private theorem lev_succ_le {R : Type} [CommRing R] (ϖ : R) (k : ℕ) : lev ϖ (k + 1) ≤ lev ϖ k := by
  exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ (Nat.le_succ k))

private theorem mulPow_ker {R : Type} [CommRing R] {ϖ : R} (hr : IsSMulRegular R ϖ) (k : ℕ) :
    (mulPow ϖ k).ker = (lev ϖ 1).toAddSubgroup := by
  ext a
  rw [AddMonoidHom.mem_ker, mulPow_apply, Ideal.Quotient.eq_zero_iff_mem, Submodule.mem_toAddSubgroup]
  simp only [lev, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have hinj : Function.Injective (fun y : R => ϖ ^ k • y) := hr.pow k
    apply hinj
    show ϖ ^ k • a = ϖ ^ k • (ϖ ^ 1 * c)
    rw [smul_eq_mul, smul_eq_mul, hc]
    ring
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [hc]; ring⟩

theorem card_quot_lev_succ {R : Type} [CommRing R] {ϖ : R} (hr : IsSMulRegular R ϖ) (k : ℕ) :
    Nat.card (R ⧸ lev ϖ (k + 1)) = Nat.card (R ⧸ lev ϖ 1) * Nat.card (R ⧸ lev ϖ k) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : R ⧸ lev ϖ (k + 1) →+ R ⧸ lev ϖ k,
      ∀ a, φ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a :=
    ⟨(Ideal.Quotient.lift (lev ϖ (k + 1)) (Ideal.Quotient.mk (lev ϖ k))
      (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (lev_succ_le ϖ k ha))).toAddMonoidHom,
      fun a => by simp⟩
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ a, hφ a⟩
  have hker : φ.ker = (mulPow ϖ k).range := by
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [AddMonoidHom.mem_ker, hφ, AddMonoidHom.mem_range, Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro ha
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp ha
      exact ⟨c, by rw [mulPow_apply, ← hc]⟩
    · rintro ⟨c, hc⟩
      rw [mulPow_apply, Ideal.Quotient.eq] at hc
      have h1 : ϖ ^ k * c - a ∈ lev ϖ k := lev_succ_le ϖ k hc
      have h2 : ϖ ^ k * c ∈ lev ϖ k := Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
      have := sub_mem h2 h1
      simpa using this
  have e1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker
  have e2 : Nat.card ((R ⧸ lev ϖ (k + 1)) ⧸ φ.ker) = Nat.card (R ⧸ lev ϖ k) :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective φ hsurj).toEquiv
  have e3 : Nat.card φ.ker = Nat.card (R ⧸ lev ϖ 1) := by
    rw [hker]
    have := Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (mulPow ϖ k)).toEquiv
    rw [← this, mulPow_ker hr]
    rfl
  rw [e1, e2, e3]
  ring

theorem card_quot_lev : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ),
    IsUnrQuad R σ ϖ q ε → ∀ k : ℕ, Nat.card (R ⧸ lev ϖ k) = q ^ (2 * k) := by
  intro R _ σ ϖ q ε hR k
  induction k with
  | zero =>
    have htop : lev ϖ 0 = ⊤ := by
      show Ideal.span {ϖ ^ 0} = ⊤
      rw [pow_zero]
      exact Ideal.span_singleton_one
    rw [Nat.mul_zero, pow_zero]
    exact Nat.card_eq_one_iff_unique.mpr ⟨Ideal.Quotient.subsingleton_iff.mpr htop, ⟨0⟩⟩
  | succ k ih =>
    rw [card_quot_lev_succ hR.reg k, ih, hR.card]
    ring

end GlobalTheory.CompanionTheory.UnrDens
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuotientCardStatement
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_quotient_card : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε → ∀ k : ℕ, Nat.card (R ⧸ lev ϖ k) = q ^ (2 * k) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.card_quot_lev | exact GlobalTheory.CompanionTheory.UnrDens.card_quot_lev | (intros; apply GlobalTheory.CompanionTheory.UnrDens.card_quot_lev <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedNondeg
noncomputable section
open PositivityTheory.PfSWUS.Loc
namespace GlobalTheory.CompanionTheory.SiegLoc

variable {R : Type} [CommRing R]

theorem psi_pow {σ : R →+* R} {ϖ : R} {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ}
    (hψ : IsLevelChars σ ϖ ψ) (k j : ℕ) (a : R) :
    ψ (k + j) (Ideal.Quotient.mk _ (ϖ ^ j * a)) = ψ k (Ideal.Quotient.mk _ a) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← ih, ← Nat.add_assoc, pow_succ', mul_assoc]
    exact hψ.compat (k + j) (ϖ ^ j * a)

theorem mem_lev_iff {ϖ : R} {k : ℕ} {a : R} : a ∈ lev ϖ k ↔ ∃ c, a = ϖ ^ k * c := by
  rw [lev, Ideal.mem_span_singleton, dvd_def]

theorem fixed_nondeg {σ : R →+* R} {ϖ : R} {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ}
    (hψ : IsLevelChars σ ϖ ψ) (hfix : σ ϖ = ϖ) (hreg : IsSMulRegular R ϖ) (k : ℕ) (a : R)
    (ha : σ a = a) (h : ∀ b, σ b = b → ψ k (Ideal.Quotient.mk _ (a * b)) = 1) : a ∈ lev ϖ k := by
  induction k generalizing a with
  | zero => simp [lev]
  | succ k ih =>
    have ha' : a ∈ lev ϖ k := ih a ha (fun b hb => by
      have := h (ϖ * b) (by simp [hfix, hb])
      rw [show a * (ϖ * b) = ϖ * (a * b) by ring, hψ.compat] at this
      exact this)
    obtain ⟨c, rfl⟩ := mem_lev_iff.1 ha'
    have hregk : IsSMulRegular R (ϖ ^ k) := hreg.pow k
    have hc : σ c = c := by
      apply hregk
      simpa [map_mul, map_pow, hfix] using ha
    have hc1 : c ∈ lev ϖ 1 := hψ.prim c hc (fun b hb => by
      have h1 := h b hb
      have h2 := psi_pow hψ 1 k (c * b)
      rw [Nat.add_comm 1 k, ← mul_assoc] at h2
      rw [← h2]; exact h1)
    obtain ⟨d, rfl⟩ := mem_lev_iff.1 hc1
    exact mem_lev_iff.2 ⟨d, by ring⟩

theorem trace_nondeg {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ}
    (hR : IsUnrQuad R σ ϖ q ε) (hψ : IsLevelChars σ ϖ ψ) (k : ℕ) (y : R)
    (h : ∀ t, ψ k (Ideal.Quotient.mk _ (t * y + σ (t * y))) = 1) : y ∈ lev ϖ k := by
  obtain ⟨u, hu, -⟩ := hR.basis
  have key : ∀ t, t * y + σ (t * y) ∈ lev ϖ k := fun t => by
    refine fixed_nondeg hψ hR.fix_ϖ hR.reg k _ (by simp [hR.inv, add_comm]) (fun b hb => ?_)
    have := h (b * t)
    convert this using 3
    simp only [map_mul, hb]; ring
  have h1 := key 1
  have h2 := key u
  have h3 : (u - σ u) * y ∈ lev ϖ k := by
    have : (u - σ u) * y = (u * y + σ (u * y)) - σ u * (1 * y + σ (1 * y)) := by
      simp only [map_mul, map_one]; ring
    rw [this]
    exact Ideal.sub_mem _ h2 (Ideal.mul_mem_left _ _ h1)
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  have : y = v * ((u - σ u) * y) := by rw [← mul_assoc, hv, one_mul]
  rw [this]
  exact Ideal.mul_mem_left _ _ h3

end GlobalTheory.CompanionTheory.SiegLoc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectTensorProduct
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectTensorProduct
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem frobenius_symm_smul {p : ℕ} {A C : Type} [CommRing A] [CommRing C] [Algebra A C]
    (FA : A ≃+* A) (hFA : ∀ x, FA x = x ^ p) (FC : C ≃+* C) (hFC : ∀ x, FC x = x ^ p)
    (a : A) (c : C) : FC.symm (a • c) = FA.symm a • FC.symm c := by
  apply FC.injective
  rw [RingEquiv.apply_symm_apply, Algebra.smul_def, Algebra.smul_def, map_mul,
    RingEquiv.apply_symm_apply, hFC, ← map_pow (algebraMap A C), ← hFA (FA.symm a),
    RingEquiv.apply_symm_apply]

private theorem exists_ringEquiv_frobenius_of_pf (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (h : Pf p A) :
    ∃ F : A ≃+* A, ∀ x, F x = x ^ p := by
  obtain ⟨g, hg⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p A h.char 1
  have hg' : ∀ x, g x = x ^ p := fun x => by rw [hg, pow_one]
  have hb : Function.Bijective g := by
    have e : (g : A → A) = fun x => x ^ p := funext hg'
    rw [e]
    exact h.bij
  exact ⟨RingEquiv.ofBijective g hb, fun x => by rw [RingEquiv.ofBijective_apply, hg']⟩

theorem pf_tensor : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (B : Type) [CommRing B]
    [Algebra A B] (K : Type) [CommRing K] [Algebra A K], Pf p A → Pf p B → Pf p K →
    Pf p (B ⊗[A] K) := by
  intro p _ A _ B _ _ K _ _ hA hB hK
  obtain ⟨FA, hFA⟩ := exists_ringEquiv_frobenius_of_pf p A hA
  obtain ⟨FB, hFB⟩ := exists_ringEquiv_frobenius_of_pf p B hB
  obtain ⟨FK, hFK⟩ := exists_ringEquiv_frobenius_of_pf p K hK
  have hchar : (p : B ⊗[A] K) = 0 := by
    have h := map_natCast (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] K) p
    rw [← h, hB.char, map_zero]
  obtain ⟨g, hg⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p (B ⊗[A] K) hchar 1
  have hg' : ∀ x, g x = x ^ p := fun x => by rw [hg, pow_one]
  let f : B →+ K →+ B ⊗[A] K :=
    AddMonoidHom.mk' (fun b => AddMonoidHom.mk' (fun k => FB.symm b ⊗ₜ[A] FK.symm k)
      (fun k k' => by rw [map_add (f := _), TensorProduct.tmul_add]))
      (fun b b' => by
        ext k
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add (f := _), TensorProduct.add_tmul])
  have hf : ∀ (a : A) (b : B) (k : K), f (a • b) k = f b (a • k) := by
    intro a b k
    simp only [f, AddMonoidHom.mk'_apply]
    rw [frobenius_symm_smul FA hFA FB hFB, frobenius_symm_smul FA hFA FK hFK, TensorProduct.smul_tmul]
  have hψ : ∀ x, TensorProduct.liftAddHom f hf (g x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul b k =>
      rw [hg', Algebra.TensorProduct.tmul_pow, TensorProduct.liftAddHom_tmul]
      simp only [f, AddMonoidHom.mk'_apply]
      rw [← hFB b, ← hFK k, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hgfun : (fun x : B ⊗[A] K => x ^ p) = g := funext fun x => (hg' x).symm
  refine ⟨hchar, ?_⟩
  rw [hgfun]
  refine ⟨Function.LeftInverse.injective hψ, ?_⟩
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero g⟩
  | tmul b k =>
    obtain ⟨b', hb'⟩ := hB.bij.2 b
    obtain ⟨k', hk'⟩ := hK.bij.2 k
    have hb'' : b' ^ p = b := hb'
    have hk'' : k' ^ p = k := hk'
    refine ⟨b' ⊗ₜ[A] k', ?_⟩
    rw [hg', Algebra.TensorProduct.tmul_pow, hb'', hk'']
  | add x y hx hy =>
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hy
    exact ⟨x' + y', by rw [map_add (f := _), hx', hy']⟩

end GlobalTheory.CompanionTheory.PerfectRing
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectTensorProductStatement
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perfect_tensor_product : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : Type) [CommRing K] [Algebra A K], Pf p A → Pf p B → Pf p K → Pf p (B ⊗[A] K) := by
  first | exact @GlobalTheory.CompanionTheory.PerfectRing.pf_tensor | exact GlobalTheory.CompanionTheory.PerfectRing.pf_tensor | (intros; apply GlobalTheory.CompanionTheory.PerfectRing.pf_tensor <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectFrobeniusRootSolution
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectFrobeniusRootSolution
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem solv_of_solv_pow : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (m n k : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A), Pf p B → Solv B (fun t j => a t j ^ p ^ k) (fun t => c t ^ p ^ k) → Solv B a c := by
  intro p _ A _ B _ _ m n k a c hB hS
  obtain ⟨y, hy⟩ := hS
  obtain ⟨-, -, hroot, hinj, -⟩ := pf_facts p B hB
  obtain ⟨F, hF⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p B hB.char k
  choose y' hy' using fun j => hroot k (y j)
  refine ⟨y', fun i => hinj k _ _ ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hF, ← hF, map_sum, hF, ← map_pow, ← hy i]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hF, Algebra.smul_def, Algebra.smul_def, mul_pow, map_pow, hy' j]

end GlobalTheory.CompanionTheory.PerfectRing
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectFrobeniusRootSolutionStatement
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perfect_frobenius_root_solution : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (m n k : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A), Pf p B → Solv B (fun t j => a t j ^ p ^ k) (fun t => c t ^ p ^ k) → Solv B a c := by
  first | exact @GlobalTheory.CompanionTheory.PerfectRing.solv_of_solv_pow | exact GlobalTheory.CompanionTheory.PerfectRing.solv_of_solv_pow | (intros; apply GlobalTheory.CompanionTheory.PerfectRing.solv_of_solv_pow <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueAlgebraUnramified
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueAlgebraUnramified
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens

theorem resAlg_of_isUnrQuad : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ),
    ∀ h : IsUnrQuad R σ ϖ q ε, ResAlg (R ⧸ lev ϖ 1) (barσ σ ϖ h.fix_ϖ 1) q ε := by
  intro R _ σ ϖ q ε h
  have hτ : ∀ a : R, barσ σ ϖ h.fix_ϖ 1 (Ideal.Quotient.mk (lev ϖ 1) a) =
      Ideal.Quotient.mk (lev ϖ 1) (σ a) := fun a => Ideal.Quotient.lift_mk _ _ _
  obtain ⟨u, hu, hdec⟩ := h.basis
  refine ⟨?_, ?_, ?_, h.one_lt, h.card, h.eps⟩
  · intro e
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective e
    rw [hτ a, hτ (σ a), h.inv]
  · intro e he hne
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective e
    obtain ⟨x, y, hx, hy, rfl⟩ := hdec a
    rw [hτ] at he
    have hy0 : Ideal.Quotient.mk (lev ϖ 1) y = 0 := by
      have h1 : Ideal.Quotient.mk (lev ϖ 1) (y * (u - σ u)) = 0 := by
        have hxy : y * (u - σ u) = (x + y * u) - σ (x + y * u) := by
          rw [map_add (f := _), map_mul, hx, hy]
          ring
        rw [hxy, map_sub, he, sub_self]
      rw [map_mul] at h1
      exact (IsUnit.mul_left_eq_zero (hu.map (Ideal.Quotient.mk (lev ϖ 1)))).mp h1
    have hxe : Ideal.Quotient.mk (lev ϖ 1) (x + y * u) = Ideal.Quotient.mk (lev ϖ 1) x := by
      rw [map_add (f := _), map_mul, hy0, zero_mul, add_zero]
    rw [hxe] at hne ⊢
    exact (h.fixLocal x hx fun hmem => hne (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)).map _
  · refine ⟨Ideal.Quotient.mk (lev ϖ 1) u, ?_, ?_⟩
    · have hm := hu.map (Ideal.Quotient.mk (lev ϖ 1))
      rwa [map_sub, ← hτ] at hm
    · intro e
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective e
      obtain ⟨x, y, hx, hy, rfl⟩ := hdec a
      refine ⟨Ideal.Quotient.mk (lev ϖ 1) x, Ideal.Quotient.mk (lev ϖ 1) y, ?_, ?_, ?_⟩
      · rw [hτ, hx]
      · rw [hτ, hy]
      · rw [map_add (f := _), map_mul]

end GlobalTheory.CompanionTheory.UnrDens
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueAlgebraUnramifiedStatement
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_algebra_unramified : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), ∀ h : IsUnrQuad R σ ϖ q ε, ResAlg (R ⧸ lev ϖ 1) (barσ σ ϖ h.fix_ϖ 1) q ε := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.resAlg_of_isUnrQuad | exact GlobalTheory.CompanionTheory.UnrDens.resAlg_of_isUnrQuad | (intros; apply GlobalTheory.CompanionTheory.UnrDens.resAlg_of_isUnrQuad <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PqLift
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem pq_lift : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] (T : Type) [CommRing T]
    (T₁ : Type) [CommRing T₁] (i : S →+* T) (I : Ideal S) (φ : S →+* T₁),
    PQ p i I → Pf p T₁ → (∀ x ∈ I, φ x = 0) → ∃! ψ : T →+* T₁, ψ.comp i = φ := by
  intro p _ S _ T _ T₁ _ i I φ hPQ hPf hI
  obtain ⟨-, hred, hroot, hinj, -⟩ := pf_facts p T₁ hPf
  have hcharT : (p : T) = 0 := hPQ.pf.char
  have hcharT₁ : (p : T₁) = 0 := hPf.char
  have hA : ∀ a b : S, i a = i b → φ a = φ b := by
    intro a b hab
    obtain ⟨j, hj⟩ := (hPQ.ker (a - b)).mp (by rw [map_sub, hab, sub_self])
    have h0 := hI _ hj
    rw [map_pow, map_sub] at h0
    exact sub_eq_zero.mp (hred _ _ h0)
  have hfrobT : ∀ (k : ℕ) (u v : T), (u + v) ^ p ^ k = u ^ p ^ k + v ^ p ^ k := by
    intro k u v
    obtain ⟨F, hF⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p T hcharT k
    rw [← hF, ← hF, ← hF, map_add (f := _)]
  have hfrobT₁ : ∀ (k : ℕ) (u v : T₁), (u + v) ^ p ^ k = u ^ p ^ k + v ^ p ^ k := by
    intro k u v
    obtain ⟨F, hF⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p T₁ hcharT₁ k
    rw [← hF, ← hF, ← hF, map_add (f := _)]
  let Rel : T → T₁ → Prop := fun y z => ∃ (k : ℕ) (x : S), y ^ p ^ k = i x ∧ z ^ p ^ k = φ x
  have hex : ∀ y, ∃ z, Rel y z := by
    intro y
    obtain ⟨k, x, hx⟩ := hPQ.pow y
    obtain ⟨z, hz⟩ := hroot k (φ x)
    exact ⟨z, k, x, hx, hz⟩
  have hfun : ∀ y z z', Rel y z → Rel y z' → z = z' := by
    rintro y z z' ⟨k, x, hyx, hzx⟩ ⟨m, x', hyx', hzx'⟩
    have hi : i (x ^ p ^ m) = i (x' ^ p ^ k) := by
      rw [map_pow, map_pow, ← hyx, ← hyx', ← pow_mul, ← pow_mul, mul_comm]
    have hφ := hA _ _ hi
    rw [map_pow, map_pow, ← hzx, ← hzx', ← pow_mul, ← pow_mul, mul_comm, ← pow_add] at hφ
    exact hinj _ _ _ hφ
  choose ψf hψf using hex
  have hRelψ : ∀ y z, Rel y z → ψf y = z := fun y z h => hfun y _ _ (hψf y) h
  have hadd : ∀ y₁ y₂, ψf (y₁ + y₂) = ψf y₁ + ψf y₂ := by
    intro y₁ y₂
    apply hRelψ
    obtain ⟨k₁, x₁, hy₁, hz₁⟩ := hψf y₁
    obtain ⟨k₂, x₂, hy₂, hz₂⟩ := hψf y₂
    refine ⟨k₁ + k₂, x₁ ^ p ^ k₂ + x₂ ^ p ^ k₁, ?_, ?_⟩
    · rw [hfrobT, map_add (f := _), map_pow, map_pow, ← hy₁, ← hy₂, ← pow_mul, ← pow_mul, ← pow_add,
        ← pow_add, add_comm k₂ k₁]
    · rw [hfrobT₁, map_add (f := _), map_pow, map_pow, ← hz₁, ← hz₂, ← pow_mul, ← pow_mul, ← pow_add,
        ← pow_add, add_comm k₂ k₁]
  have hmul : ∀ y₁ y₂, ψf (y₁ * y₂) = ψf y₁ * ψf y₂ := by
    intro y₁ y₂
    apply hRelψ
    obtain ⟨k₁, x₁, hy₁, hz₁⟩ := hψf y₁
    obtain ⟨k₂, x₂, hy₂, hz₂⟩ := hψf y₂
    refine ⟨k₁ + k₂, x₁ ^ p ^ k₂ * x₂ ^ p ^ k₁, ?_, ?_⟩
    · rw [mul_pow, map_mul, map_pow, map_pow, ← hy₁, ← hy₂, ← pow_mul, ← pow_mul, ← pow_add,
        ← pow_add, add_comm k₂ k₁]
    · rw [mul_pow, map_mul, map_pow, map_pow, ← hz₁, ← hz₂, ← pow_mul, ← pow_mul, ← pow_add,
        ← pow_add, add_comm k₂ k₁]
  have h1 : ψf 1 = 1 := hRelψ 1 1 ⟨0, 1, by simp, by simp⟩
  have h0 : ψf 0 = 0 := hRelψ 0 0 ⟨0, 0, by simp, by simp⟩
  let ψ : T →+* T₁ :=
    { toFun := ψf, map_one' := h1, map_mul' := hmul, map_zero' := h0, map_add' := hadd }
  refine ⟨ψ, ?_, ?_⟩
  · ext s
    show ψf (i s) = φ s
    exact hRelψ (i s) (φ s) ⟨0, s, by simp, by simp⟩
  · intro ψ' hψ'
    ext y
    show ψ' y = ψf y
    obtain ⟨k, x, hx⟩ := hPQ.pow y
    refine (hRelψ y (ψ' y) ⟨k, x, hx, ?_⟩).symm
    rw [← map_pow, hx, ← RingHom.comp_apply, hψ']

end GlobalTheory.CompanionTheory.PerfectRing
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenIsCompactPrincipal
open ValuativeRel Matrix
open scoped Topology

namespace GlobalTheory.CompanionTheory.PrincipalCongruence

variable {k : Type*} [Field k] [ValuativeRel k]

theorem inv_congr {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n k)
    (hAB : A * B = 1) {t : k} (ht : valuation k t < 1)
    (hA : ∀ i j, valuation k (A i j - (1 : Matrix n n k) i j) ≤ valuation k t) :
    ∀ i j, valuation k (B i j - (1 : Matrix n n k) i j) ≤ valuation k t := by
  by_contra h
  push_neg at h
  obtain ⟨i₁, j₁, h₁⟩ := h
  haveI : Nonempty (n × n) := ⟨(i₁, j₁)⟩
  obtain ⟨⟨i₀, j₀⟩, hm⟩ := Finite.exists_max
    (fun p : n × n => valuation k (B p.1 p.2 - (1 : Matrix n n k) p.1 p.2))
  have hm' : ∀ l j, valuation k (B l j - (1 : Matrix n n k) l j) ≤
      valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀) := fun l j => hm (l, j)
  have hM : valuation k t < valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀) :=
    h₁.trans_le (hm' i₁ j₁)
  have hM0 : 0 < valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀) :=
    lt_of_le_of_lt zero_le' hM
  have hmat : (A - 1) * (B - 1) = -(A - 1) - (B - 1) := by
    simp only [sub_mul, mul_sub, hAB, one_mul, mul_one]
    abel
  have key : B i₀ j₀ - (1 : Matrix n n k) i₀ j₀ = -(A i₀ j₀ - (1 : Matrix n n k) i₀ j₀) -
      ∑ l, (A i₀ l - (1 : Matrix n n k) i₀ l) * (B l j₀ - (1 : Matrix n n k) l j₀) := by
    have := congrFun (congrFun hmat i₀) j₀
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.neg_apply] at this
    rw [this]
    ring
  have hsum : valuation k (∑ l, (A i₀ l - (1 : Matrix n n k) i₀ l) *
      (B l j₀ - (1 : Matrix n n k) l j₀)) ≤
      valuation k t * valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀) := by
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul]
    exact mul_le_mul' (hA i₀ l) (hm' l j₀)
  have hlt : valuation k t * valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀) <
      valuation k (B i₀ j₀ - (1 : Matrix n n k) i₀ j₀) :=
    mul_lt_of_lt_one_left hM0 ht
  have hle := Valuation.map_sub (valuation k) (-(A i₀ j₀ - (1 : Matrix n n k) i₀ j₀))
    (∑ l, (A i₀ l - (1 : Matrix n n k) i₀ l) * (B l j₀ - (1 : Matrix n n k) l j₀))
  rw [← key, Valuation.map_neg] at hle
  rcases le_max_iff.mp hle with h | h
  · exact absurd ((h.trans (hA i₀ j₀))) (not_le.mpr hM)
  · exact absurd (h.trans hsum) (not_le.mpr hlt)

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def congSet (n : Type*) [DecidableEq n] (t : k) : Set (Matrix n n k) :=
  {A | ∀ i j, valuation k (A i j - (1 : Matrix n n k) i j) ≤ valuation k t}

theorem isOpen_congSet (n : Type*) [Fintype n] [DecidableEq n] {t : k} (ht : t ≠ 0) :
    IsOpen (congSet n t) := by
  have h : congSet n t = ⋂ i, ⋂ j, (fun A : Matrix n n k => A i j - (1 : Matrix n n k) i j) ⁻¹'
      GlobalTheory.SplitWeil.cball (Units.mk0 t ht) := by
    ext A
    simp [congSet, GlobalTheory.SplitWeil.cball]
  rw [h]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact (GlobalTheory.SplitWeil.isOpen_cball _).preimage
    ((continuous_id.matrix_elem i j).sub continuous_const)

theorem isCompact_congSet (n : Type*) [Fintype n] [DecidableEq n] {t : k} (ht : t ≠ 0) :
    IsCompact (congSet n t) := by
  have h : congSet n t = Set.pi Set.univ fun i => Set.pi Set.univ fun j =>
      (fun x : k => x + (1 : Matrix n n k) i j) '' GlobalTheory.SplitWeil.cball (Units.mk0 t ht) := by
    ext A
    constructor
    · intro hA i _ j _
      exact ⟨A i j - (1 : Matrix n n k) i j, hA i j, by simp⟩
    · intro hA i j
      obtain ⟨x, hx, hxA⟩ := hA i (Set.mem_univ _) j (Set.mem_univ _)
      have hx' : A i j - (1 : Matrix n n k) i j = x := by
        rw [← hxA]
        simp
      rw [hx']
      exact hx
  rw [h]
  exact isCompact_univ_pi fun i => isCompact_univ_pi fun j =>
    (GlobalTheory.SplitWeil.isCompact_cball _).image (continuous_id.add continuous_const)

def congGL (n : Type*) [Fintype n] [DecidableEq n] (t : k) : Set (GL n k) :=
  {g | (g : Matrix n n k) ∈ congSet n t}

theorem isOpen_congGL (n : Type*) [Fintype n] [DecidableEq n] {t : k} (ht : t ≠ 0) :
    IsOpen (congGL n t) :=
  (isOpen_congSet n ht).preimage Units.continuous_val

theorem isCompact_congGL (n : Type*) [Fintype n] [DecidableEq n] {t : k} (ht : t ≠ 0)
    (ht1 : valuation k t < 1) : IsCompact (congGL n t) := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  rw [Units.isEmbedding_embedProduct.isCompact_iff]
  have hc : IsCompact ((congSet n t ×ˢ (MulOpposite.op '' congSet n t)) ∩
      {p : Matrix n n k × (Matrix n n k)ᵐᵒᵖ |
        p.1 * p.2.unop = 1 ∧ p.2.unop * p.1 = 1}) := by
    refine ((isCompact_congSet n ht).prod
      ((isCompact_congSet n ht).image MulOpposite.continuous_op)).inter_right ?_
    have hu : Continuous fun p : Matrix n n k × (Matrix n n k)ᵐᵒᵖ => p.2.unop :=
      MulOpposite.continuous_unop.comp continuous_snd
    exact (isClosed_eq (continuous_fst.matrix_mul hu) continuous_const).inter
      (isClosed_eq (hu.matrix_mul continuous_fst) continuous_const)
  convert hc using 1
  ext ⟨A, B⟩
  constructor
  · rintro ⟨g, hg, hgp⟩
    simp only [Units.embedProduct_apply, Prod.mk.injEq] at hgp
    obtain ⟨rfl, rfl⟩ := hgp
    refine ⟨⟨hg, _, inv_congr (g : Matrix n n k) _ g.mul_inv ht1 hg, rfl⟩, ?_⟩
    exact ⟨g.mul_inv, g.inv_mul⟩
  · rintro ⟨⟨hA, -⟩, h₁, h₂⟩
    refine ⟨⟨A, B.unop, h₁, h₂⟩, hA, ?_⟩
    simp [Units.embedProduct_apply]

theorem isOpen_isCompact_principal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (t : k), t ≠ 0 → ValuativeRel.valuation k (t) < 1 →
    IsOpen {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k
      ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
        ValuativeRel.valuation k (t)} ∧
    IsCompact {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k
      ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
        ValuativeRel.valuation k (t)} :=
  fun _ _ _ _ _ N _ ht ht1 => ⟨isOpen_congGL (Fin N) ht, isCompact_congGL (Fin N) ht ht1⟩

end GlobalTheory.CompanionTheory.PrincipalCongruence
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedExtensionIntegralBasis
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedExtensionIntegralBasis
open ValuativeRel Topology Filter
open PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.UnramDict

section
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem t2Space_isNonarchimedeanLocalField_singleBlock : T2Space K := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

theorem exists_pow_lt_value {a γ : ValueGroupWithZero K} (ha : a < 1) (hγ : γ ≠ 0) :
    ∃ m : ℕ, a ^ m < γ := by
  have e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have : MulArchimedean (ValueGroupWithZero K) := .comap e.toMonoidHom e.strictMono
  exact exists_pow_lt₀ ha (Units.mk0 γ hγ)

variable {K}

theorem exists_value_eq_zpow {π : K} (h0 : valuation K π ≠ 0) (h1 : valuation K π < 1)
    (hmax : ∀ x : K, valuation K x < 1 → valuation K x ≤ valuation K π) {x : K} (hx : x ≠ 0) :
    ∃ m : ℤ, valuation K x = valuation K π ^ m := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have hb0 : e (valuation K π) ≠ 0 := by
    intro h
    exact h0 (e.injective (h.trans (map_zero e).symm))
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (e.symm (WithZero.exp (-1 : ℤ)))
  have hey : e (valuation K y) = WithZero.exp (-1 : ℤ) := by rw [hy]; simp
  have hy1 : valuation K y < 1 := by
    rw [← e.strictMono.lt_iff_lt, hey, map_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hle : e (valuation K y) ≤ e (valuation K π) := e.strictMono.monotone (hmax y hy1)
  have hlt : e (valuation K π) < 1 := by simpa using e.strictMono h1
  have hb : e (valuation K π) = WithZero.exp (-1 : ℤ) := by
    obtain ⟨b, hbe⟩ : ∃ b : ℤ, e (valuation K π) = WithZero.exp b := ⟨_, (WithZero.exp_log hb0).symm⟩
    rw [hbe] at hle hlt ⊢
    rw [hey, WithZero.exp_le_exp] at hle
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
    congr 1
    omega
  have hx0 : e (valuation K x) ≠ 0 := by
    intro h
    exact (Valuation.ne_zero_iff _).2 hx (e.injective (h.trans (map_zero e).symm))
  refine ⟨-WithZero.log (e (valuation K x)), e.injective ?_⟩
  have hz : (WithZero.exp (-1 : ℤ)) ^ (-WithZero.log (e (valuation K x))) =
      e (valuation K x) := by
    rw [← WithZero.exp_zsmul]
    simpa using WithZero.exp_log hx0
  show e (valuation K x) = e (valuation K π ^ (-WithZero.log (e (valuation K x))))
  rw [map_zpow₀ e, hb, hz]

end

section Matrices

theorem mem_unitGL_iff {F : Type*} [Field F] [ValuativeRel F] {n : ℕ} (g : GL (Fin n) F) :
    g ∈ unitGL (n := Fin n) F ↔
      (∀ i j, (g : Matrix (Fin n) (Fin n) F) i j ∈ intO F) ∧
        ∀ i j, ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ intO F := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨fun i j => ((h : Matrix (Fin n) (Fin n) (intO F)) i j).2, fun i j => ?_⟩
    rw [← map_inv]
    exact (((h⁻¹ : GL (Fin n) (intO F)) : Matrix (Fin n) (Fin n) (intO F)) i j).2
  · rintro ⟨hA, hB⟩
    let f : intO F →+* F := (intO F).subtype
    let A : Matrix (Fin n) (Fin n) (intO F) := fun i j => ⟨_, hA i j⟩
    let B : Matrix (Fin n) (Fin n) (intO F) := fun i j => ⟨_, hB i j⟩
    have hinj : Function.Injective (f.mapMatrix (m := Fin n)) :=
      Matrix.map_injective Subtype.val_injective
    have hAf : f.mapMatrix A = (g : Matrix (Fin n) (Fin n) F) := by ext i j; rfl
    have hBf : f.mapMatrix B = ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
      ext i j; rfl
    have hAB : A * B = 1 := hinj (by rw [map_mul, hAf, hBf, map_one]; exact Units.mul_inv g)
    have hBA : B * A = 1 := hinj (by rw [map_mul, hAf, hBf, map_one]; exact Units.inv_mul g)
    exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hAf⟩

end Matrices

section Extension

variable {k E : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [Algebra k E]

theorem value_algebraMap_le_iff [ValuativeExtension k E] (a b : k) :
    valuation E (algebraMap k E a) ≤ valuation E (algebraMap k E b) ↔
      valuation k a ≤ valuation k b := by
  rw [← Valuation.Compatible.vle_iff_le, ← Valuation.Compatible.vle_iff_le,
    ValuativeExtension.vle_iff_vle]

theorem tendsto_pow_zero {x : E} (hx : valuation E x < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero' E).tendsto_right_iff]
  intro γ hγ
  obtain ⟨m, hm⟩ := exists_pow_lt_value E hx hγ
  filter_upwards [eventually_ge_atTop m] with n hn
  show valuation E (x ^ n) < γ
  rw [map_pow]
  exact (pow_le_pow_right_of_le_one' hx.le hn).trans_lt hm

theorem continuous_algebraMap_of_lt_one [ValuativeExtension k E] {π : k}
    (h0 : valuation E (algebraMap k E π) ≠ 0) (h1 : valuation E (algebraMap k E π) < 1) :
    Continuous (algebraMap k E) := by
  refine continuous_of_continuousAt_zero (algebraMap k E) ?_
  rw [ContinuousAt, map_zero, (IsValuativeTopology.hasBasis_nhds_zero' E).tendsto_right_iff]
  intro γ hγ
  obtain ⟨m, hm⟩ := exists_pow_lt_value E h1 hγ
  have hπ0 : π ≠ 0 := by
    rintro rfl
    simp at h0
  have hmem : {a : k | valuation k a < valuation k (π ^ m)} ∈ 𝓝 (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem (by simpa using pow_ne_zero m hπ0)
  filter_upwards [hmem] with a ha
  have h2 : valuation E (algebraMap k E a) < valuation E (algebraMap k E (π ^ m)) := by
    rw [← not_le, value_algebraMap_le_iff, not_le]
    exact ha
  show valuation E (algebraMap k E a) < γ
  refine h2.trans_le ?_
  rw [map_pow, map_pow]
  exact hm.le

theorem continuous_linearMap [FiniteDimensional k E] [ContinuousSMul k E] (f : E →ₗ[k] E) :
    Continuous f := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField k := Valued.toNontriviallyNormedField k (ValueGroupWithZero k)
  haveI := t2Space_isNonarchimedeanLocalField_singleBlock E
  exact f.continuous_of_finiteDimensional

theorem value_lt_one_of_continuous (τ : E ≃ₐ[k] E) (hτ : Continuous τ) {x : E}
    (hx : valuation E x < 1) : valuation E (τ x) < 1 := by
  have ht : Tendsto (fun n : ℕ => τ (x ^ n)) atTop (𝓝 0) := by
    have h := (hτ.tendsto 0).comp (tendsto_pow_zero hx)
    rw [map_zero] at h
    exact h
  have hmem : {y : E | valuation E y < 1} ∈ 𝓝 (0 : E) :=
    (IsValuativeTopology.hasBasis_nhds_zero' E).mem_of_mem one_ne_zero
  obtain ⟨n, hn, hn0⟩ := ((ht.eventually hmem).and (eventually_gt_atTop 0)).exists
  by_contra hc
  have h1 : 1 ≤ valuation E (τ x) ^ n := one_le_pow₀ (not_lt.1 hc)
  have h2 : valuation E (τ (x ^ n)) < 1 := hn
  rw [map_pow, map_pow] at h2
  exact absurd h2 (not_lt.2 h1)

theorem value_le_one_of_continuous (hc : ∀ τ : E ≃ₐ[k] E, Continuous τ) (τ : E ≃ₐ[k] E) {x : E}
    (hx : valuation E x ≤ 1) : valuation E (τ x) ≤ 1 := by
  by_contra h
  have h1 : 1 < valuation E (τ x) := not_le.1 h
  have hy0 : valuation E (τ x) ≠ 0 := (zero_lt_one.trans h1).ne'
  have h2 : valuation E (τ x)⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ h1
  have h3 := value_lt_one_of_continuous τ.symm (hc _) h2
  rw [map_inv₀, AlgEquiv.symm_apply_apply, map_inv₀] at h3
  have hx0 : valuation E x ≠ 0 := by
    intro h0
    have : x = 0 := (Valuation.zero_iff _).1 h0
    simp [this] at hy0
  exact absurd ((inv_lt_one₀ (zero_lt_iff.2 hx0)).1 h3) (not_lt.2 hx)

theorem value_eq_one_of_continuous (hc : ∀ τ : E ≃ₐ[k] E, Continuous τ) (τ : E ≃ₐ[k] E) {x : E}
    (hx : valuation E x = 1) : valuation E (τ x) = 1 := by
  refine le_antisymm (value_le_one_of_continuous hc τ hx.le) ?_
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have h1 : valuation E x⁻¹ ≤ 1 := by rw [map_inv₀, hx, inv_one]
  have h2 := value_le_one_of_continuous hc τ h1
  rw [map_inv₀, map_inv₀] at h2
  have hy0 : valuation E (τ x) ≠ 0 := by simpa using hx0
  exact (inv_le_one₀ (zero_lt_iff.2 hy0)).1 h2

theorem value_map_eq (hc : ∀ τ : E ≃ₐ[k] E, Continuous τ) {π : k}
    (h0 : valuation E (algebraMap k E π) ≠ 0) (h1 : valuation E (algebraMap k E π) < 1)
    (hmax : ∀ x : E, valuation E x < 1 → valuation E x ≤ valuation E (algebraMap k E π))
    (τ : E ≃ₐ[k] E) (x : E) : valuation E (τ x) = valuation E x := by
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨m, hm⟩ := exists_value_eq_zpow h0 h1 hmax hx
  set p := algebraMap k E π with hp
  have hy : valuation E (x * p ^ (-m)) = 1 := by
    rw [map_mul, map_zpow₀, hm, ← zpow_add₀ h0]
    simp
  have h2 := value_eq_one_of_continuous hc τ hy
  rw [map_mul, map_zpow₀ τ, hp, τ.commutes, ← hp, map_mul, map_zpow₀, zpow_neg,
    mul_inv_eq_one₀ (zpow_ne_zero _ h0)] at h2
  rw [h2, hm]

end Extension

theorem unramifiedDictionary_a : PositivityTheory.Rg.Tf.Loc.D0a := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ hun σ _
  obtain ⟨π, h1, hmax⟩ := hun
  have h0 : valuation E (algebraMap k E π) ≠ 0 := by
    obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation E)
    intro h
    have := hmax r hr1
    rw [h] at this
    exact hr0 ((Valuation.zero_iff _).1 (le_antisymm this zero_le'))
  have hcont := continuous_algebraMap_of_lt_one h0 h1
  haveI : ContinuousSMul k E := continuousSMul_of_algebraMap k E hcont
  have hc : ∀ τ : E ≃ₐ[k] E, Continuous τ := fun τ => continuous_linearMap τ.toLinearMap
  have hval := value_map_eq hc h0 h1 hmax
  have hint : ∀ a : k, algebraMap k E a ∈ intO E ↔ a ∈ intO k := by
    intro a
    have := value_algebraMap_le_iff (E := E) a 1
    simpa [Valuation.mem_integer_iff] using this
  refine ⟨hval, hint, ?_, ?_, hcont, ?_⟩
  · intro n g
    rw [mem_unitGL_iff, mem_unitGL_iff, ← map_inv]
    exact and_congr (forall₂_congr fun i j => hint _) (forall₂_congr fun i j => hint _)
  · intro τ n g
    have hτ : ∀ x : E, τ x ∈ intO E ↔ x ∈ intO E := by
      intro x
      simp only [Valuation.mem_integer_iff, hval]
    rw [mem_unitGL_iff, mem_unitGL_iff, ← map_inv]
    exact and_congr (forall₂_congr fun i j => hτ _) (forall₂_congr fun i j => hτ _)
  · intro n
    exact Continuous.units_map _ (continuous_id.matrix_map hcont)

end GlobalTheory.CompanionTheory.UnramDict
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedExtensionIntegralBasisStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_extension_integral_basis : PositivityTheory.Rg.Tf.Loc.D0a := by
  first | exact @GlobalTheory.CompanionTheory.UnramDict.unramifiedDictionary_a | exact GlobalTheory.CompanionTheory.UnramDict.unramifiedDictionary_a | (intros; apply GlobalTheory.CompanionTheory.UnramDict.unramifiedDictionary_a <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecInnerOfKerBasic
noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.E1

theorem vecInner_of_kerBasic : KerBasic → VecInner := by
  intro hK X ι _ Φ y j k u hΦ
  constructor
  · intro hk
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hk l] with z hz
    rw [hz, RCLike.inner_apply, mul_comm]
  · intro hk
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hk l] with z hz
    have h := (hK X (Φ j l) (hΦ j l)).2.2.2.2.1 z y
    rw [hz, h, RCLike.inner_apply, Complex.conj_conj, mul_comm]

end GlobalTheory.CompanionTheory.E1

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerClose
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.KernelClose

theorem kerClose : KerClose := by
  intro X Ω x y hΩ
  have hC : IsCompact ((fun o : X.G => x * o * y⁻¹) '' Ω) :=
    hΩ.image (by fun_prop)
  have hfin := X.proper _ hC
  have hsupp : ∀ φ : X.G → ℂ, Function.support φ ⊆ Ω →
      (Function.support fun γ : X.Γ => φ (x⁻¹ * (γ : X.G) * y)) ⊆ (hfin.toFinset : Set X.Γ) := by
    intro φ hφ γ hγ
    have hmem : x⁻¹ * (γ : X.G) * y ∈ Ω := hφ hγ
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    exact ⟨_, hmem, by group⟩
  have hker : ∀ φ : X.G → ℂ, Function.support φ ⊆ Ω →
      ker X.Γ φ x y = ∑ γ ∈ hfin.toFinset, φ (x⁻¹ * (γ : X.G) * y) := fun φ hφ =>
    finsum_eq_sum_of_support_subset _ (hsupp φ hφ)
  refine ⟨(hfin.toFinset.card : ℝ), Nat.cast_nonneg _, ?_⟩
  intro φ φ' ε hφ hφ' hε
  rw [hker φ hφ, hker φ' hφ', ← Finset.sum_sub_distrib]
  calc ‖∑ γ ∈ hfin.toFinset, (φ (x⁻¹ * (γ : X.G) * y) - φ' (x⁻¹ * (γ : X.G) * y))‖
      ≤ ∑ γ ∈ hfin.toFinset, ‖φ (x⁻¹ * (γ : X.G) * y) - φ' (x⁻¹ * (γ : X.G) * y)‖ :=
        norm_sum_le _ _
    _ ≤ hfin.toFinset.card • ε := Finset.sum_le_card_nsmul _ _ _ fun γ _ => hε _
    _ = (hfin.toFinset.card : ℝ) * ε := nsmul_eq_mul _ _

end GlobalTheory.CompanionTheory.KernelClose
end
