module

public import ReciprocityTheory.DualLattices.RestrictedHopfOrderApproximationStatement
public import ReciprocityTheory.DualLattices.Imports

@[expose] public section

section -- merged from ReciprocityTheory.DualLattices.HasLenCokerDet
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

lemma hasLen_of_equiv {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) {x : NNReal} (h : HasLen v R N x) : HasLen v R M x := by
  obtain ⟨k, c, ⟨f⟩, hx⟩ := h
  exact ⟨k, c, ⟨e.trans f⟩, hx⟩

theorem hasLen_coker_det' {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (hv : v.Integers R) (κ : Type) [Fintype κ] [DecidableEq κ] (X : Matrix κ κ R) :
    HasLen v R ((κ → R) ⧸ LinearMap.range X.mulVecLin) (v (algebraMap R C X.det)) := by
  set e := Fintype.equivFin κ
  set X' := X.submatrix e.symm e.symm
  have hdet : X'.det = X.det := Matrix.det_submatrix_equiv_self e.symm X
  let Φ : (κ → R) ≃ₗ[R] (Fin (Fintype.card κ) → R) := LinearEquiv.funCongrLeft R R e.symm
  have hrange : (LinearMap.range X.mulVecLin).map (Φ : (κ → R) →ₗ[R] (Fin (Fintype.card κ) → R)) =
      LinearMap.range X'.mulVecLin := by
    ext z
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      refine ⟨y ∘ e.symm, ?_⟩
      funext i
      show (X' *ᵥ (y ∘ e.symm)) i = (X *ᵥ y) (e.symm i)
      simp only [X', Matrix.mulVec, dotProduct, Matrix.submatrix_apply, Function.comp_apply]
      exact Equiv.sum_comp e.symm (fun k => X (e.symm i) k * y k)
    · rintro ⟨y, rfl⟩
      refine ⟨X *ᵥ (y ∘ e), ⟨y ∘ e, rfl⟩, ?_⟩
      funext i
      simp only [Matrix.mulVecLin_apply, X', Matrix.submatrix_mulVec_equiv, Φ,
        LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Function.comp_apply]
      simp
  have h := Smith.hasLen_coker_det hv X'
  rw [hdet] at h
  exact hasLen_of_equiv (Submodule.Quotient.equiv _ _ Φ hrange) h

theorem lenId_of_B (hB : LenIdBStatement) : LenIdStatement :=
  lenId_of (fun C _ v R _ _ hv => hasLen_coker_det' v R hv) hB

end ReciprocityTheory.PGsh.Up
end
end

section -- merged from ReciprocityTheory.DualLattices.AinfFacts
noncomputable section

open WittVector Ideal

namespace ReciprocityTheory.PGsh

namespace Ainf

variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

abbrev A := WittVector p (PreTilt O p)

def root (ε : PreTilt O p) (k : ℕ) : PreTilt O p := (frobeniusEquiv (PreTilt O p) p).symm^[k] ε

def xi (ε : PreTilt O p) : A p O := ∑ i ∈ Finset.range p, teichmuller p (root p O ε 1) ^ i

def nu (ε : PreTilt O p) : A p O := teichmuller p (root p O ε 1) - 1

lemma root_pow (ε : PreTilt O p) (k : ℕ) : root p O ε k ^ p ^ k = ε := by
  have hsp : ∀ x : PreTilt O p, ((frobeniusEquiv (PreTilt O p) p).symm x) ^ p = x := fun x => by
    rw [← frobenius_def, ← _root_.frobeniusEquiv_apply, RingEquiv.apply_symm_apply]
  induction k with
  | zero => simp [root]
  | succ k ih =>
    simp only [root] at ih ⊢
    rw [Function.iterate_succ_apply', pow_succ', pow_mul, hsp]
    exact ih

lemma torsion_free (hv : v.Integers O) (n : ℕ) (a : O) (h : a * (p : O) ^ n = 0) : a = 0 := by
  have h' := congrArg (algebraMap O C) h
  rw [map_mul, map_pow, map_natCast, map_zero] at h'
  have hpC : (p : C) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have h0 : algebraMap O C a = 0 := (mul_eq_zero.1 h').resolve_right (pow_ne_zero _ hpC)
  exact hv.hom_inj (by rw [h0, map_zero])

lemma frob_surj (hv : v.Integers O) : Function.Surjective (frobenius (ModP O p) p) := by
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap O C x) hp.out.pos
  have hvy : v y ≤ 1 := by
    have h1 : v y ^ p ≤ 1 := by
      rw [← map_pow, hy]
      exact hv.map_le_one x
    exact (pow_le_one_iff_of_nonneg (by positivity) hp.out.ne_zero).1 h1
  obtain ⟨z, rfl⟩ := hv.exists_of_le_one hvy
  refine ⟨Ideal.Quotient.mk _ z, ?_⟩
  rw [frobenius_def, ← map_pow]
  congr 1
  exact hv.hom_inj (by rw [map_pow, hy])

lemma theta_surj (hv : v.Integers O) : Function.Surjective (fontaineTheta O p) :=
  surjective_fontaineTheta (frob_surj p O hv)

lemma O_local (hv : v.Integers O) : IsLocalRing O := by
  haveI : Nontrivial O :=
    ⟨⟨(0 : O), (1 : O), fun h => by
      have h2 := congrArg (algebraMap O C) h
      simp at h2⟩⟩
  have hu : ∀ y : O, v (algebraMap O C y) = 1 → IsUnit y := fun y hy =>
    hv.isUnit_of_one (isUnit_iff_ne_zero.2 fun h0 => by
      rw [h0, map_zero] at hy
      exact zero_ne_one hy) hy
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  rcases (hv.map_le_one x).lt_or_eq with hlt | heq
  · right
    apply hu
    rw [map_sub, map_one]
    exact Valuation.map_one_sub_of_lt v hlt
  · left
    exact hu x heq

lemma sepO (a : O) (h : ∀ n : ℕ, a ∈ span {(p : O) ^ (n + 1)}) : a = 0 := by
  apply IsHausdorff.haus' (I := span {(p : O)})
  intro n
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  cases n with
  | zero => simp
  | succ k => exact SModEq.zero.2 (h k)

lemma quot_nontrivial {R : Type} [CommRing R] (I : Ideal R) (hI : I ≠ ⊤) : Nontrivial (R ⧸ I) :=
  Ideal.Quotient.nontrivial_iff.2 hI

lemma local_of_surj_sq {S T : Type} [CommRing S] [CommRing T] [IsLocalRing T] (f : S →+* T)
    (hf : Function.Surjective f) (hk : ∀ k ∈ RingHom.ker f, k * k = 0) : IsLocalRing S := by
  haveI : Nontrivial S := hf.nontrivial
  have key : ∀ y : S, IsUnit (f y) → IsUnit y := by
    intro y hy
    obtain ⟨u, hu⟩ := hy
    obtain ⟨z, hz⟩ := hf (↑u⁻¹ : T)
    have hker : y * z - 1 ∈ RingHom.ker f := by
      rw [RingHom.mem_ker, RingHom.map_sub, map_mul, map_one, hz, ← hu, Units.mul_inv, sub_self]
    have hsq := hk _ hker
    have h1 : y * (z * (1 - (y * z - 1))) = 1 := by linear_combination -hsq
    exact ⟨⟨y, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (f x) with h | h
  · exact Or.inl (key x h)
  · exact Or.inr (key (1 - x) (by rwa [map_sub, map_one]))

variable (hv : v.Integers O) (ε : PreTilt O p)
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
include hv hε

lemma ker_theta : RingHom.ker (fontaineTheta O p) = span {xi p O ε} := by
  obtain ⟨pflat, hpf⟩ := exists_pflat (p := p) (C := _) (v := v) (O := O) (hv := hv)
  have hX := xiNu p _ v O (kerTheta (p := p) (C := C) (O := O) (v := v) hv) ε hv hε
  simp only [xi, nu, root, Function.iterate_one] at *
  exact (hX.2.2.2 pflat hpf).1

lemma theta_xi : fontaineTheta O p (xi p O ε) = 0 := by
  rw [← RingHom.mem_ker, ker_theta p O hv ε hε]
  exact Ideal.mem_span_singleton_self _

lemma xi_nzd (y : A p O) (hy : y * xi p O ε = 0) : y = 0 := by
  obtain ⟨pflat, hpf⟩ := exists_pflat (p := p) (C := _) (v := v) (O := O) (hv := hv)
  have hK := (kerTheta (p := p) (C := C) (O := O) (v := v) hv) pflat hpf
  have hX := xiNu p _ v O (kerTheta (p := p) (C := C) (O := O) (v := v) hv) ε hv hε
  simp only [xi, nu, root, Function.iterate_one] at *
  obtain ⟨u, hu⟩ := (hX.2.2.2 pflat hpf).2
  rw [hu, ← mul_assoc] at hy
  have h1 : y * ↑u = 0 := (mem_nonZeroDivisors_iff.1 hK.2.1).2 _ hy
  have h2 : y * ↑u * ↑u⁻¹ = 0 := by rw [h1, zero_mul]
  rwa [mul_assoc, Units.mul_inv, mul_one] at h2

lemma teich_eps : teichmuller p ε = 1 + nu p O ε * xi p O ε := by
  have hX := xiNu p _ v O (kerTheta (p := p) (C := C) (O := O) (v := v) hv) ε hv hε
  simp only [xi, nu, root, Function.iterate_one] at *
  linear_combination hX.1

lemma theta_nu : fontaineTheta O p (nu p O ε) ≠ 0 := by
  have hX := xiNu p _ v O (kerTheta (p := p) (C := C) (O := O) (v := v) hv) ε hv hε
  simp only [xi, nu, root, Function.iterate_one] at *
  rw [hX.2.1]
  exact sub_ne_zero.2 (hε.ne_one hp.out.one_lt)

lemma untilt_eps : ε.untilt = 1 := by
  have he : ε = ((frobeniusEquiv (PreTilt O p) p).symm ε) ^ p := by
    rw [← frobenius_def, ← _root_.frobeniusEquiv_apply, RingEquiv.apply_symm_apply]
  rw [he, map_pow, hε.pow_eq_one]

end Ainf

end ReciprocityTheory.PGsh
end
end

section -- merged from ReciprocityTheory.DualLattices.EmbeddingSeparatingGroupStatement
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def EmbeddingSeparatingGroupStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    p ≠ 2 → HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H),
    ∃ (G : Type) (_ : CommGroup G) (_ : Fintype G) (β : G → O),
      (∀ γ γ', H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ')) ∧ H.ρ (β 1) = 1 ∧
      IsUnit (Fintype.card G : R) ∧
      (∀ i γ, U.εT i ≠ 0 → U.sg (U.φ i) (β γ) = U.sg i (β γ) ^ p) ∧
      (∀ i k, U.εT i ≠ 0 → U.εT k ≠ 0 → i ≠ k →
        ∃ γ, v (algebraMap R C (U.sg i (β γ) - U.sg k (β γ))) = 1) ∧
      (∀ i, U.εT i ≠ 0 → ∃ γ, v (algebraMap R C (U.sg i (β γ) - 1)) = 1)

def EigenElementaryDivisorStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal),
    (∀ i, HasLen v R (xModE H.Ht (bt2 H U) U.εT U.εL U.cj i) (X i)) →
    ∃ (κ : Ix g → Fin U.m) (Λ : Matrix (Ix g) (Ix g) R) (ε : Ix g → R),
      IsUnit Λ.det ∧ (∀ j, Matrix.vecMul (Λ j) (U.εT (κ j)) = Λ j) ∧
      (∀ j, ∃ c, cp = ε j * c) ∧
      (∀ i, ∏ j ∈ Finset.univ.filter (fun j => κ j = i), v (algebraMap R C (ε j)) = X i) ∧
      (∀ i (n : ℕ), Nonempty (LinearMap.range (Matrix.mulVecLin (U.εT i)) ≃ₗ[R] (Fin n → R)) →
        (Finset.univ.filter fun j => κ j = i).card = n) ∧
      (∀ i, Submodule.span R (Set.range fun k => (fromRows H.Ht (bt2 H U) * U.εT i) k) =
        Submodule.span R ((fun j => ε j • Λ j) '' {j | κ j = i}))

def EigenRankStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp) (U : UnramData p g v R O σ cp H),
    (∀ i, ∃ n : ℕ, Nonempty (LinearMap.range (Matrix.mulVecLin (U.εT i)) ≃ₗ[R] (Fin n → R)) ∧
      Nonempty (LinearMap.range (Matrix.mulVecLin (U.εT (U.φ i))) ≃ₗ[R] (Fin n → R))) ∧
    (∀ i, U.εT i = 0 → U.r i = 0)

end ReciprocityTheory.PGsh.Up
end
end

section -- merged from ReciprocityTheory.DualLattices.FormalChartAtZero
noncomputable section

open TensorProduct IsLocalRing Matrix

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2

variable {R₀ : Type} [CommRing R₀]

def tEval {σ : Type} [Fintype σ] [DecidableEq σ] {S : Type} [CommRing S] [Algebra R₀ S] (N : ℕ)
    (f : MvPowerSeries σ R₀) (a : σ → S) : S :=
  ∑ e : σ → Fin N, algebraMap R₀ S (MvPowerSeries.coeff
    (Finsupp.equivFunOnFinite.symm fun i => (e i : ℕ)) f) * ∏ i, a i ^ (e i : ℕ)


open Classical in
def nEval {σ : Type} [Fintype σ] [DecidableEq σ] {S : Type} [CommRing S] [Algebra R₀ S]
    (f : MvPowerSeries σ R₀) (a : σ → S) : S :=
  if h : ∃ N, ∀ i, a i ^ N = 0 then tEval (Nat.find h) f a else 0

def fAdd {g : ℕ} {S : Type} [CommRing S] [Algebra R₀ S] (F : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R₀)
    (a b : Fin g → S) : Fin g → S :=
  fun k => nEval (F k) (Sum.elim a b)

def IsNilOver {R K : LAlg R₀} (ρ : LHom R K) : Prop :=
  Function.Surjective ρ.1 ∧ ∀ a ∈ RingHom.ker ρ.1, IsNilpotent a

lemma map_add_ker (B : BX R₀) {R K : LAlg R₀} (ρ : LHom R K) (x y : {x : B.G R // B.map ρ x = 0}) :
    B.map ρ (x.1 + y.1) = 0 := by
  rw [map_add (f := _), x.2, y.2, add_zero]

lemma map_nat_ker (B : BX R₀) {R R' K : LAlg R₀} (ρ : LHom R K) (ρ' : LHom R' K) (f : LHom R R')
    (hf : ρ'.comp f = ρ) (x : {x : B.G R // B.map ρ x = 0}) : B.map ρ' (B.map f x.1) = 0 := by
  rw [← B.map_comp, hf, x.2]

lemma map_tg_ker (B : BX R₀) {R S K : LAlg R₀} (ρ : LHom R K) (π : LHom R S) (hπ : π.SqZero)
    (ρS : LHom S K) (hfac : ρS.comp π = ρ) (w : B.gg ⊗[R₀] π.ker) : B.map ρ (B.tg π hπ w) = 0 := by
  rw [← hfac, B.map_comp, (B.tg_ker π hπ _).2 ⟨w, rfl⟩, map_zero]

structure FormalChartAtZero (B : BX R₀) (K : LAlg R₀) (g : ℕ) where
  F : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R₀
  F_unit : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S), (∀ i, IsNilpotent (a i)) →
    fAdd F a 0 = a
  F_comm : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b : Fin g → S), (∀ i, IsNilpotent (a i)) →
    (∀ i, IsNilpotent (b i)) → fAdd F a b = fAdd F b a
  F_assoc : ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a b c : Fin g → S),
    (∀ i, IsNilpotent (a i)) → (∀ i, IsNilpotent (b i)) → (∀ i, IsNilpotent (c i)) →
    fAdd F (fAdd F a b) c = fAdd F a (fAdd F b c)

  gb : Module.Basis (Fin g) R₀ B.gg
  χ : ∀ {R : LAlg R₀} (ρ : LHom R K), IsNilOver ρ →
    {x : B.G R // B.map ρ x = 0} ≃ (Fin g → maximalIdeal (R : Type))
  χ_add : ∀ {R : LAlg R₀} (ρ : LHom R K) (hρ : IsNilOver ρ) (x y : {x : B.G R // B.map ρ x = 0}),
    (fun k => ((χ ρ hρ ⟨x.1 + y.1, map_add_ker B ρ x y⟩ k : maximalIdeal (R : Type)) : (R : Type))) =
      fAdd F (fun k => (χ ρ hρ x k : (R : Type))) (fun k => (χ ρ hρ y k : (R : Type)))
  χ_nat : ∀ {R R' : LAlg R₀} (ρ : LHom R K) (ρ' : LHom R' K) (hρ : IsNilOver ρ) (hρ' : IsNilOver ρ')
    (f : LHom R R') (hf : ρ'.comp f = ρ) (x : {x : B.G R // B.map ρ x = 0}) (k : Fin g),
    ((χ ρ' hρ' ⟨B.map f x.1, map_nat_ker B ρ ρ' f hf x⟩ k : maximalIdeal (R' : Type)) : (R' : Type)) =
      f.1 (χ ρ hρ x k : (R : Type))
  χ_tg : ∀ {R S : LAlg R₀} (ρ : LHom R K) (hρ : IsNilOver ρ) (π : LHom R S) (hπ : π.SqZero)
    (ρS : LHom S K) (hfac : ρS.comp π = ρ) (w : B.gg) (i : π.ker) (k : Fin g),
    ((χ ρ hρ ⟨B.tg π hπ (w ⊗ₜ i), map_tg_ker B ρ π hπ ρS hfac _⟩ k : maximalIdeal (R : Type)) :
      (R : Type)) = gb.repr w k • (i : (R : Type))

structure SM (B : BX R₀) (K W : LAlg R₀) (ρW : LHom W K) : Prop where
  nil : IsNilOver ρW
  onto : Function.Surjective (B.map ρW)

abbrev algOf {O S : LAlg R₀} (s : LHom O S) : Algebra (O : Type) (S : Type) := s.1.toRingHom.toAlgebra

structure FIN (B : BX R₀) (O : LAlg R₀) (p : ℕ) where
  ι : Type
  [fι : Fintype ι]
  [dι : DecidableEq ι]
  AAx : ι → LAlg R₀
  sO : ∀ i, LHom O (AAx i)
  free : ∀ i, letI := algOf (sO i); Module.Free (O : Type) (AAx i : Type) ∧ Module.Finite (O : Type) (AAx i : Type)
  y : ∀ i, B.G (AAx i)
  y_p : ∀ i, p • y i = 0
  univ : ∀ (S : LAlg R₀) (s : LHom O S) (z : B.G S), p • z = 0 →
    ∃ i, ∃ φ : LHom (AAx i) S, φ.comp (sO i) = s ∧ B.map φ (y i) = z ∧
      ∀ j (φ' : LHom (AAx j) S), φ'.comp (sO j) = s → B.map φ' (y j) = z → j = i ∧ HEq φ' φ
  sep : ∀ i (f : (AAx i : Type)), (∀ φ : LHom (AAx i) O, φ.comp (sO i) = LHom.id O → φ.1 f = 0) → f = 0
  rank : (∑ i, (letI := algOf (sO i); Module.finrank (O : Type) (AAx i : Type))) =
    Nat.card {t : B.G O // p • t = 0}

attribute [instance] FIN.fι FIN.dι

def torP (B : BX R₀) (p : ℕ) (S : LAlg R₀) : AddSubgroup (B.G S) where
  carrier := {z | p • z = 0}
  add_mem' {a b} ha hb := by
    change p • a = 0 at ha
    change p • b = 0 at hb
    change p • (a + b) = 0
    rw [smul_add, ha, hb, add_zero]
  zero_mem' := smul_zero p
  neg_mem' {a} ha := by
    change p • a = 0 at ha
    change p • (-a) = 0
    rw [smul_neg, ha, neg_zero]

lemma mem_torP (B : BX R₀) (p : ℕ) {S : LAlg R₀} (z : B.G S) : z ∈ torP B p S ↔ p • z = 0 := Iff.rfl

lemma map_torP (B : BX R₀) (p : ℕ) {S S' : LAlg R₀} (f : LHom S S') (x : torP B p S) :
    B.map f (x : B.G S) ∈ torP B p S' := by
  refine (mem_torP B p _).2 ?_
  rw [← map_nsmul, (mem_torP B p _).1 x.2, map_zero]

lemma tg_torP (B : BX R₀) (p : ℕ) {R S : LAlg R₀} (π : LHom R S) (hπ : π.SqZero) (w : B.gg)
    (i : π.ker) (hi : p • i = 0) : B.tg π hπ (w ⊗ₜ i) ∈ torP B p R := by
  refine (mem_torP B p _).2 ?_
  rw [← map_nsmul, ← TensorProduct.tmul_smul, hi, TensorProduct.tmul_zero, map_zero]

structure OAct (B : BX R₀) (O : LAlg R₀) (p : ℕ) (E : Type) [CommRing E] where
  act : E → ∀ S : LAlg R₀, LHom O S → torP B p S →+ torP B p S
  act_one : ∀ S s x, act 1 S s x = x
  act_mul : ∀ a b S s x, act (a * b) S s x = act a S s (act b S s x)
  act_add : ∀ a b S s x, act (a + b) S s x = act a S s x + act b S s x
  act_nat : ∀ a {S S' : LAlg R₀} (s : LHom O S) (s' : LHom O S') (f : LHom S S'), f.comp s = s' →
    ∀ x, B.map f (act a S s x : B.G S) = act a S' s' ⟨B.map f x, map_torP B p f x⟩
  actL : E → B.gg →ₗ[R₀] B.gg
  act_tg : ∀ a {R S : LAlg R₀} (s : LHom O R) (π : LHom R S) (hπ : π.SqZero) (w : B.gg)
    (i : π.ker) (hi : p • i = 0),
    (act a R s ⟨B.tg π hπ (w ⊗ₜ i), tg_torP B p π hπ w i hi⟩ : B.G R) = B.tg π hπ (actL a w ⊗ₜ i)

def wS (p : ℕ) (n : ℕ) : MvPolynomial (Fin n) ℤ :=
  let q : MvPolynomial (Fin n) ℤ := (∑ j, (MvPolynomial.X j) ^ p) - (∑ j, MvPolynomial.X j) ^ p
  ∑ m ∈ q.support, MvPolynomial.monomial m (q.coeff m / (p : ℤ))

structure WData {p : ℕ} [Fact p.Prime] (Tw : ATowerL R₀ p) (K : LAlg R₀) where
  W : LAlg R₀
  ρW : LHom W K
  ρ1 : LHom (Tw.R 0) K
  ψ : LHom (Tw.R' 1) W
  πW : LHom W (Tw.R 0)
  πW_surj : Function.Surjective πW.1
  ρW_eq : ρ1.comp πW = ρW
  p_sq : ((p : (W : Type))) ^ 2 = 0
  ker_πW : RingHom.ker πW.1 = Ideal.span {(p : (W : Type))}
  ann_p : ∀ a : (W : Type), (p : (W : Type)) * a = 0 ↔ πW.1 a = 0
  compat : ∀ a, πW.1 (ψ.1 a) = (Tw.r 0).1 ((Tw.π 1).1 a)
  b : (W : Type)ˣ
  ξ_img : ψ.1 (Tw.ξ 1) = p * b
  Rb : Type
  [rb : CommRing Rb]
  [rbc : CharP Rb p]
  [rbp : PerfectRing Rb p]
  T : Rb →* (W : Type)
  decomp : ∀ w : (W : Type), ∃ c : Rb, ∃ c' : (W : Type), w = T c + p * c'
  witt_add : ∀ (n : ℕ) (a : Fin n → Rb), ∑ j, T (a j) =
    T (∑ j, a j) + p * T (MvPolynomial.eval₂ (Int.castRingHom Rb)
      (fun j => (frobeniusEquiv Rb p).symm (a j)) (wS p n))
  T_kill : ∀ c : Rb, πW.1 (T c) = 0 → T c = 0

attribute [instance] WData.rb WData.rbc WData.rbp

structure HodgeTateData (p : ℕ) [Fact p.Prime] (g : ℕ) (R : Type) [CommRing R] [Algebra ℤ_[p] R]
    (Oe : Type) [CommRing Oe] [Algebra ℤ_[p] Oe] (σ : Oe ≃ₐ[ℤ_[p]] Oe) (cp : R) where
  ρ : Oe →ₐ[ℤ_[p]] Matrix (Ix g) (Ix g) ℤ_[p]
  ρL : Oe →+* Matrix (Fin g) (Fin g) R
  P : Matrix (Ix g) (Ix g) ℤ_[p]
  PL : Matrix (Fin g) (Fin g) R
  E : Matrix (Ix g) (Ix g) ℤ_[p]
  E_alternating : Eᵀ = -E ∧ ∀ i, E i i = 0
  isUnit_det_E : IsUnit E.det
  E_equivariant : ∀ a, (ρ a)ᵀ * E = E * ρ (σ a)
  projectors : P * P = P ∧ PL * PL = PL ∧ Pᵀ * E = E * P ∧
    (∀ a, P * ρ a = ρ a * P) ∧ ∀ a, PL * ρL a = ρL a * PL
  Ht : Matrix (Fin g) (Ix g) R
  Bt : Matrix (Fin g) (Ix g) R
  Ht_equivariant : (∀ a, Ht * (ρ a).map (algebraMap ℤ_[p] R) = (ρL (σ a))ᵀ * Ht) ∧
    Ht * P.map (algebraMap ℤ_[p] R) = PLᵀ * Ht
  form_eq_alt : Btᵀ * Ht - Htᵀ * Bt = cp • E.map (algebraMap ℤ_[p] R)

def ptOf (B : BX R₀) {O : LAlg R₀} {g : ℕ} {p : ℕ} (τ : Ix g → ℕ → B.G O) (t : Ix g → ZMod p) : B.G O :=
  ∑ j, (t j).val • τ j 0

structure Link {p : ℕ} [Fact p.Prime] {g : ℕ} (B : BX R₀) (Tw : ATowerL R₀ p) (Dt : DualTower Tw)
    [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
    {cp : (Tw.O : Type)} (H : HodgeTateData p g (Tw.O : Type) Oe σ cp) (gb : Module.Basis (Fin g) R₀ B.gg)
    (A : OAct B Tw.O p Oe) where
  τ : Ix g → ℕ → B.G Tw.O
  τ_tors : ∀ i n, (p ^ (n + 1)) • τ i n = 0
  τ_compat : ∀ i n, τ i n = p • τ i (n + 1)
  τ_basis : Function.Bijective (fun t : Ix g → ZMod p =>
    (⟨ptOf B τ t, by
      simp only [ptOf, Finset.smul_sum, smul_comm p]
      exact Finset.sum_eq_zero fun j _ => by
        have h := τ_tors j 0
        rw [zero_add, pow_one] at h
        rw [h, smul_zero]⟩ : {x : B.G Tw.O // p • x = 0}))
  ht : Ix g → B.gg →ₗ[R₀] (Tw.O : Type)
  bt : Ix g → B.gg ⊗[R₀] (Tw.O : Type)
  ht_spec : ∀ i n, B.IsHeight (Dt.Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (τ i n))
    ((Tw.q n).1.toLinearMap ∘ₗ ht i)
  bt_spec : ∀ i n, ∃ (th : B.G (Tw.R' n)) (w : B.gg ⊗[R₀] (Tw.R' n : Type)),
    B.map (Tw.π n) th = B.map (Tw.q n) (τ i n) ∧
    (p ^ (n + 1)) • th = B.tg (Tw.π n) (Tw.sqZero n)
      (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w) ∧
    LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap w =
      LinearMap.lTensor B.gg (Tw.q n).1.toLinearMap (bt i)
  Ht_eq : ∀ k i, H.Ht k i = ht i (gb k)
  Bt_eq : ∀ k i, H.Bt k i = (Module.Basis.baseChange (Tw.O : Type) gb).repr
    (TensorProduct.comm R₀ B.gg (Tw.O : Type) (bt i)) k
  E_spec : ∀ i j n, ∃ k : ℕ, (Tw.q n).1 (algebraMap ℤ_[p] (Tw.O : Type) (H.E i j)) = k ∧
    B.IsPairing (p ^ (n + 1)) (τ i n) (τ j n) (Tw.ζ n ^ k)
  ρ_spec : ∀ a j, (A.act a Tw.O (LHom.id Tw.O) ⟨τ j 0, (mem_torP B p _).2 (by
      have h := τ_tors j 0
      rwa [zero_add, pow_one] at h)⟩ : B.G Tw.O) = ∑ k, (PadicInt.toZMod (H.ρ a k j)).val • τ k 0
  ρL_spec : ∀ a k l, H.ρL a k l = algebraMap R₀ (Tw.O : Type) (gb.repr (A.actL a (gb l)) k)

end ReciprocityTheory.PGsh.Be2
end
end

section -- merged from ReciprocityTheory.DualLattices.LiftMonomialDeterminantStatement
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section FrobDefs

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}

def xL (D : Lifts H U X) (j : Ix g) (y : Nb p g) : C := algebraMap R C (D.ε j) * D.u j y

def monX (D : Lifts H U X) (α y : Nb p g) : C := ∏ j, xL D j y ^ (α j).val

def valM (D : Lifts H U X) : Matrix (Nb p g) (Nb p g) C := Matrix.of fun y α => monX D α y

def coefX (D : Lifts H U X) (f : Nb p g → C) : Nb p g → C := (valM D)⁻¹ *ᵥ f

def linX (D : Lifts H U X) (f : Nb p g → C) (k : Ix g) : C := coefX D f (Pi.single k 1)

def blockL (D : Lifts H U X) (τ : Fin U.m) : Submodule R (Ix g → R) where
  carrier := {c | ∀ k, D.κ k ≠ τ → c k = 0}
  add_mem' := by intro a b ha hb k hk; simp [ha k hk, hb k hk]
  zero_mem' := by intro k _; rfl
  smul_mem' := by intro r a ha k hk; simp [ha k hk]

end FrobDefs

def LiftMonomialDeterminantStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal) (D : Lifts H U X), (valM D).det ≠ 0

def FrobeniusBlockStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    p ≠ 2 → HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal) (D : Lifts H U X),
    (∀ j l, D.κ l ≠ U.φ (D.κ j) → linX D (fun y => xL D j y ^ p) l = 0) ∧
    ∀ i (e : {j // D.κ j = i} ≃ {l // D.κ l = U.φ i}),
      v (Matrix.of fun j l : {j // D.κ j = i} => linX D (fun y => xL D j.1 y ^ p) (e l).1).det =
        X i ^ p / X (U.φ i)

def FrobeniusLengthBoundStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    p ≠ 2 → HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal) (D : Lifts H U X),
    (valM D).det ≠ 0 →
    H.AA.carrier = Submodule.span R (Set.range fun (α : Nb p g) (y : Nb p g) =>
      ∏ j, (algebraMap R C (D.ε j) * D.u j y) ^ (α j).val) →
    ∀ (τ : Fin U.m) (N : Submodule R (Ix g → R)) (z : NNReal), N ≤ blockL D τ →
      (∀ c ∈ N, ∃ f ∈ sqIdeal (augIdeal H.AA.carrier), ∀ k, algebraMap R C (c k) = linX D f k) →
      HasLen v R (blockL D τ ⧸ N.comap (blockL D τ).subtype) z →
      z ≤ v (algebraMap R C (p : R)) ^ U.r τ

end ReciprocityTheory.PGsh.Up
end
end

section -- merged from ReciprocityTheory.DualLattices.EigenQuotientSmithStatement
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def EigenQuotientSmithStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp) (m : ℕ) (e : Fin m → O)
    (π : Equiv.Perm (Fin m)),
    (∀ i j, e i * e j = if i = j then e i else 0) → (∀ i, σ (e i) = e (π i)) →
    (∑ i, H.ρ (e i)) + H.P = 1 → (∀ i, H.ρ (e i) * H.P = 0) →
    (∑ i, H.ρL (e i)) + H.PL = 1 → (∀ i, H.ρL (e i) * H.PL = 0) →
    ∀ w, π w ≠ w → ∀ (r : ℕ) (Bw : Matrix (Ix g) (Fin r) ℤ_[p]),
      LinearMap.range (Matrix.mulVecLin Bw) = LinearMap.range (Matrix.mulVecLin (H.ρ (e w))) →
      LinearMap.ker (Matrix.mulVecLin Bw) = ⊥ →
    ∀ X : NNReal, HasLen v R (xMod H e π w) X →
    ∃ (Λ : Matrix (Fin r) (Fin r) R) (dj : Fin r → R), IsUnit Λ.det ∧
      (∀ j, dj j • Λ j ∈ Submodule.span R (Set.range fun k : Fin g ⊕ Fin g =>
        fun i : Fin r => (phiP H e * Bw.map (algebraMap ℤ_[p] R)) k i)) ∧
      (∀ j, v (algebraMap R C cp) ≤ v (algebraMap R C (dj j))) ∧
      X = ∏ j, v (algebraMap R C (dj j))

end ReciprocityTheory.PGsh.Up
end
end
