module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
noncomputable section

namespace GlobalTheory.KumDlog

open GlobalTheory.K5

variable {p : ℕ} [Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

def IsDer (S : Subalgebra (O0 p) Ω) (D : Ω → Ω) : Prop :=
  (∀ x ∈ S, ∀ y ∈ S, IsInt (p := p) (D (x + y) - D x - D y)) ∧
  (∀ x ∈ S, ∀ y ∈ S, IsInt (p := p) (D (x * y) - x * D y - y * D x)) ∧
  ∀ c : O0 p, IsInt (p := p) (D (algebraMap (O0 p) Ω c))

def FixI (G : Subgroup (Gal p Ω)) : Subalgebra (O0 p) Ω where
  carrier := {x | IsInt (p := p) x ∧ ∀ g ∈ G, g x = x}
  mul_mem' := fun {a b} ha hb =>
    ⟨IsIntegral.mul ha.1 hb.1, fun g hg => by rw [map_mul, ha.2 g hg, hb.2 g hg]⟩
  add_mem' := fun {a b} ha hb =>
    ⟨IsIntegral.add ha.1 hb.1, fun g hg => by rw [map_add (f := _), ha.2 g hg, hb.2 g hg]⟩
  algebraMap_mem' := fun c => ⟨isIntegral_algebraMap, fun g _ => g.commutes c⟩

def Hinf (T : Tower p Ω) : Subgroup (Gal p Ω) := ⨅ n, Gn T n

def Hfix (T : Tower p Ω) (r : Ω) : Subgroup (Gal p Ω) :=
  Hinf T ⊓ MulAction.stabilizer (Gal p Ω) r

def Lev (T : Tower p Ω) (m : ℕ) : Subalgebra (O0 p) Ω :=
  Algebra.adjoin (O0 p) {T.ζ m, T.qq m}

def Vals (T : Tower p Ω) (m : ℕ) (dz dq : Ω → Ω) : Prop :=
  IsInt (p := p) (dz (T.ζ m) - p * T.ζ m / (p : Ω) ^ m) ∧ IsInt (p := p) (dz (T.qq m)) ∧
  IsInt (p := p) (dq (T.ζ m)) ∧ IsInt (p := p) (dq (T.qq m) - p * T.qq m / (p : Ω) ^ m)

def DualData (B C : Subalgebra (O0 p) Ω) {ι : Type} [Fintype ι] (u v : ι → Ω) (tr : Ω → Ω) : Prop :=
  B ≤ C ∧ (∀ x ∈ C, IsInt (p := p) x) ∧ (∀ k, u k ∈ C) ∧ (∀ k, v k ∈ C) ∧ (∀ x ∈ C, tr x ∈ B) ∧
  (∀ x ∈ C, ∀ y ∈ C, tr (x + y) = tr x + tr y) ∧ (∀ b ∈ B, ∀ x ∈ C, tr (b * x) = b * tr x) ∧
  (∀ y ∈ C, ∑ k, u k * tr (v k * y) = p * y) ∧ (∀ y ∈ C, ∑ k, v k * tr (u k * y) = p * y) ∧
  ∑ k, u k * v k = p

theorem mem_Gn {T : Tower p Ω} {n : ℕ} {g : Gal p Ω} :
    g ∈ Gn T n ↔ g (T.ζ n) = T.ζ n ∧ g (T.qq n) = T.qq n := Iff.rfl

theorem mem_Hinf {T : Tower p Ω} {g : Gal p Ω} :
    g ∈ Hinf T ↔ ∀ n, g (T.ζ n) = T.ζ n ∧ g (T.qq n) = T.qq n := by
  simp only [Hinf, Subgroup.mem_iInf, mem_Gn]

theorem mem_Hfix {T : Tower p Ω} {r : Ω} {g : Gal p Ω} :
    g ∈ Hfix T r ↔ g ∈ Hinf T ∧ g r = r := Iff.rfl

theorem int_add {x y : Ω} (hx : IsInt (p := p) x) (hy : IsInt (p := p) y) : IsInt (p := p) (x + y) := IsIntegral.add hx hy
theorem int_sub {x y : Ω} (hx : IsInt (p := p) x) (hy : IsInt (p := p) y) : IsInt (p := p) (x - y) := IsIntegral.sub hx hy
theorem int_mul {x y : Ω} (hx : IsInt (p := p) x) (hy : IsInt (p := p) y) : IsInt (p := p) (x * y) := IsIntegral.mul hx hy
theorem int_neg {x : Ω} (hx : IsInt (p := p) x) : IsInt (p := p) (-x) := IsIntegral.neg hx
theorem int_pow {x : Ω} (hx : IsInt (p := p) x) (k : ℕ) : IsInt (p := p) (x ^ k) := IsIntegral.pow hx k
theorem int_alg (c : O0 p) : IsInt (p := p) (algebraMap (O0 p) Ω c) := isIntegral_algebraMap
theorem int_zero : IsInt (p := p) (0 : Ω) := isIntegral_zero
theorem int_one : IsInt (p := p) (1 : Ω) := isIntegral_one
theorem int_nat (k : ℕ) : IsInt (p := p) (k : Ω) := by
  simpa using (int_alg (k : O0 p) : IsInt (p := p) (algebraMap (O0 p) Ω _))
theorem int_int (k : ℤ) : IsInt (p := p) (k : Ω) := by
  simpa using (int_alg (k : O0 p) : IsInt (p := p) (algebraMap (O0 p) Ω _))
theorem int_sum {ι : Type*} (s : Finset ι) (f : ι → Ω) (h : ∀ i ∈ s, IsInt (p := p) (f i)) :
    IsInt (p := p) (∑ i ∈ s, f i) := IsIntegral.sum f h
theorem int_congr {x y : Ω} (hx : IsInt (p := p) x) (h : y = x) : IsInt (p := p) y := h ▸ hx
theorem int_gal (g : Gal p Ω) {x : Ω} (hx : IsInt (p := p) x) : IsInt (p := p) (g x) :=
  IsIntegral.map (g : Ω →ₐ[O0 p] Ω) hx
theorem int_of_pow {x : Ω} {k : ℕ} (hk : 0 < k) (hx : IsInt (p := p) (x ^ k)) : IsInt (p := p) x :=
  IsIntegral.of_pow hk hx

theorem zeta_pow (T : Tower p Ω) (n j : ℕ) : T.ζ (n + j) ^ (p ^ j) = T.ζ n := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', pow_mul, ← add_assoc, T.ζpow, ih]

theorem qq_pow (T : Tower p Ω) (n j : ℕ) : T.qq (n + j) ^ (p ^ j) = T.qq n := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', pow_mul, ← add_assoc, T.qpow, ih]

theorem ppow_pos (n : ℕ) : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n

theorem int_zeta (T : Tower p Ω) (n : ℕ) : IsInt (p := p) (T.ζ n) :=
  int_of_pow (ppow_pos n) (by rw [(T.prim n).pow_eq_one]; exact int_one)

theorem zeta_ne (T : Tower p Ω) (n : ℕ) : T.ζ n ≠ 0 := (T.prim n).ne_zero (ppow_pos n).ne'

theorem int_zeta_inv (T : Tower p Ω) (n : ℕ) : IsInt (p := p) (T.ζ n)⁻¹ :=
  int_of_pow (ppow_pos n) (by rw [inv_pow, (T.prim n).pow_eq_one, inv_one]; exact int_one)

theorem kummerTower_qq_pow_level_eq_q (T : Tower p Ω) (n : ℕ) : T.qq n ^ (p ^ n) = algebraMap (O0 p) Ω (qO p) := by
  have := qq_pow T 0 n
  rwa [zero_add, T.q0] at this

theorem isUnit_qO : IsUnit (qO p) := by
  refine IsUnit.map _ (IsUnit.of_mul_eq_one (HahnSeries.single (-1 : ℤ) (1 : ℤ_[p])) ?_)
  rw [HahnSeries.single_mul_single]; simp

theorem int_qq (T : Tower p Ω) (n : ℕ) : IsInt (p := p) (T.qq n) :=
  int_of_pow (ppow_pos n) (by rw [kummerTower_qq_pow_level_eq_q]; exact int_alg _)

theorem qq_ne (T : Tower p Ω) (n : ℕ) : T.qq n ≠ 0 := by
  intro h
  have h1 := kummerTower_qq_pow_level_eq_q T n
  rw [h, zero_pow (ppow_pos (p := p) n).ne'] at h1
  exact ((isUnit_qO (p := p)).map (algebraMap (O0 p) Ω)).ne_zero h1.symm

theorem int_qq_inv (T : Tower p Ω) (n : ℕ) : IsInt (p := p) (T.qq n)⁻¹ := by
  refine int_of_pow (ppow_pos (p := p) n) ?_
  obtain ⟨w, hw⟩ := (isUnit_qO (p := p))
  rw [inv_pow, kummerTower_qq_pow_level_eq_q, ← hw]
  refine int_congr (int_alg (↑w⁻¹ : O0 p)) ?_
  exact inv_eq_of_mul_eq_one_right (by rw [← map_mul]; simp)

theorem Lev_int (T : Tower p Ω) (m : ℕ) : ∀ x ∈ Lev T m, IsInt (p := p) x := by
  have : Lev T m ≤ integralClosure (O0 p) Ω := by
    refine Algebra.adjoin_le ?_
    rintro x (rfl | rfl)
    · exact int_zeta T m
    · exact int_qq T m
  exact fun x hx => this hx

theorem zeta_mem_Lev (T : Tower p Ω) (m : ℕ) : T.ζ m ∈ Lev T m :=
  Algebra.subset_adjoin (by simp)

theorem qq_mem_Lev (T : Tower p Ω) (m : ℕ) : T.qq m ∈ Lev T m :=
  Algebra.subset_adjoin (by simp)

theorem Lev_mono (T : Tower p Ω) {m m' : ℕ} (h : m ≤ m') : Lev T m ≤ Lev T m' := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  refine Algebra.adjoin_le ?_
  rintro x (rfl | rfl)
  · rw [← zeta_pow T m j]; exact pow_mem (zeta_mem_Lev T _) _
  · rw [← qq_pow T m j]; exact pow_mem (qq_mem_Lev T _) _

theorem Lev_le_FixI (T : Tower p Ω) (m : ℕ) {G : Subgroup (Gal p Ω)} (hG : G ≤ Gn T m) :
    Lev T m ≤ FixI G := by
  refine Algebra.adjoin_le ?_
  rintro x (rfl | rfl)
  · exact ⟨int_zeta T m, fun g hg => (hG hg).1⟩
  · exact ⟨int_qq T m, fun g hg => (hG hg).2⟩

theorem Hinf_le (T : Tower p Ω) (m : ℕ) : Hinf T ≤ Gn T m := iInf_le _ m

theorem IsDer.mono {S S' : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D) (hS : S' ≤ S) :
    IsDer S' D :=
  ⟨fun x hx y hy => h.1 x (hS hx) y (hS hy), fun x hx y hy => h.2.1 x (hS hx) y (hS hy), h.2.2⟩

theorem IsDer.zero {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D) : IsInt (p := p) (D 0) := by
  simpa using h.2.2 0

theorem IsDer.one {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D) : IsInt (p := p) (D 1) := by
  simpa using h.2.2 1

theorem IsDer.sum {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D) {ι : Type*}
    (s : Finset ι) (f : ι → Ω) (hf : ∀ i ∈ s, f i ∈ S) :
    IsInt (p := p) (D (∑ i ∈ s, f i) - ∑ i ∈ s, D (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h1 := h.1 (f a) (hf a (by simp)) (∑ i ∈ s, f i)
      (sum_mem fun i hi => hf i (by simp [hi]))
    exact int_congr (int_add h1 (ih fun i hi => hf i (by simp [hi]))) (by ring)

theorem IsDer.pow {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D)
    (hS : ∀ x ∈ S, IsInt (p := p) x) {x : Ω} (hx : x ∈ S) (k : ℕ) :
    IsInt (p := p) (D (x ^ (k + 1)) - (k + 1 : ℕ) * x ^ k * D x) := by
  induction k with
  | zero => simpa using int_zero
  | succ k ih =>
    have h1 := h.2.1 x hx (x ^ (k + 1)) (pow_mem hx _)
    refine int_congr (int_add h1 (int_mul (hS x hx) ih)) ?_
    rw [← pow_succ']; push_cast; ring

theorem IsDer.pow' {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D)
    (hS : ∀ x ∈ S, IsInt (p := p) x) {x : Ω} (hx : x ∈ S) (k : ℕ) :
    IsInt (p := p) (x * D (x ^ k) - k * x ^ k * D x) := by
  rcases k with _ | k
  · simpa using int_mul (hS x hx) h.one
  · exact int_congr (int_mul (hS x hx) (h.pow hS hx k)) (by ring)

theorem IsDer.alg_mul {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D)
    (hS : ∀ x ∈ S, IsInt (p := p) x) (c : O0 p) {x : Ω} (hx : x ∈ S) :
    IsInt (p := p) (D (algebraMap (O0 p) Ω c * x) - algebraMap (O0 p) Ω c * D x) :=
  int_congr (int_add (h.2.1 _ (S.algebraMap_mem c) x hx) (int_mul (hS x hx) (h.2.2 c))) (by ring)

theorem IsDer.sub {S : Subalgebra (O0 p) Ω} {D D' : Ω → Ω} (h : IsDer S D) (h' : IsDer S D') :
    IsDer S (fun x => D x - D' x) :=
  ⟨fun x hx y hy => int_congr (int_sub (h.1 x hx y hy) (h'.1 x hx y hy)) (by ring),
   fun x hx y hy => int_congr (int_sub (h.2.1 x hx y hy) (h'.2.1 x hx y hy)) (by ring),
   fun c => int_sub (h.2.2 c) (h'.2.2 c)⟩

theorem IsDer.smul {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D) {c : Ω}
    (hc : IsInt (p := p) c) : IsDer S (fun x => c * D x) :=
  ⟨fun x hx y hy => int_congr (int_mul hc (h.1 x hx y hy)) (by ring),
   fun x hx y hy => int_congr (int_mul hc (h.2.1 x hx y hy)) (by ring),
   fun a => int_mul hc (h.2.2 a)⟩

theorem IsDer.conj {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D) (g : Gal p Ω)
    (hg : ∀ x ∈ S, g x ∈ S) : IsDer S (fun x => g.symm (D (g x))) := by
  refine ⟨fun x hx y hy => ?_, fun x hx y hy => ?_, fun c => ?_⟩
  · refine int_congr (int_gal g.symm (h.1 _ (hg x hx) _ (hg y hy))) ?_
    simp
  · refine int_congr (int_gal g.symm (h.2.1 _ (hg x hx) _ (hg y hy))) ?_
    simp
  · refine int_gal g.symm ?_
    rw [g.commutes]; exact h.2.2 c

theorem IsDer.adjoin {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D)
    (hS : ∀ x ∈ S, IsInt (p := p) x) {t : Set Ω} (ht : t ⊆ S) (h0 : ∀ x ∈ t, IsInt (p := p) (D x)) :
    ∀ x ∈ Algebra.adjoin (O0 p) t, IsInt (p := p) (D x) := by
  have hle : Algebra.adjoin (O0 p) t ≤ S := Algebra.adjoin_le ht
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact h0 x hx
  | algebraMap c => exact h.2.2 c
  | add x y hx hy ihx ihy =>
    exact int_congr (int_add (h.1 x (hle hx) y (hle hy)) (int_add ihx ihy)) (by ring)
  | mul x y hx hy ihx ihy =>
    exact int_congr (int_add (h.2.1 x (hle hx) y (hle hy))
      (int_add (int_mul (hS x (hle hx)) ihy) (int_mul (hS y (hle hy)) ihx))) (by ring)

end GlobalTheory.KumDlog
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.C1FieldNormSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraNormEqHomogeneousPolynomialInCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Imports
namespace GlobalTheory.IdealPowerMembership

open MvPolynomial

theorem main : ∀ (K L : Type) [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] [inst_3 : FiniteDimensional K L], ∃ (f : MvPolynomial (Fin (Module.finrank K L)) K), MvPolynomial.IsHomogeneous f (Module.finrank K L) ∧ ∀ (x : L), (Algebra.norm K : L → K) x = (MvPolynomial.eval fun (i : Fin (Module.finrank K L)) ↦ ((Module.Basis.repr (Module.finBasis K L) : L → Fin (Module.finrank K L) →₀ K) x : Fin (Module.finrank K L) → K) i : MvPolynomial (Fin (Module.finrank K L)) K → K) f := by
  intro K L _ _ _ _
  classical
  let b := Module.finBasis K L
  let P : Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) (MvPolynomial (Fin (Module.finrank K L)) K) :=
    fun j k => ∑ i, X i * C (Algebra.leftMulMatrix b (b i) j k)
  have hP : ∀ j k, (P j k).IsHomogeneous 1 := by
    intro j k
    apply IsHomogeneous.sum
    intro i _
    simpa using (isHomogeneous_X K i).mul (isHomogeneous_C (Fin (Module.finrank K L)) (Algebra.leftMulMatrix b (b i) j k))
  refine ⟨P.det, ?_, ?_⟩
  · rw [Matrix.det_apply]
    apply IsHomogeneous.sum
    intro σ _
    have h := IsHomogeneous.prod (Finset.univ : Finset (Fin (Module.finrank K L))) (fun i => P (σ i) i) (fun _ => 1) (fun i _ => hP (σ i) i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
    · rw [hs, one_smul]; exact h
    · rw [hs, Units.neg_smul, one_smul]; exact h.neg
  · intro x
    rw [Algebra.norm_eq_matrix_det b, RingHom.map_det]
    congr 1
    ext j k
    have hx : x = ∑ i, b.repr x i • b i := (b.sum_repr x).symm
    have e1 : Algebra.leftMulMatrix b x = ∑ i, b.repr x i • Algebra.leftMulMatrix b (b i) := by
      conv_lhs => rw [hx]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [map_smul]
    rw [e1, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [P, map_sum, eval_mul, eval_X, eval_C, Matrix.smul_apply, smul_eq_mul]
    rfl
end GlobalTheory.IdealPowerMembership
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraNormEqHomogeneousPolynomialInCoordinates
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem norm_isHomogeneous_poly_coords :
    ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L],
      ∃ f : MvPolynomial (Fin (Module.finrank K L)) K, f.IsHomogeneous (Module.finrank K L) ∧
        ∀ x : L, Algebra.norm K x =
          MvPolynomial.eval (fun i => (Module.finBasis K L).repr x i) f := by
  exact @_root_.GlobalTheory.IdealPowerMembership.main

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraNormEqHomogeneousPolynomialInCoordinatesStatement
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraNorm_eq_homogeneous_polynomial_in_coordinates : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L],
  ∃ f : MvPolynomial (Fin (Module.finrank K L)) K, f.IsHomogeneous (Module.finrank K L) ∧
    ∀ x : L, Algebra.norm K x = MvPolynomial.eval (fun i => (Module.finBasis K L).repr x i) f := by
  first | exact @GlobalTheory.norm_isHomogeneous_poly_coords | exact GlobalTheory.norm_isHomogeneous_poly_coords | (intros; apply GlobalTheory.norm_isHomogeneous_poly_coords <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.C1FieldNormSurjective
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem norm_surjective_of_norm_form {K L : Type} [Field K] [Field L] [Algebra K L] (hC : IsFirstChernClassOfLineBundle K) (m : ℕ) (hm0 : 0 < m)
    (B : Module.Basis (Fin m) K L) (f : MvPolynomial (Fin m) K) (hf : f.IsHomogeneous m)
    (hnorm : ∀ x : L, Algebra.norm K x = MvPolynomial.eval (fun i => B.repr x i) f)
    (hpow : ∀ a : K, Algebra.norm K (algebraMap K L a) = a ^ m)
    (b : K) : ∃ x : L, Algebra.norm K x = b := by
  let g : MvPolynomial (Fin (m + 1)) K :=
    MvPolynomial.rename Fin.succ f - MvPolynomial.C b * MvPolynomial.X 0 ^ m
  have hg : g.IsHomogeneous m := by
    refine (hf.rename_isHomogeneous).sub ?_
    have := (MvPolynomial.isHomogeneous_C (Fin (m + 1)) b).mul (MvPolynomial.isHomogeneous_X_pow (0 : Fin (m + 1)) m)
    rwa [zero_add] at this
  obtain ⟨y, hy0, hy⟩ := hC (m + 1) m g hg hm0 (Nat.lt_succ_self m)
  let x : L := B.equivFun.symm (fun i => y i.succ)
  have hrepr : ∀ i, B.repr x i = y i.succ := by
    intro i
    have h := congrFun (B.equivFun.apply_symm_apply (fun i => y i.succ)) i
    rw [Module.Basis.equivFun_apply] at h
    exact h
  have hev : Algebra.norm K x = b * y 0 ^ m := by
    have h1 := hy
    simp only [g, map_sub, map_mul, map_pow, MvPolynomial.eval_rename, MvPolynomial.eval_C,
      MvPolynomial.eval_X] at h1
    rw [hnorm]
    have e : (fun i => B.repr x i) = y ∘ Fin.succ := funext hrepr
    rw [e]; exact sub_eq_zero.mp h1
  have hnz : ∀ z : L, Algebra.norm K z = 0 → z = 0 := by
    intro z hz
    by_contra hz'
    have hu : IsUnit z := (isUnit_iff_ne_zero).mpr hz'
    exact (hu.map (Algebra.norm K)).ne_zero hz
  have hy00 : y 0 ≠ 0 := by
    intro h0
    apply hy0
    have hx : x = 0 := hnz x (by rw [hev, h0, zero_pow hm0.ne', mul_zero])
    funext i
    refine Fin.cases h0 (fun j => ?_) i
    have := hrepr j
    rw [hx, map_zero] at this
    simpa using this.symm
  refine ⟨x * algebraMap K L (y 0)⁻¹, ?_⟩
  rw [map_mul, hpow, hev, mul_assoc, ← mul_pow, mul_inv_cancel₀ hy00, one_pow, mul_one]

theorem norm_surjective_of_is_c1 : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L], IsFirstChernClassOfLineBundle K →
    ∀ b : K, b ≠ 0 → ∃ x : L, Algebra.norm K x = b := by
  intro K L _ _ _ _ hC b _
  obtain ⟨f, hf, hnorm⟩ := GlobalTheory.T.algebraNorm_eq_homogeneous_polynomial_in_coordinates K L
  exact norm_surjective_of_norm_form hC _ Module.finrank_pos (Module.finBasis K L) f hf hnorm
    (fun a => Algebra.norm_algebraMap a) b

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.C1FieldNormSurjectiveStatement
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebra_norm_eq_of_isFirstChernClass : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L], IsFirstChernClassOfLineBundle K →
  ∀ b : K, b ≠ 0 → ∃ x : L, Algebra.norm K x = b := by
  first | exact @GlobalTheory.norm_surjective_of_is_c1 | exact GlobalTheory.norm_surjective_of_is_c1 | (intros; apply GlobalTheory.norm_surjective_of_is_c1 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBasisOnZetaPowMulQPow
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBasisOnZetaPowMulQPow
noncomputable section
open Polynomial
namespace GlobalTheory.K5.OnFree

section General

variable {R : Type*} [CommRing R] (f : R[X]) (m : ℕ) (c : R)

abbrev relIdeal : Ideal R[X][X] := Ideal.span {C f, X ^ m - C (C c)}

abbrev topPoly : (AdjoinRoot f)[X] := X ^ m - C (algebraMap R (AdjoinRoot f) c)

def toAdj : (R[X][X] ⧸ relIdeal f m c) →ₐ[R] AdjoinRoot (topPoly f m c) :=
  Ideal.Quotient.liftₐ (relIdeal f m c)
    (Polynomial.eval₂AlgHom
      (Polynomial.aeval (AdjoinRoot.of (topPoly f m c) (AdjoinRoot.root f)))
      (AdjoinRoot.root (topPoly f m c)) (fun _ => Commute.all _ _)) (by
      have h : relIdeal f m c ≤ RingHom.ker (Polynomial.eval₂AlgHom
          (Polynomial.aeval (R := R) (AdjoinRoot.of (topPoly f m c) (AdjoinRoot.root f)))
          (AdjoinRoot.root (topPoly f m c)) (fun _ => Commute.all _ _)) := by
        rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
        constructor
        · have h1 : aeval (AdjoinRoot.of (topPoly f m c) (AdjoinRoot.root f)) f = 0 := by
            rw [← AdjoinRoot.algebraMap_eq, aeval_algebraMap_apply, AdjoinRoot.aeval_eq,
              AdjoinRoot.mk_self, map_zero]
          simpa [RingHom.mem_ker] using h1
        · have h2 := AdjoinRoot.eval₂_root (topPoly f m c)
          simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h2
          simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_pow]
          change eval₂ _ _ X ^ m - eval₂ _ _ (C (C c)) = 0
          rw [eval₂_X, eval₂_C, RingHom.coe_coe, aeval_C,
            IsScalarTower.algebraMap_apply R (AdjoinRoot f)]
          exact h2
      exact fun a ha => h ha)

def baseToQuot : AdjoinRoot f →ₐ[R] (R[X][X] ⧸ relIdeal f m c) :=
  AdjoinRoot.liftAlgHom f (Algebra.ofId R _) (Ideal.Quotient.mk (relIdeal f m c) (C X)) (by
    have h : (Ideal.Quotient.mkₐ R (relIdeal f m c)) (C f) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (by simp))
    have h2 : aeval ((Ideal.Quotient.mkₐ R (relIdeal f m c)) (CAlgHom (R := R) (X : R[X]))) f = 0 := by
      rw [aeval_algHom_apply, aeval_algHom_apply, aeval_X_left_apply]
      exact h
    exact h2)

def toQuot : AdjoinRoot (topPoly f m c) →ₐ[R] (R[X][X] ⧸ relIdeal f m c) :=
  AdjoinRoot.liftAlgHom (topPoly f m c) (baseToQuot f m c)
    (Ideal.Quotient.mk (relIdeal f m c) X) (by
    have h : (Ideal.Quotient.mk (relIdeal f m c)) (X ^ m - C (C c)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (by simp))
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C, RingHom.coe_coe, AlgHom.commutes]
    rw [map_sub, map_pow] at h
    exact h)

theorem toQuot_root : toQuot f m c (AdjoinRoot.root _) = Ideal.Quotient.mk (relIdeal f m c) X := by
  simp [toQuot]

theorem toQuot_of_root : toQuot f m c (AdjoinRoot.of _ (AdjoinRoot.root f)) =
    Ideal.Quotient.mk (relIdeal f m c) (C X) := by
  have h : baseToQuot f m c (AdjoinRoot.root f) = Ideal.Quotient.mk (relIdeal f m c) (C X) :=
    AdjoinRoot.liftAlgHom_root _ _ _ _
  rw [← h]
  simp [toQuot]

theorem toAdj_X : toAdj f m c (Ideal.Quotient.mk (relIdeal f m c) X) = AdjoinRoot.root _ := by
  change eval₂ _ _ X = _
  rw [eval₂_X]

theorem toAdj_C_X : toAdj f m c (Ideal.Quotient.mk (relIdeal f m c) (C X)) =
    AdjoinRoot.of _ (AdjoinRoot.root f) := by
  change eval₂ _ _ (C X) = _
  rw [eval₂_C, RingHom.coe_coe, aeval_X]

def adjEquiv : AdjoinRoot (topPoly f m c) ≃ₐ[R] (R[X][X] ⧸ relIdeal f m c) :=
  AlgEquiv.ofAlgHom (toQuot f m c) (toAdj f m c)
    (by
      refine Ideal.Quotient.algHom_ext R ?_
      refine Polynomial.algHom_ext' ?_ ?_
      · refine Polynomial.algHom_ext ?_
        have := toQuot_of_root f m c
        rw [← toAdj_C_X] at this
        exact this
      · have := toQuot_root f m c
        rw [← toAdj_X] at this
        exact this)
    (by
      refine AdjoinRoot.algHom_ext' ?_ ?_
      · refine AdjoinRoot.algHom_ext ?_
        have := toAdj_C_X f m c
        rw [← toQuot_of_root] at this
        exact this
      · have := toAdj_X f m c
        rw [← toQuot_root] at this
        exact this)

theorem exists_basis [Nontrivial R] (hf : f.Monic) (d : ℕ) (hd : f.natDegree = d) (hd0 : 0 < d)
    (hm : m ≠ 0) :
    ∃ b : Module.Basis (Fin d × Fin m) R (R[X][X] ⧸ relIdeal f m c),
      ∀ i j, b (i, j) = (Ideal.Quotient.mk (relIdeal f m c) (C X)) ^ (i : ℕ) *
        (Ideal.Quotient.mk (relIdeal f m c) X) ^ (j : ℕ) := by
  let b₁ : Module.Basis (Fin d) R (AdjoinRoot f) :=
    (AdjoinRoot.powerBasis' hf).basis.reindex (finCongr hd)
  have hb₁ : ∀ i, b₁ i = AdjoinRoot.root f ^ (i : ℕ) := by
    intro i
    simp only [b₁, Module.Basis.reindex_apply, PowerBasis.coe_basis]
    rfl
  haveI : Nontrivial (AdjoinRoot f) := nontrivial_of_ne _ _ (b₁.ne_zero ⟨0, hd0⟩)
  have hg : (topPoly f m c).Monic := monic_X_pow_sub_C _ hm
  have hgd : (topPoly f m c).natDegree = m := natDegree_X_pow_sub_C _
  let b₂ : Module.Basis (Fin m) (AdjoinRoot f) (AdjoinRoot (topPoly f m c)) :=
    (AdjoinRoot.powerBasis' hg).basis.reindex (finCongr hgd)
  have hb₂ : ∀ j, b₂ j = AdjoinRoot.root (topPoly f m c) ^ (j : ℕ) := by
    intro j
    simp only [b₂, Module.Basis.reindex_apply, PowerBasis.coe_basis]
    rfl
  refine ⟨(b₁.smulTower b₂).map (adjEquiv f m c).toLinearEquiv, fun i j => ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.smulTower_apply, hb₁, hb₂, Algebra.smul_def,
    AdjoinRoot.algebraMap_eq, ← toQuot_of_root, ← toQuot_root, ← map_pow (toQuot f m c),
    ← map_pow (toQuot f m c), ← map_mul, map_pow]
  rfl

end General

theorem on_free (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    ∃ b : Module.Basis (Fin (Nat.totient (p ^ n)) × Fin (p ^ n)) (O0 p) (On p n),
      ∀ i j, b (i, j) = xn p n ^ (i : ℕ) * yn p n ^ (j : ℕ) := by
  rcases subsingleton_or_nontrivial (O0 p) with h | h
  · haveI : Subsingleton (On p n) := Module.subsingleton (O0 p) _
    exact ⟨Module.Basis.ofRepr (LinearEquiv.ofSubsingleton _ _), fun _ _ => Subsingleton.elim _ _⟩
  · have hpos : 0 < p ^ n := pow_pos hp.out.pos n
    exact exists_basis (cyclotomic (p ^ n) (O0 p)) (p ^ n) (qO p) (cyclotomic.monic _ _) _
      (natDegree_cyclotomic _ _) (Nat.totient_pos.2 hpos) hpos.ne'

end GlobalTheory.K5.OnFree
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBasisOnZetaPowMulQPowStatement
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_On_zeta_pow_mul_q_pow : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), ∃ b : Module.Basis (Fin (Nat.totient (p ^ n)) × Fin (p ^ n)) (O0 p) (On p n),
  ∀ i j, b (i, j) = xn p n ^ (i : ℕ) * yn p n ^ (j : ℕ) := by
  first | exact @GlobalTheory.K5.OnFree.on_free | exact GlobalTheory.K5.OnFree.on_free | (intros; apply GlobalTheory.K5.OnFree.on_free <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PolyDegreeSlashActionRightActionProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PolyDegreeSlashActionRightActionProperties
noncomputable section

open Polynomial Matrix
open scoped MatrixGroups

namespace GlobalTheory.HeckeFamilyMatrices.SlPAct

abbrev rowA (g : Matrix (Fin 2) (Fin 2) ℤ) : ℂ[X] := C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)

abbrev rowB (g : Matrix (Fin 2) (Fin 2) ℤ) : ℂ[X] := C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)

theorem polySlash_apply (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w g p = ∑ i ∈ Finset.range (w + 1), p.coeff i • (rowA g ^ i * rowB g ^ (w - i)) := by
  simp [slP, LinearMap.sum_apply, rowA, rowB]

theorem slP_X_pow (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) {i : ℕ} (hi : i ≤ w) :
    slP w g (X ^ i) = rowA g ^ i * rowB g ^ (w - i) := by
  rw [polySlash_apply]
  simp only [coeff_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hi)) h

theorem eq_sum_of_mem {w : ℕ} {p : ℂ[X]} (hp : p ∈ degreeLT ℂ (w + 1)) :
    p = ∑ i ∈ Finset.range (w + 1), C (p.coeff i) * X ^ i := by
  by_cases h0 : p = 0
  · subst h0; simp
  · apply as_sum_range_C_mul_X_pow'
    rw [natDegree_lt_iff_degree_lt h0]
    exact mem_degreeLT.1 hp

theorem mem_of_natDegree_le {w : ℕ} {q : ℂ[X]} (h : q.natDegree ≤ w) : q ∈ degreeLT ℂ (w + 1) := by
  rw [mem_degreeLT]
  exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le h)

theorem natDegree_rows_le (g : Matrix (Fin 2) (Fin 2) ℤ) {i w : ℕ} (hi : i ≤ w) :
    (rowA g ^ i * rowB g ^ (w - i)).natDegree ≤ w := by
  have hA : (rowA g).natDegree ≤ 1 := natDegree_linear_le
  have hB : (rowB g).natDegree ≤ 1 := natDegree_linear_le
  calc (rowA g ^ i * rowB g ^ (w - i)).natDegree
      ≤ (rowA g ^ i).natDegree + (rowB g ^ (w - i)).natDegree := natDegree_mul_le
    _ ≤ i * 1 + (w - i) * 1 := add_le_add (natDegree_pow_le_of_le i hA) (natDegree_pow_le_of_le _ hB)
    _ = w := by omega

theorem polySlash_mem (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) : slP w g p ∈ degreeLT ℂ (w + 1) := by
  rw [polySlash_apply]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (mem_of_natDegree_le ?_)
  exact natDegree_rows_le g (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))

theorem polySlash_one (w : ℕ) {p : ℂ[X]} (hp : p ∈ degreeLT ℂ (w + 1)) : slP w 1 p = p := by
  rw [polySlash_apply]
  conv_rhs => rw [eq_sum_of_mem hp]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [smul_eq_C_mul, rowA, rowB]

theorem polySlash_conj (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    (slP w g p).map (starRingEnd ℂ) = slP w g (p.map (starRingEnd ℂ)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [polySlash_apply, polySlash_apply, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [smul_eq_C_mul, Polynomial.map_mul, Polynomial.map_pow, coeff_map, rowA, rowB]

theorem slP_C_mul_X_pow (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (c : ℂ) {i : ℕ} (hi : i ≤ w) :
    slP w g (C c * X ^ i) = c • (rowA g ^ i * rowB g ^ (w - i)) := by
  rw [← smul_eq_C_mul, map_smul, slP_X_pow w g hi]

theorem polySlash_mul {m n : ℕ} (g : Matrix (Fin 2) (Fin 2) ℤ) {u v : ℂ[X]}
    (hu : u ∈ degreeLT ℂ (m + 1)) (hv : v ∈ degreeLT ℂ (n + 1)) :
    slP (m + n) g (u * v) = slP m g u * slP n g v := by
  have e : u * v = ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
      C (u.coeff i * v.coeff j) * X ^ (i + j) := by
    conv_lhs => rw [eq_sum_of_mem hu, eq_sum_of_mem hv]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [C_mul, pow_add]; ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum, polySlash_apply m g u, polySlash_apply n g v, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hi' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hj' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [slP_C_mul_X_pow _ _ _ (by omega)]
  have : m + n - (i + j) = (m - i) + (n - j) := by omega
  rw [this, smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul, C_mul, pow_add, pow_add]
  ring

theorem pow_mem {a : ℕ} {u : ℂ[X]} (hu : u ∈ degreeLT ℂ 2) : u ^ a ∈ degreeLT ℂ (a + 1) := by
  apply mem_of_natDegree_le
  have h1 : u.natDegree ≤ 1 := by
    by_cases h0 : u = 0
    · simp [h0]
    · have := (natDegree_lt_iff_degree_lt h0).2 (mem_degreeLT.1 hu); omega
  calc (u ^ a).natDegree ≤ a * 1 := natDegree_pow_le_of_le a h1
    _ = a := by omega

theorem polySlash_pow (g : Matrix (Fin 2) (Fin 2) ℤ) {u : ℂ[X]} (hu : u ∈ degreeLT ℂ 2) (a : ℕ) :
    slP a g (u ^ a) = slP 1 g u ^ a := by
  induction a with
  | zero =>
    have := slP_X_pow 0 g (i := 0) le_rfl
    simpa using this
  | succ a ih =>
    rw [pow_succ, polySlash_mul g (pow_mem hu) hu, ih, pow_succ]

theorem rowA_mem (g : Matrix (Fin 2) (Fin 2) ℤ) : rowA g ∈ degreeLT ℂ 2 := mem_of_natDegree_le natDegree_linear_le
theorem rowB_mem (g : Matrix (Fin 2) (Fin 2) ℤ) : rowB g ∈ degreeLT ℂ 2 := mem_of_natDegree_le natDegree_linear_le

theorem polySlash_one_linear (h : Matrix (Fin 2) (Fin 2) ℤ) (x y : ℂ) :
    slP 1 h (C x * X + C y) = C x * rowA h + C y * rowB h := by
  have e1 := slP_X_pow 1 h (i := 1) le_rfl
  have e0 := slP_X_pow 1 h (i := 0) (by omega)
  simp only [pow_one, pow_zero, one_mul, mul_one, Nat.sub_self, Nat.sub_zero] at e1 e0
  have e0' : slP 1 h (C y) = C y * rowB h := by
    calc slP 1 h (C y) = slP 1 h (y • (1 : ℂ[X])) := by rw [smul_eq_C_mul, mul_one]
      _ = y • rowB h := by rw [map_smul, e0]
      _ = C y * rowB h := smul_eq_C_mul _
  rw [map_add (f := _), e0', ← smul_eq_C_mul, map_smul, e1, smul_eq_C_mul]

theorem polySlash_one_rowA (g h : Matrix (Fin 2) (Fin 2) ℤ) : slP 1 h (rowA g) = rowA (g * h) := by
  rw [rowA, polySlash_one_linear]
  simp only [rowA, rowB, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  simp only [C_add, C_mul]
  ring

theorem polySlash_one_rowB (g h : Matrix (Fin 2) (Fin 2) ℤ) : slP 1 h (rowB g) = rowB (g * h) := by
  rw [rowB, polySlash_one_linear]
  simp only [rowA, rowB, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  simp only [C_add, C_mul]
  ring

theorem polySlash_rowA_pow_mul_rowB_pow (g h : Matrix (Fin 2) (Fin 2) ℤ) (a b : ℕ) :
    slP (a + b) h (rowA g ^ a * rowB g ^ b) = rowA (g * h) ^ a * rowB (g * h) ^ b := by
  rw [polySlash_mul h (pow_mem (rowA_mem g)) (pow_mem (rowB_mem g)), polySlash_pow h (rowA_mem g),
    polySlash_pow h (rowB_mem g), polySlash_one_rowA, polySlash_one_rowB]

theorem polySlash_polySlash (w : ℕ) (g h : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w (g * h) p = slP w h (slP w g p) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [polySlash_apply w g p, map_sum, polySlash_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [map_smul]
  congr 1
  have := polySlash_rowA_pow_mul_rowB_pow g h i (w - i)
  rw [Nat.add_sub_cancel' hi'] at this
  exact this.symm

theorem polySlash_act : ∀ (w : ℕ) (g h : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]), p ∈ degreeLT ℂ (w + 1) →
    slP w g p ∈ degreeLT ℂ (w + 1) ∧ slP w (g * h) p = slP w h (slP w g p) ∧ slP w 1 p = p ∧
      (slP w g p).map (starRingEnd ℂ) = slP w g (p.map (starRingEnd ℂ)) :=
  fun w g h p hp => ⟨polySlash_mem w g p, polySlash_polySlash w g h p, polySlash_one w hp, polySlash_conj w g p⟩

end GlobalTheory.HeckeFamilyMatrices.SlPAct
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PolyDegreeSlashActionRightActionPropertiesStatement
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyDegreeSlashAction_right_action_properties : ∀ (w : ℕ) (g h : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]), p ∈ degreeLT ℂ (w + 1) → slP w g p ∈ degreeLT ℂ (w + 1) ∧ slP w (g * h) p = slP w h (slP w g p) ∧ slP w 1 p = p ∧ (slP w g p).map (starRingEnd ℂ) = slP w g (p.map (starRingEnd ℂ)) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.SlPAct.polySlash_act | exact GlobalTheory.HeckeFamilyMatrices.SlPAct.polySlash_act | (intros; apply GlobalTheory.HeckeFamilyMatrices.SlPAct.polySlash_act <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableHeckeOperatorsExplicit
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableHeckeOperatorsExplicit
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

private theorem im_mul_pos' {q : ℕ} (hq : 0 < q) {z : ℂ} (hz : 0 < z.im) : 0 < ((q : ℂ) * z).im := by
  have : (0 : ℝ) < q := by exact_mod_cast hq
  simpa using mul_pos this hz

private theorem im_div_pos' {q : ℕ} (hq : 0 < q) {z : ℂ} (hz : 0 < z.im) (j : ℕ) :
    0 < ((z + j) / (q : ℂ)).im := by
  have : (0 : ℝ) < q := by exact_mod_cast hq
  rw [Complex.div_natCast_im]
  simpa using div_pos hz this

theorem uOp_mdiff {q : ℕ} (hq : 0 < q) {f : ℍ → ℂ} (hf : MDiff f) : MDiff (uOp q f) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf ⊢
  have h : DifferentiableOn ℂ (fun z : ℂ =>
      (q : ℂ)⁻¹ * ∑ j ∈ Finset.range q, (f ∘ ofComplex) ((z + j) / q)) {z : ℂ | 0 < z.im} := by
    refine DifferentiableOn.const_mul ?_ _
    refine DifferentiableOn.fun_sum fun j _ => ?_
    exact hf.comp (f := fun z : ℂ => (z + j) / (q : ℂ)) (by fun_prop) fun z hz => im_div_pos' hq hz j
  refine h.congr fun z hz => ?_
  simp only [Function.comp, uOp, ofComplex_apply_of_im_pos hz]

theorem vOp_mdiff {q : ℕ} (hq : 0 < q) {f : ℍ → ℂ} (hf : MDiff f) : MDiff (vOp q f) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf ⊢
  have h : DifferentiableOn ℂ (fun z : ℂ => (f ∘ ofComplex) ((q : ℂ) * z)) {z : ℂ | 0 < z.im} :=
    hf.comp (f := fun z : ℂ => (q : ℂ) * z) (by fun_prop) fun z hz => im_mul_pos' hq hz
  refine h.congr fun z hz => ?_
  simp only [Function.comp, vOp, ofComplex_apply_of_im_pos hz]

theorem hecke_mdiff : ∀ (q : ℕ) (k : ℤ) (σ : SL(2, ℤ)) (f : ℍ → ℂ), 0 < q → MDiff f →
    MDiff (GlobalTheory.Hk.uOp q f) ∧ MDiff (GlobalTheory.Hk.vOp q f) ∧ MDiff (GlobalTheory.Hk.heckeT k q σ f) := by
  intro q k σ f hq hf
  refine ⟨uOp_mdiff hq hf, vOp_mdiff hq hf, ?_⟩
  have hs : MDiff (f ∣[k] σ) := by
    rw [ModularForm.SL_slash]
    exact MDifferentiable.slash hf k _
  exact (uOp_mdiff hq hf).add ((vOp_mdiff hq hs).const_smul _)

end GlobalTheory.Hk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableHeckeOperatorsExplicitStatement
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mdifferentiable_heckeOperatorsExplicit : ∀ (q : ℕ) (k : ℤ) (σ : SL(2, ℤ)) (f : ℍ → ℂ), 0 < q → MDiff f → MDiff (GlobalTheory.Hk.uOp q f) ∧ MDiff (GlobalTheory.Hk.vOp q f) ∧ MDiff (GlobalTheory.Hk.heckeT k q σ f) := by
  first | exact @GlobalTheory.Hk.hecke_mdiff | exact GlobalTheory.Hk.hecke_mdiff | (intros; apply GlobalTheory.Hk.hecke_mdiff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertFixesRootOfUnitRatio
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertFixesRootOfUnitRatio
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem inert_fixes_root_of_unit_ratio (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (B : ValuationSubring Ω)
    (g : Ω ≃ₐ[K] Ω) (N : ℕ) (c θ : Ω) :
    0 < N → B.valuation (N : Ω) = 1 → Inert B g → g c = c → c ≠ 0 → g (θ ^ N) = θ ^ N →
      B.valuation (θ ^ N / c ^ N) = 1 → g θ = θ := by
  intro hN hvN hin hgc hc hgθ hvθ
  set v := B.valuation
  by_cases hθ : θ = 0
  · simp [hθ]
  set u := θ / c with hu
  have hu0 : u ≠ 0 := div_ne_zero hθ hc
  have hvu : v u = 1 := by
    have h1 : v u ^ N = 1 := by rw [← map_pow, hu, div_pow]; exact hvθ
    exact (pow_eq_one_iff_left (Nat.pos_iff_ne_zero.mp hN)).mp h1
  have hgu : g u = g θ / c := by rw [hu, map_div₀, hgc]
  have hguN : (g u) ^ N = u ^ N := by
    rw [← map_pow, hu, div_pow, map_div₀, map_pow g c, hgc, hgθ]
  set ξ := g u / u with hξ
  have hξN : ξ ^ N = 1 := by rw [hξ, div_pow, hguN, div_self (pow_ne_zero _ hu0)]
  have hvξ1 : v (ξ - 1) < 1 := by
    have h2 : ξ - 1 = (g u - u) / u := by rw [hξ, sub_div, div_self hu0]
    rw [h2, map_div₀, hvu, div_one]
    exact hin u hvu.le
  have hvξ : v ξ ≤ 1 := by
    have : ξ = (ξ - 1) + 1 := by ring
    rw [this]
    exact (Valuation.map_add v _ _).trans (max_le hvξ1.le (by simp))
  have hpow : ∀ j : ℕ, v (ξ ^ j - 1) < 1 := by
    intro j
    have h3 : ξ ^ j - 1 = (∑ i ∈ Finset.range j, ξ ^ i) * (ξ - 1) := (geom_sum_mul ξ j).symm
    rw [h3, map_mul]
    have h4 : v (∑ i ∈ Finset.range j, ξ ^ i) ≤ 1 :=
      Valuation.map_sum_le v (fun i _ => by rw [map_pow]; exact pow_le_one' hvξ i)
    calc v (∑ i ∈ Finset.range j, ξ ^ i) * v (ξ - 1) ≤ 1 * v (ξ - 1) := mul_le_mul_left h4 _
      _ = v (ξ - 1) := one_mul _
      _ < 1 := hvξ1
  set S := ∑ i ∈ Finset.range N, ξ ^ i with hS
  have hSN : S - (N : Ω) = ∑ i ∈ Finset.range N, (ξ ^ i - 1) := by
    rw [hS, Finset.sum_sub_distrib]; simp
  have hvSN : v (S - (N : Ω)) < 1 := by
    rw [hSN]; exact Valuation.map_sum_lt v one_ne_zero (fun i _ => hpow i)
  have hS0 : S ≠ 0 := by
    intro h0
    rw [h0, zero_sub, Valuation.map_neg, hvN] at hvSN
    exact lt_irrefl _ hvSN
  have hmul : S * (ξ - 1) = 0 := by rw [hS, geom_sum_mul, hξN, sub_self]
  have hξ1 : ξ = 1 := by
    rcases mul_eq_zero.mp hmul with h | h
    · exact absurd h hS0
    · exact sub_eq_zero.mp h
  have : g u = u := by
    rw [hξ, div_eq_one_iff_eq hu0] at hξ1; exact hξ1
  rw [hgu, hu] at this
  exact (div_left_inj' hc).mp this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertFixesRootOfUnitRatioStatement
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_apply_eq_of_pow_fixed_of_valuation_one : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (B : ValuationSubring Ω) (g : Ω ≃ₐ[K] Ω) (N : ℕ) (c θ : Ω),
  0 < N → B.valuation (N : Ω) = 1 → Inert B g → g c = c → c ≠ 0 → g (θ ^ N) = θ ^ N → B.valuation (θ ^ N / c ^ N) = 1 → g θ = θ := by
  first | exact @GlobalTheory.inert_fixes_root_of_unit_ratio | exact GlobalTheory.inert_fixes_root_of_unit_ratio | (intros; apply GlobalTheory.inert_fixes_root_of_unit_ratio <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedIntegersAdicComplete
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedIntegersAdicComplete
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5

theorem o0_isAdicComplete_span_p : ∀ (p : ℕ) [Fact p.Prime], IsAdicComplete (Ideal.span {(p : O0 p)}) (O0 p) := by
  intro p _
  have hfg : (pI p).FG := ⟨{(p : Lau p)}, by simp⟩
  have h : IsAdicComplete (pI p) (O0 p) := AdicCompletion.isAdicComplete hfg
  have hmap : (pI p).map (algebraMap (Lau p) (O0 p)) = Ideal.span {(p : O0 p)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [← hmap]
  exact { toIsHausdorff := IsHausdorff.map_algebraMap_iff.2 h.toIsHausdorff
          toIsPrecomplete := IsPrecomplete.map_algebraMap_iff.2 h.toIsPrecomplete }

end GlobalTheory.K5
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedIntegersAdicCompleteStatement
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_integers_adic_complete : ∀ (p : ℕ) [Fact p.Prime], IsAdicComplete (Ideal.span {(p : O0 p)}) (O0 p) := by
  first | exact @GlobalTheory.K5.o0_isAdicComplete_span_p | exact GlobalTheory.K5.o0_isAdicComplete_span_p | (intros; apply GlobalTheory.K5.o0_isAdicComplete_span_p <;> assumption)
end
end
