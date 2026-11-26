module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open GlobalTheory.UnitLemma Polynomial Filter Topology Classical

variable {K : UQ} (B : InvAlg K) {ι : Type}

abbrev al (K : UQ) (a : K.O) : K.E := algebraMap K.O K.E a

def InDual (s : B.A) (M : Submodule K.O B.A) : Prop :=
  ∀ z ∈ M, Algebra.trace K.E B.A (s * z) ∈ (algebraMap K.O K.E).range

def indM (M : Submodule K.O B.A) (y : B.A) : ℚ := if y ∈ M then 1 else 0

def indD (M : Submodule K.O B.A) (s : B.A) : ℚ := if InDual B s M then 1 else 0

def dlt {A : Type} [CommMonoid A] (π : ι → A) (I : Finset ι) (f : A → ℚ) (y : A) : ℚ :=
  ∑ J ∈ I.powerset, (-1 : ℚ) ^ J.card * f ((∏ j ∈ J, π j) * y)

def term (π : ι → B.A) (I I' : Finset ι) (u s : B.A) (M : Submodule K.O B.A) : ℚ :=
  dlt π I (indM B M) u * dlt π I' (indD B M) s

def HH (π : ι → B.A) (I I' : Finset ι) (u s : B.A) : ℚ :=
  ∑ᶠ M ∈ B.Lin, B.sgnLat M * term B π I I' u s M

def eS (e : ι → B.A) (I : Finset ι) : B.A := ∑ i ∈ I, e i

def Pos (a : K.O) (e : ι → B.A) (N : ℕ) (M : Submodule K.O B.A) (p : ι → ℤ) : Prop :=
  ∀ i, (∀ r : B.A, IsIntegral K.O r → (al K a ^ (p i + N)) • (e i * r) ∈ M) ∧
    ∀ m ∈ M, IsIntegral K.O ((al K a ^ (-p i)) • (e i * m))

def chi (e : ι → B.A) (I : Finset ι) (y : B.A) : ℚ :=
  K.eta (Algebra.norm K.E (y * eS B e I + (1 - eS B e I)))

def IsPre [Fintype ι] (e : ι → B.A) (S : Finset ι) : Prop :=
  CompleteOrthogonalIdempotents e ∧ ∀ i, ∃ f : B.A, IsIdempotentElem f ∧ f ≠ 0 ∧
    (∀ y, f * y ≠ 0 → ∃ z, f * y * z = f) ∧
    (i ∈ S → e i = f ∧ B.σ f = f) ∧ (i ∉ S → f * B.σ f = 0 ∧ e i = f + B.σ f)

def IsFrame [Fintype ι] (e π : ι → B.A) (S : Finset ι) : Prop :=
  IsPre B e S ∧ ∀ i ∈ S, B.Plus (π i) ∧ π i * (1 - e i) = 1 - e i ∧ K.eta (Algebra.norm K.E (π i)) = -1

def Win (I I' : Finset ι) (L k : ℕ) (p : ι → ℤ) : Prop :=
  ∀ i, -(L : ℤ) ≤ p i ∧ p i ≤ 2 * k + L ∧ (i ∈ I → 2 * (k : ℤ) - L ≤ p i) ∧ (i ∈ I' → p i ≤ L)

def Mid (S : Finset ι) (L k : ℕ) (p : ι → ℤ) : Prop :=
  ∀ i ∉ S, (L : ℤ) ≤ p i ∧ p i ≤ 2 * k - L

theorem eta_mul {x y : K.E} (hx : x ≠ 0) (hy : y ≠ 0) : K.eta (x * y) = K.eta x * K.eta y := by
  unfold UQ.eta val
  rw [map_mul, WithZero.log_mul (by simpa using hx) (by simpa using hy), neg_add, zpow_add₀ (by norm_num)]

theorem eta_sq (x : K.E) : K.eta x * K.eta x = 1 := by
  unfold UQ.eta
  rw [← mul_zpow]; simp

theorem abs_eta (x : K.E) : |K.eta x| = 1 := by
  unfold UQ.eta; simp

theorem abs_indM (M : Submodule K.O B.A) (y : B.A) : |indM B M y| ≤ 1 := by
  unfold indM; split_ifs <;> simp

theorem abs_indD (M : Submodule K.O B.A) (y : B.A) : |indD B M y| ≤ 1 := by
  unfold indD; split_ifs <;> simp

theorem abs_dlt {A : Type} [CommMonoid A] (π : ι → A) (I : Finset ι) (f : A → ℚ) (hf : ∀ y, |f y| ≤ 1) (y : A) :
    |dlt π I f y| ≤ 2 ^ I.card := by
  unfold dlt
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ J ∈ I.powerset, |(-1 : ℚ) ^ J.card * f ((∏ j ∈ J, π j) * y)| ≤ ∑ J ∈ I.powerset, (1 : ℚ) :=
        Finset.sum_le_sum fun J _ => by rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]; exact hf _
    _ = 2 ^ I.card := by simp [Finset.card_powerset]

theorem abs_term (π : ι → B.A) (I I' : Finset ι) (u s : B.A) (M : Submodule K.O B.A) :
    |term B π I I' u s M| ≤ 2 ^ I.card * 2 ^ I'.card := by
  unfold term
  rw [abs_mul]
  exact mul_le_mul (abs_dlt _ _ _ (abs_indM B M) _) (abs_dlt _ _ _ (abs_indD B M) _) (abs_nonneg _) (by positivity)

theorem dlt_eq_zero {A : Type} [CommMonoid A] (π : ι → A) (I : Finset ι) (f : A → ℚ) (y : A) (i : ι) (hi : i ∈ I)
    (h : ∀ J ⊆ I.erase i, f (π i * ((∏ j ∈ J, π j) * y)) = f ((∏ j ∈ J, π j) * y)) : dlt π I f y = 0 := by
  unfold dlt
  rw [← Finset.insert_erase hi, Finset.sum_powerset_insert (Finset.notMem_erase i I)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun J hJ => ?_
  have hJ' : i ∉ J := fun h => Finset.notMem_erase i I (Finset.mem_powerset.1 hJ h)
  rw [Finset.prod_insert hJ', Finset.card_insert_of_notMem hJ', mul_assoc, h J (Finset.mem_powerset.1 hJ)]
  ring

end GlobalTheory.UnitLemma.Desc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStableGauss
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def Hyp (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ) : Prop :=
  IsField A.K ∧ IsField A.L ∧ IsStdChar ψ ∧ SelfDual μ (A.kerL ψ x) ∧
    ∀ s : A.Kˣ, ((∃ y, A.NL y = s) → ω s = 1) ∧ ((¬ ∃ y, A.NL y = s) → ω s = -1)

def nOp (A : Et F E) (ψ : AddChar F ℂ) (x z : A.K) (φ : A.L → ℂ) : A.L → ℂ :=
  fun y => A.psiK ψ (z * x * A.NL y) * φ y

def mOp (A : Et F E) (ω : A.K → ℂ) (s : A.Kˣ) (φ : A.L → ℂ) : A.L → ℂ :=
  fun y => ω s * (A.absK s : ℂ) * φ ((s : A.K) • y)

def fOp (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L) (φ : A.L → ℂ) : A.L → ℂ :=
  fourB μ (A.kerL ψ x) φ

def gaussInt (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L) (u : A.K) (S : Set A.L) : ℂ :=
  ∫ y in S, A.psiK ψ (u * x * A.NL y) ∂μ

def IsStableGauss (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L) (u : A.K) (G : ℂ) : Prop :=
  ∃ Λ₀ : AddSubgroup A.L, IsOpen (Λ₀ : Set A.L) ∧ IsCompact (Λ₀ : Set A.L) ∧
    ∀ Λ : AddSubgroup A.L, IsOpen (Λ : Set A.L) → IsCompact (Λ : Set A.L) → Λ₀ ≤ Λ →
      gaussInt A ψ x μ u Λ = G

end GlobalTheory.JR.WeilQuad
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerBasisOfCharpolySeparable
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerBasisOfCharpolySeparable
open GlobalTheory.UnitLemma Matrix MeasureTheory

namespace GlobalTheory.UnitLemma

open Polynomial

theorem _root_.GlobalTheory.UnitLemma.charpoly_dvd_minpoly_of_separable {E V : Type} [Field E] [AddCommGroup V] [Module E V]
    [Module.Finite E V] (f : Module.End E V) (h : (LinearMap.charpoly f).Separable) :
    LinearMap.charpoly f ∣ minpoly E f := by
  set L := AlgebraicClosure E
  have hinj : Function.Injective (algebraMap E L) := (algebraMap E L).injective
  rw [← map_dvd_map (algebraMap E L) hinj (LinearMap.charpoly_monic f)]
  have hm0 : (minpoly E f).map (algebraMap E L) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero (Algebra.IsIntegral.isIntegral f))
  have hroot : ∀ r ∈ ((LinearMap.charpoly f).map (algebraMap E L)).roots,
      r ∈ ((minpoly E f).map (algebraMap E L)).roots := by
    intro r hr
    rw [mem_roots hm0]
    rw [mem_roots (Polynomial.map_ne_zero (LinearMap.charpoly_monic f).ne_zero),
      ← LinearMap.charpoly_baseChange, ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hr
    obtain ⟨v, hv⟩ := hr.exists_hasEigenvector
    have hzero : aeval (f.baseChange L) ((minpoly E f).map (algebraMap E L)) = 0 := by
      rw [aeval_map_algebraMap]
      have hφ := Polynomial.aeval_algHom_apply (Module.End.baseChangeHom E L V) f (minpoly E f)
      rw [minpoly.aeval, map_zero] at hφ
      exact hφ
    have hv' :=
      Module.End.aeval_apply_of_hasEigenvector (p := (minpoly E f).map (algebraMap E L)) hv
    rw [hzero, LinearMap.zero_apply, eq_comm, smul_eq_zero] at hv'
    exact hv'.resolve_right hv.2
  have hsplit := IsAlgClosed.splits ((LinearMap.charpoly f).map (algebraMap E L))
  rw [hsplit.eq_prod_roots_of_monic ((LinearMap.charpoly_monic f).map _),
    Multiset.prod_X_sub_C_dvd_iff_le_roots hm0, Multiset.le_iff_subset (nodup_roots h.map)]
  exact hroot

theorem _root_.GlobalTheory.UnitLemma.exists_basis_pow_of_separable : ∀ (K : _root_.GlobalTheory.UnitLemma.UQ)
    (B : _root_.GlobalTheory.UnitLemma.InvAlg K), B.P.Separable →
    ∃ e : Module.Basis (Fin (Module.finrank K.E B.A)) K.E
      B.A, ∀ i, e i = B.g ^ (i : ℕ) := by
  intro K B hsep
  set g := B.g
  have hmin : minpoly K.E (LinearMap.mulLeft K.E g) = minpoly K.E g :=
    minpoly.algHom_eq (Algebra.lmul K.E B.A)
      (fun x y hxy => by simpa using congrArg (fun φ => φ 1) hxy) g
  have hdvd := _root_.GlobalTheory.UnitLemma.charpoly_dvd_minpoly_of_separable _ hsep
  rw [hmin] at hdvd
  have hdeg : (minpoly K.E g).natDegree =
      Module.finrank K.E B.A := by
    apply le_antisymm (minpoly.natDegree_le g)
    rw [← LinearMap.charpoly_natDegree (LinearMap.mulLeft K.E g)]
    exact natDegree_le_of_dvd hdvd (minpoly.ne_zero (Algebra.IsIntegral.isIntegral g))
  have hli : LinearIndependent K.E
      (fun i : Fin (Module.finrank K.E B.A) => g ^ (i : ℕ)) :=
    (linearIndependent_pow g).comp (Fin.cast hdeg.symm) (Fin.cast_injective _)
  exact ⟨basisOfLinearIndependentOfCardEqFinrank' _ hli (Fintype.card_fin _),
    fun i => by rw [coe_basisOfLinearIndependentOfCardEqFinrank']⟩

end GlobalTheory.UnitLemma
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerBasisOfCharpolySeparableStatement
open GlobalTheory.UnitLemma Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_power_basis_of_charpoly_separable : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∃ e : Module.Basis (Fin (Module.finrank K.E B.A)) K.E B.A, ∀ i, e i = B.g ^ (i : ℕ) := by
  first | exact @GlobalTheory.UnitLemma.exists_basis_pow_of_separable | exact GlobalTheory.UnitLemma.exists_basis_pow_of_separable | (intros; apply GlobalTheory.UnitLemma.exists_basis_pow_of_separable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticStarStructure
open GlobalTheory.JR MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem Unram.exists_basis_antifixed (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [h : Unram F E] :
    ∃ (b : Module.Basis (Fin 2) F E) (d : F), b 0 = 1 ∧ star (b 1) = - b 1 ∧ b 1 * b 1 = algebraMap F E d ∧ d ≠ 0 := by
  have : CharZero F := h.charZero
  have hsmul : ∀ (c : F) (z : E), star (c • z) = c • star z := by
    intro c z
    rw [Algebra.smul_def, Algebra.smul_def, star_mul, h.star_fix, mul_comm]
  obtain ⟨y, hy⟩ := h.star_ne
  set u : E := y - star y with hu
  have hsu : star u = -u := by rw [hu, star_sub, star_star, neg_sub]
  have hu0 : u ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  have key : ∀ s t : F, star (s • (1 : E) + t • u) = s • 1 + t • u → t = 0 := by
    intro s t hst
    rw [star_add, hsmul, hsmul, star_one, hsu, smul_neg, add_right_inj] at hst
    have h2 : (2 : F) • (t • u) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← hst]
      exact neg_add_cancel _
    rcases smul_eq_zero.mp h2 with h2 | h2
    · exact absurd h2 two_ne_zero
    · exact (smul_eq_zero.mp h2).resolve_right hu0
  have hli : LinearIndependent F ![(1 : E), u] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := key s t (by rw [hst, star_zero])
    refine ⟨?_, ht⟩
    rw [ht, zero_smul, add_zero] at hst
    exact (smul_eq_zero.mp hst).resolve_right one_ne_zero
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by rw [Fintype.card_fin, h.finrank_eq]
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = u := by simp [b]
  have hsum := b.sum_repr (u * u)
  rw [Fin.sum_univ_two, hb0, hb1] at hsum
  have hfix : star (b.repr (u * u) 0 • (1 : E) + b.repr (u * u) 1 • u) =
      b.repr (u * u) 0 • 1 + b.repr (u * u) 1 • u := by
    rw [hsum, star_mul, hsu, neg_mul_neg]
  have h1 := key _ _ hfix
  rw [h1, zero_smul, add_zero] at hsum
  refine ⟨b, b.repr (u * u) 0, hb0, by rw [hb1, hsu], ?_, ?_⟩
  · rw [hb1, Algebra.algebraMap_eq_smul_one]
    exact hsum.symm
  · intro hd
    rw [hd, zero_smul] at hsum
    exact mul_self_ne_zero.mpr hu0 hsum.symm

theorem quadratic_star_structure {K L : Type} [CommRing K] [CommRing L] [StarRing L] [Algebra K L]
    (b : Module.Basis (Fin 2) K L) (d : K) (hb0 : b 0 = 1) (hs : star (b 1) = - b 1)
    (hd : b 1 * b 1 = algebraMap K L d) (hK : ∀ x : K, star (algebraMap K L x) = algebraMap K L x)
    (hdu : IsUnit d) (h2 : IsUnit (2 : K)) :
    Function.Injective (algebraMap K L) ∧ (∀ y : L, algebraMap K L (Algebra.norm K y) = y * star y) ∧
      (∀ y : L, algebraMap K L (Algebra.trace K L y) = y + star y) ∧
      (∀ y' : L, (∀ y : L, Algebra.trace K L (star y' * y) = 0) → y' = 0) := by
  have hrep0 : ∀ a c : K, b.repr (a • b 0 + c • b 1) 0 = a := by
    intro a c; simp
  have hrep1 : ∀ a c : K, b.repr (a • b 0 + c • b 1) 1 = c := by
    intro a c; simp
  have hexp : ∀ y : L, y = b.repr y 0 • b 0 + b.repr y 1 • b 1 := by
    intro y
    conv_lhs => rw [← b.sum_repr y]
    rw [Fin.sum_univ_two]
  have hsmul : ∀ (c : K) (z : L), star (c • z) = c • star z := by
    intro c z
    rw [Algebra.smul_def, Algebra.smul_def, star_mul, hK, mul_comm]
  have hstar : ∀ y : L, star y = b.repr y 0 • b 0 + (-b.repr y 1) • b 1 := by
    intro y
    conv_lhs => rw [hexp y]
    rw [star_add, hsmul, hsmul, hb0, star_one, hs, smul_neg, neg_smul]
  have hmul : ∀ z : L, z * b 1 = (b.repr z 1 * d) • b 0 + b.repr z 0 • b 1 := by
    intro z
    conv_lhs => rw [hexp z]
    simp only [Algebra.smul_def, hb0, mul_one, map_mul, add_mul]
    linear_combination (algebraMap K L (b.repr z 1)) * hd
  have hc0 : ∀ z : L, b.repr (z * b 0) = b.repr z := by
    intro z; rw [hb0, mul_one]
  have htr : ∀ z : L, Algebra.trace K L z = b.repr z 0 + b.repr z 0 := by
    intro z
    rw [Algebra.trace_eq_matrix_trace b, Matrix.trace_fin_two, Algebra.leftMulMatrix_eq_repr_mul,
      Algebra.leftMulMatrix_eq_repr_mul, hc0, hmul, hrep1]
  have hmap : ∀ x : K, algebraMap K L x = x • b 0 := by
    intro x; rw [hb0, Algebra.algebraMap_eq_smul_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hmap] at hx
    have := hrep0 x 0
    rw [zero_smul, add_zero, hx] at this
    simp at this
    exact this.symm
  · intro y
    rw [Algebra.norm_eq_matrix_det b, Matrix.det_fin_two]
    simp only [Algebra.leftMulMatrix_eq_repr_mul, hc0, hmul, hrep0, hrep1]
    calc _ = (b.repr y 0 • b 0 + b.repr y 1 • b 1) * (b.repr y 0 • b 0 + (-b.repr y 1) • b 1) := by
          simp only [Algebra.smul_def, hb0, mul_one, map_mul, map_sub, map_neg]
          linear_combination (algebraMap K L (b.repr y 1) * algebraMap K L (b.repr y 1)) * hd
      _ = y * star y := by rw [← hexp y, ← hstar y]
  · intro y
    rw [htr, hmap]
    calc _ = (b.repr y 0 • b 0 + b.repr y 1 • b 1) + (b.repr y 0 • b 0 + (-b.repr y 1) • b 1) := by
          simp only [add_smul, neg_smul]; abel
      _ = y + star y := by rw [← hexp y, ← hstar y]
  · intro y' hy'
    have g1 := hy' 1
    have g2 := hy' (b 1)
    rw [mul_one, htr, hstar, hrep0] at g1
    rw [hmul, htr, hrep0, hstar, hrep1] at g2
    have hp : b.repr y' 0 = 0 := by
      have h3 : (2 : K) * b.repr y' 0 = 0 := by rw [two_mul]; exact g1
      exact h2.mul_right_eq_zero.mp h3
    have hq : b.repr y' 1 = 0 := by
      have h3 : (2 : K) * (b.repr y' 1 * d) = 0 := by linear_combination -g2
      exact hdu.mul_left_eq_zero.mp (h2.mul_right_eq_zero.mp h3)
    rw [hexp y', hp, hq, zero_smul, zero_smul, add_zero]

theorem Et.quadratic_structure : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), Nonempty (Module.Basis (Fin 2) A.K A.L) ∧ Function.Injective (algebraMap A.K A.L) ∧ (∀ y : A.L, algebraMap A.K A.L (A.NL y) = y * star y) ∧ (∀ y : A.L, algebraMap A.K A.L (Algebra.trace A.K A.L y) = y + star y) ∧ (∀ y' : A.L, (∀ y : A.L, Algebra.trace A.K A.L (star y' * y) = 0) → y' = 0) := by
  intro F E _ _ _ _ hU A
  have : CharZero F := hU.charZero
  obtain ⟨b, d, hb0, hs, hd, hd0⟩ := Unram.exists_basis_antifixed F E
  let B : Module.Basis (Fin 2) A.K A.L := A.push.symm.out.basis b
  have hB : ∀ i, B i = algebraMap E A.L (b i) := fun i => by
    simp [B, IsBaseChange.basis_apply]
  have key := quadratic_star_structure B (algebraMap F A.K d) (by rw [hB, hb0, map_one])
    (by rw [hB, A.star_E, hs, map_neg])
    (by
      rw [hB, ← map_mul, hd, ← IsScalarTower.algebraMap_apply F E A.L,
        ← IsScalarTower.algebraMap_apply F A.K A.L])
    A.star_K ((isUnit_iff_ne_zero.mpr hd0).map _)
    (by
      have h2F := (isUnit_iff_ne_zero.mpr (two_ne_zero : (2 : F) ≠ 0)).map (algebraMap F A.K)
      rwa [map_ofNat] at h2F)
  exact ⟨⟨B⟩, key.1, key.2.1, key.2.2.1, key.2.2.2⟩

end GlobalTheory.JR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DistribHaarCharTransport
open GlobalTheory.JR MeasureTheory Filter Topology
open scoped Pointwise

namespace GlobalTheory.JR.ModuleNorm

theorem distribHaarChar_transport {G H A B : Type} [Group G] [Group H]
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
    [T2Space A] [SecondCountableTopology A] [DistribMulAction G A] [ContinuousConstSMul G A]
    [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] [LocallyCompactSpace B]
    [T2Space B] [SecondCountableTopology B] [DistribMulAction H B] [ContinuousConstSMul H B]
    (e : A ≃ₜ+ B) (g : G) (h : H) (he : ∀ x, e (g • x) = h • e x) :
    distribHaarChar B h = distribHaarChar A g := by
  borelize A B
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : A)
  have h0 : (Measure.addHaar : Measure A) K ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hK0).ne'
  have hT : (Measure.addHaar : Measure A) K ≠ ⊤ := hK.measure_lt_top.ne
  have hmap : ∀ s : Set B, ((Measure.addHaar : Measure A).map e) s = (Measure.addHaar : Measure A) (e ⁻¹' s) :=
    fun s => e.toHomeomorph.toMeasurableEquiv.map_apply s
  have key : ∀ x, h⁻¹ • e x = e (g⁻¹ • x) := fun x => by
    rw [inv_smul_eq_iff, ← he, smul_inv_smul]
  have hpre : e ⁻¹' (e.symm ⁻¹' K) = K := by
    ext x; simp
  have hpre2 : e ⁻¹' (h • e.symm ⁻¹' K) = g • K := by
    ext x
    simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, key]
    simp
  have h0' : ((Measure.addHaar : Measure A).map e) (e.symm ⁻¹' K) ≠ 0 := by rw [hmap, hpre]; exact h0
  have hT' : ((Measure.addHaar : Measure A).map e) (e.symm ⁻¹' K) ≠ ⊤ := by rw [hmap, hpre]; exact hT
  apply ENNReal.coe_injective
  rw [distribHaarChar_eq_div h0' hT', distribHaarChar_eq_div h0 hT, hmap, hmap, hpre, hpre2]

theorem distribHaarChar_pi_two {G A : Type} [Group G]
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A]
    [T2Space A] [SecondCountableTopology A] [DistribMulAction G A] [ContinuousConstSMul G A]
    (g : G) : distribHaarChar (Fin 2 → A) g = distribHaarChar A g ^ 2 := by
  borelize A
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : A)
  have h0 : (Measure.addHaar : Measure A) K ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hK0).ne'
  have hT : (Measure.addHaar : Measure A) K ≠ ⊤ := hK.measure_lt_top.ne
  have hg : (Measure.addHaar : Measure A) (g • K) = distribHaarChar A g * Measure.addHaar K := by
    rw [distribHaarChar_eq_div h0 hT, ENNReal.div_mul_cancel h0 hT]
  apply distribHaarChar_eq_of_measure_smul_eq_mul
    (μ := Measure.pi fun _ : Fin 2 => (Measure.addHaar : Measure A)) (s := Set.univ.pi fun _ => K)
  · rw [Measure.pi_pi]; simp [h0]
  · rw [Measure.pi_pi]; simp [hT]
  · rw [Set.smul_set_univ_pi, Measure.pi_pi, Measure.pi_pi]
    simp only [Pi.smul_apply, Fin.prod_univ_two, hg]
    push_cast
    ring

theorem distribHaarChar_eq_norm (K L : Type) [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] [T2Space K] [LocallyCompactSpace K] [SecondCountableTopology K]
    [CommRing L] [TopologicalSpace L] [IsTopologicalRing L] [T2Space L] [LocallyCompactSpace L]
    [SecondCountableTopology L] [StarRing L] [ContinuousStar L] [Algebra K L]
    (e : (Fin 2 → K) ≃ₗ[K] L) (he : Continuous e) (hes : Continuous e.symm) (y : Lˣ) (k : Kˣ)
    (h : algebraMap K L k = y * star (y : L)) :
    distribHaarChar L y = distribHaarChar K k := by
  let eC : (Fin 2 → K) ≃ₜ+ L :=
    { e.toAddEquiv with continuous_toFun := he, continuous_invFun := hes }
  let kL : Lˣ := Units.map (algebraMap K L).toMonoidHom k
  have h1 : distribHaarChar L kL = distribHaarChar (Fin 2 → K) k :=
    distribHaarChar_transport eC k kL (fun x => by
      show e (k • x) = kL • e x
      simp only [Units.smul_def]
      rw [map_smul, Algebra.smul_def, smul_eq_mul]
      rfl)
  have h2 := distribHaarChar_pi_two (A := K) k
  let yS : Lˣ := Units.map (starRingEnd L).toMonoidHom y
  let sC : L ≃ₜ+ L :=
    { starAddEquiv with continuous_toFun := continuous_star, continuous_invFun := continuous_star }
  have h3 : distribHaarChar L yS = distribHaarChar L y :=
    distribHaarChar_transport sC y yS (fun x => by
      show star (y • x) = yS • star x
      rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, star_mul']
      rfl)
  have h4 : kL = y * yS := Units.ext (by simp [kL, yS, h, starRingEnd_apply])
  have hsq : distribHaarChar L y ^ 2 = distribHaarChar K k ^ 2 := by
    rw [← h2, ← h1, h4, map_mul, h3, sq]
  exact (pow_left_inj₀ zero_le zero_le two_ne_zero).mp hsq

end GlobalTheory.JR.ModuleNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedCentralizerIsNormOneTorus
open GlobalTheory.Tw Matrix Polynomial

noncomputable section

namespace GlobalTheory.Tw.CentralizerAdjoin

section Dual
variable {n : ℕ} {R : Type} [CommRing R]

def dm (U V : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) (DualNumber R) :=
  Matrix.of fun i j => TrivSqZeroExt.inl (U i j) + TrivSqZeroExt.inr (V i j)

theorem dm_fst (U V : Matrix (Fin n) (Fin n) R) : (dm U V).map TrivSqZeroExt.fst = U := by
  ext i j; simp [dm]

theorem dm_snd (U V : Matrix (Fin n) (Fin n) R) : (dm U V).map TrivSqZeroExt.snd = V := by
  ext i j; simp [dm]

theorem dm_one : dm (1 : Matrix (Fin n) (Fin n) R) 0 = 1 := by
  ext i j : 1
  refine TrivSqZeroExt.ext ?_ ?_ <;> by_cases h : i = j <;> simp [dm, Matrix.one_apply, h]

theorem dm_mul (U V U' V' : Matrix (Fin n) (Fin n) R) :
    dm U V * dm U' V' = dm (U * U') (U * V' + V * U') := by
  ext i j : 1
  refine TrivSqZeroExt.ext ?_ ?_
  · simp [dm, Matrix.mul_apply, TrivSqZeroExt.fst_sum]
  · simp [dm, Matrix.mul_apply, TrivSqZeroExt.snd_sum, Finset.sum_add_distrib, mul_comm]

theorem dm_smul (a : DualNumber R) (U V : Matrix (Fin n) (Fin n) R) :
    a • dm U V = dm (a.fst • U) (a.fst • V + a.snd • U) := by
  ext i j : 1
  refine TrivSqZeroExt.ext ?_ ?_
  · simp [dm]
  · simp [dm, mul_comm]

theorem dm_pow (N g : Matrix (Fin n) (Fin n) R) (hc : g * N = N * g) (k : ℕ) :
    dm N g ^ (k + 1) = dm (N ^ (k + 1)) (((k + 1 : ℕ) : R) • (N ^ k * g)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, dm_mul]
    congr 1
    rw [Matrix.smul_mul, Matrix.mul_assoc (N ^ k) g N, hc, ← Matrix.mul_assoc, ← pow_succ]
    rw [show (((k + 1 + 1 : ℕ) : R)) = ((k + 1 : ℕ) : R) + 1 by push_cast; ring, add_smul, one_smul]
    abel
end Dual
end GlobalTheory.Tw.CentralizerAdjoin

namespace GlobalTheory.Tw.CentralizerAdjoin
section Comm
variable {n : ℕ} {R : Type} [CommRing R]

theorem snd_aeval (N g : Matrix (Fin n) (Fin n) R) (hc : g * N = N * g) (P : (DualNumber R)[X]) :
    ∃ Q : R[X], (aeval (dm N g) P).map TrivSqZeroExt.snd =
      aeval N (derivative (P.map (TrivSqZeroExt.fstHom R R R).toRingHom)) * g + aeval N Q := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨Q1, h1⟩ := hp
    obtain ⟨Q2, h2⟩ := hq
    refine ⟨Q1 + Q2, ?_⟩
    rw [map_add (f := _), Matrix.map_add _ TrivSqZeroExt.snd_add, h1, h2, Polynomial.map_add (f := _), derivative_add,
      map_add, map_add, Matrix.add_mul]
    abel
  | monomial k a =>
    cases k with
    | zero =>
      refine ⟨C a.snd, ?_⟩
      rw [aeval_monomial, pow_zero, mul_one, Algebra.algebraMap_eq_smul_one, ← dm_one, dm_smul, dm_snd]
      simp [Algebra.algebraMap_eq_smul_one]
    | succ k =>
      refine ⟨monomial (k + 1) a.snd, ?_⟩
      rw [aeval_monomial, ← Algebra.smul_def, dm_pow N g hc, dm_smul, dm_snd, Polynomial.map_monomial,
        derivative_monomial, aeval_monomial, aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, TrivSqZeroExt.fstHom_apply, add_tsub_cancel_right,
        smul_zero, zero_add, Matrix.smul_mul, smul_smul]

theorem mem_adjoin_of_commute (N g : Matrix (Fin n) (Fin n) R) (hs : N.charpoly.Separable)
    (hc : g * N = N * g) : g ∈ Algebra.adjoin R {N} := by
  obtain ⟨Q, hQ⟩ := snd_aeval N g hc (dm N g).charpoly
  have hf : (dm N g).map (TrivSqZeroExt.fstHom R R R).toRingHom = N := dm_fst N g
  rw [← Matrix.charpoly_map, hf, Matrix.aeval_self_charpoly, Matrix.map_zero _ rfl] at hQ
  obtain ⟨a, b, hab⟩ := hs
  have h1 : aeval N b * aeval N (derivative N.charpoly) = 1 := by
    have := congrArg (aeval N) hab
    rwa [map_add, map_mul, map_mul, Matrix.aeval_self_charpoly, Matrix.mul_zero, zero_add, map_one] at this
  have h2 : g = - aeval N (b * Q) := by
    rw [map_mul, ← Matrix.mul_neg, ← eq_neg_iff_add_eq_zero.mpr hQ.symm, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [h2]
  exact neg_mem (aeval_mem_adjoin_singleton R N)

end Comm
end GlobalTheory.Tw.CentralizerAdjoin

namespace GlobalTheory.Tw.CentralizerAdjoin
section Tw
variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]
open GlobalTheory.Tw.Model

theorem inv_mem_adjoin_of_isUnit {N : Matrix (Fin n) (Fin n) R} (hN : IsUnit N) :
    N⁻¹ ∈ Algebra.adjoin R {N} := by
  have hd := (Matrix.isUnit_iff_isUnit_det N).mp hN
  have hc : IsUnit (N.charpoly.coeff 0) := by
    rw [Matrix.det_eq_sign_charpoly_coeff] at hd
    exact isUnit_of_mul_isUnit_right hd
  have key := congrArg (aeval N) (Polynomial.X_mul_divX_add N.charpoly)
  rw [Matrix.aeval_self_charpoly, map_add (f := _), map_mul, aeval_X, aeval_C] at key
  have hinv : N⁻¹ = -((hc.unit⁻¹ : Rˣ) : R) • aeval N (divX N.charpoly) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.mul_smul, eq_neg_iff_add_eq_zero.mpr key, smul_neg, neg_smul, neg_neg,
      Algebra.algebraMap_eq_smul_one, smul_smul, hc.val_inv_mul, one_smul]
  rw [hinv]
  exact Subalgebra.smul_mem _ (aeval_mem_adjoin_singleton R N) _

theorem adj_mul' {δ : Matrix (Fin n) (Fin n) R} (hδ : IsUnit δ) (g h : Matrix (Fin n) (Fin n) R) :
    adj δ (g * h) = adj δ h * adj δ g := by
  have hd := (Matrix.isUnit_iff_isUnit_det δ).mp hδ
  simp only [adj, conjTranspose_mul, Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ hd, ← Matrix.mul_assoc (Phi n R)ᵀ (Phi n R),
    transpose_mul_Phi, Matrix.one_mul]

theorem adj_semi (δ : Matrix (Fin n) (Fin n) R) (c : R) (g h : Matrix (Fin n) (Fin n) R) :
    adj δ (c • g + h) = star c • adj δ g + adj δ h := by
  simp only [adj, conjTranspose_add, conjTranspose_smul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul]

theorem adj_one' {δ : Matrix (Fin n) (Fin n) R} (hδ : IsUnit δ) : adj δ 1 = 1 := by
  have hd := (Matrix.isUnit_iff_isUnit_det δ).mp hδ
  rw [adj, conjTranspose_one, Matrix.mul_one, Matrix.mul_assoc δ, Phi_mul_transpose, Matrix.mul_one,
    Matrix.mul_nonsing_inv _ hd]

theorem adj_algebraMap {δ : Matrix (Fin n) (Fin n) R} (hδ : IsUnit δ) (r : R) :
    adj δ (algebraMap R _ r) = algebraMap R _ (star r) := by
  have h := adj_semi δ r 1 0
  rw [add_zero, adj_one' hδ] at h
  have h0 : adj δ 0 = 0 := by simp [adj]
  rw [h0, add_zero] at h
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, h]

theorem isUnit_theta' {δ : Matrix (Fin n) (Fin n) R} (hδ : IsUnit δ) : IsUnit (theta δ) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse (theta_mul_theta_inv hδ))

theorem isUnit_nrm {δ : Matrix (Fin n) (Fin n) R} (hδ : IsUnit δ) : IsUnit (nrm δ) :=
  hδ.mul (isUnit_theta' hδ)

theorem adj_nrm {δ : Matrix (Fin n) (Fin n) R} (hδ : IsUnit δ) : adj δ (nrm δ) = (nrm δ)⁻¹ := by
  have hd := (Matrix.isUnit_iff_isUnit_det δ).mp hδ
  rw [adj_eq hδ (isUnit_nrm hδ)]
  congr 1
  rw [nrm, theta_mul, theta_theta hδ]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]

theorem commute_of_mem (N g : Matrix (Fin n) (Fin n) R) (hg : g ∈ Algebra.adjoin R {N}) :
    g * N = N * g := by
  induction hg using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.mp hx]
  | algebraMap r => exact Algebra.commutes r N
  | add x y _ _ hx hy => rw [Matrix.add_mul, Matrix.mul_add, hx, hy]
  | mul x y _ _ hx hy => rw [Matrix.mul_assoc, hy, ← Matrix.mul_assoc, hx, Matrix.mul_assoc]

theorem adj_adjoin {δ : Matrix (Fin n) (Fin n) R} (hδ : IsUnit δ) (g : Matrix (Fin n) (Fin n) R)
    (hg : g ∈ Algebra.adjoin R {nrm δ}) :
    adj δ g ∈ Algebra.adjoin R {nrm δ} ∧ adj δ (adj δ g) = g := by
  have hN := isUnit_nrm hδ
  have hNd := (Matrix.isUnit_iff_isUnit_det _).mp hN
  have hadd : ∀ x y : Matrix (Fin n) (Fin n) R, adj δ (x + y) = adj δ x + adj δ y := fun x y => by
    simpa using adj_semi δ 1 x y
  have hinvN : adj δ (nrm δ)⁻¹ = nrm δ := by
    have h1 : adj δ (nrm δ)⁻¹ * (nrm δ)⁻¹ = 1 := by
      calc adj δ (nrm δ)⁻¹ * (nrm δ)⁻¹ = adj δ (nrm δ)⁻¹ * adj δ (nrm δ) := by rw [adj_nrm hδ]
        _ = adj δ (nrm δ * (nrm δ)⁻¹) := (adj_mul' hδ _ _).symm
        _ = 1 := by rw [Matrix.mul_nonsing_inv _ hNd, adj_one' hδ]
    calc adj δ (nrm δ)⁻¹ = adj δ (nrm δ)⁻¹ * (nrm δ)⁻¹ * nrm δ := by
          rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hNd, Matrix.mul_one]
      _ = nrm δ := by rw [h1, Matrix.one_mul]
  induction hg using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.mp hx, adj_nrm hδ, hinvN]
    exact ⟨inv_mem_adjoin_of_isUnit hN, rfl⟩
  | algebraMap r =>
    rw [adj_algebraMap hδ, adj_algebraMap hδ, star_star]
    exact ⟨Subalgebra.algebraMap_mem _ _, rfl⟩
  | add x y _ _ hx hy =>
    rw [hadd, hadd, hx.2, hy.2]
    exact ⟨add_mem hx.1 hy.1, rfl⟩
  | mul x y _ _ hx hy =>
    rw [adj_mul' hδ, adj_mul' hδ, hx.2, hy.2]
    exact ⟨mul_mem hy.1 hx.1, rfl⟩

end Tw
end GlobalTheory.Tw.CentralizerAdjoin

namespace GlobalTheory.Tw.CentralizerAdjoin
section Cent
variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]
open GlobalTheory.Tw.Model

theorem cent_eq {δ : Matrix (Fin n) (Fin n) R} (hδ : Reg δ) :
    cent δ = {g | g ∈ Algebra.adjoin R {nrm δ} ∧ g * adj δ g = 1} := by
  have hu := hδ.1
  have hd := (Matrix.isUnit_iff_isUnit_det δ).mp hu
  ext g
  constructor
  · rintro ⟨hgU, hgd⟩
    have hc : g * nrm δ = nrm δ * g :=
      calc g * nrm δ = g * δ * theta δ := by rw [nrm, Matrix.mul_assoc]
        _ = δ * theta g * theta δ := by rw [hgd]
        _ = δ * theta (g * δ) := by rw [theta_mul, Matrix.mul_assoc]
        _ = δ * theta (δ * theta g) := by rw [hgd]
        _ = nrm δ * g := by rw [theta_mul, theta_theta hgU, nrm, Matrix.mul_assoc]
    refine ⟨mem_adjoin_of_commute _ g hδ.2 hc, ?_⟩
    rw [adj_eq hu hgU, ← hgd, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det g).mp hgU)]
  · rintro ⟨-, h⟩
    have hgd := Matrix.isUnit_det_of_right_inverse h
    have hgU : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).mpr hgd
    have hU1 : IsUnit (δ * theta g * δ⁻¹) :=
      (hu.mul (isUnit_theta' hgU)).mul (Matrix.isUnit_nonsing_inv_iff.mpr hu)
    have h2 : (δ * theta g * δ⁻¹)⁻¹ = g⁻¹ := by
      rw [← adj_eq hu hgU]; exact (Matrix.inv_eq_right_inv h).symm
    have e := congrArg Inv.inv h2
    rw [Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hU1),
      Matrix.nonsing_inv_nonsing_inv _ hgd] at e
    refine ⟨hgU, ?_⟩
    calc g * δ = δ * theta g * δ⁻¹ * δ := by rw [e]
      _ = δ * theta g := by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]

end Cent
end GlobalTheory.Tw.CentralizerAdjoin

open GlobalTheory.Tw.CentralizerAdjoin in
theorem GlobalTheory.Tw.twisted_centraliser :
    ∀ (n : ℕ) (R : Type) [CommRing R] [StarRing R] [IsArtinianRing R] [IsReduced R] (δ : Matrix (Fin n) (Fin n) R),
      Reg δ → (∀ g h, adj δ (g * h) = adj δ h * adj δ g) ∧ (∀ (c : R) g h, adj δ (c • g + h) = star c • adj δ g + adj δ h) ∧
        adj δ (nrm δ) = (nrm δ)⁻¹ ∧
        (∀ g ∈ Algebra.adjoin R {nrm δ}, adj δ g ∈ Algebra.adjoin R {nrm δ} ∧ adj δ (adj δ g) = g) ∧
        (∀ g, g * nrm δ = nrm δ * g ↔ g ∈ Algebra.adjoin R {nrm δ}) ∧
        cent δ = {g | g ∈ Algebra.adjoin R {nrm δ} ∧ g * adj δ g = 1} := by
  intro n R _ _ _ _ δ hδ
  exact ⟨adj_mul' hδ.1, adj_semi δ, adj_nrm hδ.1, adj_adjoin hδ.1,
    fun g => ⟨mem_adjoin_of_commute _ g hδ.2, commute_of_mem _ g⟩, cent_eq hδ⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmallDualLattices
open GlobalTheory.JR MeasureTheory Filter Topology

namespace GlobalTheory.JR.DualLattice

variable {F : Type} [NontriviallyNormedField F]

theorem stdChar_key {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) (y : F)
    (h : ∀ c : F, ‖c‖ ≤ 1 → ψ (c * y) = 1) : ‖y‖ ≤ 1 := by
  by_contra hy
  push Not at hy
  obtain ⟨x0, hx0, hx1⟩ := hψ.2
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy; linarith
  have hinv : ‖y⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hy
  have := h _ (hx1 _ hinv)
  rw [mul_assoc, inv_mul_cancel₀ hy0, mul_one] at this
  exact hx0 this

theorem stdChar_continuous {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) : Continuous ψ := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_)
  filter_upwards [Metric.closedBall_mem_nhds x one_pos] with y hy
  have : y = x + (y - x) := by ring
  rw [this, AddChar.map_add_eq_mul, hψ.1 (y - x) (by simpa [dist_eq_norm] using hy), mul_one]

variable {V : Type} [AddCommGroup V] [Module F V]

def box [IsUltrametricDist F] {ι : Type} (e : Module.Basis ι F V) (r : ℝ) (hr : 0 ≤ r) : AddSubgroup V where
  carrier := {x | ∀ i, ‖e.repr x i‖ ≤ r}
  zero_mem' := by intro i; simpa using hr
  add_mem' := by
    intro a b ha hb i
    rw [map_add (f := _), Finsupp.add_apply]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (hb i))
  neg_mem' := by
    intro a ha i
    simpa using ha i

theorem mem_box [IsUltrametricDist F] {ι : Type} (e : Module.Basis ι F V) (r : ℝ) (hr : 0 ≤ r) (x : V) :
    x ∈ box e r hr ↔ ∀ i, ‖e.repr x i‖ ≤ r := Iff.rfl

noncomputable def coordHomeo [TopologicalSpace V] [IsModuleTopology F V] {ι : Type} [Fintype ι]
    (e : Module.Basis ι F V) : V ≃ₜ (ι → F) :=
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd F V
  { e.equivFun.toEquiv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.equivFun.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.equivFun.symm.toLinearMap }

theorem box_eq [IsUltrametricDist F] [TopologicalSpace V] [IsModuleTopology F V] {ι : Type} [Fintype ι]
    (e : Module.Basis ι F V) (r : ℝ) (hr : 0 ≤ r) :
    (box e r hr : Set V) = coordHomeo e ⁻¹' Metric.closedBall 0 r := by
  ext x
  rw [SetLike.mem_coe, mem_box, Set.mem_preimage, mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hr]
  rfl

theorem box_open_compact [IsUltrametricDist F] [LocallyCompactSpace F] [TopologicalSpace V]
    [IsModuleTopology F V] {ι : Type} [Fintype ι]
    (e : Module.Basis ι F V) (r : ℝ) (hr : 0 < r) :
    IsOpen (box e r hr.le : Set V) ∧ IsCompact (box e r hr.le : Set V) := by
  haveI : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  rw [box_eq]
  exact ⟨(IsUltrametricDist.isOpen_closedBall _ hr.ne').preimage (coordHomeo e).continuous,
    (coordHomeo e).isCompact_preimage.2 (isCompact_closedBall _ _)⟩

theorem box_dual [IsUltrametricDist F] {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) {ι : Type} [Fintype ι]
    (e e' : Module.Basis ι F V) (B : V → V → F)
    (hB : ∀ x y, B x y = ∑ i, e.repr x i * e'.repr y i) (t : F) (ht : t ≠ 0) (y : V) :
    y ∈ box e' ‖t⁻¹‖ (norm_nonneg _) ↔ ∀ x ∈ box e ‖t‖ (norm_nonneg _), ψ (B x y) = 1 := by
  classical
  have htp : 0 < ‖t‖ := norm_pos_iff.2 ht
  constructor
  · intro hy x hx
    apply hψ.1
    rw [hB]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [norm_mul]
    calc _ ≤ ‖t‖ * ‖t⁻¹‖ := mul_le_mul (hx i) (hy i) (norm_nonneg _) (norm_nonneg _)
      _ = 1 := by rw [← norm_mul, mul_inv_cancel₀ ht, norm_one]
  · intro h i
    have h1 : ‖t * e'.repr y i‖ ≤ 1 := by
      refine stdChar_key hψ _ fun c hc => ?_
      have hx : (c * t) • e i ∈ box e ‖t‖ (norm_nonneg _) := by
        intro j
        rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
        split_ifs
        · rw [smul_eq_mul, mul_one, norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) hc
        · simp
      have := h _ hx
      rw [hB, Finset.sum_eq_single i] at this
      · simpa [mul_assoc] using this
      · intro j _ hj
        simp [Finsupp.single_apply, hj.symm]
      · simp
    rw [norm_mul] at h1
    rw [norm_inv, ← one_div, le_div_iff₀ htp, mul_comm]
    exact h1

end GlobalTheory.JR.DualLattice

open GlobalTheory.JR.DualLattice in
theorem GlobalTheory.JR.exists_small_dual_lattices : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F] (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] (β : LinearMap.BilinForm F V), β.IsSymm → β.Nondegenerate → Continuous (fun p : V × V => ψ (β p.1 p.2)) ∧ (∀ U ∈ 𝓝 (0 : V), ∃ M N : AddSubgroup V, (M : Set V) ⊆ U ∧ IsOpen (M : Set V) ∧ IsCompact (M : Set V) ∧ IsOpen (N : Set V) ∧ IsCompact (N : Set V) ∧ (∀ y, y ∈ N ↔ ∀ x ∈ M, ψ (β x y) = 1) ∧ (∀ x, x ∈ M ↔ ∀ y ∈ N, ψ (β x y) = 1)) := by
  intro F _ _ _ ψ hψ V _ _ _ _ _ β hs hβ
  classical
  let e := Module.finBasis F V
  let e' := β.dualBasis hβ e
  have hB : ∀ x y, β x y = ∑ i, e.repr x i * e'.repr y i := by
    intro x y
    conv_lhs => rw [← e.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, hs.eq]
  refine ⟨(stdChar_continuous hψ).comp ?_, fun U hU => ?_⟩
  · simp only [hB]
    refine continuous_finsetSum _ fun i _ => ?_
    exact (((continuous_apply i).comp (coordHomeo e).continuous).comp continuous_fst).mul
      (((continuous_apply i).comp (coordHomeo e').continuous).comp continuous_snd)
  · have h0 : (coordHomeo e).symm 0 = 0 := map_zero e.equivFun.symm
    have hU' : (coordHomeo e).symm ⁻¹' U ∈ 𝓝 (0 : Fin (Module.finrank F V) → F) :=
      (coordHomeo e).symm.continuous.continuousAt.preimage_mem_nhds (by rwa [h0])
    obtain ⟨ε, hε, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hU'
    obtain ⟨t, ht0, htε⟩ := NormedField.exists_norm_lt F hε
    have ht : t ≠ 0 := norm_pos_iff.1 ht0
    have hti : 0 < ‖t⁻¹‖ := norm_pos_iff.2 (inv_ne_zero ht)
    refine ⟨box e ‖t‖ (norm_nonneg _), box e' ‖t⁻¹‖ (norm_nonneg _), ?_,
      (box_open_compact e _ ht0).1, (box_open_compact e _ ht0).2,
      (box_open_compact e' _ hti).1, (box_open_compact e' _ hti).2,
      box_dual hψ e e' (fun x y => β x y) hB t ht, fun x => ?_⟩
    · rw [box_eq]
      intro x hx
      have := hsub (Metric.closedBall_subset_closedBall htε.le hx)
      simpa using this
    · have := box_dual hψ e' e (fun y x => β x y)
        (fun y x => by simp only [hB, mul_comm]) t⁻¹ (inv_ne_zero ht) x
      simpa only [inv_inv] using this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitting
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def WeilAt (A : Et F E) : Prop :=
  ∀ ψ : AddChar F ℂ, IsStdChar ψ → ∀ (x : A.Kˣ) (μ : Measure A.L), SelfDual μ (A.kerL ψ x) →
    ∃ γ W, A.IsWeil ψ x A.etaK μ γ W

def IsSplitting (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L) : Prop :=
  (∀ k : A.K, eL (algebraMap A.K A.L k) = (algebraMap A₁.K A₁.L (eK k).1, algebraMap A₂.K A₂.L (eK k).2)) ∧
  (∀ e : E, eL (algebraMap E A.L e) = (algebraMap E A₁.L e, algebraMap E A₂.L e)) ∧
  ∀ y : A.L, eL (star y) = (star (eL y).1, star (eL y).2)

end GlobalTheory.JR
end
end
