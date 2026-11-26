module

public import GroundTheory.AutomorphicForms.Cartan
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
public import Formalism.FormalDegreeBessel.StatementDS
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitProductClosureProperties
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanExists
namespace GlobalTheory.CompanionTheory.Dblock.CartanDVR

open Matrix

theorem cartan_exists : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] (n : ℕ) (ϖ : R), Irreducible ϖ →
    ∀ g : Matrix (Fin n) (Fin n) K, IsUnit g.det →
      ∃ (u v : Matrix (Fin n) (Fin n) R) (a : Fin n → ℤ), IsUnit u.det ∧ IsUnit v.det ∧ Antitone a ∧
        g = u.map (algebraMap R K) * Matrix.diagonal (fun i => (algebraMap R K ϖ) ^ (a i)) *
          v.map (algebraMap R K) := by
  intro R K _ _ _ _ _ _ n ϖ hϖ g hg
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K

  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun p : Fin n × Fin n => g p.1 p.2)
  have hb0 : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.2
  choose A' hA' using hb
  let A : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => A' (i, j)
  have hAg : A.map (algebraMap R K) = algebraMap R K (b : R) • g := by
    ext i j
    simpa [A, Algebra.smul_def] using hA' (i, j)
  have hbK : algebraMap R K (b : R) ≠ 0 := fun h => hb0 (hinj (by simpa using h))
  have hA : A.det ≠ 0 := by
    intro h
    have h1 : (A.map (algebraMap R K)).det = 0 := by
      have := RingHom.map_det (algebraMap R K) A
      rw [h, map_zero] at this
      simpa using this.symm
    rw [hAg, Matrix.det_smul] at h1
    exact (mul_ne_zero (pow_ne_zero _ hbK) hg.ne_zero) h1
  obtain ⟨P, Q, e, he, hPQ⟩ := GroundTheory.Automorphic.Cartan.exists_eq_mul_diagonal_pow_mul hϖ A hA
  obtain ⟨c, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hϖK : algebraMap R K ϖ ≠ 0 := fun h => hϖ.ne_zero (hinj (by simpa using h))
  have hwK : algebraMap R K (w : R) ≠ 0 := fun h => w.ne_zero (hinj (by simpa using h))
  have hPd : IsUnit (P : Matrix (Fin n) (Fin n) R).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 P.isUnit
  have hQd : IsUnit (Q : Matrix (Fin n) (Fin n) R).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 Q.isUnit
  refine ⟨((w⁻¹ : Rˣ) : R) • (P : Matrix (Fin n) (Fin n) R), Q, fun i => (e i : ℤ) - c, ?_, hQd, ?_, ?_⟩
  · rw [Matrix.det_smul]
    exact ((Units.isUnit _).pow _).mul hPd
  · intro i j hij
    have := he hij
    simp only
    omega
  · have hwinv : algebraMap R K ((w⁻¹ : Rˣ) : R) = (algebraMap R K (w : R))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← map_mul]
      simp
    have hdiag : Matrix.diagonal (fun i => (algebraMap R K ϖ) ^ ((e i : ℤ) - c)) =
        ((algebraMap R K ϖ) ^ c)⁻¹ • (Matrix.diagonal (fun i => ϖ ^ e i)).map (algebraMap R K) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [zpow_sub₀ hϖK, div_eq_mul_inv, mul_comm]
      · simp [Matrix.diagonal_apply_ne _ hij]
    have hmap : A.map (algebraMap R K) = (P : Matrix (Fin n) (Fin n) R).map (algebraMap R K) *
        (Matrix.diagonal (fun i => ϖ ^ e i)).map (algebraMap R K) *
        (Q : Matrix (Fin n) (Fin n) R).map (algebraMap R K) := by
      rw [hPQ]
      simp only [Matrix.map_mul]
    have hsm : (((w⁻¹ : Rˣ) : R) • (P : Matrix (Fin n) (Fin n) R)).map (algebraMap R K) =
        (algebraMap R K (w : R))⁻¹ • (P : Matrix (Fin n) (Fin n) R).map (algebraMap R K) := by
      ext i j
      simp [hwinv]
    rw [hsm, hdiag, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, smul_smul, ← hmap, hAg,
      smul_smul, hw]
    have : (algebraMap R K (w : R))⁻¹ * ((algebraMap R K ϖ) ^ c)⁻¹ *
        algebraMap R K ((w : R) * ϖ ^ c) = 1 := by
      rw [map_mul, map_pow]
      field_simp
    rw [this, one_smul]

end GlobalTheory.CompanionTheory.Dblock.CartanDVR
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne
noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}

def IsUnif (p : Lˣ) : Prop := ‖(p : L)‖ < 1 ∧ ∀ x : L, x ≠ 0 → ∃ a : ℤ, ‖x‖ = ‖(p : L)‖ ^ a

theorem entry_mul {A B : Matrix (Fin n) (Fin n) L} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ i j, ‖A i j‖ ≤ a) (hB : ∀ i j, ‖B i j‖ ≤ b) (i j : Fin n) : ‖(A * B) i j‖ ≤ a * b := by
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb) fun l _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hA i l) (hB l j) (norm_nonneg _) ha

theorem entry_mul_sub_one {A B : Matrix (Fin n) (Fin n) L} {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1)
    (hA : ∀ i j, ‖(A - 1) i j‖ ≤ r) (hB : ∀ i j, ‖(B - 1) i j‖ ≤ r) (i j : Fin n) :
    ‖(A * B - 1) i j‖ ≤ r := by
  have e : A * B - 1 = (A - 1) * (B - 1) + (A - 1) + (B - 1) := by noncomm_ring
  rw [e, Matrix.add_apply, Matrix.add_apply]
  have h := entry_mul h0 h0 hA hB i j
  have h2 : r * r ≤ r := by nlinarith
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (hB i j))
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h.trans h2) (hA i j))


variable (L n) in
def congK (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) : Subgroup (GL (Fin n) L) where
  carrier := {k | ∀ i j, ‖((k : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r ∧
    ‖(((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r}
  mul_mem' := by
    intro a b ha hb i j
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]
      exact entry_mul_sub_one h0 h1 (fun i j => (ha i j).1) (fun i j => (hb i j).1) i j
    · rw [_root_.mul_inv_rev, Units.val_mul]
      exact entry_mul_sub_one h0 h1 (fun i j => (hb i j).2) (fun i j => (ha i j).2) i j
  one_mem' := by
    intro i j
    simp [h0]
  inv_mem' := by
    intro a ha i j
    simpa [and_comm] using ha i j

theorem mem_congK {r : ℝ} {h0 : 0 ≤ r} {h1 : r ≤ 1} {k : GL (Fin n) L} :
    k ∈ congK L n r h0 h1 ↔ ∀ i j, ‖((k : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r ∧
      ‖(((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r := Iff.rfl

def dPow (p : Lˣ) (a : Fin n → ℤ) : GL (Fin n) L where
  val := diagonal fun i => ((p ^ a i : Lˣ) : L)
  inv := diagonal fun i => ((p ^ (-a i) : Lˣ) : L)
  val_inv := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [← Units.val_mul, _root_.zpow_neg, mul_inv_cancel, Units.val_one]
  inv_val := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [← Units.val_mul, _root_.zpow_neg, inv_mul_cancel, Units.val_one]

theorem dPow_val (p : Lˣ) (a : Fin n → ℤ) :
    ((dPow p a : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = diagonal fun i => ((p ^ a i : Lˣ) : L) := rfl

theorem dPow_add (p : Lˣ) (a b : Fin n → ℤ) : (dPow p (a + b) : GL (Fin n) L) = dPow p a * dPow p b := by
  apply Units.ext
  rw [Units.val_mul, dPow_val, dPow_val, dPow_val, diagonal_mul_diagonal]
  congr 1
  funext i
  rw [Pi.add_apply, _root_.zpow_add, Units.val_mul]

theorem dPow_zero (p : Lˣ) : (dPow p (0 : Fin n → ℤ) : GL (Fin n) L) = 1 := by
  apply Units.ext
  simp [dPow_val]

def tExp (n : ℕ) (i : Fin (n + 2)) : Fin n → ℤ :=
  fun j => if (i : ℕ) = n + 1 then -1 else if (j : ℕ) < i then 1 else 0

def tGen (p : Lˣ) (i : Fin (n + 2)) : GL (Fin n) L := dPow p (tExp n i)

end GlobalTheory.CompanionTheory.CartGL
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CapelliPolynomialPermutationMatch
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CapelliPolynomialPermutationMatch
noncomputable section

namespace GlobalTheory.CompanionTheory.CharOfLowK

theorem roots_prod_X_sub_C {n : ℕ} (k : Fin n → ℂ) :
    (∏ a, (Polynomial.X - Polynomial.C (k a))).roots = Multiset.map k Finset.univ.val := by
  have hprod : (∏ a, (Polynomial.X - Polynomial.C (k a))) =
      ((Multiset.map k Finset.univ.val).map fun x => Polynomial.X - Polynomial.C x).prod := by
    rw [Multiset.map_map]
    rfl
  rw [hprod, Polynomial.roots_multiset_prod_X_sub_C]

theorem exists_perm_of_capelliPolynomial_eq {n : ℕ} (f g : Fin n → ℂ)
    (h : ∀ Y, Formalism.QuantumDeterminants.capP f Y = Formalism.QuantumDeterminants.capP g Y) :
    ∃ τ : Equiv.Perm (Fin n), ∀ a, f a = g (τ a) := by
  classical
  have hp : (∏ a, (Polynomial.X - Polynomial.C (-f a))) = ∏ a, (Polynomial.X - Polynomial.C (-g a)) := by
    apply Polynomial.funext
    intro Y
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_neg_eq_add]
    exact h Y
  have hmap : Multiset.map (fun a => -f a) Finset.univ.val = Multiset.map (fun a => -g a) Finset.univ.val := by
    rw [← roots_prod_X_sub_C (fun a => -f a), ← roots_prod_X_sub_C (fun a => -g a)]
    exact congrArg Polynomial.roots hp
  have hcard : ∀ c : ℂ, Fintype.card {a // -f a = c} = Fintype.card {a // -g a = c} := by
    intro c
    have hc := congrArg (Multiset.count c) hmap
    rw [Multiset.count_map, Multiset.count_map] at hc
    rw [Fintype.card_subtype, Fintype.card_subtype, Finset.card, Finset.card, Finset.filter_val,
      Finset.filter_val]
    convert hc using 3 <;> simp [eq_comm]
  let e : ∀ c, {a // -f a = c} ≃ {a // -g a = c} := fun c => Fintype.equivOfCardEq (hcard c)
  let τ : Equiv.Perm (Fin n) :=
    ((Equiv.sigmaFiberEquiv (fun a => -f a)).symm.trans (Equiv.sigmaCongrRight e)).trans
      (Equiv.sigmaFiberEquiv (fun a => -g a))
  refine ⟨τ, fun a => ?_⟩
  have key : -g (τ a) = -f a := (e (-f a) ⟨a, rfl⟩).2
  exact neg_inj.mp key.symm

end GlobalTheory.CompanionTheory.CharOfLowK

namespace GlobalTheory.CompanionTheory.RgCOBlock

open Finset Polynomial

theorem exists_linear_factors_indexed {ι : Type} [DecidableEq ι] (F : Finset ι) :
    ∀ P : ℂ[X], P.Monic → P.natDegree = F.card → ∃ r : ι → ℂ, P = ∏ a ∈ F, (X - C (r a)) := by
  induction F using Finset.induction_on with
  | empty =>
    intro P hm hd
    refine ⟨fun _ => 0, ?_⟩
    simpa using eq_one_of_monic_natDegree_zero hm (by simpa using hd)
  | insert a F ha ih =>
    intro P hm hd
    rw [Finset.card_insert_of_notMem ha] at hd
    have hdeg : P.degree ≠ 0 := by
      intro h
      have : P.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr h.le
      omega
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root P hdeg
    obtain ⟨Q, hQ⟩ := dvd_iff_isRoot.mpr hz
    have hmQ : Q.Monic := by
      have h := hm
      rw [hQ] at h
      exact (monic_X_sub_C z).of_mul_monic_left h
    have hdQ : Q.natDegree = F.card := by
      have h := congrArg natDegree hQ
      rw [(monic_X_sub_C z).natDegree_mul hmQ, natDegree_X_sub_C] at h
      omega
    obtain ⟨r, hr⟩ := ih Q hmQ hdQ
    refine ⟨Function.update r a z, ?_⟩
    rw [Finset.prod_insert ha, Function.update_self, hQ, hr]
    congr 1
    refine Finset.prod_congr rfl fun b hb => ?_
    rw [Function.update_of_ne (fun h : b = a => ha (h ▸ hb))]

theorem exists_perm_of_monic_factors (n M : ℕ) (lev : Fin n → ℕ) (χ : Fin n → ℂ) (P : Fin M → ℂ[X]) (s : Fin M → ℂ)
    (hlev : ∀ a, lev a < M)
    (hP : ∀ i, (P i).Monic ∧ (P i).natDegree = (univ.filter fun a => lev a = (i : ℕ)).card)
    (hcap : ∀ Y : ℂ, ∏ i, (P i).eval (Y + s i) = Formalism.QuantumDeterminants.capP χ Y) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin M,
      ∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)), χ (σ a) =
        (P i).nextCoeff + ((univ.filter fun a => lev a = (i : ℕ)).card : ℂ) * s i := by
  choose r hr using fun i => exists_linear_factors_indexed _ (P i) (hP i).1 (hP i).2
  let lv : Fin n → Fin M := fun a => ⟨lev a, hlev a⟩
  let g : Fin n → ℂ := fun a => s (lv a) - r (lv a) a
  have hfil : ∀ i : Fin M, (univ.filter fun a => lev a = (i : ℕ)) = univ.filter fun a => lv a = i := by
    intro i
    ext a
    simp [lv, Fin.ext_iff]
  have hg : ∀ i : Fin M, ∀ a ∈ univ.filter (fun a => lev a = (i : ℕ)), g a = s i - r i a := by
    intro i a ha
    have : lv a = i := by
      rw [hfil] at ha
      exact (Finset.mem_filter.mp ha).2
    simp only [g, this]
  have hpoly : ∀ Y, Formalism.QuantumDeterminants.capP g Y = Formalism.QuantumDeterminants.capP χ Y := by
    intro Y
    rw [← hcap Y]
    unfold Formalism.QuantumDeterminants.capP
    rw [← Finset.prod_fiberwise univ lv]
    refine Finset.prod_congr rfl fun i _ => ?_
    conv_rhs => rw [hr i, eval_prod]
    rw [hfil i]
    refine Finset.prod_congr rfl fun a ha => ?_
    rw [← hfil i] at ha
    rw [hg i a ha]
    simp only [eval_sub, eval_X, eval_C]
    ring
  obtain ⟨σ, hσ⟩ := GlobalTheory.CompanionTheory.CharOfLowK.exists_perm_of_capelliPolynomial_eq g χ hpoly
  refine ⟨σ, fun i => ?_⟩
  have h1 : ∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)), χ (σ a) =
      ∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)), (s i - r i a) :=
    Finset.sum_congr rfl fun a ha => by rw [← hσ a, hg i a ha]
  rw [h1, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  conv_rhs => rw [hr i, prod_X_sub_C_nextCoeff]
  ring

end GlobalTheory.CompanionTheory.RgCOBlock
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CapelliPolynomialPermutationMatchStatement
open Finset Polynomial

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelli_polynomial_permutation_match : ∀ (n M : ℕ) (lev : Fin n → ℕ) (χ : Fin n → ℂ) (P : Fin M → ℂ[X]) (s : Fin M → ℂ),
    (∀ a, lev a < M) → (∀ i, (P i).Monic ∧ (P i).natDegree = (univ.filter fun a => lev a = (i : ℕ)).card) →
    (∀ Y : ℂ, ∏ i, (P i).eval (Y + s i) = Formalism.QuantumDeterminants.capP χ Y) →
    ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin M,
      ∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)), χ (σ a) =
        (P i).nextCoeff + ((univ.filter fun a => lev a = (i : ℕ)).card : ℂ) * s i := by
  first | exact @GlobalTheory.CompanionTheory.RgCOBlock.exists_perm_of_monic_factors | exact GlobalTheory.CompanionTheory.RgCOBlock.exists_perm_of_monic_factors | (intros; apply GlobalTheory.CompanionTheory.RgCOBlock.exists_perm_of_monic_factors <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsFibreFamilyLength
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.LenFib

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]

theorem sigR_sigR {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (y : R ⊗[F] E) :
    sigR R σ (sigR R σ y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, OneHerm.sigma_sigma hσ]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem hR_self_fixed {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (x : Fin M → R ⊗[F] E) :
    sigR R σ (hR R σ J x x) = hR R σ J x x := by
  have hJR : ∀ i j, sigR R σ (JR R J i j) = JR R J j i := by
    intro i j
    have h := hJ.1 j i
    simp only [JR, Matrix.map_apply, inclR, sigR]
    simp [h]
  unfold hR hform
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, sigR_sigR R hσ, hJR]
  ring

def gramH {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (X : Fin 1 → Fin M → R ⊗[F] E) :
    HermR R σ 1 :=
  ⟨gramR R σ J X, by
    intro a b
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha hb
    exact hR_self_fixed R hσ hJ (X 0)⟩

theorem qR_eq_hermHalf {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (X : Fin 1 → Fin M → R ⊗[F] E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0) = OneHerm.hermHalf R σ (gramH R hσ hJ X) :=
  rfl

theorem hermScal_qR [TopologicalSpace R] [IsTopologicalRing R] {σ : E →ₐ[F] E}
    (hσ : IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (X : Fin 1 → Fin M → R ⊗[F] E) :
    ((hermScal R σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0)) : HermR R σ 1) :
      Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) = gramR R σ J X := by
  rw [qR_eq_hermHalf R hσ hJ X, OneHerm.hermScal_hermHalf R hσ]
  rfl

theorem qR_of_gram [TopologicalSpace R] [IsTopologicalRing R] {σ : E →ₐ[F] E}
    (hσ : IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) {X : Fin 1 → Fin M → R ⊗[F] E} {c : R}
    (h : gramR R σ J X = ((hermScal R σ c : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E))) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0) = c := by
  have h' : gramH R hσ hJ X = hermScal R σ c := Subtype.ext h
  rw [qR_eq_hermHalf R hσ hJ X, h', OneHerm.hermHalf_hermScal R hσ]

theorem isUnit_det_hermScal (σ : E →ₐ[F] E) {c : R} (hc : IsUnit c) :
    IsUnit ((hermScal R σ c : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det := by
  rw [Matrix.det_fin_one]
  exact hc.map (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[F] E)

theorem isUnit_det_gramR [TopologicalSpace R] [IsTopologicalRing R] {σ : E →ₐ[F] E}
    (hσ : IsCMExt F E σ) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) {X : Fin 1 → Fin M → R ⊗[F] E}
    (h : IsUnit (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0))) : IsUnit (gramR R σ J X).det := by
  rw [← hermScal_qR R hσ hJ X]
  exact isUnit_det_hermScal R σ h

theorem continuous_qR {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] :
    Continuous fun X : Fin 1 → Fin M → R ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0) := by
  obtain ⟨-, -, -, -, -, htr, -, -, -, hgr⟩ := TopK.topTens_props F E σ hσ R
  have h := (hgr 1 M J).matrix_elem 0 0
  exact continuous_const.mul (htr.comp h)

theorem exists_bump [TopologicalSpace R] [LocallyCompactSpace R] [T2Space R]
    (hU : IsOpen {c : R | IsUnit c}) {c₀ : R} (hc₀ : IsUnit c₀) :
    ∃ χ : R → ℝ, Continuous χ ∧ tsupport χ ⊆ {c : R | IsUnit c} ∧ ∀ᶠ c in 𝓝 c₀, χ c = 1 := by
  obtain ⟨K, hK, hcK, hKU⟩ := exists_compact_subset hU hc₀
  obtain ⟨f, hf1, -, hfs, -⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  refine ⟨f, f.continuous, hfs, ?_⟩
  filter_upwards [mem_interior_iff_mem_nhds.mp hcK] with c hc using hf1 hc

end GlobalTheory.CompanionTheory.SW.LenFib


open GlobalTheory.CompanionTheory.SW.LenFib in
theorem GlobalTheory.CompanionTheory.SW.isFibreFamily_length : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (μ : Measure (Fin 1 → Fin M → R ⊗[F] E)) (ν : Measure R), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ν {c | ¬ IsUnit c} = 0 → μ {X | ¬ IsUnit ((fun X : Fin 1 → Fin M → R ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (R) σ J (X 0)) X)} = 0 → ∀ m, IsGramFib R σ J 1 μ (ν.map (hermScal R σ)) m → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (fun X : Fin 1 → Fin M → R ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (R) σ J (X 0)) id Set.univ ν {c | IsUnit c} (fun c => m (hermScal R σ c)) := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hLoc μ ν _ _ _ hμ0 m hm
  obtain ⟨hTR, hLC, hSC, hT2, -, -, hOE, -⟩ := hLoc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  obtain ⟨hfib, hint, hcont⟩ := hm
  set q : (Fin 1 → Fin M → R ⊗[F] E) → R := fun X => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0) with hq
  have hqc : Continuous q := LenFib.continuous_qR R hσ J
  have hUo : IsOpen {c : R | IsUnit c} := by
    have h := hOE.isOpen_range
    have he : Set.range (Units.val : Rˣ → R) = {c : R | IsUnit c} := by
      ext c
      exact Iff.rfl
    rwa [he] at h
  have hemb : MeasurableEmbedding (hermScal R σ) := (OneHerm.hermHomeo R hσ).measurableEmbedding
  have hsub : ∀ X, IsUnit (q X) → IsUnit (gramR R σ J X).det := fun X h =>
    LenFib.isUnit_det_gramR R hσ hJ h
  have hres : μ.restrict {X | IsUnit (gramR R σ J X).det} = μ := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    refine measure_mono_null ?_ hμ0
    intro X hX hXq
    exact hX (hsub X hXq)
  have hae : ∀ c, ∀ᵐ X ∂(m (hermScal R σ c)), q X = c := by
    intro c
    refine measure_mono_null ?_ (hfib (hermScal R σ c))
    intro X hX hXm
    exact hX (LenFib.qR_of_gram R hσ hJ hXm.1)
  refine ⟨?_, ?_, ?_⟩
  · intro c
    refine measure_mono_null ?_ (hae c)
    intro X hX hXq
    exact hX ⟨hXq, Set.mem_univ X⟩
  · intro φ hφ
    have h := hint φ hφ
    rw [hres, hemb.lintegral_map] at h
    rw [Measure.restrict_univ, h]
  · intro φ hφc hφs _
    have key : ∀ c₀, IsUnit c₀ → Integrable φ (m (hermScal R σ c₀)) ∧
        ContinuousWithinAt (fun c => ∫ v, φ v ∂(m (hermScal R σ c))) {c | IsUnit c} c₀ := by
      intro c₀ hc₀
      obtain ⟨χ, hχc, hχs, hχ1⟩ := LenFib.exists_bump R hUo hc₀
      have hφ'c : Continuous fun X => φ X * χ (q X) := hφc.mul (hχc.comp hqc)
      have hφ's : HasCompactSupport fun X => φ X * χ (q X) := HasCompactSupport.mul_right hφs
      have hφ't : tsupport (fun X => φ X * χ (q X)) ⊆ {X | IsUnit (gramR R σ J X).det} := by
        intro X hX
        have h1 : X ∈ tsupport (χ ∘ q) := tsupport_mul_subset_right hX
        exact hsub X (hχs (tsupport_comp_subset_preimage χ hqc h1))
      obtain ⟨hI, hC⟩ := hcont _ hφ'c hφ's hφ't
      have heq : ∀ c, χ c = 1 → (fun X => φ X * χ (q X)) =ᵐ[m (hermScal R σ c)] φ := by
        intro c hc
        filter_upwards [hae c] with X hX
        rw [hX, hc, mul_one]
      have hmaps : Set.MapsTo (hermScal R σ) {c : R | IsUnit c}
          {S : HermR R σ 1 | IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det} :=
        fun c hc => LenFib.isUnit_det_hermScal R σ hc
      have hC' : ContinuousOn (fun c => ∫ v, φ v * χ (q v) ∂(m (hermScal R σ c))) {c | IsUnit c} :=
        hC.comp (OneHerm.continuous_hermScal R σ).continuousOn hmaps
      refine ⟨(hI _ (hmaps hc₀)).congr (heq c₀ hχ1.self_of_nhds), ?_⟩
      refine (hC' c₀ hc₀).congr_of_eventuallyEq ?_ ?_
      · filter_upwards [mem_nhdsWithin_of_mem_nhds hχ1] with c hc
        exact (integral_congr_ae (heq c hc)).symm
      · exact (integral_congr_ae (heq c₀ hχ1.self_of_nhds)).symm
    exact ⟨fun c hc => (key c hc).1, fun c hc => (key c hc).2⟩
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeOperatorsSpanAndFaithful
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeOperatorsSpanAndFaithful
open CompanionTheory.Rg.Fl

noncomputable section

namespace GlobalTheory.CompanionTheory.HeckeBasis

variable {G : Type} [Group G] (K : Subgroup G)

theorem lam_single (g : G) (y : G ⧸ K) (c : ℂ) :
    lam K g (Finsupp.single y c) = Finsupp.single (g • y) c := by
  simp [lam, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem lam_mul (g g' : G) (u : (G ⧸ K) →₀ ℂ) :
    lam K (g * g') u = lam K g (lam K g' u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single y c => simp [lam_single, mul_smul]

theorem lam_one (u : (G ⧸ K) →₀ ℂ) : lam K 1 u = u := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single y c => simp [lam_single]

theorem lam_apply_smul (g : G) (u : (G ⧸ K) →₀ ℂ) (y : G ⧸ K) :
    lam K g u (g • y) = u y :=
  Finsupp.mapDomain_apply_of_injective (MulAction.injective g) u y

def IsFixed (u : (G ⧸ K) →₀ ℂ) : Prop := ∀ k ∈ K, lam K k u = u

variable {K}

theorem lam_congr {u : (G ⧸ K) →₀ ℂ} (hu : IsFixed K u) {x x' : G}
    (h : (x : G ⧸ K) = x') : lam K x u = lam K x' u := by
  have hk : x⁻¹ * x' ∈ K := QuotientGroup.eq.1 h
  have : x' = x * (x⁻¹ * x') := by group
  rw [this, lam_mul, hu _ hk]

variable (K)

def op (u : (G ⧸ K) →₀ ℂ) : Module.End ℂ ((G ⧸ K) →₀ ℂ) :=
  Finsupp.lsum ℂ fun y => LinearMap.toSpanSingleton ℂ _ (lam K (Quotient.out y) u)

theorem op_single_out (u : (G ⧸ K) →₀ ℂ) (y : G ⧸ K) (c : ℂ) :
    op K u (Finsupp.single y c) = c • lam K (Quotient.out y) u := by
  simp [op, LinearMap.toSpanSingleton_apply]

variable {K}

theorem op_single {u : (G ⧸ K) →₀ ℂ} (hu : IsFixed K u) (x : G) (c : ℂ) :
    op K u (Finsupp.single (x : G ⧸ K) c) = c • lam K x u := by
  rw [op_single_out, lam_congr hu (QuotientGroup.out_eq' (x : G ⧸ K))]

theorem op_mem {u : (G ⧸ K) →₀ ℂ} (hu : IsFixed K u) : op K u ∈ Hk K := by
  rw [Hk, Subalgebra.mem_centralizer_iff]
  rintro _ ⟨g, rfl⟩
  refine Finsupp.lhom_ext' fun y => LinearMap.ext_ring ?_
  induction y using QuotientGroup.induction_on with
  | H x =>
    have hgx : g • (x : G ⧸ K) = ((g * x : G) : G ⧸ K) := rfl
    simp only [Finsupp.lsingle_apply, Module.End.mul_apply, LinearMap.comp_apply]
    rw [op_single hu, lam_single, hgx, op_single hu, lam_mul]
    simp

variable (K)

def delta : (G ⧸ K) →₀ ℂ := Finsupp.single ((1 : G) : G ⧸ K) 1

theorem lam_delta (x : G) : lam K x (delta K) = Finsupp.single (x : G ⧸ K) 1 := by
  have : x • ((1 : G) : G ⧸ K) = (x : G ⧸ K) := by
    change ((x * 1 : G) : G ⧸ K) = x
    rw [mul_one]
  rw [delta, lam_single, this]

theorem delta_fixed_eval (h : Hk K) : IsFixed K ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K)) := by
  intro k hk
  have hc : lam K k * (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) = (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) * lam K k :=
    (Subalgebra.mem_centralizer_iff ℂ).1 h.2 _ ⟨k, rfl⟩
  have hd : lam K k (delta K) = delta K := by
    have hk1 : (k : G ⧸ K) = ((1 : G) : G ⧸ K) :=
      QuotientGroup.eq.2 (by simpa using K.inv_mem hk)
    rw [lam_delta, delta, hk1]
  have := LinearMap.congr_fun hc (delta K)
  simp only [Module.End.mul_apply] at this
  rw [this, hd]

variable {K}

theorem op_delta {u : (G ⧸ K) →₀ ℂ} (hu : IsFixed K u) : op K u (delta K) = u := by
  rw [delta, op_single hu, lam_one, one_smul]

theorem eq_zero_of_delta (h : Hk K)
    (h0 : (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) = 0) : h = 0 := by
  apply Subtype.ext
  refine Finsupp.lhom_ext' fun y => LinearMap.ext_ring ?_
  induction y using QuotientGroup.induction_on with
  | H x =>
    have hc : lam K x * (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) = (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) * lam K x :=
      (Subalgebra.mem_centralizer_iff ℂ).1 h.2 _ ⟨x, rfl⟩
    have := LinearMap.congr_fun hc (delta K)
    simp only [Module.End.mul_apply] at this
    rw [h0, map_zero, lam_delta] at this
    simpa using this.symm

def orbitVec (hK : IsHeckePair K) (g : G) : (G ⧸ K) →₀ ℂ :=
  ∑ y ∈ (hK g).toFinset, Finsupp.single y (1 : ℂ)

open Classical in
theorem orbitVec_apply (hK : IsHeckePair K) (g : G) (z : G ⧸ K) :
    orbitVec hK g z = if z ∈ MulAction.orbit K (g : G ⧸ K) then 1 else 0 := by
  classical
  simp [orbitVec, Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem lam_apply (k : G) (u : (G ⧸ K) →₀ ℂ) (z : G ⧸ K) :
    lam K k u z = u ((k⁻¹ : G) • z) := by
  have := lam_apply_smul K k u ((k⁻¹ : G) • z)
  rwa [smul_inv_smul] at this

theorem orbitVec_fixed (hK : IsHeckePair K) (g : G) : IsFixed K (orbitVec hK g) := by
  classical
  intro k hk
  ext z
  have hmem : ((k⁻¹ : G) • z ∈ MulAction.orbit K (g : G ⧸ K)) ↔
      z ∈ MulAction.orbit K (g : G ⧸ K) := by
    have e : (k⁻¹ : G) • z = (⟨k, hk⟩ : K)⁻¹ • z := rfl
    rw [e, ← MulAction.orbit_eq_iff, ← MulAction.orbit_eq_iff (a := z), MulAction.orbit_smul]
  rw [lam_apply, orbitVec_apply, orbitVec_apply]
  simp only [hmem]

theorem IsFixed.apply_of_mem_orbit {u : (G ⧸ K) →₀ ℂ} (hu : IsFixed K u) {x z : G ⧸ K}
    (hz : z ∈ MulAction.orbit K x) : u z = u x := by
  obtain ⟨k, rfl⟩ := hz
  have h := lam_apply_smul K (k : G) u x
  rw [hu _ k.2] at h
  exact h

def heckeOp (hK : IsHeckePair K) (g : G) : Hk K :=
  ⟨op K (orbitVec hK g), op_mem (orbitVec_fixed hK g)⟩

theorem heckeOp_delta (hK : IsHeckePair K) (g : G) :
    (heckeOp hK g : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) = orbitVec hK g :=
  op_delta (orbitVec_fixed hK g)

theorem exists_mem_span_delta (hK : IsHeckePair K) (n : ℕ) :
    ∀ u : (G ⧸ K) →₀ ℂ, IsFixed K u → u.support.card ≤ n →
      ∃ t ∈ Submodule.span ℂ (Set.range (heckeOp hK)),
        (t : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) = u := by
  classical
  induction n with
  | zero =>
    intro u _ hc
    have : u = 0 := by simpa using hc
    exact ⟨0, Submodule.zero_mem _, by simp [this]⟩
  | succ n ih =>
    intro u hu hc
    by_cases h0 : u = 0
    · exact ⟨0, Submodule.zero_mem _, by simp [h0]⟩
    obtain ⟨y, hy⟩ := Finsupp.support_nonempty_iff.2 h0
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    set c := u (g : G ⧸ K) with hcdef
    have hc0 : c ≠ 0 := Finsupp.mem_support_iff.1 hy
    have hfix : IsFixed K (u - c • orbitVec hK g) := by
      intro k hk
      rw [map_sub, map_smul, hu k hk, orbitVec_fixed hK g k hk]
    have hsub : (u - c • orbitVec hK g).support ⊆ u.support.erase (g : G ⧸ K) := by
      intro z hz
      have hz' := Finsupp.mem_support_iff.1 hz
      simp only [Finsupp.coe_sub, Finsupp.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        orbitVec_apply] at hz'
      refine Finset.mem_erase.2 ⟨?_, ?_⟩
      · rintro rfl
        apply hz'
        simp [MulAction.mem_orbit_self, ← hcdef]
      · refine Finsupp.mem_support_iff.2 fun hzu => hz' ?_
        have hno : z ∉ MulAction.orbit K (g : G ⧸ K) := fun hm =>
          hc0 (by rw [hcdef, ← hu.apply_of_mem_orbit hm, hzu])
        simp [hzu, hno]
    have hcard : (u - c • orbitVec hK g).support.card ≤ n := by
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hy] at this
      omega
    obtain ⟨t, ht, hte⟩ := ih _ hfix hcard
    refine ⟨t + c • heckeOp hK g,
      Submodule.add_mem _ ht (Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)), ?_⟩
    have : ((t + c • heckeOp hK g : Hk K) : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) =
        (t : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) +
          c • (heckeOp hK g : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) := rfl
    rw [this, hte, heckeOp_delta]
    abel

theorem heckeBasis : ∀ (G : Type) [Group G] (K : Subgroup G), IsHeckePair K → ∃ T : G → Hk K, (∀ (g : G) (S : Finset (G ⧸ K)), (↑S : Set (G ⧸ K)) = MulAction.orbit K (g : G ⧸ K) → (T g : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (Finsupp.single ((1 : G) : G ⧸ K) 1) = ∑ y ∈ S, Finsupp.single y (1 : ℂ)) ∧ Submodule.span ℂ (Set.range T) = ⊤ ∧ ∀ h : Hk K, (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (Finsupp.single ((1 : G) : G ⧸ K) 1) = 0 → h = 0 := by
  intro G _ K hK
  refine ⟨heckeOp hK, ?_, ?_, fun h h0 => eq_zero_of_delta h h0⟩
  · intro g S hS
    have hSe : S = (hK g).toFinset := by
      ext z
      rw [Set.Finite.mem_toFinset, ← hS, Finset.mem_coe]
    have := heckeOp_delta hK g
    rw [orbitVec, ← hSe] at this
    exact this
  · rw [eq_top_iff]
    intro h _
    obtain ⟨t, ht, hte⟩ := exists_mem_span_delta hK _
      ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K)) (delta_fixed_eval K h) le_rfl
    have : h - t = 0 := eq_zero_of_delta (h - t) (by
      have e : ((h - t : Hk K) : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) =
          (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) -
            (t : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) := rfl
      rw [e, hte, sub_self])
    rw [sub_eq_zero.1 this]
    exact ht

end GlobalTheory.CompanionTheory.HeckeBasis
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeOperatorsSpanAndFaithfulStatement
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_operators_span_and_faithful : ∀ (G : Type) [Group G] (K : Subgroup G), IsHeckePair K → ∃ T : G → Hk K, (∀ (g : G) (S : Finset (G ⧸ K)), (↑S : Set (G ⧸ K)) = MulAction.orbit K (g : G ⧸ K) → (T g : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (Finsupp.single ((1 : G) : G ⧸ K) 1) = ∑ y ∈ S, Finsupp.single y (1 : ℂ)) ∧ Submodule.span ℂ (Set.range T) = ⊤ ∧ ∀ h : Hk K, (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (Finsupp.single ((1 : G) : G ⧸ K) 1) = 0 → h = 0 := by
  first | exact @GlobalTheory.CompanionTheory.HeckeBasis.heckeBasis | exact GlobalTheory.CompanionTheory.HeckeBasis.heckeBasis | (intros; apply GlobalTheory.CompanionTheory.HeckeBasis.heckeBasis <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PairingStatement
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PairingStatement
open CompanionTheory.Rg.Fl

namespace GlobalTheory.CompanionTheory.HeckePair

theorem stPair : StPair := by
  intro G _ _ _ K hKo hKc g
  have : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hKo
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hcont : Continuous fun k : K => (((k : G) * g : G) : G ⧸ K) :=
    (QuotientGroup.continuous_mk (N := K)).comp (continuous_subtype_val.mul continuous_const)
  have hfin : (Set.range fun k : K => (((k : G) * g : G) : G ⧸ K)).Finite :=
    (isCompact_range hcont).finite_of_discrete
  refine hfin.subset ?_
  rintro _ ⟨k, rfl⟩
  exact ⟨k, rfl⟩

end GlobalTheory.CompanionTheory.HeckePair
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PairingStatementStatement
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.PairingStatement : StPair := by
  first | exact @GlobalTheory.CompanionTheory.HeckePair.stPair | exact GlobalTheory.CompanionTheory.HeckePair.stPair | (intros; apply GlobalTheory.CompanionTheory.HeckePair.stPair <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MovingStatement
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MovingStatement
open CompanionTheory.Rg.Fl

namespace GlobalTheory.CompanionTheory.CartanMove

variable {G G' : Type} [Group G] [Group G']

theorem closure_symm_eq (e : G ≃* G') {l : ℕ} (t' : Fin l → G') :
    Submonoid.closure (Set.range fun j => e.symm (t' j)) =
      (Submonoid.closure (Set.range t')).map e.symm.toMonoidHom := by
  rw [MonoidHom.map_mclosure, ← Set.range_comp]
  rfl

theorem apply_mem_closure (e : G ≃* G') {l : ℕ} (t' : Fin l → G') {s : G}
    (hs : s ∈ Submonoid.closure (Set.range fun j => e.symm (t' j))) :
    e s ∈ Submonoid.closure (Set.range t') := by
  rw [closure_symm_eq] at hs
  obtain ⟨x, hx, rfl⟩ := hs
  simpa using hx

theorem symm_mem_closure (e : G ≃* G') {l : ℕ} (t' : Fin l → G') {s : G'}
    (hs : s ∈ Submonoid.closure (Set.range t')) :
    e.symm s ∈ Submonoid.closure (Set.range fun j => e.symm (t' j)) := by
  rw [closure_symm_eq]
  exact ⟨s, hs, rfl⟩

theorem isCartan_comap (e : G ≃* G') {K' : Subgroup G'} {d l : ℕ} (h : IsCartan K' d l) :
    IsCartan (K'.comap e.toMonoidHom) d l := by
  obtain ⟨c', t', h1, h2, h3, h4⟩ := h
  have hmem : ∀ {x : G'}, x ∈ K' → e.symm x ∈ K'.comap e.toMonoidHom := fun {x} hx => by
    simpa [Subgroup.mem_comap] using hx
  refine ⟨fun i => e.symm (c' i), fun j => e.symm (t' j), ?_, ?_, ?_, ?_⟩
  · intro i k
    simpa [Subgroup.mem_comap] using h1 i (e k)
  · intro i j
    exact (h2 i j).map e.symm
  · intro g
    obtain ⟨i, j, s, hs, k, hk, k', hk', hg⟩ := h3 (e g)
    refine ⟨i, j, e.symm s, symm_mem_closure e t' hs, e.symm k, hmem hk, e.symm k', hmem hk', ?_⟩
    apply e.injective
    simpa [map_mul] using hg
  · intro s hs s' hs' k hk
    obtain ⟨a, ha, b, hb, hab⟩ := h4 (e s) (apply_mem_closure e t' hs) (e s')
      (apply_mem_closure e t' hs') (e k) hk
    refine ⟨e.symm a, hmem ha, e.symm b, hmem hb, ?_⟩
    apply e.injective
    simpa [map_mul] using hab

theorem stMove : StMove := by
  intro G G' _ _ _ _ e h U hU
  have hopen : IsOpen ((U.map e.toMulEquiv.toMonoidHom : Subgroup G') : Set G') := by
    have : ((U.map e.toMulEquiv.toMonoidHom : Subgroup G') : Set G') = e.toHomeomorph '' (U : Set G) := rfl
    rw [this]
    exact e.toHomeomorph.isOpenMap _ hU
  obtain ⟨K', hK'U, hoK', hcK', d, l, hC⟩ := h _ hopen
  refine ⟨K'.comap e.toMulEquiv.toMonoidHom, ?_, ?_, ?_, d, l, isCartan_comap _ hC⟩
  · intro x hx
    obtain ⟨u, hu, hux⟩ := hK'U hx
    have : u = x := e.toMulEquiv.injective hux
    exact this ▸ hu
  · exact hoK'.preimage e.toHomeomorph.continuous
  · exact e.toHomeomorph.isCompact_preimage.2 hcK'

end GlobalTheory.CompanionTheory.CartanMove
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MovingStatementStatement
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.MovingStatement : StMove := by
  first | exact @GlobalTheory.CompanionTheory.CartanMove.stMove | exact GlobalTheory.CompanionTheory.CartanMove.stMove | (intros; apply GlobalTheory.CompanionTheory.CartanMove.stMove <;> assumption)
end
end
