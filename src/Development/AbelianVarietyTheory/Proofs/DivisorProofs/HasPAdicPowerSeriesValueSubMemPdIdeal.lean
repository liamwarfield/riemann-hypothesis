module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHopfIdealKerIdealOfBialgHom
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.WChartsB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PderivEqZeroOfColOp
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeAndRelDimOfOpenCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHopfIdealKerIdealOfBialgHomStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueSubMemPdIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueSubMemPdIdeal
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

namespace GlobalTheory.HasValCong

open scoped Nat

section Ring

variable {B : Type} [CommRing B]

theorem pow_eq_pow_factorization_mul (p : ℕ) (hp : p.Prime) (J : Ideal B)
    (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) :
    ∀ n : ℕ, 0 < n → ∀ x ∈ J, ∃ y ∈ J, x ^ n = (p : B) ^ ((n)!.factorization p) * y := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn x hx
    by_cases hpn : p ∣ n
    · obtain ⟨m, rfl⟩ := hpn
      have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
      have hmn : m < p * m := by
        have := hp.two_le
        nlinarith
      obtain ⟨y, hy, hxy⟩ := hJ x hx
      obtain ⟨y', hy', hyy⟩ := ih m hmn hm y hy
      refine ⟨y', hy', ?_⟩
      rw [Nat.factorization_factorial_mul hp, pow_mul, hxy, mul_pow, hyy, pow_add]
      ring
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact ⟨x, hx, by simp⟩
      obtain ⟨y, hy, hxy⟩ := ih k (by omega) hk x hx
      refine ⟨x * y, J.mul_mem_left x hy, ?_⟩
      have h0 : (k + 1).factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpn
      rw [Nat.factorial_succ, Nat.factorization_mul (by omega) (Nat.factorial_ne_zero k),
        Finsupp.coe_add, Pi.add_apply, h0, zero_add, pow_succ, hxy]
      ring

theorem pow_eq_factorial_mul (p : ℕ) (hp : p.Prime)
    (hu : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B)) (J : Ideal B)
    (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) (n : ℕ) (hn : 0 < n) (x : B) (hx : x ∈ J) :
    ∃ y ∈ J, x ^ n = ((n ! : ℕ) : B) * y := by
  obtain ⟨y, hy, hxy⟩ := pow_eq_pow_factorization_mul p hp J hJ n hn x hx
  obtain ⟨u, hu'⟩ := hu (n ! / p ^ (n !).factorization p)
    (Nat.coprime_ordCompl hp (Nat.factorial_ne_zero n)).symm
  refine ⟨(↑u⁻¹ : B) * y, J.mul_mem_left _ hy, ?_⟩
  have hfac : ((n ! : ℕ) : B) =
      (p : B) ^ (n !).factorization p * ((n ! / p ^ (n !).factorization p : ℕ) : B) := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self]
  rw [hxy, hfac, ← hu', mul_assoc, ← mul_assoc (u : B), Units.mul_inv, one_mul]

theorem sum_eq_mul_mem {ι : Type} (s : Finset ι) (c : B) (J : Ideal B) (f : ι → B)
    (h : ∀ i ∈ s, ∃ y ∈ J, f i = c * y) : ∃ y ∈ J, ∑ i ∈ s, f i = c * y := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, J.zero_mem, by simp⟩
  | insert i s hi ih =>
    obtain ⟨y, hy, e⟩ := h i (Finset.mem_insert_self i s)
    obtain ⟨y', hy', e'⟩ := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
    exact ⟨y + y', J.add_mem hy hy', by rw [Finset.sum_insert hi, e, e', mul_add]⟩

theorem add_pow_sub_pow (p : ℕ) (hp : p.Prime)
    (hu : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B)) (J : Ideal B)
    (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) (a j : B) (hj : j ∈ J) (n : ℕ) :
    ∃ y ∈ J, (a + j) ^ n - a ^ n = (n : B) * y := by
  rcases n with _ | n
  · exact ⟨0, J.zero_mem, by simp⟩
  rw [add_comm a j, add_pow, Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero]
  rw [add_sub_cancel_right]
  apply sum_eq_mul_mem
  intro k _
  obtain ⟨y, hy, hjy⟩ := pow_eq_factorial_mul p hp hu J hJ (k + 1) (Nat.succ_pos k) j hj
  refine ⟨((n.descFactorial k : ℕ) : B) * a ^ (n + 1 - (k + 1)) * y, J.mul_mem_left _ hy, ?_⟩
  have h : (n + 1).choose (k + 1) * (k + 1)! = (n + 1) * n.descFactorial k := by
    rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose, Nat.succ_descFactorial_succ]
  have h' : (((n + 1).choose (k + 1) : ℕ) : B) * (((k + 1)! : ℕ) : B) =
      ((n + 1 : ℕ) : B) * ((n.descFactorial k : ℕ) : B) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, h]
  rw [hjy]
  linear_combination (a ^ (n + 1 - (k + 1)) * y) * h'

end Ring

section Monomial

variable {B : Type} [CommRing B] {σ : Type}

theorem prod_pow_sub_prod_pow (p : ℕ) (hp : p.Prime)
    (hu : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B)) (J : Ideal B)
    (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) (z z' : σ → B) (hz : ∀ i, z i - z' i ∈ J)
    (α : σ → ℕ) (s : Finset σ) :
    ∃ b : σ → B, (∀ i, b i ∈ J) ∧
      ∏ i ∈ s, z i ^ α i - ∏ i ∈ s, z' i ^ α i = ∑ i ∈ s, (α i : B) * b i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun _ => J.zero_mem, by simp⟩
  | insert i s hi ih =>
    obtain ⟨b, hb, e⟩ := ih
    obtain ⟨y, hy, ey⟩ := add_pow_sub_pow p hp hu J hJ (z' i) (z i - z' i) (hz i) (α i)
    have hzz : z' i + (z i - z' i) = z i := by ring
    rw [hzz] at ey
    refine ⟨Function.update (fun k => z' i ^ α i * b k) i (y * ∏ k ∈ s, z k ^ α k), ?_, ?_⟩
    · intro k
      by_cases hk : k = i
      · subst hk
        rw [Function.update_self]
        exact J.mul_mem_right _ hy
      · rw [Function.update_of_ne hk]
        exact J.mul_mem_left _ (hb k)
    · rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi, Function.update_self]
      have h1 : ∑ k ∈ s, (α k : B) *
          Function.update (fun k => z' i ^ α i * b k) i (y * ∏ k ∈ s, z k ^ α k) k =
          z' i ^ α i * ∑ k ∈ s, (α k : B) * b k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Function.update_of_ne (by rintro rfl; exact hi hk)]
        ring
      rw [h1]
      linear_combination (∏ k ∈ s, z k ^ α k) * ey + z' i ^ α i * e

theorem sum_eq_map_mem {Q : Type} [CommRing Q] [Algebra B Q] {ι : Type} (s : Finset ι)
    (J : Ideal B) (f : ι → Q) (h : ∀ i ∈ s, ∃ b ∈ J, f i = algebraMap B Q b) :
    ∃ b ∈ J, ∑ i ∈ s, f i = algebraMap B Q b := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, J.zero_mem, by simp⟩
  | insert i s hi ih =>
    obtain ⟨y, hy, e⟩ := h i (Finset.mem_insert_self i s)
    obtain ⟨y', hy', e'⟩ := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
    exact ⟨y + y', J.add_mem hy hy', by rw [Finset.sum_insert hi, e, e', map_add (f := _)]⟩

variable [Fintype σ] {Q : Type} [CommRing Q] [Algebra B Q]

theorem monomial_val_sub (p : ℕ) (hp : p.Prime)
    (hu : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B)) (J : Ideal B)
    (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) (z z' : σ → B) (hz : ∀ i, z i - z' i ∈ J)
    (α : σ →₀ ℕ) (a : Q) (ha : ∀ i, ∃ c : B, (α i : Q) * a = algebraMap B Q c) :
    ∃ b ∈ J, a * (∏ i, algebraMap B Q (z i) ^ α i) - a * ∏ i, algebraMap B Q (z' i) ^ α i =
      algebraMap B Q b := by
  choose c hc using ha
  obtain ⟨b, hb, e⟩ := prod_pow_sub_prod_pow p hp hu J hJ z z' hz α Finset.univ
  refine ⟨∑ i, b i * c i, J.sum_mem (fun i _ => J.mul_mem_right _ (hb i)), ?_⟩
  have e' := congrArg (algebraMap B Q) e
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_prod, map_pow, map_sum, map_mul, map_natCast] at e'
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← mul_sub, e', Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← hc i]
  ring

theorem eval_sub_eval (p : ℕ) (hp : p.Prime)
    (hu : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B)) (J : Ideal B)
    (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) (z z' : σ → B) (hz : ∀ i, z i - z' i ∈ J)
    (P : MvPolynomial σ Q)
    (hP : ∀ (α : σ →₀ ℕ) i, ∃ c : B, (α i : Q) * P.coeff α = algebraMap B Q c) :
    ∃ b ∈ J, MvPolynomial.eval (fun i => algebraMap B Q (z i)) P -
      MvPolynomial.eval (fun i => algebraMap B Q (z' i)) P = algebraMap B Q b := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [P.as_sum, map_sum, map_sum, ← Finset.sum_sub_distrib]
  apply sum_eq_map_mem
  intro v _
  rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  exact monomial_val_sub p hp hu J hJ z z' hz v (P.coeff v) (hP v)

end Monomial

theorem hasVal_sub_mem : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q]
    [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ]
    [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ J : Ideal B,
    (∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) → ∀ (z' : σ → B) (f : MvPowerSeries σ Q) (q q' : Q),
    (∀ i, z i - z' i ∈ J) → DIn (⊤ : Ideal B) f → HasVal p z f q → HasVal p z' f q' →
    ∀ m : ℕ, ∃ b ∈ J, ∃ b' : B, q - q' = algebraMap B Q (b + p ^ m * b') := by
  intro p hpf B O Q _ _ _ _ θ hF σ _ _ z _ J hJ z' f q q' hzz hD hv hv' m
  have hp : p.Prime := hpf.out
  obtain ⟨N1, h1⟩ := hv m
  obtain ⟨N2, h2⟩ := hv' m
  obtain ⟨b1, e1⟩ := h1 (max N1 N2) (le_max_left _ _)
  obtain ⟨b2, e2⟩ := h2 (max N1 N2) (le_max_right _ _)
  have hP : ∀ (α : σ →₀ ℕ) i, ∃ c : B, (α i : Q) *
      (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => max N1 N2) f).coeff α =
        algebraMap B Q c := by
    intro α i
    rw [coeff_trunc']
    split_ifs
    · obtain ⟨c, -, hc⟩ := hD α i
      exact ⟨c, hc⟩
    · exact ⟨0, by simp⟩
  obtain ⟨b, hb, e⟩ := eval_sub_eval p hp hF.unit_coprime J hJ z z' hzz _ hP
  refine ⟨b, hb, b1 - b2, ?_⟩
  simp only [map_add (f := _), map_mul, map_sub, map_pow, map_natCast] at e1 e2 ⊢
  linear_combination e1 - e2 + e

end GlobalTheory.HasValCong
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueSubMemPdIdealStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasPAdicPowerSeriesValue_sub_mem_pd_ideal : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ J : Ideal B, (∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) → ∀ (z' : σ → B) (f : MvPowerSeries σ Q) (q q' : Q), (∀ i, z i - z' i ∈ J) → DIn (⊤ : Ideal B) f → HasVal p z f q → HasVal p z' f q' → ∀ m : ℕ, ∃ b ∈ J, ∃ b' : B, q - q' = algebraMap B Q (b + p ^ m * b') := by
  first | exact @GlobalTheory.HasValCong.hasVal_sub_mem | exact GlobalTheory.HasValCong.hasVal_sub_mem | (intros; apply GlobalTheory.HasValCong.hasVal_sub_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCocommOfSurjective
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup.KerGrp


set_option autoImplicit false in
open CategoryTheory TensorProduct Coalgebra Bialgebra in
theorem _root_.GlobalTheory.PDivGroup.KerGrp.isCocomm_of_surjective {k A B : Type} [CommRing k] [CommRing A] [CommRing B]
    [Bialgebra k A] [Bialgebra k B] [IsCocomm k A] (f : A →ₐc[k] B)
    (hf : Function.Surjective f) : IsCocomm k B := by
  constructor
  ext b
  obtain ⟨a, rfl⟩ := hf b
  have hcomm : ∀ y : A ⊗[k] A, TensorProduct.comm k B B (TensorProduct.map (f : A →ₗ[k] B)
      (f : A →ₗ[k] B) y) = TensorProduct.map (f : A →ₗ[k] B) (f : A →ₗ[k] B)
      (TensorProduct.comm k A A y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hA : TensorProduct.comm k A A (comul a) = comul a :=
    LinearMap.congr_fun (Coalgebra.comm_comp_comul (R := k) (A := A)) a
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [← CoalgHomClass.map_comp_comul_apply, hcomm, hA]


set_option autoImplicit false in
open CategoryTheory TensorProduct Coalgebra Bialgebra in
theorem _root_.GlobalTheory.PDivGroup.KerGrp.map_res_kerIdeal {p : ℕ} {k : Type} [CommRing k] {G H : _root_.GlobalTheory.PDivGroup p k} (u : G ⟶ H)
    (n : ℕ) : Ideal.map (G.res n : G.A (n + 1) →ₐ[k] G.A n) (_root_.GlobalTheory.PDiv.kerIdeal (u.app (n + 1))) =
      _root_.GlobalTheory.PDiv.kerIdeal (u.app n) := by
  have hc := congrArg (fun g : H.A (n + 1) →ₐc[k] G.A n =>
    ((g : H.A (n + 1) →ₐ[k] G.A n) :
      H.A (n + 1) →+* G.A n))
    (_root_.GlobalTheory.PDivGroup.Hom.comm u n)
  have hres : Ideal.map (H.res n : H.A (n + 1) →ₐ[k]
      H.A n) (_root_.GlobalTheory.PDiv.augIdeal k (H.A (n + 1))) =
      _root_.GlobalTheory.PDiv.augIdeal k (H.A n) :=
    _root_.GlobalTheory.PDiv.kerIdeal_of_surjective (H.10 n)
  unfold _root_.GlobalTheory.PDiv.kerIdeal
  change Ideal.map ((G.res n : G.A (n + 1) →ₐ[k]
      G.A n) : G.A (n + 1) →+* G.A n)
      (Ideal.map ((u.app (n + 1) : H.A (n + 1) →ₐ[k]
        G.A (n + 1)) : H.A (n + 1) →+* G.A (n + 1))
        (_root_.GlobalTheory.PDiv.augIdeal k (H.A (n + 1)))) =
    Ideal.map ((u.app n : H.A n →ₐ[k] G.A n) :
      H.A n →+* G.A n)
      (_root_.GlobalTheory.PDiv.augIdeal k (H.A n))
  rw [Ideal.map_map]

  rw [show ((G.res n : G.A (n + 1) →ₐ[k] G.A n) :
      G.A (n + 1) →+* G.A n).comp
      ((u.app (n + 1) : H.A (n + 1) →ₐ[k] G.A (n + 1)) :
        H.A (n + 1) →+* G.A (n + 1)) =
      ((u.app n : H.A n →ₐ[k] G.A n) :
        H.A n →+* G.A n).comp
      ((H.res n : H.A (n + 1) →ₐ[k] H.A n) :
        H.A (n + 1) →+* H.A n) from hc, ← Ideal.map_map]
  rw [← hres]
  rfl

theorem exists_of_family {p : ℕ} {k : Type} [Field k] (G : PDivGroup p k)
    (u : G ⟶ G) (h₀ : ℕ) (B : ℕ → Type) [∀ n, CommRing (B n)] [∀ n, HopfAlgebra k (B n)]
    (π : ∀ n, G.A n →ₐc[k] B n) (hπ : ∀ n, Function.Surjective (π n))
    (hk : ∀ n, RingHom.ker (π n) = kerIdeal (u.app n))
    (h : ∀ n : ℕ, Module.finrank k (B n) = p ^ (n * h₀)) :
    ∃ (K : PDivGroup p k) (i : K ⟶ G), ∀ n : ℕ, Function.Surjective (i.app n) ∧
      RingHom.ker (i.app n) = kerIdeal (u.app n) := by
  haveI : ∀ n, IsCocomm k (B n) := fun n => isCocomm_of_surjective (π n) (hπ n)
  have hle : ∀ n, RingHom.ker (π (n + 1)) ≤ RingHom.ker ((π n).comp (G.res n)) := fun n a ha => by
    have : G.res n a ∈ RingHom.ker (π n) := by
      rw [hk, ← map_res_kerIdeal]
      rw [hk] at ha
      exact Ideal.mem_map_of_mem (G.res n : G.A (n + 1) →ₐ[k] G.A n) ha
    exact this
  let r := fun n => liftSurj (π (n + 1)) (hπ (n + 1)) ((π n).comp (G.res n)) (hle n)
  have hr : ∀ n a, r n (π (n + 1) a) = π n (G.res n a) := fun n a => liftSurj_apply ..
  let K : PDivGroup p k :=
    { height := h₀
      A := B
      finite := fun n => Module.Finite.of_surjective (π n : G.A n →ₗ[k] B n) (hπ n)
      rank_eq := fun n q => by rw [Module.rankAtStalk_eq_finrank_of_free, h]; rfl
      res := r
      res_surjective := fun n b => by
        obtain ⟨c, rfl⟩ := hπ n b
        obtain ⟨a, rfl⟩ := G.res_surjective n c
        exact ⟨_, hr n a⟩
      ker_res := fun n => by
        rw [← map_torsionIdeal (hπ (n + 1)), ← G.ker_res]
        refine le_antisymm (fun b hb => ?_) (Ideal.map_le_iff_le_comap.2 fun a ha => ?_)
        · obtain ⟨a, rfl⟩ := hπ _ b
          have h1 : G.res n a ∈ RingHom.ker (π n) := (hr n a).symm.trans hb
          rw [hk, ← map_res_kerIdeal] at h1
          obtain ⟨c, hc, e⟩ := (Ideal.mem_map_iff_of_surjective
            (G.res n : G.A (n + 1) →ₐ[k] G.A n) (G.res_surjective n)).1 h1
          rw [← hk] at hc
          have hc' : π (n + 1) c = 0 := hc
          have e' : G.res n c = G.res n a := e
          have h2 : a - c ∈ RingHom.ker (G.res n) := by
            rw [RingHom.mem_ker, map_sub, e', sub_self]
          have h3 : π (n + 1) a = π (n + 1) (a - c) := by rw [map_sub, hc', sub_zero]
          rw [h3]
          exact Ideal.mem_map_of_mem (π (n + 1) : G.A (n + 1) →ₐ[k] B (n + 1)) h2
        · have ha' : G.res n a = 0 := ha
          change r n (π (n + 1) a) = 0
          rw [hr, ha', map_zero] }
  exact ⟨K, ⟨π, fun n => BialgHom.ext fun a => hr n a⟩, fun n => ⟨hπ n, hk n⟩⟩


set_option autoImplicit false in
open CategoryTheory TensorProduct Coalgebra Bialgebra in
theorem _root_.GlobalTheory.PDivGroup.KerGrp.exists_kernel (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (G : _root_.GlobalTheory.PDivGroup p k)
    (u : G ⟶ G) (h₀ : ℕ)
    (h : ∀ n : ℕ, Module.finrank k (G.A n ⧸ _root_.GlobalTheory.PDiv.kerIdeal (u.app n)) = p ^ (n * h₀)) :
    ∃ (K : _root_.GlobalTheory.PDivGroup p k) (i : K ⟶ G), ∀ n : ℕ, Function.Surjective (i.app n) ∧
      RingHom.ker (i.app n) = _root_.GlobalTheory.PDiv.kerIdeal (u.app n) := by
  classical
  obtain ⟨I, hIdef⟩ : ∃ I : ∀ n, Ideal (G.A n),
      ∀ n, I n = _root_.GlobalTheory.PDiv.kerIdeal (u.app n) := ⟨_, fun n => rfl⟩
  haveI hH : ∀ n, (I n).IsHopfIdeal k := fun n => by
    rw [hIdef]
    exact _root_.GlobalTheory.T.isHopfIdeal_kerIdeal_of_bialgHom' k _ _ (u.app n)
  have hq : ∀ n, Function.Surjective (Bialgebra.Quotient.mkBialgHom (R := k) (I n)) := by
    intro n x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨a, by simp⟩
  haveI hcoc : ∀ n, IsCocomm k (G.A n ⧸ I n) := fun n =>
    _root_.GlobalTheory.PDivGroup.KerGrp.isCocomm_of_surjective _ (hq n)
  have hmapI : ∀ n, Ideal.map (G.res n : G.A (n + 1) →ₐ[k]
      G.A n) (I (n + 1)) = I n := by
    intro n
    rw [hIdef, hIdef]
    exact _root_.GlobalTheory.PDivGroup.KerGrp.map_res_kerIdeal u n
  have hle : ∀ n, I (n + 1) ≤ (I n).comap (G.res n :
      G.A (n + 1) →ₐ[k] G.A n) := fun n =>
    Ideal.map_le_iff_le_comap.1 (hmapI n).le
  let φ : ∀ n, (G.A (n + 1) ⧸ I (n + 1)) →ₐ[k] (G.A n ⧸ I n) :=
    fun n => Ideal.quotientMapₐ (I n) (G.res n :
      G.A (n + 1) →ₐ[k] G.A n) (hle n)
  have hφ : ∀ n a, φ n (Ideal.Quotient.mk (I (n + 1)) a) =
      Ideal.Quotient.mk (I n) (G.res n a) := fun n a => rfl
  have hcounit : ∀ n, (Bialgebra.counitAlgHom k _).comp (φ n) =
      Bialgebra.counitAlgHom k (G.A (n + 1) ⧸ I (n + 1)) := by
    intro n
    refine AlgHom.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change CoalgebraStruct.counit (R := k) (Ideal.Quotient.mk (I n) (G.res n a)) =
      CoalgebraStruct.counit (R := k) (Ideal.Quotient.mk (I (n + 1)) a)
    rw [← Bialgebra.Quotient.mkBialgHom_apply (R := k), ← Bialgebra.Quotient.mkBialgHom_apply (R := k),
      CoalgHomClass.counit_comp_apply, CoalgHomClass.counit_comp_apply,
      CoalgHomClass.counit_comp_apply]
  have hcomul : ∀ n, (Algebra.TensorProduct.map (φ n) (φ n)).comp (Bialgebra.comulAlgHom k _) =
      (Bialgebra.comulAlgHom k _).comp (φ n) := by
    intro n
    refine AlgHom.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Algebra.TensorProduct.map (φ n) (φ n)
        (CoalgebraStruct.comul (R := k) (Ideal.Quotient.mk (I (n + 1)) a)) =
      CoalgebraStruct.comul (R := k) (Ideal.Quotient.mk (I n) (G.res n a))
    rw [← Bialgebra.Quotient.mkBialgHom_apply (R := k) (I (n + 1)),
      ← Bialgebra.Quotient.mkBialgHom_apply (R := k) (I n),
      ← CoalgHomClass.map_comp_comul_apply (Bialgebra.Quotient.mkBialgHom (R := k) (I (n + 1))),
      ← CoalgHomClass.map_comp_comul_apply (Bialgebra.Quotient.mkBialgHom (R := k) (I n)),
      ← CoalgHomClass.map_comp_comul_apply (G.res n)]
    generalize CoalgebraStruct.comul (R := k) a = y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hφ]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  let r : ∀ n, (G.A (n + 1) ⧸ I (n + 1)) →ₐc[k] (G.A n ⧸ I n) :=
    fun n => BialgHom.ofAlgHom (φ n) (hcounit n) (hcomul n)
  have hr : ∀ n a, r n (Ideal.Quotient.mk (I (n + 1)) a) =
      Ideal.Quotient.mk (I n) (G.res n a) := fun n a => rfl
  have hrs : ∀ n, Function.Surjective (r n) := by
    intro n x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := G.10 n a
    exact ⟨Ideal.Quotient.mk _ b, hr n b⟩
  have hker : ∀ n, RingHom.ker (r n) =
      _root_.GlobalTheory.PDiv.torsionIdeal (R := k) (A := G.A (n + 1) ⧸ I (n + 1)) (p ^ n) := by
    intro n
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, hr, Ideal.Quotient.eq_zero_iff_mem,
      ← _root_.GlobalTheory.PDiv.map_torsionIdeal (hq (n + 1))]
    change _ ↔ Ideal.Quotient.mk (I (n + 1)) a ∈ Ideal.map (Ideal.Quotient.mk (I (n + 1))) _
    rw [Ideal.mem_quotient_iff_mem_sup, ← G.ker_res n]
    change a ∈ Ideal.comap (G.res n : G.A (n + 1) →ₐ[k]
      G.A n) (I n) ↔ _
    rw [← hmapI n, Ideal.comap_map_of_surjective (G.res n :
      G.A (n + 1) →ₐ[k] G.A n) (G.10 n),
      ← RingHom.ker_eq_comap_bot, sup_comm]
    all_goals rfl
  have hkq : ∀ n, RingHom.ker (Bialgebra.Quotient.mkBialgHom (R := k) (I n)) =
      _root_.GlobalTheory.PDiv.kerIdeal (u.app n) := by
    intro n
    rw [← hIdef]
    ext x
    simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  refine ⟨_root_.GlobalTheory.PDivGroup.mk h₀ (fun n => G.A n ⧸ I n)
    (commRing := fun n => inferInstance) (hopf := fun n => inferInstance) (cocomm := hcoc)
    (finite := fun n => Module.Finite.of_surjective (Ideal.Quotient.mkₐ k (I n)).toLinearMap
      Ideal.Quotient.mk_surjective)
    (projective := fun n => inferInstance) (fun n q => ?_) r hrs hker,
    _root_.GlobalTheory.PDivGroup.Hom.mk (fun n => Bialgebra.Quotient.mkBialgHom (R := k) (I n))
      (fun n => ?_), fun n => ⟨hq n, ?_⟩⟩
  · rw [Module.rankAtStalk_eq_finrank_of_free]
    have hn := h n
    rw [← hIdef] at hn
    simpa using hn
  · exact DFunLike.ext _ _ fun a => rfl
  · exact hkq n

end GlobalTheory.PDivGroup.KerGrp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualBasisCoordMemMaximalIdealOfForallApply
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualBasisCoordMemMaximalIdealOfForallApply
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem dualBasis_coord_mem_maximalIdeal : ∀ (O : Type) [CommRing O] [IsLocalRing O] (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M] [Module.Projective O M] (k : ℕ) (lb : Module.Basis (Fin k) O (Module.Dual O M)) (l : Module.Dual O M), (∀ w, l w ∈ IsLocalRing.maximalIdeal O) → ∀ j, lb.repr l j ∈ IsLocalRing.maximalIdeal O := by
  intro O _ _ M _ _ _ _ k lb l hl j
  haveI : Module.Free O M := Module.free_of_flat_of_isLocalRing
  let ε := Module.Free.chooseBasis O M
  have hsum : l = ∑ i, l (ε i) • ε.dualBasis i := by
    refine ε.ext fun a => ?_
    simp [Module.Basis.dualBasis_apply_self, Finset.sum_apply, LinearMap.sum_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum]
  simp only [Finset.sum_apply', map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hl _)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualBasisCoordMemMaximalIdealOfForallApplyStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualBasis_coord_mem_maximalIdeal_of_forall_apply : ∀ (O : Type) [CommRing O] [IsLocalRing O] (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M] [Module.Projective O M] (k : ℕ) (lb : Module.Basis (Fin k) O (Module.Dual O M)) (l : Module.Dual O M), (∀ w, l w ∈ IsLocalRing.maximalIdeal O) → ∀ j, lb.repr l j ∈ IsLocalRing.maximalIdeal O := by
  first | exact @GlobalTheory.dualBasis_coord_mem_maximalIdeal | exact GlobalTheory.dualBasis_coord_mem_maximalIdeal | (intros; apply GlobalTheory.dualBasis_coord_mem_maximalIdeal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffCartierComapOfIsIsoRestrictOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffCartierComapOfIsIsoRestrictOpen
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory

theorem effCartier_comap_of_isIso_restrict : ∀ {Y Y' : Scheme.{0}} (s : Y' ⟶ Y) (I : Y.IdealSheafData) (U : Y.Opens), IsIso (s ∣_ U) → FinalTheorems.EffCartier (I.comap s) → FinalTheorems.EffCartier (I.comap U.ι) := by
  intro Y Y' s I U hiso hE
  have h1 : FinalTheorems.EffCartier ((I.comap s).comap (s ⁻¹ᵁ U).ι) :=
    effCartier_comap_of_isOpenImmersion' _ _ hE
  have h2 := effCartier_comap_of_isOpenImmersion' _ (inv (s ∣_ U)) h1
  have key : inv (s ∣_ U) ≫ (s ⁻¹ᵁ U).ι ≫ s = U.ι := by
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, Category.assoc, key] at h2
  exact h2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffCartierComapOfIsIsoRestrictOpenStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.effCartier_comap_of_isIso_restrict_open : ∀ {Y Y' : Scheme.{0}} (s : Y' ⟶ Y) (I : Y.IdealSheafData) (U : Y.Opens), IsIso (s ∣_ U) → FinalTheorems.EffCartier (I.comap s) → FinalTheorems.EffCartier (I.comap U.ι) := by
  first | exact @GlobalTheory.effCartier_comap_of_isIso_restrict | exact GlobalTheory.effCartier_comap_of_isIso_restrict | (intros; apply GlobalTheory.effCartier_comap_of_isIso_restrict <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneTmulQuotReduction
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv

theorem one_tmul_quot_reduction :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (I : Ideal O),
      (∀ y : (O ⧸ I) ⊗[O] M, ∃ b : M, y = 1 ⊗ₜ b) ∧
      (∀ b : M, (1 : O ⧸ I) ⊗ₜ[O] b = 0 ↔ b ∈ I • (⊤ : Submodule O M)) ∧
      ∀ (a : O) (b : M), b ∈ Ideal.span {a} • (⊤ : Submodule O M) ↔ ∃ z, b = a • z := by
  intro O M _ _ _ I
  refine ⟨?_, ?_, ?_⟩
  · intro y
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective (I • (⊤ : Submodule O M))
      (TensorProduct.quotTensorEquivQuotSMul M I y)
    refine ⟨b, ?_⟩
    rw [← TensorProduct.quotTensorEquivQuotSMul_symm_mk I b, hb, LinearEquiv.symm_apply_apply]
  · intro b
    rw [← (TensorProduct.quotTensorEquivQuotSMul M I).map_eq_zero_iff,
      TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]
  · intro a b
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨z, -, hz⟩
      exact ⟨z, hz.symm⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, Submodule.mem_top, rfl⟩

end GlobalTheory.PDiv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstMapToFractionsMemSubmodule
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstMapToFractionsMemSubmodule
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.SubstSub

theorem coeff_subst_up_mem : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (σ τ : Type) [Fintype σ] (S : Submodule B Q) (f : MvPowerSeries σ Q) (u : σ → MvPowerSeries τ B), (∀ i, constantCoeff (u i) = 0) → (∀ α, coeff α f ∈ S) → ∀ β, coeff β (subst (up Q u) f) ∈ S := by
  intro B Q _ _ _ σ τ _ S f u hu hf β
  have hc : ∀ i, constantCoeff (up Q u i) = 0 := fun i => by
    simp only [up]
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hu, map_zero]
  have ha : HasSubst (up Q u) := hasSubst_of_constantCoeff_zero hc
  rw [coeff_subst ha]
  refine finsum_induction (fun x => x ∈ S) S.zero_mem (fun x y hx hy => S.add_mem hx hy) ?_
  intro d
  have hp : (d.prod fun s e => (up Q u s) ^ e) = map (algebraMap B Q) (d.prod fun s e => (u s) ^ e) := by
    simp only [up, Finsupp.prod, map_prod, map_pow]
  simp only [hp, coeff_map, smul_eq_mul]
  rw [mul_comm, ← Algebra.smul_def]
  exact S.smul_mem _ (hf d)

end GlobalTheory.SubstSub
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstMapToFractionsMemSubmoduleStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_subst_mapToFractions_mem_submodule : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (σ τ : Type) [Fintype σ] (S : Submodule B Q) (f : MvPowerSeries σ Q) (u : σ → MvPowerSeries τ B), (∀ i, constantCoeff (u i) = 0) → (∀ α, coeff α f ∈ S) → ∀ β, coeff β (subst (up Q u) f) ∈ S := by
  first | exact @GlobalTheory.SubstSub.coeff_subst_up_mem | exact GlobalTheory.SubstSub.coeff_subst_up_mem | (intros; apply GlobalTheory.SubstSub.coeff_subst_up_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSumElimPowerSeriesSwapVariableGroups
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSumElimPowerSeriesSwapVariableGroups
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.SwapCoeff

theorem swap_eq_rename (R : Type) [CommRing R] (d : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) R) :
    swap c = rename (Equiv.sumComm (Fin d) (Fin d)) c := by
  rw [rename_eq_subst]
  unfold swap at2
  congr 1
  funext s
  rcases s with i | i <;> rfl

theorem coeff_swap : ∀ (R : Type) [CommRing R] (d : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a e : Fin d →₀ ℕ), coeff (Finsupp.sumElim a e) (swap c) = coeff (Finsupp.sumElim e a) c := by
  intro R _ d c a e
  have h := coeff_embDomain_rename (Equiv.sumComm (Fin d) (Fin d)).toEmbedding c (Finsupp.sumElim e a)
  have hinj : Function.Injective (Equiv.sumComm (Fin d) (Fin d)) := (Equiv.sumComm _ _).injective
  have hE : Finsupp.embDomain (Equiv.sumComm (Fin d) (Fin d)).toEmbedding (Finsupp.sumElim e a) =
      Finsupp.sumElim a e := by
    rw [Finsupp.embDomain_eq_mapDomain]
    ext x
    rcases x with i | i
    · have := Finsupp.mapDomain_apply_of_injective hinj (Finsupp.sumElim e a) (Sum.inr i)
      simpa using this
    · have := Finsupp.mapDomain_apply_of_injective hinj (Finsupp.sumElim e a) (Sum.inl i)
      simpa using this
  rw [hE] at h
  rw [swap_eq_rename]
  exact h

end GlobalTheory.SwapCoeff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSumElimPowerSeriesSwapVariableGroupsStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_sumElim_powerSeriesSwapVariableGroups : ∀ (R : Type) [CommRing R] (d : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a e : Fin d →₀ ℕ), coeff (Finsupp.sumElim a e) (swap c) = coeff (Finsupp.sumElim e a) c := by
  first | exact @GlobalTheory.SwapCoeff.coeff_swap | exact GlobalTheory.SwapCoeff.coeff_swap | (intros; apply GlobalTheory.SwapCoeff.coeff_swap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSubFiniteFree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Hecke

theorem heckeSub_finite_free : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (k N : ℕ), 0 < k → 0 < N → k.Coprime p → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), Finite (GlobalTheory.UPel.HT.Hecke.heckeSub o g N) ∧ ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (h : 𝟙_ (Over S) ⟶ o.A), h ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N → toUnit (Over.mk x) ≫ h = 1 → h = 1 := by
  intro p _ D R _ b g k N hk hN hkp hNp S s o
  refine ⟨?_, ?_⟩
  · haveI := D.finLa
    let K : Submodule ℤ D.La := LinearMap.range ((k : ℤ) • LinearMap.id)
    haveI : Finite (D.La ⧸ K) := by
      apply Module.finite_of_fg_torsion
      intro q
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective K q
      refine ⟨⟨(k : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hk.ne')⟩, ?_⟩
      show (k : ℤ) • (Submodule.Quotient.mk y : D.La ⧸ K) = 0
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact ⟨y, by simp⟩
    let σ := Function.surjInv (Submodule.Quotient.mk_surjective K)
    refine Finite.of_surjective (fun q : D.La ⧸ K => (⟨o.eta (N • g (σ q)), mem_heckeSub o g N _⟩ : heckeSub o g N)) ?_
    rintro ⟨h, x, rfl⟩
    refine ⟨Submodule.Quotient.mk x, Subtype.ext ?_⟩
    have e : Submodule.Quotient.mk (σ (Submodule.Quotient.mk x)) = (Submodule.Quotient.mk x : D.La ⧸ K) :=
      Function.surjInv_eq _ _
    rw [Submodule.Quotient.eq] at e
    obtain ⟨z, hz⟩ := e
    have hz' : σ (Submodule.Quotient.mk x) = x + k • z := by
      simp only [LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul] at hz
      rw [hz]; abel
    show o.eta (N • g (σ (Submodule.Quotient.mk x))) = o.eta (N • g x)
    rw [hz', map_add (f := _), map_nsmul, smul_add, smul_smul, o.eta_add, o.eta_ker, _root_.mul_one]
  · intro κ _ _ x h hh h1
    obtain ⟨x0, rfl⟩ := hh
    have hβ : x ≫ s = spMap (Spec.preimage (x ≫ s)).hom := (Spec.map_preimage _).symm
    obtain ⟨I, hI⟩ := o.geom κ x _ hβ
    have h2 : I.ev (N * k) (N • g x0) = 1 := by rw [← hI]; exact h1
    obtain ⟨y, hy⟩ := (I.ker (N * k) (Nat.mul_pos hN hk) (Nat.Coprime.mul_left hNp hkp) _).1 h2
    rw [hy, o.eta_ker]

end GlobalTheory.UPel.HT.Hecke
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealLatticeHasNonrealMultiplier
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealLatticeHasNonrealMultiplier
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.LatOfMult

theorem main : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (Λ : PeriodPair), 0 < d → δ ^ 2 = -(d : K) → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 𝔞 Λ → (∀ a : 𝓞 K, MulStable Λ (ι a)) ∧ MulStable Λ (ι δ) ∧ (ι δ).im ≠ 0 ∧ IsIntegral ℤ δ := by
  intro K _ _ d δ ι 𝔞 Λ hd hδ hL
  have hmem : ∀ z : ℂ, z ∈ Λ.lattice ↔ ∃ x ∈ (𝔞 : Set K), ι x = z := by
    intro z
    have := congrArg (fun S : Set ℂ => z ∈ S) hL
    simpa using this
  have hstab : ∀ a : 𝓞 K, MulStable Λ (ι a) := by
    intro a ω hω
    obtain ⟨x, hx, rfl⟩ := (hmem ω).1 hω
    refine (hmem _).2 ⟨(a : K) * x, ?_, by simp⟩
    have h1 : a • x ∈ (𝔞 : Submodule (𝓞 K) K) := Submodule.smul_mem _ a hx
    rwa [Algebra.smul_def] at h1
  have hint : IsIntegral ℤ δ := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_add_C _ (by norm_num)
    · simp [hδ]
  refine ⟨hstab, ?_, ?_, hint⟩
  · exact hstab ⟨δ, hint⟩
  · intro him
    have h2 : (ι δ) ^ 2 = -(d : ℂ) := by rw [← map_pow, hδ]; simp
    have h3 := congrArg Complex.re h2
    simp [pow_two, Complex.mul_re, him] at h3
    have : (0:ℝ) < d := by exact_mod_cast hd
    nlinarith [sq_nonneg (ι δ).re]

end GlobalTheory.LatOfMult
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealLatticeHasNonrealMultiplierStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionalIdealLattice_has_nonreal_multiplier : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (Λ : PeriodPair), 0 < d → δ ^ 2 = -(d : K) → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 𝔞 Λ → (∀ a : 𝓞 K, MulStable Λ (ι a)) ∧ MulStable Λ (ι δ) ∧ (ι δ).im ≠ 0 ∧ IsIntegral ℤ δ := by
  first | exact @GlobalTheory.LatOfMult.main | exact GlobalTheory.LatOfMult.main | (intros; apply GlobalTheory.LatOfMult.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightDegreeLeOfHomogeneousFockWeightVector
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightDegreeLeOfHomogeneousFockWeightVector
noncomputable section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg


open GlobalTheory.JointHarm in
theorem degW_le_of_isSide {σ : Type} {p q r s : ℕ} {e : Ln p q r s → σ}
    {act : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)} [Fintype σ]
    (he : Function.Bijective e) (h : IsSide e act) {d : ℕ}
    {μ : Ix p q → ℚ} {P : MvPolynomial σ ℂ} (hd : P ∈ homog σ d) (hP0 : P ≠ 0)
    (hP : P ∈ wtSub act μ) : degW (cPair r s) μ ≤ d := by
  obtain ⟨m, hm⟩ := support_nonempty.2 hP0
  obtain ⟨h1, h2⟩ := (h.mem_wtSub μ P).1 hP
  have e1 : m.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hd (mem_support_iff.1 hm)
  rw [← e1, degree_eq_blocks he, degW, Fintype.sum_sum_type, Nat.cast_add, Nat.cast_sum,
    Nat.cast_sum]
  refine add_le_add (Finset.sum_le_sum fun t _ => ?_) (Finset.sum_le_sum fun t _ => ?_)
  · rw [mixed_weight _ _ (h1 t) hm, Nat.cast_add]
    exact (abs_sub _ _).trans (by simp only [Nat.abs_cast, le_refl])
  · rw [mixed_weight _ _ (h2 t) hm, Nat.cast_add]
    exact (abs_sub _ _).trans (by simp only [Nat.abs_cast, le_refl])

theorem degW_le_of_homog_wtSub : ∀ (p q r s : ℕ),
    (∀ (d : ℕ) (μ : Ix p q → ℚ) (P : Pol p q r s), P ∈ homog (Ix p q × Ix r s) d → P ≠ 0 →
      P ∈ wtSub (fockAct1 p q r s) μ → degW (cPair r s) μ ≤ d) ∧
    (∀ (d : ℕ) (μ : Ix r s → ℚ) (P : Pol p q r s), P ∈ homog (Ix p q × Ix r s) d → P ≠ 0 →
      P ∈ wtSub (fockAct2 p q r s) μ → degW (cPair p q) μ ≤ d) := fun _ _ _ _ =>
  ⟨fun _ _ _ hd h0 hP =>
      degW_le_of_isSide Function.bijective_id GlobalTheory.JointHarm.isSide_one hd h0 hP,
    fun _ _ _ hd h0 hP =>
      degW_le_of_isSide Prod.swap_bijective GlobalTheory.JointHarm.isSide_two hd h0 hP⟩

end GlobalTheory.FockAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightDegreeLeOfHomogeneousFockWeightVectorStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightDegree_le_of_homogeneous_fockWeightVector : ∀ (p q r s : ℕ), (∀ (d : ℕ) (μ : Ix p q → ℚ) (P : Pol p q r s), P ∈ homog (Ix p q × Ix r s) d → P ≠ 0 → P ∈ wtSub (fockAct1 p q r s) μ → degW (cPair r s) μ ≤ d) ∧ (∀ (d : ℕ) (μ : Ix r s → ℚ) (P : Pol p q r s), P ∈ homog (Ix p q × Ix r s) d → P ≠ 0 → P ∈ wtSub (fockAct2 p q r s) μ → degW (cPair p q) μ ≤ d) := by
  first | exact @GlobalTheory.FockAlg.degW_le_of_homog_wtSub | exact GlobalTheory.FockAlg.degW_le_of_homog_wtSub | (intros; apply GlobalTheory.FockAlg.degW_le_of_homog_wtSub <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechOneCoboundaryOfRefinement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechOneCoboundaryOfRefinement
open AlgebraicGeometry CategoryTheory GlobalTheory.KS

namespace GlobalTheory.KS.Refine

theorem isCob_of_refine : ∀ {Y : Scheme.{0}} {I J : Type} (Uc : I → Y.Opens) (c : GlobalTheory.KS.C1 Uc),
    GlobalTheory.KS.IsCoc Uc c → ∀ (V : J → Y.Opens) (σ : J → I), (∀ p, V p ≤ Uc (σ p)) → (⨆ p, V p = ⊤) →
    ∀ (B : ∀ p, Γ(Y, V p)), (∀ p p', GlobalTheory.KS.rsT (c (σ p) (σ p')) (V p ⊓ V p') =
      GlobalTheory.KS.rsT (B p') (V p ⊓ V p') - GlobalTheory.KS.rsT (B p) (V p ⊓ V p')) → GlobalTheory.KS.IsCob Uc c := by
  intro Y I J Uc c hc V σ hV hVt B hB
  have hV' : ∀ p y, y ∈ V p → y ∈ Uc (σ p) := fun p y h => hV p h
  have cov : ∀ O : Y.Opens, O ≤ ⨆ p, O ⊓ V p := by
    intro O x hx
    have : x ∈ ⨆ p, V p := by rw [hVt]; trivial
    obtain ⟨p, hp⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, hx, hp⟩
  have glue : ∀ i, ∃ t : Γ(Y, Uc i), ∀ p, rsT t (Uc i ⊓ V p) =
      rsT (B p) (Uc i ⊓ V p) + rsT (c (σ p) i) (Uc i ⊓ V p) := by
    intro i
    refine exists_rsT_eq (fun p => Uc i ⊓ V p) (fun p => inf_le_left) (cov _) _ fun p p' => ?_
    have h1 := congrArg (fun s => rsT s ((Uc i ⊓ V p) ⊓ (Uc i ⊓ V p'))) (hB p p')
    have h2 := congrArg (fun s => rsT s ((Uc i ⊓ V p) ⊓ (Uc i ⊓ V p'))) (hc (σ p) (σ p') i)
    simp only [rsT_add, rsT_sub] at h1 h2 ⊢
    repeat
      first | rw [rsT_rsT] at h1 | rw [rsT_rsT] at h2 | rw [rsT_rsT]
      all_goals try (intro x hx; try simp only [TopologicalSpace.Opens.mem_inf] at hx ⊢; aesop)
    linear_combination h1 - h2
  choose t ht using glue
  refine ⟨t, fun i j => ?_⟩
  refine eq_of_rsT_eq (fun p => Uc i ⊓ Uc j ⊓ V p) (fun p => inf_le_left) (cov _) _ _ fun p => ?_
  have h1 := congrArg (fun s => rsT s (Uc i ⊓ Uc j ⊓ V p)) (ht i p)
  have h2 := congrArg (fun s => rsT s (Uc i ⊓ Uc j ⊓ V p)) (ht j p)
  have h3 := congrArg (fun s => rsT s (Uc i ⊓ Uc j ⊓ V p)) (hc (σ p) i j)
  simp only [rsT_add, rsT_sub] at h1 h2 h3 ⊢
  repeat
    first | rw [rsT_rsT] at h1 | rw [rsT_rsT] at h2 | rw [rsT_rsT] at h3 | rw [rsT_rsT]
    all_goals try (intro x hx; try simp only [TopologicalSpace.Opens.mem_inf] at hx ⊢; aesop)
  linear_combination h1 - h2 + h3

end GlobalTheory.KS.Refine
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechOneCoboundaryOfRefinementStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCechOneCoboundary_of_refinement : ∀ {Y : Scheme.{0}} {I J : Type} (Uc : I → Y.Opens) (c : GlobalTheory.KS.C1 Uc), GlobalTheory.KS.IsCoc Uc c → ∀ (V : J → Y.Opens) (σ : J → I), (∀ p, V p ≤ Uc (σ p)) → (⨆ p, V p = ⊤) → ∀ (B : ∀ p, Γ(Y, V p)), (∀ p p', GlobalTheory.KS.rsT (c (σ p) (σ p')) (V p ⊓ V p') = GlobalTheory.KS.rsT (B p') (V p ⊓ V p') - GlobalTheory.KS.rsT (B p) (V p ⊓ V p')) → GlobalTheory.KS.IsCob Uc c := by
  first | exact @GlobalTheory.KS.Refine.isCob_of_refine | exact GlobalTheory.KS.Refine.isCob_of_refine | (intros; apply GlobalTheory.KS.Refine.isCob_of_refine <;> assumption)
end
end
