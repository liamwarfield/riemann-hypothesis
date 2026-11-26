module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JTEqAndPowTwelveEqDD
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHopfIdealKerIdealOfBialgHom
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockOperatorsLieRepresentationCommute
public import Formalism.PieriBlockIdeals.PieriColumnMinors.HighestWeightMemWZero
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspidalProductMultiplicity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHopfIdealKerIdealOfBialgHomStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerIdealFinrankEqPowOfIdempotent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKernelIdealMulOfIdempotents
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKernelIdealMulOfIdempotents
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

theorem finrank_quot_kerIdeal_mul_of_idem (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    (G : PDivGroup p k) (u v : G ⟶ G) (huv : u + v = 𝟙 G) (h1 : u ≫ v = 0) (h2 : v ≫ u = 0)
    (n : ℕ) :
    Module.finrank k (G.A n ⧸ kerIdeal (u.app n)) * Module.finrank k (G.A n ⧸ kerIdeal (v.app n)) =
      p ^ (n * G.height) := by
  have hdim : Module.finrank k (G.A n) = p ^ (n * G.height) := by
    obtain ⟨q⟩ : Nonempty (PrimeSpectrum k) := inferInstance
    have h := G.rank_eq n q
    rw [Module.rankAtStalk_eq_finrank_of_free] at h
    simpa using h
  have hker := GlobalTheory.T.ker_app_eq_bialgHomKernelIdeal_of_idempotents p k G u v huv h1 h2 n
  have hord := finrank_eq_ker_mul_range k (G.A n) (G.A n) (u.app n)
  have hr : Module.finrank k (LinearMap.range ((u.app n : G.A n →ₐ[k] G.A n).toLinearMap)) =
      Module.finrank k (G.A n ⧸ kerIdeal (v.app n)) := by
    rw [← hker]
    exact (((u.app n : G.A n →ₐ[k] G.A n).toLinearMap.quotKerEquivRange).symm.finrank_eq).trans rfl
  rw [← hdim, hord, hr]

end GlobalTheory.PDivGroup
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKernelIdealMulOfIdempotentsStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_kernelIdeal_mul_of_idempotents : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (G : PDivGroup p k) (u v : G ⟶ G), u + v = 𝟙 G → u ≫ v = 0 → v ≫ u = 0 → ∀ n : ℕ, Module.finrank k (G.A n ⧸ kerIdeal (u.app n)) * Module.finrank k (G.A n ⧸ kerIdeal (v.app n)) = p ^ (n * G.height) := by
  first | exact @GlobalTheory.PDivGroup.finrank_quot_kerIdeal_mul_of_idem | exact GlobalTheory.PDivGroup.finrank_quot_kerIdeal_mul_of_idem | (intros; apply GlobalTheory.PDivGroup.finrank_quot_kerIdeal_mul_of_idem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKernelIdealSuccLeMulLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKernelIdealSuccLeMulLevels
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

namespace PDiv

theorem finrank_quot_kerIdeal_le_mul {k A B C : Type} [Field k] [CommRing A] [CommRing B]
    [CommRing C] [HopfAlgebra k A] [HopfAlgebra k B] [HopfAlgebra k C] [Module.Finite k A]
    [Module.Finite k B] [Module.Finite k C] (m : B →ₐc[k] A) (r : A →ₐc[k] C)
    (hr : Function.Surjective r) (hk : RingHom.ker (r : A →ₐ[k] C) ≤ kerIdeal m)
    (u : A →ₐc[k] A) (v : B →ₐc[k] B) (w : C →ₐc[k] C) (hm : ∀ b, u (m b) = m (v b))
    (hw : ∀ a, r (u a) = w (r a)) :
    Module.finrank k (A ⧸ kerIdeal u) ≤
      Module.finrank k (C ⧸ kerIdeal w) * Module.finrank k (B ⧸ kerIdeal v) := by
  haveI := GlobalTheory.T.isHopfIdeal_kerIdeal_of_bialgHom' k A A u
  haveI := GlobalTheory.T.isHopfIdeal_kerIdeal_of_bialgHom' k B B v
  let πA : A →ₐc[k] A ⧸ kerIdeal u := Bialgebra.Quotient.mkBialgHom (kerIdeal u)
  let πB : B →ₐc[k] B ⧸ kerIdeal v := Bialgebra.Quotient.mkBialgHom (kerIdeal v)
  have hπA : Function.Surjective πA := Ideal.Quotient.mk_surjective
  have hπB : Function.Surjective πB := Ideal.Quotient.mk_surjective
  have hA : ∀ a, πA (u a) = algebraMap k _ (counit a) :=
    (kerIdeal_le_ker_iff u (πA : A →ₐ[k] A ⧸ kerIdeal u)).1
      fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
  have h1 : kerIdeal v ≤ RingHom.ker (πA.comp m : B →ₐ[k] A ⧸ kerIdeal u) :=
    (kerIdeal_le_ker_iff v _).2 fun b => by
      change πA (m (v b)) = _
      rw [← hm, hA, CoalgHomClass.counit_comp_apply]
  let m' : (B ⧸ kerIdeal v) →ₐc[k] A ⧸ kerIdeal u :=
    liftSurj πB hπB (πA.comp m) fun b hb => h1 (Ideal.Quotient.eq_zero_iff_mem.1 hb)
  have hm' : m'.comp πB = πA.comp m := BialgHom.ext fun b =>
    liftSurj_apply πB hπB (πA.comp m) (fun b hb => h1 (Ideal.Quotient.eq_zero_iff_mem.1 hb)) b
  let q : A →ₐ[k] (A ⧸ kerIdeal u) ⧸ kerIdeal m' :=
    (Ideal.Quotient.mkₐ k (kerIdeal m')).comp (πA : A →ₐ[k] A ⧸ kerIdeal u)
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective.comp hπA
  have h2 : RingHom.ker (r : A →ₐ[k] C) ≤ RingHom.ker q := fun a ha => by
    have h3 : πA a ∈ kerIdeal m' := by
      rw [← kerIdeal_comp_of_surjective m' hπB, hm', kerIdeal_comp]
      exact Ideal.mem_map_of_mem _ (hk ha)
    exact Ideal.Quotient.eq_zero_iff_mem.2 h3
  let q' : C →ₐ[k] (A ⧸ kerIdeal u) ⧸ kerIdeal m' :=
    AlgHom.liftOfSurjective (r : A →ₐ[k] C) hr q h2
  have hq' : ∀ a, q' (r a) = q a := AlgHom.liftOfSurjective_apply (r : A →ₐ[k] C) hr q h2
  have h4 : kerIdeal w ≤ RingHom.ker q' := (kerIdeal_le_ker_iff w q').2 fun c => by
    obtain ⟨a, rfl⟩ := hr c
    rw [← hw, hq', CoalgHomClass.counit_comp_apply]
    change Ideal.Quotient.mkₐ k (kerIdeal m') (πA (u a)) = _
    rw [hA, AlgHom.commutes]
  let q'' : (C ⧸ kerIdeal w) →ₐ[k] (A ⧸ kerIdeal u) ⧸ kerIdeal m' :=
    Ideal.Quotient.liftₐ (kerIdeal w) q' h4
  have hq'' : Function.Surjective q''.toLinearMap := fun x => by
    obtain ⟨a, rfl⟩ := hq x
    exact ⟨Ideal.Quotient.mk _ (r a), hq' a⟩
  rw [finrank_eq_ker_mul_range k _ _ m']
  exact Nat.mul_le_mul (LinearMap.finrank_le_finrank_of_surjective hq'')
    (LinearMap.finrank_range_le _)

end PDiv

namespace PDivGroup

theorem resOne_app {p : ℕ} {R : Type} [CommRing R] {G H : PDivGroup p R} (f : G ⟶ H) (n : ℕ)
    (a : H.A (n + 1)) : G.resOne n (f.app (n + 1) a) = f.app 1 (H.resOne n a) := by
  induction n with
  | zero => simp only [resOne_zero]
  | succ n ih => rw [resOne_succ, resOne_succ, res_app, ih]

theorem finrank_quot_kerIdeal_succ_le (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    (G : PDivGroup p k) (u : G ⟶ G) (n : ℕ) :
    Module.finrank k (G.A (n + 1) ⧸ kerIdeal (u.app (n + 1))) ≤
      Module.finrank k (G.A 1 ⧸ kerIdeal (u.app 1)) *
        Module.finrank k (G.A n ⧸ kerIdeal (u.app n)) :=
  by
    have hker (n : ℕ) : RingHom.ker (G.resOne n : G.A (n + 1) →ₐ[k] G.A 1) =
        torsionIdeal (R := k) (A := G.A (n + 1)) p := by
      induction n with
      | zero =>
        have hid : (G.resOne 0 : G.A 1 →ₐ[k] G.A 1) = AlgHom.id k _ := by
          ext a; exact G.resOne_zero a
        rw [hid]
        refine le_antisymm ?_ ?_
        · intro a ha
          have : a = 0 := ha
          simp [this]
        · refine (torsionIdeal_le_ker_iff p (AlgHom.id k (G.A (0 + 1)))).2 ?_
          simpa using G.pts_pow_self 1 (WithConv.toConv (AlgHom.id k (G.A 1)))
      | succ n ih =>
        have hcomp : (G.resOne (n + 1) : G.A (n + 2) →ₐ[k] G.A 1) =
            (G.resOne n : G.A (n + 1) →ₐ[k] G.A 1).comp
              (G.res (n + 1) : G.A (n + 2) →ₐ[k] G.A (n + 1)) := by
          ext a; exact G.resOne_succ n a
        have hsurj : Function.Surjective (G.res (n + 1) :
            G.A (n + 2) →ₐ[k] G.A (n + 1)) := G.res_surjective (n + 1)
        have hk : RingHom.ker ((G.resOne n : G.A (n + 1) →ₐ[k] G.A 1).comp
            (G.res (n + 1) : G.A (n + 2) →ₐ[k] G.A (n + 1))) =
            Ideal.comap (G.res (n + 1) : G.A (n + 2) →ₐ[k] G.A (n + 1))
              (RingHom.ker (G.resOne n : G.A (n + 1) →ₐ[k] G.A 1)) := by
          ext a; exact Iff.rfl
        rw [hcomp, hk, ih, ← map_torsionIdeal (G.res_surjective (n + 1)) p]
        erw [Ideal.comap_map_of_surjective _ hsurj]
        refine sup_eq_left.mpr ?_
        have h0 : Ideal.comap (G.res (n + 1) : G.A (n + 2) →ₐ[k] G.A (n + 1)) ⊥ =
            torsionIdeal (R := k) (A := G.A (n + 2)) (p ^ (n + 1)) := by
          rw [← G.ker_res (n + 1)]
          ext a; exact Iff.rfl
        rw [h0]
        exact torsionIdeal_le_of_dvd (dvd_pow_self p (Nat.succ_ne_zero n))
    have hmul : kerIdeal (G.mulP n) =
        torsionIdeal (R := k) (A := G.A (n + 1)) p := by
      unfold torsionIdeal
      rw [← G.mulP_comp_res n, kerIdeal_comp_of_surjective _ (G.res_surjective n)]
    exact finrank_quot_kerIdeal_le_mul (G.mulP n) (G.resOne n) (G.resOne_surjective n)
      ((hker n).trans hmul.symm).le _ _ _ (app_mulP u n) (resOne_app u n)

end PDivGroup

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKernelIdealSuccLeMulLevelsStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_kernelIdeal_succ_le_mul_levels : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (G : PDivGroup p k) (u : G ⟶ G) (n : ℕ), Module.finrank k (G.A (n + 1) ⧸ kerIdeal (u.app (n + 1))) ≤ Module.finrank k (G.A 1 ⧸ kerIdeal (u.app 1)) * Module.finrank k (G.A n ⧸ kerIdeal (u.app n)) := by
  first | exact @GlobalTheory.PDivGroup.finrank_quot_kerIdeal_succ_le | exact GlobalTheory.PDivGroup.finrank_quot_kerIdeal_succ_le | (intros; apply GlobalTheory.PDivGroup.finrank_quot_kerIdeal_succ_le <;> assumption)
end
end

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

theorem natSeq_pow_of_mul_eq {p h : ℕ} (hp : p.Prime) (a b : ℕ → ℕ)
    (hab : ∀ n, a n * b n = p ^ (n * h))
    (ha : ∀ n, a (n + 1) ≤ a 1 * a n) (hb : ∀ n, b (n + 1) ≤ b 1 * b n) :
    ∃ s : ℕ, ∀ n, a n = p ^ (n * s) := by
  have h1 : a 1 * b 1 = p ^ h := by simpa using hab 1
  obtain ⟨s, hs, hs'⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro _ h1)
  obtain ⟨t, ht, ht'⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro_left _ h1)
  have h0 : a 0 * b 0 = 1 := by simpa using hab 0
  have ha0 : a 0 = 1 := Nat.eq_one_of_mul_eq_one_right h0
  have hb0 : b 0 = 1 := Nat.eq_one_of_mul_eq_one_left h0
  have hst : s + t = h := by
    rw [hs', ht', ← pow_add] at h1
    exact Nat.pow_right_injective hp.two_le h1
  have hale : ∀ n, a n ≤ p ^ (n * s) := by
    intro n
    induction n with
    | zero => simp [ha0]
    | succ n ih =>
      calc a (n + 1) ≤ a 1 * a n := ha n
        _ ≤ p ^ s * p ^ (n * s) := by rw [hs']; exact Nat.mul_le_mul_left _ ih
        _ = p ^ ((n + 1) * s) := by rw [← pow_add]; ring_nf
  have hble : ∀ n, b n ≤ p ^ (n * t) := by
    intro n
    induction n with
    | zero => simp [hb0]
    | succ n ih =>
      calc b (n + 1) ≤ b 1 * b n := hb n
        _ ≤ p ^ t * p ^ (n * t) := by rw [ht']; exact Nat.mul_le_mul_left _ ih
        _ = p ^ ((n + 1) * t) := by rw [← pow_add]; ring_nf
  refine ⟨s, fun n => ?_⟩
  by_contra hne
  have hlt : a n < p ^ (n * s) := lt_of_le_of_ne (hale n) hne
  have hpos : 0 < p ^ (n * t) := pow_pos hp.pos _
  have key : a n * b n < p ^ (n * s) * p ^ (n * t) :=
    calc a n * b n ≤ a n * p ^ (n * t) := Nat.mul_le_mul_left _ (hble n)
      _ < p ^ (n * s) * p ^ (n * t) := Nat.mul_lt_mul_of_pos_right hlt hpos
  rw [hab n, ← pow_add, ← Nat.mul_add, hst] at key
  exact lt_irrefl _ key

theorem kerIdeal_finrank_eq_pow_of_idempotent : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    (G : PDivGroup p k) (u v : G ⟶ G), u + v = 𝟙 G → u ≫ v = 0 → v ≫ u = 0 →
    ∃ h₀ : ℕ, ∀ n : ℕ, Module.finrank k (G.A n ⧸ kerIdeal (u.app n)) = p ^ (n * h₀) := by
  intro p _ k _ G u v huv h1 h2
  exact natSeq_pow_of_mul_eq (Fact.out : p.Prime)
    (fun n => Module.finrank k (G.A n ⧸ kerIdeal (u.app n)))
    (fun n => Module.finrank k (G.A n ⧸ kerIdeal (v.app n)))
    (GlobalTheory.T.finrank_kernelIdeal_mul_of_idempotents p k G u v huv h1 h2)
    (GlobalTheory.T.finrank_kernelIdeal_succ_le_mul_levels p k G u) (GlobalTheory.T.finrank_kernelIdeal_succ_le_mul_levels p k G v)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTruncationCongrOfPadicContinuousEvalEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTruncationCongrOfPadicContinuousEvalEqZero
open GlobalTheory.QLog

namespace GlobalTheory

theorem evalPoly_eq {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {d : ℕ}
    (x : Fin d → A) (E : MvPowerSeries (Fin d) O →ₐ[O] A) (hX : ∀ i, E (MvPowerSeries.X i) = x i)
    (P : MvPolynomial (Fin d) O) : E (P : MvPowerSeries (Fin d) O) = MvPolynomial.aeval x P := by
  have key : E.comp (MvPolynomial.coeToMvPowerSeries.algHom O) = MvPolynomial.aeval x :=
    MvPolynomial.algHom_ext fun i => by simp [hX]
  have := congrArg (fun F : MvPolynomial (Fin d) O →ₐ[O] A => F P) key
  simpa using this

theorem aeval_monomial_mem_span_pow {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {d : ℕ}
    (x : Fin d → A) (N : ℕ) (α : Fin d →₀ ℕ) (hα : N ≤ α.degree) (c : O) :
    MvPolynomial.aeval x (MvPolynomial.monomial α c) ∈ Ideal.span (Set.range x) ^ N := by
  rw [MvPolynomial.aeval_monomial]
  refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hα ?_)
  rw [Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) _

end GlobalTheory

namespace GlobalTheory

theorem trunc_dec : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (d : ℕ) (x : Fin d → A) (E : MvPowerSeries (Fin d) O →ₐ[O] A), IsEval p x E → ∀ (n N : ℕ) (f : MvPowerSeries (Fin d) O), E f = 0 → ∃ P : MvPolynomial (Fin d) O, (∀ α : Fin d →₀ ℕ, N ≤ α.degree → AddMonoidAlgebra.coeff P α = 0) ∧ (∀ α : Fin d →₀ ℕ, α.degree < N → AddMonoidAlgebra.coeff P α = MvPowerSeries.coeff α f) ∧ MvPolynomial.aeval x P ∈ Ideal.span (Set.range x) ^ N ⊔ Ideal.span {(p : A) ^ n} := by
  intro p O A _ _ _ d x E hE n N f hf
  obtain ⟨hX, hc⟩ := hE
  obtain ⟨M, hM⟩ := hc n
  classical
  set F : Finset (Fin d →₀ ℕ) := Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => max N M) with hF
  have memF : ∀ α : Fin d →₀ ℕ, α.degree < max N M → α ∈ F := by
    intro α h
    rw [hF, Finset.mem_Iic]
    intro i
    simpa using (Finsupp.le_degree i α).trans h.le
  set P : MvPolynomial (Fin d) O :=
    ∑ α ∈ F.filter (fun α => α.degree < N), MvPolynomial.monomial α (MvPowerSeries.coeff α f) with hP
  set Q : MvPolynomial (Fin d) O :=
    ∑ α ∈ F.filter (fun α => ¬ α.degree < N), MvPolynomial.monomial α (MvPowerSeries.coeff α f) with hQ
  have cP : ∀ β, AddMonoidAlgebra.coeff P β = if β ∈ F ∧ β.degree < N then MvPowerSeries.coeff β f else 0 := by
    intro β
    rw [hP, MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' (F.filter _) β]
    simp only [Finset.mem_filter]
  have cQ : ∀ β, AddMonoidAlgebra.coeff Q β = if β ∈ F ∧ ¬ β.degree < N then MvPowerSeries.coeff β f else 0 := by
    intro β
    rw [hQ, MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' (F.filter _) β]
    simp only [Finset.mem_filter]
  refine ⟨P, ?_, ?_, ?_⟩
  · intro α hα
    rw [cP, if_neg]
    omega
  · intro α hα
    rw [cP, if_pos ⟨memF α (lt_of_lt_of_le hα (le_max_left _ _)), hα⟩]
  · have hrest : (p : A) ^ n ∣ E (f - (P : MvPowerSeries (Fin d) O) - (Q : MvPowerSeries (Fin d) O)) := by
      apply hM
      intro α hα
      have hαF := memF α (lt_of_lt_of_le hα (le_max_right _ _))
      rw [map_sub, map_sub, MvPolynomial.coeff_coe, MvPolynomial.coeff_coe, cP, cQ]
      by_cases h : α.degree < N
      · simp [hαF, h]
      · simp [hαF, h]
    have hQmem : MvPolynomial.aeval x Q ∈ Ideal.span (Set.range x) ^ N := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hQ, map_sum]
      refine Ideal.sum_mem _ fun α hα => aeval_monomial_mem_span_pow x N α ?_ _
      exact not_lt.1 (Finset.mem_filter.1 hα).2
    have hsplit : MvPolynomial.aeval x P = -(MvPolynomial.aeval x Q) -
        E (f - (P : MvPowerSeries (Fin d) O) - (Q : MvPowerSeries (Fin d) O)) := by
      rw [map_sub, map_sub, hf, evalPoly_eq x E hX, evalPoly_eq x E hX]
      ring
    rw [hsplit]
    refine Ideal.sub_mem _ ((Ideal.neg_mem_iff _).2 (Ideal.mem_sup_left hQmem)) (Ideal.mem_sup_right ?_)
    exact Ideal.mem_span_singleton.2 hrest

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTruncationCongrOfPadicContinuousEvalEqZeroStatement
open GlobalTheory.QLog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_truncation_congr_of_padicContinuousEval_eq_zero : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (d : ℕ) (x : Fin d → A) (E : MvPowerSeries (Fin d) O →ₐ[O] A), IsEval p x E → ∀ (n N : ℕ) (f : MvPowerSeries (Fin d) O), E f = 0 → ∃ P : MvPolynomial (Fin d) O, (∀ α : Fin d →₀ ℕ, N ≤ α.degree → AddMonoidAlgebra.coeff P α = 0) ∧ (∀ α : Fin d →₀ ℕ, α.degree < N → AddMonoidAlgebra.coeff P α = MvPowerSeries.coeff α f) ∧ MvPolynomial.aeval x P ∈ Ideal.span (Set.range x) ^ N ⊔ Ideal.span {(p : A) ^ n} := by
  first | exact @GlobalTheory.trunc_dec | exact GlobalTheory.trunc_dec | (intros; apply GlobalTheory.trunc_dec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylSchurEndomorphism
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylSchurEndomorphism
open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace GlobalTheory.LeviCut

theorem eV_coe_fin (N : ℕ) (ν : Fin N → ℕ) (a b : Fin N) (x : dualWeyl ℚ N N ν) :
    ((eV N ν a b x : dualWeyl ℚ N N ν) : MvPolynomial (Fin N × Fin N) ℚ) =
      Formalism.CohomologicalDescent.LR.der N N a b (x : MvPolynomial (Fin N × Fin N) ℚ) := by
  simp only [eV, dif_pos (And.intro a.isLt b.isLt)]
  rfl

theorem nablaSchur : NablaSchur := by
  intro N ν hν S hS hfix
  have hc : ∀ (a b : Fin N) (x : dualWeyl ℚ N N ν), eV N ν a b (S x) = S (eV N ν a b x) := by
    intro a b x
    have h := LinearMap.congr_fun (hS a a.isLt b b.isLt) x
    simpa only [Module.End.mul_apply] using h
  set v : dualWeyl ℚ N N ν := ⟨hw ℚ le_rfl ν, hwMem ℚ N N le_rfl ν hν⟩ with hv

  have hder : ∀ a b : Fin N, a < b →
      Formalism.CohomologicalDescent.LR.der N N a b ((S v : dualWeyl ℚ N N ν) : MvPolynomial (Fin N × Fin N) ℚ) = 0 := by
    intro a b hab
    have h1 : eV N ν a b v = 0 := by
      apply Subtype.ext
      rw [eV_coe_fin]
      exact Formalism.CohomologicalDescent.LR.der_hw_raise ν a b hab
    rw [← eV_coe_fin, hc, h1, map_zero]
    rfl
  have hkill : ∀ a b : Fin N, a < b → ∀ k : ℕ, 1 ≤ k →
      rowDiv ℚ a b k ((S v : dualWeyl ℚ N N ν) : MvPolynomial (Fin N × Fin N) ℚ) = 0 := by
    intro a b hab k hk
    obtain ⟨k, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [Formalism.CohomologicalDescent.LR.der_pow a b (ne_of_lt hab), pow_succ, Module.End.mul_apply]
    have h2 := hder a b hab
    change (Formalism.CohomologicalDescent.LR.der N N a b : Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ)) _ = 0 at h2
    rw [h2, map_zero, smul_zero]
  obtain ⟨c, hcv⟩ := hwLine ℚ N N le_rfl ν hν _ (S v).2 hkill
  have hc1 : c = 1 := by
    rw [hcv, Formalism.CohomologicalDescent.LR.fock_smul_right] at hfix
    have hpos := Formalism.CohomologicalDescent.LR.hw_norm_pos ν
    have h3 : (c - 1) * fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) = 0 := by rw [sub_mul, hfix, one_mul, sub_self]
    rcases mul_eq_zero.1 h3 with h | h
    · linarith
    · exact absurd h (ne_of_gt hpos)
  have hSv : S v = v := by
    apply Subtype.ext
    rw [hcv, hc1, one_smul]

  set M : Submodule ℚ (MvPolynomial (Fin N × Fin N) ℚ) :=
    (LinearMap.ker (S - 1)).map (dualWeyl ℚ N N ν).subtype with hM
  have hmem : ∀ x : dualWeyl ℚ N N ν, S x = x → (x : MvPolynomial (Fin N × Fin N) ℚ) ∈ M := by
    intro x hx
    refine ⟨x, ?_, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, hx, sub_self]
  have hle : M ≤ dualWeyl ℚ N N ν := by
    rintro f ⟨x, _, rfl⟩
    exact x.2
  have hcl : RowDivClosed M := by
    intro a b k
    refine Formalism.CohomologicalDescent.LR.closed_of_der a b M ?_ k
    rintro f ⟨x, hx, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hx
    have h4 := hmem (eV N ν a b x) (by rw [← hc, hx])
    rw [eV_coe_fin] at h4
    exact h4
  have hhw : hw ℚ le_rfl ν ∈ M := hmem v hSv
  have heq := closedEqNabla N N le_rfl ν hν M hle hcl hhw
  apply LinearMap.ext
  intro x
  have hx : (x : MvPolynomial (Fin N × Fin N) ℚ) ∈ M := by rw [heq]; exact x.2
  obtain ⟨y, hy, hyx⟩ := hx
  have hyx' : y = x := Subtype.ext hyx
  subst hyx'
  simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hy
  rw [Module.End.one_apply]
  exact hy

end GlobalTheory.LeviCut
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylSchurEndomorphismStatement
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeyl_schur_endomorphism : GlobalTheory.LeviCut.NablaSchur := by
  first | exact @GlobalTheory.LeviCut.nablaSchur | exact GlobalTheory.LeviCut.nablaSchur | (intros; apply GlobalTheory.LeviCut.nablaSchur <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviWhittakerColumnCharacterEigenVecMulNeBot
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviWhittakerColumnCharacterEigenVecMulNeBot
noncomputable section

namespace GlobalTheory.FinGL.LeviWh

open GlobalTheory.FinGL Formalism.L2.DIV Module

section Mat

variable {F : Type} [Field F] {r : ℕ} {k : Fin r} {H U : Matrix (Fin r) (Fin r) F}

theorem corner_row (hH : ∀ i j, H i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j → i < k ∧ j < k)
    (N : Matrix (Fin r) (Fin r) F) {i : Fin r} (hi : ¬ i < k) (j : Fin r) : (H * N) i j = N i j := by
  have : (H * N) i j = ((1 : Matrix (Fin r) (Fin r) F) * N) i j := by
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    have : H i m = (1 : Matrix (Fin r) (Fin r) F) i m := by
      by_contra hne
      exact hi (hH i m hne).1
    rw [this]
  rw [this, one_mul]

theorem corner_nil_mul (hH : ∀ i j, H i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j → i < k ∧ j < k)
    (hU : ∀ i j : Fin r, j.val < k.val → U i j = (1 : Matrix (Fin r) (Fin r) F) i j) :
    (U - 1) * H = U - 1 := by
  conv_rhs => rw [← mul_one (U - 1)]
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hm : m < k
  · rw [Matrix.sub_apply, hU i m hm, sub_self, zero_mul, zero_mul]
  · have : H m j = (1 : Matrix (Fin r) (Fin r) F) m j := by
      by_contra hne
      exact hm (hH m j hne).1
    rw [this]

end Mat

variable {F : Type} [Field F] {r : ℕ}

theorem corner_conj_val {k : Fin r} (h u : GL (Fin r) F)
    (hH : ∀ i j, (h : Matrix (Fin r) (Fin r) F) i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j → i < k ∧ j < k)
    (hU : ∀ i j : Fin r, j.val < k.val → (u : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j) :
    ((h * u * h⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
      1 + (h : Matrix (Fin r) (Fin r) F) * ((u : Matrix (Fin r) (Fin r) F) - 1) := by
  rw [Units.val_mul, Units.mul_inv_eq_iff_eq_mul, add_mul, mul_assoc, corner_nil_mul hH hU, Units.val_mul,
    mul_sub, one_mul, mul_one, add_sub_cancel]

theorem corner_conj {k : Fin r} (h u : GL (Fin r) F)
    (hH : ∀ i j, (h : Matrix (Fin r) (Fin r) F) i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j → i < k ∧ j < k)
    (hU : ∀ i j : Fin r, j.val < k.val → (u : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j) :
    (∀ i j : Fin r, ¬ i < k → ((h * u * h⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j =
      (u : Matrix (Fin r) (Fin r) F) i j) ∧
    (∀ i j : Fin r, j.val < k.val → ((h * u * h⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j =
      (1 : Matrix (Fin r) (Fin r) F) i j) ∧
    (∀ i : Fin r, ((h * u * h⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k =
      ((h : Matrix (Fin r) (Fin r) F) * (u : Matrix (Fin r) (Fin r) F)) i k) := by
  rw [corner_conj_val h u hH hU]
  refine ⟨fun i j hi => ?_, fun i j hj => ?_, fun i => ?_⟩
  · rw [Matrix.add_apply, corner_row hH _ hi, Matrix.sub_apply, add_sub_cancel]
  · rw [Matrix.add_apply, Matrix.mul_apply, Finset.sum_eq_zero, add_zero]
    intro m _
    rw [Matrix.sub_apply, hU m j hj, sub_self, mul_zero]
  · have : (h : Matrix (Fin r) (Fin r) F) i k = (1 : Matrix (Fin r) (Fin r) F) i k := by
      by_contra hne
      exact lt_irrefl _ (hH i k hne).2
    rw [mul_sub, mul_one, Matrix.add_apply, Matrix.sub_apply, this, add_sub_cancel]

theorem eig_colChar_vecMul_ne_bot (F : Type) [Field F] (ψ : AddChar F ℂ) (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) (k : Fin r) (l : Fin r → F)
    (h : blockTri (κ := F) b)
    (hH : ∀ i j, ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j →
      i < k ∧ j < k)
    (hne : eig σ (colSet F b k.val) (colChar ψ b k l) ≠ ⊥) :
    eig σ (colSet F b k.val)
      (colChar ψ b k (Matrix.vecMul l ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F))) ≠ ⊥ := by
  rw [Submodule.ne_bot_iff] at hne ⊢
  obtain ⟨v, hv, hv0⟩ := hne
  rw [mem_eig] at hv
  refine ⟨σ h⁻¹ v, ?_, fun h0 => hv0 ?_⟩
  · rw [mem_eig]
    rintro u ⟨hu, hU⟩
    obtain ⟨c1, c2, c3⟩ := corner_conj (h : GL (Fin r) F) (u : GL (Fin r) F) hH hU
    have hc : ((h * u * h⁻¹ : blockTri (κ := F) b) : GL (Fin r) F) =
        (h : GL (Fin r) F) * (u : GL (Fin r) F) * (h : GL (Fin r) F)⁻¹ := rfl
    have hmem : h * u * h⁻¹ ∈ colSet F b k.val := by
      refine ⟨?_, ?_⟩
      · rw [hc]
        refine ⟨fun i j hij => ?_, fun i => ?_⟩
        · have hij' : j < i := hij
          by_cases hj : j < k
          · rw [c2 i j hj, Matrix.one_apply_ne (ne_of_gt hij')]
          · rw [c1 i j (fun hi => hj (hij'.trans hi)), unip_lower hu hij']
        · by_cases hi : i < k
          · rw [c2 i i hi, Matrix.one_apply_eq]
          · rw [c1 i i hi, unip_diag hu]
      · rw [hc]; exact c2
    have hχ : colChar ψ b k l (h * u * h⁻¹) =
        colChar ψ b k (Matrix.vecMul l ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) u := by
      unfold colChar
      rw [hc]
      congr 2
      · simp only [c3]
        have := congrFun (Matrix.vecMul_vecMul l ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)
          ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) k
        exact this.symm
      · unfold edgeSum
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        split_ifs with hij
        · refine c1 i j fun hi => ?_
          have h1 : j.val = i.val + 1 := hij.1.1
          have h2 : k.val < j.val := hij.2
          have h3 : i.val < k.val := hi
          omega
        · rfl
    have e : σ u (σ h⁻¹ v) = σ h⁻¹ (σ (h * u * h⁻¹) v) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      congr 2
      group
    rw [e, hv _ hmem, map_smul, hχ]
  · have : σ h (σ h⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [← this, h0, map_zero]

end GlobalTheory.FinGL.LeviWh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviWhittakerColumnCharacterEigenVecMulNeBotStatement
open GlobalTheory.FinGL GlobalTheory.FinGL.LeviWh Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviWhittakerColumnCharacter_eigen_vecMul_ne_bot : ∀ (F : Type) [Field F] (ψ : AddChar F ℂ) (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V) (k : Fin r) (l : Fin r → F) (h : blockTri (κ := F) b), (∀ i j, ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j → i < k ∧ j < k) → eig σ (colSet F b k.val) (colChar ψ b k l) ≠ ⊥ → eig σ (colSet F b k.val) (colChar ψ b k (Matrix.vecMul l ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F))) ≠ ⊥ := by
  first | exact @GlobalTheory.FinGL.LeviWh.eig_colChar_vecMul_ne_bot | exact GlobalTheory.FinGL.LeviWh.eig_colChar_vecMul_ne_bot | (intros; apply GlobalTheory.FinGL.LeviWh.eig_colChar_vecMul_ne_bot <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviTensorBlockExt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabLeBlockTri
noncomputable section

namespace GlobalTheory.HcIrr

open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {r s : ℕ}

def natBlocks (b : Fin r → Fin s) : Fin r → ℕ := fun i => (b i : ℕ)

theorem blockTri_le_parab (b : Fin r → Fin s) : blockTri (κ := K) (natBlocks b) ≤ parab K b := by
  intro p hp
  refine ⟨fun i j hij => hp hij, fun i j hij => ?_⟩
  exact (inv_mem hp : p⁻¹ ∈ blockTri (κ := K) (natBlocks b)) hij

theorem parab_le_blockTri (b : Fin r → Fin s) : parab K b ≤ blockTri (κ := K) (natBlocks b) := by
  intro p hp i j hij
  exact hp.1 i j hij

theorem levi_one (b : Fin r → Fin s) (c : Fin s) : levi K b c 1 = 1 := by
  apply Units.ext
  exact Matrix.submatrix_one _ Subtype.val_injective

theorem levi_mul (b : Fin r → Fin s) (c : Fin s) (p q : parab K b) :
    levi K b c (p * q) = levi K b c p * levi K b c q := by
  apply Units.ext
  exact blk_mul b c p.2.1 q.2.1

variable (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))

def leviTensor : Representation ℂ (blockTri (κ := K) (natBlocks b))
    (PiTensorProduct ℂ (fun c => (lam c : Type))) where
  toFun p := infl K b lam (Subgroup.inclusion (blockTri_le_parab b) p)
  map_one' := by
    have : ∀ c, (lam c).ρ (levi K b c (Subgroup.inclusion (blockTri_le_parab b) 1)) = LinearMap.id := by
      intro c
      rw [map_one, levi_one, map_one]
      rfl
    simp only [infl, this]
    exact PiTensorProduct.map_id
  map_mul' p q := by
    have : ∀ c, (lam c).ρ (levi K b c (Subgroup.inclusion (blockTri_le_parab b) (p * q))) =
        (lam c).ρ (levi K b c (Subgroup.inclusion (blockTri_le_parab b) p)) ∘ₗ
          (lam c).ρ (levi K b c (Subgroup.inclusion (blockTri_le_parab b) q)) := by
      intro c
      rw [map_mul, levi_mul, map_mul]
      rfl
    simp only [infl, this]
    exact PiTensorProduct.map_comp _ _

theorem leviTensor_apply (p : blockTri (κ := K) (natBlocks b)) :
    leviTensor b lam p = PiTensorProduct.map (fun c =>
      (lam c).ρ (levi K b c (Subgroup.inclusion (blockTri_le_parab b) p))) := rfl

instance finiteTensor : FiniteDimensional ℂ (PiTensorProduct ℂ (fun c => (lam c : Type))) :=
  Module.Finite.of_basis (Basis.piTensorProduct fun c => Module.finBasis ℂ (lam c : Type))

end GlobalTheory.HcIrr
end
end

noncomputable section

namespace GlobalTheory.HcIrr

open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {r s : ℕ}

def extMat (b : Fin r → Fin s) (c : Fin s) :
    Matrix {i // b i = c} {i // b i = c} K →* Matrix (Fin r) (Fin r) K where
  toFun g := Matrix.reindex (Equiv.sumCompl fun a => b a = c) (Equiv.sumCompl fun a => b a = c)
    (Matrix.fromBlocks g 0 0 1)
  map_one' := by simp
  map_mul' x y := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp

theorem extMat_in (b : Fin r → Fin s) (c : Fin s) (g : Matrix {i // b i = c} {i // b i = c} K)
    (i j : {i // b i = c}) : extMat b c g i.1 j.1 = g i j := by
  simp [extMat, Equiv.sumCompl_symm_apply_of_pos (p := fun a => b a = c) i.2,
    Equiv.sumCompl_symm_apply_of_pos (p := fun a => b a = c) j.2]

theorem extMat_out (b : Fin r → Fin s) (c : Fin s) (g : Matrix {i // b i = c} {i // b i = c} K) (i j : Fin r)
    (h : ¬ (b i = c ∧ b j = c)) : extMat b c g i j = (1 : Matrix (Fin r) (Fin r) K) i j := by
  by_cases hi : b i = c <;> by_cases hj : b j = c
  · exact absurd ⟨hi, hj⟩ h
  · have : i ≠ j := fun e => hj (e ▸ hi)
    simp [extMat, Equiv.sumCompl_symm_apply_of_pos (p := fun a => b a = c) hi,
      Equiv.sumCompl_symm_apply_of_neg (p := fun a => b a = c) hj, this]
  · have : i ≠ j := fun e => hi (e ▸ hj)
    simp [extMat, Equiv.sumCompl_symm_apply_of_neg (p := fun a => b a = c) hi,
      Equiv.sumCompl_symm_apply_of_pos (p := fun a => b a = c) hj, this]
  · simp [extMat, Equiv.sumCompl_symm_apply_of_neg (p := fun a => b a = c) hi,
      Equiv.sumCompl_symm_apply_of_neg (p := fun a => b a = c) hj, Matrix.one_apply]

def blockExt (b : Fin r → Fin s) (c : Fin s) :
    GL {i // b i = c} K →* blockTri (κ := K) (natBlocks b) :=
  (Units.map (extMat b c)).codRestrict (blockTri (κ := K) (natBlocks b)) fun g => by
    refine mem_blockTri.2 fun i j hij => ?_
    show extMat b c _ i j = 0
    have hne : b i ≠ b j := fun e => by
      simp only [natBlocks, e] at hij
      exact lt_irrefl _ hij
    rw [extMat_out b c _ i j (fun e => hne (e.1.trans e.2.symm)),
      Matrix.one_apply_ne (fun e => hne (congrArg b e))]

theorem blockExt_in (b : Fin r → Fin s) (c : Fin s) (g : GL {i // b i = c} K) (i j : {i // b i = c}) :
    (((blockExt b c g : blockTri (κ := K) (natBlocks b)) : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i.1 j.1 =
      (g : Matrix _ _ K) i j :=
  extMat_in b c _ i j

theorem blockExt_out (b : Fin r → Fin s) (c : Fin s) (g : GL {i // b i = c} K) (i j : Fin r)
    (h : ¬ (b i = c ∧ b j = c)) :
    (((blockExt b c g : blockTri (κ := K) (natBlocks b)) : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j =
      (1 : Matrix (Fin r) (Fin r) K) i j :=
  extMat_out b c _ i j h

theorem levi_blockExt_same (b : Fin r → Fin s) (c : Fin s) (g : GL {i // b i = c} K) :
    levi K b c (Subgroup.inclusion (blockTri_le_parab b) (blockExt b c g)) = g := by
  apply Units.ext
  ext x y
  exact blockExt_in b c g x y

theorem levi_blockExt_ne (b : Fin r → Fin s) {c c' : Fin s} (h : c' ≠ c) (g : GL {i // b i = c} K) :
    levi K b c' (Subgroup.inclusion (blockTri_le_parab b) (blockExt b c g)) = 1 := by
  apply Units.ext
  ext x y
  have := blockExt_out b c g x.1 y.1 (fun e => h (x.2.symm.trans e.1))
  show (((blockExt b c g : blockTri (κ := K) (natBlocks b)) : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) x.1 y.1 =
    (1 : Matrix _ _ K) x y
  rw [this]
  simp [Matrix.one_apply, Subtype.ext_iff]

variable (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))

theorem leviTensor_blockExt (c : Fin s) (g : GL {i // b i = c} K) :
    leviTensor b lam (blockExt b c g) = PiTensorProduct.map
      (Function.update (fun c' => (LinearMap.id : (lam c' : Type) →ₗ[ℂ] (lam c' : Type))) c ((lam c).ρ g)) := by
  rw [leviTensor_apply]
  congr 1
  funext c'
  by_cases h : c' = c
  · subst h
    rw [levi_blockExt_same, Function.update_self]
  · rw [levi_blockExt_ne b h, Function.update_of_ne h, map_one]
    rfl

end GlobalTheory.HcIrr
end
end
