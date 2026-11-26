module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ColumnDataLaws
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VacuumCharacterDeterminant
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GeneralDiagonalMatrix
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicCoeffDenominatorBoundOfBoundedRoots
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormMultisetSumLeOfForallLeUltrametric
namespace GlobalTheory

open Polynomial

theorem norm_multiset_sum_le_of_forall_le_ultrametric {K : Type} [NormedField K]
    [IsUltrametricDist K] (m : Multiset K) {C : ℝ} (hC : 0 ≤ C) (h : ∀ x ∈ m, ‖x‖ ≤ C) :
    ‖m.sum‖ ≤ C := by
  induction m using Multiset.induction_on with
  | empty => simpa using hC
  | cons a s ih =>
    rw [Multiset.sum_cons]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · exact h a (Multiset.mem_cons_self _ _)
    · exact ih fun x hx => h x (Multiset.mem_cons_of_mem hx)

theorem norm_multiset_prod_le_pow_card_of_forall_le {K : Type} [NormedField K]
    (m : Multiset K) {B : ℝ} (h : ∀ x ∈ m, ‖x‖ ≤ B) :
    ‖m.prod‖ ≤ B ^ Multiset.card m := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, Multiset.card_cons, norm_mul, pow_succ']
    have ha := h a (Multiset.mem_cons_self _ _)
    exact mul_le_mul ha (ih fun x hx => h x (Multiset.mem_cons_of_mem hx)) (norm_nonneg _)
      ((norm_nonneg _).trans ha)

theorem norm_coeff_natDegree_sub_le_pow_of_roots_le (K : Type) [NormedField K]
    [IsUltrametricDist K] [IsAlgClosed K] (Q : Polynomial K) (hQ : Q.Monic) (B : ℝ)
    (hB : ∀ r : K, Q.IsRoot r → ‖r‖ ≤ B) (i : ℕ) (hi : i ≤ Q.natDegree) :
    ‖Q.coeff (Q.natDegree - i)‖ ≤ B ^ i := by
  have hcard : Multiset.card Q.roots = Q.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hroot : ∀ r ∈ Q.roots, ‖r‖ ≤ B := fun r hr => hB r (isRoot_of_mem_roots hr)
  have hBi : 0 ≤ B ^ i := by
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simp
    · have : 0 < Multiset.card Q.roots := by omega
      obtain ⟨r, hr⟩ := Multiset.card_pos_iff_exists_mem.1 this
      exact pow_nonneg ((norm_nonneg _).trans (hroot r hr)) _
  rw [Polynomial.coeff_eq_esymm_roots_of_card hcard (Nat.sub_le _ _), hQ.leadingCoeff,
    Nat.sub_sub_self hi, one_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Multiset.esymm]
  refine norm_multiset_sum_le_of_forall_le_ultrametric _ hBi ?_
  intro x hx
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hx
  obtain ⟨hle, hc⟩ := Multiset.mem_powersetCard.1 ht
  rw [← hc]
  exact norm_multiset_prod_le_pow_card_of_forall_le t fun y hy =>
    hroot y (Multiset.mem_of_le hle hy)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicCoeffDenominatorBoundOfBoundedRoots
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

open Polynomial

theorem not_dvd_den_of_padic_norm_le_one (p : ℕ) [Fact p.Prime] (c : ℚ)
    (hc : ‖(c : ℚ_[p])‖ ≤ 1) : ¬ p ∣ c.den := by
  intro hd
  have hden : ‖((c.den : ℤ) : ℚ_[p])‖ < 1 :=
    Padic.norm_intCast_lt_one_iff.2 (Int.natCast_dvd_natCast.2 hd)
  have hnum : ‖((c.num : ℤ) : ℚ_[p])‖ < 1 := by
    have h1 : ((c.num : ℤ) : ℚ_[p]) = (c : ℚ_[p]) * ((c.den : ℤ) : ℚ_[p]) := by
      have : (c.num : ℚ) = c * (c.den : ℤ) := by
        rw [Int.cast_natCast, Rat.mul_den_eq_num]
      exact_mod_cast congrArg (fun x : ℚ => (x : ℚ_[p])) this
    rw [h1, norm_mul]
    calc ‖(c : ℚ_[p])‖ * ‖((c.den : ℤ) : ℚ_[p])‖ ≤ 1 * ‖((c.den : ℤ) : ℚ_[p])‖ :=
          mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact hden
  have hpn : (p : ℤ) ∣ c.num := Padic.norm_intCast_lt_one_iff.1 hnum
  have hcop := c.reduced
  have h2 : p ∣ c.num.natAbs := by
    rw [← Int.natCast_dvd_natCast, Int.natCast_natAbs]; exact (dvd_abs _ _).2 hpn
  have h3 := Nat.dvd_gcd h2 hd
  rw [hcop.gcd_eq_one] at h3
  exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.1 h3)

theorem padic_denom_coeff_of_roots_bounded :
    ∀ (p : ℕ) [Fact p.Prime] (q : Polynomial ℚ), q.Monic → ∀ k : ℕ,
      (∀ μ : PadicAlgCl p, (q.map (algebraMap ℚ (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ (p : ℝ) ^ k) →
      ∀ i, ∃ m : ℕ, m.Coprime p ∧ ∃ a : ℤ, ((p ^ (k * q.natDegree) * m : ℕ) : ℚ) * q.coeff i = a := by
  intro p _ q hq k hroot i
  have hp : p.Prime := Fact.out
  by_cases hi : q.natDegree < i
  · refine ⟨1, Nat.coprime_one_left _, 0, ?_⟩
    rw [coeff_eq_zero_of_natDegree_lt hi]; simp
  push_neg at hi
  have hQm : (q.map (algebraMap ℚ (PadicAlgCl p))).Monic := hq.map _
  have hQd : (q.map (algebraMap ℚ (PadicAlgCl p))).natDegree = q.natDegree := natDegree_map _
  have hB := GlobalTheory.norm_coeff_natDegree_sub_le_pow_of_roots_le (PadicAlgCl p) _ hQm ((p : ℝ) ^ k)
    hroot (q.natDegree - i) (by omega)
  rw [hQd, Nat.sub_sub_self hi, coeff_map] at hB
  have hn : ‖((q.coeff i : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (k * q.natDegree) := by
    have e : algebraMap ℚ (PadicAlgCl p) (q.coeff i) =
        algebraMap ℚ_[p] (PadicAlgCl p) ((q.coeff i : ℚ) : ℚ_[p]) := by
      rw [eq_ratCast, map_ratCast]
    rw [e, PadicAlgCl.norm_extends] at hB
    refine hB.trans ?_
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by exact_mod_cast hp.one_lt.le)
      (Nat.mul_le_mul_left k (Nat.sub_le _ _))
  set c : ℚ := ((p ^ (k * q.natDegree) : ℕ) : ℚ) * q.coeff i with hcdef
  have hc : ‖(c : ℚ_[p])‖ ≤ 1 := by
    have hp0 : (0 : ℝ) < (p : ℝ) ^ (k * q.natDegree) := by
      have : (0 : ℝ) < p := by exact_mod_cast hp.pos
      positivity
    rw [hcdef]
    push_cast
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
    calc ((p : ℝ) ^ (k * q.natDegree))⁻¹ * ‖((q.coeff i : ℚ) : ℚ_[p])‖
        ≤ ((p : ℝ) ^ (k * q.natDegree))⁻¹ * (p : ℝ) ^ (k * q.natDegree) :=
          mul_le_mul_of_nonneg_left hn (inv_nonneg.2 hp0.le)
      _ = 1 := inv_mul_cancel₀ hp0.ne'
  refine ⟨c.den, ?_, c.num, ?_⟩
  · exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2
      (not_dvd_den_of_padic_norm_le_one p c hc))
  · rw [← Rat.den_mul_eq_num c, hcdef]
    push_cast
    ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicCoeffDenominatorBoundOfBoundedRootsStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_coeff_denominator_bound_of_bounded_roots : ∀ (p : ℕ) [Fact p.Prime] (q : Polynomial ℚ), q.Monic → ∀ k : ℕ, (∀ μ : PadicAlgCl p, (q.map (algebraMap ℚ (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ (p : ℝ) ^ k) → ∀ i, ∃ m : ℕ, m.Coprime p ∧ ∃ a : ℤ, ((p ^ (k * q.natDegree) * m : ℕ) : ℚ) * q.coeff i = a := by
  first | (exact @GlobalTheory.padic_denom_coeff_of_roots_bounded) | (exact GlobalTheory.padic_denom_coeff_of_roots_bounded) | (intros; apply GlobalTheory.padic_denom_coeff_of_roots_bounded  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenbasisPsiInfinitePlaceDistinctRoots
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardRootsMapPol
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Pair

theorem card_roots_map_pol (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (φ : G.F →+* ℂ) :
    ((P.pol.map φ).roots.toFinset).card = G.n ∧ P.pol.Monic := by
  have hint : IsIntegral G.F (P.γ : G.C) := Algebra.IsIntegral.isIntegral _
  have hmon : P.pol.Monic := minpoly.monic hint
  refine ⟨?_, hmon⟩
  have hsep : (P.pol.map φ).Separable := P.reg.2.map
  have hdeg : (P.pol.map φ).natDegree = G.n := by
    rw [Polynomial.natDegree_map]; exact P.reg.1
  rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep), ← hdeg]
  exact IsAlgClosed.card_roots_eq_natDegree

end GlobalTheory.LKMid.Pair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixDiagonalizableOfCharpolyEqProdDistinct
open Polynomial

namespace GlobalTheory

theorem matrix_diagonalizable_of_charpoly_eq_prod_distinct (K : Type) [Field K] (n : ℕ)
    (γ : Matrix (Fin n) (Fin n) K) (ν : Fin n → K) (hν : Function.Injective ν)
    (hγ : γ.charpoly = ∏ k, (X - C (ν k))) :
    ∃ y : GL (Fin n) K, γ * (y : Matrix (Fin n) (Fin n) K) = (y : Matrix (Fin n) (Fin n) K) * Matrix.diagonal ν := by
  have hev : ∀ k, Module.End.HasEigenvalue (Matrix.toLin' γ) (ν k) := by
    intro k
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hγ]
    simp only [IsRoot, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (sub_self _)
  choose v hv using fun k => (hev k).exists_hasEigenvector
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' _ ν hν v hv
  set Y : Matrix (Fin n) (Fin n) K := Matrix.of fun i k => v k i with hY
  have hcols : Y.col = v := by
    funext k i; rfl
  have hu : IsUnit Y := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    rw [hcols]; exact hli
  refine ⟨hu.unit, ?_⟩
  simp only [IsUnit.unit_spec]
  ext i k
  rw [Matrix.mul_diagonal]
  have h1 := (hv k).apply_eq_smul
  rw [Matrix.toLin'_apply] at h1
  have h2 := congrFun h1 i
  simp only [Pi.smul_apply, smul_eq_mul] at h2
  rw [Matrix.mul_apply]
  simp only [hY, Matrix.of_apply]
  rw [mul_comm, ← h2]
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenbasisPsiInfinitePlaceDistinctRoots
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount Polynomial
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

variable {p : ℕ} [Fact p.Prime]

theorem charpoly_psi_eq_map_pol (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F) :
    (G.psi v (P.γ : G.C)).charpoly = P.pol.map v.embedding := by
  letI : Algebra G.F ℂ := v.embedding.toAlgebra
  have hg : ∀ a, G.psi v (algebraMap G.F G.C a) = algebraMap G.F (Matrix (Fin G.n) (Fin G.n) ℂ) a :=
    fun a => by rw [G.psi_F, Matrix.algebraMap_eq_diagonal]; rfl
  let g : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) ℂ := { G.psi v with commutes' := hg }
  let L : ℂ ⊗[G.F] G.C →ₐ[ℂ] Matrix (Fin G.n) (Fin G.n) ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ _) g (fun r _ => Algebra.commute_algebraMap_left r _)
  haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
  have hinj : Function.Injective L :=
    (IsSimpleRing.injective_ringHom_or_subsingleton_codomain L.toRingHom).resolve_right (not_subsingleton _)
  have hL : ∀ x : G.C, L ((1 : ℂ) ⊗ₜ x) = G.psi v x := fun x => by
    show (Algebra.TensorProduct.lift _ g _) ((1 : ℂ) ⊗ₜ x) = _
    erw [Algebra.TensorProduct.lift_tmul]
    rw [map_one, one_mul]
    rfl
  set γ : G.C := (P.γ : G.C) with hγ
  have hdeg : (minpoly G.F γ).natDegree = G.n := P.reg.1
  have hli : LinearIndependent G.F (fun i : Fin G.n => γ ^ (i : ℕ)) := by
    have := linearIndependent_pow (K := G.F) γ
    rw [hdeg] at this
    exact this
  have hT : LinearIndependent ℂ (fun i : Fin G.n => (1 : ℂ) ⊗ₜ[G.F] (γ ^ (i : ℕ))) :=
    Module.Flat.linearIndependent_one_tmul hli
  have hM : LinearIndependent ℂ (fun i : Fin G.n => (G.psi v γ) ^ (i : ℕ)) := by
    have := hT.map' L.toLinearMap (LinearMap.ker_eq_bot.2 hinj)
    have e : (fun i : Fin G.n => (G.psi v γ) ^ (i : ℕ)) =
        L.toLinearMap ∘ (fun i : Fin G.n => (1 : ℂ) ⊗ₜ[G.F] (γ ^ (i : ℕ))) := by
      funext i
      simp only [Function.comp_apply, AlgHom.toLinearMap_apply]
      rw [hL, map_pow]
    rw [e]
    exact this
  have hint : IsIntegral ℂ (G.psi v γ) := Algebra.IsIntegral.isIntegral _
  set q := minpoly ℂ (G.psi v γ) with hq
  have hqm : q.Monic := minpoly.monic hint
  have hqdeg : G.n ≤ q.natDegree := by
    by_contra hlt
    push_neg at hlt
    have h0 : aeval (G.psi v γ) q = 0 := minpoly.aeval _ _
    rw [Polynomial.aeval_eq_sum_range' hlt, Finset.sum_range] at h0
    have h1 := Fintype.linearIndependent_iff.1 hM (fun i => q.coeff i) h0 ⟨q.natDegree, hlt⟩
    have h2 : q.coeff q.natDegree = 1 := hqm.coeff_natDegree
    rw [h2] at h1
    exact one_ne_zero h1
  have hpol : aeval (G.psi v γ) (P.pol.map v.embedding) = 0 := by
    have h : aeval (g γ) (minpoly G.F γ) = 0 := by rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    change aeval (G.psi v γ) ((minpoly G.F γ).map (algebraMap G.F ℂ)) = 0
    rw [Polynomial.aeval_map_algebraMap]
    exact h
  have hFint : IsIntegral G.F γ := Algebra.IsIntegral.isIntegral _
  have hm1 : (P.pol.map v.embedding).Monic := (minpoly.monic hFint).map _
  have hn1 : (P.pol.map v.embedding).natDegree = G.n := by
    rw [Polynomial.natDegree_map]; exact hdeg
  have e1 := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm hm1 (minpoly.dvd _ _ hpol)
    (by rw [hn1]; exact hqdeg)
  have e2 := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm (Matrix.charpoly_monic _)
    (Matrix.minpoly_dvd_charpoly _) (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; exact hqdeg)
  rw [e2, e1]

theorem psi_eigenbasis : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F),
    ∃ (Z : GL (Fin G.n) ℂ) (lam : Fin G.n → ℂ), Function.Injective lam ∧
      (∀ z : ℂ, P.pol.eval₂ v.embedding z = 0 ↔ ∃ i, lam i = z) ∧
      G.psi v (P.γ : G.C) * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) =
        (Z : Matrix (Fin G.n) (Fin G.n) ℂ) * Matrix.diagonal lam := by
  intro p _ G P v
  set Q := P.pol.map v.embedding with hQ
  obtain ⟨hcard, hmon⟩ := GlobalTheory.LKMid.Pair.card_roots_map_pol p G P v.embedding
  have hsep : Q.Separable := P.reg.2.map
  have hnd : Q.roots.Nodup := Polynomial.nodup_roots hsep
  have hQm : Q.Monic := hmon.map _
  have hne : P.pol ≠ 0 := hmon.ne_zero
  let e : Fin G.n ≃ {x // x ∈ Q.roots.toFinset} :=
    (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hcard)).symm
  let lam : Fin G.n → ℂ := fun i => (e i : ℂ)
  have hlam : Function.Injective lam := fun i j h => e.injective (Subtype.ext h)
  have hprod : Q = ∏ k, (X - C (lam k)) := by
    have h1 : Q = (Q.roots.map (fun a => X - C a)).prod :=
      (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hQm
        (IsAlgClosed.card_roots_eq_natDegree)).symm
    rw [h1]
    have h2 : (Q.roots.map (fun a => X - C a)).prod = ∏ a ∈ Q.roots.toFinset, (X - C a) := by
      rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hnd]
    rw [h2, ← Finset.prod_coe_sort]
    exact (Fintype.prod_equiv e _ _ (fun _ => rfl)).symm
  have hcp : (G.psi v (P.γ : G.C)).charpoly = ∏ k, (X - C (lam k)) := by
    rw [charpoly_psi_eq_map_pol, ← hQ, ← hprod]
  obtain ⟨Z, hZ⟩ := GlobalTheory.matrix_diagonalizable_of_charpoly_eq_prod_distinct ℂ G.n _ lam hlam hcp
  refine ⟨Z, lam, hlam, fun z => ?_, hZ⟩
  rw [← Polynomial.mem_roots_map_of_injective v.embedding.injective hne, ← hQ, ← Multiset.mem_toFinset]
  constructor
  · intro hz
    exact ⟨e.symm ⟨z, hz⟩, by simp [lam]⟩
  · rintro ⟨i, rfl⟩
    exact (e i).2

end GlobalTheory.LKMid
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenbasisPsiInfinitePlaceDistinctRootsStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigenbasis_psi_infinitePlace_distinct_roots : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F), ∃ (Z : GL (Fin G.n) ℂ) (lam : Fin G.n → ℂ), Function.Injective lam ∧ (∀ z : ℂ, P.pol.eval₂ v.embedding z = 0 ↔ ∃ i, lam i = z) ∧ G.psi v (P.γ : G.C) * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) = (Z : Matrix (Fin G.n) (Fin G.n) ℂ) * Matrix.diagonal lam := by
  first | (exact @GlobalTheory.LKMid.psi_eigenbasis) | (exact GlobalTheory.LKMid.psi_eigenbasis) | (intros; apply GlobalTheory.LKMid.psi_eigenbasis  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MoveTriLat
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotMove

open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

variable {D : D7} {T : Type} {A A' WW : HSp D}

def moveTri (Y : Tri T A A' WW) (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E))
    (g : GA D A) (g' : GA D A') (h : GA D WW) (t₀ : T) (r r' : T → ℂ) : Tri T A A' WW where
  rA := ⟨ΛA, Lev.finE A g * Y.rA.β, Y.rA.s, Y.rA.B⟩
  rA' := ⟨ΛA', Lev.finE A' g' * Y.rA'.β, Y.rA'.s, Y.rA'.B⟩
  rW := ⟨ΛW, Lev.finE WW h * Y.rW.β, Y.rW.s, Y.rW.B⟩
  ω := Y.ω
  ω' := Y.ω'
  vac := Y.ω t₀ (g, h) Y.vac
  vac' := Y.ω' t₀ (g', h) Y.vac'
  e := Y.e
  c := Y.c
  f t := (r t)⁻¹ • Y.ω t (g, h) (Y.f t)
  f' t := (r' t)⁻¹ • Y.ω' t (g', h) (Y.f' t)
  m := Y.m.map (fun x => x * g⁻¹)
  fd := (fun x => x * g) ⁻¹' Y.fd
  m' := Y.m'.map (fun x => x * g'⁻¹)
  fd' := (fun x => x * g') ⁻¹' Y.fd'

variable (Y : Tri T A A' WW) (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
  (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E))
  (g : GA D A) (g' : GA D A') (h : GA D WW) (t₀ : T) (r r' : T → ℂ)

end GlobalTheory.BotMove

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftMemLevelOfDatumFlagCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftMemLevelOfDatumFlagCharacter
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem lift_mem_levVP : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ) (g0 : P.H) (κ : GA D (Vc D i)), IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0.1 κ → κ ∈ levG (Vc D i) (R.βV i) (RecTie.datVP R i t P) ∧ levChi (Vc D i) (R.βV i) (RecTie.datVP R i t P) κ = ((P.chi g0 : ℂˣ) : ℂ)⁻¹ * levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i t P g0 κ hκ
  obtain ⟨hG, hpar, hr⟩ := hκ
  have hrt : Formalism.L2.DIV.rTup (R.βV i) (RecTie.datVP R i t P) (finE (Vc D i) κ) = g0.1 := hr
  have hmem : finE (Vc D i) κ ∈ Formalism.L2.DIV.lev D.sp.cm (Vc D i).gram (R.βV i) (RecTie.datVP R i t P) := by
    refine ⟨hpar, ?_⟩
    rw [hrt]; exact g0.2
  refine ⟨⟨hG, hmem⟩, ?_⟩
  have e1 : Formalism.L2.DIV.ext1 (RecTie.datVP R i t P).P.H (RecTie.datVP R i t P).P.chi
      (Formalism.L2.DIV.rTup (R.βV i) (RecTie.datVP R i t P) (finE (Vc D i) κ)) = (P.chi g0)⁻¹ := by
    rw [Formalism.L2.DIV.extendOne_of_mem _ hmem.2]
    simp only [hrt]
    rfl
  have e2 : Formalism.L2.DIV.ext1 (flagL (R.datVt i t)).P.H (flagL (R.datVt i t)).P.chi
      (Formalism.L2.DIV.rTup (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) κ)) = 1 := by
    rw [Formalism.L2.DIV.extendOne_of_mem _ (show Formalism.L2.DIV.rTup (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) κ) ∈ (flagL (R.datVt i t)).P.H from Subgroup.mem_top _)]
    rfl
  have key : Formalism.L2.DIV.levFn (R.βV i) (RecTie.datVP R i t P) (finE (Vc D i) κ) =
      (P.chi g0)⁻¹ * Formalism.L2.DIV.levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) κ) := by
    unfold Formalism.L2.DIV.levFn
    rw [e1, e2, one_mul, mul_assoc]
    rfl
  show ((Formalism.L2.DIV.levFn (R.βV i) (RecTie.datVP R i t P) (finE (Vc D i) κ) : ℂˣ) : ℂ) = _
  rw [key, Units.val_mul, Units.val_inv_eq_inv_val]
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftMemLevelOfDatumFlagCharacterStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_mem_levelOfDatum_flagCharacter : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ) (g0 : P.H) (κ : GA D (Vc D i)), IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0.1 κ → κ ∈ levG (Vc D i) (R.βV i) (RecTie.datVP R i t P) ∧ levChi (Vc D i) (R.βV i) (RecTie.datVP R i t P) κ = ((P.chi g0 : ℂˣ) : ℂ)⁻¹ * levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ := by
  first | exact @GlobalTheory.lift_mem_levVP | exact GlobalTheory.lift_mem_levVP | (intros; apply GlobalTheory.lift_mem_levVP <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPairScalarIsomorphicEquivalence
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPairScalarIsomorphicEquivalence
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Pair

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p}

theorem sh_mul' (a b : G.C) : sh G (a * b) = sh G b * sh G a := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem sh_one' : sh G (1 : G.C) = 1 := by
  simp only [sh, map_one, MulOpposite.unop_one]

theorem rel_equivalence : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), Equivalence (Pair.Rel (G := G)) := by
  intro p _ G
  refine ⟨fun P => ?_, fun {P Q} h => ?_, fun {P Q R} h h' => ?_⟩
  · refine ⟨1, 1, one_pos, ?_, ?_⟩
    · simp [sh_one']
    · simp
  · obtain ⟨y, s, hs, hβ, hγ⟩ := h
    refine ⟨y⁻¹, s⁻¹, inv_pos.mpr hs, ?_, ?_⟩
    · have e : sh G (y : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
        rw [← sh_mul', Units.inv_mul, sh_one']
      rw [hβ]
      simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, e, mul_one,
        inv_mul_cancel₀ hs.ne', mul_inv_cancel₀ hs.ne', one_smul, Units.inv_mul_cancel_left]
    · rw [hγ]; group
  · obtain ⟨y, s, hs, hβ, hγ⟩ := h
    obtain ⟨y', s', hs', hβ', hγ'⟩ := h'
    refine ⟨y' * y, s' * s, mul_pos hs' hs, ?_, ?_⟩
    · rw [hβ', hβ, Units.val_mul, sh_mul']
      simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc, mul_comm s]
    · rw [hγ', hγ]; group

end GlobalTheory.LKMid.Pair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPairScalarIsomorphicEquivalenceStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kottwitzPairScalarIsomorphic_equivalence : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), Equivalence (Pair.Rel (G := G)) := by
  first | (exact @GlobalTheory.LKMid.Pair.rel_equivalence) | (exact GlobalTheory.LKMid.Pair.rel_equivalence) | (intros; apply GlobalTheory.LKMid.Pair.rel_equivalence  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleTrivializationsDifferByGroupPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleTrivializationsDifferByGroupPoint
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem quot_mul_star {S A : Type*} [Ring S] [CommRing A] [Algebra A S] (σ : S →+* Sᵐᵒᵖ) (b : S) (x x' : Sˣ)
    (t t' : Aˣ) (hx : (x : S) * b * (σ x).unop = algebraMap A S t)
    (hx' : (x' : S) * b * (σ x').unop = algebraMap A S t') :
    ((x' * x⁻¹ : Sˣ) : S) * (σ ((x' * x⁻¹ : Sˣ) : S)).unop = algebraMap A S ((t' * t⁻¹ : Aˣ) : A) := by
  have h1 : (σ x).unop * (σ ((x⁻¹ : Sˣ) : S)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have ht : algebraMap A S ((t⁻¹ : Aˣ) : A) * algebraMap A S (t : A) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have h2 : ((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop = algebraMap A S ((t⁻¹ : Aˣ) : A) * b := by
    calc ((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop
        = algebraMap A S ((t⁻¹ : Aˣ) : A) * (((x⁻¹ : Sˣ) : S) * algebraMap A S (t : A) *
            (σ ((x⁻¹ : Sˣ) : S)).unop) := by
          rw [← Algebra.commutes (t : A), ← mul_assoc, ← mul_assoc, ht, one_mul]
      _ = algebraMap A S ((t⁻¹ : Aˣ) : A) * ((((x⁻¹ : Sˣ) : S) * x) * b *
            ((σ x).unop * (σ ((x⁻¹ : Sˣ) : S)).unop)) := by
          rw [← hx]; simp only [mul_assoc]
      _ = _ := by rw [Units.inv_mul, h1, one_mul, mul_one]
  calc ((x' * x⁻¹ : Sˣ) : S) * (σ ((x' * x⁻¹ : Sˣ) : S)).unop
      = x' * (((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop) * (σ x').unop := by
        simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, mul_assoc]
    _ = algebraMap A S ((t⁻¹ : Aˣ) : A) * ((x' : S) * b * (σ x').unop) := by
        rw [h2]; simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]
    _ = _ := by rw [hx', ← map_mul, mul_comm, Units.val_mul]

theorem triv_quot : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (β : G.C)
    (x x' : (R ⊗[ℚ] G.C)ˣ) (t t' : Rˣ), Triv G R β x t → Triv G R β x' t' →
    ∃ g : UPts G.star R, (g : (R ⊗[ℚ] G.C)ˣ × Rˣ).1 = x' * x⁻¹ := by
  intro p _ G R _ _ β x x' t t' hx hx'
  exact ⟨⟨(x' * x⁻¹, t' * t⁻¹), quot_mul_star (starT G.star R) (inC G R β) x x' t t' hx hx'⟩, rfl⟩

end GlobalTheory.LKMid
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleTrivializationsDifferByGroupPointStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianTripleTrivializations_differ_by_group_point : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (β : G.C) (x x' : (R ⊗[ℚ] G.C)ˣ) (t t' : Rˣ), Triv G R β x t → Triv G R β x' t' → ∃ g : UPts G.star R, (g : (R ⊗[ℚ] G.C)ˣ × Rˣ).1 = x' * x⁻¹ := by
  first | (exact @GlobalTheory.LKMid.triv_quot) | (exact GlobalTheory.LKMid.triv_quot) | (intros; apply GlobalTheory.LKMid.triv_quot  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApplyPvNeZero
open NumberField
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame)
open GlobalTheory.ThFr (IsSympl per_add)
open GlobalTheory.Dict (pv pv_smul span_range_pv)

namespace GlobalTheory.FrameEquiv

theorem dense_of_rat_of_span {V : Type} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [ContinuousAdd V]
    [ContinuousSMul ℝ V] (S : Set V) (h0 : (0 : V) ∈ S) (ha : ∀ u ∈ S, ∀ v ∈ S, u + v ∈ S)
    (hq : ∀ q : ℚ, ∀ u ∈ S, (q : ℝ) • u ∈ S) (hS : Submodule.span ℝ S = ⊤) : Dense S := by
  let P : Submodule ℝ V :=
    { carrier := closure S
      zero_mem' := subset_closure h0
      add_mem' := fun {a b} h1 h2 => map_mem_closure₂ continuous_add h1 h2 ha
      smul_mem' := fun t a h1 => by
        have ht : t ∈ closure (Set.range ((↑) : ℚ → ℝ)) := Rat.denseRange_cast t
        refine map_mem_closure₂ (f := fun (s : ℝ) (v : V) => s • v) continuous_smul ht h1 ?_
        rintro _ ⟨q, rfl⟩ u hu
        exact hq q u hu }
  have hP : Submodule.span ℝ S ≤ P := Submodule.span_le.2 subset_closure
  intro z
  exact hP (hS ▸ Submodule.mem_top)

theorem denseRange_pv {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {g : ℕ}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) : DenseRange (pv X idx x) := by
  have hq (q : ℚ) (v : Fin r → E) : pv X idx x ((q : E) • v) = (q : ℝ) • pv X idx x v := by
    rw [pv_smul]
    funext j
    simp
  refine dense_of_rat_of_span _ ⟨0, ?_⟩ ?_ ?_ (span_range_pv idx hs hx)
  · simpa using hq 0 0
  · rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    refine ⟨u + v, ?_⟩
    rw [pv, pv, pv, per_add]
    rfl
  · rintro q _ ⟨u, rfl⟩
    exact ⟨_, hq q u⟩

theorem exists_apply_pv_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → ∀ x ∈ X.dom, ∀ θ : (Fin g → ℂ) → ℂ, Continuous θ → θ ≠ 0 → ∃ v : Fin r → E, θ (pv X idx x v) ≠ 0 := by
  intro E _ _ _ r X g bas idx hs x hx θ hθ h0
  by_contra h
  push Not at h
  exact h0 ((denseRange_pv idx hs hx).equalizer hθ continuous_const (funext h))

end GlobalTheory.FrameEquiv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicUnitCarryingFormToNormMultiple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicUnitCarryingFormToNormMultiple
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem adelic_norm_move : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.C) (M : Type) [Field M] [NumberField M] (j : M →+* G.C) (σ : M →+* M), (∀ y : M, β * sh G (j y) = j (σ y) * β) → ∀ (a : M) (u : (AfP p ⊗[ℚ] M)ˣ), (u : AfP p ⊗[ℚ] M) * Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom u = 1 ⊗ₜ a → ∃ U : (AfP p ⊗[ℚ] G.C)ˣ, (U : AfP p ⊗[ℚ] G.C) * inC G (AfP p) β * (starT G.star (AfP p) U).unop = inC G (AfP p) (j a * β) ∧ ∀ y : G.C, (∀ m : M, y * j m = j m * y) → inC G (AfP p) y * U = U * inC G (AfP p) y := by
  intro p _ G β M _ _ j σ hβ a u hu
  let J : AfP p ⊗[ℚ] M →ₐ[ℚ] AfP p ⊗[ℚ] G.C := Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) j.toRatAlgHom
  have hJ : ∀ (r : AfP p) (m : M), J (r ⊗ₜ m) = r ⊗ₜ j m := fun r m => rfl
  have key : ∀ w : AfP p ⊗[ℚ] M, inC G (AfP p) β * (starT G.star (AfP p) (J w)).unop =
      J (Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom w) * inC G (AfP p) β := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      have e2 : J (Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom (r ⊗ₜ m)) = r ⊗ₜ j (σ m) := rfl
      rw [hJ, e2, starT_tmul]
      show ((1 : AfP p) ⊗ₜ β) * (r ⊗ₜ (G.star (j m)).unop) = (r ⊗ₜ j (σ m)) * ((1 : AfP p) ⊗ₜ β)
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      congr 1
      exact hβ m
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), MulOpposite.unop_add, mul_add, hx, hy, map_add (f := _), add_mul]
  refine ⟨Units.map J.toMonoidHom u, ?_, ?_⟩
  · show J u * inC G (AfP p) β * (starT G.star (AfP p) (J u)).unop = _
    rw [mul_assoc, key, ← mul_assoc, ← map_mul, hu, hJ]
    show ((1 : AfP p) ⊗ₜ j a) * ((1 : AfP p) ⊗ₜ β) = (1 : AfP p) ⊗ₜ (j a * β)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  · intro y hy
    show inC G (AfP p) y * J u = J u * inC G (AfP p) y
    generalize (u : AfP p ⊗[ℚ] M) = w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      rw [hJ]
      show ((1 : AfP p) ⊗ₜ y) * (r ⊗ₜ j m) = (r ⊗ₜ j m) * ((1 : AfP p) ⊗ₜ y)
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, hy m]
    | add x z hx hz => rw [map_add (f := _), mul_add, add_mul, hx, hz]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicUnitCarryingFormToNormMultipleStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicUnit_carrying_form_to_normMultiple : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.C) (M : Type) [Field M] [NumberField M] (j : M →+* G.C) (σ : M →+* M), (∀ y : M, β * sh G (j y) = j (σ y) * β) → ∀ (a : M) (u : (AfP p ⊗[ℚ] M)ˣ), (u : AfP p ⊗[ℚ] M) * Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom u = 1 ⊗ₜ a → ∃ U : (AfP p ⊗[ℚ] G.C)ˣ, (U : AfP p ⊗[ℚ] G.C) * inC G (AfP p) β * (starT G.star (AfP p) U).unop = inC G (AfP p) (j a * β) ∧ ∀ y : G.C, (∀ m : M, y * j m = j m * y) → inC G (AfP p) y * U = U * inC G (AfP p) y := by
  first | (exact @GlobalTheory.adelic_norm_move) | (exact GlobalTheory.adelic_norm_move) | (intros; apply GlobalTheory.adelic_norm_move  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkIffOfRel
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Pair

theorem inv_form_of_rel {S : Type*} [Ring S] [Algebra ℚ S] (b b' y : Sˣ) (z : S) (s : ℚ)
    (h : (b' : S) = algebraMap ℚ S s * (y * b * z)) :
    s • (z * ((b'⁻¹ : Sˣ) : S) * y) = ((b⁻¹ : Sˣ) : S) := by
  have h1 : algebraMap ℚ S s * (y * b * z) * ((b'⁻¹ : Sˣ) : S) = 1 := by rw [← h, Units.mul_inv]
  calc s • (z * ((b'⁻¹ : Sˣ) : S) * y)
      = ((b⁻¹ : Sˣ) : S) * ((y⁻¹ : Sˣ) : S) * (algebraMap ℚ S s * (y * b * z) * ((b'⁻¹ : Sˣ) : S)) * y := by
        simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, mul_assoc, Units.inv_mul_cancel_left]
    _ = _ := by rw [h1, mul_one, mul_assoc, Units.inv_mul, mul_one]

theorem form_of_rel {p : ℕ} [Fact p.Prime] {G : HTGroup p} (b b' y : G.Cˣ) (s : ℚ)
    (h : (b' : G.C) = algebraMap ℚ G.C s * (y * b * sh G y)) (v : InfinitePlace G.F) (x : Fin G.n → ℂ) :
    (star x ⬝ᵥ ((G.gram v * G.psi v ((b⁻¹ : G.Cˣ) : G.C)) *ᵥ x)).re =
      (s : ℝ) * (star (G.psi v y *ᵥ x) ⬝ᵥ
        ((G.gram v * G.psi v ((b'⁻¹ : G.Cˣ) : G.C)) *ᵥ (G.psi v y *ᵥ x))).re := by
  have hu : IsUnit (G.gram v).det := (G.gram_det v).isUnit
  have e : G.gram v * G.psi v ((b⁻¹ : G.Cˣ) : G.C) =
      (s : ℂ) • ((G.psi v y)ᴴ * (G.gram v * G.psi v ((b'⁻¹ : G.Cˣ) : G.C)) * G.psi v y) := by
    rw [← inv_form_of_rel b b' y _ s h, map_rat_smul, map_mul, map_mul, sh, G.psi_star, Matrix.mul_smul,
      ← Rat.cast_smul_eq_qsmul ℂ]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  rw [e, Matrix.smul_mulVec, dotProduct_smul, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, smul_eq_mul, ← Complex.ofReal_ratCast, Complex.re_ofReal_mul]

theorem mark_iff_of_rel : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Pair G) (μ : ℂ),
    P.Rel Q → (P.Mark μ ↔ Q.Mark μ) := by
  rintro p _ G P Q μ ⟨y, s, hs, hβ, hγ⟩
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  constructor
  · rintro ⟨v, hv, x, hx, hpos⟩
    refine ⟨v, hv, G.psi v y *ᵥ x, ?_, ?_⟩
    · rw [Matrix.mulVec_mulVec, ← map_mul, hγ, ← Units.val_mul, inv_mul_cancel_right, Units.val_mul, map_mul,
        ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul]
    · rw [form_of_rel P.β Q.β y s hβ] at hpos
      exact (mul_pos_iff_of_pos_left hs').1 hpos
  · rintro ⟨v, hv, x, hx, hpos⟩
    refine ⟨v, hv, G.psi v ((y⁻¹ : G.Cˣ) : G.C) *ᵥ x, ?_, ?_⟩
    · have e : P.γ * y⁻¹ = y⁻¹ * Q.γ := by rw [hγ]; group
      rw [Matrix.mulVec_mulVec, ← map_mul, ← Units.val_mul, e, Units.val_mul, map_mul,
        ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul]
    · rw [form_of_rel P.β Q.β y s hβ, Matrix.mulVec_mulVec x (G.psi v y), ← map_mul, Units.mul_inv, map_one,
        Matrix.one_mulVec]
      exact mul_pos hs' hpos

end GlobalTheory.LKMid.Pair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactOpenLevelConjCommensurable
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfCompactOpen
open GlobalTheory.LKCount
open scoped Classical

namespace GlobalTheory.RelIndexCompact

theorem relIndex_ne_zero_of_compact_open {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {K L : Subgroup G} (hL : IsCompact (L : Set G))
    (hK : IsOpen (K : Set G)) : K.relIndex L ≠ 0 := by
  have : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have ho : IsOpen ((K.subgroupOf L : Subgroup L) : Set L) := hK.preimage continuous_subtype_val
  have := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.index_ne_zero_of_finite

theorem conj_map_isCompact_isOpen {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : Subgroup G) (x : G) (hK : IsCompact (K : Set G)) (ho : IsOpen (K : Set G)) :
    IsCompact ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) ∧
      IsOpen ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.coe_map]
  have hc : Continuous (fun g : G => x * g * x⁻¹) := by fun_prop
  refine ⟨hK.image hc, ?_⟩
  have : ((MulAut.conj x).toMonoidHom : G → G) '' (K : Set G) =
      (fun g : G => x⁻¹ * g * x) ⁻¹' (K : Set G) := by
    ext y; simp [MulAut.conj_apply]
    constructor
    · rintro ⟨a, ha, rfl⟩; simpa [mul_assoc] using ha
    · intro hy; exact ⟨x⁻¹ * y * x, hy, by group⟩
  rw [this]; exact ho.preimage (by fun_prop)

end GlobalTheory.RelIndexCompact
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactOpenLevelConjCommensurable
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem level_conj_commensurable : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (g : G.GAf),
    Subgroup.Commensurable (L.K.toSubgroup.map (MulAut.conj g).toMonoidHom) L.K.toSubgroup := by
  intro p _ G L g
  obtain ⟨hc', ho'⟩ := GlobalTheory.RelIndexCompact.conj_map_isCompact_isOpen L.K.toSubgroup g L.compact L.K.isOpen
  exact ⟨⟨GlobalTheory.RelIndexCompact.relIndex_ne_zero_of_compact_open L.compact ho'⟩,
    ⟨GlobalTheory.RelIndexCompact.relIndex_ne_zero_of_compact_open hc' L.K.isOpen⟩⟩

end GlobalTheory.LKMid
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactOpenLevelConjCommensurableStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactOpenLevel_conj_commensurable : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (g : G.GAf), Subgroup.Commensurable (L.K.toSubgroup.map (MulAut.conj g).toMonoidHom) L.K.toSubgroup := by
  first | (exact @GlobalTheory.LKMid.level_conj_commensurable) | (exact GlobalTheory.LKMid.level_conj_commensurable) | (intros; apply GlobalTheory.LKMid.level_conj_commensurable  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocKCongr
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeEps
open Formalism.L2.Host (atFin unif IsUnitAt)

namespace GlobalTheory.GaussModulus

variable {E : Type} [Field E] [NumberField E]

theorem valued_algebraMap (w : HeightOneSpectrum (𝓞 E)) (z : E) :
    Valued.v (algebraMap E (w.adicCompletion E) z) = w.valuation E z :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w z

theorem exists_int_approx (w : HeightOneSpectrum (𝓞 E)) {x : w.adicCompletion E} (hx : Valued.v x ≤ 1) (k : ℕ) :
    ∃ y : 𝓞 E, Valued.v (x - algebraMap E (w.adicCompletion E) (y : E)) ≤ WithZero.exp (-(k : ℤ)) := by
  set c : w.adicCompletion E := algebraMap E _ ((unif w ^ k : Eˣ) : E) with hcdef
  have hvc : Valued.v c = WithZero.exp (-(k : ℤ)) := by
    rw [hcdef, valued_algebraMap, valuation_unif_pow]
  have hc0 : c ≠ 0 := fun h => by
    rw [h, map_zero] at hvc
    exact WithZero.exp_ne_zero hvc.symm
  let U : Set (w.adicCompletion E) :=
    (fun z => c⁻¹ * (z - x)) ⁻¹' ((w.adicCompletionIntegers E) : Set (w.adicCompletion E))
  have hU : IsOpen U := (Valued.isOpen_integer (w.adicCompletion E)).preimage
    (continuous_const.mul (continuous_id.sub continuous_const))
  have hU' : U.Nonempty := ⟨x, by
    simp only [U, Set.mem_preimage, sub_self, mul_zero, SetLike.mem_coe]
    exact zero_mem _⟩
  obtain ⟨b, hb⟩ := (HeightOneSpectrum.denseRange_algebraMap E w).exists_mem_open hU hU'
  have hb' : Valued.v (algebraMap E _ b - x) ≤ WithZero.exp (-(k : ℤ)) := by
    have h1 : Valued.v (c⁻¹ * (algebraMap E _ b - x)) ≤ 1 := hb
    rw [← mul_inv_cancel_left₀ hc0 (algebraMap E _ b - x), map_mul, hvc]
    exact mul_le_of_le_one_right' h1
  have hk1 : WithZero.exp (-(k : ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have hb1 : w.valuation E b ≤ 1 := by
    rw [← valued_algebraMap]
    have e : algebraMap E (w.adicCompletion E) b = (algebraMap E _ b - x) + x := by ring
    rw [e]
    exact Valuation.map_add_le _ (hb'.trans hk1) hx
  obtain ⟨y, hy⟩ := w.exists_valuation_sub_lt_of_integer hb1 (Units.mk0 (WithZero.exp (-(k : ℤ))) WithZero.exp_ne_zero)
  refine ⟨y, ?_⟩
  have e2 : algebraMap E (w.adicCompletion E) (y : E) - x =
      algebraMap E _ ((y : E) - b) + (algebraMap E _ b - x) := by
    rw [map_sub]
    ring
  rw [Valuation.map_sub_swap, e2]
  refine Valuation.map_add_le _ ?_ hb'
  rw [valued_algebraMap]
  exact hy.le

end GlobalTheory.GaussModulus

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairAdelicProdUnramifiedEmbeddingInjec
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairAdelicProdUnramifiedEmbeddingInjec
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem finiteAdeleRingAway_nontrivial (p : ℕ) [Fact p.Prime] : Nontrivial (AfP p) := by
  obtain ⟨q, hqp, hq⟩ := Nat.exists_infinite_primes (p + 1)
  have hqi : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  let v0 : IsDedekindDomain.HeightOneSpectrum ℤ :=
    { asIdeal := Ideal.span {(q : ℤ)}
      isPrime := (Ideal.span_singleton_prime hqi.ne_zero).mpr hqi
      ne_bot := by simpa using hqi.ne_zero }
  have hne : v0.asIdeal ≠ Ideal.span {(p : ℤ)} := by
    intro h
    change Ideal.span {(q : ℤ)} = Ideal.span {(p : ℤ)} at h
    rw [Ideal.span_singleton_eq_span_singleton, Int.associated_iff_natAbs] at h
    simp at h
    omega
  exact (AfP.eval (p := p) ⟨v0, hne⟩).toRingHom.domain_nontrivial

theorem pair_toAf_injective {p : ℕ} [Fact p.Prime] {G : HTGroup p} (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ)
    (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) : Function.Injective (P.toAf x t hx) := by
  haveI := finiteAdeleRingAway_nontrivial p
  intro a b h
  have h0 := congrArg Subtype.val h
  have h1 := congrArg Prod.fst h0
  have h2 := congrArg Prod.snd h0
  simp only [Pair.toAf, MonoidHom.codRestrict_apply, MonoidHom.comp_apply, MonoidHom.prodMap, MonoidHom.prod_apply, Prod.map_fst, Prod.map_snd,
    Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_left_inj, mul_right_inj] at h1 h2
  have e1 : (a : G.Cˣ × ℚˣ).1 = (b : G.Cˣ × ℚˣ).1 := by
    apply Units.ext
    have := congrArg Units.val h1
    simp only [Units.coe_map, MonoidHom.coe_coe] at this
    exact Algebra.TensorProduct.includeRight_injective (algebraMap ℚ (AfP p)).injective this
  have e2 : (a : G.Cˣ × ℚˣ).2 = (b : G.Cˣ × ℚˣ).2 := by
    apply Units.ext
    have := congrArg Units.val h2
    simp only [Units.coe_map, MonoidHom.coe_coe] at this
    exact (algebraMap ℚ (AfP p)).injective this
  exact Subtype.ext (Prod.ext e1 e2)

theorem pair_embedding_injective : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (r : ℕ) (z : Gr G r), Function.Injective ((P.toAf x t hx).prod (P.toQr r z)) := by
  intro p _ G P x t hx r z a b h
  exact pair_toAf_injective P x t hx (congrArg Prod.fst h)

end GlobalTheory.LKMid
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairAdelicProdUnramifiedEmbeddingInjecStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitudePair_adelicProdUnramifiedEmbedding_injective : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (r : ℕ) (z : Gr G r), Function.Injective ((P.toAf x t hx).prod (P.toQr r z)) := by
  first | (exact @GlobalTheory.LKMid.pair_embedding_injective) | (exact GlobalTheory.LKMid.pair_embedding_injective) | (intros; apply GlobalTheory.LKMid.pair_embedding_injective  <;> assumption)
end
end
