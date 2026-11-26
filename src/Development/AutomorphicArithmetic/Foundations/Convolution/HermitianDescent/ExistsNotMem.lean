module

public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalBase

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ExistsNotMem
namespace UpperTheory.ConvolutionTheory.D

section

variable {S T : Type} [CommRing S] [CommRing T] [Algebra S T]

private theorem pow_succ_app (σ : T ≃ₐ[S] T) (j : ℕ) (t : T) : (σ ^ (j + 1)) t = σ ((σ ^ j) t) := by
  rw [pow_succ', AlgEquiv.mul_apply]

private theorem pow_succ_app' (σ : T ≃ₐ[S] T) (j : ℕ) (t : T) : (σ ^ (j + 1)) t = (σ ^ j) (σ t) := by
  rw [pow_succ, AlgEquiv.mul_apply]

private theorem exists_notMem {σ : T ≃ₐ[S] T} {q : ℕ} (h : IsGal σ q) (a : T)
    (ha : ∏ i ∈ Finset.range q, (σ ^ i) a = 1) (P : Ideal T) (hP : P ≠ ⊤) :
    ∃ z, a * σ z = z ∧ z ∉ P := by
  obtain ⟨s, x, y, hxy⟩ := h.sep
  let c : ℕ → T := fun j => ∏ i ∈ Finset.range j, (σ ^ i) a
  have hc : ∀ j, a * σ (c j) = c (j + 1) := by
    intro j
    simp only [c]
    rw [Finset.prod_range_succ', map_prod, mul_comm]
    simp only [pow_succ_app, pow_zero, AlgEquiv.one_apply]
  let z : T → T := fun t => ∑ j ∈ Finset.range q, c j * (σ ^ j) t
  have hz : ∀ t, a * σ (z t) = z t := by
    intro t
    have h1 : a * σ (z t) = ∑ j ∈ Finset.range q, c (j + 1) * (σ ^ (j + 1)) t := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [z, map_sum, Finset.mul_sum, map_mul, ← hc, pow_succ_app, mul_assoc]
    have h2 := Finset.sum_range_succ (fun j => c j * (σ ^ j) t) q
    rw [Finset.sum_range_succ'] at h2
    have h3 : c q = 1 := ha
    have h4 : c 0 = 1 := by simp [c]
    rw [h3, h4, h.pow, pow_zero] at h2
    rw [h1]
    exact add_right_cancel h2
  have hs : ∑ i, x i * z (y i) = 1 := by
    have : ∑ i, x i * z (y i) = ∑ j ∈ Finset.range q, c j * ∑ i, x i * (σ ^ j) (y i) := by
      simp only [z, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    rw [this, Finset.sum_eq_single 0]
    · rw [hxy 0 h.pos]; simp [c]
    · intro j hj hj0
      rw [hxy j (Finset.mem_range.1 hj), if_neg hj0, mul_zero]
    · intro h0
      exact absurd (Finset.mem_range.2 h.pos) h0
  by_contra hcon
  push Not at hcon
  apply hP
  rw [Ideal.eq_top_iff_one, ← hs]
  exact P.sum_mem fun i _ => P.mul_mem_left _ (hcon _ (hz _))

private theorem mem_of_mem {σ : T ≃ₐ[S] T} {q : ℕ} (h : IsGal σ q) (a z : T) (hz : a * σ z = z)
    (P Q : Ideal T) [Q.IsPrime] (hPQ : P.comap (algebraMap S T) = Q.comap (algebraMap S T))
    (hzP : z ∈ P) : z ∈ Q := by
  have hd : ∀ j, (σ ^ j) z ∣ z := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      refine dvd_trans ?_ ih
      rw [pow_succ_app']
      conv_rhs => rw [← hz, map_mul]
      exact dvd_mul_left _ _
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by have := h.pos; omega⟩
  have hN : σ (∏ j ∈ Finset.range (r + 1), (σ ^ j) z) = ∏ j ∈ Finset.range (r + 1), (σ ^ j) z := by
    rw [map_prod]
    simp only [← pow_succ_app]
    rw [Finset.prod_range_succ, h.pow, Finset.prod_range_succ' _ r, pow_zero]
  obtain ⟨n, hn⟩ := h.fix _ hN
  have h1 : algebraMap S T n ∈ P := by
    rw [hn, Finset.prod_range_succ']
    exact P.mul_mem_left _ (by simpa using hzP)
  have h2 : algebraMap S T n ∈ Q := by
    rw [← Ideal.mem_comap, ← hPQ]; exact h1
  rw [hn, Ideal.IsPrime.prod_mem_iff] at h2
  obtain ⟨j, -, hj⟩ := h2
  exact Q.mem_of_dvd (hd j) hj

end

private theorem finite_max (k S : Type) [CommRing k] [IsLocalRing k] [CommRing S] [Algebra k S]
    [Module.Finite k S] : Finite (MaximalSpectrum S) := by
  have hf := Algebra.QuasiFinite.finite_primesOver (R := k) (S := S) (IsLocalRing.maximalIdeal k)
  have : Finite ((IsLocalRing.maximalIdeal k).primesOver S) := hf
  refine Finite.of_injective (β := (IsLocalRing.maximalIdeal k).primesOver S)
    (fun m => ⟨m.asIdeal, m.isMaximal.isPrime, ⟨?_⟩⟩) ?_
  · have := m.isMaximal
    exact (IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := k) m.asIdeal)).symm
  · intro m m' hm
    exact MaximalSpectrum.ext (congrArg Subtype.val hm)

theorem h90 : H90 := by
  intro k R _ _ _ _ S T _ _ _ _ _ σ q h a ha
  classical
  have hfin : Module.Finite S T := (galBase S T S σ q h).1
  have := finite_max k S
  have := Fintype.ofFinite (MaximalSpectrum S)
  have hloc : ∀ m : MaximalSpectrum S, ∃ z : T, a * σ z = z ∧
      ∀ P : Ideal T, P.IsMaximal → P.comap (algebraMap S T) = m.asIdeal → z ∉ P := by
    intro m
    by_cases hm : ∃ Q : Ideal T, Q.IsMaximal ∧ Q.comap (algebraMap S T) = m.asIdeal
    · obtain ⟨Q, hQ, hQm⟩ := hm
      obtain ⟨z, hz, hzQ⟩ := exists_notMem h a ha Q hQ.ne_top
      exact ⟨z, hz, fun P _ hP hzP => hzQ (mem_of_mem h a z hz P Q (hP.trans hQm.symm) hzP)⟩
    · exact ⟨0, by simp, fun P hP hPm => (hm ⟨P, hP, hPm⟩).elim⟩
  choose z hz hzP using hloc
  have he : ∀ m : MaximalSpectrum S, ∃ e : S, e - 1 ∈ m.asIdeal ∧ ∀ m', m' ≠ m → e ∈ m'.asIdeal := by
    intro m
    obtain ⟨e, he⟩ := Ideal.pi_quotient_surjective (I := fun m : MaximalSpectrum S => m.asIdeal)
      (fun m m' hne => MaximalSpectrum.isCoprime_of_ne hne) (Pi.single m 1)
    refine ⟨e, ?_, fun m' hne => ?_⟩
    · rw [← Ideal.Quotient.eq, he m, Pi.single_eq_same, map_one]
    · rw [← Ideal.Quotient.eq_zero_iff_mem, he m', Pi.single_eq_of_ne hne]
  choose e he1 he0 using he
  have hu : IsUnit (∑ m, algebraMap S T (e m) * z m) := by
    by_contra hnu
    obtain ⟨P, hP, hmem⟩ := exists_max_ideal_of_mem_nonunits hnu
    let m : MaximalSpectrum S := ⟨P.comap (algebraMap S T), Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := S) P⟩
    apply hzP m P hP rfl
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m)] at hmem
    have h1 : ∑ m' ∈ Finset.univ.erase m, algebraMap S T (e m') * z m' ∈ P :=
      P.sum_mem fun m' hm' => P.mul_mem_right _ (he0 m' m (Finset.ne_of_mem_erase hm').symm)
    have h2 : algebraMap S T (e m - 1) * z m ∈ P := P.mul_mem_right _ (he1 m)
    have h3 := P.sub_mem (P.sub_mem hmem h1) h2
    rw [map_sub, map_one] at h3
    convert h3 using 1
    ring
  refine ⟨hu.unit, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hu.unit_spec, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, σ.commutes, mul_left_comm, hz]

end UpperTheory.ConvolutionTheory.D
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalExt
open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

theorem UpperTheory.ConvolutionTheory.D.galExt :
    UpperTheory.ConvolutionTheory.D.GalExt := by
  intro F E k _ _ _ _ _ σ q h
  exact (UpperTheory.ConvolutionTheory.D.galBase F E k σ q h).2.2.2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.RepNmSucc
noncomputable section

open Matrix Polynomial

namespace UpperTheory.ConvolutionTheory.D

section

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R] {n : ℕ}

private theorem rep_sg_succ (σ : R ≃ₐ[k] R) (i : ℕ) (d : GL (Fin n) R) :
    sg (σ ^ (i + 1)) d = sg σ (sg (σ ^ i) d) := by
  ext a b
  simp [sg, pow_succ', Matrix.GeneralLinearGroup.map_apply]

private theorem rep_sg_one (d : GL (Fin n) R) : sg (1 : R ≃ₐ[k] R) d = d := by
  ext a b
  simp [sg, Matrix.GeneralLinearGroup.map_apply]

private theorem rep_sg_up (σ : R ≃ₐ[k] R) (γ : GL (Fin n) k) : sg σ (up R γ) = up R γ := by
  ext a b
  simp [sg, up, Matrix.GeneralLinearGroup.map_apply]

private theorem rep_nm_succ (σ : R ≃ₐ[k] R) (q : ℕ) (d : GL (Fin n) R) :
    nm σ (q + 1) d = nm σ q d * sg (σ ^ q) d := by
  simp [nm, List.range_succ]

private theorem rep_shift (σ : R ≃ₐ[k] R) (q : ℕ) (d : GL (Fin n) R) :
    d * sg σ (nm σ q d) = nm σ q d * sg (σ ^ q) d := by
  induction q with
  | zero => simp [nm, rep_sg_one]
  | succ q ih => rw [rep_nm_succ, map_mul, ← mul_assoc, ih, rep_sg_succ]

private theorem rep_cp_up (γ : GL (Fin n) k) : cp (up R γ) = (cp γ).map (algebraMap k R) := by
  rw [cp, cp, ← Matrix.charpoly_map]
  rfl

end

theorem nmRep : NmRep := by
  intro k R _ _ _ _ σ q hσ n δ γ hsep hcp
  haveI : Module.Finite k R := (galBase k R k σ q hσ).1
  have hs : ((nm σ q δ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).charpoly.Separable := by
    have h := hsep.map (f := algebraMap k R)
    rwa [← hcp] at h
  obtain ⟨x, hx⟩ := (conjSep k R n _ hs).1 ((up R γ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)
    ((rep_cp_up γ).trans hcp.symm)
  have hx' : nm σ q δ * x = x * up R γ := Units.ext (by simpa using hx)
  have h1 : nm σ q (sgConj σ x δ) = up R γ := by
    rw [(nmPoly k R σ q hσ n δ).2 x, mul_assoc, hx', inv_mul_cancel_left]
  refine ⟨x, h1, ?_⟩
  have h2 := rep_shift σ q (sgConj σ x δ)
  rw [h1, rep_sg_up, hσ.pow, rep_sg_one] at h2
  exact h2

end UpperTheory.ConvolutionTheory.D
end
end
