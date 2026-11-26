module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerEpsilonRootPowSubZetaExpMemFiltration

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEquationLiftAinf
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfMuFrobeniusEquationSolvableAndTendsto
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfMuFrobeniusEquationSolvableAndTendsto
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.ExpImage.Conv

section General

variable {A : Type*} [CommRing A]

theorem step_mem (I : Ideal A) (φ : A →+* A) (hφ : I.map φ ≤ I) {c : A} (hc : c ∈ I) (n : ℕ)
    {y : A} (hy : y ∈ I ^ n) : c * φ y ∈ I ^ (n + 1) := by
  rw [pow_succ']
  refine Ideal.mul_mem_mul hc ?_
  have h : φ y ∈ (I ^ n).map φ := Ideal.mem_map_of_mem φ hy
  rw [Ideal.map_pow] at h
  exact Ideal.pow_right_mono hφ n h

theorem solve (I : Ideal A) [hI : IsAdicComplete I A] (φ : A →+* A) (hφ : I.map φ ≤ I) {c : A}
    (hc : c ∈ I) (q : A) : ∃ y, y - c * φ y = q := by
  let f : ℕ → A := fun n => (fun z => q + c * φ z)^[n] 0
  have hf : ∀ n, f (n + 1) = q + c * φ (f n) := fun n => Function.iterate_succ_apply' _ _ _
  have h1 : ∀ n, f n - f (n + 1) ∈ I ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := step_mem I φ hφ hc n ih
      rw [hf (n + 1)]
      nth_rewrite 1 [hf n]
      convert this using 1
      rw [map_sub]; ring
  have h2 : ∀ m n, m ≤ n → f m - f n ∈ I ^ m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := add_mem ih (Ideal.pow_le_pow_right hmn (h1 n))
      rwa [sub_add_sub_cancel] at this
  obtain ⟨L, hL⟩ := hI.toIsPrecomplete.prec' f (by
    intro m n hmn
    simp only [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
    exact h2 m n hmn)
  simp only [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem] at hL
  refine ⟨L, ?_⟩
  rw [← sub_eq_zero]
  refine hI.toIsHausdorff.haus' _ fun n => ?_
  simp only [smul_eq_mul, Ideal.mul_top, SModEq.zero]
  refine Ideal.pow_le_pow_right (Nat.le_succ n) ?_
  have := sub_mem (step_mem I φ hφ hc n (hL n)) (hL (n + 1))
  convert this using 1
  rw [hf, map_sub]; ring

theorem geom_mem (p : ℕ) (e : A) :
    ∑ i ∈ Finset.range p, e ^ i ∈ Ideal.span {(p : A), e - 1} := by
  have h : ∑ i ∈ Finset.range p, e ^ i = (p : A) + ∑ i ∈ Finset.range p, (e ^ i - 1) := by
    rw [Finset.sum_sub_distrib]; simp
  rw [h]
  refine add_mem (Ideal.subset_span (by simp)) (Ideal.sum_mem _ fun i _ => ?_)
  obtain ⟨d, hd⟩ : e - 1 ∣ e ^ i - 1 := by simpa using sub_dvd_pow_sub_pow e 1 i
  rw [hd]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

theorem map_le (p : ℕ) (φ : A →+* A) {m c : A} (h : φ m = c * m) :
    (Ideal.span {(p : A), m}).map φ ≤ Ideal.span {(p : A), m} := by
  rw [Ideal.map_span, Ideal.span_le]
  rintro _ ⟨x, rfl | rfl, rfl⟩
  · rw [map_natCast]; exact Ideal.subset_span (by simp)
  · rw [h]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

theorem iterate_mem (I : Ideal A) (φ : A →+* A) (hφ : I.map φ ≤ I) {m c : A} (hc : c ∈ I)
    (h : φ m = c * m) (k : ℕ) : ∃ d ∈ I ^ k, φ^[k] m = d * m := by
  induction k with
  | zero => exact ⟨1, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨d, hd, e⟩ := ih
    refine ⟨c * φ d, step_mem I φ hφ hc k hd, ?_⟩
    rw [Function.iterate_succ_apply', e, map_mul, h]; ring

end General

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem frob_mu : WittVector.frobenius AI.μ =
    (∑ i ∈ Finset.range l, WittVector.teichmuller l AI.ε ^ i) * AI.μ := by
  have h : WittVector.frobenius (WittVector.teichmuller l AI.ε) =
      WittVector.teichmuller l AI.ε ^ l := by
    rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
  rw [LocAinf.μ, map_sub, map_one, h, geom_sum_mul]

theorem mu_not_isUnit : ¬ IsUnit AI.μ := by
  intro h
  obtain ⟨θ, hθ⟩ := exists_isTheta l P AI
  have h0 : θ AI.μ = 0 := (hθ.2.2.2.1 _).2 ⟨AI.π₁, by rw [AI.μ_eq, mul_comm]⟩
  have := h.map θ
  rw [h0] at this
  exact not_isUnit_zero this

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), (∀ q : Ainf l, ∃ y : Ainf l, AI.μ * y - WittVector.frobenius (AI.μ * y) = AI.μ * q) ∧ ∀ M n : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, (WittVector.frobenius : Ainf l →+* Ainf l)^[k] AI.μ ∈ Ideal.span {((l : ℕ) : Ainf l) ^ n, AI.ξ ^ M} := by
  intro l _ P AI
  have hc : ∑ i ∈ Finset.range l, WittVector.teichmuller l AI.ε ^ i ∈
      Ideal.span {((l : ℕ) : Ainf l), AI.μ} := geom_mem l _
  have hφ := map_le l _ (frob_mu AI)
  refine ⟨fun q => ?_, fun M n => ⟨n + M, fun k hk => ?_⟩⟩
  · haveI := (GlobalTheory.Per.AinfComplete.main l AI.μ (mu_not_isUnit AI)).1
    obtain ⟨y, hy⟩ := solve _ _ hφ hc q
    refine ⟨y, ?_⟩
    rw [map_mul, frob_mu, ← hy]; ring
  · obtain ⟨d, hd, e⟩ := iterate_mem _ _ hφ hc (frob_mu AI) k
    rw [e]
    refine Ideal.mul_mem_right _ _ ?_
    have h1 : Ideal.span {((l : ℕ) : Ainf l), AI.μ} ≤ Ideal.span {((l : ℕ) : Ainf l), AI.ξ} := by
      rw [Ideal.span_le]
      rintro x (rfl | rfl)
      · exact Ideal.subset_span (by simp)
      · rw [AI.μ_eq]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    have h2 := Ideal.pow_le_pow_right hk (Ideal.pow_right_mono h1 k hd)
    rw [Ideal.span_insert] at h2
    rw [Ideal.span_insert, ← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow]
    exact Ideal.sup_pow_add_le_pow_sup_pow h2

end GlobalTheory.ExpImage.Conv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfMuFrobeniusEquationSolvableAndTendstoStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_mu_frobenius_equation_solvable_and_tendsto : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), (∀ q : Ainf l, ∃ y : Ainf l, AI.μ * y - WittVector.frobenius (AI.μ * y) = AI.μ * q) ∧ ∀ M n : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, (WittVector.frobenius : Ainf l →+* Ainf l)^[k] AI.μ ∈ Ideal.span {((l : ℕ) : Ainf l) ^ n, AI.ξ ^ M} := by
  first | exact @GlobalTheory.ExpImage.Conv.main | exact GlobalTheory.ExpImage.Conv.main | (intros; apply GlobalTheory.ExpImage.Conv.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEquationLiftAinf
noncomputable section

namespace GlobalTheory.ExpImage.Tail

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l}

abbrev Fr (l : ℕ) [Fact l.Prime] (n : ℕ) : Ainf l →+* Ainf l :=
  (WittVector.frobenius : Ainf l →+* Ainf l) ^ n

theorem Fr_succ (n : ℕ) (a : Ainf l) : Fr l (n + 1) a = WittVector.frobenius (Fr l n a) := by
  rw [Fr, pow_succ']; rfl

theorem Fr_succ' (n : ℕ) (a : Ainf l) : Fr l (n + 1) a = Fr l n (WittVector.frobenius a) := by
  rw [Fr, pow_succ]; rfl

theorem frob_teich (x : OCb l) :
    WittVector.frobenius (WittVector.teichmuller l x) = WittVector.teichmuller l x ^ l := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]

theorem Fr_teich (n : ℕ) (x : OCb l) :
    Fr l n (WittVector.teichmuller l x) = WittVector.teichmuller l x ^ l ^ n := by
  induction n with
  | zero => simp [Fr]
  | succ n ih => rw [Fr_succ, ih, map_pow, frob_teich, ← pow_mul, pow_succ']

theorem lifts_Fr {w : Ainf l} {c : ↥(K0 K)} (h : Lifts AI K w c) (n : ℕ) :
    Lifts AI K (Fr l n w) ((frK P K ^ n) c) := by
  induction n with
  | zero => simpa [Fr] using h
  | succ n ih =>
    rw [Fr_succ, pow_succ']
    exact ih.frob

theorem lifts_sum {ι : Type} (T : Finset ι) (w : ι → Ainf l) (c : ι → ↥(K0 K))
    (h : ∀ i ∈ T, Lifts AI K (w i) (c i)) : Lifts AI K (∑ i ∈ T, w i) (∑ i ∈ T, c i) := by
  unfold Lifts at h ⊢
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  exact Finset.sum_congr rfl h

def oK (P : LocPrime l) (K : FinExt l) : ↥(K0 K) →+* P.R.BdR :=
  (oB P).comp (algebraMap ↥(K0 K) (Om l))

theorem oK_apply (c : ↥(K0 K)) : oK P K c = oB P (c : Om l) := rfl

def u (P : LocPrime l) (j : ℕ) : P.R.BdR := qB P ((j.factorial : ℚ_[l])⁻¹) * tD P ^ j

theorem u_mem (j : ℕ) : u P j ∈ FilB P 0 := by
  refine qB_mul_mem _ (FilB_anti ?_ (FilB_pow tD_mem j))
  simp

theorem taylor0 (hT : LocTied l P AI) (m M : ℕ) :
    io AI (WittVector.teichmuller l AI.ε ^ m) - ∑ j ∈ Finset.range M, (m : P.R.BdR) ^ j * u P j ∈
      FilB P (M : ℤ) := by
  have h := GlobalTheory.T.teichmullerEpsilonRoot_pow_sub_zeta_exp_mem_filtration l P AI hT 0 m M
  rw [P.ζQ_zero, one_pow, map_one, one_mul] at h
  convert h using 3 with j hj
  · rfl
  · rw [pow_zero, div_one, div_eq_mul_inv, map_mul, map_pow, map_natCast, u, mul_assoc]

theorem span_mem_Lat {M n : ℕ} {a : Ainf l}
    (ha : a ∈ Ideal.span {((l : ℕ) : Ainf l) ^ n, AI.ξ ^ M}) : io AI a ∈ Lat AI M n := by
  obtain ⟨x, y, rfl⟩ := Ideal.mem_span_pair.mp ha
  refine ⟨x, ?_⟩
  have h := FilB_zero_mul (io_mem AI y) (FilB_pow (io_ξ_mem AI) M)
  rw [mul_one] at h
  convert h using 1
  simp only [map_add (f := _), map_mul, map_pow]
  ring

theorem tail (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : LocTied l P AI)
    (K : FinExt l) (ι : Type) (T : Finset ι) (w : ι → Ainf l) (c : ι → ↥(K0 K)) (m : ι → ℕ) (M : ℕ)
    (d : ℕ → ↥(K0 K)) (hM : 1 ≤ M) (hw : ∀ i ∈ T, Lifts AI K (w i) (c i))
    (hd : ∀ j < M, ‖(d j : Om l)‖ ≤ 1 ∧
      d j - (l : ↥(K0 K)) ^ j * frK P K (d j) = ∑ i ∈ T, c i * (m i : ↥(K0 K)) ^ j) :
    ∃ y : Ainf l, y - WittVector.frobenius y =
        ∑ i ∈ T, w i * WittVector.teichmuller l AI.ε ^ m i ∧
      io AI y - ∑ j ∈ Finset.range M,
        qB P ((j.factorial : ℚ_[l])⁻¹) * oB P (d j : Om l) * tD P ^ j ∈ FilB P (M : ℤ) := by
  have hD : ∀ j, ∃ D : Ainf l, j < M → Lifts AI K D (d j) := by
    intro j
    by_cases hj : j < M
    · obtain ⟨D, hD⟩ := GlobalTheory.T.exists_lifts_of_norm_le_one_alt l P AI hT K (d j) (hd j hj).1
      exact ⟨D, fun _ => hD⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose D hD using hD
  have h0 : D 0 - WittVector.frobenius (D 0) = ∑ i ∈ T, w i := by
    have h1 := (hD 0 hM).sub (hD 0 hM).frob
    have h2 := (hd 0 hM).2
    simp only [pow_zero, one_mul, mul_one] at h2
    rw [h2] at h1
    exact h1.unique (lifts_sum T w c hw)
  obtain ⟨q, hq⟩ : AI.μ ∣ ∑ i ∈ T, w i * (WittVector.teichmuller l AI.ε ^ m i - 1) := by
    refine Finset.dvd_sum fun i _ => Dvd.dvd.mul_left ?_ _
    have := sub_dvd_pow_sub_pow (WittVector.teichmuller l AI.ε) 1 (m i)
    rwa [one_pow] at this
  obtain ⟨hc1, hc2⟩ := GlobalTheory.T.ainf_mu_frobenius_equation_solvable_and_tendsto l P AI
  obtain ⟨y', hy'⟩ := hc1 q
  have hy : (D 0 + AI.μ * y') - WittVector.frobenius (D 0 + AI.μ * y') =
      ∑ i ∈ T, w i * WittVector.teichmuller l AI.ε ^ m i := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib] at hq
    rw [map_add (f := _)]
    linear_combination h0 + hy' - hq
  refine ⟨D 0 + AI.μ * y', hy, ?_⟩
  set y := D 0 + AI.μ * y' with hydef
  let E : ℕ → P.R.BdR := fun n => io AI (Fr l n y) -
    ∑ j ∈ Finset.range M, (l : P.R.BdR) ^ (j * n) * oK P K ((frK P K ^ n) (d j)) * u P j
  have hstep : ∀ n, E n - E (n + 1) ∈ FilB P (M : ℤ) := by
    intro n
    have h1 : io AI (Fr l n y) - io AI (Fr l (n + 1) y) =
        ∑ i ∈ T, oK P K ((frK P K ^ n) (c i)) *
          io AI (WittVector.teichmuller l AI.ε ^ (m i * l ^ n)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Fr_succ', ← map_sub, ← map_sub, hy, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [map_mul, map_mul, (lifts_Fr (hw i hi) n).io_eq, map_pow (Fr l n), Fr_teich, ← pow_mul,
        mul_comm (l ^ n), oK_apply]
    have h2 : ∀ j ∈ Finset.range M,
        (l : P.R.BdR) ^ (j * n) * oK P K ((frK P K ^ n) (d j)) * u P j -
          (l : P.R.BdR) ^ (j * (n + 1)) * oK P K ((frK P K ^ (n + 1)) (d j)) * u P j =
        ∑ i ∈ T, oK P K ((frK P K ^ n) (c i)) * (((m i * l ^ n : ℕ) : P.R.BdR) ^ j * u P j) := by
      intro j hj
      have h3 := congrArg (fun x => oK P K ((frK P K ^ n) x)) (hd j (Finset.mem_range.mp hj)).2
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sub, map_mul, map_pow, map_natCast, map_sum] at h3
      have h4 : (frK P K ^ (n + 1)) (d j) = (frK P K ^ n) (frK P K (d j)) := by
        rw [pow_succ]; rfl
      have h5 : ∑ i ∈ T, oK P K ((frK P K ^ n) (c i)) * (((m i * l ^ n : ℕ) : P.R.BdR) ^ j * u P j)
          = (l : P.R.BdR) ^ (j * n) * u P j *
            ∑ i ∈ T, oK P K ((frK P K ^ n) (c i)) * (m i : P.R.BdR) ^ j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        push_cast
        ring
      rw [h4, h5, ← h3]
      ring
    have h6 : E n - E (n + 1) = ∑ i ∈ T, oK P K ((frK P K ^ n) (c i)) *
        (io AI (WittVector.teichmuller l AI.ε ^ (m i * l ^ n)) -
          ∑ j ∈ Finset.range M, ((m i * l ^ n : ℕ) : P.R.BdR) ^ j * u P j) := by
      simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
      rw [← h1, Finset.sum_comm, ← Finset.sum_congr rfl h2, Finset.sum_sub_distrib]
      simp only [E]
      ring
    rw [h6]
    refine Submodule.sum_mem _ fun i hi => FilB_zero_mul ?_ (taylor0 hT _ _)
    rw [oK_apply, ← (lifts_Fr (hw i hi) n).io_eq]
    exact io_mem AI _
  have htel : ∀ n, E 0 - E n ∈ FilB P (M : ℤ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := add_mem ih (hstep n)
      rwa [sub_add_sub_cancel] at this
  have hE0 : E 0 ∈ FilB P (M : ℤ) := by
    refine GlobalTheory.T.mem_deRhamFiltration_of_forall_ainfLattice l P AI hT M _ fun r => ?_
    obtain ⟨k₀, hk₀⟩ := hc2 M r
    have hk : ∀ j, ∃ k : ℕ, (l : P.R.BdR) ^ k * u P j ∈ Lat AI M r := fun j =>
      (GlobalTheory.T.bounded_and_eventually_sub_mem_Lat_alt l P AI hT _ (u_mem j) M r).1
    choose k hk using hk
    set n := k₀ + ∑ j ∈ Finset.range M, k j with hn
    have hEn : E n ∈ Lat AI M r := by
      obtain ⟨M', rfl⟩ := Nat.exists_eq_add_of_le' hM
      have e0 : oK P K ((frK P K ^ n) (d 0)) = io AI (Fr l n (D 0)) := by
        rw [oK_apply, (lifts_Fr (hD 0 hM) n).io_eq]
      have e1 : E n = io AI (Fr l n y') * io AI (Fr l n AI.μ) - ∑ j ∈ Finset.range M',
          (l : P.R.BdR) ^ ((j + 1) * n) * oK P K ((frK P K ^ n) (d (j + 1))) * u P (j + 1) := by
        simp only [E, hydef]
        rw [Finset.sum_range_succ', e0]
        simp only [map_add (f := _), map_mul, u, zero_mul, pow_zero, Nat.factorial_zero, Nat.cast_one,
          inv_one, map_one]
        ring
      rw [e1]
      refine sub_mem (io_mul_mem_Lat AI _ (span_mem_Lat ?_)) (sum_mem fun j hj => ?_)
      · have := hk₀ n (Nat.le_add_right _ _)
        rwa [← RingHom.coe_pow] at this
      · have hj' : j + 1 < M' + 1 := Nat.succ_lt_succ (Finset.mem_range.mp hj)
        have hle : k (j + 1) ≤ (j + 1) * n := by
          have a1 : k (j + 1) ≤ ∑ j ∈ Finset.range (M' + 1), k j :=
            Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj')
          have a2 : n ≤ (j + 1) * n := Nat.le_mul_of_pos_left _ (Nat.succ_pos j)
          omega
        obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hle
        have := io_mul_mem_Lat AI (((l : ℕ) : Ainf l) ^ e * Fr l n (D (j + 1))) (hk (j + 1))
        convert this using 1
        rw [he, oK_apply, ← (lifts_Fr (hD _ hj') n).io_eq, map_mul, map_pow, map_natCast]
        ring
    have := add_mem (FilB_le_Lat AI (n := r) (htel n)) hEn
    rwa [sub_add_cancel] at this
  convert hE0 using 1
  simp only [E, Fr, pow_zero, mul_zero, one_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [u, oK_apply, AlgHom.one_apply]
  ring

end GlobalTheory.ExpImage.Tail
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEquationLiftAinfStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_equation_lift_Ainf : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (ι : Type) (T : Finset ι) (w : ι → Ainf l) (c : ι → ↥(K0 K)) (m : ι → ℕ) (M : ℕ) (d : ℕ → ↥(K0 K)), 1 ≤ M → (∀ i ∈ T, Lifts AI K (w i) (c i)) → (∀ j < M, ‖(d j : Om l)‖ ≤ 1 ∧ d j - (l : ↥(K0 K)) ^ j * frK P K (d j) = ∑ i ∈ T, c i * (m i : ↥(K0 K)) ^ j) → ∃ y : Ainf l, y - WittVector.frobenius y = ∑ i ∈ T, w i * WittVector.teichmuller l AI.ε ^ m i ∧ io AI y - ∑ j ∈ Finset.range M, qB P ((j.factorial : ℚ_[l])⁻¹) * oB P (d j : Om l) * tD P ^ j ∈ FilB P (M : ℤ) := by
  first | exact @GlobalTheory.ExpImage.Tail.tail | exact GlobalTheory.ExpImage.Tail.tail | (intros; apply GlobalTheory.ExpImage.Tail.tail <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusSolutionExpansionModFiltration
noncomputable section

namespace GlobalTheory.ExpImage.Expand

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

theorem frob_teich (x : OCb l) :
    WittVector.frobenius (WittVector.teichmuller l x) = WittVector.teichmuller l x ^ l := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]

theorem root_pow (AI : LocAinf l P) (m : ℕ) : AI.εroot m ^ (l ^ m) = AI.ε := by
  induction m with
  | zero => simp [LocAinf.εroot]
  | succ m ih =>
    rw [pow_succ', pow_mul, LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
    exact ih

theorem epsT_pow (AI : LocAinf l P) (s : ℕ) :
    epsT AI s ^ (l ^ s) = WittVector.teichmuller l AI.ε := by
  rw [epsT, ← map_pow, root_pow]

theorem lifts_iter {AI : LocAinf l P} {K : FinExt l} {w : Ainf l} {c : ↥(K0 K)}
    (h : Lifts AI K w c) (k : ℕ) :
    Lifts AI K ((WittVector.frobenius : Ainf l → Ainf l)^[k] w) ((frK P K ^ k) c) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ', AlgHom.mul_apply]
    exact ih.frob

theorem qB_eq (z : ℚ_[l]) : qB P z = oB P (algebraMap ℚ_[l] (Om l) z) :=
  IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR z

theorem coeff_eq (K : FinExt l) (s j : ℕ) {ι : Type} (T : Finset ι) (c : ι → ↥(K0 K))
    (m : ι → ℕ) (d : ↥(K0 K)) :
    algebraMap ℚ_[l] (Om l) ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ *
        levSum P K s j T c m d =
      ∑ k ∈ Finset.range s, ∑ i ∈ T, (((frK P K ^ k) (c i) : ↥(K0 K)) : Om l) *
          (P.ζQ s ^ (m i * l ^ k) * algebraMap ℚ_[l] (Om l)
            ((((m i * l ^ k : ℕ) : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ j / (j.factorial : ℚ_[l]))) +
        algebraMap ℚ_[l] (Om l) ((j.factorial : ℚ_[l])⁻¹) * (d : Om l) := by
  have hl : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hj : (j.factorial : ℚ_[l]) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  rw [levSum, mul_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (((m i * l ^ k : ℕ) : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ j / (j.factorial : ℚ_[l]) =
        ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ * ((l : ℚ_[l]) ^ (j * k) * (m i : ℚ_[l]) ^ j) := by
      push_cast
      rw [div_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm k j]
      field_simp
    rw [e, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast]
    ring
  · have e : (j.factorial : ℚ_[l])⁻¹ =
        ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ * (l : ℚ_[l]) ^ (s * j) := by
      field_simp
    rw [e, map_mul, map_pow, map_natCast, mul_assoc]

theorem expand : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (ι : Type) (T : Finset ι) (w : ι → Ainf l) (c : ι → ↥(K0 K)) (m : ι → ℕ) (M : ℕ) (d : ℕ → ↥(K0 K)), 1 ≤ M → (∀ i ∈ T, Lifts AI K (w i) (c i)) → (∀ j < M, ‖(d j : Om l)‖ ≤ 1 ∧ d j - (l : ↥(K0 K)) ^ j * frK P K (d j) = (frK P K ^ s) (∑ i ∈ T, c i * (m i : ↥(K0 K)) ^ j)) → ∃ y : Ainf l, y - WittVector.frobenius y = ∑ i ∈ T, w i * epsT AI s ^ m i ∧ io AI y - ∑ j ∈ Finset.range M, oB P (algebraMap ℚ_[l] (Om l) ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ * levSum P K s j T c m (d j)) * tD P ^ j ∈ FilB P (M : ℤ) := by
  intro l _ P AI TT K s ι T w c m M d hM hw hd
  obtain ⟨y₁, h1, h2⟩ := GlobalTheory.T.frobenius_equation_lift_Ainf l P AI TT K ι T
    (fun i => (WittVector.frobenius : Ainf l → Ainf l)^[s] (w i)) (fun i => (frK P K ^ s) (c i)) m M d hM
    (fun i hi => lifts_iter (hw i hi) s) (fun j hj => ⟨(hd j hj).1, by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [(hd j hj).2, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_pow, map_natCast]⟩)
  set H : ℕ → Ainf l := fun k =>
    ∑ i ∈ T, (WittVector.frobenius : Ainf l → Ainf l)^[k] (w i) * epsT AI s ^ (m i * l ^ k) with hH
  have hφ : ∀ k, WittVector.frobenius (H k) = H (k + 1) := by
    intro k
    simp only [hH]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, Function.iterate_succ_apply', epsT, frob_teich, ← pow_mul]
    congr 2
    ring
  have hs : H s = ∑ i ∈ T, (WittVector.frobenius : Ainf l → Ainf l)^[s] (w i) *
      WittVector.teichmuller l AI.ε ^ m i := by
    simp only [hH]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm (m i), pow_mul, epsT_pow]
  have h0 : H 0 = ∑ i ∈ T, w i * epsT AI s ^ m i := by simp [hH]
  refine ⟨∑ k ∈ Finset.range s, H k + y₁, ?_, ?_⟩
  · have ht := Finset.sum_range_sub' H s
    rw [Finset.sum_sub_distrib] at ht
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), map_sum, Finset.sum_congr rfl (fun k _ => hφ k), ← h0]
    rw [← hs] at h1
    linear_combination ht + h1
  · have hk : ∑ k ∈ Finset.range s, ∑ i ∈ T, oB P (((frK P K ^ k) (c i) : ↥(K0 K)) : Om l) *
        (io AI (epsT AI s ^ (m i * l ^ k)) - oB P (P.ζQ s ^ (m i * l ^ k)) *
          ∑ j ∈ Finset.range M, qB P ((((m i * l ^ k : ℕ) : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ j /
            (j.factorial : ℚ_[l])) * tD P ^ j) ∈ FilB P (M : ℤ) := by
      refine Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun i hi => ?_
      refine FilB_zero_mul ?_ (GlobalTheory.T.teichmullerEpsilonRoot_pow_sub_zeta_exp_mem_filtration l P AI TT s (m i * l ^ k) M)
      rw [← (lifts_iter (hw i hi) k).io_eq]
      exact io_mem AI _
    have e1 : io AI (∑ k ∈ Finset.range s, H k) = ∑ k ∈ Finset.range s, ∑ i ∈ T,
        oB P (((frK P K ^ k) (c i) : ↥(K0 K)) : Om l) * io AI (epsT AI s ^ (m i * l ^ k)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hH]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [map_mul, (lifts_iter (hw i hi) k).io_eq]
    have e2 : ∑ j ∈ Finset.range M, oB P (algebraMap ℚ_[l] (Om l)
          ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ * levSum P K s j T c m (d j)) * tD P ^ j =
        ∑ k ∈ Finset.range s, ∑ i ∈ T, oB P (((frK P K ^ k) (c i) : ↥(K0 K)) : Om l) *
          (oB P (P.ζQ s ^ (m i * l ^ k)) *
            ∑ j ∈ Finset.range M, qB P ((((m i * l ^ k : ℕ) : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ j /
              (j.factorial : ℚ_[l])) * tD P ^ j) +
        ∑ j ∈ Finset.range M, qB P ((j.factorial : ℚ_[l])⁻¹) * oB P (d j : Om l) * tD P ^ j := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [coeff_eq, map_add (f := _), map_sum, map_mul, ← qB_eq, add_mul, Finset.sum_add_distrib,
        Finset.sum_mul, Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    have := add_mem hk h2
    rw [map_add (f := _), e1, e2]
    convert this using 1
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring

end GlobalTheory.ExpImage.Expand
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusSolutionExpansionModFiltrationStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusSolution_expansion_mod_filtration : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (ι : Type) (T : Finset ι) (w : ι → Ainf l) (c : ι → ↥(K0 K)) (m : ι → ℕ) (M : ℕ) (d : ℕ → ↥(K0 K)), 1 ≤ M → (∀ i ∈ T, Lifts AI K (w i) (c i)) → (∀ j < M, ‖(d j : Om l)‖ ≤ 1 ∧ d j - (l : ↥(K0 K)) ^ j * frK P K (d j) = (frK P K ^ s) (∑ i ∈ T, c i * (m i : ↥(K0 K)) ^ j)) → ∃ y : Ainf l, y - WittVector.frobenius y = ∑ i ∈ T, w i * epsT AI s ^ m i ∧ io AI y - ∑ j ∈ Finset.range M, oB P (algebraMap ℚ_[l] (Om l) ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ * levSum P K s j T c m (d j)) * tD P ^ j ∈ FilB P (M : ℤ) := by
  first | exact @GlobalTheory.ExpImage.Expand.expand | exact GlobalTheory.ExpImage.Expand.expand | (intros; apply GlobalTheory.ExpImage.Expand.expand <;> assumption)
end
